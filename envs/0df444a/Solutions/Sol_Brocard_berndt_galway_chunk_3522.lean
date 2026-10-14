-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3522
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:17.445737+00:00
-- url     : https://prove2.me/submissions/4a938be7-9fd4-44de-9d07-11ec0ad03e68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 633273381 ≤ n < 633453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 633274631 1250 633273381 633273383
    0x901180c0302060a05040f0f170604051513020301061502060106020a0510110f03040c090c020102181002120307030e0c0904120809010b0301180203150405060c03071b030f120204061b 80
    0x780a00001c2480260b1031f0095001d40000c0d620262000c0c5003608803440c0c00003442010900d90444c4041c0030004000007075012180b0820302110406a031074511242d40f1501c20a0060360540c03c040700010324030620b2a5100302c1e00c0c1e0036070aa50440c0c0c3c950500341d0b41d03a0b15400c002400340c6c1c0048010042c044081d40128010180303800882e2624030041d10030b001c41e4000f610251000780c141501084440441d218507150428507000a5092404801d030280328038020300c4110707016030101000500000d00c00d200320402840041041d40e01c90600610040c000c1c01c843d0031003440361080040c1807505107410003000d0b1040350300205114034202543e01c11100d090003d0031020346917483c0e03001e011240c1c0d001e00490f44041541031030307503a41d640035004051401014001c451040707580f00d0248400326801141d440c0d070003950f440b03600340daa480300902285c4520003030301051075403400040c070101019808500044001002e0b030b20310441e400c0040c0040c0c224400c40c400e0402003110160311041c08001c0c3c0748104c03a01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 633275881 1250 633274631 633274637
    0x31409010e040c08062407030302071502070b100b042411061335131a0309151918020901090212070306050303030f04050c0a0605030901180c0302060a 66
    0x8214200402c0a54410200100c0414a0102002810b040000c001d181148149007a02c05c204042e8000801074446d050b400780425800040d8003090100d0181603003c91085c200e0704554824603420201050725054524418440c01c07a9400500705c142d420548003030f0307a564013b040620061281403c842c4094503400b0003031084103c1c022101400c1440518411000d024110302c180080303140034205650344a0000c0906107007034024100c021200d01e0002100c0d0b000c0026145d80fa07500011005840000382c1c8551301c0741550301c840700030170306840780554003400b4400c3c21140f203000c000307500c00441401120290800014008403041c0d425041d08030071840700c2c2800411100940302c1c3c0209160b028240c0202070b1003500001c070801c03841140310002d40d100e8a01e24081041a0600f00081d8580c400541008507031143c40c80803509000007808000101c44009205a158547d101d0380500b01c2e400444848810794179100f401000d08181081100c0c00f030754810400a400c5065034208845508030780000810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 633277131 1250 633275881 633275897
    0x30b011205101a120d030c02030f0403080a1404060309060e030a0e060f0c070f0602070b1c0218090411090106091a031f060203120c07020d060903050d020a0e04051303140901 76
    0x1551110568004000703134902c0500600700440001030309035680e031072082085504c20418070001c14007a030180c07820303294056001c0380e40e400c040b0802c0361030318503050707600c552101c00140c006050361b01544080a01e40c0300718410710180d01d920000e80e460b4000d40704400040b450203054290f86141c210000d0030b18595050429080800100ca617524000c0d854120310380302c8807103000510403607404119500c010501080203528250780c49e50004400ba240480201c140c0e900070851007104d01c000c035000c0840030400b5000f4459071816040041c24100c0645c0702c20300a120120000c81c1031440b0b0711000c016142c0742c900448807400c02c00d1b116015684018942000022140041488080c105000000a10040e030042da1100310b40b04100d188481d003d4a04007035002d00304040d80c01a194a00e01c3c0c241541c000c240003591007001d0405a8091081d000b080203500d00c00a18201c6036904110b01510004040c0c5080100b03a41c0c8070b810b000801e8040c080034002c5440c4440100d0903241450003006125018544411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 633278381 1250 633277131 633277181
    0xe09060f03010f02070327061d01050f0a02100605040c020c090406183804020112140c040f14150c150a09031803200303070206070c030b01120510 64
    0x104a0b0040789080700000c080300141d00740504107c2d0400500e0102c1c444c52010317a46400c1e0091300c0420308087c030300384403505c40300b001c412030b8003542c1a2aa0f1013a42254103a8904084000a48401c50f079401031300701ea840c107680400c0a0030301c2d1180c20380b49441500188496441142001403d00d001403085410720307243c0e24101c0c420700e0044c1590200520583d0031580d20092040c003904000c0b40d070102a000d5003003040c180a501081c412500b40c205030213007001000014114241400381400020b562524034841090111041051000b4011680d000b040c0000c040c2d21054860340003c1ca030b140003548034006ca00c0158868114000410945807180c007201e141c8081062590350300fa0f011902503501940d9040d03018149a0026074184100000c1407114000c2811aa1441c600100203a00081030361001072920714991410000c41d003486800920154844501f89416044001c0c1c41c0411940110310300d00003e440c0c000451503820aa501201a04011010386003050040c841d8904c1203010f000080e00f180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 633279631 1250 633278381 633278411
    0x17062503091b1203141602061b06070504090e0a02030c0405060a1205030304020111010c0804032613020f030d09090b0d3c08030109020c0c030d0201060807060e09060f0301 75
    0x8401000418603500f8809030908000d01004042c03080c03604450350401100040d0744c0880000c1109a9041310010b0310782c940b416059a00f6000b040e40064070f40324050503c2402908031000d0011038440c0c0105000102d20100d929448604601c002500b56002c500d804410745020b0300700c10340c4114090280e00ca034070b5880301248040010f1080960702904000140300c190750788001400c402c06032400007800b91484a890003408a540104003034100308204480e4449010402d05011041501240c980e0580c10f10380b440207449900c60900728030440d241c40145d84076040104e2840041d500c2e58031603c620302d24004e04000906640c90601d40e110243d90003030000207101d4600440544c00707400010b8640744d203070021008418001002d800c14050a001c1d1400004d00342c8080301e055503030240c0050b0700c5818031803440c1d1800d0340c0703041c10582c5400f5618a0750121a0f05500c42c80840d101241240d040d940d0b942d4040d03c00c40b901102d00368004501c500041c95500f0401001c600c804009400003400d400440118 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 633280881 1250 633279631 633279683
    0x60f04180b07200a020111011d0f100c12021806030f0402131107081605120316050f040e19020d060528060f14041706250309 55
    0x894104401c0c0c0140007109912101d100890492640610074110722640225511101c07440005c1c1003105088810306903d000b0b4100c822036041e0440e01d1065540b540c900340e07840d48203079030720412940b10380d010090f000902c038050190300182d036031030301e84110000c04c00000c0039510a00b00d2410118a81c0c071000010307102c0d4001035108060358010b010b90f83c20940b0400907680307106888400100d0811061415240c032240448890581c80808940e41e81022003004014501144010789140a039101400710b04105c0001940b0448007a100d640103000390700e0040d1240d0144000c8070440c01014042445265400e010a5400914820402c0b083c00a02c04002c800d90703025100303441909458000402036030603d2a040000c60b6001080c040345082000030108182e40c0c0c0e4840d40c02000240c6040c06031840c0102d4000640b01c0400d011b40e0b543d0340d110051a13100e0141100c1c2c0c5c41e001e20480300010301584614500110303191003c4050754119881d150101c0c06001d00c1d0700c060b1402194170b040c40c0546080a054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 633282131 1250 633280881 633280883
    0x10b040329010e070c05060106050423061b0a0507060302120a0501030c03080f0d0c03060510020705090a020a051902060601140a0804080a0e060c0109170304080915210103050c18060f0418 82
    0x1403071340c0e900d040098514003a254208cd002e40c6000e090505040c0741e44074000c1d11046034070320703000b102c01c1d801e1601424645940207101070020302400c003010981d15416001080c0d1650098990116521440c060100b100c00912000d01944e4200c01c080c000128098028503140303490681c018200410160024102c90310010900046682e41e0002c00590a0186400c91046407500207418150310304400301c1c000c182d0041108410640c00a15407a6480c0550151a80141d000d440c2c545035001c2044040d54540007075440902155a0004840e5803c0c054804c4900fa420302c1d5541d511562669034035240c441e041040c040d800d120f01c144612400d9100c000c09400350200440012507010160f0420052414410100c0643c41314100104008605014212502e4500555004a00d50408405c2450600884c002d4540100501d101d42c1d4103401c1c1d4402e0b175410784c2e000d0b130103540d42481c5001c200300c2039122841d90346440004001c0000c003940750000f1216529003002d800400c4110a840d05170b0080002800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 633283381 1250 633282131 633282137
    0x209030f0f0708010b01122d020403050601170c010c29011502070f060e030c041a0a080d12390905010c03080103060b0d0209010b040329010e070c05060106 68
    0x1101e01c0c041d00200030840c000d1082100800210342c2e03480000f0a00905001a20f44603511410400811302c3c41075500000f00f036a901d40c207005120000c801c20041d5025102c2641d043c03280b1030010a0310010911a07160101804004154200d0004015a050610f5050035185984259890070341001340a10070002806904a00381007903050150201c409092800c02104642c03001806103c21800c0c1141e117400d450716030604500c180d500d80002480e002000500a0300181030001021502e00091101d07880e56008449280d91f8613100c003441962034001c88006000980542c4501c94000e106030700240150b0002429009080304800040c0b99001a07101100f042e071000d100c4000345c40b60701240341c8003d028246441c10000c0144d440c01415a5010b0101600391a0b58503640300881d603440c1000d030003840d400303010b005896039916015a6203030030905c0147d07922900c0d09854845081010030740c00000d6180300c944001ca0b4201644410000001010f500c20320249100c16404207000308001c90083c03003543c0e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 633284631 1250 633283381 633283393
    0x70e120106270b01090501201207050c012c01020118050c03070806010605030117010b1305011802030412030b0d3315140a0e010308091215040807060209030f 69
    0x2610020011400c0b0707994505551528034507900030381e40039407000704454091030200482824a0b14100e248941b00e29113492620440301c5554103c0654000782c0761850140060382c201441070401510851204c3c941300400f202c10411000d0a00c4289003003100080b070600c0005002c141c0755014601880c200f071002c1d030b841c1d4465400f100303092404100c02d001400510000e072001d5494200f02070b05d2400103010341c00340d4105d900e40ca0a072a40c0254040213003c1001050450706005643c2d084009240a0013030012054041942801850300c0d4001c4902039580029642410500080704500030840301d01001d0340407a111b08480045150486c02c801010043d01d980d00d010801760801740400400300680820032401d01d0200909050000084012540224540c00111910b440000d104229603082003c7c2c05100d0800401131041e22806004c1c095429622411000b101140481e80c2c0c0100c0c00f001c280034030303500d0001400526408003400416110b0300001d800c14014100180c202000d01c07400e000e4940c005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 633285881 1250 633284631 633284669
    0x1805271609090b01170a06231603150501020c190b030a02190c200609060c0f120f0a0f03021303030c05010c0f020c06160803100303030b0117070e120106 67
    0x2102001e0050400b144104602011203080607110b00325214003030145035035658050410041807403500885210b10f1000c1c411883d00707041d0711510046441d40c9c580000c0c644401d24151422410000094a0058006006204403a0104800e107484450840c02d0600c0e0450001503503c0804095401015030318405030312844680d005811402510740c40c0400c220740580fa6202058900d481c020500030446100f0721040f45100c0415458070450811540241c00002e10900407031001c909030595504840950300d00c4503010f0901c6429004010b55828403103000c00007804880e004141c0c0424030406404c0141c20007185090000071031010b540240c0c04141e2098505c000c200c028414111080090305041d6451042004004d54a1104c950349a0158600043c100c7e51540804000c0c02d280b42c2c407500c25542e07840c15075000494000203100c02c901082c10507255407411741c0510003140249036600f0045440c1d50300da80c002c80d07010f00c5600d04113410001074080794000c96403e0081402030000d04002e43d90078000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 633287131 1250 633285881 633285893
    0x9080d0c020703110402030414060a02090906191707030606090911090c031810090c06020f030a2a060906150504020c070611030c010510180527160909 66
    0x10506018086400100c018400113401a440511040c400d540040c1c89544074508909041d0740031602000c584598001c000601310380d60003e201d500d00c10b032080f0b200ba4071020140916001c295400c1490074003426401e21070300800c0c000d91704407608108111040e199880d103402c004c46d481c640189083e04c0c0c941c0100d40921003230403880c07103d07c2c4040e0b40115492408000e103203d40c4c00702a2109408056214505034241c1003080104418403500d5420458914140b0700404403102601c92100540034408154103200d8001c400d0b107030310168a071121240305281008100c590450101410b521031801da407182c002c2100f9105080741680700d1743c40040c83c0039034042844076212007075000c02e21031070040103050500307200451204121011820034501000c81080f500e4214001c034817810001e58600420031016010f041c4082e400c40d861b08011245154000301444140e400803a41d5581668400121200c000f40302d00b421410303c28440191040350000e80b02030139803003040758003000e0916201d02c40c40090081d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 633288381 1250 633287131 633287141
    0x1050c1912091203020705101206080d0207050d03051603090b070c0e22020f010327060b04020a020a0f03020321150909061305010b0d080a0e03160b0d0b030109080d 72
    0x82000351405500f000d42d030025690b01c0c0c82d0081d036006074040200e0001c01809200100001944c5c12800e0065517151241143e4440d01034001c0030052062000c002010304020010040c56074059a030a032a1541d139240ad0b5084011000301101080704148000074084900340141140354440e41304907407020b1408980c41c4004401a041105109407501098500d6600010a5071071035030540d044911b4901e400011f0b802068280f16062400090410382101480b045440000041c4100c0e0100160000c030703c140012030243e41102c1300580d003d034110134049a48002e00400191280c41203c1c078141801862210320f0742c1d81c0034440501c2540d0300510005400804441d076140f0025210708240d460030821b481d6403a0000741048503040c02400103001408402e4120001040014115801d404094030b440405544428403400000d014030480700c2d030134a00803a0b1565104101000850701901b401c0d000642a40015200300e80c2e0340e0b642c1c910341004c0d00d0a00a910009005261950303c03030325800600310070b4030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 633289631 1250 633288381 633288389
    0x507020d020c0a0b0706180602040f030c0f0b2b0609060806011e0e1005041a04050f04081801090f0f0303020f030a12110705061018051501050c191209 66
    0x120019020b01c10504e020b802d0f118015048880442e140c264910b4840c1205420b180180c4040d00001d80842d0f0111004440c204907485145100d02807607070741a60319806500e500131549502c0d42000041400605292039401c1c005030cd261040540700c40b04001c3c0b0484105520031207200d42c54201c10800b0900904c901130040c602120001180c83e00300044139120b444600420701c10013821000f26a0406521034044d0240002400c02c0010700c0b0888100e800040ca5512850b1045040000060001c400080010b019541c05a006802c003800004a41c21564483c60424108149504009410002c1102d440b0003032880b18600d0300081c0c29420004e04280f0098601c803803d9000f085501f5440354050f083e203038460603480300012010042d40c40c1d07a1161107600e901030301c10300c503900c00d1210740d0304415045d404403081c0e81d180c4400c0d0071007100c2d1719050301c0003100d241840d030245500e801e00700d501a500408501818005030b13003004456038a55522680d6401c400d981810a0707503030090300385402c44c0c06c600244c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 633290881 1250 633289631 633289639
    0x2060a05270f0d1110090801090b0a0b01020a03080610030e010f1a09012907050319020721020d020d0f08030601120b06070213021b0a060f02070c09050c0d0507020d020c 74
    0x100f110b54945035001d0a0089089000342c14007980b0502d8180b26101041c00340c40402e000780030020850800c0c048880c01a5081c03445186491041d10956000094811000340d2584130118141c0c0c919040101e0f000c1c60740d0010080c5900c0d0074021400300c2c8207100790360b40b40f00c00302d50000b000300440006945484480250300c0c01648880018446203e4408002d1210300b07003040e0394a41140f44104003445130051780c1c0c0c0140036100104e4210b020300001404c0c0305400300301d50700b12800140d403165001d55401d20b990241d14609128001c60300982488040500c1050000d0150081c0130450340c0d56417a46014280250303100200401441855030f40030103404002c07941d12605120b0b5068440000c0c0e024807030004002c1c403542c030741a00720306000307a141c040e9594000070420f2010002d075581c41c540d0301e603901c0d20750440e0b410b440c2c03604505004040788251415070381c00c01c8401e80b135142018072607801410040c04208100700c1c00d000702c0c0001300360350245504c2020705601801a07000d00c0c403070192401094030851841 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 633292131 1250 633290881 633290899
    0xf03040e0f060303180103091a19061a1605160603060b040303054501020f03040819171c050601022b090e0106080f0106080403090302060a05270f 64
    0x10b20382c0c001003914549a00300d60100000e070000001038004000306a40105101c0c50300c039108101d40c0b0583c3c17106114958400a1104450001002000325a094050480810040c828031034010380c1120180c41d9a0b19800c80c1c5828200041d1a12441c295075901802c022601c0c030582402101d615004c0c0310018089401044d06083c15586c0140190141e9104602d40701c4084180354880d081610090902d01e00701d011040c1c00d11801d003019070382c034644510014050311800a080e81003400001c03c07101200e03641d81c00340c440c3c1071180012000031255a142034801c0394003648464084648880284188000e0b508854814100d8610b4141a910000c1c803890540d000308051606400c6654a9440d500071001055800c91f40d000c0e00c01e840602143d04004003203103810703002055041e0882d4003103001e511460f00040c1c690380d81d0001118038000840e001000280300307c00c100300509055005d040c01e40c0440c24098145071000c3d01c88500541080a641c41d0f085416480404504201d450444828420b40714071074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 633293381 1250 633292131 633292141
    0x1210150309080f2109070518040f02060f19020606040f09030206070e030a0f061508060c091905030613021009050105030112030908060f01050a060503360f03040e0f 72
    0x100e0068000102d011280010b42c0c3d030400c03458440c404e06a1025001019050800321401680c9503214094980107099404451020080c15101d4920840e480080c0182454075a824001682c12500a0680041091001a45c110300c0e81c0f10352008554180d000b0a01d0785001e90400095601a0801d199500c1c988681d8a022a5020620980c041c049040490301207010001180c80c19030314032030280105050100303140801155400c10326074025036408505049881c0c82d4000c0d11014140c8150408240400900105041c5a46165032941100c51601046a640c001090034424100e8070043c01d0400000d240c0c0c114502410382c150560b009180607034149080c9400170b000c1e884180160341c51762054441d42000c0601c61500000030b89865010f9400d81e05100d06250700c0240280196032060380e40b483e0103d103d62080c41035a20800507110b403580c020300300d01ca04140b428034810f041c4a006560a05860040c5e40030040c50003502d400000640e030320740c03604201c0d002e1140b010708680b620ba100a81809 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 633294631 1250 633293381 633293393
    0xe01030c120b1c030c0212060613050402040605100c02041109031e03130b030f0f060f06030405010b060a0f021e031e0d0518060601020105090d141210150309 69
    0x900020441d07040000c0c20800b10001401c041002d0103800f0910140c0801c1204042d0300a4925111034070071b0700c2401240303030008810340d210301c03007240d440390804807416a95241d45038a40207160414009000001c52b540ca0750045402c8450b8400b000703001c05d00c44204002142020303c10401c1c0b07009ca929070141003410344c0000a40b03812010100680b1030210039102441d5407403d01c1141e40110050000d850211f55448011286804c22502c0e2442042c2c0c0c00001142c001820114600c5000004c2104003010342801c2007140ca80c2001d041a241c40d0350701c0c078202059031680e0004103041c081684541c0060382c45640c0007841c00d80e0112800040c0c2c408564150822b5000006840e40c20f01074484400c0d900081d544030320001d0251542443c04039007054140119243c96070301c1094109085010b07280580c0c0c0b540010b900b0b80c0c00564108115a01c403d580100c120f100304104421041503c0700c1502c0c0c5034071a030300d01e0205002a00c42d20b120342c030881005c0010400c15030000b80c880ac0181014841c1030a02d84541d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 633295881 1250 633294631 633294647
    0x105011106060a060507051510030203070e07050703111911040f1505060c1204090c0311030403170a060b0d0b04050906040f030806010903150b030601060306050a0909050a020d030f0e01030c 83
    0x191040c40000701b0001c080000c00d100c01455071140f07520850b07082ca0000c01c14101c07407441c2d1009074041c0c05404c9000c81c1d0500c507160500d118107296150140303056100da40131103003080f89a01c1d04e14280100210014a494283c00e03405405008030400748424080302c00b00401c484001030842c03296407804c803041b08404800c0003904101c40e02200c50030388510307581d0030040c20040c1c1c4021000741208009008540c8210395400b0540c114116a01040f541401c400d00a14511050714090301217a00c1c0c1c91240c00c041d01002520f0f034040b40030100440c03625035031061101142c00929441c00c1c01a1a561003c80505040c80b40960000b00800140034500b410344500c0e60000c0c11480180c01c2018020014009234052141200215400b0740d01c40d2101c00303803c000d8001010300300c00c168880c0c01030034000200f041c482e014940946000400d801d4110f0b19003440c003002040720490407201c600556042030f003da0703502c110b0f00711014026101c4252125075003000601840c107140c0603e041c180391030844030007030354401c0503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 633297131 1250 633295881 633295889
    0x10507021f09171303021f080c0901020a1202120403061a090f0a0c02070f090e01061703182701061202070c060f110f150604091106030c0c0a0602030105011106060a 72
    0x3484d039a1003454074120b9007034055402c084d4010780400810088400b0304005680052150382c0c480d111b54503180d4200c40720303209824410b40181e0209021402040071003003030181c07042050049a8911903603030310112058105510a840f4580d941041040350b211380340c17402d00f004904030707142103441c81c00421b0710180c0fa0740a0121031700c0782e69403d201c822403402040102c015150200c581425259111075440213810032064010465081820014905000c1540c2a011244450240d8108155407441d0303000440c4002c480d503800864141010600d080d5444c10010152034103203081e806604100c405414a003007014031905aa20400c00d0b41c2c0481c503559440000c0d904a8a000350403400c54850441c0c03080148040d1340c145018101c1a50010380c000285940451030360b1904d04501e556600c10002260080d003000b811600f040380503000c03a46001d4000f0b5520003c3c200c07800e03003442c04400c3c486150440c0345608948060380000103000968202030a01070010b51a0000c101fa40b9115000c1043c100301c0d841 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 633298381 1250 633297131 633297173
    0x605030c09160c0f050a0f050d18050123070c15020712021320030610050705153102041a130c020309060c0a110316050d080903010507021f09 62
    0x2c600f8007049030000088020b02e40003402c0301e2480015042c14054501c204004803080d2140d81c0c010b0042500610681075030040d0090f01d250403902d4140103550300100e0502d40440c40c041d0341a0f500500c01c8000c040e2100380e016a5000458908020405200341c108451240c00c1d90b0010f20200000c44c0c0007290071422540c1511980400030700c603480c03400600302c4074140f001d24040c0424403024241e100c8014520a400c00ca4071318101210807201510300b4450303090040c10581047c0c0c03803444280d040580d030175041424102c5452485071207203041504000b0180c042c6038011803020114007540f4250040c0001c8680c940b9210b00b2000d4494005110a180f200e40000c125840e040035000180c000d2058400b00700e8054226070350380f40003800c819110320005070101c821b102d610343c08000505000030341c107510701f0300244050304075801c0008015014041e10b40841d400b00c0c0070044a07806803801e010741d60061080313400510700089030814001c401403161040103111807901d514080819510103a0144a01da201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 633299631 1250 633298381 633298397
    0x501182a03120c0b07080910110306040c020f06012306090102030d0c030b04090f0204050112050714190b18010e0315040206070512071202010506091602010615030605030c0916 77
    0x7550a503060380c42c041c211349007941c10001d60f544c002100920690004080c2c2d1251343d0560240000c8494000c00f140c1914014800030390241004d40c07016800402038012101000d07101500549420401d03000040940a404c1c0c641c0950740034074031840c00010040f158107040602c01e00000303559014070300d1540492a1681c4820300510302035407040b41100d00140061200c80c08034186064280c1186400306d0060349800f00024460450a031361081d4540d000d0b016142d1f041c500510504021801340c03006d9441302c8042c1c01d0141401280207c140206041c049003601c03142c800b000c040300e45c0c017146241c505105400c15003a089507404644185800c440c80300c1c480007070700e6600204405020341a0010083e1140300c00c072200c0c3c00301ca240035141031072152100811810507070320200d00780e0b6025600550446060380100310706010032400546a00000c1c4000510075550b51a90410040c1382488840800d07500e4030184040c0c2070501005021030000e50700c02c01e09040220603003080c820001028000c0010790 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 633300881 1250 633299631 633299663
    0x7050712290402041a030f01231e0a022106011107050a090f090503070f020316030203061617040b010f0f031104020307121104050a0905070c031107030501182a03 71
    0x10400102d80803170068202c805059007110300f98024040716041c000102903000d000003940c403027008600c1c400c880030001700b034060407444524072071080060b00290180c1d40a12600d607403003807100401d0405c032421501442e070500308000050b040000c80c05403407080e82c010407014401a240c040418084810415001070040d2035200c03500010181140018801e00000483c282070102c0f040c1440940c038002c070705445190300c1c01c036680203100d08a407200a4254001c1d00005044498112911b00e1601003070814107807225451070021034081048608440382140c8e8401407005188601d0318401816a00091110040c11608d80d901044130008500784126000000980030500c109540040544c01e031130140b042c00c1c2c400303141418541190207030602588041c48005580100c4d40207850084603540c40e80c01000302142c0b81105e4244642e030f2200028072860130300000241003403080850744070742c0d00441010a1060315005540709030070034801c038180c3c580c07001030601c8540c412030314000c59522000d492921540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 633302131 1250 633300881 633300911
    0x170609270a0f0f03081812030c0f0c060103030221030f06010e060414010e04110d0c260a0e16060c0203160b18060406140903030705071229040204 64
    0x60420080c054000c07550b800302005805407904480c58466280d0b50f00c40e90b501301e440000022030b03015988071070784500c1c19071120010756002075800210181c0c00510340382080c6d070b0040c0140e0010762054000d42c4060010400d045c0d050103401451580c0d0104844600000b1054643d40d01014004045c4c402502011a5140e0301403039004403081006043c40707850741e0303032142d00d00701140b100072203039020985000700c80d0703140d01c1c02d4400c4010181017218000d042004110362240104064901041402020003030903024007910101c008150042c07a98200240c82d041d091034050311520703800003403258014481c84002007040c02c603c1c800d640f0149400c0f0011861230000030303d4280d0010400900d4041554003242241541000381001c0302d020722300b480350f0540502404a50310440c49840d0003e9004224610254010401481f0344c4078010100e80c2800301d191240d80c10b0403e070340c1c00710410107820210407040000e10381d455040c146503988240349107401c00306407031022500184024070842d81c5254001c20414 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 633303381 1250 633302131 633302143
    0x30a09181803050703030c02060f0a0209040b03030c0f12070210050706023709030302060601121d0610090506060904020901031b050301170606060a2a0317060927 71
    0xd0a80822080a50300d00b00900b103944800403d0780000e00744000d00981500003e0810b000342c0ca40076586c51644d840324401c00080d00038110540e80130b91945081103480e54208040c1140c002c12101400c200500c180303003140382040819441790803038400e004141c00360f51001c0403418450b546040150360340c001450300800902c195030508826643d29500100c00d40700a151006056619044400d502008481d040c1c81000750341c400140142e0056000400551041c90800c03141c1049080120f0701c45800f04106140743d00503050701195600001c2048800303d440b0b40d01c0d00c014400080200490700301400070400f944207520005008030f0700018050382c140d100c1d90114220084021035240b85000061006255500a2044840740e100b01c4076403180a0303c3c00b0800070b020303a00040a032441c04003a080243c8903e00354140380c140260442070712000b07030b01211000003102031090390703000b01042d0840039007a01c020001d06050b02a8078118200a080c481000c400300c0710868074111080604401c010142c0f500c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 633304631 1250 633303381 633303401
    0x90b030c0a14030313090504032703020f010905040504051c110316020a15020c040e010c0e280b0301061b0f020904050709020a051c0e032d030423030a0918 68
    0x51175003c00051003c20b541c071850255110359192215600040c0300c00174900c92108031142400f140010410041c9020000c110f445c0c801810301141442c1c0e5200010200c40c0121400d4403180c02903000c0380d50005507800301038950b090350300f403a00b80e140501e01c0c49640ca004e002d40c85601031035110003034800c2d036880040e080000d01280041e00b41034000e01d44025201e05024603203d0066003001c0d242e9216401c10301600c00360441030390b03880304400c091904110007442039018212400b840712803200c00d00c02c03203488a803024102d001c0810396254580103008003a08182216641003400b100c0b4424001400800e0f1108280c0d01101c440090303844c2c504105041030300f241c1c442c1d032144c0d200144c202045074000c80600681039641550008103403042480354184d852190507102c0e60303007082014540d035a012001d4032110008480c8019140000312591410035801541c003507410007401c40c020440c141c910a079400f14a0b003441d001c5c42c240703038a1005c06003020707034140245529171010601c4100c3c0740c3d0380750380480040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 633305881 1250 633304631 633304657
    0x503180c0607050d020624010509063001061e0507051c0903060b04050408190309050607050c01050718060e01050c01060906051507020f1c0213020301090b030c0a140303 74
    0x402c6a0710740196120340d440c201c1030242c002c010010f030103001d803081c41da001103001802e01d0070030706440c0c001190654800e17103003982c0c012010304c08814208422800351040880b094103904c220745c2010004d4030503c2c0168818020010f01c40ea8200303c41009681d0400d101090342403840d25440329252580c10480ca000090908642070b40000d220390b03510414000c00c81e0b0041c00e00700045031003e4240801d40300c048802800594041050130082c501d9817204441d071042e14600028404402e90f1114104002035590b000060404204600000028401c0076082005c41c00c0120044080110340300800c0400c1c810300051101c6030b02d002d501d0342d000d907040791210b40c007403002001816194100b200040809004541c0201b082005d45116065044110380f00d09400400b054aa12142c00070880e031070003401802401200072481600068036102000c0d1400342c280c0d40302680b0796041022403003c54034000c0c5030742d00c41d40c001d001c2c1054035140d0350311010035a000403104d42a0030113900c02292640c494010302d6015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 633307131 1250 633305881 633305887
    0x70605060d020414010f09060f030209061206010b12060f010e220e06160503220c081914070e0a1508060103080a120c0815120f01090c060c030503180c06 67
    0x5414000080c0f14181e403000781e029240b0f5a02c80f04130314100c419274001d82040a4042c0f02c180094940b0381031050b48001c00600c54002150301d10012410082e0030392010302c24440224541c0c280388000760300c0f03540c09001074031050148038414000820000e50400304034041c201d04003600000043c1031803410001c01d4001e505000c090640400c0030ba07203180448d0034406294043c0308074289188600d0480740240d0410720515400940d881c82600d5413900c0f12012039000c2d801c4400005c5c501d200b40403060341e0380c505a0300703c0102c2c409420170b4072081a20001d001c003550082c000c14002a040ea0003126000400840005103a100c00000c6803480102c1d9001601d5921030f0350f000200b0410302600502c008800b40d0360725000c1681d507602a0b0250741c5010600c0303000c540c0240001d400c100b05224003000b40780d8000d0042c0c0240c4203400e183d600740f10180c83c100d0243e075150130702c0d80c2c240301d401c10f035500042900f860040300d19081502c0040c80703400301a0440340000030040700032100ba0030402030407455520040036155 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 633308381 1250 633307131 633307151
    0x40201121503020901050a15080a0204090e0a06050108030307120e2b020f0d1b020d0618021e010f0503130b0a2903030d02090415030503031e0c070605060d0204 70
    0x1070040721501c401c0f4401c1c1c90700c000103c0c203400d00804c18411640b45501e101d00d48041024180d942440080c010a040340d402d0200142c8904a40078013441da05445000c3c10740d510b0b4030b05161098502c140c00600846d82708000784200158815004d504804501e080061070250400360603041c0b01c0e910102114420304807071142c4001c0524848614129800e03000c5492008030441c1c02034a410070320144101041c0809804200c80884609154100f48000d0014000c0301980c0d1315441224640030b00c8081300c9030784442c01c00450400780507240a0030301c051000e04401d6100c04c0020306d216100180c030010014080081022046140c002041c07403588910300b00178610304190f03000000e0130711000e01005a5440740318118050411017400381c0007000074010310b00e4054000403840103507100089140d0400e40d91142109046546410200914401c82c00f80da501c1c1400e820250707079200c0b5281e6040f010200c510034024600301102c115207800b84d0000c0c000c18165280e4000912007421500080d401030300300b019070070f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 633309631 1250 633308381 633308411
    0x2070c03050d0207061d1f051b0708070b041401050c0a0b091c110d0f0e0a0f06080c163801030c0b04051503151203070303061d0f04020112 61
    0x8003c1d03404598072540708050b11038459452969a03001c03941c10452100307c00005103c80090704506000070700340a481c0481d281200405248902c1d1081400d4204030800d000c0900c06000c0307d0010940207081600789420402034500d070080807a5184d040c8500000c40c812261030500c100d41d0210340103051920246040c5042035203800703140c1c1140394009080e803c001c24481c0269200104111035500134000d0080501c41515030341c220703c3d84003044c080c05802c03205803640c42c2190394000d403603030754040c00e807151900e200648900070180c25103103004000d000f01300b6035211940781e0340030594120311150001d40010844480c0b1816101d000c943e005445100114002402a4203604881c030801816852903914458200f56000d81c5c06050360104120180c49003601c1444003843c1c001444450041840300365000041c51354103180321111641c0c002052401c2496014070802c0c00401006172030400901c0b00882055420344014250082c0d22491004103041d6445403884070b00d4154064410407412200390b0b814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 633310881 1250 633309631 633309643
    0x10091a040b010e0610020c120313081609110f07030c060f05090606012a020a05060307110d0c08090904050c09130611070530071212060e0a02070c03050d02 68
    0x1900603100c028003280850400407141d00a41485501800e011040e0b107003080310341c208a45904a10340700512282b50054a12a8030303c0c0200041002440702c80305210a0089100c6207078450307005940380400400c5c4088410341112411581523010f15034960003443d00b0380d2101c0101002600c040c0c5070403606c1141c20a41c4d84420f001c2d146420480d600d51380c601c401158800c0d0721079405c07180c00e028481c4000041401c017207003485044c4000c2443c403209407101d0100c0d0043d00b0499480780020321395a440642100d00f40126040d00c0640e141502801d146611211040d11034800c98a0286425000190501c1380510098080c844014540360540c14105488003043c2c084400913200c243c501040807508020210459089075486000382c400041c00c1040901c03585440d20000c03626104440700c1101c15000940207100d0703903101d61005038890300500340042060010409010301c4c185003c1d000d100c407074900320060b548841d6080b005660740c2c0031440d251200b02c00560000b400c0b8030400c4542c096494000c604 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 633312131 1250 633310881 633310889
    0x8040311070f0506090616240c09061202130303120b1903060c02031b03070308130302101a061b210406140c03030403020a031b0510091a040b01 63
    0x101110124410342840d25110103204000c0720501030003041049003400b00282034005002410f19083c0003100d00c81da10700c00e4181204070752881c00350700001d000426010a500030b030b03480d0074002c100d612819080030f8010800390207400c081c02445204084c5103c65501200c41000100310340400302c07550703441c0144c90718a0010802c1c035000e0610082d0340003810206040c90900303040700b0708001070f1072654607035500411004a480046000c01c00041d440364490305000b203014005100110303a24061400c0c014004d00010702540c900b1b8003251101c2c40400d40c0021078034148000c0010000e40d0484003c802c01c0c070030070f076844640d4208401090845510b035051241001c942c0000f02030b80c40082d8001c0c0d6841c450425030207a4a601c401c2844207124440c8a1213880c0c246031072510b107542c0760400b0290900c5c59034100b00c600f24010b901c00b0120408042e0302207104100c400154100c0c950225440e0786440d190340c007406400300b040d0355030b141c1242031184c81040405620000207403d16a81454141140301a6007405 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 633313381 1250 633312131 633312137
    0x41a090106050a051b030427050a0b030307060b011e0207150306120b06040f09060c0905010513060804170301033009030305090109030b070306081203040302150702010608010507080403 81
    0xc1c84074040d2080311030b015000c3d910b9910b001c145103d20841c003849076070705440314070050001084001d2501124200194280c0075a00e0841089041005640000786403020280c185241000c15480c000180c2e140958001c0000c03440044200048a928401030781003403005c01070104c6014625001b01d00c40054035421150101441501201036041d154070f80300d034280402d0784221500c00305590900450700200d00030004030b14080e04008450545000100c1900c2d001d950f214105000750700300c40d0072030040c10282005410000c4036002e80c0101800341c03046100b132228140c0010100f100e801c0c48103407800e2240300c8868983d6144e003003d502a09420002c04c0e0041d4003070f840341d10388626118016034110382a41e515a83c0a0035554100c40d1a0002ca40d580d0502100080100c0014400c1c0103007440303020035540004000c0d00d0003402c140303010204520700c0700980040042c000842c0c1e0101e491030401190841c0b81d9a6516a028100c0c0184041e51011440f54a06814401d090340e0004400b03010714060b507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 633314631 1250 633313381 633313399
    0x40303121e052d01030f020108150d06020c15040803012108071103163c030b1e06090604240f0614120115020c0414010302090f01030f021e041a 63
    0x408407000c061801c0c000034100781401c550301e10040d80709d24006a84041030000490401080d1000708158030b210800441f0b203260007103020350040c40b08100c1c4002c000c8900c4c00301c003200d0505488020007488180205403581800346405081020700e803502040c0315500022943ea1a400c90806040c1c44160440c0c41e840390060070808144410031313581010070b0b9004c0c605024000701004445040d10021010a03464419089692040a000301205070005501500d680c0300d40e4a07040303200440d15241d001c841c2e40c4400900c000d118080d260020801c0d48101c1c2070710002030000c09041c42040704402e055020542401d0040c02140d002c81c00c076860809c40780180c481000400d0030f491402e0090291140481d003a8020070010030440d4181c88404031011042d0060322000131444002c1015641e400310200c402c00e442d10010000c6060280d01a0303402400200c40205070b504503030f1904031101250130046c0c0b05d5503501c101c68004500902400d10705400081c010402050a0100391b00b03021660042a40705a24030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 633315881 1250 633314631 633314701
    0x1005090f030a0e0118050612010303020705011b060e12070c080c09130201030903110106030804080c01030c05030a020327150906010623070b130c0b040303121e05 71
    0x180d070315840312501c481d4082103a0f0070044408420718185140950595400001c00e80c5034480140a074610017044c01c40558150700b07020b0305c4c010b8645e00140c1042080c4020600d07101070512110650340d401400030071944403002110340b40002c01c02c0402072072140010500f0411540e00c0d0311034100c0c1e042005680c0b8426000b4108090140125450450241856802c1d401503102e9401280694824108080b451000c11582421601e0a4001b00c9105100007801e01494400b000b40340407003142440d0502c00b07262201d1004200d400080d00d9180030540100100f95005c6502c0031400d00c0156080e68044030300008030440d40d03540e140c40b02c040c020a0b9218040384004001040080c165600ba443d0710706030b603480125a4982940c040d86103401e2000c01d1240c0b400007540302290500a041036030000021298500b0011701c0c90550b0f81c0700607050b1404210400000740c0040205000300c2c02100f0020b02000e04c515040440e50a112400341102d03e0203040101d0144007003e543d040900142074009100c00b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 633317131 1250 633315881 633315883
    0xb1002160510140913020d0c03150501090b0a050c03190f0e0f130b0d050106030210030509070b07060912020d2601030f0c030f0c0501030c18050f0406081005090f 71
    0x40312614000242c603d400f428801d003940030082c440b00ca009009901894844000842240c100041000445d0303107503054401001d46c18060a0700d60b61405420351980c514000010744544003600c22401c94440200741001c092b4001c0085d0745c079201c500b100740d982d549501c5000306641d02c00601c245c0085014100520703a030758032030b241c0006002c501130091002c2c00c100c5010495040c0d1102034161080f034864040c8486a1a01c0c031800388458412400414040c2c1544108050020308901c0602058a40420483c803000c001546400700d03070194400b16078664240c1004400380c003007100003070001c50586803401070440d4000b40c01c0c0082c64680e69042040d80f4020300301034500c11880a0f0515010401c1c0040c004545194148100c140c0f0441030140803a03a00d0340d4442c0c1c070300d1181c0c50079940c425000200b01b0203940c0501494126451515011101306481d03040324000350b83c50700074280510440c6801c650f164071181c0c00302010b058010119550b03681201503000190004507401d5420303001b414040080080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 633318381 1250 633317131 633317149
    0xf01080102070314161b0f050306040302030301090b010e03030a08061c052113090507030f3326071202010815060d02070303020d0c02120a0809010b10021605 69
    0x54541d84a903031620301410811001e4100e00d01701c075940e2040038000400990070918000c46241c10840e2203804500d006146541a08240d10540c06a00700500f000b0010f940030088905440002ca00010285c140600403507006400c41c61030398040c840040d2070228280c00c0030441e40310301c104584801d400c8803500300d05402d04200d00c0b4001c249038041403946050040010f40d00403052180f900c0c2c1c41c104000540040c0301e4442981c845403540b541e4030184864a41e040c0075218003401d003680b00384480f00780c040c1d22400050380204e00c080d03d13501a03440107880e038600c48040401804180d20409003400074840044008450b8000c4c0b0106104284000990b0400c04119224907a016100d0409507a5044d099204540c1d00d000900d0748400c0c200304a2890302a244003a200c3c60303010759030040e10340d6640c0242800712a00780001c5400d56000c400c004e4a000d2024044600076003c500e0700c403100c0d0b114015500c0c054080c0c42c504a512440b00301c0f5201240303500140354a0000015000b40001d156102c062042c411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 633319631 1250 633318381 633318383
    0x19050105120a0303020f3001050418083603240112080f161a04080a03090606090e0a0201020d140d0b010e0d06050a1103130f17030901050f0108010207 66
    0xb410565442c00428025405481c600f1006075000f49490a0008554800c0800700c4000440710b501d00c01100740d0341c1c00303010aa03000d000281d0f000c10800c050300d02070301e540343c58108004104440000760b490301c800c881c0d07400844000c458401602070340c141c6851251081c04001449010340b10350303035080d201b00035a0800003441003142200507040b0b03424801284044485980c00795110141006030307907951444100240180300074680d0141c404e29081c80d2203400c40c1d615500074009040d4040078003012400110440b65200c51604002440c031306a40380000c00360a042d4448503083d407520031102003200300490348030103440c800d074203540c0c071026111001d890005901c201408049400d0120306888119540102184172050401c0122560040005100c0b500304032002c4071070300c0d00d541c18807101030618007400c40000d100e120840c0c11031801c142e1100c001c2500110280402203640300c03010601090034103c00243c100003506035035904d41071b00190701a0501b910440b40f104c02590000490743c0d41817007912155 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 633320881 1250 633319631 633319633
    0x608012306090405070e01060207090605100e01030f0b06030a051f2142090803150406170c1e0607020d0302100e01060f0504060e010b1305091905010512 67
    0xa44a800601c82c0388103004000321990b20510740c002c10356200441b0914001c01c0c6035801442c0c400c0c184003004007a141c090344940d0040d0b802020204000c1d4008135a400c45d0002031038005090151484058060f0203040902c40d000304c0004244403945400b604500e2080807a54012141d03003444044140c41001584071b0401c0b0740041b6030100c0c003c0c0c2507092008ac4441e000d8010140400c3e00100c0c12540f42d0501c90301340c0e01082c0f503c005075994404845844000040c1c0050420400c05542c454201c5407100030148010400b0519410301540c6c2c8951000c00980446600461301e03a0441001c55901c402c10b2501c14810034442062640c15200d0040800301100c2c06044a801d10b40343c2d90034033294920910007201075004d850303590000c5051078460001c91500301ca0000c0b07031152400e50b100c042c051241e0400d81c0a01d08241c828410800c0a01096045880000044c0e076190000407501000400701d4000381c1c0d000340c52a00f4082c0f440f06468110400852580782008103981e69000c000c65940681d00c6c1c0110f07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 633322131 1250 633320881 633320951
    0x102a0203070e0a09060f0912090f0e0a020c06040503040608010503010902150706091202150f070e0d150203070509033007020d020306070c0c090507090302090606120901060801 77
    0x18140c2070040712a040070f0301d8440815044403d076203040079154072602a107121a60b0302605400d0004603000020004103078205165118100341c0b55822078000ca0244031840070580000c1385131600554101c412031070701d0300103403007a45c00c151804640341e030702901c942d20024500f40008078940c507040c42404440c541c002c1c208040b0300b800031000c01c000d801090058030750550320280c00c0046281440b080c04116281e5002d084414107004042032800e170040c1c05404003818240070841d501d034102c48000b000100440740000030304c2e018034040243c64a08610016514000702c03e002c600c1350400b0241c10f102c00207c05031110340d0800c03a0790484480142042040010b0b42480d160302240040380182480d80c005000c000311490150046440c202055850200080ca02a020070030f01c540c442c1100060318801b00b0600c09410314007070040010380c440c0406485902c856000c42e41541e19441101d4030520805000079441c03414510031802000c0d03c1c0700d00c1d0764650810100904508054290240d500a4402c6940d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 633323381 1250 633322131 633322139
    0x4020703170903090913230105190b03150c070519031403070c15181109060a180f02090405070c060b040207081c02090303070b07021e2a102a020307 65
    0x241c1c3e000109083d0342c60181580030344041b4120b4a1090302c55101c034400410745081c80f0480d12b81c59201445900840b51a10400f590903580100d070071508001c41d141c2062071911007441144007449004002061171262030032649150070311208a10009003e601ca0b50032440f0f000d00d030100c0c50711048480f500040c51500600d00015008008400c086040f024000f4404103a24440110303200f007054241d130710311b8034103100720f24a282602e1000d90050003903440200c1b1718a0441c00c00794800300702c400c10b240c403031701d410854429070016419190404c400030014003803410418000f61040020000540d04142462820086d905190080302e0160303622064841c07501003000c0145203206168452000760301d408000b207400665040000d406001c4c000c003c403044604054001030701d800c80d00c5115904010059080c0500307040d011940680442d200140180d0201e83e02445041555081c03401903403110070201880401d80d48501d5070300310780511180c820807641001c0d2003a02305139051000290f2650040714240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 633324631 1250 633323381 633323401
    0x3092401062309030706030f0e010b031009051912090906060507060b040e010203190509060c16030c020a0801020a1101051303110a1e0203061302060415020705040207031709030909 79
    0x158481688840c2c00f81008030301c01c002810640a81e2110001a41f41d508101001c2c500307100c0d0030615004040200441c140d11030100340c49000081ca40d00940f50380c0c00d02402400320500c5940b80610b500e090140e244500c52600d03900300940100070500151200ea40428001d4140c07280906030b80c000e40b41c25081601030381e1500003902440e401260415240e100e035984001090001c0d5000f00700142c200c90006a40c3e140715022280c00520b03620307807580074005001d02e41c8840700450364007600041180070b00b8441410300340c2e0741c013844003c002e41103151500d0014540030194080c2124036070951342c02d030142c03000b4882d15083ea07900340c031851402c0103035644910000e0b001d000c1c032078110301203034066841d0400e40b03445045007020100c543c400d04650800707449045103824001d26a124400e2404c04c1c0c0701492a4010541034042d034003c44908a01540044080714000c0081e40002c01d001001955142c40d2464020018016401070012610b035003000b046074024040103494150101a04030340c00c5036070b40c40d191 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 633325881 1250 633324631 633324677
    0x7020c060c0715020d02210304140c0a241409010810090608010b0109120b220b040c03120f0215060a08010c08011a0903030f09150309240106 62
    0x1000742849441c1000910201e99000d100700c00e42140c0141a45c4c0902007000b03030802e0072541d100440d000c100c082c409081d001010550b608a1781011504030800031680c1910303d041d502e460031aa00821090001604202100a0011003108007241c01d01d1070802081c00d507040e007002101c04155120900013040b45520a40325240e21010316007070381e0410b9030b41c0c001c10011101c0940203100565180c9084001c507580001c0c001c4020100c401000c644401c5640300e0020f282c00103810428130803041000100304502c1001009090750f004803440901d4107185c9061000c0b03c80303511046400300842881000d80c7c902540342040201d07655005488241121464488100c03c000c01e0a80d0204040a0102d001142481541d0300d41d800c40c0c4410611f541003a0100101629200180e4a0a0020041104240c6000c019507000c8011500310742e480d030700d001f030003c1c20300d902510300b0704541d40000c400c000300002c001894503044010401d00c4018010f5440b003440c0c400409021329000301ea0345a880d201d418010a040b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 633327131 1250 633325881 633325897
    0x1012151b2a0b07050405100f02060c03070503191e0501030c0503010e150406060e0403030510050a1a09040f091a010b0306010804230105090309010306090b01080103121209080a080601020607020c06 86
    0x100e1072400d1b8844d40003a080f601c1c1c03400c00d0000100207031594140d180d010001c0940001036211503030f08600d00510014450722008101c04407001d046080c0f509d80790183d4002036501c8021508000d041441d2820101c0240001d11095500520f034501c0028113040601c10704074049d1094003e4294074010356018803030f0719000784c0100c0705c903941d500d0005105641401310500a030703c40d0341c0102e603904000c0c0c64038103400c0664010510489103250704101d680c526003180200300c0b1216503040d44a41c1c05c40000390040c44809404d40030b0600b080004c02c10010400001c00186121030176900190342c94a884c0b960a000480c0c43d24042200140484d010480c002d00007400443c03281d0100040c3c1540e02d00c11425603900b030b9516500e50b0b002003100000c560b0035010740405031802140c2004141100c02c0020f10f641c1d018440a403009d80000740d110100352007040081c4445030b0102c0140070644061509900d1503106511820000e4400000b00c1c500390b1000c50803901074882a401000a000c2581c200001ca50001c25 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 633328381 1250 633327131 633327137
    0x70303110a0f06050a1a0f043b0d0302030c03060d11040e0303220b070e0d050312070801120f0305180909071d1012151b2a0b07 56
    0x760907001501000040b03a0552048501207902d040400c016000d583c0c2980b400e0b5038500b02c0c1501c202c0c0d0f54440803020074210800b1100481c0441c1c901c000c6a1140044c0401e90003006034a0074140b030304800004251034500c001d10101d070020701a010046007280819150380c050107604101050040c50320340f509198550140c42040c1ca6100d1810005007128541464402150800f0040207401901c016002113108800c1c108121440d290b43e6400083c0600202032505000ca105020303030b000e46403403152001882d8054126aa01d0010029644c22128102c7c0d174000011002c20010030a0101c2c14000303031541d540140041091107880e40c0c1239400c2d41049040301c01c012481c1c0660030300b503614028001d00032400700700035014a6080003480c020002507150303001c0c40c140d00401407044008074024004112040090b5500d007100040c81c040311104210302c60304403010300703100c0342074016617810342070b04800f141ca62520355800e0251000c0100314403411100320b491015441c0d1035000300d00001041c03680130302681303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 633329631 1250 633328381 633328393
    0xf0b0a140c03160c0f0303171e01230a080a0212030906040b090a1703250b07110d0e03030a0e0f0301020a090806131709040f0c03020d060f0807030311 66
    0x2040d45282d50040d400400080340010207070f000380003940344030402403e1a801805815400c41c0c80141c01402c140e40d829401458243c009801e69824006602c0c560a00e421015204c2d65140c0304142a016070312502018080c1e811540c00135840d010256004458907200908404051034080001c100309044401c041c0d40002c100314089583e440d4010f20141c09502c00c40f9071070346800024400090340a80100ea1b5003031844e0400c006981c000810349a070b0804030f006a0840054282c4140c440145224000380b200c201642800b070455001b8181d41c14400403581145c020b5545424202e030181e008402460301900300b0020000018032840554044000142c8221100e00d241000b1a08a82c410149000094a41c0806024030101808099004055500e60541c20812510740d1403aa4500140c3c2000c01800011000e1150300ca50b00100307440032039000104814012602c0c00380c0030354040926810000c4c507040d008161500c42d41c1c0e214091f40c0280b0018900359095950039111a12511b201003400c2c4621 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 633330881 1250 633329631 633329647
    0xf030f020316020f01020f040b1c0c11010e150a0e0f030c0a020a06030902032a0904140d030e0c01080c1603050a080603030313060221010b130f0b0a14 66
    0x68001580959a00000d1542d0350061a800034141881516000040d134010003e4440c1c80d03114005440503104451191642d50b0519901c01c08000002809007a81c182002c0c190b0595682000310500c41d800100300902925000142040d1218000420161900c0800b004110424856842100d02c1c000e0803044864004080c00c029142d500030054000386607001c03002450443c02d113068050000c0400d414184010060307503001940340c603061056001c81c24030310181c0315191a0000500c40f26690042c0120b003183c182030401c110603041c8903030034603120300c100803c000c0c050741b00c1d100354401c40c00c02001901800b000700004450701500502060f540321700034065081041c03007280c20180f9071486500c41c0d03070380d0b41071259002d040c20600806151194005004000741694404000203090f40d220344010b0759400100c0741042080040103895955108000010404403140e0700140940707070511a000c2d0005698115414000d0405c1c014001c0c40c035410301210641900810743c141c0d42e1401303014158100446 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 633332131 1250 633330881 633330911
    0x140904090507080607020706050f160f0221010c020d020a0f03090312050c0c18072106060e0414040512070201201c03020a2a02180403020601080106030c0302010f03 72
    0x1ca83c11000082d009042413100642e0108220b000500c01424080d0800e1500c041408040c0104104152016000c0c40c1070010089010385009103640c2c020a40385e039021203000301b0b5100e0a00440510b11941c606050070341e07101c3c00010148241140741d07000340f800107460303515203504640701c010071818840c00c1103011000683c5410f5240d02040a03545003030311400d07402065450200d04421290080c0d10312402a000c056906e48165406021402c003181c4800501c0c0c0414001140040b80c1d68050345041004541950300801d54003680904032810b20000213024040b61007c007003910001e04c1940120740800400000303001524078a401410204c2a007444c0c0705949080e01c83c1300000c0c8986420101c0091148040001e00200d52101450704508101483c8070183c000410b020500d140f1a00c184c042d00c601e140d506601c0707600030341d002d0144803881c1e0346201e0401041c1802c0c1c07011000b60150b400081140300c3e0510440c1b00700c1e9001102421103034035540040d1040c206407503c840c10142c40750502645409 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 633333381 1250 633332131 633332143
    0x40f0504050a053309070f0f030209010b0c0d20011a10031109120102070f0f031d01050405010305060414040503130e0108030301050103020c070e040605010e06040b011409040905 78
    0x2000307070007500b40714a41e498a0380c1402400d1580100c4007000481d0b55900e081404a004044000d81c85112070b039131034510202d032420720664002002a01e01c45404501c2c14040b21742401142c0c802d0740e2034a032a0341c807055603082a010700c084420380707a84170380c5003072000610030044090022207032040795000c1c15010340050309407010749408984070820130300c106809041400d020b82464819240420140000911000c842d01c901d01c0428803503070400300c0d045210942941100c1100c1ea12881c0b88074040303014036060b40c28100005055000c07a98060005200101e044811031804005a5a051a00b424540150b004080151105402c141c0c1c0f100100454842c03401282d01550080c001181c84030f20302d200b640a2842150400d4090b00c24100040100042c0001035905540007400c0140c0c4905c0f5202c0c050345030546a501c1071803e0880c10092006000c0103911080c180c074240806940580c2d54030040c88203581c5201c40c0c00e40041c24280c0ca2054400c0818068151305800030000b0a90403001c2e15068079000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 633334631 1250 633333381 633333383
    0x101503140303040c0e15091e0f070f140301120807020607060603020405160801170a081210050d03021f0b0a09021801020616050d0621021806130b040f0504 68
    0x241c4000207002c2402070804400b0010130304404154030074540b4048083d180c441400c102c502901030b50000c220a60603030b0742c8014024917401e540034801d160010044000a0080d40c5560101d40504050109030f8816004512902c014520091459203043c94000c108044480c003580c0d01e81e028490800169140c1d001052200e00601010605505600400c07046030009040109501944c3e414403c07840d80011300d01d411560700c0d00e0402e01ca101c41002c81030501491202c01085078070000384005072848542070841c0038444410100c801c0984070b10500c0790042202c2e030080c0150344210402a0550101281c080c4508004013003c560441c00b58003254080845400200481d9000700e411240820301c0f00d985288114244010326a07801c0605410040ea10500300c42c50802a0000c0c510041032101c0d04120010104151958039110131a441b922140e407242c0b004a2040802410380c04040383c0068160b80619401008440d41e0b000d110b489100030106c41d03800541180d200c44960540400e03074404c0502c25 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 633335881 1250 633334631 633334633
    0x302060705061509100308030606090406033005040e0601020a0b07050901080916121119080d080f0604020d0e0105040311070807060e01030209120609280510150314 72
    0x50800c11200e841541d6075244650061306090200104002284400b408903900464000c1d600e8440e0307008101c0311b00c00d580380e05400c141480800810414191603000010340c00e0195100c8030f00104d00b14500340718940010700e0010380c06000074440310004030822a0000d00500498030801c05680e2042d0380c050b411184000420004034800e1425604406c00719070007a843c0024204061101000c170240c10f01e03e010320f09010a07101000340802284980c1e80c1c0101100420400781c02500d81d01e1001d4142013806450340500840791408503080c0280742d65800f664841e960782d011650b610041c00000d401003080400081d0300c901d81c207403541c2400e22035076009600a40e1405081c0820051241c600b0700d480d404001c8131f41c0040010001c8591159103560820002d00e00541e5940940000407030920070301001c1d80c22402600c0520441c86000a40700030001c0f0208103607500d11a0304070001c05c1c59842d41c00040d100b5008401e000290352a964080341c203035120703240b00e0b0700303103c0d12510b94103840300d80c04c1d101c6a4070b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 633337131 1250 633335881 633335893
    0x905010806030321060a21121101050a20090919060f0905010609060f02060105010509061b0d031a030c1207120c0602011506050702090a021e090f0a29040302060705 72
    0x10f420301142c00d001401d201081045100c494050790f1240200e180000f412384c00041c4400c0023000e224075800e048c0040a50001e10040c10b06c0c6884030010703c1225410400c4c1c840b00d1080c0f42c07104c5060320542d05101c070010001811541c8804e10450303640308146184600960b030308008104040e0303980c82c5002901c0600800201981840c20240081b180da41011b4184021040040700560f8001200c40c15100c080ca000c82d11101c195002c0380c414040e404880c02e85030306000c0400c0c590880011f8415030180982c2e800d21410311107800d80d140c507a09501b2000c1e01600070112100d01030510150486905030a00304940e0303100d543e000321100000745048110f402106003001000b190350709024001e040190680e909030348524060005c2c0080c4544800280289500307400100e40120540c1a41c422414200010000c1c901016a40c001d550249800c00e12805121301c00c01041d09040c3e00d044140d444000a203120740710111700a246510303c01c0c0312030704152000c000101c010b854080213049c41c188200700a00c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 633338381 1250 633337131 633337141
    0xb04110d240905061504060b1c0501050604060f1b0609081908060f1009030203120714121c0908043809010e010203070c0b04030b070507030905010806030321 69
    0x2503640825180d0307016540c00d264a240118a021441d1504060303007003c9810303209465804900035000580c0a450340500c08201c1984030448566220100c40d8004000c2000eaa01e49040080034040c5004010000303d000912016060003071100391003901e503920b100c021141d00c9a03208810382d881c01d00d00719540d0782c012440740d019520486501d070000780103041c080110f20380800071070116200800c1c0c0c41e201e40c0c003c146c0d40030190b014102c004091b43e000b9040d180e039080180d41002c110f500009007200c0020707280405605840000c00c040a11040d914151440c024441760b059007100000f41c2c200741c4d02d5584565600010314010018001010300000f00d100308002400700045946242c17138198454541c0c41818028207000108994504200342003142c5d00155010040380703580101b030b1001388040f901034004950700300f80401400440c0d200d1a80100d840c0e480041c12520341c007910a0040200b0400c20080c45298010040c50742d1240c000303012242400c0070f00409800da0344a100d82102c1c0e076010401804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 633339631 1250 633338381 633338423
    0xc0d09060513021912030c02190605340809150711010815090402010f0e04180611070804121e06050108070f2601060f080d02060a0908070b04110d 64
    0x81e180320100300c070f04c089039140a840c00c4202d29401d40090070003116940030003c43d038034482e0240007403541001c207001c100e4807510003806036846080651800718011180d071113265840454001c000760f184416880c0e20000b03a403040883e41191000700c0d805610f8041c400c40780314428001d4a40140242e81204038400300728005803c1f5034000d810041603012405982e1b840b91103001680360466820710300411030450050045030310200180d205a80141040c0707280b0201c0c501c008408055600862042240e500194071510780c600c200231000b09810814007081001c4021078504039050303801608141601007104000101c0038200000486019680f0401840301101c100801e03405001c80c21210b240107828254214076400d40080c400c4121000c80c510079081e00e5080d0060350081000407030301c10055465020054940150b819440c1c014404da400207000c1084070300903124040d800c03008042c60300780e89458059010000030000e4440e0b103040140e0070312988030000100c402e103000d1692412459100103000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 633340881 1250 633339631 633339649
    0x150402090a050106050712030e0d0c0b070905010f030c0e06071b08120702060c0705030307030c060f050103031d01021513020f09062809140613140c0d0906051302 71
    0x41607401d18000040c0079160300f00003140d05480e04004d801c1e0301c07070a000f2011405005200c2c108070f900d008500407e050f0a8000d2104850b95220310300b44003455445900446000440e4400e1500040810480d25104c60007a844044445110318050002c041900040780f8a0350012408940c82080c4640c5d0a518426030030b500b4024128001c05001031107200007480246000d041c0001c1c1c840e940000d4400c511070b500308207850040030050181c0307450700403604015000c0301054009841031400e00c02c00c504440c40358802d45050780d078141c40c0d01660214610100c182c031000c04010b03070b041d442110b40d0240e001c160031708518401d9002c0c900700044981c06106010402c4442100b130341c015403d070004d10a1a9441c000a02d58003c3c4e80010742c21501d00700100ca84900702c0a03840910b005160982941c607030071441284d0b91050f4000d8428031690030000802504880d81610622405058000440d8118841100034441e40e00b407024041030498146d207608089800603903600c0d0040d054103c8040031030030312200c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 633342131 1250 633340881 633340891
    0x10021303061a060d180606080c10020a02010210020a200f01060602030412123014041203020307020a02040f141e011514030403020105090c04020a05250515040209 71
    0x307519442d03003200d00499014003c0500110500382c640c0c00d402d003a488075640030f80c9a80c2c0c004c10b003840f20558480503180c64007003035040d260084040304000160f26000007452008140c0c1030b801801000056402e81c8000d401c80742402c1c08100108031200522040c1072501089880040040e0640d0a46070003244d007113440644c0078a080d50070510042018810f01c3c4040c2d00e071107810283c8201412020a07085400311100212110b0003504100007800b2000b40c50120b03031802c025540100664080303100d41a240c0801140d0040511544030100c1840520940156400c101d0b940110b504980c626400101520035029880080660b01d9a075500b1481c800314890740c2112a0b4042c103119078801600007016000140103011a0707054200c69400b6862045841010b1028a00c000b2601c9091a1a00a000c0c0a0a4800c4006032107441c050042501e86403088642000c95900c8031450400943c1400300d0390030b10340d080d02003070005850010300480d038180100c1c99040700e05a1000001d10f0035104100c0c0c1d00300040c0c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 633343381 1250 633342131 633342161
    0x203030c28090e0117030702040e070806070e090114060306040f230912031312020304170616030e1510090504080a020d03020f03010b07020a0b04090606140a090e091002130306 77
    0x16103617002074008012540c40b50740588001ca200b240c2080030354501804d40e80410810300c42d220400000c0c03680581d00380055142200d40940c140d0f0ba54880810350741c0f0810301d00c9da100d582000414150314095012600d211800040400d070010300382e01d44003114401e002c0110355069540c0801c40540010f00070104a895400b10090441c100749040203e05000314400803c02030552110b140c0b164020015540106120505591450709007642e83d610703a54107917a401c00e01440d05c0c4a14a1290280c050160b19a080400a100c040c0c001100c001d8a50400f4200410120139000003094804144c000c1a00c103c0c01030034640d5070790310000c00003854044a0910b0038201031042c081c800d4000424005c603411110410052501c5040600004401c014298404c802d99000000d0004030f900450700100d0407034249442da102c000221506150071445003400c202c0006503d1441400007110b1023030420740000020b001c60b5002030702c0d18407030800c90b07120303000310718504482002c2001003041a01a004850710200303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 633344631 1250 633343381 633343409
    0xa15020106080a120c0305220302100e011d010306120507060206010e060d060c110a050607090f0f03081c020408162408062206061e0203030c28090e01 66
    0x1384034080543e10303405a000c10441480b1030102070600c00d906071414039102c40c2c04101011080100000305001a21007280a1205200041200390050619009100068440c140c221502c030032468483c0140d196001d0626940305004503101800250316050240300d41c0047c40c9450420030080c0c80c00300d05a0103600301c4061030b010040240c80d0380c110894415880f20001c0740100030f100c02519000f0000b410041079200f040f60003005d012700000c8040c051207854999141c2d041c5c4a0318010800c0d115401613103900078040008200090b2a0001805011001d8541d00f5012010300303030041c1030341c0c1f00d503000f01812b601903031603420352907a4542890010418501d6400d80341030042030040c144a0103003c498240880030380011041e4845184001c50000c0b800849416a10348150a400a01c15402120000740c9100044d45203070480d50303148010307440d90303800860031903496540441d10369100c40140366070710006a83d81d91142007524402c001c8481c180d12041c1c0c80c00e05003244c0700c00a500c168400c102c401145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 633345881 1250 633344631 633344633
    0x60909020a0f1a07030c02100801090609020c12131805040b16020d230d020c10020c0a120306030f140c06030112020906030a0c06022a130213050a15020106080a 70
    0x16102c0654000014030001e42c5400c0d450901b600c0d800c0222101a4100d99040c05500f48650300142e16810b8500071501040103644500d01c890803401601e912031515441040251400404e040c0a0428042d00e0290002c1c0951550100030b08441850800f81e9681d48030400c0c0004c0081d0481003d030702140062260090411942c0000d5940303544203c148184648083c10a4003401c104100c14001d404030b8001903900c40e8007014803002540041c00c5101c0b54094541c4200c0350095a000b207805036440f500003811402d003551104c0b2180030b024070003c018581d41c0d080000c00152541d02c0039050300d025510440c9254034022507503082440034418140300d60010030042c021564208451181c8540607284404142d407002c001c08d2410020040c050100c2e001038200040da1540090325901e00702c02180c2c480c54038080c06d00d04180b0101c8414040e03074020b2403c128048001302650203450007401201c4c4055541e940c0d040800c100d460300e0342010200c0b1640c250f64241158090080c480149500c2004000240007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 633347131 1250 633345881 633345899
    0x608030a020c01211a09130605090a02032104080a0f0312060509070e061b01150603110409020304050c1302030601141306050313061b08090105061f030e01060909020a0f 74
    0x10070040548000d40e034031140800714a040b0b010750b642c0170024110016a04105e4007000d107002c4042c100300c2c1c01605040018091036001f00b510102d095001c1d0051207080240d40315000360050b44182d0140485041c070000444a4040080920440c0203030240f0b0200180341c103004002032230308a1120380b5642442070400150301e4010303c03294171400c545080d0300c0948080d40081c0c1548901064030b6020f800a8007003441048042d80010030600c1400901c514440e41c074076080d815201c2c3c9160340d0301500401d0100b00a403802680066600512034000d40c0c0c214641b50002401c00346c01c400008100607804000c005165801c010082c074600005010142486014404404240340d07501404080001c00300c0440c44020f412041c103a02c4650180041c000d00c00c880c0f0325042401400000c05000840d2400400e5981206100380741c0146030190001d41440a403c0f03903070309500032645000c400c041da00d2003d5600000280b0601000d001c000001040140e01c9004000024146401540b04180120010804094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 633348381 1250 633347131 633347177
    0x30903030b01020d1e020c121b01110601030f03050d05040c06020606030304030c03110a051e010e010903030c020f1f0c0606080102030105061e1e1b01060f090e100608030a020c01 78
    0x42d0312005c1e0406046050107d0400d1505e481c41504032610310742c1c000b441030011070109035030b10005840b4003070702201400440d1130030112103881005400640051010400c600030080c0c03068002d041840c41c0207441d0100004840f8226000d854100d0100814001158140005504130b00c04400440c103250031515200000d0300b09200040042c1400400c2440503182d00f4001002403400900400710b41c0c100d803c442a000c049401110b000445043c2c190090790701902c0c00702c080d280c00d035452000b044020b50031700c102903164443c8107500007001c1201d1902d14600c01c1454034101039950381c1809080c601d203408419a0303802d4000c0741403a40180010b10454403540e043d40d00c049250480791007410074a450a042510949040c1d9030f2070801c208009003441144001440c1615000f520841c43c050010700c40c40c00c0b5800780c00359019071020322030308109240103a000814203007a1002925844004401e418040340c0b284d0344480707903c0d0408900c0b010f0b0a601030004280c8001d0a080080d6100d00d50b00e01340c5c048070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 633349631 1250 633348381 633348407
    0x20f030f032a070609060e041e090f0b09070501080c07120503150a03080424050406050906041d01081c0206010513020903010c0503100803120a02030403110d030903030b01020d 77
    0x2000e03a00034078a80c0c0b940741c0b40c6120b507002200c207071100c1a444400c001c0c4103801c0ba00a242c00704802111b0100e0f5402c4c54801c200d50055030514103c80340c05a04400d40c0580440c1c1001d4a10300b11074003414000c10310440107079005007031240041020b41d1501001500c030071001004140c8810090100401007000405407038031030071162510710750700d0f5140c0c2c2e2480700c598a032201c03141c1c1001c54001d001c020044c01100038020380300464010540008070035042510a041040e10200050081c0800c0050500480261194240c0100460306054940103140d0700041c83c607a03403159a0383ca2200411450a0a00408142c405000031442891a1002029517100d00c10711606010310710500408408131807542c15114030303001c01002070152445040004005810954910400e50f912100c00200560000200d13840c0010030107a41501d80c0d0b035051444000c0d08000e2068050008a640d03103242e54000740b00c00c02488195072000511a082d5040c02421101401c04c00d5040d54000e184011300c15402c0b40d2001000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 633350881 1250 633349631 633349657
    0x1b2013150e0c0c1c030533060930072301050f0a0306081c080c0d0603020d030201020d050f010e0423010e07090f1107120e0909010504020f030f03 64
    0x980c40b0a40b140c0352030710600d10328002a006048030240d20320302d0a0358070038000456a07010300443d01c40c0d1018980c0101c91000211151100751211000303000100c10b1903c03510300042105003400c918030702040300701c03644601c490141103400d01030400105146c099080d072a03038800000e1800d07504160300e1b28010320180a0424500d0054189010260b03c10811540b26802a01c001911a08000c2000e80a041c136800741980c18003442c20072010f02086012640c06090240d52002c1640d10f84124a583c1c030340c0240f014005513500c6c0c030b00100140e00c170f120140091600c6a4001030769141c1c075400720421180301034540700045c000c0740d00411291340000540d6400640110009020130714004441404481d5000d80441c1942007074103503c0b0310b400105859003141c5101c03005000302450300d030903403088490000342d400e04660300740146c60204406100114248599017800b08040341003100103107a264040320300c00b0450f03450b04100003c6003400c080d07081400344242e00a040e983c00090f07000e070703c9000d010302021003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 633352131 1250 633350881 633350909
    0x3030106050d180f030f02031e0708040308070c0f050420030703060306110a021006060504060f09080303010b0903010e06040b0601050903190807031418011b201315 72
    0x802c4207a0b4070042200700d1039600b111103c540c42c5082e4105413401039066002c1090440a02c85680c0080b00b04c2c1c007030010241c509003840c0301ca00405486508400001c1c2c580c55000d1202000280205c0c005250081c00f0315084d0710042d103401d80025004e450364011034011406d0100c0080b9241180d0070300e140d2018003450301c640f01c0d510150201c00030000c55001170702c40390425248500002c82200181060b104a0342031b14403c94000c040a41924420300c108400610200800c0010f01c1c8a0b641c0d01485412501c3c0c240020f565401d0461310750f400a0b00b0030f905071400041d440c4d100d03140034030494980b00d807518040c10042c03415403624400326100804041c140107001403860520b6a007440405814800c0f1842000342c1d061a050130301c1c094100e002c2c2180400d80596001d41d100707120109a4a417180354001484921259000444003003e10a01d64131804460824140000354803200b50342c1c0250030302d800c2914081c1d5440400040d06003a16500301c150b1f19002080440c0c02c00c800c0b03080181c0340761440ea058 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 633353381 1250 633352131 633352147
    0xa111e150402012607030e060f0412141c0e010b22020c010e0c010e032b03141609050a03030c200315041703010602100b0a05040c09090f020306030303010605 69
    0x4250100d9410a84e1540c0000705800800c9a4a40d03c50301483c1960740801c19000701c1e24507141d80e5041620185000e1440c0c500180010303000c0200d14080015030b14105250800044048256030400030340c59401030f900c1d04030000c4c03480c00340c45048001c4d91640001d0080c0115203012900b07411b0507a0040071404030481034407003460000d4046401b8007110000800203240c0301540103860340ca0080100c0e0001e032030030039294003901d00000c000d951a0b10075608140701110311103e051082c94017868020030305072203e0410329860041e115441c403890141c0c020300307010406110b006292030b1607508403601c0364402040030b00101e41d00410361410710303500095202c2c2100400d0072140c2c03c9915844256818810b142c10b0841c8810b49a0034540a41c0c0308800443d222480c0e001c41d0f9503540000d000b09001030340622400765884003260441d441d06040500f04044841d280ca0204083da200f188114001c60b4124004100f0561030748586070007400c0840045065083c25400261070381310600c680c2007000710204184c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 633354631 1250 633353381 633353387
    0x512180904021906030b0a050303071205030403020a0b041a070503150103020c0102040510121b0c06200406030c090f030f0b070e0901090905010c080c2506020a111e15040201 76
    0xa40c03243c180c086282c0d48640d00c4000401400401c0011402801c0c1e1000020340740c00c0000691391151341c000f01d50300c2c1a0000700390482d101e8100401c21b030214440d10303814901140302e0403069800345000d035202d200781482c04880b81c280743c400640320a041001c1003040002805000c00d0740302d00b1403424a070159446414030b140c40d001e80119001035a202100b24000040690402c40801030018080014403a0a001c00c050030141400300500d680462102d0080b8000a40d0980c0601105821402e0340d2000c0705011003042940c1d082900181c0200b039071407040820302604050010001c240c2e014200184500355610040d880003907050082200c1f06900204e0a070b40d000315080c808070070020b409400c141da510105a4068401c10368192680d5107408800c628a078444c58200b403052148507181480e140700c0c000252080b1540704103c48000c1000c88816001591900040280d0107081d0789030b07440f504c00901407a080c801c0c001030080c00000c100b98103031006a40850644a00440128140b009690b00d000507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 633355881 1250 633354631 633354649
    0x60b0a0f120c0801110a090906030507090509030705070b0919150c0519060f0b040203070905060a03020408010f0504050f0f0a03030b010504090c1701120c050405070509090f04051218090402 83
    0x5100f00b0750130701d071701c0700244e0451201401440b0116947c040d070090752201e90200701e498500002c1c0c2140c124000520040042d500302030341000c1c0c0d0104913494225940c941a04144c055005005108bc0028a6544600e07023009030011040381060f04030030351031070f2103540001d400402c1c10840901034003082d0038041c840e050043e11820b5030290131601d00c059141c6409801001d034005034400c04c40c9000340c140c2c602d04240c826240700d4403440e10351005160600c41003094540010b000300381010f03020071020442c010280540c1801e140c1703059020a69091034580030341002c1010282c8000d84c0d1103c0030b001c41c280400100986030503007505000070600400c800488062003250001390b40c0506142810908aa1140b040a4100904024021242d882c1d038845840c1c10001180504000c104007010301c41f071300d8a54032485d0440018280640780500880c0802c0d542c4000300c541c0342c9440e030b2810400007072000c2031142d00d100d548540d4009280a4101c9079000407040b002032010700075801e12000a0440d00e85c3c40070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 633357131 1250 633355881 633355889
    0x503150d0b042109140a1d010f060f0e01120f06031113020304050307060b040b09040b09010e07060203120903071b06120203060907080603100e010f180210050a03060308120103060b0a0f120c 83
    0x6000324290319403c1fa182c40030030138030403512003520559000031014440c0e14280f540c0681e86c2c0e1085201d80e11140115a828614886200c1881d1341c0e03d100c48116895109580c001c600c40c1e1021411141400c0410040da980d0080c0107010728010400c1000040001c800c85a00641c41500083c000c8900030103e0f004189000e42590800f50344828042800000c00140d80f20340b141030000d0200f0144244900c1d02c850039480340c000980d10901422254507584201294040c9502089a00f000c81503190f01400c15036148128001c900903007007d016417540544182e840803001d4205504c0c60130544c002c60039003100100301e10200140c503404070b9030b2980c1c10301c840d409003540c001d018400c4400d020040c80c000c004114060b201d0a00c0d100c40484030f40a44c5908250450f001000d03140241e92100303041d20242d0150700280101a6180c0c40407002030042c001030039480c5402e41241c601981185080c004442c0201c0b0b0451090110010800c0f01458001c4000241c4404004004070f00a452070038040d1181c40c1d400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 633358381 1250 633357131 633357149
    0x72903161b0213021c0b0a051203090d0c0509090613020d080c06090c1c0803010306020f0f0a08220b01090b0301151d060904050d0503150d0b042109140a 67
    0x540f401d564854010f0488460203404011092281c002003c04594110f05026000303600300500300024035001c0d1034500d4089901d4181d0341f5007544040010380f12a00708504442d0320804000512040c105000d4a0794030540b00b100605160810b28081100c1e0340b40c8410082c481e032150170a600c10045550140ca040320001c40031a20700e070500109254032600200000340c01820020300109140c00c074424071464541c0c0101803a840c503420f42c1c440384041d50004050007100501005070b0040c52071b0400040607401c409607501b840a04004c4190070307d4161254640145215484e00388011902c6610000d044400c98400010a1401c1c040840d0251248041d9a801100c40160000e00b60010705140c000c150484104a11250794001c02c200c040c04040e50050919072100b591034512038080c8000315041124100c01c5514500b14000186900788200c00031520000b11a09001c1002010341d400d02000400003e50074181c01c0c503000080100b10548540c850b8200000188003941d2a203000032005040c080c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 633359631 1250 633358381 633358399
    0x4081b15010315060b180d050307030207060905060405030316230102040e0601080709060810330f0507060f091b03030f050a140d0e072903161b02 64
    0x3241400600e2091105549a810f4a403002d14004a0b6114107016165080c10150a000b141c0007850040072840c40784980042d026448080451000c101505620780319078020807107682050001072081030f207076011078001e180a22050026a401000b5101d10300307c1969480c0714140036040c0000040090411180f07110048045102100010b400401c01d48056201c051450344402c4011503903010100e441d180041d0b05000103001007441940e209810240c800040c40420307403141140e02140070501642e541d410403402c3e4001c0403040d00003000406160b681044800350140c044050b205216000c001440c41c0e82d0b9003102010b6001c29400002c44641050300d201200c072112841902020341800242c003c9940c94442070b80151080c000c0300c50509040d03481da104061181429843c50b00540101400c05855402c1100c0050040003000c0c0144100d00512040031001d03078403c09020040203400140381010030403c206400c19001240c5001d15919194072401c01d008685807000d482158000c0d4010442 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 633360881 1250 633359631 633359653
    0x62915120712050a0902040b1917010e010f0f1409031c0f06080a0c0f050d0f030c0501050405160501170c0703090305030a0503040b01080c030c120703060e071d0f04081b 74
    0x25521017101e40e8400e54007000700c50b0440301084030555820300b4005107007080050038082041604a110390800362140040b824914900095003950041102000c0d021342c0c528805c0c0500e0254064040305070343d152951200340c00c06544081e282c0c480d0030010020504443c2c40301100c00100d5015041c040e040c0e810030081c280d00d88000607104c130703104007060b1030040c1080300210305440d0702d094010031103000a05461410304980d844105240190909509100300030403000301160013802290b204500c16409000860300b14480c0c0d41701c001040d000f1504100400d81441d14070b0141c0808241c002e00d00c540015140ca10030b2804407041401a00000c01070b000105801c07081e950840c000d5030046115940040541c0e032602c01c0e196841040084296055210354640300c01410090f140f43c54070750114082e1050551a9181e980644111075081c8403141e020b820200f002c0c2d40580910f41d0900740340d00d40800e4608084e0703056031b480341c006040900198000103e8140c60a02106205501c0f01c1c41e2041c0d401070110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 633362131 1250 633360881 633360901
    0x108270f061009110406021b06090603100306060b090a090908090a03060204050406050103091a040219080f0607080601080705030606040e18071a0a0806040906291512071205 76
    0x601c929403d00e81846030455100e0386000c103480555503e03a00500602c003010710300e981e1000328031840ca500031800700500e00ca241c8915008500c0350081c005940c50039455403810304c0c01c4880c0c41d44a03251801042c090303c0394a80d41e00c2c40d280104d0f650003c022034071528030b0510a4040c8900070003d51301900c40305c030000400c030702a0080c0c0704a41c1d044030100440740d81c075401074041d04d1001d14014108078034880036408062074002c01340e400500191124540541c503020f43c0307110301c0c0550400ca102d0342c814503000d00c1c2e4140c204034041e07100700c0c030749801c280905025002810b40c500180404040c0080403000440c942c9804040c1c50003404034003c041c2c418202504500c2000480c07103c0716141e8050464003082c03000d01c1940c03070720450350840065440c0c8a20480102e5400d100648401e0b441900c4000c3d91001c01c2d0103004003605d01c100c600000c081208007600b4040e04040c400707000c901614822110404416600c0c0035078040c100e5480169202d960303010801c8880c180e8807620203840601c2e02d0140840604 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 633363381 1250 633362131 633362161
    0x6020304140105190b060304020d24020d060305251505120a06050907080f060609040e01091101084014060604110315010c05070f06080f01050108270f06 67
    0x304402d4100145e030014803d01055120443c0c001c0d42000710a00c0c0d02000481810941304411580200c090390414140b5045003aa440300035002a1162110300920a1100c1403251004440d460720000c01c82201c1045a1103046441c0c4c8203041120031b6810480c50500e0290046403145490130301e13611084e140010481c0020b00c614058140a940c0a0001130394190003a071001e8000c240b10840800c540e034942d17042100300d034400d0f4150b94201d45c40700861031000600340980840d030b601c2000d400e5a100d000b10001018110001c1880c031950321824201100345107074031911520441202032403020252440c2840e4014004d4943c010240d003a016040402034078007241c00c0c0c1c004c1400300c03024044d5265007042001c45020965600f12200980d1007211103540c01051201105c0703109100f83c1c1c070b0350360f520038281c44005102c3d4400004100108100b12080749a6074900e405400b09003810001400e08200180d040080c218070791004064410703604070361040c100403800103040140110792072450850720320180c0c0c0e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 633364631 1250 633363381 633363421
    0x10081b0f0310080a0b011e0b13050f1f030b040e0307030807030f06140607030903170306040b040204080309040518030406180f081507090515070c051c06020304140105 73
    0xb110140000c68106004540308005540102d61070b05103900388060781c20742c0d03000042410118143e00300c001a0500500014004a4503000540701c15245800b085c040c091164000851003508100c810104800d100101c2c07042d03842c11480c000982c0013040010034001c003400d0442d050b803032001040001c20154001041482090903540c02c0c450340c11943d501d0400e5071068082c0032514503e101e005407550071b001d000362402074028a0000e11107544c0c3d481d1001c0800300c14910400c204000410005c46051901840103e00310035641180703043e1400181c00d88170f00a946e55180b141c0d88502c0801c00c90701c541401134496001c22070940f99140d68425001d014203280d2000826032103113180c40015514400070145007260540e0002c0e004c0c2c00c83c10785000810003c020a14002c0c130420750400310b02c640358480c2450107040780901c03c907a05d40d41d60915420113900c40d840355204005101d1110840a0360201c0141c2650b801000581c40740c480d440c0c00741e424a00c82103003462541c0b038081000b8510b41c84000410320a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 633365881 1250 633364631 633364651
    0x21509011e0209130e07090917030f07090608100506090d1b050909060c03060607050a06110a020609060c340308160201110703110a1a0a150510081b0f03 67
    0x8512003070744500791000e600b080101760704084010800481241c0152142900c41c19104001049600b003407103a580066550703c0d4010307040000c1102c0d0941150300000645224103280c4014030300314402c1c10802440780a454003421010515022a445070f4008100c1da07548202002c6c4014000781c03104160900503c07849121750000400b1030752144012031800e0064524405480c6940c0c2c032030081c080d20b0313400792004907014032604209402040035445400d01d40040341d0840c554070140c001c0000e00d40800580700103016005001409082440003045411211082001c2d0092511021802c0c18034080c4800e0b914952680b44074880405078030143c0c4070f10407141011000d1003c91070400403800c0b54005004400094000c000d042c000c203000d003600800350002e4070102d900c011626a5440c07225071901081618401101017444120002405000c0c440c003c80c01700d13807404910b8400060602c44510303d011003440782c5c84000ca00a614442e1a0401074030010b59201d03511400c3e03e9070444183d0084a9034480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633367131 1250 633365881 633365899
    0x15040b09010b0d0525080313051e030a171b06040c0b0a082818030305010501020a08030109050c120403051801032306030f0a050a0b0115021509011e0209 67
    0x40e440d00c1c141c038140303d581000042c22003090b03811405a914152100d80702100c9818070001800d59030800c01816510b0091020000383d41c90501030008603031384000f200c184411f014040102c151000100a01c92942100520200035018603a0428a100c2c0c407900c4c0c01c0d9008050840760b45040c0015246006a110b411100362059407000505064060900c24100080b4020003240341c01d5000a02100b1041d00001410540300031a00d00104648940120740b005092590340c500130300d40c0522560b8010300b001c3c005007a40e52450f551702c015a12050007448001952400441c2604120320300b40c50228021101c3c004240c101414058950b401104d901c540c0650300340001380341548640280c12015005607072810403180c0c000c0c00d0358400d0000030281c54140c41025070b00c482c903060400c482e01150b4040d0000e4480000241054110948140c1140c0b40d40f1208040c2603108650008010300008020513084d4074503140c3c00110313400340042c1c500c0250b83ca0140f120748030013481a03034000d02541c00120303041e0300c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 633368381 1250 633367131 633367151
    0x27020f03031e0307030f05040303150906060509010302070501060f08060a110f040b070f0206040f090e060402090c0c011407120c0921030c06060312110604210215040b0901 75
    0x15803441015107000c0780040e001c2da00058216400051070b040042d03402c0c0801c03c0d41c09013042d5000c81b03a04880030340000342c850150406400e208840d880c054101804184901c030700b801c0000c2c22900c9161840c604046d4005005e0302809801c0d4002005403000303100103110160303076481196803044140c0b0854603043c40d1005d613261502407070b0115003944000400c001d05161801d4840d030240d4000e8001a680c20745145da4000040e1303605001000644480c05445001ca0305020340142140d2003203a2142807940040f06000250342ca030700800c1e52000000d40074507943c080450722140540300201c03030607100c0241101031043c0242c02c58070f0b90b90010151002044016800c8004030351028051080301851182e1054280040d00340c6001d120001d4041d051008104040d580c84400700d5826a00c2a1000700e000d41401c050154000208484055620020b209a0405450b504400040c00d090322100b160318070707050007440303009010395800244d07040742840035441c0604108280c0c4404540050b201c1d4a4049424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 633369631 1250 633368381 633368383
    0x20703031d09040803040f05010f0c1b0206070204050c040f06031a09070e01080a182306251e021b0307180510050a08030c0d0903050309010e0427020f03 67
    0x20078404801003000c2d80680311902c480046500241c41600c0881d03007500f040300072400034015440c02035034030000011811000000203111107146010301c0c03001e1212850440150380c41c07500743c4246580484001840f600e0b00005000644140d0b840050004a00000014590b41503446490800404402844000021001c001180030203c4548012503030940303516151b5482220038950011101100203401da00c0c0300e1001e20000d0300c8000c22120101102c84910210070f402142000845411000f4101030400680088a620504100000101403071450514140c8956507542107221603401d5015580d09181009480c1c1c0c0c104030103241d000c8400520800e40e4100000c00500300c8050f10070900740041e414403a20054200940000025440e1010100e8565589074050004149400055684038240d143c042c2c1041407040a100900507002410808141c0210883e807408200b440d1401c060241d51000400030040d40410400b0b240307005002c8180c2d0207000864505003030017203c10b070422480070f0b0101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 633370881 1250 633369631 633369677
    0xf060b0117041e0602220f0b040e130614040b062b020f04091e1103010b010f08090a08030c040e060402030c1204080f0a030c030c02120a050a0302071202070303 70
    0x4101d0140106000030b03c00c2480d00a81d1504c2c4941009441e10300b030302000840c00d8451000245400554a104110410044c00340c2c1d4001d107003120103141000d00d070940d807840c6c0b1396004020302d440980318941041000312562003040c1201d29825030140740c0c1810b08000711220130403100d0710300403070041e0b084d840d500302e042925500c8251142c1d0004e0320440f007503092220200158201070b420a440318800c5000412248020b13030100034a90100402a40d40d003072101044450040e44c0f0b0290749000d00c00c0d00c035640e02041400864249003011001074a45102141c030702100644081d1021101000340600c1d0107011009001300c40707040707a1000e05911340d0b00400c400c0748016200c03810004020080704500c00074050405a010340910322580c1002d02e4940c0d061070310351051000d100007a550340000ea120b1741d050f105d001c100e9802803001302000c51010b0301f9030005d4401c0040f0b02c2c0c10300101040154580e0b00c02d4048a030b1450f44030358202400c104044000c3c1d601d080e20b0204030081001c060308500c684003482c40da = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 633372131 1250 633370881 633370883
    0x6290d0803190906020c061009060303020606060a021f060602160e011403190b040b0c0c0d0806030c06040e0108120310060c03031128030e060a0c0504030f060b011704 73
    0x214a103844a9003040c01544000407100c2a19880d20743c05030101c0c00c5480039125038005600540348a151003040131802031501d8220711441c0345810010b00101ea80000e50682c4480700380d48040d0303a1003c281c0107a2400c5c0140d290f08030002d424035562105c020450b001101203903c640c00b1a10100800c0400144120b840c0c050000e4013403200004200c044c000c60a00364200070003409541040100182e903200c0c100f080ca038159804c0d102c1700c0c10700c0b0800c0301e605021540010030350022414640c080d51510344036260130b09850200104040803c82070b990501c80101141c2c00208035aa8560b95480856400ea80074420000240610350100f0651908901101d01c90007001700140400342c240f21040c3c545d080c01d424241c0c10556030b180800c0a15212000a041850114005c405a8101030108815003490030140c00704050800034105d420840000f803580d04000c04c1c0c000031469804405040740c10f40955400900381c040010356180a100e55503000c0d2445180030b0f40c5501c3d080021407002500d526060310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 633373381 1250 633372131 633372143
    0x50f16080c06161e030305090601120b13020a08100621080a0809070902070b0402150901020a0f02030c09010f080c030705180403090312030b030c041406010807020a06290d 75
    0x100f081140d0b003460340500c8480b4032405042c0322011120142c1d000762512480c08801181da0f07281400382c52681081803900500d008541498200184d541da00034415000d07049034404c40c000c0c9104c000715550101180302070310004044072903510620a00c0c10180c440c1d48154000684e141d5490581000d0110b00c0c5803801e40c0080800c0d20300006250308480c1ca0000a10100e60750007003c0b80480e481900740000c19889008060141070380c10f1030300401c00c40118000c090001c0d4002000891016600442c0326034500717810203991104951140040b07820644601e10381980180356800100314403081000b41390a986200c000c850070307050300720281555901540216507200b50200001d14851105800d00d13030b80503219140042c0300583d0384d590209600d580350030140210340c84000008203400c042116104005c002c507001d20044407081c2149880c02070207410f05041000d403900284050b4003c224180009034410010008159000803a19045d4814400e440c070ba0002583c200303080340390060403a038080703421203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 633374631 1250 633373381 633373387
    0xc180f180c05100e09070e0904060b180708060d0c050402030f010819260c010f0615140304020111150a0c1202030915070e090c0901090e010308030c0a03020403050f16080c06 76
    0x5800c115200c80006c0080c4c0400c842c0003900c801940b038500d2143e0085128400101380c1401c248100002c2c004403221505085981c0b10401400c240d00034285604005c0a035944c281b4036015040002001c8601d8024075041030000040c084103240d00000705040b1210302c2c0a440c08815168403040c0e8141c800080a40103107441041e0f00c8180103480b0704445102c20100c641441d0450300000d0318251408019881d80c801d98485c0c0c1040300481c40c043d4081c80441030b2416a0765034140a0b0341180714040580003a04100c10030054603051101007200c001c0c40f101464000b03901785403062420300a002d0395004200003540713100224000810038000e80e80180e41c20b0740071701807440d0002018000110010601c408000201d00d25800c2600c0341a203142c018040a8881980e03070681400261440d840c584c8400c210b1000c000040000c161004103413600802c500080a98480900e032048010340241e400103001805030804030355140e44005a01042c3c12510716050310b82540e10074516171244403034070009400030020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 633375881 1250 633374631 633374657
    0x60a030f11041d01030f060b121509061602100b040618020901140901051b031b280b190f060801050f0a0510050108040206130611010e030301030c180f180c0510 70
    0x81d40000008d180b010340540c3e250341d0441d200510306000714070140e5804408030103014507035105101041c1d102c1e114820352164845400350095480750059400c0291658400b090000d9a540e40c01a40c000d1246c2c03a08500c00501c10760f1454002d61000c03034040c0c08164106061110200580c0982c2e00d00c0700c050312003a003084110301c48000150312a000ac0030682c0800c200c0a0300c0490882401d800f455030000013003144403d1b610f0725040258541c4a440c0d0418804401c07000051030105040340c1c0714030301d0504005e007042040c541c0809092482c0d0800360f1a42060000310304150305501032031251114030307030b21119900d5800821044a01c1a07034117000c0380707403440814006540111001c50304079102414107450115050f58415600c0c607643c00a500181e19609103a204007001d0180c03688c503415120140d407465143d40d4804152800724410360300360704000c0c190400005816070003e5001c5840c1e10050040754800c0b20490300004a000085a18002c52100454542041600000d540001f91100e104010f09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 633377131 1250 633375881 633375893
    0x7090e16171509070e0603030c070338070807030516031113060c03090b0f0a03110c010903091706010e06040b0d12080a1415060a030f11041d01030f 65
    0x40340003a4080c07082000300e4100203003102c00b00780b0900c29440641492400c00b800110303001c3d400750040c1d11a90003403142c0f20700700c1c20205021040301e51005111620241c04040740a03500da580c0c0d10f84803122401411801800000000e0a10480c8507a1300c3e44400c1e540c1300d00c1030f0215001078a003001c0680300c0d0039050703500c180039510a5501e000c42d8810941815070b0316603c081a0f281c2e54000500180b5840c2007807003016041149600a08a4134509038280100c0c1400b4000358010941c003c010161210804981000c0280840f103000036000003d02007520f140c203000c0c0038600b03644640381d03801d068011656010000400c0d0725041e1004030350014610f0321001c04200c050b064aa41841d07100078000e12050004641d002e054004200544074a003207885c0c0f81d0300e07000455015100d181d000010703100404c070340e102441c0009a05a54200d415503100c0201c010128001c1c100b480b00d9a181c50700d45428000b013150385402501c2160310021140b46071121060540092400a100061803005140040c10010350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 633378381 1250 633377131 633377159
    0x903080a121107030e030a03020309041d1b030f01060f0e15091e07170f0703020f12010f360b04020a05070b07030c0f0c110402030907090e16 62
    0x100034642011030922481d40401111090346140d4601c41c0d00203010400c1607000038070841015421005800d8808142d10082d45074404c1d801c02da0b12440e90340d000010040310360741c0001940942807044444215200002e4503200102460300d40c03183c851400c4d007041e081c2050240c00156881c90106066582c03030302c030343c01b1070343d0102611341145801d408240c240c8507125952800c0c82044d0740f080c1d0b4030504840b000c03074154041d005040503041020f0030001541c5000280e900503000601000c01c80310b1a03807804012402409442c000d019988800600105a26909200b8a060302c04180c3d003900416030700e190307411740e40018401902c80c1c40410b0130701c000c2e0b00c0044070b207080c8070100d00c030808504980c0704400079089034045120b1101003a8042000700c144101e21f03540aa11940d50b0500b0040c2000e0404040c0620706200b8148040001140584040013200502c41007188009030065481c0d0800e01a29511604c841c0607146015207081c028080d41d0300006002c13413110340710394200c00c3d0741d500344040002921 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 633379631 1250 633378381 633378397
    0x11070f120806100906350411151204020f090a1e0204061b0501060b070309170c1509011b0b010611060f06060703180320150d05130b0c0a0f050307090308 67
    0x3000400541b940303000f104070070a20b40c0302d0300003a034038900703407a00354441200084910b000b101a0b500340010650380341c1c101e0b0031340222800800e40a47e900d2000864104801e24201d8104440e101403081d1400d0329006082d09145100b1000440d501c8003906900705c0c06184078450000b091005da088200110b40000c212007401040046805501d5040a004030f13805014102c00203890041c040183c94503008a14403036000300400781040c611107400140010f10030358007c0304040d034001541d010b2603000e140d020b141076681801031070300c030f00031402e0000e4406001d00c81c0a0211340018810300200704003181caa0b200d600e002103100c1032170711030405100598104c41c0048041c400302c3c0501401c40c1e41c003100000002c0d03105245c8149500a40100c90821802601e400c41c0100902502d1898203400c50041d903c248003020740008460340c51242508001b001d21001600e1051002c1c1802680c038281da00500b42ca14090f15003c07409202818200c41a2208032000c00c00620062801d02c000b42d2450020542e203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 633380881 1250 633379631 633379667
    0x2042102032d030723011404030813020301050c0a030c05131503141504200d020d06330906050a081b0c0f0c0306060d0611070f120806100906 62
    0x8041c0b0401c14a10719804003206460845131200180d044410301d91061750840d128500034005841c0d003185c2e04040d840054001400d007c403d4000034840740788200c51000454000f0002e006504080030620b22310742c440c5045900080c20968240d14142c0504121814940c240b106000114039000c903140400303a4011800b0304050302e56200c26180b00315248081d00402c0000044403003000746074100012503001407c00c0c075452948540e040b0080a08806584036560407000251f65a0701d0341c402c0000400d2180c01180c441d5040783e020400804881280d807981030701882c070a11440341e41c0e00f1306982c0c00301a4403807100010401c00c03c50204d9480b4481503038001c0b60301c01c1c000a0b1070500ba00f1a4103039030450281403da5038405122070310000f20400c0955843c8000b0341c0900800d04040c00480c1c11143c130090058003454840f140700350102150400c8801d0f1031303040100d42c0c0044a50380b40c00170381d4907002080f141c001501c00300494968a89400c1c907464194080d1162039000e0316044003901c141c1120003c0f10740f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 633382131 1250 633380881 633380953
    0x903010b310c020c0906040e010e030a03060f2d081e070b0438031806250e010233070c0c1205011e0204210203 49
    0x1580e12544000711180c01d48503030411410105070111441003200200c60030030507040c40704410302a070b008181c280e40c0040545220205a030ba5601041c064081e80107032080c0c039844d11038950b0352244080301805150320543d80601c10700ba503a4044900c50850f60040720007206050b0301400c0d0f51041c5444a003204025238010b144840e9545031100d0404c111006090424045400c41080c0c8003800c2c41080080e01604e080a0300301414010401c85600342001091040e500030350005888020508551340c00404100c0115680d1600c18030101082c81380c8040250f2601c140d6010400288503200401c480c035a00c2504074002e48100d450868920502030307202e41c1580074841400220000c401d4050380c2c103ca007012220110544031420200d81c1740c008000c00d08201600c81d21034002042d0800c0b810844565803018130b000c44403810704500402114007200c0300c18565160202e0090700b05d030060310444102c480c0280d50b88168401883c0c032842420f00007585600000202c0706c00c4954540716014034070000c003120031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 633383381 1250 633382131 633382151
    0x50102121803011a040b1c0f05160816080a0f020103051f15020f0a0305031f0b0c0c01090603090b0105040f02071a0f010609051008060609031902190506030a02090301 73
    0xc02c49480c40d071404a0f00f0004d4a0920540c14140690114804180e90714500703072162980c8000899215200240711140304000e410900008006503240445001d0507074130070a82d00c400e440d40d500c0c1c0d4803103c1d041440d00c80c1400245075001041400b81c1ca070304001280100107540e40110020300e0020045843c4201680412a01000e9200140040c0c03a080b0030485000140700006032800c010110307c40c8280d0321051045002961010030740e50465580403000c0f0303050a030001c5141a0507120f40203e001072002180140a11400050454014100707884884100340c03151030407030039200f600c900581011030b00001000309003040d03404062036806060005080162540d100c1d106041e40d00da15800a41d032440511440b8811420780c0b90041c0100d083c0003003110701d0840801d8400f02c1215200091010315000601c1d00d81302c1d41d085500005004045c0d0b64807019901c0c0751036030601e58071000d078002d9143d00594046041d45030007600665800411090a50740e6041d90380f00a5800000d000b6050754980d42c2c060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 633384631 1250 633383381 633383383
    0x9130f0e06100e190513021e0123160609020301050403050c070b0307081501020f0d091a131e0f030c09050a1505010309030215010303170907050102121803 68
    0x14004000d0310024103440c1c01d1814801d030703806a0503004210242840c50a1081101c3d0100240024070b207031010109160ba518585411426a80200070790041c03280d204482800802d40c600d0950b006007604c4058807190b406403102d004801058450501400070080130f80e108840141010748948204804600c402c1a075012a0a44134103903000c501003200810b41042401040c41000c0207825203103451419881d00840c0100b8915020f00101c1005101000c0500140d00c02d1200a0124491034115542c600380d0800003424810f0301e21901440601021180c10340190034000c481030120031449000010f42010003841c1c40c444030000c0501a03802c4c44200003030310040d07030500f9401180241d48102c4414500150340301036840c018006081d00c1e14204892485c8002d10035a001a40c2c400c1ca000128488685816407401030034101004011382d060000100300343c0d010340c1520180490341c15644854071400b003060395842c07050040e0340c0580c0000007200c0202c1e0054002c0e1a01000e612480c0c02002260b1002c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 633385881 1250 633384631 633384641
    0x24021b0f03030c0d020109210507022e0807020708010b0d030818061918021f0c06090507140604300602070311070b1611040902190513020403050309130f 67
    0x840175075141c20700d11041c006517800840d8045071a040040c180007521200030024030807880c00901c5102240182c0e15000404400c0241c1030030250130a03484c0800d00c082c080d181c2013041320b2010051003038805c00f141d240011b014103601c000018180a000d07500541d815941507500a1003080354801e40c00054004607420000180034071a0b032108070303c80c11f048018000645410005410301800141303114001600d49200c1c4c030515aa139807845180c100c809030320856110900c104054052410680d842051100220b003407400c440d06040c58240d4020030006008490285100782c04079424061002c8030094070310800403089040c90b0341807010045050b40c0c3c0200301d1f04040000e80008000d407251100c010000c0002d10080c2c42104241400c08000c80044001859040c0d4010321302001840c0c11041c984858110700d070404e0340149803000e40d0003080017111600e2401d1280b02c0c810582c0d0300300e00101d100c4510032101a2a0024051860008034106001402200c140c4400246640b1480400340d92081c0c420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 633387131 1250 633385881 633385903
    0xa060305100f18030f0801061d0f01030b0d03050c06010807050d0f02010207030f080d05062215030c083003150f04110406110d080403140d0624021b0f03030c 69
    0x40745d03210b05145d007008203d03800582014051058624202403c005103402c0380c848036804843c482c00410103d00100c0161003800d04484c0c1040c00d1400010406070000040d01c1d07483c40080417949540c2c5d8400d041c50b6583c03035511410b034002030329040d40b6003c1481c03d0345015400b80103004403858640d0744d903210002401d03030b620150340d848030100751030a50301694003440381c20120440e400d80f00b000074007580c1043c05010000180301240d48207401b03c1d102c83c02218040c0150b8105819414450307072111000c6e103d1110156002c1040b4004000c003c85640301200b501081c418100c0d0103007540d840118240c1c3c03c5019400056002900400400c1e080d5500d005108040701040b10443e00c9520b4035001915400d200a031104043d0443d9175100c040642c44905281d0140e05498a48451010881490444e20030101000c2e02c0a0404401046049014900300740d41d410800c201e51001c40c00e08800c90303c0700740c0c01074648010f0f07840804140092910190041001c00002c0030742e071420300c40b03c807110b00e02910702e11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 633388381 1250 633387131 633387137
    0x403080f030a1b0801062609030c060c070c090b1f02070f080c0d1b090608010c0e0f030a03030f0b1c020a2408071b0605040b0a060305100f1803 63
    0x80000b6010306000b14064009299615180b0b00180e4030b0241203480305001c0e800400507404181412462500d034800c030010074000f1024243d040c01030541c0d4983c2c0c082d02c90201548076403000f0508221004003111100d64001e4070622041d0f00b0258000080c08001803460752000c1c030700c0c1c1c04001f1829006184e042404a64005118551400c205410048220742c884510341c0c0040301d00014a480b43c84071100c900d5440b0b1056580213a050601301c401040941160351b0844c07031300c003001c150050158030440c1d0082881d1038404e41c0d2048401001001f101a220841d019004161f8250000e4080e40104080441176840070824034801d001003100300064455107102d254221031444258100019454083d00c803032011081d403110842c400301c043c05d41214640d02080740c608000340d0444c2c032640031a1038806030b10070400300113415030410501804060b503095440b1580d40c40422906039044c0316501c2241c0d4800d010704000c04002c007030000140007404540c0c2d62562110503940441c40341c0d110381c00e2428840c0c1c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 633389631 1250 633388381 633388387
    0x40f021215030613082d03010609031e0210141b011e290d14010b120d020705040203060a090e100b1905120a05031b1603020d0f080403080f 61
    0xb098079211014040ba540706070446007001c045080001210280c1405075861541075070f400b5500080c4402c0c014a00000c440701100204a042d07200744008101c2c1c5c02041040100b035030001e044485080c201c81c0095200800c01849200a4024500100702403580301105080c41d902000300d00c040880601034040c680d6444141c2c0c480f003011500142c240180c81c2604001010840174020608900c0e420b15030f44002905462102517034401c0128424070b076000d001070162200000c0341c00c0c040d002c011a0076200e210000e00500c903078600062a105c800d1400c0d4000c15001d8501001e020013540003074040394010407444c0d40404c0041e0346000f41d008054440005089082c4086542003c940000c400a4490001c0151010110701e80c0d00210302581c600311440403060894015040c41c10001c91b9004115002c08540401040e09001d5010b51200044003503d8807000360b007210040c0800e4074003009502c41400c030900f0012581c10410818410722880700b4a103401d48030b840300c03040c9821103010080090400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 633390881 1250 633389631 633389671
    0x12110a0905031504020a030b0a0608030d091101020d0909020a111b0132161209051206100e1008060a020702040f0207030801051c0c031203060f08060105040f0212 71
    0x42140f45400b0b100d2800041c014203040d03001a070003400f28400504182c0090300468030001d600ea01c018004c01440742120b988001c9411420041c00744041c0544554a141c980f001c1154004545c190810425941c2c0e508018101000c0100a41150744060100300f042041d411455101304521410000c40300c01d003c1980100c140010111150114008400344406855a18900317288442c00740f0040e985a83c0c40e04d036940c2100c1a02400d8080d400a0651303080d0303600e1011402d0300000310b20b064800a40303d0031000c0301d901e0781c6280e40741415211108460800002007100c0840d080d00a508203234043c200030125584c0e544c0d0b0628050094441c41c000c16400a1040c04514143c8038503102c4400041d0194280803407520040c05180052185034040c00060214460088a604401040c1c45d8410181c4030069100e041071740d001d00003803840b000401d1a0a001103400610b82c51020216910300004040c00c0c0c0c00c140034440a08607140412103420780a0140f20140c841d1807417000c0c403031048280c1809600d210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 633392131 1250 633390881 633390883
    0x30b2b050303130b06010f050a0804030521010e15011b020607080f132103120e010c0e030f010203040b1303050409051303230a110c030d0f0909180312110a090503 71
    0x5c0c106074144003152040e122155003017001d440c40c11405040c1800143d4507810f082c2e8951180f420404400e0343c40c00d007503c42454422030710505030f0751404460381c03003a507411aa24600405540c2e007940414040e101c0b0404160b140710340302d49654400307004182403c02a5030380c081950803504040e10706150104810b042c018100040d40c0003030902c0c19680c1c44414840c24600c4c0764100100d070107001c000d0b1031143d0a00610745500181c5101c000e540080144505500c00140510000701c840c1e84680140445683c80301414001c5d240501d40000b0100010344500c212448030300078034203081f418030205100015100c5aa44100c2c0d224105407101e4040d800303ea4a0028924003458246980746030300c032800c50301000c14890580e0f482c0882410868a210141d60700f40c0d01d04000112116030510802c0f0301c0701012680302d56074a0b82c02140d80c45000da09600c4806880941c9c007410240303405180c407880502c000c248980100031402a04850008010314140c03a417041c1988042c1350003000c00c8048a0402140c18 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 633393381 1250 633392131 633392153
    0x203210d0c0c170d1b05070c0f140d0623040b0601080103120e0409021e01110303060904110126090721060b011205130210030b2b05030313 61
    0x100d8586071200c2400b42d9500203000880384400141000045201018809660301104008182004c00000328900c0311009000d544030070011100513041c01e90004082c005045004141c035001680141907454000038420500d1010405841c00b075111906848140041c900750780c00700780f40114101c11841c01c0e0420081000c0b0142c0700354100f00c01440104081000408a82c5941c02d0a01c0d01c1e2140300c0c074403130000d401381c42c890101039441103200e2402040d007240001c500c0308004c42a01c4035245010040c010b603489000403500c0719000940702000900007901c02d86014041c400504015281000c80001c40751f180f500b00d050922180c0d807007403e0001a00341044428010062204200030342910f8161601518120010040849403200c005400ca0380c00b5812076a000a9080b01c100724524255000f180b0b0070b07441c44000d83c050b00968500100f624403074090320410b05005030034008000d9032031030808008000c881540487c100741d5442c09001941c1800114095103158443c5101c602940c103007c90055 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 633394631 1250 633393381 633393401
    0x19110a0b1306052d06010c0c0e060103060b041202060f040e0906150d030e060c01200a1403040305030f06061902031803010608060417041203050a080912070f0203210d 73
    0x20390f07010708200b0520b0310344e034444203070b500c83c0c94945041c0d21114016517034801c96480042920041130f801190588682c10704030701c01c0c40240d8060056940c0d4612900851250f80201004108180c20741d20160034100e00a01080c04040501440d0503035501102d001450283c07a084d929400c04818402001c650300c08040c00d0305012603911040d0038507541c000d8a110300ca1660540030303a00218044400b80c1080d844001c2d1503480e02c0724040624441107942c2c02680c041c040c21404149190741d0404104142c0064074402e5a260301c40d60f2454803228500d01007458000e0030f259001c2c42c10000c0c45131480100c079800d001c1a0207a0021a21703000e6890b44980b498140041e10303402a8581081081110000600e168000750441041903810b100c0d0b001e014250700c034917000fa048140180b1403403410590301000401c407046241d078039000561502ca0009448407003030480c1c9103804105014120100b80c1136203400c0002440101103400403200030ba0080c1603600c140042030340340c071808039482a2100c2e860056050345 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 633395881 1250 633394631 633394651
    0x6250f120f05092407050d0207060f0203270a0b040f090b0f010f05070528060e0c0306182802030d02010506030613061515110319110a0b130605 63
    0x20050303071001310b20695412012803c68040011310040c124401074101c1c4d02550b003200c10754866580c091006540c9840611030400000d0302c0006480005201000303039614940070501d9200307c5100190ba9102004170084c107143d100c19140c10015802042400030001021034030014003882d03207099000c42c100e51680c1e2046000301402800c1040903a400f00342c4917070406a0b030601c9078481c02d40e400c20b1880c1c041807220401030505040440711a010032401070780e42d014403812050003250082104240c9a10250f5070454040e0311140100d85003240d0701140005124000c03088a0200075000c2043c0400743c0300101c0a01d502150058800541c00c0a01a104007914240002d11084c201640800c0e40c030100113142c0da8150410000b00000c1044640021040c10340300e060220b415519035401c0c880d0001c05804070004105032150107000d86c4408000c0c0ca0300180080083d42d0f07030007604076040c0c030700c0d4240702c40c44005401030145e000f0000320041e2049004410740540340350300c80c0c20762034940101c8002070300500c07503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 633397131 1250 633395881 633395887
    0x90a05070f090e010e041a010308041503021305061e030112030e090702030405040908040806040b0f010f05011407231c031814101404020306060a0506250f120f05 71
    0x405850b96003082c1101c031039031800105e03030362607091209909020814017550b1500c500000420b0020400140060300c10344600041c144a1101c42a012846954181c00c1c609d00906010000e40c07600002420380c6000704108503c4800550395080d6080d807090f0012800001e0105d03c3e0030034540d011101ca80c00280c1510111003c0c20142c0c4040c1d0b070303802141f040f14411a154010002000b0040302a10004d2508000f00e4249007003e2802101c2c4890032034001148e110303076200002d06205900c4010341115410784070700d0180c42210320103006a6201c00400d640740303039800400125038410040e0112520b0388600c050b18904840315420110f8266810000003012b0818442800b0f011909a05500d4654030904414425501c1d2090741e0a2042202c00074466a18019904078500302c242001c0b03100d00d20031019150242d41d0b030b03800c100e00700b001c0780251a00700a003400003800c80450000040548012898200089402c55a8441ca401200002141c0e01c0c03400000b0301903d160040602c480c45042d07410900e007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 633398381 1250 633397131 633397139
    0x1b2601021c0b0312030703092a090e010912050a030c021b010e01030b06030705090a05060304030c030c051c0f0e1f03090206040512030405031c05090906010e090a05070f09 75
    0x14020700920303555551900400c01c5560304021846800000d48003075500d034600000c0203030080c0300030b11090354007064540362002c204200900384100f4280502034040d116041c11078240050032203500812203503583c0d032804d030b021031400d40d041125200c6540e1490fa950488100080c160b842031101c020940d4440350800100c0030795440c41c0c3c0440d140a04c0e0141c0c40f5002171004074007801480552640001c0000240002e5a5100c00103000908080c1c0f030340144203580300c091029600c400c480160000e100c00c0d50110000b403040c008483ca042c05502264810b011182d82107c884100b02000d0700403c03211032820000307a8220900800e0042c0880f02000800d0f8010031944855000c46680010075a9861072070b0215651030060307074081c1202509901c81040c0c40030281e640d0303510a002e407511a116050050b01c0816002c40070039803045145d524282480706d88414003040740c802500080c14030460000201d629220019050310a0004810102d1141810301002d043c680400840408001003e113040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 633399631 1250 633398381 633398407
    0x90d0507020a03020603040321020a0306080a050d0810090c08040308061c02061e0f04050a0e190c03060803191112070b0601050c0f01060503071d0708041b260102 71
    0x702d9130195022652aa1580b50480303092090040030303001414042c00d0f250003c0da0070b030f01400000301642c03020080181c4499015554400b41c480003011a8000890703001024800d1803520381100d80b101882424a40791040f20082d6000d00b008600000d6101e805c00c828541e0003096542c01a03802e0740c0c482040c0111414442007903101c3e00c80039020714400941c02c458a4524007070304000701c20304040702e92604100340a5150981c0240b0400c0c0c8100711681c001300b080743d20400c00a005140d81100032080064410003027020782844040681855980c01d800100e8190a10080800070720541e441c0d40712401583c00602004c2c040c0800c1307842a44120314070000e40c800c000c200c45880750040100e0441c1e070343d1a00121980d20405444071070500504419aa180c0780541140c01640ca04400341d48103103071203603e02135982070102a4a2044580c40000c10b0800d03000303480042d040b03070180903030400c010780c1002c02803208021648000002d10402da40441c100031207030136500b07180780d80741e0080d858080005118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 633400881 1250 633399631 633399649
    0xe1806210d030e0304050a08072c07180504110d4d0f0307020c0f0d0204020901030908030c04080c0d0308071412040b0a051503061f051305090d050702 66
    0x1c001455518060032161600400668008140c001c3c02d0100b400d0b11080142c2c0c981500b07206060025144640c104016040142c6041d6035035006545152203941d020011203081190580344280c00c980e4400214198a4901410090440b04212181e41f61040034003142141c1d40803602c4041200300c0b5006184481c40c80340e044500000201100b80b4090352481421840390000e20003003088000015910783c0840ca0001461081c0440e4082c2e42d405030104081c071054503a03820312070391700100070074102d00180707440d60103040c0d0110706150006141d0007a03603401c403055005540c40015540082000c101d0741800f08800d4815800550740e004c0d202c0b51607500a00545400f030041014812801c00490300a0707042415030301c11001c40c0b000345007141400c0c1090540346d18140c0d403691001c3d05110000356100a880340c140c1c54000007a000b454103a4801d030504d007011030200c81c800341507040440001103664a0a244c00d0b03d40d00f4080001820342004070186180c42144424501030000500004004d0398500da48 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 633402131 1250 633400881 633400903
    0x3050108060a2d1508190f050114070e15070804030b071b03050901080f13060f020405130614120607051e0c070509130c05100e180621 59
    0x3011944015408506025140120003d00d41060341d07840703020740305a50307002800c400401c0c4156640250b10341540d91340300c8081c000010401201616108002420b00009610307060084000050310118180c11102054059603a54002100480d00388050f2415880501040d80e180f60204e00d8100941d640741d0144c001d621010b0321100311680001c054501807414054151190500e40c50070440a2070042d015070003400300180080e228500043e90584002d40f03450141c0e030442010071603c8043d68420018240c059604002c46130240000105500c4400e80e9009035600300070042400707801c0240e0741020360b441c040c1c1e0b244a645003040c149880b0b100410302c641c0120301c501e42503940300e41401000001ca2490500b05a00c03500018200350501c6000c9a40c40681c0ca045490701c080ba11400c140440004070200050410801400100114580b04190081512141c20b108808020389000200c0407540c06110f0980d1070480300402940f85020201e00191411152850610002051600340c2d940c1c10f04031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 633403381 1250 633402131 633402151
    0x901020615010e0a3332040306020d0f0209221103010315061a0904090f02060c060a0b01050f090103020d0e100c080a02070f170c01020a031b0305010806 67
    0x155100d5070342d11038010740b10801030107010500f43e56595801d50295590413540200b0740401081c0c5141c10b44440d40c01050b05010310303a00c10246581403a4060f008809000380f880e010869000001040180403029000a500a040041c0c54074500c484120a80740360008090845204202e41c60503651f80c0016180035a58074040402100342c07114240006018141c1410b08041000c40000304000c0900c4001c0c1d10641280c00a000c0c841d0381c0d14200c0d00301c000341001c6c8900c100090010b590315041641c0070321481405100580c0d0100a03a40215180d507000e0000008190800b008010003180640900e100e241020719205d45015030b101c900c10790034080d94030507604040c0c0010b05250740c1c0c12070350014860902d071002910b060174800146403005091040c00d580118600f240090010000c5200b40e6141e1a08821603070070004007503070f94020204501c0250240580103010300517417103900b440988400031307140d2400680d90701f16100401c410725100700090101410302005000210700070610325040f040d428 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 633404631 1250 633403381 633403411
    0x8010b0a0905031219020a0803160203090d0c030314040501020706030f1e0b100302120c0f16050601060e10021203071427090f0c1c0c0e130209010206 66
    0x31208840101d07440c1d1010b541842035100c15000301070400001c0c001c48186100c3c0300d044880d0140c00380d0315440c404201429075481030000030100c680140406041044601c1a6807030440c15900165440c2c141c0e2001b03440d06041c2715404d00c01c142e003024040321461034484085050615090000b90313110600d024a404064030382e07003225680c040541005490140d0240034801c0713040201e0383c0600511a102d0924410201160f400c1d46860081c4202c1e05120907040d0700c0030b026074418500707500303030380c001c48140801080800119010041d64210511120f21410141c0302d503514010300100100d081c032075118031810414a48450031900066141d03510350507a0000c503201c0d030743c080d025600c00701139092010400d40000303000c40114071041c8040500451820000c040e5002100501464840c200d1381030011050302d00204521f8600300c0050084008540103a94040005940040958002ca40a07401140b051184440580b804200312130341d0103c0480b0450a0000a1000079503a01c005021411664410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 633405881 1250 633404631 633404647
    0x50604080d1d0d03080412090f0e091516020106061b03080405030f0c0c120f0619230601121829010b0d0605030c0a0e09011d1b0301090308010b 63
    0x11540304160b80c00010403001c8480040c1c1405400700c582210300710b4600c100030000999082c050054442030728800c020161a49081414040603580d01800b008420303c50130540700040d072406101a8803465480d07002003400e82c0b0905000c0d096915070307081320b814000b10070038584400d80000f203003c80154240c41c0801b0903885d0b606100e4294820581d00e000700f1000000c1a4000d280006215004500242d030070b0104003541e41045504c8900142d0180800d802c540301081c544901c4181d2220582c074050400070350101400144819019410140c8002440d41c0701000403e40c0c00202d864207c48540c4400c3c00004541c400388034034100454002005c5004410107041c9925400b04200d1851303c03041803000321542c541c440c0c0c08241e000ba20b0341040480c20700070081030340e040c0440c800c4445407000d0003200781d041c00c29101d1011850001c02600c0c80350740c0c4a1900303402000d00c51141c162a2002c2000c0d01700c4104444c1c0b003003c119160322615003e40c0c103081c000c0c00083c2c0e00136009030440d803210580e65100c1e082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 633407131 1250 633405881 633405917
    0xc071b0e060d06141503060906040c06180f030f0303141018020c07030c080d0c05030409020703030b150d0b0303040302090403030b3607020c030a110307080322050604080d 75
    0x40c990403e0782400c21800c0010405075068500d0344010206c1c215156641c441804035076170041114000c2611540c01400c000c00340c019030a40304e64000c0c20058400540c0c0311b0700c45022104c042e40c415102480a0101501030580511074031f01804028803e2082503c0c0c071494030480b88219101e81500944031114406090303110360705482c1b550340020251100143d41c3d04101c090721226002c8e81009016a041a95026000e0000c0d000d030198018080d50416140400003070007508444003d030245501c404650103280d842054040c0341200503018207450340748407003d075411114148001070096100304401d00150761b854170020791040d810301c0c0205200701070750041018031800c03c0030f803102c1d081942c0c901c004015008202d0b1500814404801046584801e0100e9941500e1181070b0f425800200d03401c0045001d0740f80c1d002e4813050160072140c7c1e00d95650101881d55201042410b205960b0480d103012205040704400c0050200315205130809080c400d400380c07161908000c0c1e00510910000658444032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 633408381 1250 633407131 633407141
    0x10503061e190f0501021c080f04020111100f05100b19050c0708060105041406010c260f09040f0b0307140301060f0e060f010f020d0c140102030c071b0e060d06 70
    0x34140089440b5039a50480194840704600903180540580c500c0380c140070000c1c213940c1031591244d07500c01150361210075404042c20000380003a030410041c2141c0c41d104400804c024103c00750b0407827000440d407110401e14070858002800c10105201d417000708200d100710760000d458450f8140d03980c1c0c103c0e043c540301c015241441003041c84100f601074070100142d440303000308a40d8101c68041d1814031042e254002e0100528030101d03100390200303c540d82c45034007140700740c90080c01c0007402002c0340c0d45048803011400303a0358000500d482002c0e203002a48040906140c069030380e10036082036043c843c3d0000280000e881d80443e001d0040c00307452001e5220a0f41d40c0940002d40103140c0d0460500f50b49848200c0284001e60031a8194007450b40c010050000754441d0380711520f668a00d030302410003c000a0b81c2110040c42c941400c0c0c0704000e03a800000d409907401e01c011401000020f03207650b030350110b074075028840700c03080700081500303015582d0200700040c1e502c501d4a9001008517005a00c90845151480c0289 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 633409631 1250 633408381 633408409
    0x4081018120801030c0b1603081e16111c08100519050925050a0c0b15030d021b01030c110706032f0d15080d080a050105010503061e 58
    0x4602000340311195802550b0706050300c2c05072004031a5551682c5040b480d910035811749400744660701c4070b9800840d128036007043d08a00c2000c031050310300415912480c2041c17820b07140741880408880760084040e411000003000f0341c40907805001c206002c0303d1202080c0c1e540178034100134032081303030001a601040698032001500700282541500c240803410301910000303901034140903018080225400c0501c494480c0182d03013164114040318214488212050f4101b44107081c1440898941e10000415800592348210186000d101c4d060304c2c00781c2054078000340e4410400c159008010442c200000148008090003400c0c01d003c14040100c52080313a0740c0c42105144140ca010f80e140204101d42c0c140c2000e000d55142c0f84281e0403180e8512403821001e000c0341401d0002c40010040700101500e9030308004c0f00e80e07411149680e500d030395403a0513a043c054202c01000020703400400b005500202032007118050002840e246045203003003004140507410b09003400848440220403040c041c3e42c2c1c040103564107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 633410881 1250 633409631 633409643
    0x8040305010c08060a09091205090118090c081303090b090d060e0a11040b060909040f0b041218050319110a030f060b0906090f0a0902121c020304081018 67
    0xc0c110b03420081c80c1c0780c01580c185118a450310000900e14036580903c180098204680358007800b85240d065445511070700c00c19040c404d6420781061440c2c1c0400307070340c0300418241d080820b0500140000419420300240704280c0703400812b0900010990128548040c0e80d9410300c00d0390f0300c500010008400c0000301e08014911424010300d07007400c22001c0750610078179104d101030381c04070b015040400c001d441422100701c0d00320100f4408280149040520990441d01034400c10b406120325440d25000700c5012076060f030b110990804035207000c40d07211000c0040700c81c07015041540c49091000003600c0c1c18001e03030780c05a0000508060018400b0340a800c6e16141c1c0018082c5a03030310758901e000c0d03211b5104004107130303082c43ca8444003007001e0a10110703a0f0312814004001d031f00e41b96500c102a0b541c800c40500a2447c256807104200b0058860b04c0701c1002c05442c1800030700c4c00e060151442d042460300342e90341508540051004101c07580d00001c000c180a81c0450000c0b03140c851080c0c0005050480000250031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 633412131 1250 633410881 633410891
    0x20703021207030f090e090c01030b1201060f1e0b0306040504050f011b02070902030f070507030e040507090509060d020306150d0f0305040e0a09080a111603061d0604080301060c0804030501 83
    0x40540000804d110340e2455142d24542c0c1c0c0d1340702d030051442101207d40000d81c2c0c20002c01001d03d588280d200b484500c0c802882404420720030404542159030750b030001c280c0441c080d0420f1258480e07040c0c00618560980940004041c242801c1070041e0102500c0d5500698032000441c041100c2800b650403a5641d0070b0007041140f4072101c41c219400011070080016000d0070b0000300780780740f40e4000c40740308000101c4d58800c43d455070b10048a29900040c416410450f60901e207040941c0c0b02d0103191301407841c595506a02038106405c0010800025041034810090540d41e680161400300c1c40300d83c0684010380fa00b29024859021620110301c20900900300540c2000307030001c041d000005070095500501c80d008640d61402e0040040700c48020002e807071000700340481034030315100d07001045042c803c07203094802d080c50714109120021103503003086600c03030344510200d01100e84062100c50700d002d030000108610b0074151901d43c044d10040c081c1100304824540ca0400f84030025007140c00031940003008001e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 633413381 1250 633412131 633412133
    0x1f141c060e0106090b010c020f10140f070c0506070506150a030b0c030906132f0405041103100209010804060c030615020706090b0a02030a0806030f0a0303061503110a03020703021207 80
    0x2c000c200c580500d00d44c080c5130503a200c4495114998107521954090002114100071300c1c00c001500010034203c0d03040059a448000c0e20b240904007410358003140c0c854481e00c904040c5014000c49880d138100a0048009020b61000308100140035904403d580c1280d05061a00502050300040c0540020300306850341ca083c040c200c048039000b14420071340c680560354036840301e420318000c17a515040c019180500c460a10303012507040300c5c581466140c0c00c11400020200c044086000d80c2d4003210241c1e2451030341410061503050521a0703c284c58800032085103070090300400603003501d20103800602131540c5c901a42281a001e42d02003070282c45039560000c0d0402e07503440b00a68580e140e00803400014100500003a0003074401040d115250070700c2c1c0185081c05010001192601e40c02040c1c0355040c458101c0421081c2c009109181d40140244d40c00700f961401d065400c070454980021110403d40b504040c4000c1c601941c042d690582480c2c1343c0981d80e0640c40c10201d1404581c0c60f840701c400280003d4001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 633414631 1250 633413381 633413383
    0x10050606041d040b16050a050903071203080f0c090d0609050102040e01241d0105030405210a030b0604060e090a02070c150e1005030a0c1e02061f141c060e 68
    0x1485644281c003110816605e1503455030441a01602e40300c0410030500110602c02c2c002c1000c3c1c0300f5000d02804036008280da82c3c43c910401c0411800a0300440c94080611807440ba160042c2d607840030070009202e280041c6003002c540e605c4101c100180c5425540c0013a0340c03c200c03080d0110b800138040d6910312045561900c58210282261060300164003515010741084c981c050b2f02000d442514441444c6480c040741001902d56a10040003107409000c3e00c12080d9a802c0c2081e0707081c0d2840c081b0703101c1c50f0311540105000780846210554051080805110801103ea8010550142d90030151021400c944400001c20007078003910b5001442d800280002140c4542c0c0b9002c03c5040e8941039540c8040144000c052104c0780c0681c02c100800628100009138805045410030711503260309103000041a075090501d04075060840303181e038005801c14420f101045060030304101d841c6981c6080d0b540d0385807030800c684014603c051200c60081a0300b10940b03a40108400342d003003185400242c00d012008000c1542 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 633415881 1250 633414631 633414689
    0x270d120506041b0e0402040b042705040f0609050102091002030d15050a06031d0303040303090b061c080307090b0f040e0c0301080307061d0a030305041203020f030f06060702120c010f03020a021005060604 89
    0xc11401070414ac040108800c40c0106402607401241a40366645a602c52102401c00e825090b5441d41d02009410115201c1c0c440031034060720030368080c503212481c0c1c4100c1000d441403d03560011210006400f03100030b0385e40100f81001c484403030030300090003c0550059402c9211000024046000120400040c0f50709904004542841030340140540e076560400c00c000c012074001d0b45044412040c0703030b00000031100c000031900035426042104040fa0750350311011195000400c0940d1700000801e082050300c0079462259084040c40040c00e09560604440c95034034040e808000e85042c1d141c50105140703400444080c000b901020065230550111414003401901c020707982150030036401e003440c1d01d18512078400e8a03480302000c00750501d581c40300f440100090001800c01da40c03045080102c00c005170385851407500600040805840c00301c44450015020f6040307003070044181801001002034042c0c1c0854002c00d40001400300041c1c0c0d031600000f1405c0d41c05203411803041a04101101101c0301c1c01c0c0428 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 633417131 1250 633415881 633415919
    0x201083105160e0f1506090a030602071505011211010c02090720060105060702010e04020f2818060309050a0605070509130b0108270d120506041b0e0402040b04 70
    0x5451030442d543c0c00400995507086544d0490b00d40504003180340425000342c00140190001d10b458144031030900028001d01c041d500403030b2200c0d8000307070035800c01500750b1140350000220300080140c1d41c500070081c5098007041d4001041d49004000070050360f8043c00c00092543d4002e03080720440e01d801103000d410994103910544800c0341c98032512541d00301c0028400c3c1a00c0e40540050300b0142190300646116030032030401644a9000e001e404e400f180401c0140880b443c40c000b002d00400400f01212511010300c06010041004095800c80c1c00c800402040d0200c0c3c0407807a0000c3c01e8810303410403c5c01c3c00d05420000b080c2c5070910082c000b645030b001002c1c04444a007203503174246440f038202e450011241a6040580030460b0b16000400002c60340d040e99840482c070340302c40d50a202480c0c50031424045031010480c0402d1000703c03140080c90b80c0c1d00c203040d44010190b80400403c01004c2200f00060401d041d60b40030000070760882c1803d520340390181d5005005034000c06032240d489a032442c08074070026075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 633418381 1250 633417131 633417163
    0xa090213060513020d0e43051210050901060f0506030f180a08040806010e0f04020906060309010e030304050c030f03040e0a0b01030902030d020d1b0201083105 70
    0x8050940d420003441144120303038000785800303c140c4009200030b029400102103201100c0e601c40c10001e040c0b42c14040c0c105c001014946491071b0105411000c00c454001c00da009a180ca05e0020010b0302d419040e15910989108039881e00c1030014071000b6078907104900c4050640c0300d00b8102070004d2700d9415000705c420f403103002c031a40c142c80d0744601c240040c40c00121005600e95a408010503ca003036000c2070820345a41c400266180c1d540741d07488500e240da1160b4170480311940100c0041000c0d0505080554010500b40d155081a0030590009607400e90090142c034804c0701d000001c103400440951007150354070030103004d80380c40c0d00d02410240c1d2100020800749003c3d019400c0c0d6406001c0000c8121019103501c01c0c2802c00d56202c0310402d9005101c40c0ca0300300d050550310040c0001594040009107400e8049a004000107103030800000c15021034039021089039801e00c8946c03001070303030420605640030221051450040004480c5802c02780d40f10390105854034406440e51051107800325201012801c030103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 633419631 1250 633418381 633418399
    0x918060901080309030c0d0609020a0e0109050106080115030509070f08010b0324070e03030d060806077805031608040f05070b0d0b030c010203121306050a0902 70
    0x2c44103a20f9106100e10340d54103030001c1e04103030310510f00303601140615400f07a02c1c006411000e40d4003059103414a50084020071000d034004111b9601c03140906030240c0b40c6450180e030154501403c000c040c294090f8284181515a80050401c1c802040310600926410300071800040d0749000c500d0007080d1121820b80a400390342c030343e1500404007a02d40302c0090301d0833004a0a41e0b40e04002141c40a42d6400e00580c07600080100c0c0d80914464029000174000310005015142003001d005058a40115001505400c41c0000c0b081c07422122142c1c55401c01a421094649006801d40803105d6220380c0044e080382e1101160201d000642c1d280300316811003e0001900c0c6001c070082e0262058007084490004050b42601170301d00c42440b54070500d03001846003144010145843d41c0c0c1900f40640c0e50410050b0f01c001003403214004085015142e03c440c0281d002d4201080d034072000075120701c40d04001a07082404a40800e147c3c000c28181021803c0d0012000c0115041980e0940d01410f982103081e40700b1100705d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 633420881 1250 633419631 633419639
    0x9040e0a1a0c0d050f0106020c090f070e0a0305070308030403080f0f0c0a0201150905270309040b01091502030403023d111603050105072a02060918060901 68
    0xe00c59500c1a0080201e030441d009011030540410750003440c44503214424402c10300003c0c807502409000d01c40c00922034902e581040d00003071600750180c503101d01c20020340f01030107414010820300343c4e002829841c040c60800c80000c08511456060382c8000c1c0684580600007080c000b92401844c040e074800d0780c800b00140c55035900c1e080d0540302500c20400304051080401d00e0322480310003c01d91000e4600002c00d85420b042c0c1e517032409000039401903a1b00d03600c542c2000a42000800381c0c000445280c245003880030b4851103019a00d00805544a010319920340c001100c680c06090288018140b0b50249a007080d41548001e4803034106100880c098000444514400c00845000700000c010307420700007040c003844007000014951520b540c0303024044100d00e1010200c00078482540041c0e584d104055109140d440d01c2421920007d0044003000a80300b00086c01c440c58543c0c4001c480b442004106102a0900000c1d481e8030a000000f5072086a03100b001001c1390f0420800c41c03081600700c40c0380d4040d1780e072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 633422131 1250 633420881 633420883
    0x603050f12180d0b04060605010206180a02040513050a03090f1502031606060b0c150c2718010e07020106060e0609060309010605040c02150a06062c1509040e 69
    0x40d002400180c0242840b09403aa1072490110544600c00101082201849a200d0310742055066030140c0d10a61604001e00c16940c040100941015861095a84494401c15002c1d1184140a40244243c0e240c1011546802c150000050780720340250540c0d410ba40706103006091440030303224a403003a008000307002944039a802c115180c10b100640145151080440d9400d041c1014003030708aa0340c03569040c021441d403107800050709413407401d0340080503805032502c49070000d200020000005007038100310710880044aa0000176500c00394010500b8040c109100040b51140d00714209000518181e0000626880a4607000c1c014000303500200700360b68071400211400c0100b119036642001d003c12141040c1d0500070019075001d00c00c6000011042d446000040035174448524440c01a800b165110030803115000c0303041d81000016100700301c000e10300070015103000d83e000443c07246040d941400702518130a2448d201c0750784034001c20301c17901d80d5103440c003006031750300010002d900a40c60000c03800e9420314 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 633423381 1250 633422131 633422143
    0x120409110f0304030825020c04050f0c2b0513020918070b07080c060f011a07031b06140c0c0f01110301050f120109151413030e01210603050f 62
    0x50a6a10500c0c1d55199242078032084001b81001c0c0c8084402030881c540b29546441c1c0010102051b80070b0319150790b034081000155032000e0842c3d903030f001c0710406000c6445c1d0200220b527400ca00502546c440390503090130303981c600845003408611544c18a410000000fa05c3c00340303807100e54402ca0f1450704a40b1a8040c00002e03080c0785e000f0300c01c541d00035001441101ea074840902403181c8100701032440c007440d11800700d06100e0243e82e04c01d030700800c4100501c51161401e4049509111605030642041c50603100208181d0420860403a050f50080805c01031091a40152034207107560004d0b803219042074140501191b200c450700721a107000322071510004503010301a2042c250220286542964202400c00140c0d03416034511640c000750207003c1d0301d507444080c05100d03003540c01480030006116442d400401917072a400c0d41c540c1071b0800441001205000009a0a01160185494520190040c0068500a1030b03c0009013031900c2c0c81d61058040e03215a0804819284208166010036600111066440d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 633424631 1250 633423381 633423397
    0x703020901090302040b0607080c0609070506070b0606070f021e010210061d0604140f0103030905060f0304030309020604260d030509030417031b0c03010b030622060603020312040911 80
    0x290b440081040985400e0b0800038035400700814280ca440b040e40e403283c056074485203130b80200780c102c081084120803003404008010501a14040e19002059583c6007000300014a500d10801c00840c0d50b1042c00390030640e1200d459800741c0b07031004881480414030b0f002c44008542e00d00610600b031481500c1031040c02004112080541050403050001c42152901d2a00401e41500f0540c2c0f41c4210b031100e0250382145004001d00c5017081015415828014411502e5030803c5000d11403c110070440c02c12800e084a6000c0e80500d4001103000b0f4500c0040c58602c01d5501c001d18050015145010102500c50306e0089c0140c210201c1d45a1174650031b00390140c07502242e0107500d40d003081c030081101244204174a40c094140d50140d0f45084244820b0340c2d42c1e4002d01003d419a64000030300c0c403240b400c00348154500d41000310014010fa181a80c54240240880070040509005007030f800c1c020000303981c202c2d03000b456004040c0c8a03c900c01c68034891168220344240040141001091a8030a41400c00c41d000070b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 633425881 1250 633424631 633424637
    0x607030e03091528170c0405010c1b1e05030a0503120703061a3a09020d0816021801060e090601110a080301080d030b0d1b0b040e07080703020901 64
    0x100340c5990400981c410742c4407010040b050100310310502518594007054114403030101d540101c1108074401000301220300b0300c0d040908800d00600c29007420351b00c203803000c840d02442d0502d81503030390340380029500e1910b03000000c000d40400801705540307101008818107404002c00c0d1044c1d8603910400c05544858244001d89150401c01c14103040505030404aa8407110f503040200359250f4a013203402d4882142c01d8038030400f41000c54840507084481c111000c4000d8400594455451340c041c01181d00102450304290a81c1e83d0410502191269582c145006800140503500c0c0c80030242403156040e1720202c124810140d400300e60600c07500148005058884503034411000072000414000c0224000d00340c1414044014002011484100b005c80003280c0b1485900b602ca515094a25260181030314250090505181c031910b9280c0302ca0000d0010b42e0742041c0410003585034040781c8903203d000b0380c21942800c80d0005000ca01024803a00701c2d0b0050002d6507603001b403075075a840210102d0007407032003181c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 633427131 1250 633425881 633425887
    0x10915200708090a080715140a140307031103100503071502030a180506280207030837020a1703061305090c03031206090c03011a0d0b0406090902030607030e03 70
    0x4030740103502a020103c8080d007182e050300e44421845103042c0301640585200040003068201055000b0f80030b82c10003500140d140d04005d11140c1c0a0494411011583d5841c00084005100a03200340c2003040754540000d82690342c0d00344420b003c06103068501481e4064802c8000004000c90100f01c02c48a080140e0302443c10404405001c4481d02c4055040101248656102250543e1501c005200f00100d8880344502d01c00d200004005070f01d040101001550806071040000c44d000c0d4045a900c40c00c602141582d558011010062040801c0300e11002c0303110313008045140d1500014202880d9002d940c140315030406100004081e40b00444505401503480c03100301c0c0d00641700c1e8002030741003910841514550790b000310200385103800c00e100d074400000303040044c0651810701c1101560003509a0307003001c0c82c56040001150585918100d0b0501214002035000391845641d4400101150000d105022080d580d81000003c1d04d03095030168402d01850010410080c043d20035450384d00741800286003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 633428381 1250 633427131 633427133
    0x108030f0f090f0a0b130905070c060b0a08061603060b030c0a050d0603080a200a08070807030c0f1a10061b020102070e16080a110403060515030109152007 68
    0x15040e008641141d80042c21408041030b26500c060008004d002032806030781d241c4141c600006c940780900c0c1e014418070b5242805104405038090030404005400400100b121045080807078180a620351201d203e50040006103c24455441114080110b0f10703a024005241c480340c10765410320041e00c0d0544240b50401c40b0000260060024004160601d0700c00110b81742d42e40c550203803550060000d240040c0b01c400c9204801000d0a48800300e1202d48001007000e040c07241c0e540c3c8001d00c101c40001d0482200819560100341c0706101c2214003940c0001542c1107681140b40403560329411703d0201a207603190000140c071401d000761701c100071503103140c3c2c828941000383c4561034180c02c0150001c1c1e045014450002c103015001041950203079140c8118503c00401c0340707100500a40e070141541074440d0500b5420f40940d00c10005440940360490b5000030680c8801d29054603202d405640d850300b550901d04003400344140303aa001d120341c1c2c0401d2414007800790500e501800070000070340d00032035142c018801e40c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 633429631 1250 633428381 633428407
    0xa08070b24010f0507240f0e07060c050709110306040e0f060a1104092915090f0109090c0e0a0f05030307120509060d0b03010b0d08070f0203010f090b0f0108030f 71
    0x3c014070342c503060292a01d0541d46981c41044c8a6030707941c000300b1102000d080c10700d0510b440b0b42c111040c6010030400c1840d01c03141406450b40d2030342c4581003c1140d08891002480000e00101000381400c54040011354078402091200360000c0301c013588074074504410382d5950000030540201011603000548802c0c0d44801079040200310301040705500b10001e2002055100041c49003189020310b40d0310860103080c18000c40c2d807c086078030150310300400001000f03410800c00b0303806840e14103004540c1d0008480b00240100c03049850b561104501506004000d480b0035000244000c0c20034040d40c02e58050b640722811460840c0c0c6c03521840e5019402000150301241c0d1008075458801d400b4500b0b030385011105000161103800203103d2004040d40c940384070156140901c289000700a0075215060710725020b803226051805003840107040480c000d07000c1007c40d6401e42c04007004402c511010070a00c071131410249620b860032036410080030104000400e405800001380c40d002a901541a40780c250940000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 633430881 1250 633429631 633429647
    0x9020d02010c080904090b3405090d0816050709020c0d0e0d0f050615150a0c0201030f18110d08090118050303030103060b0306340e030a08070b2401 65
    0xa40f103210050150340700a98a038028030026a028881c5c648035070805559546410450140c40480b06a8103842100006d82c1e0040c0a0a061480d00300191500d4104000c02c002d000850b200414030030000030340a00940e001d004070703078441e4040c0c030854a16a803103d2100c07080b03224205c4141425440140c006104903c00c503918042088050080060320900c1d40c2c03a0100a0413050007107895400040401c451501c00300c840c802c4449084980d02e0000051045001180c071803903170760b40c040110490400741075900a030072440030b10300722400400030403000402e460700259019400b200d0f451440d4502101a203000c000c1000b020707801c0b043e40344c5416165001902c00c82d1881001d1156202e04510006140e90244003543c020b5001308000310b501e039800380c105814514001d100400c00392807140d16941c502100c1001c500c98000418034000d06194102d0f0560b1803002075040c60b54584210358021040100420107081c8031072285510041c41e80300e5007200310380800e0344051084850001c901c81a09036105001c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 633432131 1250 633430881 633430883
    0x613020912010e01020a1b1e0303141f060305010f09151508010906080a0b0703052e1505030f0a02070f02090906010501080604061a0a0504080303160e0409020d02010c 73
    0x1d40c8103007000803039401d400e4400001c00d101d4140d5012400030981500051014054981e2075501490a44259150380b5401840d01c049640d664461116504160203540f090031481902c1c155031805207022950b61002a90454030a415060046c2000501c2d074024010b150580351844006256541045110030007404100c42e10840c40d11a904c0024804080e07403941015600e0503038a01c41a0340c1010141004e807019a0b11240080d4840010030000c1029115101d41128940ca404a20790f1105e032a440c6500a900b00c0004e103190b041c51402c51084200d0b60300c0c00803a80781440c007841c0c04a520741c00344e4160200702c43e118032078a1000b0024509522541c0200384052080f03100f0496a071458010850300d1004859482c65a48003a006024940c0c1101d90242e005c1c00840e01800135900f4400015070301140826a034025050203e814540340b4000e0090364090301150301100d0700d03840c20560b0000c03030b07207450340420010501c540045441420a801030101d0150060405c0d5280880c43e07004582c80c10340200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 633433381 1250 633432131 633432139
    0x90f1605090117011e050123060a0c02011e1206171c1b080d0f05061809030f0a0818071a090d051914160b0c1612110906130209 56
    0x800206605c901901052407510104000251581800c0407460304008000407648918480c255214441e43e4801c101c91f05000c1030319015080b19803510050301d019001c2840c5024041c90b1544643c2c40d03940c000030786485600880c0007800101e5a66007000c084031038071401244681c015403036480001c61109000c00c4064658900310101da00981003c1d030751810516030446a8801c0007400e14a5069180200c401884100c1400c108505160707001415500e151111801d507650306100107801c0c03810900c10794040e103107902c10031952800c243d00010007214044404410388001c40d10f48903004080000c81c602036030a500d40340d122040e035002c202c4520342c02858009602110081705c040004000380070f00c4084402151590380c140c0300910384903d5090003a12106556807119918020381c05c10140605c00700c900e031324219603803022941805d508061481c0d01c0314130718603101540003c5c6000d40c1d400303501155001c0e81d5100c4814843c0c07000c012400405440311580400321040e190514680303035000b0314220000074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 633434631 1250 633433381 633433391
    0x513030912110301060f030b0915060d0f1e03020613151a03010603260309070614070f110f0d030806010311090406030605040311060106090b0f040e090f160509011701 73
    0x48000ba094490a0f08031060306c5034280c0c410406c20030303a411901e400c040c06402810204403d42000c244c4060002c0c1428400c00740d800361101405070b0390120083c042d801903044994160510300903a00c4455061080300144510307000940e0308032500482c440c4240d481900b20880500c8080008040d2028a6003c210442014404240d965003403107584025071140d45d03014601d40d99100d5640081d800107500c0c070100d81d020030030002c032080d012800d00180c40740346c20500c9440000003840c0901e40203112000740101d0314081840c05020040400d404650012030301041d641c031590341802140f92390f01c50020045441c503404507402d58025002802039542c01491941003403500c00006d4244c42643c0d1069031403665a0081c0818582d01050f00d09515102c0380c02402c095243c101d008100e0b8106100d28485090040f5660041803d4032080754000c00121005c0c00250030900e480719152864a81007001500c07411920f0000811840c00500c2101c20003042e00301c0ba60718000f81a480e03401ca00ea8440c2c5555651 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 633435881 1250 633434631 633434663
    0x1101110607080103110103180b220602040f0b070f20030a03170106050406020601150c06020c030d1506021e030c12040f1a0702061c020301090b01030513030912 70
    0x10000306200e0401a5148a1154514200a28080340050360380d8101030a01012015000c01041c503425001c0e440402c03500e0507511102c0c6108401c007500b14075640800c0c0307851100140111350300030f0003da440503003a040d01c10740d0360500b8100e10321030440020603080c4108100408100c2101c5030b001100280502080211400000030b414402c00c41800c402081400c1d204032038030401da400307040c0034100a00317051349031038101400a580c03454140b2510000402982d94046964800c5800100c69688104c0654a54403c03480382d540325004001d100071018507043c20300850041400d105400c031040b03074014200352141d03000f10b0307001040845200e1595210801138140004402c00240b9400c440c082d103003546a9081c120382100d061055844550310451010343c015404441000300e86450768119031980d500c45034154812000f50341400b65419132440800005414855a00020b10800c0244d0b002c1101c0c2d5a2482c0101520801d014083c0c001070280209000031241c42d0302c01030352036000d050341c50644284 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 633437131 1250 633435881 633435883
    0x204022a03070c0b0a2024241e060f04030b0601080a090308061e0a030323042306071403070312140a02130e040f02030d110a110111 58
    0xd100105500c0c0d000040003010701445200500c05440c1d4464414504480c031000201665024005107014060031015101e01510420072480202c001c100100e503500150241d40c02415800c4507580c610002d1076158034041d011282101c7c01c0140c1c000d0602d100d081780841d04091200c10700c2600c6410480400600780800b01c0240640300941c41070510012910304140018030488001e420103842e6030401c2101c000094005802c04d500c603405440c081d0b030441501002d206078281e800101a040200342c0f20100900d98848210710321032a21000d0b441d428000018801c085106038030075890060003d401d08010b0170b640044010b0071040c014030150600b0b5076912140700c80066414a000d0302c0c3d0000031190100360b00620340c1020440c40c180c0c10041003100042c034188204000744604a0a580000d03035508241413850414013400742191156140c0c43d080c50801904140718100303920030312590012001c864424081c1c40b482042c0040686103240007a0340790b242c144c04c0310200605024030b1403901e0324030941c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 633438381 1250 633437131 633437197
    0xd0e04021303350702041517010606020d09030305030a11040308030702010f27030c020301020d060b0904060504150e3301090e0c0703050c07090204060c1203090f020402 74
    0x4000c1005800d0200d404082c2002c00350310350300f000783d0150f82404540c50720080009550a4039019240403845440c0c00c1c00c5c24640c01c9a54005042015115103070300c08510055000e281641c034690210f4004400c102c0044d02d4420483c80010b00085c0c003000050744002203500040084a0700740e071a141040c0c0c03240d643d54640d80007250602c0041c1e54034508810400d201c2d00942507400c00890000c2810500c840c1010b800401000c00941407048911100c0304644096045425002c2e0000080003030640740e031503900c080c0c2c0c000f040b9188600d04040c00400c036441c0620588070b400000964001040d4940103540c801a0001010011159070700d889403040c05c4c44007410b03001d04040b03065180d000d10708040009440b0711041d030881c48a0751b850000300b180e059007550494441d50307003500340f2030f844440342d9502c10700d03040d01504401c2c506070001c900002c2c2641c10542e443c1c0450b00c11010b528100401e400100c00f2504114800780c0700007600e0301c031140542880d0f402092203060010143d142803051f0350170300c55260 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 633439631 1250 633438381 633438383
    0x3080f16030809100501050901091e0c09031104060807060807020f0303010b030a0e0a02030712060b0a0e040c060201020a0507080f0d05070e03010c0518060310030506091501060201020a020d0e04021303 88
    0x10510320030081d0f1210140551a844030340144104840e5050801161252005001d07034119641c1c0c0d42c400510707021404c900c4d003840b084207134ae01340017003004202d005000342c1403171008503500c81034110010b032949028050801070715059402000301c1840d04400312649400503043e02c06500608484208517201440290b02030a140b0b26526520300300104145c0c103c0d00030301c502c00c0103a04901003280042e600414004111145480765141c41d40050a0000060407100300042c1e001d2450140091000300780140a4880e5000c0c401c006862036440c003080c0c1c00e0344a034202e0304001032810000e0500141d9200040c00b40060344060b41400d111180d00b106007255819900c9001191405421301070341d250134007580d1040d070901e280c294100700c480d480c401110741c81c0013038203403188034040001000e2a845000303200c015500042200d000d414600c6500e500c0d12500b00c0c100090100440004c92040d00500072110200303100d5005040142c2400d86c110391030a0720030a01544990200262034201846050340c0001e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 633440881 1250 633439631 633439637
    0x150c0d020304061e0b220b0a0e040b0907031109070519020f01150f03081b12030603070e090c090403020f0d0905100e0a0b0d02070f0b070206100b0403080f1603 70
    0x60492413154030040306012280d42c505107240258a51207030500d101803140314040070000c1d5411b40142001805c501c64480b60040070101000a25203209089640036170b016013400f001546902c1da546445e00003500014240c1150340c0c028101c6410a914841e5000c1c1461a00758100480d980c180b6580c05040403640300141d001c000d502d10340d0340f420b201c2c055101c001caa80103030b0014544007510301448151301c8090200c0c500801c0c25600140d404204141e140750602c1a990f220a0b40080f0545541050b81c2040c0244250075000c110880d001c3d040324020740c00403000b003214049200030000002c000400c101c0844c098983da01d95200300170451100508441c0d01c03420a81410001441150103030440c0351801c1010f0354902e400641ca03107040394001d48015122540d513580c0b41d258444061301c90b8080081641807003146c101c051240513000640111015400e41d8600c0d12a41000f941d001018040c40815010400c01000000c1c0e00500600c180c04042e052340c1e08000e0181c0c1000349a550103c015808 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 633442131 1250 633440881 633440891
    0x50a170a06090f021801140105030613060b1b06010f090f0b040c0f1409100f170f0103061a030309011803050d02012a0516050c130c1709150c0d02030406 67
    0x21482c0c44410171448643c80c0c031655400c0c2d85040740c070700103041250b0441c605204c800030101d1000d40300c180e2a80c2c07010a00701814403201d40d845010141d00d50010342400c4141c00c0d0042e02e24a408801715050b412103141034103600f1280e091003881401803516001078500d1540c4c07100071000759200c6014001c02182c2940700c080607110320034005017030043c149030b12030711451003000000d60681e15121402e0200340140383c107180d070200c8076000f40c4905e0a240c400c0d82c84aa01da1041002c140108040241624400d000a000038245943c1c1c4c2d0301101e2a00031300c2d981c540c106210b803030001e500c6606100e01031280300d255000320a50b60b440710f85c284012843c07240d005075180c0c80c00e0700c000604031019810b8104024400008620403c20040c40e50081c0d221002e0517401440044060020030822001081c2006006240c0c2408001c40100104042d03170000c801700d0442401081c00c0c0008101841c8510803100151038841c0c1c80e0492201c1120b4014817a0400ea542400402c2088465201552056202c0c40e80001c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 633443381 1250 633442131 633442133
    0x40b06040c0e100806030312090a150e0c01031a09011701061205060c030a110c0f013204170705010213050609062703010e03180901050a170a06090f 65
    0xd407990a0810340900c01d5865165040342c99400d0307014106090751401381c4068030360000003420752040c0c205080c0d20000f080b050103017840000c00c801802c1845010525124013500003a0020795032865003151140e00103054103107843d40203411080c0c1c085180360428445452403000598640c2c020b07000a8900e40201178100400e550911404020780907940071013034002200e0780d038580d8800000b0001d00079000d0100105111b00740780d40110b05500d101400301511107100700780b025910051592002c10941c00c04021048605d9060040d0324943c1751182d03a00c4014010401c91500c4400c05002240c10300b62001d0f41200301205403002c1c020741481170780050303521088214042d58105051300310510a200410801500e95540170441d0f0060030351007000055040703042c2e4207219140112403090707055400c11900c02e1040744080010000c1c2e010010159441c1c3c1101401e1181004c002d015032500400024000d02c103468000880c41c134170007901c108642100d03020b0b9407100255241428100c462102d4050040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 633444631 1250 633443381 633443389
    0x190513060e210a110a0906060804030f0503090c0103020702060c06011229040b040203013e03130b0c0d09080a02060601020d0801050f031608030901021b0306040303020d14040b06 78
    0x1d00500e031000b040360503074a41800d400d5102d011510b03008043e4452110b010105443c0e0240401c01020300c0181044500da44d4040a81700000c22242200081c00c18205200300a024030292805041007500030710f004040340300150001d500c0481e084ea48074000344104c554040d8108010f6001c0c2c8015202070380b110142d4501b00f100c2c00350f40300340c6010702e480c00b00700d48590111070b841596000c0d07004045000036440f10b001090040441300c502c588000840c0c03034482c2101060f07080f10822149402c03118455120000c6241101340426a003229100210903408008905080307204d642001c2801c0c0c03068a4180300c0700f5200c0840d1070390f880483d02c5102c0402c0211909405101a5078481400e00250201000c5284021700080050203050b1044103d942000b110340c60400501d8240044419a4056a81c445010560342d4101d503030260b00500c20380484064902e2014840e601101018005020702c0c0c44a81d401d80103174008808c2101071a0b0b130f07140c0ca1080355001d0742215000328004d030350390301032824004248 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 633445881 1250 633444631 633444649
    0x6150409051e150618130215031005150a0503070219060c030f09020f060f040812120709080307030825030606090609080a080f0f0d0e0c09010b190513060e 68
    0x6895000c0f030a01c200700668030390080c407010341e80804007100d406503120042030800001c407002c041d40000c5410081c8081c1000f001c01507000340d0140181d0158180c1e02c0c8100410b0510106100c0900541440000b403114001d03006140c001c583d900541c1c0108000c0c151064511125140c156860b0391145d03030a040440d058131440c0c0b21411003060500c05911503030081041200c07042c52682c007a4800060110402c0b81c684251406000c403501511200c54a004900d031b215080032a5582410039601301061149000b01c1500f01210b484101440c18500542c80035644054001d09804415078942c240d1100301000440ca18540302868074002020f0f8188100140100410380200c801d1018403007040c40b0fa43c4000a400d0312140c3d001d40400c0c1e86074411108410306004211002603200c601261500c0894507980101d0f528940a0040755101c000940401011940c01c2c402c8070810001084641c0241c40d900c00e908490b08140c1c01c0c0380f072030807911242441ea540041d5014070000345000c1c10626803843c01c0040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 633447131 1250 633445881 633445903
    0x13051002071d0906040201301b030b0108160912081b0c18060d02090c030912070b13030e0909100e070e01062a06020a2006150409051e 59
    0x61140c01d203041c2c807001c0d03031311200a003011781030042c007281401780c407417a68420182440800310360341400b40c1c810001d01c015102c00560f04c00c0714094465510000781c403034440c0c8120b01d60160f42e400080c0d210340a0640d000d81200c0000000c11a120201180321445510f005042c140708940c8569a00c02e040362900346c3c034030101d000000b039410521300d00e04d80c3d654400d0382d0b19140200e410441040c3e240c50000078481a19020029003001c10181042500e1362180c000e184218107200c241c83d80061070010341c2500d8441d58000030f04511404001c100d0401c042840c96050724401d04214840c4010440000c4000d00111907008480e8040c000f1261445114010501a00304901c000c00e5003e003401003480e1514814068407003048036a4040c0e90b90342c41155594840c0c104481e21030030211201303040c6000a5400800c10102090141c1c030412400300141405100b0105100d016207036944a62060120400900c1c0d082584a912001200e011400901a0030307201039271380782c020290149400450382030490b200b407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 633448381 1250 633447131 633447179
    0x1e0b2502061618050918250b03060f090a0b03010b0a0f030303020306010212041d1f0b1e04090b09061f080a0608031804110f040b1305100207 62
    0x180900040a16001c0c08541040d09041040c8643e501c040041a10703183e005580c00703503480c800d01c40d507084a109819441c110440070344220024000120804550720490141e5100c1c00603000c2184a515501461308203800a044120400c01c3c800050340c80b40065582800035543c600500300303d45000d2140c0d030840701060710a84011442c00c1c01e1101300000920002e401e0603000170000d4aa68030034003003500c11079140d00d03903940c0319038840a0380720703a0208407441000d180c04044041500c166441c507004151000105d900e00000d41081e20b400c507207811034000280810000c0c070400400c000320b00d0113003001d4109004001150340e03602d401c00020301c070050500c1d0300403544000d940d60400391001403055107240a0405000b00d40312480d048004206aa10484450101103049011581010020000700408640501c840300c1c1c0200d0606461041c10b81c5008800300400080011b0b616a0025004180c0c400486644691741c1d04003141c600144110310400503080700b503040c084d60406407409007266072400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 633449631 1250 633448381 633448393
    0x270b0d0b150d05061314030403030801090b0108061f0302041706161b030309050304050904230d051c020903150a050709060e3007030204110c0303041e0b2502 69
    0x10f100c0c16201c0b04040e2041c0180048150341310240032840407000340c9820014104d80e030751a620308000785844028001c0040c404d0401e24107210941c4104a0140035160062000c001007980003150010215070042040515400f03210004800000070180b02c010031602001d0035032032400d004405400c881070380e82d9400f44400980310380c4004440c2005482c009900d03003000101c0c91941e0808a02d1805907034485507210315143c0400c01000140003c0c1001d60300000c0100340400044602c082d20b80201c90560300c0001c0f0180710800010341650349407810707192011001894048040040307820060841055000d480d000c2e01840300700c031210300c245903015034245451302c0e01c0c131b040107401050704030001240c510170100d40044051103020442002d5030041c20a80f25840c800000801c0703902c48031544406e82c49a8a030000c08101601e0310002c0b01c40c1444000061851130b0b90b166241d0004900340020030110a000100180005c0c1544c800c55008000d05011294000312401c01c00c080d540f401003025013150428 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 633450881 1250 633449631 633449633
    0x90314160303231b070b0c070201030c0e060f1806071220100b0102010f09060507020f0106030b010512070f0807140f0904031407170c1204270b0d0b150d 67
    0x200681d19001244d0f81405502e4100070f003c2422103002d82c1300b010301101e00b080244250515954000c0600ca8800e0320b0a00408003207040a550700c112413140103400080800c031100903840c0c00c2c0c0080c10344204940744109400402c0d808108a03030808030b130880d202000a8a100402c070b400021450f0004c03422a0740200e02500402c00b0354076181404100d0000b41d4480c0300c8002c040e8002c0d0012010601101d80401030b0315110b00b80403000e01030079100c40e400760141404401210340c042c0981819a500041c3d0200035034602030510000c01620750b890400c1d4090404040342c90802004000f00501d1510004c08103141000c01c2c1100701c03034921040920a4001c2c55035118592142000035a120b44c040c10544d20944026076592460700c10010000c001400c816140c40c1c84072901d4001d40301681010003118043c40340d50a107a01d40e4403d0b40920782e28005d603c2510955110020f1100255000e40100483c60404540100310400906e90088a0880c094801c0000301149412620b4024000f00c0e081c201c02401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 633452131 1250 633450881 633450941
    0x30e01091a2d0d0c0c02120115060e09040b0c040e0115030c051204150f0c09080606190e070201140703020306013504020315041212051603090314160303 67
    0x3d104603185180c0d103d8402030802405889103803445900500a6030214840550f0680201074921b80d5014821783d5a501081252103080100a40940035141140d542c4990f20782500c0c0c2d000080400e00c1041c4200004a4101e940d107004c180205105d1401c000030902c5080003800f55410741c10b195007049020b000b03107220301050070041d40d00240c1100710103200c0303048810880003401007660b2048a180c00d0902c51240300764800c4c000801c50300b094058400315199001086a0441c2070019100c50f00c812407014030aa4032140300c2e0342d0b001041da000024900348603000c00e4602000860740300d03020981c080100803035540c10022004041995540700f246000d640703180c54030180d2000c5484160000301800040454608111044210b0326000301d2020515003032a0000f42628080e01c0d8800003001c0002040080055018185c0510074113581044203c64603c000c8004007180c60041d002c00c248070704416882c1005100500b03488845800300483c0d58040c3c240503043d070712203528840c12002d000c1148805d10503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 633453237 1106 633452131 633452137
    0x40f0b071202181c0b2d07090302182203030209090108070f0b090d0210030b0a2c06100513030b0106050d0c05070f030e01091a2d 57
    0x13103d0007143e1914072244d00010a046000e0001c900d903108054041196008001162503030a142c2249004008509903070030008201400d00c180b05501b044114080301c500000c03201c40301c80c20814101c162079403c0004c404042070280032403800709803080e0105c030141c00006220300402e5850b07001054032042507100f10312841071a00c00025103c0350a0707040c0d40030100020100303c40d00f0a00d070240840b40c841240500c04041c0d490f00040d81c01c0c2d40d00203c440142c8541c640d000d400240205503209039032100c0b00c92550780302d903d0040103019a40c0200c4d9104c11a000d151068607800d203489000440d43d100c0e0401404d8040440010480c1c5600101034650304507251418404004003503001d442d06d00c182d0501400007011042d030345005c02e00849802a031018189480c076007155a40b00c0c1000fa0505120b008e10001c41e0009540c120f01c1c0c0d64607200c0040368600280b01d0705085402490354801c1c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 633273381 633453237 := by
  have h0 := BRFrame.cov_init 633273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 633273381 ≤ n) (h2 : n < 633453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
