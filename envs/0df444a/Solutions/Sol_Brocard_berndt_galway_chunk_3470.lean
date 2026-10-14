-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3470
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:45:20.460506+00:00
-- url     : https://prove2.me/submissions/38ea6a1e-80e7-45c0-9e82-e9897396d1f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 623920863 ≤ n < 624100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 623922113 1250 623920863 623920897
    0x3080f0402030a1e02121516050705060c0c0d080702060a150302060c070e150a06120209130c1103030402030304150c240f0e0a170d0203180d0804050c010f050403080307110c06 77
    0x24050030a00e038030307508e10712408002040042c00007203402000b0311030007125a04c5425a0b18984051500e04020b13420351a801000861000c8c0103540d035002580c603401c0048400002541000604107d0790140c2981c8000d402640c042a4210b11030780110f0b0300e9080f60921040110755036281e00801c038412520f11001940100d80c140c2c180300b034074880c0603c01c4001101307400051506026100144020b15030f0345850350210345910140d41456402241e80040e03070000b0f0010b6003142801d6002030789a02690080110f18014025005012881003142414868014009241408968200d040c811403a4603011b908c890409100c02901083d902c0385143c41740c089070281540c2c030b255a5a0f1094440401c10084810405009010b002455880294040d000c6141c060191008442c40c0600300121070500c0c0c0c01b03101d010010000441c07808108000c0e04802446d200c0440c1c944c0003c2542c05001c0c0d03800161940102008201045070050030120039650041c04542111408900304a12440f960180b0040d01002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 623923363 1250 623922113 623922121
    0x403080406050403050906030a090302010c03151224020325121d0f0c1e060a27090510082802030a140706030509030703080f0402030a1e021215 63
    0x182d6101c10341080c42440c226142a11010001e00c4c1c07074100f6101892003030368514048007055024807809003010402d080074440d084330f003440d40451210343e10a0010b81c0c0340c003002c440200924400c03181040311070140d80211408074401000000c2d04112a000150084d440c070030051010f01e46005066001036550341403800502c082c1c0040039001e4183c1c400c1004200d80c07000468404244845450700324250000d01d8500d1911040208008182c210100d0612101110b0021a01d505080300c01c41d4030301e070518242e42d0743da50845140c840801420b11a031014485000b00700d41c8c4c0160030240c0261440c000085000d911191059214000d0190020750142d140110342000d03131381145100c0d00c45000070103451402c132094a0703c4d030825041d00b040e00d00f0b5801485050003950781610480c0d40280c458401981091420ba802034803462000d00402041400c2c400001c00f1580c01308110045c00740d111007055a104200119245051505a0308034482d00c03180b2003038098144005507100c48410004822121611 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 623924613 1250 623923363 623923373
    0x30c1401021c05130e131109060d08180a0f14031204060e0d0203010501061806020304060509040b1c141506030a0b07050f040b211003080904060f0312110604030804 72
    0x80010080641035941d682d00241c0c9000300b00100d88100c0300c01c20391010360721b070b01d14264040d901c0b111840f920444031201400380300d0b2116240b562a05500a200329540c50104020f021407120015017a41e020058a41c08114540102001000c540b0307940f03520241020400209511462010805c02e040315080c881000310703512a00402410103409803402d1a00480e40c0c000c21300303417071f0241c04c500082141d0b10340100b000c201459a800060200f44050360919052410003400761040220307841c800e07a1a402c401ea101d94800616002e0704292841c2c4c40d240c01b815107804400000c030000d8980c03943c00760714a640390a14105420911030a401005000c0f040c2c1070b23540300308170483c01610350002c01a06000c0819812105002480500030168841e0f4540171406141d241401410b46641c10081c00c0005200512001d91640c0c1c2c2903981c40000161102109408134005001641c00304004803201b0900000740f01181c00d03106102915aa1015030324002003880a54800040d640200020408800280402c13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 623925863 1250 623924613 623924617
    0x40c0819020d09080c0d09080340050f0d0c170c03030a0305061507050607080903090a1409090a0209130302072d08010510030809040f0204030c1401021c05 68
    0xe0041100103041841c48200b150484404071411102c0384130004450890000400070030700030f404107150103070060341803041940d201c4c081c0460446402503040b03140c0300f04482410030f001e40c0e802c4d5078000c0d041c50a400c8000a23104030b010700c5140d008444903002e464290403e070341c0c52084150400e006c4001ca9150812034603294985004030f0a0500030701420100c5551f0510050120290b40d5801141c00e041c440e040002c0032248200034640d100c000c012900010f040464640c0e480015030821500a542d01c00155044d441807100359035002e052004080b4007200040b0b11600a000b05445410099658010b859980e070340d08800698884900d50003c5e2208a1442d840100b0320b02c2031051700c451a90b129034100d241c0d4003e01c0326000c10342e60030700b0f03041e0071030a00c0c0401c43c01000081d009001d10308124504000101c0c0500001d40f140e0400a902d100d43d0326250040d1480407200342c01150358aa607401c04400e4085a8095805240d402d0b00310114190b02c0050990f84048007204001c1c01c104001e0815240c036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 623927113 1250 623925863 623925901
    0xc0206100b0f041e0806222003011b020f01110f0a090905010b09010f09050906210708060603071203050f0313120809153601090f02010e040c08 63
    0x144003c00011038110120182c0d090070608860f0000e115505042c00281054402494024904400154040f074040b2441038280d0154008050304001914140560508440c0c0a00981c0541c2040d006415100203880d14106902280e402e40313508611204025090740d24840b07180b100884184540301082c00400020000c0d6036060500004066485680701d0641d0000d07400303040b4800e800708001c04213507085080035074192003a00c0c004604908002c002440f820001e029a40540c14070f5602400151444c5000840c01107410220f0b4603456075544450350341e00d01116101d0080c0100840010326004285000c50300d29850f03250903052519851821420350801414481c20b6121842c00b040440c156102d03001a42d8420382c2e07080860710f8988602c1340741102d1014070140141101040002c1d560402004481810070a00481d1118010304004108080c0641d1003140079440c0401e607400308000755030385100b0305e8403c1e02c0d00038841c5418400c020490344010440130105140e10001211104007100348c3c030312 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 623928363 1250 623927113 623927137
    0x2030601052b06120209010611010209190f061d22051509060f06040b09011e0809060c030105010c060b06041d09070b0910050903010621060c0206100b 66
    0x4040c40c40300c820300c1841c002d0007440c00000c800c0b0051011a4a07600405001d00a0090b00a401003a20703070200340b0a4905209130020480000000000d0b00020340469200d04030045c075080c55000d0421403103081010921038109a0342d4000c80024106000382c0000c3c0344038000c01410748099841c1d00130300c50b491410040c0600406080e8602822a802c90310800d4000c503002a40e04c2c0d02400f19205100b841840584164401d40c201c1c3c000050543c1c620044a0584071503145481c0c44d00281401a11003842c0340c882051252100d80c8108002540705140d548079215031400c079103403a225101d44040c503102c203014003400201068142d00100310290000c4008070406400341d4501a99080f084070740e036218006070500b0000e050b051081080c81000000051b003115030007039103421041400135040a80e0607022000b400b00104001e400d507502940490000c002440000a10340c25200052901401802c02241c40380d190802e00407a0500c0054264426612980485130240c20400c0c804a075070007107109580 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 623929613 1250 623928363 623928367
    0x4032301050c03040b04020105130e070305100b070201030f0b1005030a111e031009060f1d0708070c050109020a090f0c08041e05010605040608031306030c1e200c030d02030705030301090203060105 86
    0x1094612b04541c50018101c4200221950802d60001000d41d80c7c0500b07000f421064140d01440380e12090000c61714895424280000d0f002c0c508003000b4064052a0442c03503110042c0e000ea604210f81202c01540f2459808608101c4070b04006840e10351806203902c00d012a03003529103510074ad40104802160000480f0055921080c7d07111314010a07210b5541141690104003101089042c1043e140000d08210f520600f00d1103160040c0001d0208400a1840341000b003c1c80c424404d00400398482d02c1c1d555006024800d20305c0d19041c01d0b1001d019401b0f02e036101203140a042c418803603c0f80700f402d801a680913030340b040486120000009510400e0340166059541c65900258664480c81140c000f80100805540c4803802030044002c0c23090290702010030306041c195020007250303014290050308400d103080c03a426410100710848080400c00c10307107162010110583c600d011000a089000b03884102c0c1258a00d4041543c101d8490003003440080c015803050005000c0307081f041d000b96030301803c1850464 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 623930863 1250 623929613 623929627
    0xa14011e0e03030a380f0105340c030c180207050d030b01050d140a0c0528030b03060a0504060c0509090a0b010c05030301090510150c0318050604032301050c03040b04020105 76
    0x844480c40a50b041403000317050090345560700309075026850701c0c002428421b0400b0040e01a82140e2940c640005041d41c442d4040070301801c6a0035121501603070004207100c0c016850340792069044c0018003904e680900c41d000302e0041880c2c80c2c02200c4500d030340400585030924071001e0a4020f000b201c040b41c5d0600809200c1c0b018884410300c0b07141c6815001c07514803010703400c010146cac404680e410074812042040412010502c0e402581e01d031080c1c980c564407046070140040710102e0050240d144230a9040c026032040c0a00a80301c1d8001c64004c6008240802c04075902a4007500d040c821204595000403c210000b040c20000d60301114021806040c10340310420248c0c1e4044c259413090b00409a9259994140486940c90000a20103480c01407171034220b004551030068859195104010700300b0041200054182120b00c03406401840041e29094466803203107441c07840300c05070400c85010441001942d081210701401054040e2140b50b0210f0300d5900c0d55110400b02c00c8008109038180b010401c149 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 623932113 1250 623930863 623930921
    0x3110307061a010302040f03241407170907050d0606170a1202060c031602010b0a081f0b010c08070602070203061602010b0118090b030a14011e0e03030a 67
    0xc1000a10440c00020080c81512190660207030079203000341014410710081c4070b0403201d5404201669040b40b02d032541c1040d84030840c1c6e0b88801c0b109a404585003007401c05100171511240340c50040803103440c0c80c1c80c1d140030b2503000c2c451004100c4036010b503540034440401450070a4490214078074050280403555030f8461421615228070740280e0758181e40464802018130000e4500c480f07003120301e44043e202030700b0841e0b06103600e80000f800794400101498085142c0714000d5100f00310031a0041c007079030034041e51900701c961101c40d00c1036044000c0d031100c88400c242c115a0301c683c15180405071100a510720a80c4c55101840e0803841d011a26154200b01100161350108219441365171401e07800f482c90501c10350000c1c207680d540e00c0034906001112101c50307540b00c0060fa0031820786480040000354804010f000a2802203020b001800710680035141e41981c41040d000090026240d5440c0d200c46100c07a048842161001e01105120340c00500c0400c001c0e2032282c2089044444200c04150f20700010050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 623933363 1250 623932113 623932117
    0x2070c06020601030212061501050a1e050409230a0e0a0b0a15051206040206091507050a050c010c0305040605090103060509090105060907050f03040f030c050604080a0206010b071e031103 82
    0x100e80964007141c010811403030118110101e900500014042c241808003100041c0c94040325000c0c18071130040f1b8030091841c410f08a8100b00d90181ca400e551282070305802070040c0c5d002d8040c00080600301411010042200b41000030218680d052601e2207a4a00910900404010f41c60442c603000d951f900784003150000000301d0103481e8590000032402007410810200c1513050388414041c1c4407902c0c44191008021032001e51181e019100710b6900c0300700ba00000c41d01c0c2507100000701d62901c00b00b0941e0900a000411040c02e034441c000f100c0d44000c40d1001510ba043e90f9020080c0055030800c024800e55115a0260100ba5018100421600d4440307001954410007114a401d0503990741040122901d44400303181e420403420300300716140c0280426420340d288001000540385030203148d09c0750109482201030512894019003541c107207003000d28040c0c050794010b4110300018400c1c20004200c060b40d8004595140c0d078401c0100c0d8003501d014019644090b9462401c0d418880e6403090720b5001401400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 623934613 1250 623933363 623933369
    0x11120a0b07051c020a02071208070b04240209030d030e1e010605101e050f040e0c0d0c230306010c0b1009020c01290d03080405030705010f0b0f03060c030a090602070c 73
    0xd6112004420001c0c0740811070380c8223144071a40d401415001c50410300c111940142c00880c203004946d200d04002e60f2503802002a1070701101000340003070515526074050801654118140d48000032409001c8080c4e49100501c41003a401ca031f4a413940c210310b4461030320194041c0c140040b44181e56100010300c5110072081d008081884c2c80c10152480e2a80280750104c450a8100035080950354800c50803140202d00030500c0240040c0c0200e00342403158000c1c0c4080000800042c080c43e9a0300303100074034084628040c0503500071000070410240070920f055034400c1c201a0354803444001030743c980199506010700903000c8514591804980c00c40c1c6400200106c0c40d6290011680c110307007040761145030221001c40c00d4070511080c4d2222503681d03410b560500c1c054141c60f10305240d469505215003036102d48200104190300e0801c80d03c0c6490031540111701c04000803942c1d041d180782a1740c01d040c1c80754011100040449000c100150100701268080c0008500404005041103255a40c4495084803a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 623935863 1250 623934613 623934667
    0x10e011d06100b0a110a0818090c0304021804023706020a02181906120201080606070b0a05090705040915060503150c0715150311120a0b0705 62
    0x990103403004001080740a401001108449880c54600000c0306140c4c0902c1c00303d202000500901851016010400c254119030040c0b4020350315060860519010351403d400d050264a101001a24807011074080e00c1c41260050201d580320901c004403400301140042080340c1c0884002c040000702d280780c03214480780b2004501104400c46039003100040c0045950310000441d4042c1f2125001a1600025540d81003020b8a0035101901d42584508441c1041110002c043c0d18000d80001c00b080724401c0110428000e80f26000141c41e45030a200c094803410b1806407800d070291020076102b41807503004a510004100c142c50710f00d9100e4000805a84001600f80c0e0030002c0168030500c50301c954800d650003030030114020051812100e2446a01101c01004000c120f2004240003090144021440c0b008000c40d035010001701006201400264401d40826100c88a506000604608103c210a80c4d40142803000b81800784c419a00d0201094000b0b0901b410848248852100803000d0704040d0080c403400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 623937113 1250 623935863 623935901
    0x1204030c1223010b011d01120924061503020301030b0f090715090312210e0102090406090c0305070e032d070303020a0506060901061e41040b0405010c05010e01 70
    0x2d40300060030316206c1050803550903400f80c500030140c0c0e0445e60b02100800303442808140000b15051890b4440080700c050800c16131107542c51000780305507070300c03040030340304c00d80710341c0e0100040d0903421002c0740402d000040c40f4248100128142a42d055410340d031048103001158a403e84074104003681c00d007019514804101d8210050042200118140e003940d425407a1201180da089552085107000c131a00303161540e50360745220300400100f0b40484203d40c901400500034160381c1d28100d8010004103900e40e00081c40d02002c41d605a20413524980c0041006000b80114001001403052504a910f41030918003002188944054414007007800154040e40280c1075003000340c205181080002003c85102e4040c240041c000b25402240b160314001c1c3c003203218914800014400c0d1000c6510981120100c05844242d84044800c8941421450f119100403013883c6c1550080352268002e034060811140c0c8144014025944105054404a4042c3c000418130b054141240d608649601c00744421b44040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 623938363 1250 623937113 623937131
    0x4151d030124050f061909030f03080901140105060d0c05070204110702030609010507020a062720030a080a0e190b1b0613080f040b0c0307051204030c122301 69
    0x10700c444031001004155215201308604000264041c4150f4800318181c491003140a00001e00c5100060007460307002d42003c2c2a452a400c010f00811001c4681e08240c1d8241455101c980c40c00c00601812240d0183c46241400c2c1120380e090050300d000542002008424024003000d03a8490160380480b88440c0039595840d01781c2d0040c10304080000788860b006a04080900c03603c10b40c00944440c1c3c0d19007001002600c540511000a01c49403143d000c41c800b80a0942400244015007107101c0c07200155403109000494100285a150082d116024005000c10b10030840c04501440030018007000c01441400962105045544038813443e40010466150109440c503103007041d03980624100c41014020525450140c5680e08010800790005103500c00c0840c0004181312850159030103052501812a101c100c0501190b60720341003d40240c1d0141b0803407500d07100e48030900d0111025681c00c4040049264101010400d28058082c4119500c02c518000414a0440541050f14a407804030010a440d55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 623939613 1250 623938363 623938421
    0x1b030c07051c1b0804031a06030f070617060411070f0308060d1509150f0911101b1703090604030e040c02030706090c08060f070306060504151d0301 65
    0x10209081c003000c1d60044a4030710b02242c0181508802c061280792000760741d4002e00d40742c0d082e4050b1340c0c001440f6200c0c6400b0680c00c0080360082e14412202501110036211130303d80c0c1c05588440920a440200f6a000380d0410009a0915441e6100740042d2000c03a4000c003103a51900d5591180005503051160000220101a032050001c0e4004404031400c40d0101191340f14611000c102c81e40c05006c099503179400344c0c1001104480000902c0d500c010801c08079012689942c05030580b4001103030103006007481d0f110b1920384000c01820250707443c0c0d142e00c080d40c07104403080c00700401d0150603600000480003210005103040c00646c030410800c800f0703250b28201480e01500c504c5002541038802c03820000d03d00c820075400001d4520b00c5802000c045594003241c140459000f182d0317045004640186000c00100440d0110140c0c0100e47c07039034040043c1907640404940da40124000c14007103030081100700700b040703109890003001031491102410017544404c1c0003038212110888518014101c840c08400150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 623940863 1250 623939613 623939623
    0x509010f030c050907140307031d01020903010501080d0c0311030d1a010f0c031e0c0506090a2001091a0d0e0d020708071208031e09012a020d081b030c0705 68
    0xc40f0955421800b4100950f02030001840c0d040040428900840003600c511700c26006407134040c001c1c0301407034481880312404030f0207580030307003c02c502a40c06e01000244c0701d00300090340b4060060680e00c5d20031889150f50201c3c1d081040d08441c2410b44828410318046a40c0d0313109107509216008140480310708090b0014000380c8450b0014000d104040c003d00001c243c00c408400740050800d009258182000282603415101208016000703110754810030040d0344000804c941d80c14000c419410648a4001341d007000c1c040c5001d0150300054107045c042085400790224090b1003603201c1d00e40750030f0810580746241156940f8081d1103096011803803061860b501070103d00302030700d0800e000d0001c4c141090100340825015401c014600e080000c0024001c41414106552207416103400c500642485200280682038290518071084003aa803628407a040c120b403941194140358016201c45449101d017035079420710081c00c096074060400554180004200000c511a81c0c038807800d2030f1a031405040680c40c02d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 623942113 1250 623940863 623940869
    0x11a09090a030f1808030c031305060414090606090402030901140a0e0303060906180703020a08010f050907080a0605031e0607030e060114010201060e070c05010e0705100c020a0509010f030c 83
    0x2074006075140c0e0301096008a01e0400704074142402007107882c0599081c801c0d001280d200c003201e4080803d0420a50601100501d00c0c45003031840300b8042030f10fa40c02c2001d184118842c08940203d01c013110809805e100c10469407241000b0040707400c4c9882d250120b020b80c3d004031018959655507005c00b4100f40b42901c1c01c0781e00709100d803070100118140c00141540d43d204c041e042ca4440d800110000303406a44110500d414820002c42d00e4a880c1002400a0042e400c0075580c0b401003400b0b80d002003102003d100746c40c0d013104d034001d290010701c0d22420401c1d2040c003400307040c1c00216515a00080303245c0d02c0401440ca4407a0124620341c41c1c0742d81c9a0880b07070038010f018109000305400c295542c0d2804000060003030641301c3c940207694003812183c005038010410f59000107030414141c0704000c1c206412414000c0641e001e60001d01103407000e56002c42c0c80306801c1c06110303400050020420304451040e21003603440ea00c0541400b0b14503844400003181c40009900850f010184801d040c4108103510002d0f00003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 623943363 1250 623942113 623942131
    0xd0603050d08010e16081003020a0303050309060a0903050423060a050a03180f080c1501060e0f01030504030203041e0b041715090304060323090709060b070b180a05011a09 75
    0x41e0421719030103e0501c811000d41c1080150b0308010849410744050054001c6038014690031002e43d886c54043d0150300200d0f0050201e005100015008d007410307000723130f0154613419941c4906d02802c2c0304801800fa070003490742d03507007082070f44420304c0039034840f00c000380ac0c52021603e5190300c4072880140101501d10a035100300142c040400c00700b0000d004001490742056108040e10b80700c850748041740d03107402c1003600c5115609032602e00018416400491042c03002001b0703141e00320007004000054059440548000700103074400c1204200713801120a03120305d41d444013402021a283c0d2103444d004e82d41c02036000981200d1104801280310038007000040c18900c404d101c144000d1820f400700c103840780120320948080c1502e903c000350103889031840c003182503100103894114605100a88a54404072406600e100a10f08100410704c006084261202e507603000740145903a644040c0d00e903c04040366102c1c51041e1040b82032860004000703014500389080700d03110000da0603c4010801c158040c010382030201e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 623944613 1250 623943363 623943389
    0x1305010302070804030b060102030d0c030b010e030a03120b031002120109061d0f270a02040c03060f050f01170f041101030608030901082203051305010f020703060b04020d0603050d0801 81
    0xc04010a40d01106d41008142d6010390f981d000507421441107032211441940780040c14824290194003c005041d801c0e40d030070f0341542d042c6e001c2c582e80b00e005150140c00700c3c024050304000808030b078001400481c4013405452007013001c0c0400038140e03001038600280d20701074040180040c0c21a442080e0013402450715001200b1200d0b0103100403400b002d4039540351080044001aa502254035a05a01c0481078800c4554200c170400007545030801484100d00c176a04003048903501078464003d250541e070580d101e50705581c1c0390500300302d0584052b044e603030306001007d4503541412450081040c460b5000ea07140034914a001d240003141214214141e80c18107241050901c140c4d0400401d0301c40d002e4007800d0403015601c1c0d440c00310701d1142c3c0706071000c44000d03010403c000405a00c0b0015048050782c00c114586920b41329030040d42d6040b580111980142d10070f9408002040240d040039150301800742005243c440304081440c183d4000707400036141c65218008010446a10a003902e0040c424048010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 623945863 1250 623944613 623944627
    0x51803030702090411060f0708090118080c0f0d06020412030e04050f0403110c060c0f0105100e04020d0305040806010b0c150c0f09030102091806010801120807120309050a03051305010302 82
    0x11664040070788040c007001040710305d243d66512104c044404680800200b1910707510245440c003002d074000d074181ca00103040400c01e0341e0b0388c0202c0305002c016189c00c00c000d8180160b1042c14072540c0e0718440040d580c86540500c004001c00d03150f100500243c40c03004000d040c01a264100942003100740c5d02c400e40120318180c104851071601000310354000f581803400002501348204154a42040c01c000030758000310005020b00800000182004140c0e1414020b001540c1e034031043c40701341c1a00c0e00c200c860b4008403100050040c42e00081c09070303250b0312030b084c900e00342911510100c0c41c01d10300340c00858240000042c0302c48010320801100303daa40c21100134040074134000ba0b040c540340c001c0f5184800a4003001c50a110565400e4069811284000e00041400d450000b11a00401010340c4c1c0180480c0f520000855540020342c0c1c000e40150f00610620f1816009a560303060310b905a914000c205a5552800e0000920500c0505440e9029507a4035488558a08040030050700d5580002e06040c4100072203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 623947113 1250 623945863 623945869
    0x414070f06030b13060b03010f0e130f021201050c212a09091e071704031d1309030906020d0e040b01030b0a18110913090503040506040303051803030702 67
    0x490107403101c41c03501150f6040c15102040060103241c034034821190070b211020070364100c00005981280d21400c200054990313610450b818200043d190058402e02c00203145000c605410041034010740b0190056080100a0100d00c0c00c6071000c1d1001300711755800160b040c61000840142c4d042c0c0100805002c0c03001d0a20701c061384094181da0b0803400d0740402c64807800300480b1500e000d94509040c003410365a040c1c80e200c0c481605551f060171f003170109280c8010200c2c1285118824000b6408200803a0107419119620705461541d1400d0199001491002c6814201d46421f1070f030301c800074001d02021884900c0340c038010b00995801d802100c00c55020843c11068281d01c900c000704d02540070307200022a1301c50900101c024102d550000c540010083d040092031f01c00d5103180088624142d401045252900c03076400070544112004103074001d0f221542c508030303104143c3c001c1c45010310840031603103042d540354042003142e0001d900903004148007085441030b450403c24503885c031240440c081d40c60601c11b6400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 623948363 1250 623947113 623947139
    0x515010f110708100f0606050a050d0b03010b0d0f03110c010917010b03010203161403101512151706091c0c02130203061e0a0b0c0a1a041407 62
    0x52a02003008561519140800500642d40070f040340d40143c41c0380782a0200410050308010041101c014074002c03001410912880580d65052219502d8610340030300307169444007801c828030815a155680f00d94055507580c803001441102c5100321410709065030030b410302a0250745410035058103a0050200119a42ea00c031440006552032003180b45410200b805046e030040c034200c1c04094156100009015044031107000d0140800001c0c1e0300c0c0e1381080d0441d039080d031003400241c4415280a040f80e0040c0705040c10b01604c41c80c1d80c5403904e007460018142d901c022080d5011003642e07000e40c808080b4144081040d26860304090840c003402400c0e181450700510b5981e1141144161000c0da0741d070100031081c1d101e041c0310402c0a800400d02036400403542c001e00f00941c41903074814410300328140703108602a42c50348510303403161004220040302d900c1d04c440300d40507602605807004540a241680b000090b50002070141040e07407241e185146107064035148041141160307035100190301032001000340c01c80000d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 623949613 1250 623948363 623948387
    0x31f180b130e1911030f06010302090c0c030a0f02010e1b040b0105090904030509030703050d0f0f210b030a06091208011205072306400e060a050904060f051501 70
    0x1c074403d4001450605400c2040d44240705a030500400441804050001907440c0c16a40222018481603d501031b500039140700d400c91050150300140071007180c1c280a03114181c103101490001046015000103500d0410341d484040c480c1c224410314070f18565092178450203d1800007030030080d08d0540e2007000030740090700040c80101007000c0000c60401c80e031801e10055008641c440112680c00303c16030406045445034545810001c1c84a03012412b00ea48500341c40a44440001611408506440e07030500291442d15541601031244032000000160a0b1107502c1c4218000c0854810300007502000800c403002c1030340402c00882c142007150000c00c401040d40c804440f0340700c0c040600d40c0ca8091001c410303188200c4403141e2004000c41e00250301d201448810465640e820124540804100c030120940c4201240555085846880500000030420700c201d802540040410024903954800a80e000d0b40c02c5400f02e50950b10362218840c1490340b8061550031080795802202161600b04c0002d091020121b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 623950863 1250 623949613 623949643
    0xf01080604020d0b090103060e0c010f12270c0f0e0c0412151e0507140a030518010606021f0218060a12020301080c24031f180b130e 58
    0x14882182c10303241c0e21004d0341800180c00100702e581e40e400d0950013000640b00900c403a0241070a4041c03150700c81c4022070712148076a10780349103944482600034010544510b50b100b850140042203450003a200b000144a58071030310f00c2904036414107012540c0701a0650080240312200c5091001c4150904117490035641d001000d041031707010500f814840c8600690881038001c1c54442d9692815031004080b5080c20143d034020f10032a1100c01080310241e070020086a04607005012804a543c465009560410140c8004803803c2000c5560142150011351040006da4002034012010030a0043d41031440f50307489030214105100d441004440c2d070280180c3c00c1c4140d030000ba440207082d0081c3e11f00c80052510202c21500c07582c407007035250b03a90540c0701c11032881001805014003260130400815440080001401070070743e01d078110580220522a803d4000540b11440040b60100500c03031a180800d00a03038020450200910500001c0c2088a070401121418440741198885001403121200075500b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 623952113 1250 623950863 623950867
    0x6030319091d011d060609060a170c071209050a09390e061305120a0f110f0f0904080f0d151d01060c0b10091d010b0f0108060402 57
    0x350608580019042e0030090703040201c001d880d030700c0803030105542d4141c0c1c4200021a031000040301e8609115401107442d01c0c1d10000030052907195081520180100741014186102c0d0800803000342d8454060440348499072050100d2088280000c14103056035050160910600090501000ca23962507114050b5444007a240e1081d03044807551050705c10b0340700d020b418050040340f0348021b0b14440160342c1514035000442c81c3d2580c0e02c00d807411008440d240d20121170303003101c205d03e00024881c2c40301802d4090841401400103406c082440080500e0f220751080705d030101880034103020003000a061665039802244a01c24408482d1528260b00781c101d908000f0440d00e607502602c0c150100d10443c0681c4291504048019604029004078002a03a280c900501000c0d507503040313404140c00d401d00c1800009500e07005040040380400b020035410002c107001c419540e980340c2c1500c400f599840d4410520b40c0001c003000e11842c0c4c20a118419842004660782c401012030310f80003c10804001e0322561040ea40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 623953363 1250 623952113 623952157
    0x4021906092303030304030903060e12040905131725030507110307090f02070215030c180619020f0f0d090501120905010e0601032006040b090f0a12051203060303 71
    0xc0c01010040b40c40c02400c4950300d14107440c005107034940d079100c125141814a01210710006021034a03001c80c0c8a9511001d04080c0b40400340c4010b010b015040182c4542104144404901449450245404082c0449594415178401110b4480c1b2451301d65024003003a100850009034050b0403500320980001d0542d0120f407000340041d01705981603205c100340518100940403000700c0c030380182030300c18000c40d4060290900348a500049210440d00000300c428204109840d95003141c421050040c006000700381010489070090b160940c1146500c00541c6c441d06000c2c0b0150005c000d030691400d10300c0301600c204084884003816200ca10f000301414402c04820121880c545030748500c52443d0800d0003030160800c110106600da46c02800159a480007040c42403028030741700c5841c4400014080d0072a071800d4903003d28000540c111101107075110740c2008520350240c1d100502c05018200100e5501d080d1007107858001d190410464403c00d21150510801029a9000c000d03109590000f040385204255 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 623954613 1250 623953363 623953409
    0x70f02061308240906041703040507051903150e030a030e100501030305090901230603040807060f0209100903120809120a02100e0303091e010b0402120402190609 71
    0x18140c002411a21441500e80c00c0c22801c2c000d10070101d1401d051103c0aa102d040f483c1d500c4503c110342c082e010000000d110300400481c84003d45e4882d0040c0e007900e00742c544034130025405a80c042003031000b001c0344034014030074400e26032441d2a0030040c000d4100141300705108181c0c0c5034000c1440c894145a91401504005181801941580151010104034641c2c5a02e0f000d8070075000340c00040c0c0144403603800800e481c0c485114000c0c0d800328104048641031072b244200291580010000c46500b0350501c56080018083d016044901c00704180c05038455181c40144000c54070740d51035003810880d45600401c0400c034403445e404084e01492602201a98800d1100c61030070f40c403121230021654001850341d41403503012401c14500c2680000602c1200380c08003003143c0e2400705072181c5600c0c5c0c0181c8145540c41d01c00100c41403030141200300200341041030380c0c00141240c00c4960328000c030022650401003149498000340740412584906403841c0713030400701d004001c588140103116014052409040c0b51320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 623955863 1250 623954613 623954647
    0x1302040b010905060706060f06090e04262d0708030c030402030a02031e07060309110d060e03070803341b170705060a02090d02010302070804080d050301031403070f0206 74
    0xf0f030291000b0380d94031240c505036000300b0140c41145002401d03020041811449822584102c4074410b058081a40ba248c841f66421451400d40c0444120101e00000300040480054001c1504001880303003407510002103c100007083c900070100c00b40c0d080000000240d0b0b0b04c81a070742c00001d240b40150300caa0b07540c80800d10309215140c000c5d60600c504051482a01c0307036249100c0d01864038500341c8000540d40c00c010b03401d84400620080c0b02d0000317621048803909255a1400040340a47d0380401d207a5000b0103000d0455002c07034410384000600004000c0185800e00b0400c0340903080614101420324140c0c2117181100b4100d80c008100844841e855184250387d13030b0441d4800d0723004028000c480c0341c1458109541e9200308021150360160800281041c0c800f8400c1e50380f5080041e111100d00485030340114000d500450007201c1d03500043c480030a14850070008500042c0f1503480e450f9aa50540c149108906003030500710009500400c0303003000207504409504243da9056a4650b01c0301100b4174103400e48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 623957113 1250 623955863 623955869
    0x1a0a030b04020a0f0b03090f0c09040b151504050a0b070809091b03070c02130b011e0210061517071d03031b01230108070e100b07050304140103051302040b0109 70
    0x41c00070010218040030310100031801140003908440c551100b480c0009c2e107403554490f004e68400100e0000601080034100d68541c4000301441c00e051981c0000f00150500740000c103804008400031505000d01d042c103085400152420071000c41c00c28815507901c1519100b419403440c014000240410244545981d002c032022503485001507d918200400500d20900c10304181d218030304010200000c1109072080d182c0040d0180e4409450f01d2401c03d0501031a0000c2900608611031104100c44c01d4269200d5103010341fa08041010081c0e138242d4008040c940791044036243c000881007400803554001c5091103501020504555161804000107800c40c0035031002c1c0000c50001480300000c180041d4000182191882550445811246d20014042000340940809588240800d01040038007821996001e40c000002d420080c1c6c0768002007046412941c4201c1d40d0b540003240034070402081d0240a1001c4d80c0071304e010001490100d03100d04400d0358450000e4000c5070b80784010300b01c51340708528100107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 623958363 1250 623957113 623957129
    0x60901090c0c150b010311270f04060821040e150d120305071808030702120a0f050a0201020601060e06030721090f0c050d0203060c180a03030201050702011a0a030b04020a 75
    0x40340f40c40b03071400d001a2110066042c000791400c0103c0c2c10001c150b42c04e59042c1c4451103082800320300c241c45185000000358969681c094002c1c07008820603980e034000e2001030804040604031501e0070605260101c50009402d081010b4244018000c1c001c00700c0d0200d40c02800c0740c1c854182e480c48100420303580c2c80f91000c0035165803031349080c01c99100c0d010f42142c1d004122507a2403404404d801011140c142d40c0e01e015494107070b041040326a01624100950410001e203a200381c6441d100541e40f182c145456641088426801204403d0259038050140d24014000c3e418180c80580010300021003a2000030090001c1c041d44c50345104080758450310b03d0b00d1500d0b02c000104100401801c0101804a2609080320f1070319443c0001b0035141008800d0071746545c2d000e40101101c0d280d07980001e0040d0000c000900c02c6080302d400e41802a0307030f030880c50002907000307400000e440d081c9100008d007035420919116201d944010718440c0182c031008106811641c0011316814031352610b10001d2400040c59001c1c000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 623959613 1250 623958363 623958383
    0x40303090f140c0f1c061a1f0f050a14070302070e0106030b0a3807080f07020301150302030d03020c03090a08070f1409010b0a0e1003020a1403060901090c0c 69
    0x2c071410000c0c1c3c0c018550720441d10351a0024401003000295036040a000f031a01c0c01007484240041d9158110603240d070082ca141801ca00c620390080fa44d04401a001c0f603611042880c0f111007841d0300701c400c104d291421480d00307074502104024050551401d4190140244a00080c0f000616109001c4200030f408032002c07103200340d69180030080180c041d07086803901c11101c3e0400044e0840706001458000c045000010000400c2940e4845201100c41d0791100350810030071041000a60342c4c0c008104d50160703401c002d511044e05005041c06c5aa81d0481c0543c009100b00081c00540e0b000039100290403018507003d6980c200d00d0320382c2030850182c5044260840000c06021130490000304010341601c0f003001400c0c0b03142d9031301d2039001c0460140b0074016800079648001403045040e44030040c2040b10890400031540c841803004030345c0c0b210000040700700283e4049103001207a94406541038100c404106c070541141049000035401c014123100c0d808250390b580114030383c03040c001c41b00c0207001d54111051031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 623960863 1250 623959613 623959643
    0x11116030302070f06090305070b03100b03010e04060b0303090d060f180c060f02070f18020927070203070b0a090606050a0e010f09020412061a040e03070501060506090603040303090f 80
    0x10795100707043c0c0250080801c91300d0000c03400c02d226140c10400c03a600b00d4000c00d603580c60480c0c11981940b01508a550303a60010300003240b9940c0040081d030003000114040184d0f4901800c00108071204002428880e030810064020b060f074034024001c142c0e50f0030520000360314020100d0307100240721610703104285180e40c1900300180107460110004590352138940400510001004988940040c01103204525040200348042c04121a40c800700c80e0840c5c2005240c41034a40010b481d41a00d000100c150075902c3e00b9103804499070840c4a908101203000560404600c0d960f10300a100001300318012181d80e40d541d89050101a13041800201009400c40d0b020b90f46444c407140e0590000d000e4a0400c1410000028400c0d000703200b22022a0300403000104030103056a2000080c280b800301e043d01a80944407122580d554503c9580300400911006651761280c42c50b0007400d4448961040b44600c006004020950b1540000c403503000340e040c40d00182c5092685466001000300c1d020103086d2401b104411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 623962113 1250 623960863 623960867
    0x120e01060810051609060503090102071a0712061401030509070e160e030604030e04050a0b060d0b0f061303080d020705060406090b151f0507060e060f0a06140111160303 74
    0x180d200e202214020710150313441d41d81607030700f8003400102e400002e541c6240410040384118055600448882c00161412400362a421024284413003024900e02c0c640c170030300c0b0b10550801803181000e204244203100452800842c148052010360380740303062513150300000341d0f194018051507024080c0003545000504204a9903850007041804100c0800d100e070107841480c0c0741c0041e0084c8215450795481001c036240f402407001410001e4280c00800b0345071007108a07a551161b02400062210070720024203800014100040c0040c0c685c110340c051182000721260705100e021440060700d030816410741c0c0c0c1c0c02018031001c0c000d1003220303406401800340400b4041006059000800110f018244080c0c0e2500c4440804038004100080b5aa2280901020300f1200c4248502c01100c40382505045082551a0f02d40700c0950702c19094503e01500518100400b01402c2c2420542045c0b80702c0c81000814100b00e03002c2c0c1d803000791030742141c10710817607011800142000b0801030120004510b100741e0b0003541d82c500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 623963363 1250 623962113 623962123
    0x100305150607140d0f1407050a060c0201090215090406090b101b050a0818060c0a06230406060e160c0803280501050103050121061a0a030b0708150f01120e010608 71
    0x1017000000e14038000740030070300c03044803e4402c103a0b088400382c9050b54980d6581070050140100c40015035480301c1219025a0703c40401c801803089a0320301d60b5a50395101c0030001140c1e05900b00703800540c600f18003403110b504c46c403050850031881404d00d40740080040d00100814006100010620b10a0344451000c02c240d030005000b00f0194050403114000495040012038001e00c0403005959000060100100314a60403031902e03000181149030720320250035465007108504403402d0713a245813a40e80411036044d0401c46c5030f6111466105c007401d1403038585c000502c40c1007400300107488c424010001c21b811010b84009907034409842c2c0180e0120003000c8000501405092207030343d001c40d103024000503c0c40d07403800070001082e1158440e500005c503290707903440042c80c05a110072004602c21109032020b0311020740000180d40500002c0e0b0300303440c04103801064824020f012103000c03203541d4130781e81468450100c8141e0610f400d00f0f2510301c12091840410043c05641540b000720341c00c0040c000303a12800810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 623964613 1250 623963363 623963387
    0x90f0b0c28050111030103031d04020d06171006050a030813090507020d021b0a030b042607170f0d020a0c02100c15020403050c060a030f1a100305150607140d 69
    0x4000c0c400324131035040040711030100b4800a000328001004243c01c1150301690984640001003005003085014500c0004035140d940103460000402d603026410124200440403241007100400d05c02241480040346581880380302c001d00342400481d40045080b03415000001410402c4400c104c1c2e032070148002907440d8030002e2981d0141c0140c825001800c801c913411201050f0001d0401101ca07841c0d0b95801c4d00c0c0a40041c03050341c0743c501c00c01c0480401d07000c61032100b403040940c0745030039140c56450521625400c42502c0c08018031804110742d9100d480040261400d2601c132001c01600d41075509401e881701a25041d000f540050b042e10313001d0829800581c02d0a03414062000c0c00e480c9203140ea6240c0c102d102e40d000240407540300503540000d03403500c4001000400c0341e40c40c2c0440d03110b00f4192864213840c1c41d1071024206200c801d0410440381800c0000d40c108006e1440d040c051800c0c140380c4100001050710001d40101070000d410070500ca080f00390701c0340e4800306201b2580410038082d402000b200c1d80394 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 623965863 1250 623964613 623964623
    0x3050a11041e080a030c03180e0c07020f0303040b13080309091302031905010c11060108030f0f040e0f060f0306040c140a05060309070e060d0305250f21090f0b0c28 72
    0x700000f080e540d00d400001c2072766901d60710050151140540e6031260f80141500300d0b4424041083d00b6850b4505001030401800d00414551300c901403d030f5002c15120f030540102c10154020300030901c01d82c0d103440c1da4503000b2203020040342c2401c030076002284c240030044900010803025130300d60313074100041584194503000752592821350090003010b5440d01c0e81800e201e01082da074402d100103420b00101800424043c1c25070542286415503580150346982000c0f10b040c030607204100c040000d20700b8403921100c580c5804030041d10709450b10380d5402c4000d030315501a20440c45004010084582c540d584810007600f801040143c0b82e14100c8140b0360341d41e0150189150301c4c0807400c0810468108111604550340e410b8803034608100b600c9584403015240d54000061340c074080d65482d000f061081c1e4198000f42e029140c0c0814048442e2840d0081c242101680740401410713140801502d4441a042002e588018144039500c0c2000a0718a00c2d21200389c1c1c1c13a01450907904501d2100c085001d5080546038855 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 623967113 1250 623965863 623965877
    0x180302063106080109020f2a0106050607202403040c0e09060708070c060c26010b0a0c0512030907080c0312030a02130f0b070303050a11041e080a030c03 67
    0x544040c070318246100d030002051854006101c00140c40c0c010340b004148070041d09040ca40545071038000c3c4040c0c40c3c09000000010104241080800e02074400584070a44155241000c10359a030754400d900b0103c0390031442844c102040503070b03981c040c401d20343c0c2c40f26214010701c110180d1003503407a0b40c9c019641182c0e1135046041c00914084040340d410b20031070302c0700040c0c0042d40d180f100079607240000900d03580401040c00d103500c0000e1600d10aa007541d80c0180c0d00c030001064081002ea4080e580034003110000d0680000410590751741108a6881011701d14100a46400c0792a0042c0b0344480b005054010607404007c20200d06000030349030088a810701c3c21111007070082c50505807100c401c854107141d01e440400c0010245203090700241600c0c9070101c28200090743d600480e411a0b00103412004003c00000ba04605051f45406100e4125040740c90821031140c1e0a0b00510592095200700000341e85a958100c1c40601c03140c107d94010825a41507440c80c0d200c41c500142a002e00032400c90200e640d07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 623968363 1250 623967113 623967187
    0xb0307110c030714060304060b030304030c080105100807090b04110c160902131421010f1d15040f0b15040c0f021e01090515160203071218030206 64
    0x700290101c103c0b00c44c0b42d48000740307031015000d100301c0d64802002500d05580b6013142d82c00903101003004000850245000c641e410341000602401d48002030117001410031020f0017400702000c081040405c5440480340040c8096444c000304015282c0200c2a5080000105443d4501203022450300c07511300035103104808070703519403c08900324004c49405000d900e14819042c071503410101c070700d6551064000d00c3d00d9000060242c6054102910002c10181da07515020624010003413409405a40d0300500400e0004400d407000180d0384e110207145901509c0030806c045818050103460074000d103508800046500c2c50041c0e044090620000070355800340d480c1c1031081d00c11034891a2a560400301c5503001c0d00c05240f001d1030950401d422a0814481075607640803100010700100121a00b07071641551409041c90003116032203a1303200c2c0803e07075402c0d0b420400c00c0d06e0001c0c903040801c402c0240380303040040022080700381800a0682d203400c020340240c80003400880d90b00d451a1034000305000c03002881c4070200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 623969613 1250 623968363 623968369
    0x315010e0114120414030c0a11010504031527050105060a0b040b070f03030b04060e061008010305060a020f0403020907080402120708120d0221091c09090b0a0b0307110c 74
    0x248244542d28401c5040c00400603c140311810503402500400a00034103062003204142594400d91854190b5800144c445007044000000f294201c0d20034204030381020700d1030710350b0000c0e88240c0d00307003610b0240e071403000300d9140000da54102d6141c0038260380ba81030302ca0a0b10700702d4028801034a5040c45030b00119800207582940d00c01f16015204e40c41c04035030a00031540c3d40c082d402c840c0200f00701c0c240342c0c85040040ca10340300d5101d890024407244810401504216042c03005c0955010801c0082000000052021880010b0166007009001c5401a6100f0148a5000180c015900025404000003081c4810719910028090007540200e980e01c205100e00180240d580016210f151035981004160400c010013540c090b0194900c000000343c0382580b5000500c1c100000b143c0125224804a4180300c1c01c881d0402000518106109419061400c54140504840b140d8801c0304006526003100d480642c45100c061402400b01100c000c2d00c0741001e0001170001480300c01a0140c51044034928030780c41ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 623970863 1250 623969613 623969627
    0x3d080f15010501050f0703120509071409040b0103020d03050f0301060f030f090b01062109050105011a040f21050625031e0522030206160e0f240315010e01 68
    0x340b058590910f0a00c0c0e40040743c92a401c400825002e20981000b4000c0142d40343c0103092113507040c00e010300040b50a008096001c85400003425010b06844410000041c81161800c1d042d42d0701100d088401c9100e5280403509845010884141c00002200009050380c010f149807107040c501c0e44050100ca6210030f07452040320803641000d4440080c90004110a07800341c0211107103403004030901da5900b003491001800f901e40d81350040f112a0754803c010051801038070003c0201c8500040c11610301880e10071650a0016240100791b40a40070060044001a60489103800301c1d5220b42501d0b40e5107800e041d9103195001e224992040b01c00007124620050340300e80704003a500482c600900320a40c41c45c0c0955801030070020302d2140c580c22001030003000d40742260001150684280d0041c82c00307207801540c0400c0c107401c51a254003803020b250311480d0a91760302c1d1070300b09a40f4425110841d020a100f688002c140c96540020900e2000000500c44a03d092170b00761036109400317032501c00311065a180119424 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 623972113 1250 623970863 623970869
    0x50102041a090310020c1e06090c15040608072601030c0f0f2c0907050418021f120905031201080304080604061e020a0c02040c02063d080f1501 63
    0x142c0155049410300044e943c040c000c4010030702c0c102c075804d000082c1a0b01072035070480c5c66241d40d0b0f40f00b2000c01c6030b0080c0422489401c640151540104100210300c4881107019601604040c40300b00f0b40007a0a191040a4440c1107449440c01d0a000305950b54240721082d800380800d42e2101d007140b0020407441490000b850864000d154451240c5140c00921101920f1015040050050b9001c4041811a114805502903c511000750200c949040300300411551150300844038410840c7e03241d000341e0707545444001400c2c0c40d00300d114100540c00a040320702c0602d0704e1203d81c0c2280307041d030f0103003d110001002c1c0041008440f1584140c1c0d03201e510840e6240610302c40e80c8080c1e40a100001c00050f80c6030041146c90b01005030505803c510324032800242d030071001c0c2040006040354805e0702503143c107005242c0f1a003c1030014059030b050034003084520030280341c1d1249803441340b409182c2c45651312180d41c40400c1c001030043c00d00f80d81c680d46802d865a441c0ca0103401640300e000d114a039050503000d0140d0427 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 623973363 1250 623972113 623972119
    0xc0206060a03020d0c0b0307080a0c090b04050f0f04020301230a05030d1b060507081905010317254205090309090106020d022e1e09050102041a09 64
    0xa0500d50381c2005036013428900e044500301c1500000040c6900300c1e9000e14010072031303a10740c1040d92400c81d00030400c8405850740c0c1c0042007890401080361440e002c04541c1078034415a0192003020300500811207284130042c1031034000744000000161142c29884a0100d51502010b0903c0c20708d03c1420410b80d840d150180c190b04d50444030800004501803041c0250000c0d005a000040b480c0a8440e001100e10440e80000824000803c1103481c1a0200c081c0b00300b0340c0c0c1c40c0c400300010b50440c0c440e5000030f1910311161264038000a450310b070b107003030844110b484054140d84400c8010128541650a464003e0364641d00c880c0b800c1f80e81c400b00d00512031452590510004034a1025034888a0300c01804000d400b218440c00204049256915101c50380783c040c20f60b50700201444009010001d03c4c011644016490a000040c814088401c0c4d140c1440e2407414200808101d0307941041e1520001d00340d40c00300c2820320780390503580f00803c50306402400032214144550104008000c03031000041c800c541e14158 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 623974613 1250 623973363 623973379
    0x3203030a1d06220804031208090604051b0612010b12010f0e0604020901092112090608060f1503100e0a0504020603061908070f080c0f0604120f15050a0c020606 70
    0x2440c0d503c0002601c400c0400840911100c18468a84251a60060300192a01b85c0340d442c603c5116038200000c10741020308a0024074461410791510307500c1e0007620340151507290703050b0034207031607541c0740c1054400114004482070f40959642c16244003c3d884000030341c03a0b0340030306800010b0840100c5080802c40c1e0020228103005d5582d1390821000f5030019481e241444860107001c030b003080b80116800208861408a1075032100c170f904100b104001c0b6075011004015a02c0b209201c00c0d035200c203003160030004c1543c3c80441e4880003000103048100203500d00d82c00038804001c01034042003c0e444101140c01d400e52090290f100c2400071004e4030030498020750011400c101141c0f803802c02c404c0040c80060341022204c810354852704142c2c00c0c070751035510141802c2e00c469014014084c040c000800760010858208604c23410300b2001c40c55501891080c040452105503022042c040800c0846101c1907001d1001c4945102482144d40207000c1a41d04691140c40d2030b0601644a00005080e4024000200000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 623975863 1250 623974613 623974621
    0xb040b0102070b0f13090c021f061d0c0d051015031a0d02130e1b121911041b021603031d011103030703141b04033203030a1d06 56
    0x303400d45d12600c81d0201c01070040c50000f810305054486d00f12034080982c00380c510411122140c0a140241250f411151840c00004000c034064400350750105494500344000c25a03181180324003603000d41d280c00004681404104004030011030768600660380a035200c001d100008800480880704410382211045d40c005501d001149800f84041403000e00c0240184512009444c154040d0b07641d0741031000c1c50381c2c4482c2d1075032091124003c0000398110b007501d0185410340c40020541d910701031614024800360340d440540d000d12484441c17094071400c0141c400d200c1c0c0c0e0f5005800003030011020400b60300600442e2061100030004101a40072280c155541800070320581242c840b070100c2070000745051200d41100000503490902c003941c41100e0079180010300302112001c08003c3c00005044d49808011040e0144200880c0b60954082e69041030146460908003081121101c0d0303180102040c50341000c1c40e200c03418070000021881400052818401c0d0400c07841c0205010101c0c3c3c200e049207400684c001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 623977113 1250 623975863 623975887
    0xc101e03020903031c0b040609050603030d020304030c0f08030402011101020a020c010f030f050c1b0703120305060409050f0f0c0609060405040c140705010f18030e09180d030b040b0102070b 83
    0x1501180b5401810703a0f10306480340d0b0840340c8405401c20380c1140b0a40343c0a100c180ea103403a00c24a0002e2408107030611062512200190f160310400c2d40450f40315a012003c281418450902c0101580d131000850900c40542e04081031603400880d400ca0002d501150040704880c0103000b9a81c81e40410b0f002412040c2030100107442c8040ca08c075000d010981e640c0c8440d0300702c108901441d402070340810302d8556540520310b0954281044074880d1841903028403410000a00c5205201690403003a02d000141c580317840d40014040c0924500c00380a51050340141d07008004045103c1d242100000308543c05078000ca01844441d0080484482e030008050100300045d05140d0420300620326a450601980c000503c082c41083e0480c400039070325699640582222902584103910704149a103d1901d40703d401550b0007401300410026813405040044041442140c1c50b00b8403440429074001515800405000c0c024020144620700d03503c128140348503403036954004a0703034005465450b801c40b072801e1105103030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 623978363 1250 623977113 623977117
    0x8060906040f11041a070201080112050c040614030f0705061605010b121b0306060d081c0c030903180605040e090c040207030504031203050f061002010b0604080c101e0302 75
    0x2495411075102c03600e0400003692440303803070411012041c50544580c03c203d580522881e442c030701002c03100d00410601c0c0c050313a005810141100c0c62a0b0400840313001d14035020b401e1000c1004100e810078209080030515101164215018104c10303411110082c0c21804496502d90b1140f0450343c004004000c20903544400001e0480d23824000c42c0003040342d100c0e10001c04c40d0346440c07100c041d546070402941d00c4102c10544542e1288058110011324841c01c2c07401c0010072140c5000ca0050850200050000316180c010720000901c0b07a0505040094442c2c0c20009000340200320403c170000340209601180d400f14803503511054500300d640780c0d410070f828900410a81000a4108007861245541445090365540003c1814074400d42e90b0310f440714903504d001010781301c20044000138103083c02c040103400000840310540c007200484107140c6403410f0040590040140281841e003240c40012b0200c0c100e1000074010585200a0324840d00741070718000110f85c003c0b02c148844007481070384812000031a1290300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 623979613 1250 623978363 623978371
    0x40b240a090807170d05090109170a120e0f2e020a0b0a060e0f04051c0c08030408131a160215120901050703180b07030b060c010203041e03080609 64
    0x20030008868481c81440e00c1c1003030f5907100c103480a018000c045601c660900c8026149001c0d424001d0901800400191120340c507405990310008918110603040300e4100003000d045a0000c5440c03c0903048070f8401004e03007000c4c80c02d4901541d030340d80046185007042000d050304000c2e001c044c050a0b0480881c50311640c03120660320401c512035010a280401c10301c00140e40940016040015814070301011801402d0000b4031105060181608020100e10041607070081c40d194041e900041c11048107080c0ca41030036602021781946408410801004004d10046c05020b528003880001d560703450708041c5800080340408104a84280541d81003400104034000100b84004d010052070416209a07416540100c1c00100e181940b80040c080040b0f000c0c4541078001c0304524060000035a52502107030000080e403802003003c001a0005000c40b4442d13484800706500c01030845584004418200d40030390410344064602c1d0036050b02d50800304130a0827200700b102c0c2d49526180f4141e1b998004001403890024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 623980863 1250 623979613 623979617
    0x30f0703111302120106020307063c020c0f0a02030c04090c14010c0b0403030524100e030f030a170f010f0306180b01060c1703010f0b0703030b030109030c02040b240a 73
    0x84604c6401c40304c1062020f0290115600643d29a040f900b801c10030f03030300308842100b4032140c51511040c80c0c1e0341c5604035445030f05159013100e8072030640c0301221001748500c980350000350040c80640314640c1800310307844131014000c07000c442c81d104251040104858407800000c05c0100e0351403041141014010428440344c40505090a00402d1a00c7d850345998080b0350460000790780703404002030a1229400b6141d1007482c0883e007000e45048a000c652070a00a4903080103012110800c41416a030800807004500c01c4e0405403070300c8840c0040050700d40300b0035042009103010106c0001d20f250340b050000b10704944003030860445591840d10f645009010102400f510810b181e600480403c4e0b1212030103008003c60ba03a0070f24081610708181d40c40214074907a20359500000c0004010100c0280018820784840010050341c0300c4803844d0540007011903440351900b5509100c4200305241c0c124044a0700240252403e200e142c6580c0c042000701015001c0c004241c90800c0900c07926414044003400011540d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 623982113 1250 623980863 623980867
    0x21201050d0519030e0909060114061e0c0a03141c0509011517010f1a01030c05070f151a0901060318080c07060e0607050705091312030506030f0703111302 68
    0x81d26100c8501c3c1614031099010a680c04c00804560500d80503d5911181a80142055504001d00ca8048250b65141c2520460011510b01501c85450300442c0e65000c51f4190709030f41d1000807011a840f0522401d060f004980310040307510445060108944030b07000182c08070900d80c10042c0e110b200410000e008458107640c1c50303038002018040b141408010f0070040198030203280320001c0440c2501d1001015002403420401070108032044e00b000290302240c01d003000708425001d8807040721180510fa00240c00800813203502c000788082d401040302144401401401480349000c60040044034a484441d080305c403203030040200c140709900200e5810369000c09040100704070f443d00740098001d142207500c82d030007e9108004240e00306900952400098685c982003541546980f503e4034058811079019018140001d800c10002c1180608440e0f0300180d43c402040500d80014001c0404517402ea001340b240c260070161020000410100b100c0e4098004c0c20000c007550144143d60240141c185200764007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 623983363 1250 623982113 623982133
    0x815040b15130e0601050a0e01090c05071e021008040305071106040906030302030301050301051503100b1807080402010917030d090204020c0628021309051801050c040612021201050d05 81
    0x1811555610034903012000f1880640403101e06080090680c8098410060040100402d404943c449030440d428548001002c107403445054820740705081005051184480c80050a9041050481302d62402036898100d080301c2c2003030640301814283c602901081052000707070000f880d015188800c510300903100c50f0809513640b0031a8103840c466041207000d030700f0110042c001400d003446131541c45041200240792200c0e407000403a494640e28080d0342087da8540c5601e2582c3d84520742c034050210056a4030a1041c40c0c0130704001c0001742d09a4040740046c41c4480002030346202881e50300d01d4080960301440c5000c81496000b801400e51101c200d80054086c40a45480001409050300c100d0b03603000301c031039207000080740e400030400404805014036105100e40c6280d102802c08843c1914400300c00001e0381e4803130310780c142138200019106101c0d40d1b081c00c04000c80211010060300440f07516850300d20318692002850800d07401040351880c40400040010040c80c90007031020081203015005449038070103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 623984613 1250 623983363 623983369
    0x50723100905090703020705120f040513180c0501030e0c010207090c0e090a0e19050d0804080c1b01020c042a12020309030a0905010c0320011103150405010815040b15 73
    0x3c0c04440c0100400c2d4049801414032006104426900881d91f200500d44903440480c59051301070340c0a414040c1d906c5d2174488194502950200c0100c18501e0240450306100d483c100d5107a00c05401441c3c0080d0500801003400c0c08001070141140c00142c0241c5001c60610790000d0080c845096508100844071100701130316158840c007c1e000c0e110000c0301095141c4041100c81c03400702440421001002c1c90801e42000c10b201280c200b004103014a8041000e840c2c90510110a008190484d02c0c18000c00c15a048180c6c80300e07205401218080c0c003075401c0d03e950141008100c40010b01a4400d00c2c03954408090103d04800c00c6d040401e50038288241ea40380c580345c1550480e0130803074034018184e10000313440d40080e81081c60326000b00000d00e403454040810390b8006007003040010701d2840452002401c041c4800d420f401809481d0640c181d902d40301c0c03500010b2000d0b50014540d5407406141740500210b0400f40100d1000c18002d6500705d21801a10b5a5889103da18001401480c1c20742c412481084555 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 623985863 1250 623984613 623984629
    0x203240a1e0f0b030c070305090a18321306020708220b0307050d0906020c0a0803100e01150509040207060e0a03080f090a060906021e0304050723100905 67
    0x24004041e038512500780300b40100da00200e9000010400703418010000514007403021180310710780c0740ca055a01c40302e0340e0000c5403034841c1c0d45e000b11100d19184404403404810719805500308149030216103010040c40221801008070881266203800400000506800c44480d40c85444521607030b00140351400395202c0c04441c0e0050703030340301403540911018036003003000703e8a904000c0d0010720350342407941c00c09070780c042c00c1407040e291080000c0c0d4580000c1401d10156a06a43d2584039607020384120728007520304812668012a03044a18240780361000c2078980c0c003c100241070ba0803010a1018004050744140c460350031400159900603000c0140c000050224001c0d502150103400081010345007074900545840801420f074120440900104089c1030800a01c58003c0f6400010000d18841d2500b0500040d215003400e4680ba4500c4044002952034440002d500c40c1d4040c4007541c1d42c0030f40300c00320030851001d0a50001c125041a003542c280c00d01e021562400c0c02841d904203d100343d6900e50100f01c1d04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 623987113 1250 623985863 623985899
    0x20904080309060108010506011b05100204081e151308040503070f0312110d05090414090d0f0207050102060601030e030714030901110703020a1208120108011a01030203240a 76
    0x8954088180309160000b00843c80c05000b803070300240030502d41540001d2240030a00c90024040c03104542c90018020b00780256108140000d605559981d25040d5155946030700030340612444040400070450800042026200c50104100c0c201d01c1c1d444000348140d00d0303410070105442c44081004001002d0341e041000c3e600400304241101885407442c204003407400ca00c45220401d102e004081280119000310f55054110f05604085440c4c4010303101240003898030056a00542400906004c0c0003000012417485000c4999202c0c100026040e60072a203841491040b0340c027581c40400403903d5503021390030441c04071010700100c038182000707a01c41d140055103504107050544c00000320300c2c071a03503400201c2c0012039070148020154246554041144400d15200c1c500d01e40540c00100b5042211020032103011000c010040801340d41c40b90703880c2e4024030031603040c00841442c1c6103101c100ca50003402030740d20071182101a0182251800220350001c010104490750200210801013006040004c041b405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 623988363 1250 623987113 623987123
    0x311120a090617060d060c03020705030705011d16060e13091101140f0304080a0e0306040b0f0f061014041203080a0605010203041802090102010b060706050a0b2218020904 75
    0x4070034070707122003e0128802d0414482c1c40007028010000c050300c4040464012603840000000c8142020310210300034001d800000b003860000040d40c0080c010150420861207a038951060900744692a00c113a862150040d040c810803a41c900070440715000c0e01c80e880f4508006080004894003110240c0308a85440c0001c44415104906928031564400c0d0f8809600100224061800050030f208001500009100615107000010700c81c1c0464440e01b0b1240c12402d010341100c51a090524041400c0707102141e6055481c0c481c00e002174903207119032211502a00707020308200c43d00c50603200101c5400041082c0811502030400c00051800c01d810080c2c08200d02a07650310800c1d041000c1c03103906071601a400141154014881400780110340c84860210004104c001030743c40d490580180c0c0500f00703000445c2c5d030168003c076608081c44002d800c04c9200d22101d110421000c0c1e10036003003014800d0701d074000008088190455801c80001c5a118006003c1060a60a5400029800108002801c44007120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 623989613 1250 623988363 623988377
    0xb0c070606081b1207051e03010203070909050708060a17010e03030702030a12021809040f05010606030207060b030d05220e1e010e0403051804020702090c1801050301120311120a 78
    0x10003500d1000300440d001c0201d83c8080081e2084030031507030b62241c03401194030071400031087c1040e91400760018212032201074002d40d101e02d0401c40252070102c59118a031a0282000d00081c2e0241c410400d0600c2820002c04c10b40c200c40c2450300c00714038901c1d0074190404a659400e5400e2800d40b042001d144103c9041d4021136590440180c000d11119104c4c480c82842801804480020540f03c580070440400958014802e5999030400c0000100e2507500a0000e520300f40020074081d5254005002c650b0048100380110288034050540c1c941168000300002542407000ca07442242c494410003090403210f00500c0c90548600d009414000c0a0703803a500318180e90768401820604010746c4034010007400300d603041245403540b00035000d840740d0000c213140300c00c0030803c1c0b2010340e60310b9055905181d00900101402c0c9800041c018155012850a8000600450701c0c18581d6201d8403c50341a81c05046052904001c140d4080d95414650407400392035010303502e803986950b95080c0180283c0c28035171380e44030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 623990863 1250 623989613 623989633
    0x160e2d01020c0306010e16050f0c1b061c02030a0608070803030402030d0801080616050d090b01051509030c0609031f02070c0501050a0e010806040609060b0315010c030207030b0c07060608 82
    0xe45820400ca00c2d0301c0c0030307411001c01085522582c1c41800e03031005031b008210000d44203c0104607018802c80040c40718083d808100b10b010000005400c144000b0b054045c800790301c203041d04122a5000c1c1c450b0007405808000481d00c15014142c000d9030304129030b0b0001149581d1141141803c29001e508402001c2e031000c0300b00000d40c641040245a2104141000b41442d410318200f65180e080061254041048010081503624820703001c480182c00c05001c100940c030074601d4a440d01c2802803007880d01c603101403500e00003400000070440310856002001031400c81c41e00c0050041a41045070510b505008030000b0100581040d80007030000c4080b4400141c2c2c0d84c996203480c28078420141c10040c1042018041c03110b44c15085504000d0580b0b0034200090309580381c40015003e020b6139008043e545007800f0707000030300260740c401950054070103000480144990100441d80e10f1200e00c400b90040c2e101075810404a141624480e401c10060881c080c9411450b031203e4064410b15401a0f10580c000306c3c0704 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 623992113 1250 623990863 623990867
    0x91302031e0702060c210c07060614030c010309230607030f0513080c100612060b10200309300a120509031c110d08160e2d01 55
    0x7034800749200c407000c00032400c00381002903035a240144600c0c1c1840d00000d40185030340c1c0d040ca5030030a40c1da1002d00019a0300c0c2021603007803580c00c40e8a01315402801d0040202c0c1d60414104081541c800c003600a28404c40d20000440152844c601c0a8400795100d45140c0e003403100e200c2109a0320400034000340020708201000900326030842d10001c1c21705180000b440781200540c2d00407103016421a440b541c0703e041000310641805954685a0000751415000103010f00f159840c0c0701b0038034050281004215010b606000172900801c0c001c000240b812070000d04910302081c1c805400110000c1243c1c18100090085031162202c0407001d28100b491201c48990214041c11880030f40095002902110946d980c4d500740c40c18800e031081050050200e1106010307142001030440352010403942c2d150f00ca580210140c0082003041d1488c4041c01807801c83c5ea6454000c0304614040c800010030360944171042ca81c101d030344e81c006072411f66002c0580d0f041210903180b52500300618905805803642251544000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 623993363 1250 623992113 623992141
    0x4030201021b010504051207140a030909060618030210020a05010c033204020105031b070f030809070303050f18060315040b030a03050d0c0e06131a04051c020609130203 74
    0xd002c030b5030704010400000450100341d00550f0b21841c602c2584446030392034080c200d61410b10080b078080c401c2c41d6100c4141680070b0149800c40d68107120800c07a054652000300c6980200015428500070110300400050a040354040f20407016403043d682c124156694440c20740c1c00c00c0c20f42500184d10f40031100358062020980000021802420000d000d00342c0d1089001614005c101a045c0302c0080000b500003550f11422000d00b00d844000d00d1f5aa1100d03103004200030244000640010346004001603109900150181c107503501929803d04011a051800300c650b403054032014070080c2014110b84a0381c40302000b0794003840c1d28480c9810404400c0c02071000b00e403144450244a580103e42034804242c1000448206a420080c04200361110013001d440a01d00d541c01d01d42c211200082402c0000310310701c4202e003039800004c400855202d08180414050240340141a444000c000400f09920314a0005015251001d0001070504e0599400502c05440307106100d10341c0d540000800501c0020555 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 623994613 1250 623993363 623993407
    0x40b01030504031205040c0513050a0c020601050a0b07171902100209010e0906040230101508090c0406060207030228030b0a021303060b0f0d050c22050403020102 71
    0x18007007000e880c00ea01c0081034600d2280304007041640e6000450240410610f80300c001e0700300602403030300c81c40d0380825201c01410200e40070360b2242d1034103218042c1d031403022481c1812101e008100c8102c1e941070503e00c0302184e021603000c03901400e03c0b406680b038064038040a0031b030601744c6e1691040c0c03240f2801d20203418440c1004464940d20f01c100020303032044c1c0c0c00214004841074180c0b8800070a540c0c0300e000c00c000784190310402186034042400c0098074040c00c0c07410703400301c018120000030b20b85030912142c8842580c0d01450b035503c644003154059042c400d0084e254840c2105046445e8202c1e4840403400301d64180d0049001030f00907450510960078500c0145440d04018084101d030b600c41140300c00e048820a002c0103107070b64218004102440c949030103440d0510881804425420b960f46424001880e20400f0103014000b1003807481e82c0c501d4494294803e080e0040007400000d143d51b42041040301001c12010407031000c0000d0030003050244e1080c00e10581c070a40005035207030200e0380002550642c001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 623995863 1250 623994613 623994617
    0x506070507051e0d0309060905100501031a010605090103091a0f07031802030738090907030e0703020f1804060c03060b0a0906260420042c070f0e06040b01 68
    0x42e10031450010000c0d50b60f0382e1350400d01d00003580040da441c0c24401b03007802c0c1c1d00c041c090b0711909103401103d401c00d0740154100c078032640e04085510705103400342c4140e0100b4811413010070700c2800041c0095000c0d811003004a07104e0790107a000098404026580510207481b0000501da8110400c0020345d0148516a40c3c0309110000c1203060205a0000f070360303240c1d14002d4084988001c0e03070920f03418102c0c1308400c20f41c1c2c1d03681e085003c41c50100d2200c4c48e142e4008101e1544501030240101c1c4140d03020f0310403517071000c0d001c50181c01103d0a42c0c00303000043c0e50940900790000c4244a4888200e450600c541e400f840c8075410201354035038542c1004050755816000080504010003e01142c5030304440000115082d03410400820102440ca03081e031482c078107500001c141c980708108010070168000e00c0c000180907001c0c003401c4000f100244405c0390f00148402c8440310015404c06064501c00c64091101e0481108481030705403600301051034100690303c400461081c0509001c0755190038001c5a1aa510238 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 623997113 1250 623995863 623995903
    0x1425150e0303042312070b013201140708030f0705040605071502070c08012306030d121107050f0d180e0a09060e0a11060301050907081003050607050705 67
    0x418206440b032002500041400f0055030840d04080c03040324004828159810640740000b8911100030900d030f00000041350880350f62400400c06241e80012100180d4025594118030703c0c4580d640c00daa22101ca00a5040c000e506080d03080c1075004000519403544182965070304c03400c00c100d040c40c0300b5001500341010b114080c8010b0114580c0001513503602a040450104104100d1403200000e20403050003030a10410500f010451460540098001211020185070880e004081c0b80b508803101f6102e0300d9243e00074030505c0241c00c1c0314000096560010350070000c0c0090301c0c0481d0320b0003540a00c8007110355804c1070082c80c50014040c092000a23030014105010542c0c040030051540104900070f50f4a03e11000d000f240c0b00c4100d41d48041e50455110b041005144c66050a147d03a070050000c0844441e003015260300058249032041c0e038126640508060003544a2078401d43d44100c00505149040409120000200e8420401c0c20b000e940c0d140c44a942d0340446040550616100b40d0b06004c03210a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 623998363 1250 623997113 623997131
    0xf031712040b1b0304080a11010e0d030905070f080c12030703090501030908120903300106031805120d1407020705010e030a05011506110d050406142515 67
    0x609445980180c1c0010350080b15070300e01c00680c0000c4890056100100b01c04020402081080001030405d040c003911101c562070794004515080e50410704003107985800c43c1a1641074640217411500c1c07038902c03c000b035a1066464038600c003500d40c03190b800b011040d1300a624869040c20060b801c40040ca040030046c42c54540903407809090420248902070416584000b25000c0c8003101050750f02c1001e040e095103049040c01c0b40907560740d40040d442c0100001010f080c81001241841c442210546c81c0f00d80441703503070f1804070140c005010783e00c0010131100201721300f00d0008000b400210242c500c0d548005456501c101c0c00c0504650481861020f101c1005007800f02a50700012034400b100c000f403030261040001c480103c0e0030642c403088014110341c02c01892281d1100c20000c0f0030145c030001d60303401c11010207107000d180d6101920004980420020001488224032451900c02040c0e01c00955602e403a04201100007440e240302c805c030710444100d8211a080214049064480c0c080800c801d0203a100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 623999613 1250 623998363 623998387
    0x41e051504151a0a1e0905010206090d0c1218090c030b0402090d060b03030c01061d0702010203101203090314060402040b030102040b09040b0a08060106020d020d020115060e01030b0306010f0317 85
    0x8600f0744000e442000702c1ea00007071a01c2601a40e61500311205c55141c0710740d07150710142403a1224090f15000d07005440009500304d100003042e2407005250ba1f00c010a100389a00c84010050110056004003c40440346c40305500e0700380702c400f000b0b002079100002c6560072114020300300e800f01c3c080140f20740d0041154108079926403680741441600b00c1c000169001c2000c0009243d480f444d01056015420514005942c0e14000220015041202440c6504d5502c01c04200d080b80300c21200e211140c0d40c07515043c800600d52032030130107101d0712a017410700002d034403034a4900034103065000d00c04441d030112042208508150168210b0441c0a4000754203003410700300c4850a50142007151409180d80e0301c0c00000540e01c0300d00c110300414603181a20601d58441000a445614084074940944201044032107d80d2051081c0c12002920f075548410b002e04100044a01c120f070340d14614100342c0c4401e01238a642d941882018020035100040c840c43d18954600342102500ca0502e01106040038072110400740 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 624000863 1250 623999613 623999639
    0x7180e07181a1203040e180604030807111005150301060311010f030204031a16090503070e04020303070b180706051207180b03091006090e070302041e05150415 70
    0x22820700d00880c5480800b071403510006400324200d6400f41c107a420210003000003000400640ea03040e20305900d190b4642d031501140070344086032421107502c1003000802088c41441c8050304000903107132000d41041035095051400d12103080c0c07081c1c095915424490b100d403e81c040c0960f5914107400034441c052035510350242d80d6803496000d40c10720051460b002001ca200341d04680145a2250fd050500c071a081180e218401040701c8240d90309449200b6100c281d40100b06510403207400070300514041d400d1030105801803038060400c98140c40207000c00c0c000500e41c000d070540704403c0c152a6480215030541140d01e07040c00c940c4600d00b480410014840380402201c0d049501110034100122001404e43d060041c60605a10000c180000401030201c000f401047c440d504d44c0f0809000d0217039580312030b480011240351f2403010450707a00c0200d041006091a801150b002c0c00e0259406081c00100040141510400c8070b01141d640304030a07286150f840c162140000d0700c000015034405041c00c01c0d10040340301d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 624002113 1250 624000863 624000899
    0x1208010510020d0509040b0a08150606030411150d0c030504021c2f0907020a06050606160b070201182321070606050a140907031b0c021207180e07 64
    0x2100000b03ca200360344031b07908050204c51004c0c0100d14082e40e10759940340c41e040c0090401a0701203202c0041826490000103590180d40c001d5045051a0030407003c0015075031018079103000c0d290301486240a05d080c584550052a0031944003c00d4603d0503204001c0301c65149031280a0240300800818045940c040200c28040314218001c6102e0768034103443c6401114040c851948207003041c0800a1055000c1014803056120b180c040c8040e45640f070400100b40554400d0014a07013603880c2c6100810400c0c90500d03000f159070b0000041079002817807010150810303210b043d11310003218400c001d0071010186101480c1c07030420f80600020503801e08000c101481041c5048503860340407522609000799503105800414005120038102a0340ba89071504c0101004c4d2076610034152240042d04035802400b802404039070142400c886c9804080d410b41380707440312031001d98225111005604039074904001e00c80140c00c02a0300702d0800792864040e182034440e0b4115284454000040404c80320184080000c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 624003363 1250 624002113 624002117
    0xe0702010b01320d0234020916030e0d0c0b0a02030601020a12020f1b0f03010603021c0c170303193b0a0c050a12021c050307050a1208010510020d 64
    0x1021902c421040c0f0240501c42648030218400100611441c41c980030032104151048851280880381c00c0c3c00e15409012040080d4201c3c060300d0009194103210b034940320712090300341000910901684016031138680344089a90110340d49150100c20300512182c0254003203110300055140d8030706400000d444048403800209000800c0303240d40e01e240c0c001d002c1007187c10707191811201c0b100b840c2d02071540d203c03a041e507520f40941c103a805461954201070240c20240da80142c1254245911012031007182e92420717400361010903a1420100e10a4080c5d00703100c141c881c241000750b890b800c00c0185030003c00c10144800903881d1604050040210030b038240c0003040b2007404400c015080b44041083e032076004080c4207807891b005204ca070030104a1a0015001620727400c3d14000e05154480045040641c04503201960106904134807a0b141e900402041051500c28015281801483d0351658070708000c1800443c0d400e800ca401c0b119546030b012241500500702103c51440441003110065166491001c244003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 624004613 1250 624003363 624003437
    0x617010807031103030c240f04050c120a020a03050a020f03030418022a06010608010815040f060b0d060f0b090f040201030f06050d30090b030a0f060e0702010b01 71
    0x400c07135409101362648807118030140c0e4008a0024a18041c6158103455000c48080ca40007045040d15900704084c07040e903105e8020b250a90342e40c41040391886403d686242984241041100140c50b51050080218854001803608411900c1088010f214100050380641c0c0705010402103481250412403001c0d80c05400160f072038948040360a0364105400c819911288884d20800030170400141c1181254041d44d944100c60343c030f6800b0613071510050749408402c12081c10100b03000c1804071410f6030251384035038030025041c140340d0041005c2041542050b80c0d41a6260700c10324043c0103600883c032a401003101c80c2e40e058a0941481d480000c005000a0304041d6a040d00d0410000240e000a0107801d009004480014442c03401541c41d40c030b889108136a10f039440c201c0f0b4240038240d05088091b0000d584602d444142041c40302d0076983c00080100850640341c15210f0721256040c800c0300040c10304040322121604d42000040d00750f403014132050b41081022405001004426031060034880007030a8452 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624005863 1250 624004613 624004643
    0xd0b0a0204030605091506030c150904020712090801230a090f02130c12060b070f0512031602010506090f010b09040b090c0702120a020105180301090609030306061701080703 76
    0x2000034010740e000104200c2c03400c4240000d0100024a00c05074003102c0000540030b82c0c4403414503803140078100c012034200b41a2040c08840501c01c0003c2c0400f0200a48014140502900d07017101c41ca14095071040130940800042c0401582800307002440140748221411403c802e000028221100800103003500c0c0d51754800c44100004846290803e41e001040d1090000c8694001001003a41c003014101144078086800302c4c11500340a10401c48294281c05420248241c6072460701002d003243c201e5560003452031640c079020f8590040c601504100c2c03130ba088100c8030070b00c0c0642141c0d8042c10451064210b0400c1240280c112141d050545888a00440e1168000000b2601504540c484507a101c0c410604000510310309002800360385000b1039040d5071040c00c5000c001c2e1144036124010f400034100300f0080c20b20804072481030145440243c000210040c45859810458000140403800039807900c200700980c9a0154206180800000700c02a00f545000359140c1d89500a102c0189001442e011003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 624007113 1250 624005863 624005881
    0x5010503041b03080a2010050c12151509090106050a02030c01021602030d0f2a021305010303030c030e0319261b090603130c1502011506030b0d0b 64
    0xb588046496240d40c2941070344074900300ca81600880052000075607000018001d1300713034000c102069240e9030b07000f0b40180300030340907140c01405005203210801c0d001049070305180807102c0d0b03015205201000040c0700c80c000700b40410211060003d91054038007000d1104900356510051030030f04580f02810075a81d910607415007a4214064607810144651020460f0504206030300506c2954610031016168040744540050b5030701c104094134940010b81807200d2000030800c0b50109a4400d4104601488401075a40060410719060a60030701d6551030304010030415805000c0e14083d0b880c80c2c1401d000001c0002c840c0c070398a000340d0312403180101d141d0584502c2075014003030128440c00c0c07461483c0c25028511580c52a104819225080c00040150910400c0140ca0301078a49030300000f85030318619140e03c0251881c1081c1e041c01561803082c2c180c0c000520711212041102003142e542c00100e912040da59840340000c1c007a80c407000515041c1010303203407641c1d580c5d0b49420035140c0c8499034411584400c090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 624008363 1250 624007113 624007133
    0x10f020f01020d0501090e030f0304060921051b0c0f090c0405040204031b0914010522023606041703070602070c140f0625020d1a130c0501050304 64
    0x5003416039480001d41d00701c03010058101d01d05990b405d41e010b1040b44107000c550f65132032256500c4a000caa82c00d00c041000154142c01c4921014001c5044070188242d00540001c4002103a84c000003060000400252002a4100c0d07844017035090340180c180040342c9800709686003070184865206080001c00035000181da003041c0c40c00f600018104540340c40d01ca103092065043e4016160481c101d50b2040040c213451907009400c1045c614980da803c144c0d00c1d040502c480c58140b010710032140c1e107440f41e01e40030720205440039204611091161950f0310340d0301460071000ba01441d05080c40001d01040c018980d4070ba203011541101c0103082005141c80c441d03100e0358218010309130000c1101d4000203440c028032040300401005c3d511124203200903280306c1020040ba410078960081d030041003c0c024228680e00000003da40301009010007070f260005640003484a80300803400b10346820301407070881e100002d840079035a4408035140c0381c54400360058490b030f4a501c1052007514104280040007038200b00140303034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 624009613 1250 624008363 624008383
    0x6030908041e0e01080609031c0209150414060306031203040f121d030619050604230f0601021906050606090909060f07020313030206180d052b0e010f02 67
    0x52520b091071140c041c0c0c2e103490345900c29494000f00f03c500209280320040b80c034a0003280304100035460621829500520f900c020340000d6080d603424803c214050322544580e8081a10040c0020303541c07800c0c501c8040000c0e852000c01c50085100b8005c0121030388000504062506882501d141c9035901c600d040c0b0782106410200406039030101d051044072540100c4001c032034142c11098641107000200074190b580e481252004001104542000071800d0b003540030503001034025002003114849400d82e18401003050540e072510030f5401040020003007810203840d800210920280c503c0789010010744000d0800000041c01040e0380e103001c5841c917615002181d001c2d1001408240444c034010155649a41d8111001d04030b0f01d0902c0d001441c500c0c1f022080701d4840000b564582c091a055401b4040b90b6004804036a00c03410314001203d41d284d403400d000da50002e101e00024040d00403a82801c1003418440302c101030000d030742c441e5201006a000b60b800c5281040a282240d5041240c88049150041d269 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 624010863 1250 624009613 624009629
    0x20040f09050c090d030e031c0c020d06060512030d050606090904061a12210c07180b040905030406092403021828051905060a0c061121010605040603090804 68
    0x42514201038000c0c0000c414100c0440c20b8408e880701428440080701161040b64000030b1a4800c820011314003801020402801a80005803040d10f0724007058031140240350b41c02d00c5a1004c01d950318420514060f0961008003550141c1c1080808000304d6900c0700041c1c00203084985510301d0541c0c0f901c8800712840415001480c1107241d0890800301515a01c0f040106052604010f03600d0b0445640d0408840f0100030180007491204c0ca444103101d52039450811b032103120340d25a0522059651070703004085103240a00052766460b840d00300050100d0030a81e01c4807105c003480b034403a204c081c0c020200c0d9144070404d46c2005a610900c0110344894403c8286015600281e503034510070b8012404400da030980032601b00b44541c05a1500300300700c40300a0181000200c21480c9100303100c03608000300a002c00403d1401d010119001d5551064107a41c040600c004800d100451000c4d50b0108031141d010031241d1881c1400d84a5040c400c0c014041d00c11030180782d0905440d5940c6030100299681203030001c000c15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 624012113 1250 624010863 624010879
    0xc060a050904060b280f0e0301060314010e0706030c050a0c021305090c1c08090d15020a050a09060302070327030507080606030f0d09030b0403111020040f09050c09 72
    0x5001ca0080a80200904000120f205003000c104918600030100c507030141511b07000000f440d084401c5843c00c0d20340b03602c40c0c1c01d9500d0302d0001000905085180000c4101d820000c5001200c035403006141c41240d5204804240c144201d4508594004040311286401c524041c20000303818008981c509030101003c0c01d28600c2e0800700010f0a0300481c3c804080791003201c880d484801044039507038003046004809000c1d11410014045103103000c400c041a031a1007542c0707040b05007645880d08001c03a001001004003090380002c030501282d17802901980503241a0400f1804c210003078030020328200f0302c40580360690b805a1180844049071880f404001c5900908031480725407101c1d0065100c800644000c0d00030301c00d400702d81c0407011001c9500c0e07070010f102d0365030450a85d146480700c0c0381e0920081c0003a030a002d00f02d212003100c00b10600181c0c941c209a0740d00416822503410541c1d24624a4820003001d502d23040c03106000d042824160803003141c014020102d45603d0f202070810003071003503038005603022441d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 624013363 1250 624012113 624012119
    0x81914070207090e0a0b011806050904030503040501060e04081e0d02220509010b0d0903030b06030f060f03030a05040e04050309220e030306060702100921140f0c060a05090406 77
    0x7002540c00c090300e1030407005221076818040c410390f403a841d51000520190184006104504094400307184102c0705800200c0c0031962107011822400094409a0028400000300014030809000e101d00801601d800c42e2030314a001c0d12520a00d00422085104089401c1d403003500c040482d4041c0c4496a00d040b00455842102c40d461000350303480d844151107034440a000005580ca0221080c50480d18141c46070782c03800702e44400c0d0400500b4aa00102c0501d9a00c0400407e661551000345100b0f008420b55440f80341000010400c001503030003080c030700c00c0c9c2c010062100c0f816804001ea408482e6280a505403584440c6411802c1d4003684000507040804401c1100c0340c06d070314914025031011603010801020a41c600296102e03c0308480040d00a14204614001420154000c800440e0030345011803009449000307889480c03040f140701c00c040034903440d07000081c82005001c1080308610480101503100b4000c0740c040e01d40c580c0c0e065030352041344081501c14015000b40304440c00000700510401c01251 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 624014613 1250 624013363 624013367
    0x60c0c03160906050f150d110403060501170d2705040e03030619030c050d02120601170c03010510050607032307030914010e040e01020f0d02070b06010c0308191407 72
    0x41c5110380c52006081075070014032070414450401400340040c03c030104010035821031074040d500641c041a011642c1d011401c42070451a0b02500143d8842c03d004100380d45460600100070310803040c40205500420512200d03607402443c55840040801c2c000b03025051440840c00800031154401a005030a040004a8005003c00294800d1908a500340400c100b0415030750060f2001d8003000b01600c08083e0140302c685000340b00d82104c14401071403800341058000140d810201e00303902a440d40c08540e030190821440911500800c080d040e0000c0140b842c007041c13560003000903489001e008600009501c070a041c41103009001e0102d54030711400c0820382c2e41404601c1ca07400f810040d0002410b204000c0307401161801d0000c00384a0596900784512001009c00c4028010400c0300d1a4a42d401c011a07100d00d0100c0002c0d1140c12043c050044c0c889503a4204640e0b0544001d01c82e034100f02001488100084d0030500c40b68000e4600c1c4244002031404000c010000c20058081c3e62490300c0120400520903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 624015863 1250 624014613 624014653
    0x30c060c0712050408070e06040f1806051b0711211c1d12031605010b040f0204030f0609020d0606030803090f1606030e0a0c0e090601080c0609060c0c03 67
    0x500c10212110142106942100d441c0181c2c000c13131080b50000d0904120281000d07c400745c100c5001080010200204602007086400da40d05580b07610510b00407a40a018442c0305003544045045001c40703048075075140d0303000c40c3d111b0040018900591428207480d44d4890b407008001e000303c0b005d032816000740c1240c4440d544803503908000d042d1041400310080100d10a00b248024480c1c007245c01100380d5500f00c10003020b19440d00b8400c0303484c44280701c801000c030354030428410aa03018000000d083c046050921058501308203412a00c1e03401080f080002400e00b90441c404150011400103004d40385d0320014030f0440c4c240c800680101d04045e804410310150303200030740c062002181140d00080d030807800d16484541c40203216150041400e020401540240c1200c0e4804400c403003942e1221141c1e41e00c490030a50b480c2c1090f03d40803047c400304108008104021405814031100501604100f200090032500c00c4240712030188102090740002c6a60400034070340c6414004040c0c41d540010701c0c40c070302090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 624017113 1250 624015863 624015877
    0x503030415021303110310020d060906051c0209070504050603071e0309050615030307050706021f0203280921031a060f07030915050a03050108061302040509030c060c 73
    0x140080c0d81c0101100e0203a00c200d42d800400700340300880703440c90740c0c59800300722007a400c01c26017500588409503d48003d80c4010842c003800d01100281150502c80070104031115500b000d0300584002d01c0c0703000505481c0d402100510350480c0c0100c06680d40050444440c0615801603030406008403d10007400e030031041414444d40c804140505c031400000f0201d0551380f10680207010f41c0c0021011403405c1c503d2101051016001404036403510703100d070391074510b06606c3d50700c941d005130008424108600c1c45001c00c0710303010702c80001c10340c00c50810690b0294000d20b030385809042040003044116a0704447d4001a00050b0000b21528011451004c1c00503000402501140000e02c0c0c40c090002d803906060f094030641001404043c2000400000081c0d82d600103101030b800c0c44222280003410a034102100643c400c01661515100c114115016082e128181c10407400ca0f0132440c200248000504111115070380c045402043d00c3c3c9440b19000c0c07c42c4200040c580c3e031409020200583e445845c0010440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 624018363 1250 624017113 624017123
    0x90d0f0b070f1d0103050c120a0509060601090e0c070201030623120307030507080a030e070303112a19080a0809030f0109080d0905011407170105040506030307020402030a06030c0305030304 83
    0x1002807900040310b200d0240c0b10a02041d50754000031200f0b40d44254445640700ca00e45503141d140000604881000c90011500004820f8441040003800c2d1014008560044020300b4144091414a01403c02c1400c0c020084030b01c2c17000100d980c00c250f83c480d4102100410050b02c2040c1100c075a074401c20721100d000800c4038010720040481a8104200000319501d05806a817414100380c080c2d966141c82d98059074155003019103502e047c900502080c0208002076100b0340360002c0c0890001c030350a04109801c0300d442481030403e10801d0392281d2552782c1c500a500300711142d2001d0000c240500008505607000b40d410b40c8a403111203010071039201700030040150220121202140c1554605081c1c1d04108401401c55070305200d9880501c1da640c02c803411052050001086078448030130100514642110020b002400e01c80668840c4807030014050f01400c81620144102d2800c0c0000c43e650340b2614170b000740213503030020000f207040c10943d1100002d15440b003035050350385541e030419668030341003a5001d9407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 624019613 1250 624018363 624018377
    0x9020f1527060a0f181d0408190c031d09010308031801062d030201140c0307020d030f030c0f140a120504060b030f0d0912150c030c0e06090a0b090d0f0b07 68
    0x20900d49110100c0c1d08030341411608408141100c24003072410400500111140d010a00c102001a10276245140d1500d4166a44450b821000d00700102200010041082d0404e204501908a902c6043c101c9040d03c0d0030100440d5240c4500ca4040c1c0092100a500f2105e540303003803130214407221185540c001c0c03010394215140091030421054803541001c0d03c4000e02259a40e202031502c4901e0401420782100080c003640d08000040d00400e000300149a4200c00040c01403580c1c04503250103100c3c2d0314001646203040c020131075920001800c0188044d1075000e40030b070b02113008100f0a03c0b50550220318200d899040c0203a0800d8039126011b011200800b61080c041c44004407038120000503505803c03034840c0c0c3c401031030610b407001d6885145103034a4195107849800001c035010307c070320b401030b4000890203580c0025918003804004054542e4106498031580b0204280d10f032030b81e41c441e5000c0c15907004056241d500e500840014000c91002c0200030b040c02500b60b809000c1c4030100310381510525090707ca0007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 624020863 1250 624019613 624019637
    0x90705030706080c0a0c0c0b0c0601090e1b15310e0c0904201617071a090705090709081c1d012109020f1527060a0f 51
    0x1550040c07003201e140396a8001840000f0b0060302c100c4000c070245004061f118102501e505000311203a0044907900810381c0090010402d5007118032441801f4050710003e4010004545c210501e581c0c109500383c0e02c02c480d0180310f100d0000344001126201c0e8a46600105001c4001003215112000c40300440d40c111140400041c0320b818825800d4801e010003001c462401420070308220017400b001200c2040c0380842c0900c40ca804040030020034001e42c031081c0c02054a0f182e8949030806084044d60541c899406004000c00103002030342240702d2909130003d03040c041d076480c41d680785010540d500c081c5d84403985105201030305400220b20f5086d101c0100940f28010300d41d2000300003481a2600c03590020b1000340001d042c3c0c9050300d44c51044d80304c051620448500604480f2401107044010b000e2103a41d8410a480851910541004100d6801c1d52044c80c40c07644202d001e0214050b184101400740304c0e841c15401c1d110385030b00201903484001418035885090301000102040b091500b01c0010541044000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 624022113 1250 624020863 624020867
    0xa0b01020c0306280e0c030d140a1103070503040605070b07140403020103020d0b060307200615220525020703020a151e0206061008041101030c020c09090705030706 72
    0x10381070010300a00200015280c1c0c80425824860301c03a00c0742214144916441e040d80c0c094002c8003d081d44e0b080040201681c281c00305418509140a0241800000d05004840031288000e403080b03010141420099403c0c80c0d1406401c52041610040480c040081c0c08252550048040c0c11440d004403482e8082e03950702c807001e41c0c0d0800ba994a446c1c0445090104000640c803d8000b40f00c0301108440c0480c1403401100824940e40055030400049400c80403101e40209010300e4205001c056100244180c0c00e01400d0424a0b504a50103280180300252070301c0843c04031116a2903603042904010400351401030344803200c50004ca00c0c42c000c1c041d620248440482d100244010076a50014000c4003083d2420b40c00740c081d41216040c50741400350803401041e10908441d800d2100720700c0c41c0c01501043c640706042050004240b51100b0034407003c0028400811030764072005582d00d00a0030300040600f0021343c280c1c90191032400309a800403c0e5020840890400300d480c40031038105070200c135255502c8180c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 624023363 1250 624022113 624022123
    0xf1318140105060f090a0e330424060c23060f130b0901060306050603070b040b0d180c090b2d120f01050601122906040b070b0a0b0102 59
    0x302040640304400500030340c50140000c1c0010442000340501d07060307400001c90003d0300540d12980006010400304400c2c0c075114400403c030304207000e0915802d4000f0955928650b00201696800341d69110080d080c503025503805c6144114030b40785030003c0c1513914540200100c440f4441103510006003d0340d2692101c0060b00d0323081116030344028145650750301c1d441200e02000101038510601842104d000030408240805000e10300c00400822454294180b40d400d841024040c1030190380031344d03404c01010645405903401d541c0d801524554034500014200c014203142d5000c68004034004060b5401c00c02600048030840e205c0c00e4043c07007031684080400086000008400c107004c010800703003400b02200880d0004182030010702c2314404031007901102d8a413500c0010b20b00725681d943c0080c0b000c6503070005142c40c0302c012040b0040c0000c0d10840d19010030b2001d4440d1001032078980c02c641a40c15074036032040c1c0c1c0c0034101607a0311310b1700c038001390030710407011341c002e0f1810650a032421720444095440851 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 624024613 1250 624023363 624023381
    0x3030b0405010e18070902040303020303090d0e1305072a020f0a0b160c09020a111603120807140a03150e0f0c0c0c210c010305091002090103020f1318 66
    0x141c4003143d0340d076039210fa004041c100380300580640994000070580c0c010702d00c040c0010314002d5000359100d28005e0744651920740300d00c1080c018402c01c00d107811200d0340c4484442ca02c42c6056038020038140c42e85181503405660410720442030350052015840704896a00c08111207a0080380c10f0602004c0e00c40900403c03600601606c442100100000c2c03051050a0300e2200e1902d1103404800c4200f655081114102c2c1c2001211200054022140c0c000c0c0030f108200503003101c0641415071415526540d01c00c441c0610007400302051241c1c42e00000d240601034041c00115401c4141c540f5903403004c03403100800501c0460361487e144c44880001040555680c010310748100400c0c1298402c0340c49041c902407050b008400031803254402c5840c1d10b030b126100c101108402c10700303000c0700000303c0c0000c134112030814180d109142e04251a0030100700c001840003aa862249140b80001640c460600004901a1041010741483c50b0300018507451121041100142198a8100d56841f802c4d031a45c240713000c4c1d0f50148 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 624025863 1250 624024613 624024629
    0x3120703080a051506070f15021207022e1404121b110d170c0c0418020d03081e15090705040f0b0307300c030603021f141603030b040501 60
    0xc1081301c081e04007a0003d214440c021151809950030b581e592071401403502c3e01240c0200d0300801c0c0e14480314100c2440c25000000e80c0007070902111481d00c050b40c6041101220070300204030b640c1d0421080410f6101c2600600e146c50701504500e46400c103102112660b10203d0300051541c040d44020300c80c00001c895086a0003140164580203207420880c0e0740d021910156084035488105183c0130842c3c0c8004c06008e40200080c040b402c52150400007151703650300e030a00d52030014541140050f80e91032449018a40c1c0760400c0081c0791110b41d04440d940d9480d640c1012008030034801c2c8141c1502d031401c00500720004840041e000e50320601d0031a858021841404240f001d000000d000003150031018550120306840d10001041c40803044410ba40096509085034100d03ca1264251400500800403140900e00b024000c00b459640858410032091140201003041620508440c034130480107151484007036144035071209115102a060480ca91a003100428a0510b650404d4102405000d0480b18a2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 624027113 1250 624025863 624025891
    0x70e0d06051e15030106120f0f080c150603010501051207090b220b0406170703020103020d0e1c111506040203060301060803040b041e03051e030903120703080a05 71
    0x540c0c0e000041c010241615001e880200e404144140400d48840c2c441d0042060049144080c90145401c445407900801c0091408148140204480c6022408a640c0c84190f11049007040d08061880d40a01e40d07107103c0c1800f4014104034251103c1c0c0d451400740c038044008000990b40d034402c000241c04030b03141c0c0c02400c6e00b11501c00c02580380d240c0d00200800034040d01880000341c0700912017842151300030048021740d03910068020300382001d20408010b030000c3c1c18480c1d00d0015851a5030395500311071100a0405400084e1440c000145400604103080e45500b1124044001100e5240070700c04501000009094030b4070b42c204913100000e0401210700c1d5001002c042e03445000901000e54001418507816640310000026141350410040c0020000c001d002619a82030640380303424898210f0700c5442450b01d4180030f1000c1034010404100c2011090540301c20101d80b03040c805c0c1107004ea070000710b906000c0c1600d03840c0281c0c1d0080003045120700c42d56482c1e42954405405a0840d5410f443c010340141007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 624028363 1250 624027113 624027139
    0x30c140916020a021908062431110415020d0804020607110d020d0503042303032217030304031407051e01020c06100815010b070b040c15030c08070e 65
    0xb005440c0c01c0d00c0d8203c3e0f000403c00c1034884581525002c820355460041c0c040000400c09030418443c0300d602800c4080710140e008078110380c030360100e2948041e240300e008110100c0001e1000c1240c1d104a00ac03034604494603494a40c1c42c3c0c2c5101400c6800051300015008500084ea4403510851903e44901d90060906007049103a8960710500b1884080d03240e04481d54104500c05a501c00864080b020b202d50300556445003010a0307082400032800003403210304090300481141e40e8012059079072030840c0d150900000800c000ca045108030340750b400700d00360b42c019020802000c0d502000540c442c0340039480c1d10381e10005800c05814541300d29440513140760040e5940c0314803811005280030320861114005810a245034448904082c0240d03103455035000c89620400c0001d0782880034080d0400f00d1102c00ca85503140c051780040720303c511000206581c003034400080c20095001c01407005090420740c00a00001e100d400030300141050040718003c52800303c00030798824440d41007003641c0400a404c00803246e036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 624029613 1250 624028363 624028369
    0x804030807080c0a0f02031b03071a1b0c040b0604080a02131d07080c011e05030a060b0409090b010e010b071407120312060f0f05010513030c140916020a02 68
    0x84250110b403503000810000040a03400c110f00344241c1e014810030071003602030b4030426240c00010a214001c08d43c201c065448031b07990104039a021100381100c1c41084001080d0052142d2240d5158911070800d404204000b80398001107402101005650410480348901c0800c1183e000f58491440700b544034540c0341c00107082c843c0c1d103142034000040000c00c0340c501c4442c1c54007070a6000511b82803507920030002048131501c01c01440301408401e00f8403d00103010743d261448030742d441c410541c041c07040002c04600382e001280d0055008000c040411030b125511480107a001e001d1141c020790750414040d00124840b0359054a0754100c40707100d54001c1c50801c1c5a515044223b14031001004540280d82c0b0000c0c0a1405580d007800081c07095940c5540f0380080d01c141411030301582c00c000d802528211f020300010000c46e204c202983c2c82424a1529a403400d48900c894203404d4200038007007039072100001491000b0034283c81e4100d1341110021084ea98030011044644118403541c00181e0100c514500541 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 624030863 1250 624029613 624029617
    0x31d060f090a030204050127020a08130302030f0a0809060615030a200d020301060807030207030207050906040f110d0c020a050706030b03030706180606090b0901050108070e13020c06010b0708040308 87
    0x10710050314a076040d503520f400080403140d0981c80400d07500d840c21000008000301c0b0410740a4009201800c50030b00b5000b000c000d04040e4001c1035601c1c080300541c401d50601d4002c0003035540c07070034140340702c1c980d990341150b802080100c0540354501030380320748000f240c22450320044840c0361030b04071609103083d1740c1c4d02420400036144d502108160340b103015466890709284d410091030101180c0402682d00c0d40361400081c84810002d08140406105000040000e83d0102c0d4160865408032aa40300d5500d034400080e004003000003d0240551400b9100e02a400d60038001e03251a06180f0030400c4a03804603802070b42c4403030481300d00800030b411140d401e02c00c1501a0f80070f9450000b010741224103010151340c0301e90031205403103008403640d0500d0744190200007050003600090034002d031041c01040b40e42c0c00860507011040c0100c50502541c8000680350b588680340120860000401003160101c03d8030080c0c00a60007040072480c14040e60300042150032890080360000c07076102d8103041c94a407440d201c2d1a619 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 624032113 1250 624030863 624030877
    0xa0f050f04051b010c05100507080c0c06060603040201030b031b0a060f0509090a23010905060a0e0712020d24151d0d151b09050d0b040204090b040f031d060f 69
    0x11286040d00d40f404140b01f0007010040700e005901c0000c41e03050021001d0118140140a054909c01c10010880080004142d05400c21001c2d50015141e455030310040c0c002e001d0014074150548070310401b0100301c0d131000410441001d82940d0200704251101300403601c1444201c42c5d480481e030200181f0702282800410158006075045000903c0107444a00202e030741019240c0c00b04803000000140082d070200e1090541041049903d01c1d0080d20b85010b100030140000c203000b051058982014545220755011103000e0500c1c15001c0180207041840202e1851a0701d8020721b0410090307030045030045101c600138a00469544604200c10000402c41256840416400f504a0524010303040043e2080c2d40740004541c0b101004103100007943c041211440400b450401040700780102046141c6860300990700094004191070880c1e585e600104000c1c08401c24003c1407800c0b030404010901112006d070b0000c1031f00c60f41d030708103094400c40c91560003c03c900f601281d00c01000c00600700c20440e0b0324018402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 624033363 1250 624032113 624032117
    0xf0901090b0a05120919121101060e06010f090515121f12080d021602030c01030606080711160602010b011205010303021c020f0d052d0d0c09080102030a0f050f04051b01 74
    0x71080d92100c20041d92006100840d0740b0a4110940c41c075188d04090310011101c2410020008030303180c018142000703500a002d15040c06040c1040d4500e0300d01c40c0821001510019108201c51140e4008043c034992203603125004100c114004280b2481da441202c503144000300d040c0e900110304007010200040d0800100b15400c020800c0760485610403030000d4904074080414040101d000e030300615051240a0f445039040504e0704405001141d01b00a10b1a0020740320b1402042507040d00d0b8040d0729010810000104e98070b004c010000d1354a80c150009480c0407001e9864514141c15121100d05580003800000d000d600000101c07541501a8010b6048106040c8112032289480001a60901c1c2d56402d012001a40001d081c2401044884031500140c001884426511a60000121135070080400c600a41c42c1c45049035003455220300c0801014119040c002c40d42c9003011402c01008020b41a07150780301508200000e00d000703000704103c80c401d075009400341c2040d442e0399001c1c038882000c008080741 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 624034613 1250 624033363 624033373
    0x3070306050f06092101050901060e06031f150b03040503070c0e0708010e0604140411040615080c0708090a1d060a05060706050702010e12220819050307080f0901090b0a051209 77
    0x1017191000d000e094021714108000003100350074200c80ea406c642c4c0041c082e071b00030f6105d01030300c41c203000000442c406001100e040014149100000311015801694407600e000217010061105108002c00102240e0303200b14000f440701c6030b4034a032140100c941103403400003154000004020807410410038551044009200050440c15281200030b0b601050750143c0310841c800540340302c02d04140c4540c60250bc0701e02c00066003000d0b0b21100030180f50380200840e07441c03103010641d54100550300094500f4000700030705c96802140c03540314000c2d60404145002542c13140c52000304c1c1c82070600350b40c4501603480140450b4505480740c0c4034400580300c09040101150b50328000700c0030f54003040c0b2480751706500d2172a1403a40d03101401f070145035806070103c0b10000140c6e030040c10040c58a0000300003100c8000403090030a0004103007030a0f0f06500a42401070302030240029800c2c00000500c009110301142621489400ca07110901e0031355600840383c14402241c0200044c0c0743c00c1c0078124003580c2c8401e260341115 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 624035863 1250 624034613 624034669
    0x71106040e0403030b01030c1d0f0406150c0309150c020415081218030706021504080f0406171e150a032009070503040c1403101103070306050f0609 65
    0x40c00e15075080301e0a40000e40e0b0f40854034003135a07050054900c00c503031a28001076a10040015980700c1010010315038801c0300e104d40415041d4541b0b8100e44010002141303c450f6080b5401c0000e82000c01064048001408030300007c80d00d000c003001c0b840488400756445a0340c0d40702541c2840000d0a00b41405041140c44071400141510104540400e0203005099281c0350003203030030080b0b41c1c0000c0c0b0701141d00c2a0810300040c00a00c1c1e00181c0408207140049000c0043d0700c490422030000c2c82440e0038081109000074020494035003241102d41a00c84ca007003500d4940d590401e040320344003a900c2d10040e0b11074440010038000507800c4600102c13540010309444045e075a030b50b540b451100000c54030309000b922840d6443c41e24940f40f170340503501c00b100341001865440d069450000480150095010b040010030b0902030b0b6803010401c043c42c1703c986401c10000c2c00070364452025240c01c1141c012000a0034440c010815082c5070b44005000c01000d4910781c102a4003800300b18004152003074404864203110668 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 624037113 1250 624035863 624035879
    0x308011a281704290606030417043308070c0330050a2306010516020d060e07060509011706010215010927321f061a07110604 55
    0x903000ea0310920340980c1301891242403912000c0d41000a0056051150800c01035894841c200c0742e0099008078501411200306850f980303140125002004020800c030300e0b15a030240038040c2079040b40702c1c203480300780c1e4900a0304c13044650700000c8401e04e0000315201c00070000607010300c2483e030710000701030403d585003030600481a26400d050700080503815142c10610419100700e00c0740516523685840751582040005d505100611400f40140d81048000180c4002c00490b403840c0c0c0c042c04e50b00408141ca240203900f001c90180c10f00c0c18050301c29000b42400011500e000d942190011034040e140c243c013440000301c1c04640750b070b4000c00041c1507010b070404140070201425021800f81c180b0341400200128408a02031080303805491007088000c2c44618000413801d0007030703074a80c2101c2c41c1c0c0d4102641d90040444c00010450070721107100d01e1041c0342001e00050f103c00480c0c145842d45003c20004159181542c1445484001042d50051010409600411201e2005520304900501018906550784540c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 624038363 1250 624037113 624037157
    0x60c0c10120e0105040c120305031810020d050f061906080405030909070507050c030111030a020702031e0d021c0819020415090305010b0d021c02010215040308011a28 73
    0x84030b50640d6540c800c010811041c00141c20103410f800200720041051a9030103402440080e09214100b030030100e0700440044108003088000c600602c083d5111314400004802070078050310000615081e050014046003809449084060201c1d10301d11507081c540b1109840000d8017a100b80c6407800204158505c545404c10868090065039880e00d5482080303003446400e01c07686400c0c46221b0390410040717000125003034042e00d4120000100c016a40c258920000c1e290072494159014071444442084202200c0460350000d0007240b902603404002202d283e00e0083d640842020010944140c08103440c21022480c7e001e2031001640d00620b420344601080480e520380d03020140018809990a104000c02800b030300305100e40648442180440039800121520b4003121224104451554514190380c800c20940c141040c41d1247c0b20b00c2420a420001c000d14001d0140308a5115030074208540003201c1e10031200c413107501c40c104442002d44152016100112100c41c0300c02c02400c000225200c00750340322 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 624039613 1250 624038363 624038381
    0xe040903030615020f070b1204021027051003023103080c01020d0c050a1d0a0f09020a020f03030c0406030c0507050d0801090501080d02030d020a03150e0106030506060c0c1012 77
    0x40074815a140241e51504c6485c0d088202c0301741f002c0c01281c2804840460407a08298116002d80c240d607003c000840d111528200300421340b1017000d520411440c1d100d001c0400741c03102512030240300660850190140c0c8202c0101c020420003500319045140c0010030700100200f00d80d00c020342031030703641c0c0c40d5191a030700f007003080115503580011500f000304514890900700701c0c41410000d09001d50801e0181038003100541813040e2101081e445000d07591400b0511014006441709035800c1515003d49000070b400510141000d4840c44a07182c0e041c8278000196071098610300d1801e07203030509000c0102c0140a51800002c2848401d000410000c2c20a100a6022003c1948c49001662604214400759541070303008075125085000440061a404000c9408405e81c4000151340c6001d9440200c005028503417020303545800c45000821021030324241750707040311620b49e418070450300c48100300320441c07080c4c2d4002182035101006010710703828103403d50180c040040c24068450083c0380304880036200907103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 624040863 1250 624039613 624039617
    0x3020a091a030f060a05130b0f041506090212011a1c0207060e0a021504080d0311090406031a06040513020906031f061e03080301061107090207111806010e040903030615 74
    0x4801c010a038407246c407455901c05c0072807103040500c400c50b03101e11001120281c8a010b1700d96800f0700040c2404a00c604144046000c2441040320540d02d035001c1009400c0052500c681c11001c000015820680d40e10300c1c41e00c108007035950f034030b0201005121080b115101781054143d80d004d02840c4007084a40c85081c00c803a058901901c0343c15014810060700001c003035280c0308006018030040c052108001581a0340c00907034100054404030300c44e6002c40301e0081a04859103e030401d800030040044150704c246403000c1081d222100364440004100541d8001c903540000c01d13503a4126207001d4908441d070320760400c0014058514036124443d651400c0c40ca100010190305486030420000601c038a092a4800c0a003070116032078680c02d5550300d0b180e511040c45414100b0601c9208000154414800c500c020007010400b150380e00c41e00d14001042c4070315030801e144503c40001c1120034a001018039035201d0b1380c0c165201040c18110200b00b100400c01100c0c04d40415030ba4134004512240020b01c440707000a40380d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 624042113 1250 624040863 624040873
    0x10c0314130e090a03020c040207020f09010b0c0d0201060b090409020616060e0705120601050118091a100513090f0b09090109060c0c03020a0201080a1b080a0605060403020a091a030f 80
    0x40141441002c40151422002e94061440840443d9011400e0010344800310380242e0b45005034000205038034010702190340d0051a1000001c0d8602d90280146003002542080e90340c4032640420603402c9800902c21a0001d00040005030414a00750307000c1042c0d10b10007868903081aa0325810070b2140110800d044411684d44d80300b40c00d2220042040e10005c080844040c0396402c0034291064541c1d1062048278140a2003003403041b82d0480907126280500441c0404028807440440c0d09000c42e510159a18041c65608079141c01c1140318008441c1c940d10103550301c2400901c2c08070384030010110604064003107541c03043d0f111940ea0364a2109402110150000f00c0c00f0702e01030a041c0215211484024244022581c0c00340007e0307000300d0348910058090030010050340d81d00c084072000d00b2407640003d800a5079440c11141668014066500584608004010040c0c565091014600c52404003a40c01071100c43c04005d102c001350840b103402100721131080711000030070000c28038195035015007048503003003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 624043363 1250 624042113 624042119
    0x110a1110091104020903010603050d021c0c050615030316110a06090510050315060301030b0403090f0b1c060905040302060a0f0c090501081806091005091b010c031413 73
    0x20801210842180e0004104080c140540d54502d000c40b650b2a0903001e550042101502517400b0343c0840e009640001c251260092074803030094036070326100c11300840649802a002d900c144105a8402c00d958050002d003420b48a04d032040c04070102480b50181e05105c10002c0741155500104042220340c0700340d02103110080328600300302080340242c20400c20420800c00c104031035907421400d00d0342060b8904020f6034070785401d140615403854800c500340e04610000000010040556005403081e8065619244500c0c2c03520380c80b2494044912401864070340074060000300342035024900e0015981e03810300050343c0396189004002c1d6282200c00b507000d40c11404c00c0119100c0c0710300500c04400201c68042092060214019240f01c01ca40030700c82c10014100000b41031000002c620900c81e10000c0b08a43e183d00e01408010340c1e80340d01d1400d40d0303000c6040c500450b030760060002d400d480ca003102e070b6802e54004510744011108900421015001c100300522481850a0740200600700320070951003078414141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 624044613 1250 624043363 624043397
    0x130c0f08070b030c0403030c0302010f020301180c18050103110c0f0601050913081603110708100c09080a02060901020709150501030e03030603070506030a141602070f03050718110a 79
    0x6490344a12002c0c1002c008220f81d680c1c085045400f9681c0c181848500e007180d41c10124010410340b594608001e1002002242c0039001e50540e00003482614400c1c03001c22490041251066403100c0c1f01800355004610600582d8060307000008070441d510140c6081002c2101d94902d02207440041c3c0384642c0010005002c2424040c400c0e076400101445034030005901552000c00c0c1d4814114140d0a00303240240010130540700c2c107001c204540000e805c03210301c10307280e104c225256203000d0894400140b52418040215026145510483e9403103000b600400500d44c003400110360008103140e0450246c0751010610728054403a0900414540f030319a5100c5050400240496030089a8404c03d0340c03090003081116600010034005880c0c041c0e030341036200d46074611104044c04140414843c03c04084040052200c2e80682e0a00c4800703440d4211040c01d0b9032a1020087c441180c00054084c1e00141d4043c000d02d2808909100d40300003410300002d11036241103079900140c001c645048001480d045140c50040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 624045863 1250 624044613 624044623
    0x402010f0c080f09122512020a1202060f0417070504112715122a03040c0e0106020d0206010b04051c0f05150f01121109130c0f08 57
    0x840c45080450001d20182c585000b2409010030301c014200300041e0800d80741d150307140e8041405c2007078403c4031540c100386902c11551507100e13489805c0d0407411500001e40101e880440090854000e04102e5000b820101d40150783c030b410041c04c1e038005404004e2110990390241c000c00c0182200c2403100403204983c0030550424500c0d50020344102c3c2002d140000c0742030123100b20f0746000340203101660302c40c1001000c003040a2101030565800320f540409200c28500700c000030a0b8500143c042e1798503a07602c1450009108100b00b0710101c507051400d000585007000080250340240c0209000c8124558807000300e556031400360403c00c01608101d4807000a03940401145002d0a6200080c60500b4206800310300c0c42e41c03294003050000030010220006100031907040100341600141581d402588807035280e202083c3c01d441c51941d10200700d0000800100010b030300c00c1646d03070091a500d4009050820030403002d02c060003d0300c8850003050300800050b50024000b00030078408815000180c074100c602c1d8101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 624047113 1250 624045863 624045887
    0x4080f121503031c0e070b1305130606050313030903051204091a011e03020d050907080f0c01020606091504050f06040c03060b030402190f030f060f140a0c050c0a0b040201 75
    0x703501c103001300001040c00d00f12038065104800c0c000122688500c0140d0719011455001660524000811403030f140c0170148010292503040d20001e851421040000302200c0b43c40c031070140002e00070f0000c1541b00b41ca12180d10110f501034580360175566229103c0d03038140307540340d03000702d034440800141004404a18042d85c1281551f6100108501c0129800a004007440d40c5585201580d1440a152010700039419114124100502000541390102c00603685940a0041305041c1c4144c000044aa0100107461110b03644180c2c06807880b034a640050103d00032000c1c00c1307501c2d0080b00503542c0c01c03030791100d22600d803080ca99043c14001608109092000f2a0900b031411001c06050100a200c040c07007100840f50490b9042d03900088030714401000100b506426040b2416203140d440000003806008030a0290050052404009000728809800101c954842c44190b032071481c2c4c5d0000c1d4400750700c0d45c0900041486d605107940b070309900003105400d00042d000200c030300e6201d4000380025943c0c401c81c01055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 624048363 1250 624047113 624047119
    0x1b0f071e060309050d0f02190b01031103120901080402010905040c08070305060315062b0c0305070f12030c05010f09030309261206030a0b01080f10150e04080f1215 72
    0x603d50316916a180c8039016607003844107100c0e440306102d404900c20000340120200b0b04440752a01240c515140750038190a10065580c8036152000e46500c1c64003048291503003989025003440c140c0307050015510280018826418030441441c001507a03190b900a00b01e041c94160f075408500e1800700b40141c101c800c0600b0041c0030f68000701c1d940d6400850841d1154000b00c0c100d48003600700b558000041000c2d5410611514003405c03c041c501c1c20017114032550015030b440341c019110440e1306c0d4098038215281034816214400402140c0380702190007a490340304603070701940c0003144100000c282842911580082280029914031110080c00034082030340401d1200d407040020064860700c5070788030b0350082c0f055800400d02101c0200d04640c0d81003102c1c000990380300220302400d69488200350f448650400c039403050b84c0107560401c01d84150381e1203564081c0c0b80c032500400106042101c50228014003c20807907080b81c08020b550742d00300c100005032025104619090581d45050f10b03040c0400b100b5410b1841c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 624049613 1250 624048363 624048371
    0x2040e0907090c090b07140a050304080c0103021204030806040e060c0d06080102070f080c070302091608070801030b1f17010603030f1d1c0209070207080c03121b0f071e0603 76
    0x50f54402c404a0450342c6a10b1486e8803683c0e0780c14003400405001442080d40e1003489985001c01102002807c204c0c0d0340001a80c07401e01c4803500560507071149004290703003480f020001400203805a03070459002a006400050f809200d03040325407034040b09130b540a980c140f01040b4560040300d0382c02040090034032032000794100b54007613860810844000c4c9000700106c0010400d03002201081104a005540041c00c024250401c9903034650130020324015440020840ea00041744140641c1285040701c1d400722402100350b450a546220381c8085416030340100d44810800204081180c03008038000d0942000055100c0c95440d0261124541401c92020303c08041d85a40a86503102c4205912501c00e58a6040d0b20b0700762001c00401901b49500258880903400501c03040c140d000828005a4594200b1154041e110004240d928074071403140e41104a010880101200001c41c400405080448220ba022128101b5440c3c1041600c0d005405d8075a00034409140d0403401c11301c00300060140d420204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 624050863 1250 624049613 624049631
    0x40606030b0f180a09020316060806040e0c03060411060409090b16140313020d021c060501060e09040639030f020708090108150a0e040b06010503071209020a0902040e090709 76
    0x450f2080c0028804c013186503542c1401001d548003070000760180148072550019240e01c440c1e002d000c000080e211745026600e061200c2204110005101400c900c00070001d10450380c1c1c2d9503588801441c41e81c10550481018030000445c40c9686c0641c41120784a4051030101c0d28020b0060003010100920810411000c412070501241c4440200c1c0d406c0703812004034001540150001c42c0d14040c00c07000084d00604140b0040481007110300c40c0300c40300ea12801c420300c2240d0781c41d08111410102c0d590b090303500c1510346001c607000514079440115080c07200180c0200c683d683d04681e540c407411641c40e00c1402c032000d25400501d581c0c1071064540c02c1c1c0800340300314281201130b103c00601d405481d48a0741401200390104421481c02d088180c1549401080030000035240c2085403403a00303094800f202c005100f90042000d540c021029030384122110740d0740380b04074005220b105011f0000c800301070b41c012251074800304018040b400180060f01360703540e01d19014100a44003a10341107640d4411664689001000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 624052113 1250 624050863 624050899
    0x10204050108160513170c03030c0d0302090d0b0103080304030905090709030201120e0d0306030b01300f170a080f0c030a0b0406180507021509060a0e0a02040606030b0f 74
    0x881d801035010000c03040c44552960055070035105114101d80c800c3c034241400115448007003c46c10860803108155103610500e8030505a89000e80520065030340c0100014141d2180b196025058104006086103d030032801c2d00c0c0d100c1108800c1e002900d08000c000104000c0c10b4110b5038180003880e0584003142d2500c4c204500070054003880c04000c3c104164012810010b00c0d1603044078502c80c10306001d8859171a07404001070002c0a26100407613104801700000115a0940d05541800d100d44600940c0f14640145084051a18642044404455a941200100d41080e120804c14942c801101d540e8071000c0902800840b80107150308548201d071400c001c00c00e5440ca0680b40c12035000300020505440d00400107001d0003da81010300603186020b0780204204103034201c20f000c0c0b081c58013511108082d0f900c0205201404880b00c01c0680d000c1d00104000081c5a481502c06078071810a58040c400140d00040a0314156408003001070b8403046c0901951900048040b0f070894105c4c4c54200312000301c844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 624053363 1250 624052113 624052127
    0x6240605030a0c050712051e0c07060309080708030705030a0506030109020f1003060302030f0a0309060f050f071a13110d05070509040201110a030207080d0509060d05060111101a030102040501 84
    0x509500241c0703c01104416900900035602c260768007503002220480010402442c3d50080150040c03d440f03502c6480001603d02401c9412020a0f1030150011506015058000c0d10f10144220b0305190304201c4500442e4040c80518066038480d55801d569090031700300342c1b09503440603003054441e907d80041c0c4170059076643c41c01c0d8400760090300c20248200c14808164020981340e440070b074250040c4540c5800510001c10240c034002c1c42a210340c030032285c03628012600b4141d60082038000c28820007844015000c41070191030003601c914101100300d800e455a43d25000703000e80701c0e412000100c1a5010410030440d81d00c01e030320803043d18441e600c0f040c6901c1b0990b881c402845080d00031903821740810150f912906403241900c03492801c9801d05522450000d6485185119096a0380641c800c038017101d500c030703004039820500700500b914100303079088039880018070f03000e00f0642c14084013a0840c502c18405100864058810f00800502d11181042102e030311403250b80418840d901c1080280900d0380c03c030036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 624054613 1250 624053363 624053371
    0x40509060a150909030804050f0c0604030303240902070209280e03071a010e070e01090b1303050706050c10050615071b141906050906070f0f0624060503 67
    0x10115404920402d003080e00e262641201c441a401e01100c3c4060642210300c542c0218031480403120030119074590507407144000900e442d0702100400040000c01c0c469000901e00381d4049454028940b2102444621040c0c0d550080502d103801058002c15407414488207a40503d07410100400c0d003071064102c007560140003030b001d04480d40d10300101a5401042050b90421644440c8444060442492031007400209200e543c140040500001e400c031803090703a51445158040e110b6001150034200007031030a80144501c40c0c1ca000316100004042601040260024407143c1c4456545511801010f03013044c00155011010364140428000252103101c00c80c1464400c181c2a2500c079071461905404041043c540740d52024560710000c20b0010300d40c0b0701940100000c40d0b043d00d00e41207a020034079010407580b01e5032011580901c0407a4450408400a0002610400300001c1c20021030b5211084201640020b0782c3c090750b41c84981d140003241540285046500300045e0304d1041c030b000b4000300113100043c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 624055863 1250 624054613 624054631
    0xe0702070b031b04090609021b0d02190614040311010f0b0d29150f011d22020711030106123302070303320414070f09061404050906 58
    0x41e0025980f140f5500903203016101511050007503d5131841c0300703c041e400ca1480507407000301c98845500f0526001901070708020710358000e0180002c2d1a032030328805c441000c0c0295002d0380c4031920038004100f0b07940d21520580c460b4694901c04004821000e007169a402601e4405904e00030025600d9072b2060123400b80140e0100d456000741c0340c14100080003105015010a118286005200004c07668000076080c183d8141c4207480012050310044401d440c41b103800b28001d0a0100080d06541401c0e180303d401360806148800d40c11400b400c80c1c008903800748605403000d00c2d804900301c0d2146402e0003424000c044a148502c0307540c241c1c0d224080503c8091040814180ca08002d0360a40b1170303681620800c2e21603100e01103440300410305000c0c001d0004912000c001c0e05558403007403000e0760f004090114841c4001881e41456485543c1d44405e41e0502140401901c100b802c00100c1448159250000c0e0844081c0480d410f0324100d01103044c5440004003034841e900705801c1002140700061001d80c4a4043d17 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 624057113 1250 624055863 624055891
    0x40303050a0c020a0206160c1502030d0c030506130b0a05030313170601080d0302130302100c05010f0216111305270d14090111060109061403010603030509011115100e0702070b03 78
    0x751502e0215568640c0c42258520081c441030409d0b02d80110190921840800c03040c06124801c1a00302c044490480c1c1f29544207410702d0784031a100342542e002c5090344c60090440800951a680060314581111490108210114006002d00d15020b41000d841c4401c20303008143c1541400d0195885101c03503007035002050b070702094500a61010030740300c000860300906407582c1c00156440080c1950305071402038071950308180303c04070b60800510846425818006140c08814aa035541141510700303124015441014299820b4140c10148a46406002c8240c500088451141400310ba420341c0040070078041d400c20706d01222005e81141c800c851054080f041d103a518800d002c01680c0003d6106148581340c410803001080001c40ca6200340e0544100c0d4a2595850240104040c00e03901c95000040014009001104455014154924408014005886c12007281400001c140d0f54115900140c1180444080049201c0e8141b1349802200910150070901d040140c103160620001e05240714250301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 624058363 1250 624057113 624057157
    0x1110c0106140d1b030c030804030317040327050a0905071b05030d090213051503010b0301021305010f11030a0c020f1801060809011d01060911070b072006040303050a0c020a0206 78
    0x1c100307004e20103182c0c00300c102e040e496100c0c02d041d40c150300680001c80209a2040c205098514041f000902c00c0da490794581201e003c0300104034141c25460746884190000c0608007040c3c07a5142c802e22405040780c80c1c80040d207407030140f600070900b00720a600041450801d0207480d01040c0084101c1d9022035a104000c0f401d9038840c80443c1c542010100041c091238070785003e101c082580c0018803141c00c001180203000b000300c0b01c401c0500300e1261800000e44e0704001032041195501907554514035800302d0030688000c01c0180302860842d4010550140000e0318610034070210714199451040c0c0180982e00d07a180c0a8000ba4145d6510a040c05030205102c03050000030b40e0681c094001c0602606000003501d025408405858042c0199005440986081141034010b0590740021380d014030390040c07945613542c1c540400694001c2e11003921402c0781210f2100f41aa05c48041081a01030341c420740d00014545844004c030001c5624a0190b907085401c404141c4000da6511002c1d9000d0080b000034401d08411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 624059613 1250 624058363 624058403
    0xc0405040b0a030602030403080708060a0f090e010e0304030804030c090b0d150b030304060e03070503010e12071a01060c030801050f030d05090f04050702060a141b0a020c0301110c0106140d 83
    0x82ea6400200114000000c01081590085565004196907150640b1a071288030800c0b0041049000301c4a042240d544104082041a0400304800c4840400040c0451019101c94259030013a042941d4900c00010100100302450f00e00d04001c1162240810003000803000107082c800d5182c00c050f0440498580d611000501c95000c85181d88008017269039840e5698000740011001c02c2d002031190088500024060606010715142d006014020703010740d036072403110580c0603000316200307480c8100f50300520400324148090340303806001ea03510fa041d00480b9526005240c3c40050300014000c91081000c50f6298900041d010240441410104d450340607500104040308044a000caa02c1411b240501881c83c1c0c010072154010441e0881c18003c031070700420441c07586802900ca401c440c40c0d0703880346440002c5035030024040c840150310548441410050000b820343d0b41410348a41030400016147e04801001d119440c01081e034007503650300081c51200087c000c1901034602500c5038038880c210340d050741 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 624060863 1250 624059613 624059629
    0x51906110114090705090a0506030c01110a170909060a231203070609150204033906091701061a090d050f01090b01060e0d0201110309120f010c080c0405040b 69
    0x942e0800e1003800385015035080380e8640c03242c811280103e10348404210002410b000e2940320384405001030080b10040401190307090194000c015a50007010307406000180784001001201050359186600c1d09400d100708080c03c1400741c200c600c150501c202c200000110740c0c85120030b40c0c01001641d404040d5042c085a0301d07080811203a183c03404009442410041181d11001c02c0c58000c0c4624034a0034134403402c4104a01c99400017600358005400070501c0d00c0b20000b91241c0140b03866490344140380d420380110340301060702e800460201e0183c1d2400e12610726130703640341262021088024040b461515840d07500c0f084804408151036900050404407076110f0b12603030a07080358440220f9a00071001c00d0390ba4001c0c018518102c8074402c601c400000c02510980c060800e0200042c0600746089031740c0d00642d210800c0301209000c502052000003050b43d118100040126078810141421104400c121405c40d1206000001030082143c248030b000441700e0241c8082c0c0e0001c3e1000150092450b000a10030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 624062113 1250 624060863 624060881
    0x1d040303020d0209030f030301030c0f0b03011a0d09030c0b0c07031205071b0c0e13030e04050405100c18062c01030f050106210c02121602060a020f06010519061101 72
    0x41c42282c1b030000c0c00c00b40c008002c1d81202d01940002c407450307880d0722a82d00756032038078810030682900510050116007404000b400c500c2045240c4140750861840640c0b00791080700a00342d020403811843c2c5410301c20ac44030300300ea002000d0b06601e40343c0ba031140e40c060214030707132410300042d401e40d11170000340c04a00860281d058004125085100849107140448680708240541d020f520f00c402c02054071101c085900c1c41d0328a81c03545800d05500101c0090000402000304241c80718440c003504400000003c0c401c01081c84040e03503c41100d4034803421801e03203600da1944183c0421801e80103003041c60308507010000c07030b0056140c02c0040c007400c0324004034060284042d22054243c80d1000010b0700035000709909451075518104162018007101180c01190b0360000d00f41c0250300200400004203150200034107801c1c485c2c401a25011441e0340101385560030100002015911105100c0a0032204009c00750042c10119588010900404c10000c0c400c1c00343d12644003448284244000712010a402c005d0003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 624063363 1250 624062113 624062119
    0xf07061508060f0106020106230925030b031608060610030908281106010b16120305270307150e010c090911030c04050607020105160c06091d040303020d0209 69
    0x1682440c0103c405030000a104101c0503620748440010300c190904c641c20030203141429180d0360040e1042c00d00c02c03510b600600c3c1901d00903e94036a0501080080c003c8083e64206503030004441100d1002d26207000c11315154002c54018101301080703011800038006520540a841d10b203c4044000c02c00d030060049084020003081003c20144155080e0a400301c1d880880341c0b241c85c40c9525050350984039075141500c100d040e41c0040d0018060203040000600111003109a103d0b40c08100341c451f4000e1482e40381d80840001e443d80244807400e0035103032000303a07038151000700c400e045045501c203142d0b203100302e800040500d41c4003e003003804541c299100500c50550344000740210700745103070000c000728030034011001e0301854801d0b10340a00d0104416a8450105441858941800e100411400d6040b0300c0040f810024100030786607102c020b100014000754440d4804911940c203001000e803159203560070015071030001070034004000303501001854000341c05080060b9240161a0044082c0c0720300d001d0150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 624064613 1250 624063363 624063373
    0x120f0f06180b1807050114090a08011d0706021b0109030605250320070f020d06022104031b0c0515030412080606071b120f170f07061508 60
    0x101039150055107032000344070310b107001c0aa07500c00c0300c0b5004034409080c00011550003528140030650041c082e5096420710141007505080d55440011596000794101c810a80d4444590303500d1036441200c100c5114410a011b000124201400207640b18001822080084a190003051580e400380c820740019540003101804280351400b0b2000031500d10296000e0108540c00d41c040e400783c442d100e0006044121b44400c1c540c603000840d13240090300022000e80c1d1401262f004580140e42c0e079030149062a11813000942c035281c00070b40c07003035001e8649a49030355400c4000d020000020340c001030381900491407551101c1243c00506003584001041d4020344c4d00300145415500c407281541c0701441c480d07442104002401112210201c44428080e101c03590401401e11072400024454488010980d0f216401648013a9640302440c0400d640b1141c1599088071a40b0b644080c0840ca42c81640c6500916040c145083e482006140091041c6000984410b585102a044401e07000000c00c00604604c41240c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 624065863 1250 624064613 624064631
    0x90909010207020916090501080901110c06011706130b09070b0406050d0501080d090501270603020405010f090326040b030c04080d020c03030703030e01090515060a0f120f0f06 77
    0x24002e500c1004207901c52010100011403194110800e207000b40f070300760f51740846640b40800558803a04042c00115040d520340c0e200f0070050f06c58502400c0a18031001c02060b103949001d8035210b001c0340f0020300c0007440d008401000589071004603500640303940111103500036035a0502841c00c25490fa0080080f8500c000741c0015072540c4080a0620105110810041c40e40c0c0c611415903104a149400808a014200108001c1d03004002e507102d0340c1e41d045000070b07802e0006081000840400d0f00002c2c003289d80442d050009580c03096151950390329034100b000005003103480e1842009171107084288e545007400d103940e050b04540070a650042c682020203c0c0c0b00c2c2400c071120380350382c3c00501030101c0e18425100d41444c1d4620005004c00c2150307003d005545418002e0f107084028000034550302c021592581007480005804000d40300d85403003401a031070101d0805604214006407540c1c8400a41c401d0480c050121400302e040b03014040d544180d4540901016151400c654a42e458024080c149004054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 624067113 1250 624065863 624065881
    0x70609020a030b060a080a02031c020f1c0807050325050405060304060515030a0f020423041406090c0a210c14010f080702150907090f061503021912020909 68
    0x958040c0d034046a905c105191181002c3d5600c001514010794980e00c0300b981c2c1f10146000c28200c100340001881540c2d1114900c040d00b91070300d4070f1607044504141d4000418240c0503446082c031a001700052601610358240b038a000e070000050810358100b040c607030720352040040340500210b60080c6000382c0b6494132442c1c42c2c1071907401850115180818203101001100040c60042104c0303080c0f0f0761000d82002100003540070310006101c403904918910141114096100c0f19030302a80c2d120318030503c010110b580e410001c081c1002c201518054160340a410042c40310b642ea00c20001c29a02500800038140508c42480c00742070150a2001d0248c10f015035010440e0940400c02d80300c7c248003a25080210001440f00725404101140c1d0700005821003418103400a03014014035400082e00002c640741551124121001c89448944c1040c140c0d9075448100034800003c000d42c91203242c14101103041c440741034540211842211454010003440615200014625074141c072050b420140c0300105620703000301c0d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 624068363 1250 624067113 624067133
    0x210201030c0903031e0201020c2d0705030304180204092d1512110a03150e060112120903050d051b0304050306162307050c121903050d090b040219031106070609020a03 73
    0x211142092032b43e1500001180000d0349104951011700114507051420400b003100c4601400740e030b24034a408100c0003444040500845e0068410703c010424814090000801612100104a03030350781d0070b000c450111102916507000c01c0b6100340c107002548015901e441e1500704007000210f580720105500120a111604102c20782d0501d51440400620441a404598a01d070900c141400050000c42d0140080d400150740d881c080048c1c100529110f80302c0c0d0741e007420082c842401c900014004142c1d0182a5a1901014005581c44c0c001e9881c06003050003007511000300170300e0000081c0e259860820654030442040c10300172004450075180c1950702410080c294010503044d00c0c1c9109003207424500b0300e0400501d010019400c0300804800c10000c3c00400120350f03c840c140c090081c00d001151500c072850250b00743e49403041d22001c0443c503080c41000451750800c501d41c048000c1211062000a1080c1c040405054040300d4047c1c81c0c0903503160000141281c070304001d4004000302000810001021a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 624069613 1250 624068363 624068413
    0x70606030c06170c0403020d020f0904141911120a0507030605010e010801050622180f0204110f12060a152a1a060604210201030c0903031e0201020c 65
    0x7444001d500312404070f2084803071042da000300c20305000304010001460039109034020507101408000c01c7d40f0403440002c0742064204d400b079610402d4641c60f1442800148084110140a40404200d0b00201d0300c500f000080c05465090140e0754141070226115000c0214103100f5a000c01214412501d074504400600020300c80c00e800c0700b00500c000b045890060140600c6040090064181d01002010030300c1e006c0c06090a07452110790361000380d089000e07414507410b4558064600c110748411030784140002c42d80840a0050002d0050101d80c0c43c10605908540443c8043c2c006468161110000948030b02d210307500c0001424007101410020b1074004080361030000d00201002180b00d03110725158100001c000005005240480d010b994240701010401c1d0818400781c1002d050540710480704110302c4183c00705a0b100c50034451208215a80f601a503004040d00b407500e425814070b0b5540103800160100510300101c1d46010350708000a01c01d50658880602d001c084400e410702ca036107072503070401c0000c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 624070863 1250 624069613 624069617
    0x20708031806100e040605150406270203010b07140c1f030e0c010c030819020f0c011a090c09010201090602041707080f191406070807080a0506010e0f030102070606030c06 75
    0x40b0004942d158504800700c221040940403070015522980c8000c001d00000f40300406a10000075800100d40303c5200300c202510114210700107110301400c4000102d0500071800c04040d00400040c09030300d900700140c501c216404404500501124010b403800d000141062a400c809207603d9441580854034410445444640701002844e516402d4543c843e8580703400700c0e020401502c41100000e204074081c586c00b00c1220791001c01a6071700d03084001030382d001b6206400210004210810486800c1c41110324107121a0040000c01000c00c001c18204c5400608520001c44041407040c02d990003900500380039503220604642d150349070b07410750010b0b0b400e28090303103050700c81c1c448013142422000440d45211400840141801000101c1c5481c49102d003031011140003050050806e000f05007000414011442519200d04902c0c5c001e800901005000f0069002141003406210382030340c100074107030040402a107052100b05142408280644501000101ba042c54048000b00340702d8402000001c0c0c2d0b82503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 624072113 1250 624070863 624070873
    0xa0309020405070f081503070816080d0906020703020108070e0a0b13050f030c04090f0b0c19230d150326040e280c0306090c0c0c180207080318 63
    0x90601100c9210700d01c040007000c14017000c041a4001104c1200210441004084803901626088005d08040011a90b451103000e001c1061150b400c050020003c007451a02c2c080840d10300e401c00c000d685a13010705c8080d0610a4013800b02c5d01e068070900074094880300141655181c603036200128011640840d0000314003042c1d0000100e503504c0c5c02002c030b6013040710040c002c1440041420400c0b005059150089a40c1c1300303000100800502044e218a1182c001031a145840d091a0b010350040958882000c10810040d040046402e214121110b6a000131451140303849580c0405000c1c02845400140b900489000c2000401c10407841c1261140301035511403860748584880f901001d500490240d1500112490005480010020000032402c800511a8404881610351400403201003012150010751106014880f0602501a201146400d8900262000b00c1505e0300c082c2040e6900401c48007200310145840901a143c06965180f600412603d90324203140791000c8462222408056041c012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 624073363 1250 624072113 624072121
    0x412020607030903080f060d150501150c0f060509030c07240903020904061a100e0333060a030611040e06030a0309030206070c0f0b04051503010b0f0d09080a0309020405 74
    0x110703000f51200103500d84c0f1251030580754503683e8580d030b503c024121a04034440017a4400403c01000340d10480c1d4040c01c00004195045c0800d400340e01c0751840c141c5041c85800000107000480541114681c3c540090300000d147e22542e042d90b04511500782000030611803000c000c101c1802c0c003019084064942c00c00c0c0ca00000c044c21040c0e4821080307200207076004001000003008a003594101c40310a03805000000c00d49400d03040044c600300f40491442000402150360b0801501781004501c0c2c030090018940c00982e0b41ca001c80900007103a644c1c0c1100c50344600008030b5956290f490a0102640d40300200b4018080361140200082d003041c400c01c01001090030200d9002d04010a00544c030f590141d654000c25401d6809001482e480248102c0702d00c41c902000103242d0800300e100d60058080c0c0041c080d81c1ea132800041040d80e5844002c1c000c07512108000400c1010411404c5030520708260b2071040d01c0c0c200110061008051811024010082c0000c9100000d54141e11a40f54548215410082602d0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 624074613 1250 624073363 624073367
    0x21009090f15060c060f110c0114090d0f122307030c140a1101050903040911190e0303041a03060103290105160807050f0715020607050f040e0412020607 67
    0x4850222a052180c50080c1400f407a413095802c0f8629501890020a03144900c148180403108070302001410350f1004161483c85140070301490301195680c40c641d4100c1c1c2000c1e202207448603c10a814824046444403c4441c103010342d517030201c03e502c445406c2003590626002c1c07007d448010040c40800d0030141c0700241040c1d010f841440c48001c659903403d14075030245000006554000e42d452410301c00701041da1b074400700c42406403c2c86502044051900c4900e0180e141080e142004109400f0382018466012030000d00c2401c40400d0b4951f01e005180a82d01c540400d045119682029401d4030201d441e0782850400040218000c820a071f90820801a0b400030b501150f0b0300b8000c40003103984100400349619841103000d00b5100e01030308140c040420955455045a90002070300721201e0700f1002d0000c82400c000c1c000c0314001d1101840091600040c1c20001b03480303200040039101030020206010301a41078240595000d8442c01d1182d01042c2480c1c14120aa070004103650f0005104140001e10b4440c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 624075863 1250 624074613 624074621
    0x4090605090c06130b0d1d0f160509062b030e01091d0a0b010203190c020a090203190e100c020f1c09030f1e080304060b0411030c03070c021009090f 65
    0x404d03120034005507107040c4005142580d000c400240003640e00e032061016440009140c810706202200000c06040c41c402c0c407198188030b80c0c146c3c2e680e0481c3d440c1c5810082e5840c0d5000147d0300032011180c1c0754816420f044500d20708180d106000d050016170100c1401019003085101d0344520003600ea62010b15518016800d00d0344502030300f40360941c50301010420701892600401c6c903089050069a00708000503214201d054007842e2001c0000f0040d0401c0700c00c2d4200300f02540080d10341e2030b1040d440c5142400da189490444d2007901c80c0000e64946c0740c445003000500600300c094032202c40500c41680100781c020354400313150500a600313014001030750000381c45104441e0292059912041c0d08186903407289142c0c94004101900c0c1111035519180360102d021890510740c91081d46a42e480341401d0a04c2030454054035a254003075031400e00150f65050390368007540e520a00c5811404c2e44c039621264200c0d030600d65800e009422418500102c8503003a04090b124094030301d00360381048582640001c001c180d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 624077113 1250 624075863 624075877
    0x70309080105160c050a12030b012a0b0705120c03150a05010f0509011709071e0303081803090306071d03012c030c07080a0311011a04051504090605090c06 68
    0x1e000d620703100100c164084c2034200c0c4181d000d18160350300340100e40c90300f104008000d060580000c3d03482503020342544c0c016503000d20070302858060b4001400d40411034902105001405050315080c400011491803040e011a000801050390307000081c100380a190006070401d40c0c00301480f0005983c0c8459605298181c002101c405075124000b4034501c0d2130a0701c0c030350303c0885a107040000a26801208082607484540607202803401040e500d40713002c89415071a2090001d0040c0900b1190301000400d074403101598009090801c8030040c86100c0d030049203984a4580d5094050040d0750401689503080780c82180c1151565101410791142801018201c695150030f60141701109446100e011101680d150b5100c0e210008880c0f03400c0c20710001d50b240c144a6808010164810b0420303001305036100240810040d1070030002d100c6801036080040081c4440c031100342c001c1c0c0d50380300082d0102260000c0001d03031003009401040440300c142080c0028240480b2580300510136034080031694100b10080380d0117 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 624078363 1250 624077113 624077131
    0x20d021806070c0308030a1104080d09062115120c09150b120405031e070c0e06060702040f2007110f01080403030b03010605090c0a020d02030c03180d0602030c070309080105 76
    0x30350341c219034600c41d96800c0503141040c41c40ea508c00707800050801e20002d001400e410300c020011070302d54410013010192203400000070015002c1b068060313260b400900081c4e0305584907000c90507120802010300007910302d500018030424031210352001e010a400c80c00080d1070040030140114001c0880c248507183d07441c8105480603000f0003031152100c103460350081e00305100e20300781ca28102000c1c081d14060300441825a26824000400340d0422880441c0f00c1c0090070720a28441c028500100000c24138021140c0280c00799480703900845060303169500c1045002d0300c0e55000c0038100718004004180c0e81140b07008543c0b0342c0312b0301c004016170b1030300c0300034020304600580d070f040c0c00b503691a5821000b90040c0000f1315010b640360b40700800c442c0e55494040e40700c2e0044c0340c401a20396034440c2d002854540990b51040564000300038040301e602d8007204403802c1003240c90b0040300d406e2100010410060900002404a91002c410310244400c020300411480d8026903070442102d45a404050807540e0a544100b9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 624079613 1250 624078363 624078383
    0x90c0504030b180f1b0904032124090b0604050906060d02070507090c0e0906280503010f020702100905090a0e03070b041101170f1f09020d02180607 65
    0x100c104402c42d91000b9074164001c900e0400600d003e1801c40c0c40c0a0404a540004888442d5420241c03000e041c1100d003100c0b090032904054401809101002e052800c010350b94142864680d0360365006400c42c45000d1041c03480916115801d0350001105000b40d29042d070034011084180d192600556084d203800038405512a110313581009125440701040c40e014503001d0014401003a01840441d00410300e00038040343c03854500350028400550300d80142d10601c1801c050014584401c030401e10170120111807000c07070303000b030000520803c511544500c1e419800c1c00807420040c40107401031300000b031003915040400f444806055900423101c1c01015046a8588001440e007281504158114520300041d43c1c900302ca40d485a0b180c40c03c1c00c69054480741c1c0018001e02d4a542e001c00c070040c504900e614602050300b051007410b6558400605510002a000c81d4010007449404400e00001c08222808660780d8000c00382d0200a1340242c001d402c03094581017201800c1d070078980304403040786502040101e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 624080863 1250 624079613 624079619
    0xa0c06030207021909060512390d120201061508042301090309140301020a0c0204020a1713110a12120315030b0f01080c1c030c02040c080a06090c0504 66
    0x400940082c4810399000d0f080750030f1240071042460301c280191001400201e01a410030040c8240300070012019101940807a040d9422034205242c942010000340c0001c0c6c503840c1003040340e0201e0803403d180b43d80d80680281781c004104a05103501100d040075a40090041c16950010403041c10304610b034003408106c03075500041c00141030030345411120308007000383d103070300e80d2a4803c403400c58a9500040340400c2c0f0501081c002c80030710900346640e48000b00c00a500e08000c001c0003d20307407046000002d0184e0307008904030800c01d0080a13a0070100000340c04c40070701032915240200c107050350402c0a440046a081000d11281880b403888020b44010030400b59000c5065030314141c42111401c070b40d00800d691925211411b238084004000114041c18800c40c07242420000c20422900682c458002603002880202c425161284010b2010024401d007a0b240c1800381002c0d9a5141450700c004d5100d03140c005408121500031207594029950301d002001401e455401d0700048450590aa10100d00300340410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 624082113 1250 624080863 624080867
    0x10501080106180323070504060617042603160c0308060118232d09100812070b100f091a060408031207140301050103050702012415020a0c06 62
    0x14071000801c410701504690f00d440e1340048400c0880c4240c0d100b403601801700c05c40c200402248001e04801c8030100800d501d0000080e12071203510302c2080a980208001070207000b03082d90fa0641032140d400044000e036070441506011640704032540b0110034070034400c030f404161003034070706d21040c2d6030644481840e03880d2500152410f00804400b100341025902e8003085040c02400a04020203d480d40c1310704180101d0200302a02c1c0d01d082541040e100d85101c02d10003030f504c81030b044090b850141e03075800a5845050312a100c0000c5c64210b10302502ca0982071003c000c05940081080e64095100004507031203510200307004103054811400c9002c42c41c8014018480180d00610240c408140c0c01c1c4280c1d041d07640450010380042d4080708598001051000344505440001e40d4030200b186400c6508818a41e043c0e0641e01041c0100c60405503a0790000e25624001d40c09854600000d05100d9861000725101c6854425140502da05021100707401186403030001400c1e441c090b50181e01e40117694103103141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 624083363 1250 624082113 624082127
    0x1030206030705070813151101050c03011e120b15010201050f040212010b09010b0408120c030703050f071b180905030711011803030203090a0b070503030703050703060f080f15010501080106 83
    0x2c01d8070017207001c000b8846003400900b50382c0700400c02c90700482e280c0d0262140103096200c1c0c807080c0141c1a410031007000100c03002c0038110381c1134414600556100c1c5103501d81000003084503800208000c4036500182d000e1143d9800018816a404c0410710f04001141d4012800e03180c0655000c54175940c803001040c014500a00340d804d440d85120b000180061211002071509902a0b1000d00040400a003d0003014018007041079010741c00f5680628148030100c20591741c2c8109140602004008240319019a159004481c9603a4120040242603819406d03203010700c400a00c1040340541080360000c65840c0c5a0041d003c0381034002c0003550030700c11280c580d900ca046443d60464100200b40c1420441a0316120200004d036003c0d900554860702440203001c140400d54000300d110640c14440c1600181340001169440b81d1646008205500c0b000001e5000e403032140c001c5468091070f19000700310448005480303440400c01c0400c0b141c501c0d10700910401806800e00446002401c22801403081300d0003050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 624084613 1250 624083363 624083377
    0x10905100806031f02030a14100b0d1103070513050906181312020a060b030a02100e0f030d27050612040809131b110d12110304240501030206030705 65
    0x105440d42e400340c08480d1000302240e640f00d4001d1315030100910940150718815920040381c01c0304280518103184403c100c0d955a54819001ca8101c00501031100f000940c203d81080307603500121948a0610f0a0054903d0304898082e0b81c804c4540840000c04e40380200c00c0c50300445e00500000b9800380c5c0000d0005800300001c01f000c1d4040c00c50180d41b0009031004054005200c0564082c1421041a2a001060740c111110f028860f03445580000301503038070b18800148019a40c1480f09090045501162614039000340c603079410f000700d0030031007c2c00c1e402c805042c150007044004524452034021800503000c40500136190840000e00c541c101e003903030380b854054201e4013450251b4104811040096044038414076100c6a09884080700420590080c003422200407903824070600b0075041042855840c0181c2800c007003008486110f80e842104180d124244102039090219968a414141007180075010440303003000807845082a05042c0ca60301c02d050589a000f800ca030301e0f41d150441c08641075004a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 624085863 1250 624084613 624084619
    0x30a0e0f0d110d020d0e12011d010c230405191809030906020105061807050f040e0115110a0f0812160e030a0f12020a0803070801080c010905100806 65
    0x996090300690040215002607030042d81c98541e5008040005810416031102007400e44d40401d44242c0000d80001450350810815a0841c0005a566400034050040c40d1040e845251503034803180b036152410341040d1004049a1180142c921111024542c545d00a5280500c0b0001c180b00900c03940c40c0422150115545419244581d2904c3d024440218a4403000d0121001c0d51050401c08160b0010a80c000070900c0d070008020528002c0c0100d0151440c00c40b0a00003041214005695207020f030094070aa980f9100300141c5a58441e0740c5030800c9c0c4001c3c020b0111817840c0182c400c1c210784c4039602010f4261048030141503411311968405032804c08003c402c8400c1030b018446900d140314901075051040320301c0c5c240c030010026203070b80142c1007444140d00d03d4043d40186080303402090a03419a500640d0f808401d90548164128040b401c3c4103411000410500c00003040c0034055511401d0705041c1c44080054650b0304aa410040d00e00d80c009204072a0003c2030521401f107843d006054281c2d00a60107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 624087113 1250 624085863 624085873
    0x19050703020d11060f0d0b0402040608040f060e010c030203220f0803190c02030924040b180414010e010803120c13030605010824040803182a09070e06030a0e 69
    0xa480011116000172020444291000c030b18100301917003e01900c16116400d031003c41c07a050421400600f80c99000708081c20180811500f00c00f0041340d0b91003c0b460480c200b00070081d050b01114020040c0d030090b42c8650004209075080358511101152a890595104d900e083e60110559945107213900014440906140c11041c000707a072031094007902c10a50070541c00b45644503000e108020102d1401e0401711410300310340e0102c1c4007501d107240c1110152a040140661a048000d50401c00700000400d030315086803d00401640d0f002c624070b0405d05030340c0500484462a038813910055540d0165001800d1039400c45000310b007403413a003800240b154418ac000d0f00500a5100e444031816680c0c00e900c984180c0d4480f101c160300d0101c10001103020b000940b4007103203040c10540c0701d000f11070102600e0f050307004202c2910b400c8200301c00c2000382450603501c0c040c0c40d2052410094411141080c440e818090390410001420031481000c007946009002031400e404c6856126010f0018880505180740300e101d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 624088363 1250 624087113 624087143
    0x16020303071211120406050708010605090f13020c010b012d0f020a2109060e0901092c0d0e04020306030601031223090a0e0408040605070c0902031819050703020d 71
    0x10080188442504c14618030014200745c83c00a0071207c004101c04108a0a0301c014000923511408580b14504103e860940c407480620006208000102a4841c050702c000707508088040b064120401d5081c090322000315400751020406191961204013042c0d020100c48100a00f40c041e80c200e42e0310004030710417500d5000d4941d5807005a030a90344914a201c070040c2d100b504801d41d01102440c00740c001490f0100202a459020540341203060040705507650300c90b8008640c0e00e01e400002d032007491180c0c1000c0c07071100c012100540c8540110142ca40042c864640342400e50810f0f0003140c0c01803c0140040072947e20303640b6038001040c88042c514040080c0421a002545d2568180014401c44451003c0e56180e802c0304000000c012070344030720126400b4000b04004a108003041d581160713041d00303040d91782d4581440d01e083c8940194124200e043d2020040c4009d984985651003900d1600c48220355403240d204504003084c0070710711001070240e80640d0040c4014100b2040381c0c0006441070141c05c400c214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 624089613 1250 624088363 624088391
    0x14060f040b03040b150a05061b03130603150902250311070311090603010c08010b030c041502160519050d1401060b0d1505010c032105130b160203030712 67
    0x2100f40c0e426205008000240300c20040094030118103400700b2144c52001034640004200e80d0300400742e600e0800d041c00114641b50b41000e00403921401424984240459207854001e0f00a0041010b01620060f0080c0080760341c2c00c2030b02c01c80d403800210b10071000040030b40e502d00b00141c04130044101c040203070088040c000710b0800c001d09005980315881c0d00070113118010502c440c0380b200411007440303603041c404040d80d8282c01403400d0703055440c0c02c2a9176a81c1d0713403201c8840b00c0d2445658407200e0464024084100404c0d40840c03141102c212144070203000550b1102041036906210080f04c240c01c2d085142001140b5064000300c0b070b4203103d800400000c600042809084400c143d10045442500082c07001ea40c10152040908a00d08408425a118100000209110b0840f24002c050010901869802d007021400042c05c0d007035846401c4c005461b044000c816490341c40709040b9003140121011401682914800c1c100c43c00e2598001c605607590303c0c10480790440000f44807205190741d8021508184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 624090863 1250 624089613 624089617
    0x30702070905150906060a0c030f020a0c030303060905060f01052a0a03051e1608090612070509120c0d0303051f0b071118010603051008060916080714060f040b 70
    0x21a03c420f81c0d2802ca04603000d001d869a0010017080c8a9281003061001c0560050000c084a40c1c1524020680c845807031001d80c0707000d200e440080e090001c00d00b400410141c1c1500480182c0391010f4046c00350b034540600744040b480110304c10a000ca1000e02800e20104410f181034400c030b800c00c1c0406410081180c0f51907061440004080e400a0301c002000705106442d007255164060201485c00c0c07403c140c24500312002c8005800050100c140080c00c46856a100d1041d00d504003440001c2c0d400b20f04250f140548a640585480c50141c0c030120b062504594000caa0b01001040140281f00c0b000400e580880042000814400542414401c5858a0000b070105480a801c12400b080ea480c681800c000d07507441c41402242c2e1043c034070103106404010402d20142e044843d242000b0031030f0b40f20b41001e0603a00c54180c1160b4601e215080400c80a40c83c00181c00090f80340c2038810741429501c0e82c580e9611010303140074114401901c0c9603055194144640103081c0c0304408103070303c2e00b049e031260203848190b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 624092113 1250 624090863 624090871
    0xd080705091f080f0c040303140d0e010504030e060720180708010513270c0515091306150c06061203080a0e0105150405040203070b0a050d2f030702070905 68
    0x103940b1810640c9449604140c0da0342d003142e0205241c100c0340c90403580010061245020060812012004502d03029011703e0585503400c00004041c00b00008d9064098000d280485054000075000c0e143c4801c5c9040130000c5a0083e5004038140c002d0307a00b258080d049031080701441c603800c203040041200031004940312140c0940d803d0741c3c983c00c4a501d4001001441d8880b0440d14020601d040498001c2051042c007064590003180d24a50300f50780756040c14428072a00b54403054202c00811070b0308505a404000070065800c0899120a40c100d2070f1011400300d03106030285c40000b100d10b900255001c0d004016405095101e0303040801c5903a169600441c5d03840e9512421400705e02d00b0024040c080e03040340114410300c40218020031451804081003045203000e01900f80c09036607034a0200342591418400440540800c031102d035a501000c1d1402000c541c0f02c1e903820b80c1c1c060310342a001c220500303010291000151300e42c89202044220550082c00d551300107032602c002d601c1005000070360350815004031441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 624093363 1250 624092113 624092149
    0x200a02091f08150108120403060906090203010c05041e0e060105160503120915060f061b010507170f04030c06020d0f0c09060e0303130e07111b040b0904050d08070509 73
    0x41101004a40c0c40c1040f4103030400c2a150704443d8401e070702204020281c030112900080045035078802c41c00c04c07c00030000207802079015402c01018aa640e608a0014000c450f850806800010641480310b15806031502800d207120081001040c403e41c4120b000e132500e00140d51a00307800340364640c0c4441c91948408650111840303101d0810005079024000543c02208400e2608114545440061a56910141900e10840c80440e07011814100c0030002e00c11001c50f94020002d034180301902a1508850011902c291a02d5100040801203081c0403207001d1541505c4e0f1a43c0b0300290b0781c8800c065000720540590f910343c2e5014103003460707106001d0314402c5905074607010092803c0c11030040c440418080a10301950080040700003200000c6650070840324201c03a500b08940760008122001809849446401c1c80740019403010740501c44110b9084c103030215820801d51304403500f401002041260098296003100380b02040403401049501d030300510710724080b4035040c08000007038500ca03210807075219 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 624094613 1250 624093363 624093373
    0x5151b1305010912210e090907030209090a120c02010e0301050412021c120905030c1b040c110d032c0619110d0906020f0403080901200a02091f08 64
    0x4540d581040d1042c01926802584503c144a5a292a4049a85c0021142000c2280c43d070311400244150021041c09600400074190750410205203591003010b80800d03403041e0890ba0105c0c15039100040d110340159440204000013610104055544c000c84400607814041264012081503800b0311409200314800d010030f101003600c50304020b240c00030705040a04a0700d031003031441c12803a40091402281c440800004144000705190083c00e5002d40e880201c41445104010030080110504510b00103506071400c2100409043d01200c611241c0300c030306420740e00310346002c000715031081d0485803913414034203680001841c43e110344000120128600030880c1e080201840108100c294480e0740b81c100e6114107005141d1441000c0e0001d205450200b0043c550b900841d1041085a405070341050a0050440d900e8075039070b0821228503840802024000303410b841126040c04040804104c80d1050a0001e1511106642c2440480c0c54080c12011100006031740b4043e80320020b0450304090094040070781 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 624095863 1250 624094613 624094619
    0x908030420010203180d020303040815180111040902070c0e07020d02070e0906071229090f010e0610030e0a08040f060e0d0303050a18060606170405151b13 68
    0x212841454621080c11508104492204d40500800307aa0600354100c1d2000c510382c04031f10000740703944515400707013529000f0002e04186507070720310401e0751203903403801c41810410032003242c118201c0d01014100076070306805000c10b1088858a6000d0200a4402c044004d0700c15112016000000000caa1040c01039110141055000b64140f00b8900208400022403619051590001d80c60750760083c516400c024020024103a000c0c225001050310a0529411807102e0415801d04000785160030342c417078021900c05020540c0214034a2020b07040702d10821454165845050810844409640c500010151a16402d100500d8107000880c26144a401040d03501c03440c00e00c131810400c295600040c20b001800003416696198029500c800590514001440d660380b444c01000901072000c0041000310414407440401050782d001c502642c2c00340c0c941d62102e101e840000fa80c20b08085070020180d4001a070600031104e4014007a035008101e88411502403054410720440540044841e000020a004410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 624097113 1250 624095863 624095903
    0x905011a04020903030a14070f1a240402090a0503120918090a0605060d29010b1608091516110108040812060a05030703050105180c0102100c0309080304 67
    0x10540c1100507503095040c800b895001940303078002e04400300f00340482c03485103000e00030b040c10803641059805950b60700708a089050604070400b40c840c1450000d100c1c840031a12105035108030303a9401109103100c03d0340d09000000d200103900715688007504640c074503002080659050220404040101580e9034aa95100c001c0140e00008100384103200c1084005010f0314030008201180c4503030304150089850380703c040205088642840e00540b400440303001c0c51000c0d8031031070f00250115403108003030f12682c0d8070741440c41c0c60303446042603040c030150b50b2201900002d056940500b1910000801d2030050171441d40d11070201d0b0744010180182d0065200490041115004120071141802c0c40c2548a6180c203a80e150800c0c42484080c42100164000203592903450040f510064031010307041e07840750740d542e1811601030b2400b6142400444030700c2c0b140c840b02c52000500c54071440016801003401d0101d600910b0010a20070840c0c0d0f04050301d940c0820042040343c001540036610440103500f40b04028904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 624098363 1250 624097113 624097151
    0x15090a030c0c080304080120090108010605130b03070810061b14101e0e031305131b0c0b0f101e120c06020d090b1b030d09060c0f0203041521090501 65
    0x101040c8c0c1c4414085181c440e68040c07040c0c0d042d1401824800e40e03800710841100003560309640207500143c0300004002c9600da00c8400a0301a8000070910700926032514000d403840c0c0712025900340c51004041c1c5000c040b4030200890342603c44100c00f96220004240212003d40b070503103a0b2618094404d000c2c0c0c482414452180c00707510035a034000b4506103000f515031513501042900c90144030361071b03c0304803a444807115030002c501c4610b104090000058404030240c910581800251500e0340c4d5280081d80203005400014403d08600c400c8402d41030800c803045041210b105c0141c420806406000f05920003c0362a114038a40200f5010300001e203000c100030314000000001c0c1e000c00100e5802041006442c0c401e855602180d0030a40b1407605058519500d54021602081ca0040c2421005007d02c503403a40064005441640d4443c20f0828803030080c2e13641d210301d00c41c0b010036401441a00742c4440c4070f54007491046082690748900b0210307101008040d80c5103240c083da4549d54400b2004601c1c642610 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 624099613 1250 624098363 624098411
    0xc06061502070801021c02210403091a03040f0b070c050304120b06010f020715030b18090609030a0206040308180d090e070314040f0305040f0f0815090a030c0c0803040801 75
    0x10007985040400c405041c0a00e01c103a032a0f4000342e4010601148c403080c00c6e00c0305103d004400521741c0d181d140600b001407070984948500004c804008124071400354404080b68460b03a0090f195a0201d0000d580fa035160308001850b0310100319002c15800c00090090dc0104020a403103100804d80b0305d59800d050514680c060140e5050007041c9043d94003098010504c14219200001009202072407010103401600640306495403102d4150394005a00c484004824000c041c244129003031a901d8044440c0d6030705c1504021405640000b00090020740b00b5401030382d1140031305c0c02c0200e030415071140407403501030003c82a501042110303009020744040e41d80038641c0002e10703140c28010040d00036201c803000304001d040542100641d9543c0000d05018408807001000d860b42500303001e80d500c21060040e0321550003411014000c180050144950b00400d0b6401012420042c0a2403100e9640940c1c04020011086036213182c5a10000340c0c0c050140007400041001200214040c030f1306504111141c04070348 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 624100719 1106 624099613 624099629
    0x4060b0403050105060411030a020c1014070e030d0f0e0301090f050a0c0501030603080406030216050f0d08090604030203040608090705092d0420010c0606150207 71
    0x48010310841e030180c0300070005a1140e0080100381c0f00d1394400141920001e0020400701d01e0103600502511110104890000050080601c02e07103074506c3d0290ba000c0400020844040e82000c2d0441c01c8040407030207403820310b03905075016152411100c00d81040108200d200541510250320907200507410450a055540c150b103809680ca0000010464240486100006403940a07000c2c60381642d60144805040c03c1c105401100250444260096510a8001c07a5008100c082c401a101c0c0c0c40780304054122400c0d031140140140002a05000c2154040f40400c40800d5001c02a0f9050756001d00d0b140074a501c4d4501c03072a02d014460f811446c3d00854000c00d010324002034076801ea0006014542c0104000c000f02c1c4000c5c014072007158068180c1321151021074641500e55485281c07490141000400350042d0345a0804490f03994100c0c40034003e2007000480219010440040202040 = true := by decide +kernel

theorem cover : BRFrame.Cov 623920863 624100719 := by
  have h0 := BRFrame.cov_init 623920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 623920863 ≤ n) (h2 : n < 624100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
