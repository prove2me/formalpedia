-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1361
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:34:25.797552+00:00
-- url     : https://prove2.me/submissions/c6cdc9d8-7864-4465-b34e-8978725d1e7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 244604316 ≤ n < 244784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 244605566 1250 244604316 244604323
    0x10903021b150d0c18060206060901170616121103040b010e010806040f030923030f010212061201061a030901050c040308120a0b03101a0102011509180c0b1306050a050702040e 77
    0x205c0500c080d0141c13040c0080c049034007042c003500a500840b078080d83c0b40d80e1007004444d0902a0011081103070060001300d0613002c112246a80c2d0710300c036400d0843e9070714201c40c5120210313a041812000318500000420042040c03800845002d41420304103d4015410405203d80c0c9020061004207013006069600b4207160260f120240141840b00314411203c0515070b003c000b01603000c400301d0003403050313404e104124001130003604d044680d81d10078540c99030707aa1001c002a906c00b030400780741995615240410412003c85410858030900082c00b50f490a085020320300311980200224100e440900042c000101c0701b104541110303280b90070030219901d4107015040140425443c0c00d0703041c803039041103a41c882401d803c1050301d5041c1c0903d485109101d60016030030b031540000450380d804407090080c084003005502c40810019800300c0c400c410800c980c0d800c0c202c2051500109100c00004c296010010a50100780c0050442c518129041940d03504015181e8011240024850703a26401070305c00c89003040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 244606816 1250 244605566 244605587
    0xa08070c080f0d09020114032809081303120903030e01050309070e070c060506030111070213020f0403110f030d1d010c0f0b0f01140607140f010903021b150d0c 70
    0x1055800e0f520102d000d600401404e078480100e010807581c4801a000140500940c2e204030819900d81d1000d0410a50301040c0050b125564030740b482d030b919210350226880c40082c011401c1024804010359041d810801c1c1c2c0341941000c0141002442441880085c0d40021505a0700c142803c205840e07895088440b03040905c590421105d08000c5400c005005901091491007030340180c0080155459000c18142600d17000200748140010800c520001402c1007416802440d040702401070a000d031541003000c06a105500655800104580c072100c14034100d000403107915021402401400d0248001800002ca01010040901102c0c00d1340b5089901030a024548660710940003810122a85840d220070743d42a034ce100007504aa00012030380c0b9400c881040260080146030606103800303070390307540055a8442040b002074001c002c546140a002401103a0100740709802a04550f008280c8546924450001852080400c112f4160401040e401140d41e903c64515001c2001e00304070000380c9154003039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 244608066 1250 244606816 244606837
    0x714010c03021e0d0e0f06030f13051c170609060402130506070f1b06020307080304140a0c08010b010f0c02040b0a050904150b0f010e0d14010c051803030a08070c08 72
    0x42010340d000040c049000684d41d1400c2d212038103543e00c41d000707012411040301c42842c3c00c8103040021030340c9042c1c23500010740e210154190040041c0001e03076805040c01495001500b10005402d81b04007466045416810b81c0c10308042202c010b4540100060840400604618003d65002a4040c5801c2511b5948400b5100141c00540e03507071250320340b0b0141014620008d9448050842500100200d1207214404032201b907401541007000941315090329503c0038008445421900502c010311110138451884c0f0203021700c2140214900e0001c0843c02d482c401e2102d28100a07108070003015450704444407003040c2d034060b94006079901e69280415840301c1640c01c5158842d54900c02c000800c9100011194442c2e0180028800e401d964411710040c685400c50f0213010070704541e100003140c10720003020f07240d0500507040b4070f02c1352509403c102e0031180c0ba010700c038000030000034100340510240c5055003000030080d0011481c28039401c1e0004c10801d00035000780104402c000c0e81100780202c40040d6042e0164 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 244609316 1250 244608066 244608103
    0x10030e07080a051b030a06020f0706050906090d0315170f0f0a0302010c0905090a050411100302131202010f05030901320f0105060a030906020c060103060902120714010c0302 76
    0x403142003496031400001400c41d280d103d42d0303021240ea0300b0a04115a1070f0714005c0c1c024403861006030745204c00b071f400c0f21015801c0c1e01c4c0d05008075004100f86014950289035003034081c000a05004400c1420404480d03440000e242c2494030400f22551050701c0441103860702045403070f01c0300358150744070b04205541030308019600c11485d01810b10413003c034598400c6446500200000b08003043e00342c800c00810b00c24540d0212094000880710040b607000240c0c003901c01d50b07111030300226940000b19410400700007400042d90204240c54072043c02c800c102c0244c04514403810000300241c1c00240444045003c0c0300c100100031000c40c070120b100350040800850a40200b031000362000100c6d10a4504100f0750554029181003c22000345040440505803400903140a00d44401203100350041c0c1041c61040741c1855080001c0c0940d15800d10059000e541300d40d0004c100c920140c0100400101000803103500e68104840c10007900b0700c085065640030b0030038280340845100c0d5003410390511044014410503c034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 244610566 1250 244609316 244609319
    0xa050a06051b060408190e03120a110d050301052419110d0815040e0a03050f07020d0f0515130f08040302090403020105010f14030c042c010b01080f040302060610030e07 74
    0x5c00809400c051680ca030038000f903401351075012540f64034409030094041d040340c4041c0c0780c840c412100030500d4407040d0505042181c50560b1852508074100300000000d5070100040c80940340c021080105405100403610b4003c1070b00400c04600d101c0c01e5980c9078410034500550f020f590080c1240c2004d1401001a038022400740c002c060011001180d421002105030200034810345001d12031003100390310010042134901010341d0151501d9012440c40c00c0d841c4402d01c20000181e482180032510b451160b02c0740c41c101c000a140640c17518100c15003003006c070011041082480800a02204442d036001460b2007030542d0035003000c040703d10888e040170f90803408040421042c145c05411190480b0429407140081e20f980d00050b00e01010f0f00c000c126410340100b4002026840c15410000141003215500d01166a026285201041c919012034800c0d035101d03540c429503036030080c407980e500c0350030020100e02c6440c20303903002502c0e0003004108500c20602130011440c2c0306d2082d4002c520b40c1a0000840b141203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 244611816 1250 244610566 244610573
    0xc12111b03060f040203010e0f0a0320061305120d0e0705150313020103020421020f011103040b0d0b031606031116080d0902090a1d031e0a0507050a0c060e0a050a06051b0604 76
    0x3401604ac00782c0114040140001c003482100c1807184440b00d00e04050820307174545000000c1d4150502d1001d842621401e18051185290310000b4580700c002c040c800600300d40d003c3d03050350401003250301041c8a031071030700c412881280c00701003183e40c02202e00c13201401195840c40160024003654000b04101042d1a14a00014803891031000000c0c1c02100e0f5054011081e100440b050400b0046800d5513070010b2104001c000f841401500792506202c0b000b088001d19540070a141100c0c5120b112007503207410f03208000154151091464048548402a1602e11155408000c600300c3c0303e07005140301c00c00140c41018411070b0f40485004c0758010100d400904014522030081c1440641c01842e0f043e50501c0f00544210010444580e0032030007280b050308001c0806e4202058000321040c00a00504006400000d0401d008118189124080300440c5a0400e500104a03003041c1e9041401012000c4081c00035654240c240d41c100c039403910b4115502d51101c0603d0b01c2c42581c4100c00c101da80700d158248002c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 244613066 1250 244611816 244611823
    0x409020909131104150e0702011b03050402060f0d0b040e0d20070302010c0c0806010801020a080703091a1e0f01090e030403030f0f0c12111b03060f040203010e0f 71
    0x24158100c5078100769072500030041d080844000401080d00c00700c0701d03481c0c03100d05264010305c0304804850606000f40b640c400c0708208540d0110359660040c2d6440075980c1c6041c01d03403414081140c10a107002c2043d03150130760116090b84070300e030084421800c020a40d01d040070742903007203401b902c84044d00a00100a0a80c4150b17521001c1141d035101040100103451401d81100c0180c104100340ca00080035100e00d940c0064401410f1901d0545800a000002181034103040100c14000c04280c03000603510301c08002c00410117000900b04004140c1401703030440106440307010b00c401500103020a51503503101d00d1441c151941c2c00d40c3c015440b8052600030001411004444181244c458805c14407a418090b20380307648900c140d000040c003007074044005020040c80f54022803a400120300f4100c05401c040d445584000e09518a0440041c01f180881314641c90140310300b00c4840f00f5010180d40c900b9001c400645c5a01d001015003150403580400a01517560940107208a4440d500075100190341225030b640d00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 244614316 1250 244613066 244613077
    0x110613080a1b091107060e030910050901020721030f020c03071707091134060506030c0405221b030b010e090a151a040c0c05012403080d02040b040902 66
    0x4142c02c50700d0000481a0140c09542000400d214940389042056034075000100840c1c1f081e2889448148101d40e05511000e40301d00480c9181d4a45c1900e0307070142400280303041c0564000b40c41d01a40c0701050110383d180600ba280b80c00d40c4c141059040000d052004a01d40b81c942d000c055030510802000103003103800f030140c0c002d2000c00d038002d8a88a40c0c448144009840c144001c110401c0b02c01c0140c00c82c038811003541a22180c40800b15410042d4122559410810001034160342d02030f41c1c2d20903c100d501d01000325405106007614140464504a8114040f84d04e01003110100c0400715a0a00704101201d946a0000f003031800c50028100d44904021040c1079090003010a00c0400901007070050000103201100ca9601401041307000103c0c0c100c400152032a084c1650001d5118400745800341c1d034034040d403d1604465901c4000c1c03103c10b410410b0a44002c42e02c02d206242103c43c0e103140668003c0c2c0b524082d42d0700704414076550b00c1c0740030000c002407141e9404511240c002040218401c46560000d08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 244615566 1250 244614316 244614353
    0xc26250507140601031205070512070602090f040e100b01020a0602030708091612020f0d06050c03090c0a0e04081e0301080304180b01020a030e0a031505090712110613080a 75
    0x8840d46642c00300340760f07140428080038009410f0b000a0781642c074481e40c003c0c04580c0c821815102c03075a8402401600c20780100c00304840e00b42e004a985142428035100503140044200c5041c0034010800e0506030f11400b0045018503140d884115942903a4000c00078104201c1d8000400c640c0d03460030603801000c42900351005281d40c05601164290111100411000d84401d20000060b2204981c02c00c44403007c80180d158010b407442d640c40e030105080744603062007040250b1000e5603a00d0120440c50801150110175407099110450601c8403480c003441d602d910640c00b41c0541c1c2c1d1418615403100080c1d000c2007002c0504200000085403001020000e0700c12104407085451071014480440d81c281d80c00e14510f1801030384400b03a9000032078803600c00311603031200c00360001070300741c0d100e889441c0b8035009070141504041d110410304c500d0940030004000103001c01050154148003176583caa251285c807004031882140003284c1080e011179202c101c2e80003003c0c1041114080081440d08480e400c02c00543d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 244616816 1250 244615566 244615583
    0x90c03040308091f021b150415060b2508030106030e070501090810090323030f0a02040506070f05072103020607140d11041a07060c26250507 62
    0x2111201c00103681c1c4198100070410b0744d00d400f80d986501009400c102441040f110100c05003a42c80e90040c0400a0288544428a8003600d402d0408501182c14040c855482d149031103010401e070700800c000c0c2e4015101050840c411080d444100d401c0b42440c29502400403d800800044c0d8540c06078800301450f6042026180000c0d035a00065030302d40002e10844486410501c0c010900c090580c0c0700001241c0300c0e00b0540284004523034a80c0700303103010300c6101410800000034002c084100082c0e40741e0000c1150030a500d41402c0c1000300d142130140400c000c0c000300c400d0300440c0802030103100394806003010622010f00300140d240c206803203498122064000d80906404144802e01c00e4065810171980c0240952410340c1d040c40d000003c02980c4041c81c6900f2060002091501450714801105074040140a4490402c1c0c01c0000c112902c0340404018042c0c50010712140906d81802d0b88004c0c1e014807a0441207039511540f80d0010860003203080003a1880d114031490700b58000018210960148500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 244618066 1250 244616816 244616821
    0x23070320180f070806100e0109150e03010f09020a030b04080405040207030f11070303080601050a021609021c02030f0a09061506050a030c03060e040605040c080f0d080705090f0f04020702090c03040308 88
    0x141c031441e0080d145d4a03000034541c081038204901450030900a00e9046c580b05080c0c51784c9400782c11a580080061200140c04c0400707851551500340650000d046880c0d104003c041140e40c0000e01c10076441c0f01c01029294281c0005d0240541c0609450090001500656485400d450010000f2085108031700104054207003000c000c0e1b50026609090ba40d00d130701c905016464010040d941900556402c00c21440303180d00301c110030766a0f03452200051114210250715850900302012400006c2e0344c048155130303c1031080156036203403080400d42100c002000044e4604160601c100034180c51542d0320340c43c2d0030b4840e0024100e940100200118a0180e0b0100b00381c584808044080e281c1510801e00e00c4500d100c0420045082c640c00705420a11a0303d5020306960344029160038035804005400c17054002d03a0703010321841d810400103a80080503203881e514001029000821428101a025000b20004415544a500c0da54121259185c006222510603d0402810a060f500c200d50440025240901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 244619316 1250 244618066 244618081
    0x30201090606140a05011209020d140f0d020d080402010507050105100608010515090f0d0c06050a030c050c030d0b030c041103061302040305120306210a23070320180f 73
    0x403d00318840080200661625020044034103040400040c52115900e04108c0010b954001e0210f0700756109120a19682e2010500181030111644150015030018071441d42400c0d40810011407158203400d20842ca0748803800100e07032900545000905039803030700c418020010151341c0d4400442d80c4a540d201820703030701c6206200c034241440096800440d001d0114010a00d0440906588000080e01f07003511807580382c8801e00985055400031000c01c10000c0e07020081d952502408560036010300301145403074010420a90707244034200c204000300350307110440320640d078041c0014030315100d00900074082080040f00705001a4402e44103648145100c8803420b01291080c000e580899400c2030140012014a014003441c642c4001e142e56407004070036175603d41040c1d50032500d116003c102401445010007501e40440400743c02d01c401c00b00013481a040c1c0c4144d400c00030781030741642c0c1d0052004800513540c8038181243ea409480b03541d8810790503000c00b915204004140c510441480e840380416455241 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 244620566 1250 244619316 244619339
    0x40e07031d0c100c021f0507030f020102130e1306050108010b0109050d030509130605130506030d0e06030a090302120f1330030c0f0302010509070b040806040b1909030201090606 78
    0x9240d50b4002100c21014000c180c000c00001c4e04d258000b80400640080011b00142c800300001102c001080011074050f00b07240d441805a4800900342c00210701d8081000660100c1503c107100300000d40582400080c14400000c2040b40b003268001020301031940c52348040340c080c20410a0032400520380301400107440c0f401114410145415440e0545001207020511104d441052320031180e55444034800101905c800c1c0034207030705103424a400545800c102040600b0411030022002c100014003e0400302c5654800460350041000750000036148079070329042e800c0c200e14441c400320f41c02000c039200090b28400070051030003103108030301800401c2e19508410962a14884d203829848041204a01101000034412205d00d019007040c90900a80d503461025800c1d40c03410480041c0d45500c1408200d4204201340c1020b07282c511a180d080a04041d0540e60754172004002800c4207e400e0085180d0b41845200b078030202d407074a00c084c040c003059414068080e0021000c1103441c41e2070170800107090401003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 244621816 1250 244620566 244620583
    0x6140306010e0a0203090703052a060c100209240706050106021605040902040e061503011b0e04051f03050a11040209133204060e15160203040e07031d 66
    0x9958510b261502002c030301c000e40009104c180d03240704980700840858401c0202844410b01c041105ca00c404010b02c0700b84410849949541c014882402002031005012030b0b200e850342410040142c1711102400011007012040d107802c500d03482226289038005290400609441d401000184101d07643e03003104903075818005000380f011100d4200b05005924140d04040c0f1360302c1c001040480c92041074899242000b205a41d10780301c0c05807681299030030341000c3c040c42d00c20608410b04101000304000024000352003103141c00d4070a9a5070b200082d01c6036440003e0a00d80c82105003003c8401741c991a200d40d03030b044000b506171503c0d07450117071a2209151038001c40e4400c900240a9a101800c104000c002501c01c9400024240c2076030212421105034200342c411717048145001d070f480c940c20319081640864031801001d4550307812204c44050740b000120400394101c2c04020340108441c0c8000710882c1035004507000209440b40030024401610b6264004140071002c0252019440c80140c10855448081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 244623066 1250 244621816 244621829
    0x31b0906120a1d1507260705120f15030601080705041107060903080711060606070204020304050708031c110315060d0207051606033e0f072a030f0f0f0b07030614030601 74
    0x1c00001240e81d02c0054181f40c00c001e4a082c0303103041201451001080810860710082c0b9074100b2820400d180c0d1031120400c0c0c681900360060300d82941408491502ca00e224018540502c0c2c0750b11a254481c804441150800d50304480704010203121440c005012080c15921107002a5603c20901104a00407404900031400103000b07a01d0160507a081c800a5080104191990b025840d00059050b6081c0010001c0d9403e030b514540c001c0c0220000f000c00c581d11821503089090b17081c000c1155030300d0304281941503c1011175080e03846103a41d84405029210f80d82c401441d9004401e5070045101125008006803291a101403060900c12004900d010040e0030801e00002001c441005424202c241c03901c180c5841d80414600d4402044c00c82d40e502c1d80a10310403507040c004003458031a80942900c0c003c2d4051410b1860402062654558075508588940e02030100d10118400d4810410b917140c46103a003a9100d0700d009414034000e480500141054414040c5103900c3c0c100c140071034070380400da0f94142d985 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 244624316 1250 244623066 244623107
    0x50a15020c0a03030c0203070f0c17010203010e010302310b12010207110402030604060e0112050601080a050a02060a0e0d0c0503010b0d0c0e1f030503031b0906120a1d1507 75
    0x81c2e924201e000d001d00c015030000b0340c0420050080400c0b017081c1c1c0d40390414002c0d14a501601d00d40919504448242800c00f8216481800184126202840b00341d04581e01100c9550801030085511400f0746924550f0440400002009030001e0300b20350024214948129480c031012216000b00342d091b0720411f03a0041849c6002d0056000c2464161702031508070300040c00001e070f4180ca801d02800540400e8104c0071f901005139150304c0401808000d05409026840040c103612040c3e0754459070b41d071a4200000744900004560602c40341c0c071501e00241d8074200100229103048650510303009031846402068041e500705017246c500350400f0103140c24420340c8046246c2e4114640f2090004052015008045031404001f0059000000f02c10110145008001441e500d00384604a44640e5071040c0c0c8442c00303284107019502a40e9100020b80305988075541d00540c0d01d03694244c4050017400314614031250003800300342101801e4400110602c0010300b141e4005505d46500b1416a4640b5210b030340707442e20b1038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 244625566 1250 244624316 244624333
    0x3020d03110f0d0c0c061137060905010c020102031b090a051503180d0504171c030f06050901030209060d050307020d0303052a041a040909050a15020c 66
    0x284203204084080d01c000c030079103544140c06030300203041585040c00e2000045100e9985420f000c03812021100501c0241032034554990840c103110380741c0300c01c070a4102d90040d06180f204011700386141080050550030030001030740d000a00e00320005003540d06003036a60f1741ca00b41c1101807040c01442228003c1611104510060403202100845035000c2e100b41500000d10702d800084544840c520403818040c80440a52280f074100144035580d4605196000294031500404c0d10154000040f5000c0e0f9000b41080d288048a140c2d1042c942a8030702890b40e00884408488007045a00d6801200030384601081400303c540d45504010f074810080c04040c1d40110b1100201e111840c2c812800500c4511640c20380781800042d4002038541c10306002d0035004031361031b00e04020020780d03603d0100080d90412246400524401c0c800b210950003a030048080f4a040840183c0311280c090044d50010a0381d0032092245882d1480c295841c1c0155076004c0b1618a005880110128014026548078412b00d900414080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 244626816 1250 244625566 244625573
    0x1e0f08010506130504020f0702030d0503010b090603040f02030a2004020f0a110709180b0604020a230f04090b0108010f2103050c160e0c040302012f15010501020c040603020d 76
    0x40d80140000035401c1030140c030001c4e1944031800504070b00c0b00c1420003d51150402c3c01450700300340c2601c40314820040c00b0801482500105000c3e00d000002c282e4515443e035645280102140c404041c000c1d61500c00c101c80c80040092942072048414480c1100c58000a03c000c14001603010340b000790485201c0500c04a658144120800d101c40c0c100001268441da9840036450125600b04010540d040c0500e07034a1410310682c0410107802a0b4207582c00c5180492092004000c02078581c828810083d22000c0c042104c031072001a60503003501c24000594176583c6070810001401041d000c40c0c00720340310300000a5100d80d007644003000c4444021041c1551000183c180c0302050029804805010f4144008619020300b001400c0300c010303200c185146902d043c8550071003907020007007806491100410082c40141d9120100b071460b021401d44403202c0f10340f4260802c0180c00422007116151040040e09107040d00b0350040745040310004c0c0c0944103050161803d103c2038551034000650420380c10110039000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 244628066 1250 244626816 244626829
    0x6040b0d020609040908040f08010f0b06040b0d0509030912030912150a0209030102040306020a030203072705010e030a0605041a06240901090816090b06032707080604031e0f080105 79
    0x1817501c02c40d0355038580b90322021440c13111052a00300e00310704c1c2e41d1000021001e11481c8916440b1719400c440e00b9082ca450010b03d05000d2080a14016485899a0119000343c0d82001a00d48646c0001c0c600081484d0111a040d5a03800006480d23104101a0014034a403107400b198000000b003208506440503a00c15140c0000396002e4892950199800c1000202103a000d1024020099455030050380e030b130400d003000034100c6078285c0d90042c61002102030400902c0a243c500f0341104c01c00e00340101510040d000090030501c64000c05050b580c10003081004000c6101c4001101c00c2100b50300001980b02c043c148001c0039142e0f03801c400000910203491981c044c81c0405494550814541020103544425050b4141210a134001c00c5856000c0001c2c00b036008035000f280000d99041c3e03441401c0d464000320520f5161a000e03546402484c0d00410b01459520520000010348074850483e1000d0800f8600100750602e80d80340420f07504441e44006880e14030a880c542c0440d24540e84605059003002c041160 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 244629316 1250 244628066 244628081
    0xf0b1807080411090a1b140d0905150901150605130e0402030a1505070e030a0b01031b03060504030504051e0d0b1017011d06011203030b04111206040b0d02060904 71
    0xc0f00040b400b0f1851095a54100b158864400004d000c548006031481c6d041900020251400c14042c0e104408150000341710705480802c80200c001003246103040c00c06030708003a0b244000400e6541c1510420140381030540298010f8401c0e1041071207103541c0c1c0c4c0c00071103090040b0a00024050070b441d50401c19442103c200356041030004003a500c54042e01d80d25034015101c001c002c90501921030f8100a842c1c1c0d0450140180c1d20820f5010b8502803c0c50b58800000c0b41e014000200a80b407100407842c1c3c134100303600c6540701031a808402005541000c2c180902507811511071399100e4a0300c8481003585003241c01c18884070302406000c030b10b10b00005aa607085101c80c0200f501e90f11000c0c3c118000b03200b503e40030b90324183c0907140b4000600309003403448820901512400c0006558000d4004020717101d90360443c019070030340510f40010611790b020002006851444440c42d6852004902003140e00700d4030b021240104002c0320204145a004e000f885191400140040c1d8045000e00c500012030074030b504643d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 244630566 1250 244629316 244629323
    0x5032b0f05030423010e07061b0317070306150206060405070e09130809040f1a0402040e13050a0803150117010515071e05060106030509070e01030303020d0f050a0f0b18070804 77
    0x20803002d40d100300e403821105086c039218041d0b40311401c20003030b054206644081e19040c222066900d540310b5200a482c461101c911804038003503180010300b41500c00c1d40044043c010300c9103141111081204000d50300e000c2540c03907900c030f103103003001107800140209403481020b00701801c03a44d040c0d982c454850a0f02c40c0764150980b02e400d8100644c900946d15480b0744d03109011800300019401041600c2102c1c0410703544606409544104018440d119840031826480350b451080c2100c0300c182481d0441c20f09072441c10040013a0404001e1100420500722000d41082d4285da80001da40310700005406101020f02c900364201d00c002041a028000f0340c0c1c01810020301401c1d246031b022411301e80c108502c044421080e2007580020006101d016070601034160052101e0004180080c108400d03050034440600c801024150300042c8641c0059a80d00404080c81505000700843e00d04881d02c1c8015255040700029224641a0144558076040d044030415441e4680b00b12610b0751402016a418034010704183c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 244631816 1250 244630566 244630613
    0x210141506070303200a02060a05062d0a0603050106110a0305040b090f0a080601170a050d0509031f05070e0d08040e1909081801020f121305032b0f050304 68
    0x1401000505100d010390010481704142e4800302104d0082c10604060116100340d800e2000b4018036036603558401c441c03210300c40652081914680d2003034034031020f0019580c1e048450408001621b940540c0801d040341c42c151100304080e48900d030860388843c070b031400040c086182804244001010755014102e062030290610300004d860100040143e2044c0d40074070003d5201c3c2e0014041140038007040007144c9985002400824071694800703484010403a80c10041050219840c190366900b0030400c0c20b869640d000c5e46e103100741c0c00c21074240a098112600340210704d0030a015000307030a1100521000e0b0b40c0280354282020309001c4a0304040c0d0002c0c0c1551000120400004d80003c030038854070700050301c601c1e640c5686440c90704601258000ea20583c0c0d040d034218081002c42c031740d0b020a5940320001c0010030305549401e02d510001c0440210b81245426108050b5044041d2982180c098148100c45200d402160a45901121118540100000002d000384082800250300c0503180d0181d4a181c07022 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 244633066 1250 244631816 244631831
    0xa081b040f0b0c19050705011d0418020a0b1218070302060408070f0906080a0b06032a0306010902030709060c03030207020402030c03040c0b0405031509010b09070210141506070303 79
    0xd07100d9100d999040529000070004180100c00010410001420506070501d5442111600d5158441070350703209481c1880031300c840303041403d17140b071443d400301c940024000c06c1250b5122418040100040e0812070145104030f60214240109800b6940b25400c07080100500b0754520036044020680f00d2901541031003030300404030051362182d000d4805061750314010b0521502d0105c1a000303403060b03030384000d54292034002c0c10310450801041e80054541c204d5280c8040d6107814002c2071a01000250b10070360070002d40b551001c8026000e0b121001141308508036034480c0d884481940c203e10054500c00013240c011101040058014008003d945000c6c0c20018181619034000c1000e980c070885845c901598000200800c0146c3e1003800406002c4c072018a43c10075080c40301007685c030000c10f04940d007040010800103001020941000c082000b019080003804d00740f00c00003075902c060000340d800841307090010070b0b101210380da80704910604071060f02007a0044a42e0900c040b07580554410f0b400c140d103a152 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 244634316 1250 244633066 244633079
    0x9080d0905031c090c030615030c0603021e091011101107030314040302061b0702030a030201020304051903140a0e150c0705041a04020f0403060e060115050a081b04 72
    0x40c02000380e016201856540800320394a854040003092240c1c07220f4640103a080c0071807000c0040d9400e40e44e1180c000503d500707040380c0e010407040355907000030b00000e000c40d404903265a0680290290f2501015100059040000301000501441900540002d0301d00000d0350810302c00c0700c46040d43c2c458102a9244c0340c0c0c08009030002c1c0d401c00e810100c01c0010014241081560602c038000700a504115022010709041d07070025207460f4003928080103103c1804448210000d40780c01c960410b540201182c81c0e92203d442d001e4080e40044609940d28010303107440038034131003090300c0c6548029810764130740c3c81c5a1440000b15a898211801c03480c104500061540c02540350b5106000741180015000d54030b550208808a1610380540c1209000b1810480322040040c00810000c800e200c0031140961650f030007055201e030794000d6a101511042c10300703241c0c2c0e81c410408141541a1448108030041e0103d012030300350ba151040d074100b1000600740f48009450112584081038200210703002c00340c5001d583c0e45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 244635566 1250 244634316 244634321
    0x70305120103060902100206101413020309011a0a0f09051003060911030609120906070206160317130506150a1a04080d030e030703080603100e2410030609080d 70
    0x200200c48441d0380e1101c3d103056251019004007104083e01c01401c0a107412140e27803007410080c1c450b0b4201c00c0840700d0f081805070b4403004034052959004004646924150400714060300403000c030400c0c0071004d10407c00071400c1944020040d2403912000c0c140403890001c41c400107000040c00c8584a580c200070101c000b42d05409107002c2240100b20345006c1088140400d400c018001e00800c0d020343c03101091909400201d0180c88a02d28222a02e0b0749171001070001c11400e10501c2c1810700452002c05056040541040e030392207864110744003242803583c40c015452020b5200b0390b0054155070101c0c0016490852102c541c84504001070a580b12072030307446c103022101c200e0b03aa448031041880410203100c00d200800c080915403000c0e2034103029840400f03d10795168446c8400190421190000141541e1000c120310310000100c044104194020700d0062500c40d41c0d46294158a1000740103004a185c484480c010f005050360090a02c80300e01d155640780040180f038400312030000e0f0a020803100e1400b80d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 244636816 1250 244635566 244635569
    0x60103090b010315050906160507061416020708030406050d0e10050a0b0111060103080405240a051902010b0a0b07110d0c03020901060212040e0a0f0f0b040b04060510050703051201 79
    0x40003800303095a0010030403411785000a00c400c840d644030300c04104d5420200111405021058180243e440c0ca00d410003601030b0a00c40795000c0b50315100b4003400006000c181441c1d0326450b559003900d818585070014151244140d202c0d0100045c2e080c060000195400c0e4403414004903201700311180903010b510040140c810445071085440d5490407211841d5800040e41d001c40c1c00c1440181c101d96055a079084500d0240e80201c84c000d00501904109401d44009515080313003c0000940d144d2800c46402421380d07100701d01c0c601c6a1552241c100c1c10090050154422400d801801001342604020400c89a83c11140050f00c1c540502980083c0580390440684501409160f41c00c07400b50070344c014019050f4040c0e00940455101c6481e640d690411423064405503903114ac074852044d1904521070028205040e408100146404005550f05000741d203c11900001660240644c1c00d4610800c021100c691103481d80115214420410342c43c0b24200900c3c95611034102607040610b0320b0320f805441c1809 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 244638066 1250 244636816 244636823
    0x6050d0203061f052104020d080a050c0a0c03021003050f0a02091507112b020d02010905220e0f0a0204020a0306030c080303190c020d03050711030f09090601021c0503060103090b0103 80
    0x4113103021480d80b1a500f81548154405c0c2061410651701095449001103406400d00784c000c034032030380010b04c9002120715290340c1030221036041029080036520780c41d44e484220f101e2061810028800c0e0301030b0240e0f9201d600c03000f001380e41944d0343d47c003004080c0d4011007120b54081411440307441d0300c0203000050014103010320400980a00101c05201c45004503c880052021607600b401c40700119200140114503810344c0c544805810920050303601759070b66008558000d440741000c01198a1410644c0e1107000c041c0001c0c0314030b100041380586c4920651420189070341010307681e4000f60602e40c000f0011141d40780f0340003411a03500d0b15648651066074200300c4a6810000070701283c400000722180b1901c100da08208003101c070300600a0f5480c20600c00c48030505440d440040c0026000380c484040f1107000301e0640cac0d078400b85140890826407081056600c101c0601c400b1403074070751000980100e500700032554000d80b9654444d050f00c2d56040148801d04040d00c0d1b04400c0009004510703500d000314031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 244639316 1250 244638066 244638077
    0x6120d090503190c060e0f04020408240709050909031308070305070b09010804020418170c010e03030903030721090c15080c0d0f0f0e070e0a0606050d0203061f 70
    0x2050101810007400f241012000354184200310003040c0700f804000308444003420a440700040e03007400309041c100d18403005a401480403400060120020441d08002f03070804010401c0c135031059405a44420040d00c405000600c010720034072490a040310600e800c5650281203a0810492040440002d65607401c21342c159040030004004010080101c080a0100c000c0b21a061500c0c010000344100002040070380320355183d0b12903c215240085008068540040302c05920054455145000d6448491040150742c40d207018100c5030b03400403003900c0c013601c0618065455034903140700c11214610b440802c02c07041c050000109040d0903a41c803030a00c410740701d06103101c91a0728000c0e81051003113152a00030700f03010301c0c0000c010202c5034401c1150300e0140481000109690010001030050a11005c01b45409240c07c1104841d644001400011a80c800c072900505560b2162040d0640303195104400c00b082050243c1444045650050f41e80500050011440d46035000500030f51081884000008242d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 244640566 1250 244639316 244639319
    0x8120408090909060105010509010509180c180a030203100914030a020d0806030309010c140c150903010b030f0c1507150606032708070201031d0114180a0b06120d09 72
    0x602c1c1d024194440610300240a5644c904800a0170038420440784078100034000071408440c2d6101040b6071b640d1280c058062600f0303d429105440c2e0b80c1c2c0501c680451078002d1602c80c403210302d007034440c51003602c0d8080c000d0421491002c0e001350182401c80b40444680050840500d400c3c44104090000152a0303801400800001c05004d802000c0240c0710074041e4004001078101c60360000a1000d03000d0303000c444410550040000303141810a0306142c254020140c4050145441c9070501514200c0d400301c0080240d00070799020195202070149a1049503007043c034446021749000e100290b07204441c916124500380c0350780d0f03030040c40003008680b680c0815501e641c1401141e601d403040c1c0c14100c000c0c4103841d414240c0701e070a0010320301c04410000c01c0c1500001d40f05046921907008445416030f2100540c1c0840300e042e6000340a0422098a4400300703a0180c0001c0c00c92403107103100f4003004000c6010f065034120903290800b45c00c40080c91541c110310071307815400f0701100800c030120050030590f9801342c416 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 244641816 1250 244640566 244640569
    0x12050a150b011803120f110f030c070e0402151e030a09050105011401020337020d030f0603110607050f19030206100b2b09031d0a0f050d0812040809 65
    0x680c0040c24056002c140c6009100081c5c0200d2504103903072090821411120303841004480c0c5180c0301303000c0b44080c05480f00000d052a0008064a03400c1049004c1d41c038800d48548441e032165900710340103035211b6103100c03540603122164402401d9503158403f0301b1701031801c03600601c0901c0d441a111103100c1685c440760601402030078418217014007070250448251110450000b50b90303005000e801c04500e22803903012400c980c842465586800c2c02046140c1d02442c441d4800780d00d550782c4003440d402083c1040311149580c803480c81181c0507260302400d55281c034015101840016081444212181c0c03050300785004480a04006400c0b44070900350b11009400c08500e4001c1c1441d9010f031843c04a06003141042c0301030b1a2005c1a03c15641a4860300300c203210500500c80c0c0d10002c4082d984262501d08401c16061540c1300c00f103805250300050b88440100c400009203da4208544940c4000000c0d000007440540303092140414864010284036003004909050303080000015138040b1840c42c070001c7c0008a5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 244643066 1250 244641816 244641827
    0x6101b08040f051002011103070f02010605090a060303021c0215060f040509030c07050909060a0522030f030b103e0c030c0105120115090312020f1207020a12050a150b01 74
    0x10141ca1700c02403017002251901500940006406541031200500ca5032410600c04d5001e0b1000788802032140030355090510344070b801001d840c0416401070103084003802c198200c00076000c1d50f10310180e00400c04480289c25200c0f500e04003806031903104100000e40c2c0741541e40c1d80101805041c504010b95641d10b1030400441c54204681d020038002c0030000100031230480040390181d0700c00f40111010134955280c940b1441011903091a00e51040c07800c003207507403d0640c404403eaa0314019901d04110710103400041020204960404200041d00704001c0e6101c545108011981c884881840d0765040d41081c80805032081d4407104c01d00e036607012810038a140c1c5001c110000134103a007820041d144c80c922068502e003000050040554104604a1071008588164010802150411420702588081050007900e9150500c120482271080308409151040d00c08100ca505680c000c01d0b0314000d40c5046525001c0b400c2101c0296014018078004d60045100207000b035516004000d400610b100955001406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 244644316 1250 244643066 244643089
    0xe0405010b04150302090a050c0909161706030a030f0216081f0204180c120c0f1701080c0112020d02030405030d050a05100308070606050a060c050105090606101b08040f05 75
    0x82c0104000820141e10b40b103003000d81002c1070b0b00010400f541d48003a920014842e000c1601e07004401c0c141040002c0f911040e2412440c0d840d537a0f20000c5080c01e041d02c1c0d412003c00e0b208564150002c0340000700090160141401251441c0151096800216191300c0407810b6581710003090b401c00a003000c5440400d0740d0860055000e4803045041500b8001e0103421a190300c9450700e42269110110803c9034000c030a80b1b50301d0000010140310252007142c0080021001d18544c501040c241c5150b007410358a0f4006260503a40c0d400010312207007020400448038030400321060480c540c1e081040c45111078150005610840c002c0006555030190010384400f285c10042c0590000c03860041071181c0c924284000508507900f1082654542110b420440000e1106920007503000002a100140b015004407801a416000b48000c02c46503403950301e2240c90b044101c4800c0d501100300c030100002507014081d82000014650484600d4038415035580c05c5070b61003500100c0d00e1400d60501008140780882e8100c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 244645566 1250 244644316 244644341
    0x305060a02180d1713092a0c050303061011010504050d080702010c05030105090a0b0d150c09051809100c0201050a0e0115051c08030f04020a0608070e06070c0e0405010b04 75
    0x1125031030741c0c58080f4075224000b442481e00c14005022810400c80d0b01d200720245c40706c00820044060114240b003407072002044100b0b80881c2c4032038100c019070700440180768a1074124005c5c0d440c42e915402042409801c41c04080c00707200e101c518544c02101c091050602c2203205000a0444041506d805003610030028240c03021681030010501c485540001a04c0c111340c4103581a441d541ca0b5a03000c4809010070018260b0084500720031407042c852804c03180a0b402d80c0e8184108003907441d5060445540c402c1d4001c0f40d4200c2c2161031500300792003461202c4c0303611105040940b0b0070b1030380469500301620310042d60038005039114424048051500d120b040150030070600200300c0402c030f41050310340c0c1c01c00c0d0f845218840d0010f1050300b40c60310041d22007031807441e13400408c082e507a2402540205d2142c03010f80742680511004030001c9801d9008029450040130161102d06c60203905000300300103588203080466480d00b0340701d400504a41004003640c00340d8810b50012511150100600040340d030301c940d011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 244646816 1250 244645566 244645579
    0x1410031106030702070603020d090210020706120b0d0b1b1306020c0406180b121f060506040f031104091a0612010203100506160807030c0c1a0a050a02070305060a0218 73
    0x410f82640000b0803038211100b40c240580c41d0010f916010b0024421a1400f135000b01415125008695004c2081c40a91b4516141c4021a401c001115000c507401d0312803a40d000000c00200b040458110242607900c0b6800502c044c2c030992100580c1758058120080104041d0170440040c0b20b0160144450181007206076810400310385800c540c00c08028102d04d0410038203a4030f801c0c1c0b400c0c0c1d4076003d8515a800c6031540072101100c1031104111080b2000c00b141300201d034500500840c039440c0039001ca40c01c407441c2c2503144010341e00707684448602000c898100766025a03140000c0001450a04143c03101100d65081c4021628002c4140070756500481000e80d0a0703441001000810186401b00000b9946d054079007584890540d54580c0d9501c0d003c0c00c01409049000c02d92608050b4040140e000c200c0c8a1180c200c91581d075419010f07052400340301e9000b00c409003888101c000d103200d13001510040c4818411101ca06075241c640d0740c101b080944140c0007c50300084c8450310851041c58184150078181e41c907 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 244648066 1250 244646816 244646821
    0x6020102030709150e06030c0c0f07080d0f03021201170f010b010f0f0512150112020c030405011d0a0803030a060e0105030c0121020a2312061201141003110603 70
    0xc00b031210f24064a0b6400d0449584031031003c0c40380300313070228a01001c0c003010b980b400d111150a1240d04014034294903440b0340350480300e40004c080703006400c94460304000d10600391041304c240ea010341300c04048400c00d03a00384514281800700c030b0031043c02810b40d5801c611440c01c114590380c1c1060550340444100340c0c1010030030031940e640907800400100441c81d20341403a0b400c82000311a0342c8108058580c0c0441c0e0201408000780483d031580b1515142600d4240700f40a4500c0e450040c1e0046c0341c0020483d41081c00100f10302c0d40140c610107081c0d154201c0d408001c2000e880011101c1c10700350031840040e4004410807404903110700c2400c000c0c25000c10001d40c01d61621002030380d586201c079030050401445450002c1601c0c00310012521030110000b0954a9141c9404020300081f07403490000282e0841c100d41089164041c0c00700d52880c1c0600d41d0a4145540e1141444039244030303d0740c0f0581c03d659a0007600880c00c211403c05015044002d9100c0029195003011102341199003d594070400c002c009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 244649316 1250 244648066 244648081
    0x2d22060512060105180310060617010315050c04030605041b050f030c1c0c0b120a110d1509020d02120a02030915270d0906050f0711031207120305010602010203 70
    0x741254091403d203042075440400711a80320003d444200410382511600780c2c582140c095681160050714440d503142c01d1200051802000300d00c03420304c40603007900144008080e00c00c00303a030000d03036200ba14030100d14501956079690300304546044806582c20032204014511b91000b802503000200320841740c0750aa1540540043e031602c2e0b048102d5881040d40c07490284145102d05080301aa640084c014882140d6815010000c1d80c4441040341300d81c031840380081c02c00d500922444001c4120607001d01e080c5503406c0c034444001d0a0315980300041380d502000008a07804240014030450403104400340c0c503061440110061040c1c0603111116141c010b004000c1d00810014411409002c1c0d6065100c0d16250007208040002c00e001e8001400c03108941740c10410b0000050048224510b84d407a6040240e036640300316264058007892000c41203040002c00089415000f50141c01d1400405031803640010140d848407503070001c001242c4198459210b01070b4542c2620031a4014422030009502d035185c24103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 244650566 1250 244649316 244649347
    0x302181501500a0f050a0f050a020f031c060801021e0706020c010f02180306060307060c0501150603060f0e1b07030203091008011403030403082d220605 67
    0x100c00e40982600401050081c0c030031800340b5205000290b9100c611440100264401c036030000103e044003c002c000c1d948100100c4074500c00c1907407465004ca0f0140d000710780c3e981c00101c0100451141038500845c2c88820b00040890300410111501420b4a485444040e40c00c5c40d03002101d00d9105000c99040e0030320301907102a00c01d000c54003903035644100b80703812002402038603d087d4440d864412030717100401d045d03402455003c01e4140034024442d12082015aa04001c440b0a509900000003c201b151701501034030300500c2c0303d04008100c1c1c4104010751088000603074007950000307444880c00c0040e043c0441d51500904003500070a0180c0c54075454041d00c105181015800140d030016180050601c2032041e00c8200000800c0310b0b0050b241250020509182070190000300000c00c5103005080c540002141c04a950010b5942d0801c0e101500e014203046c0f0401000c964200d042d00101001c1000600510030401c00d500100c89800980c4620204c2c0705503138002c10b05006041104400c40a083c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 244651816 1250 244650566 244650617
    0x80301060e01090e0f07030506041e0b010509120303010614040828050109030809010b01020c030a06050901091a0f0a090f1209180501030b0c030403050d11040302181501 74
    0x14103040d2101c001c0c460040702d050750542c0c41041c01100100600a41000c1001100c0c010710403941c003400780340c90740010441110101c0c0302d03500c05243c0060010140042070f80040014420504280382040080c4004ca1803400c0161713600c04040d0000401408425000403408000326440f4444504050800d8000341d0340c1c1e0703a00d2184011854010304c0300c07800043d24100071400c6c030741d000c0e000307200e544110b2401800c48501500d40b00c84650074141318080a51002884c80d2070304100900030810303115252906001424003510404065480d00b84070b5000c50b003021341540540752800c690b03c0c21854041a1200003020152803071006508156015000c660403200c841282608808110494600040d0655000d03405a00a09141110079000100000300e03a0005049038012601c2a40c00e030780781c5840030002c0c441241c004000c610140f003100b1b5414015440744d241e01c4540801c3e03d103455241e0b0009034410081032124410801c01b04104582c0246422280c0712a06007030a1103400c01750410038500b0b0743c803070f00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 244653066 1250 244651816 244651829
    0x90c0e0a150e0402060d0e0102030601021c020c0918010507021014060f060310050a0902040602061302180a021e04141002031b100204060503010f06080c0a03020d020c07080705100507080301 83
    0x30b2001c1800e541c2c92400b1600b02201418041100d01c001c030f0b010354040c0d04111503403070240c02003511505a18150704481100f5003040d5020f403411201d44020400d00303403006441c41c240100d4905207030001c80001d206060180080d500208104594038001034241e455600b030480420a2810034481e0548846507250505241110030644a603030304100100c8840895000e40c6c1d00c40980d0100280c5410356078000d00075521030f54281c407603651f54040e40540e10b08000d00002d4001c0000003e58800750003a8443ca0313003103404038502600d8041c0c1c1d1800c0105404000343d81002842001604010105c500c2560031300d8403034280c5014a01954581001e0340364052080405565078a0a4000c035140009026000e1960a1074800719102d81d01c40f42c00600340d0700f0901a84045071000c28000c10700302c0c000c1640074411450b141c400340c03a001f640c500450180d0840c0d2a04040d040c3c00b44a902d201180c01d000070005001000014200d080c03616040118240c10402520188641040182e0200d81d0080440b0f054503503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 244654316 1250 244653066 244653089
    0x503070303050402031c0906020d020102041a09061303060605090a140412030905070909030206010e040f080a0c0b0a15090903120b0f060307020304051f08150f0301090c0e0a15 77
    0x83d40d0010a08008040646050364101303417a00204207034204041109854071035084410107000c450041e401c0340300e14058040080000895441004122001420801000f13400a428960100011069407400790000c07245a51103400c11321403400c11203101c0d45c0c001d41c07900301400032500060105820107009003015090074041038640e01c0d09130007034000303c8815074408c0071584131030b5446c55148020444018200d0060040a0001a48000c0103030164041c2e81c100c00345120790f040c50398a0540d80d80c410000320003441801e038105008183c0101c245880b6003403030000400c1c0300084100820002400d030f0003c54002c0d24100041000c2a441200c004010075000000103404d51500d002a180301010303c54140d002038004104881e59034080044d1003140d038140e4600c0c003504046510f0490a22417840d401c000109103030005114201c60300340c40300b862040a00560701c80c040032800300342960030b00340040d114002d294a0810114032048071099201022280802c8804003c0a60030760122003446100340200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 244655566 1250 244654316 244654321
    0x608100608151315110f0d0c020f060705030411040507030e0c0105030c0d0b1c14010b030c090f0a06050619090e010803030708090c0a2403110405100e03010c050421050307030305 78
    0x440c4d65009144116074900383c591034003a070070083e105640c00020200300715401c000d84c0ca6211400019050070301e01e01f4002524165841a408032556003004005541259142c0d40511031510b0f1880761b00e01841c504da070049516083c000101d450214100f81d0740d4104031042081003501603480b0151044100f020b44040b40b001644c074005800c00c00b490105008059030744640c07508000341c41c0100b0008591000003803248044150400d5181c803246048140c02011101c0002d0119070b020013443c3e4070084800e00041d02c69210b07070100c2d0030307a000002003a03d00d11a0050b110001c40d002005407004042d5040c46602d51b60520821540f40c0c0030203800d89044c0110500800c1e2141014050a445480041d080f007058954500034840c141c0302071000e071200c5891003d034140e1071074824010200c80303140001c2c82901c3d05140c1420b01250303d176402d80040410002c008900d503da502809004080030003943d4050301d40741004461414400300b036410300d0032810035418940000340080142c0f51010b406090014082d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 244656816 1250 244655566 244655603
    0x2100e1807180f060c05150f06030f0102040302090703050a090f060e070902030c09040e19060902090a0b09040311120408061501170c030a091e0506100311120106081006081513 77
    0x1d001600d264400000040258a6001042389441400101c00b107035050000c0710191401c034499030002940140086001414123030281e04503681280c8040e000060034003940d1a07492070102624001c0f100b1b66241c14424000042c00c1000001034001d1880842c81e504000c0214001c6214403000d09010340d4441140c43c00988043c41070080c08150a00221510032030b506d88000103165200c000ca104440f401c0224015203c54800d120300c00780080d003c5041611b454600742c40b07884580700f004019200701f40c5c0b44801040000b0140c0001c1c10080010801400c051288015045446010b613041002c00745210500140f040150741d0271021851001d6500d032504880d5002500c0400d0018140070b00c81c00440302502002d440182d051070044007a101e50ba200c0e41c04505c113503070031844050503c0c0d5503045007145519140c00050f2149610308000180e07640d8030040207050580c940d41110680707903030b5001082220424080010040e1300c55100c91558a028030440701c84002c1e4074070191003001612a0840740c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 244658066 1250 244656816 244656823
    0x2031606060506130911091c020f1c02040b0d020d0308070c02120a0308010e131103031623030310180b040203190f0501080a02100e1807180f060c05 65
    0x500406000c00380e441a50300c0030f0039502c141c5441005d0b41540b9041c1aa0754088130401030b20380c0024000c201d07401c403070369040311001700c29060303042642c0c444002800c2d003115566440140c1c2c40000c24034a50a110702c294010401285c085950250207050b052044000580c0d030700a04010702940340c24070520b581c80d0340310202c40d020700500c0003e4000c2c80c40c0000d01048600000c054142a11943d504d0300c1503030302c0c5c01d21005204015180070191500303840c00c01d0000780d032940c0b501607804c0d00501224142204141072015088104606640040504100350f01901c007045400c110102c1010003541365003401d0207103092a404511a15100421020380c0031070040c0e00d070b000903a89801c024402e6480341860380d0940585695600c540d00758a2800140800c0b2000e980280c50407034007031030040c05800e8010380910400043e403051f03aa00b0010309920030007550740d40d01c684074100d8401d800b00408910300058007070003554505038600e4026003c00c0e03041103000303c0c08011400ba102c80d0716200400c908940f410b01d18 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 244659316 1250 244658066 244658069
    0x109030c081e121906080318060f0301031214030c1204030c0605042f030c060703050c0601060504030311010506030c19330503010e07050f04080f0d09050109060203160606 75
    0x444400081e0401d28103100401141c0203190086441d552100745814131070840d1050710031440590028071070031050301c48288481d22810800390680c1d282a11600c1650003990003600111014601c2121403688654040340040c9010349141400345182010f2503403424038041d4219080c40c0c02148800102010f100b00140e20015500032424003040c01d00d807506403002402c898400b20000d45401006440c4503961300b6907902d04001501a0002c0301445051200e80c0d401042c05606024041040b08501c82d0100503140c000e08544d03075055159811031030014242c520a001c07094181e030420b424400c4a5602080751400c0c688200d4500000c83c083e04100050b40d0811341c84505034070100c02c9401c50b600001c21050741d01d03603d5104003044e00262040c041c0e800d80000e00410f180c200c4c0c10800150610700450003056440c0d0000302c01c90a1554401c8894601a90340300d164050f904240765100c0003581080940d17020b8102400c0404c036007410103000030355030300440b607402a840c52400b00f03031424031141d603001c1c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 244660566 1250 244659316 244659367
    0x2030601110a060e0d050a0909110c0a0c030204060e0124030b060703030504020f03030408033001080309090609061005070f0b0c07030f090e060f01140a0c020906030109030c08 77
    0xb0030181290a004000300b03400d40c44011540202410504594860b40c1180d40c01a03103500e4540c01c250600c00b892004140615001c001a00e003000095548042081882d1440348582d02c00c219090852040c401a103201d0340c0040d9080c26800e00600030001083c0d01c545600c00038820001c2e1140049100301e020300b80b20203031583c000400045000c189585600450301c910300984060301149005018540e581c8142d100c1c40c1d5054005100244c5c0c01102142d8854500e0444540054034504500304031010b250f080c2d00031039039a0300001d0313545854180000265400101104d58040b54a41000031036a4084003120003410010b0014016007000311500c40701c401e0342d810405070742c1580f034030086a0180c0e604c0150140c0c0820301e40480080d401c5e12446a000c00d8407042a442d501c5a100c40301800b401c090100401410b22400d008020380040800b00901500c849554401c0c904680c24014003003c8130780501036a0107641410811404240c01c54003ca46003a8016941a42c4098024120310038511607a01407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 244661816 1250 244660566 244660573
    0x20d030806010c0605130b0105191e150f18080c150c0102030720010e1c031407051903111e1312020406080a0c06050d0b040603120e030703080702040203060111 70
    0x403035000c1c1c034505c203c01911f1041070100a9a602e403410004171000c040c50403480f004c0c1c032070403e005120001d02c04502164107030000040c0c19495560a04001c202e800380c1000081d0240744544400c1d50110244c42c80d1032040c0586a0013074107201411761510720401c8054080e5800000c0e40090f40142d07801c4440c0010020021500d82c00c2c0b0300c100400d0101440200e15043c83d04880d01003610006224422045501030b006103da03005a81d0485d0f080340905c0408418940c3d01da50901c071995002c802a0f1064004e691419560154103c02e910030150019041c4105454800740b8211421281c00f2642c544866024814050051205000180c0300340d455007041d440e1004000241c120712500c007500141d00c211400c0c0310580d2514204c55540450ac603000e0180d04590508202140c02a00204580c4c6000d810109501c00c101c0041810380e51140e204540309410341100888c600d52104402401c181d04802a101c0945143c4840d4412300030540d001c0e2180d9400408074580d80e000c2c1c2e030041c00d5001c0003010b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 244663066 1250 244661816 244661821
    0x306090506010302091008063402060f070c0b0a020f0f07081c020903030304021009090c051c020310090c09090617011a0303160507030503191407020d030806010c0605 73
    0x303a038a60000384001c90058910502141d031881c450402034083e2420f1500504142d035600e056584d11402c5c4040a03145140034516007240340d0285084502c1d586210f030001e01c004c0c20302e090100b040e0f00300140104100404980744400042180c0f1030a90400300b640405038407000c3d000c2e0015aa80318003400d40e45900000104a01007016600c00b9141003503040c501c03820760801600c009010b074442c10070700a41c144c008000080c0180743c6051001100030651904014040d2a029804100c1d60764140d200007190000c00c1030040ca02040404140d88600c5948c1542181000c0384000d10b1422280078100090391955103100c850386c03240303d0040082000c124107218059032840810207201201c06d10316104d50070320302a08003451813017100300300c004400340082d4074240840031a007415040041d170031213241c0605c2c41d00002040342003004d4420009981c80143d0304501d07040014015902d40423406c40c202c28144030290150f40d0700082c0712140703909401c10880e580d651400407541c06400340d4004084030315110a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 244664316 1250 244663066 244663073
    0x212061006030b0307060906031a0909010b09130c03080c01110d02030105011d0f1201091a0601020607030504050312070e10020706030c090b0315060412051c0e011e0504030609 77
    0x400c012a01103031070070440725500c0c40c00d0548405007401142e004c0381c07a1400800c0007500c00d9100e40804a00103501d034280c21b18240015428110684d645d03041691110410821403400c0d0b1142c581055104001c0381e40c3c09000e56840321002460b2001038034000c0702040c8101d9010302904522408518603020359076075003c1100500c02500207029171400108890106481c8002192030506050310040c001c0d42211031403000c202401c0031058484505540700d00f50f1308001150081c3c8505100043c0c0c080d01c0d01490580d000925002000300040101801cac8424800403400110844880300f5441d412000300742e80c1c915059881c400e00c41d200e1078000408001041c507150740450005c00780c80c080d940c00c0c41000300f2a1022140380760740740510603050f0b0302000420801403041305408658000509840e00b000c0d5100244041455189403c1e0f50035000240c04040e500d14048601e010308610f41804d0725140c04000000b0401111b2081c8110f410504820044546000304c1c181c0e0300035030b4080c000b406601140c3c41c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 244665566 1250 244664316 244664341
    0x210702010f09050d05160f030c03080f091b0604090207061a19050f0604080d0c060c05040f05040b120604080c060a09051c09080d02030c060601140d0c03110304050a0c1a07020409021206 81
    0x9d034180c2c0015000e60104203001d43c500351302802040c42c60700403e4441e4440301135044254203041c003654407420410000070941c049001800c03040f400b4400c00601000001c010751144000c940c4800d21400000895101c10700500b0080c0c0b003503520a6031142e4121a014010500910450308280003521404085075021540b01d121a101c1510450080c08000c00c140015070b02d0707000340e000e00c01c10742c0c4604e5010300080c2020b901c030002190000306a8603400810f0031321241040c0b0285c03010794100d0750014501905c040200314880d040784100328108401c0c200c0d07464160300c8019900700707448041d00c0a41071808442c030401521002e092080240c807070750301450b44040d41c0d1381d0000321018400c1c0115030004a856014000b4144040805ca0920340f9004070380019038010000030781d641c0281035640301c41c06004148100614480c500c00c100526800446042076507818003258032281c040724900e500160355160040079101d14580c1543c000c624020703207100044a05090203008449071241b1004c1140d900f4094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 244666816 1250 244665566 244665587
    0x40306050a0e070812091810031103060f0a02030604271511040b070302030d050414060a0603020a1701060801020705150108060709031106210702010f09050d05160f03 73
    0x41142d501d10641039074843d403440c032440045800514000c00c691503d903000305840c2c01c00030300c0803404520f15103940024030400c0c1c414807594030f44480e0610070005201506410108110014542403901c040303003098211000b402c9602580d004004620b00c0d44664100c03440c207400c5201484080c035040d501d01c4004030481081030355207032000c545081a0111a04c0b80c005081c80150440c2c0c40c00f4205508581f41d42e1020108804500c420810641042414420349002d1072042400140c0500c00e2000c05180c5103026045020309807800e0020401641c50480500c200c40e51000c0100070b9208440d15030b4014115940b12400c15400000d2007020090301068004040078070014460007039880365001d41d0303030354001c6841d14007003690150140f0200b0051050044010301c0100b2151810500003610750f9451070010242100b0342d1104288503c142d0203008012918030b109208200031001c5458490340c030580c0300c8416084c41000101ca0b50a2030708624140f01c101e811028000b42042240f40041c801d4022 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 244668066 1250 244666816 244666831
    0xe131e030e04110f090907110d050403060509030c07090f021c0608070e070c031d120a03030e0109110f010201061d0108010b060c0c1513080f010e070509040305090406050604030605 79
    0x1011451040b034601041aa04613401601415080c00c2c0300d0014081c0400317010308580c05001c41031146071000603040200880300c241c46c2c1d03601e9843c1d61962502200382d030070180400c09680c0051101e0030041d000061104100c03450740c04040f03411140310200000034031842040e00c10210044140c102c01002c20703003054044a90030000c845440d82d0300d0500142c84a03095844000040d800400301c00400d00c159a8141928004146607203a1240480040d041400300c003a0548290020300e0b081d0180f541510807101075900f1000280803110050307851041031300b00000c890b4842d00c80c0c4100006241d20075403100011300300d503c084200190410203540c4c2c003d0720921075680d4940c24074400c8102402e00f84191040700341e00308020b10b100c0c0704450070001c03201d000711304002c1a6401403200000b40242103a07207500800311f55000e081078101400045096900501502c40742d039000352000c101c10340326a01074030342c404c0d05480c0c450780320350f14000014098180c43c1e011586c0118003140100501005a100c1d07805100d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 244669316 1250 244668066 244668071
    0xf0c06091209030613080405090f06010315060c02010804050102040902040b28121e0f020d18021f050903010207060c020607090f09020f07120e0a09060e131e030e04 72
    0x3661881e800144602c15186406411000c007203101215402000b01102c1d01c191107550a158503180810801c89046481d03a112000e88000d00c405940c251041210840c0e6100540d80300030706091014201040d2184000d0410691b10001000e109080d419a4090039075114155a60b980d0f40c2408661600a8808405008600491070103c9030515202d03034080d03d040d46614007100a0920880003c1c0303107100d004180b94003040c0d01c032120303c030f058424412144942d060041c2c0344d85c1030700596003c07507040303d4001e841258000600c0d0090303612070111481101412003540c080c0301d20300f0011189400783c00303a142c0d015030000c52002c0411a071600a28080701a983c2100e0707440e40c640380f0880c0e00d45414400c8406c10804400e040c07002c4a4039400601c13022208094443c6440095a110941944404500070004428014940003440c1c802960001000241c000348002030404444d00009100500440c0c9102c0070701c1091010010061059100c0b1900080c1544904110b42409000914050a00c91080380f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 244670566 1250 244669316 244669333
    0x30f0f0201020a0903060b2710050a030503030a0509070e010e040b0601020a030905060a03060302061c050c12070804112701060302040b1222140111090108060f060f0c0609 75
    0x14414429150310f81226076580140a00c1e5446040c002c01a185040740c0202d004940000c40c4808819400c81701c1043e50840849454035048250510390940c00580c030406500204002207107001007560340000a80c20002896140c1040c2e151a00340c1c580e00296501002e100005082c1005254640c41180201c0010490b95240401240c035003034016030003804104018402d000d5400c14a010f803c06a10303a003030004500d40c49400154445d0407501c1040c0c501c4095641000d05170442e40600364001c14031803182401c0901032103d01000e000d000305640c0c20001031500060902080c910301402000c0c01822044100d0083c00c8010104050703020040e412501100002a6843c072030b10840b012615401c0e112070802107030102c11850054003810910029101000003600c0006403540a545c4511480107130110390141b00c1e1842c03d560b000c2024480000080c061403031780d41d80080400d41d0000040b551120b0260954002034018061015208401c0700041444060000001100350044402d10304460214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 244671816 1250 244670566 244670597
    0x709020d05062e050c07080a0c050d030507060b010c080f0c01110a05041e08011401080106061d0f0d0507080708060f0c1b0109021c0308090601081b01020c0d030f 71
    0xc115845507901a0b15050f000c04003405a00030305003c0307580e418030700a80f40132940012149809103e40105000350455400c13401040341001d107140040c48140d071840900001624050880e0003050307000b40c207654a42184030603a0307100382d544000c01075100a566031103459628000710540c200d450881000e604e002c0089244280c0e280039a4036809565a90900d4a411304800c0c0101040d00f84c91350700000904100860010310a00900701e803801840030141480d85401c0059096941c40d80c081018841001180e503070019058400c15503426041d1070204c3c44201070740108603810381d460b40c00b5000c1c5c000c150000c00c1b005000f040f42d60440c0c40903c101e0300d05803545032050a41c52425600e01f08518003c00c0044400040c4503118411228900d000013291441500818030200068070203c54980034a801c3d081003542040b0000d0700030060800500d059810b042940e03035102c1d140313020080b4608400b141290660710803c1b01c0c00307030110041d0210342018a02c1c500900385200111000c000b1401000d03001c40c01e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 244673066 1250 244671816 244671829
    0x1180e01123c02010903020a080609070b0a0905010507030c020d0b0702010b0102030306100c020316090b0907111b0604090f06030b1807180212090606010908030c060a0f0209030709020d0506 83
    0x180c40c200910003028a602000021504400f24140b02c503055000002d6607031281d0000c0103082000c0903041a14000e001c5604040d0b103900312240130b840a00020301032580c0a0702c21815a4400e0920560f0b070b00841c281a202c2c00c2d9000c100962210a0548032800c2150300d907101805045c0540007400701c00e290707600580e20780c041211940c3e0416100710680b440b0502c1159041030050016041d103c541080d04884410307801c02c1c0e0040d201c1c15440f604415180c1c2030405415030300050620742801240b501810031900c03603500403149850558104240c46150340c42c1411180103100b0070300c0c200641600501000064011762000340c840c4a48140061441c801c03501d10b2004030028040a040b803d810f0020100310316404a11108100c0e50910010640c9a911116140188401001400585000300006104451a13008400550400d00980f95404800505250011510704010400310b0035066210002e0168031001d50f898450107000288001603036000700794003502c0107000d0003031341d60b041d06110700c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 244674316 1250 244673066 244673123
    0x60302030601050a060c0b220b0601021204050105031803041d10050d0f080a120f0504050708070b0a0309020d06051f0b03070e04020703030b030d0905030106090e0601030201180e0112 80
    0x2160303c041131180001c10180e01c01e98080480b40d2301384603003003003660b01c04e240890314002100ca52011000340034580da010407003041c20410039500c5502d05420440000c1a600001e014280e92a40411400701401003d10540c1e01500005d00c6416403200c2e50040708282e200251072500c0460300201c804581401c00b07004020301550030041006003908603a0b48c0000e9603100080640c200a030030780030000c005059009105034a80100c402140c581054101789040ca00580c2c4039601c0303507102420402442c03010b0740030754600004034140029a4900c600108080c01500c542c010b05007487c00301008001041d442c0e0400000c0c801600390345000740c0340c0110b41d4461000303aa007c40400d82d035a0b018615880d19400400e00584245400b08121743c50704046450403c1c6c4401030400303d40004020301040c01c0900c1140c0c01006003400c24032000301c0d014030007a01c03900180000b904000c09034100c0f0030a408070304080001002c204141102e00d603550006111500502c2000f110008440e02c002c03901580c0c0c1203007801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 244675566 1250 244674316 244674329
    0x20d110f1917070506091e0405100602010b04141302030a050601030b1605070c031e02031501061701140d0311060c030403090e04030e0103020315150a03060519090504060f020a0201060302030601050a 87
    0x21b25042000c01000100d50911040429a4152040611450300c480c060507000f000c1c0c05207007059a6041c960040d09462040030071038001d5181c4500840c2c40481c55080300d40008604444c0f0b10380700028004242021042440903140d8441c0c40000801c100d07074003c0c61441144200d200b0300041440c80821501c0e44241f040290801c00c0e0381c6014800b15024154800c4000a011288424000550f0100b802c00080109140010327034454010440c05030850094004c041014042c6035666042902180f8004060403c1c2805080020310410805018441d0707801c3c0040390008035141d6241500c0d04c9125940101c60440c0000ca00b50000108180c2c1c40f0b00c014001c991540381c200314101c5520044000750001400d02c2c8091210003c008001d132203a40d2174a5002560360203a070341d1421446406801d4135450741c00140902c008038812401b0015203131121064038200e09021640f03803103a00708039000e00b40515400c09040c3c80015410409601540010101c07407003501074a88a0780d1341c07410800c82e0055441000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 244676816 1250 244675566 244675579
    0x4060611030f0d0605030a0f030311040506030f061207030f051c080a11161a06150703030f0b040509031b030c0c0111210706050f04020d110f19170705 66
    0xb00c5440b1001400341a40440300030380083e0340b039982c42c0020300d8004000d40548440c40b15240d00c009041d07050041c00c0384903410800302841c1526141c04580ca80c0f100801c0840c3c00d0302240080f0760181c0ea908a0700398010a4542103420040d100d007810092440c0e20002141d0074800c1018014548041981e4001e81082035280c07111103640b84041c1c02d02900030340001250703038001000703034903507003500c0035000c1401d07034001c1b500d4100b1942a40a072043c01c1030040c0c40540f00d500d0307440384244140c120400326a1456418640482c5c0d215070602d105010303100d00505540d201341060104071307003040f0000140001c0000c0d040625800114085155186d2003003000294190300200501c1807594016041d81050a440d002255155170b64a0451103050030f01c110351b03030700f03401c0005049070503c03603c4e004550b040a03001000e44090300b00703940015883c2c03108007001401d1091071480c0070500d903500a54510442005400e04980d48194811500751510300d01480355103240050701000c1702038001031508203496025000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 244678066 1250 244676816 244676827
    0x42615060f0a03080d0e0c0321131517100302030d0e030a060c030501080f0c1e030f10321f0803040902040e0f100302040515041a0406061103 62
    0x5002440c1c9240c007405030062a84400000021003841c0104020702050303400141e1200c2410f03403141040c811450440c821350005024060340325901080c0c0d94402d12485500350703122120505c440003040c169004400303501c050070304100802c5c3c000100501c020308442c2d0001c41c0c0d55444140440384101400041d405a00154a185803030f4002d840c0341141e050700808944070100c06945000c15501c1c2145441700294440004002200f000c001e2440728503000b1001d813909080d483c011440383c032240b110b800d0060082400351101c0c0d44080c0400340240c02c040d000d5641a641101d804030150545440c2e4500c80f005048234840700e42107401c0c010304811600311980a49464003030050703401d4803002d501c1c2c0d209814441000a10704808200600041401e010090f0b25103203040d160001c10b420003000c0d20840c0c40e5013002c201010030940c1700c050950750304840009440e02c840441c951070007900305000f90047d2910108091189400d0f00d00c406107403044600740071503030300e50104666070200a040b824481c2d105011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 244679316 1250 244678066 244678069
    0x81605180402011b0803090c0307080a170d0e0a050c0108060411041206021b06100e071e110307030305100503011107151b030c02070509060a050607050102070804261506 74
    0xc40c2d800301100d00c04d0003003400e10f0503102e034100b90340261001c0490351300c08507a161440c242131201d940144240c01c00340c16066000c0e01c0300c980404003951348020f8164005200c50103054250b0101301c0e840d10a00440d48481002c1c0f8095503036400c10f200c0107021902c00e070b0004e40146000c1c001c002c0c1100d036244141d401c0c589021841a9180305890003215503607001d0101c954000703092034003184035209510040c0b80600b4246019038034805290000708000100c0703010080102d41180e0003050030701d00b0510b40803002e040c01608907a540038110034a009400300090746070034180e240d04528002c03514699210049591182018222205a560182d0ba030805204240224400c0d05100404984880011170005e2201c034400d100365032035442c0f62002c00c1c0e6814918070310590421022014100035201280d15090003000640282c0703162148902c20400000da40d000c1000a406503460315611400031a141d07615054000741000d22001c643e090143c529100456101000680140489260a0340d85a6407900030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 244680566 1250 244679316 244679327
    0x106091104060c020a120803071106060901060503090106030816020a050f01020a0b0a0209030109030507060c030e10150b0f040302131a0906012705180f0a0c09090608160518040201 79
    0x51050380d10052420300003d500d040c03025420446c40c840c440807560380c41c1400c40584107034030701ca941110aa10400030042c00b62207411049056401e9070801c56100d035116031010340506242d410003030007500c1c08034801c1c0c50018910207820007148200c568260f00d60301c50041c05401c5804480f00390050344041d00c03180100c4c0109000b190004083e090252a01c0070364000309007550b0f0340180c2100001c00004907442400580c1c8500c1c0c010070785034038003484001031a02019a4038180861100c0c01e01c1d554001d803920700e030068844078004103c02c02c801610780740103002c03041540d00244800c0c0c0c0940e80140603c200703070440c1d200d0b00c810382a032143c03100084040e007024800032940050215040c00f4101c0200300c030144c032001903186804601000b040300d003801e180c184402006403c13141101e0f1031086003402140d04180c002194010002040024804900a401c441042d826400a0449494a800840c41110201c1c02d40744030740c5903e015032041c5545000b4080500440707604d00d004510544007040c0191b11a1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 244681816 1250 244680566 244680587
    0x120c060a090305070605010e15030312070e030a051501030501140903030c13050301050a09170a0210090c03020901061812020f090603030409150e011208120c13030b09010609110406 79
    0x7440e00740e081041304d41d40d1008860082c2c10034070400320924100714400240c0e084103100c55200b5070285040540300303030138101002c10140c02d180a000030007500c2e01d260b480400c203c421030740d00441110307030303c4030b280750940303c45802030006842c1542000f12010500350403205050140319072500452459070360015a40c0b0300c1d00302100c0741c1007800d40c0940000b010758007401120700a250b802800a10318103203140104890283d5080850180e07420b0010041654000c00d4050142c041c401e00460001c002c0e01d40140c0c41800b43e00001d601c092030b040042921540140d030801103030800360011480b2038552070b2429042c00c0c4007200a500c20450001c0d1081c0e41008100250400b102a00b102d0034540c171119840700395400c0e44041c4814100045003004030300b9429083d1401000b65038020303661a00709445051940c412340083c4511a0342000c04074605003100d000300c50b010320403403025840342e135164907000584110540d1000115800e020000c40c0c8418103100d800e80e0406245155807419113080019610350040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 244683066 1250 244681816 244681823
    0x3020703080a2006240a0e060a081c09050108011206021b01180201090e0601081303110a11040c0e03100c020313030c0f0b040f030f0230120c060a09 65
    0x12541d40c441010040c0d50f0312020380c0da0030340160039189400503040d03403581030b43c03884a0024a445c01500c2c8044e154180e0743d8007510a00004504641c1e203403408103031451030640c0b2200061050700c8803051074004564619440e0a020750341c520102e5501e6004541d8440203001e2824401a05280080004c040d0703801040140c0a4030542103a09160400c843d08569544090400b0034001011343d00840d039026084034040d041c0e8140c4100030713040c1280001e200c8800104010301c05428140c00780c007454001c420150000c0c2140c0200c450071049071030184e001d2803850810a018a0030900d02d45401d41c0030340300720740503e00080c00410443e445881d10202071715200403020150300041107850441c1c450500040050741c081c8400c2034286180c401c0f00389402e4103030741c0840d000d9801400103201d026610403103003003269000701c000030000c0e400d40009803506083c0c1c40c10126040b0390640824802071104910820b00040700291038400a0140803010303640324281160b2126040f01c80014030004d026449007454900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 244684316 1250 244683066 244683077
    0xe042901180902040507020708120f0304030c02010203070605010311040f0902010e01120e0703050f060c04030807080306060f16030914090610050714151605070b1b1201090b0105040303020703080a 86
    0x342c004c42c044510a5800800507001510203000f030a008100342d00303c280d800c0010500e0524036480c0d030412408060070003820095903001d001c066a20030426503d4040e004001000103585d6450200300743e10156441a01aa0130040b00d603022401030b124520700c0c19010307107802160b420403000461ba03060b90101d003060000e94949000c1c80380e00d801c11480d40075500c2880101658a41540c09501e490790040c00040d500c10100024400a402c1c1001c3c0c41c103190380010015140d444d018005980ea01910a803001d8400300807402c034240c076000c02e03020000103010380c440d1602e00b5190601c514440300d1040303440d904404240045035141c10501600b03411884d0700e240c41400c140c51542c600c2504680c860091089a014650400088a00104668001c404818001303041503040c00040c1c558000c42c07030b02521589480c030004e2078036409a00a0120078100a444550310034680c003c040e41040c0a008521080785800d02052855010304100d40950f034240c0c00411807075196030f6030810250b1000720300c00d00b0040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 244685566 1250 244684316 244684331
    0x10806100c1b0305060402040e0708071811070501140a020901090b1b030c0f060106090e04031107180e0c040b09062b03030c080a0903081503010908040e04290118 71
    0x142d030380803490091445032014182500b010f0040100fa0345040c9840743c555080035408002d9500001492811035070215000da0520a06020040051008003054a0817000020341c400812006500c10000804a02e0a00f01d1640707802d0690000ca00541c001d0740c2c0483c08a020038414401404050843da80d810380c00c1032030138400f07244001d05640007840d8112203a441380500e440d8400040c401c032805085c030391400e107240500d40328441c0b090050260026051009483d022181000280001c0d40038203203030503249481907131050a0100a01c440721f82a6020f002e00ca80c1d680680c9400e0084001441001300320060703640307807e01007103485034040301c0c41a452900020b0a032444801d0300b50034a100d5020b46c5000030014120400980600801045180c0d00c0340f0f8042d4070000a5044403035650000d00d01103010300796200000100740100315050002e8000309020400180c030390103480a0701d2140d4440c101c403503c0d0301c1c00c0d581000340c400a605005252a102d060052015401c402100c1010040200c800b04894 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 244686816 1250 244685566 244685603
    0x70507020a050301020d05040c060f0c0206092e021608030703081e090c0103050c03040c06110a0606080c0a0803130b0304170a0806030606061201030213090b070914010806100c 77
    0x81e8051b10b00c4440c010345540811040c01035106410340205114209558000817041000b440044083c0000f4031a131400b103244101c0e40c488000303100ca4000c0140800c62001c001c1c250800034400d80c80c03000c00051240f43d045030707010404002540c0c115000f50004500f8440182c1c3c5c140c6084100810312204980c020703010100400c5603664403401240b0110191500c80148400141900c00041882c103c0082c1042031000240d124031940003210054034210400308844040d103401c2c520309140151156090010204403200046102c44403090201c0b0300c11425030341e842400d5101d000303415281f080b602580000300118000c000c02998414490420307229468440840c401c03564014030105e60000350800200704243c1410001b690300200204d4540341807060622045010300b00501009005d41c2191180b110080070941294040c240e01060f003039810b2030880c000608400c40e620a4907282c0d1007494180c10300f9409030141500445c00030f49416400e125030441035441e02c00046048520700e81d4858003c608 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 244688066 1250 244686816 244686821
    0x711030307050703080f040f121b0605010e100305030304060209130204080c01020d030501080309060d140106021b010513152307021302190807090807030b0601120e0303070507020a050301 82
    0x1041c054503000d49805090500a15440b0300516020b00d540c6404e00340b1010170107401142d030341d00da0b1000c00320720b0103400000c1c12101c0c0c64021600c00b24100307d0351340369020400290806816501c0c60768072104980c0c0c0360301512100450621014000e900108041000704119070000c2c14880406410380a0110818654800700c1c0d00550240c5400c0d04250320b410713415070317050041c2c100640403440c0a01055042c05601c50300e83c802c8031503151040000080e80c0048045641150012001c4011140255030b540e5002948400800030b00051030452000c0b9823340d17601030802d80e2804002c0c140e0716107419003440100c0000c0f5020318000400c3c03050302103102c1241c0c0c104620350301051150201c1b1716140c0480c3d2040c010010350420400404900512007114882d0741c0c40070204440155151401503038030751200a45503805680c02840c454011241c000c030520401d025414010031003a070b83c0c090340c030b0a0600c1c1c038400c8404211110180c1c4d00100b000c5032441d0b00c1600500840e0340020844203040b59110002801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 244689316 1250 244688066 244688071
    0xc0a030308090c01020a0c050607030314040b040203060708040f06050603030c120901090b0429040306060303021f090308010b0901091707030203120309061b070609030c060c020f07030b07110303 85
    0x7411203080004038601400390325207503034080c001800d01c008642d559041045003030142e5070180e41c01003204030606110340c00010410300402d17000340761420035050540b01103808039000c1c1e009100c2c050100320307074500c0350310001e10031500807504003000d04240e500c110140c40040c0c01c0c2c2e5814030040c804403500740310911224401e41c0b0521442641e034410040003501183e140da0103000c0c0740d8014401000a030500c1100304144001d001c3e1002c111008050000c01c0c41d000c0d642025241929000001c400c2507000200701420600d02024031100d418074081d180141c5040540c02000610340b01e00403c409141c0303001400c48440705052484c03405423155208030702841c0f041a60240c0b548800d40070415030605100344202c00090f010950310394501070761071998504000c0c042e4440e07032030310b84091010b52488000350f03200d46500001c1071101d4a802c0c00c0041059240280650302c56150413032a040981c0000fa41210040244000e002c1051031600d60883c1c0700c0008045402384500386404201c888024030040d807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 244690566 1250 244689316 244689323
    0x50d0c05090f060307210b090a0f0f06050c040b0a0e01120e0a0c0f0305070e0a020708070803061302031611070e100e01080102040605040b070516180e0303071407050c0a03 75
    0xe08a10f401030070145007803000c1d80010000c03075003070340d034211040320304420701d13010a8001d0744285454650710f0001d458292003480140c5465040c512140401245a1200d00d070a4080c0d8024882519107031540703c6c2c1c5104511444112100400c00c0760041405031000c180c4008050401c8600b040c0c0700381c03d0b5402d4980c2620001039581103070350715104103c840480100a480031100a000e22801d5030341e05130303550080b0700481600100c046c0001707140e603c1e2601140c030403d80c40082240c482c400351402d90500e40007035035214801c031440c10551001155038402d581c0328450408403c540c11a00f0a42a2007001c0c102403802464020340c2c60200b0f403400710502c614003d40030002001212458030071030003084030041c2c0041e0f56503401008200040c0e40e0000c141c0c4d06445181c6c43e0785948090a14109151201140030310301c2c090076543c800035101c00c0c1911a4944840c4100c02400030959640c0d02a0322840101c0300440840c00c894050810042c4282c05004040d1054003100c800405c1c0100042c82c1010550046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 244691816 1250 244690566 244690591
    0x206040b0a0219020303070308090a05010609050106110c1c0c0905070207031a0f0c090103090c0605040807090b0604030305090d061406040f0905060f0a0f0203131703010609050d0c0509 81
    0x107115a0304001d07a5980b241c40349a5007621001c9a80000c0d16403250a6001d02003154120210700028000e000c004c044980c440001c100072541c0314050005414244a40c90210340c2207000d00035120804658002d407004c00402550401140808017100c2c6000030b83c06848400c130056011440c0130f914850710340980425001851002d01c0c510740024802c2c50701c822103a81d84d18885c01e0203050301200041a80007240c0b0000c9030b4503051000700481c010a00703280098100380c0300e44000111203400000a00c10359170400c064031143c039100d13604242034600240105401500801040003c00c0c80390300070b403203400001050625101c145444420503641c80116150005c1c04450912603207203020b124004114101101c24401040c860300d910f616040020f2811408000440c000f802443e0241e1001d0640403004504540780d041c9428290070241000c0f10484881d020340d0b80142504400c1300640b81210500d54540000905103001e000340d2400365a401c88008144400214180d6900c603070711031241030b811016 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 244693066 1250 244691816 244691827
    0x1603020f0c060115051602060703050f1201030215040b04090e0304050a300f14010e0a080301030b1b0f09031c030f060e0112020d02271f0b12130206040b 67
    0xa61000320310141c4400280001000145400303002c0d101c0041201d87c0468190740c441501e41803c0c0c03214428035500035031400000480f00d21051100c410707030341601d00980780c82c8401007105444c4605032045005030703d040344041c081048407405caa000030050803a40c1060700e0929980fa000b281c08084503800c031000c03e94907451841c80c030001502000000741e107051044500310070135443e46a40901000800b41c1a59103060060846010940028101100d01e004844040d0124201070006810030b0004a90700411000412810030804500400c0040e01705809440c3c04440381015103280e020b03104040e0580929424483c01c0f17034900f12101d04002da6900c0204890180e240d5400807194260048210003143d40014403000444060710806940d040e03803d1072500d4214000202c000c00540c00c01d241010b4010039890151912100e80d03030141000d12140c07840c040751b084101c6818400f0b40901102c400e000c0c02804501d000e500c0e02c25401c0802103400c100e115850360040f54869000340c202010072040080c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 244694316 1250 244693066 244693079
    0x1903140319051305040203040c030c0b120624030405070305010f02030a0b04050403020601060e0a09020f1201090501050607062309071d01140d0201210903090e0f1603020f0c0601 78
    0x180304201c9095207000e510b040e4044074020968903144c0282d070b001e95400b000150811036400304080107950083c0d14644001d98070307960458298800001904030b13000340070100f0181d0410011041400c0c3c8100010280000040880031081d01300800c00d480750301c500100003010520a00c10205a401540c030003581d40c1c80c2010045060780d0b1002d14503030180b8500300c1080007181d4040340c140e054560f0f900c1c0c031018406448000411100c40ea4012078006403001400410b880110030003040c0103035245034010b000b070fa03866440f034003101e0092040c1604a4400c00820001a0555010702c00740c0000d101403203900f010314289500c40b10421940c81c08181c0c80340f1003e02281640c821341c132613910b43d1010940801d41c11310801c40c5034000e0458040e0b0044c00c1d11101e050443e8080c03000300080040030909540c100813910f141d90050900c10f00c0c246c01042503584080788003102031249500c038030f920150503904c41c4c940081c1d80141c20b800015620416038288803030440c04002d64000d18404075800c000308059410b001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 244695566 1250 244694316 244694347
    0xf060513030e030f100510050a08070302210d051c05090a0b010f05031b042702090c030f150f060406021c081012050703020409080c0c060901020a0219031403 69
    0x442521070b40c1301c0f000da14503d5500098044098410581c041859100d00d15250100f103000d42201da030000c000440883c8403400045d200f07084034000c5420040c0b00c0d4111280750034070600302030310f007005800200d5492030b40390144c0000e082407130020188075410b00c003441c407000484d60292200362941d00020004410b0044416030b59000d4a40c040100144614160000f551030702100040c0c0641d54109a91003141d07919136015040c043c0b00300c00015280d0038240d01ca0014800074070805c03403091001340c0120301c00c28181000c0d41d10030060001c07030b50340b9034480001000013240843e8015074030207808003021a094a0306c00c040c000412040d0002c04682d58110708030010310b4500509182000900c0080114550808030031808890815501b09118041ca052490810401303800103900703d82802281810809850000c160300d2121130280d03a44a00307000c08004862050600007401680b081100d140075140001a40140160041501c02825a281e6030303d46801315402122099400120344c2009190510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 244696816 1250 244695566 244695587
    0xf03191803020c0103020c071703040f1e0b161e080a03090309050f0a030b0a0204051c140a0308011401020f011107020909120a050a0c1a07020106120b010905040f06051303 75
    0x5d0a0039401d01508401041d6074464134400ea03400b81509880488816500f801110701400070220032160705901c652004580000c019080110342141260000d105040c84060760070071020f2180012400459807101000d40310210080311034108408007080021301000c00901400380340761004900506a401d01400c0c1c04400d6110342e0040450319400c40f500d64503003a902044d6680144000d665898202a8100034000e0740c100c90b07001b83c2d40d80c0126001d0b514042c0c000040a11a0000c0381c54850740020607a25125600401804204408018818030038542001442c46c0740600c1101c029502c5800c0c210700b501c130a1358007051840740020340c3d08294107110002ca648141e106c001440154411150102d4a02c120500c031000c00c007011039004d1580c0d00c20600e246080b9041010b42046441c00484241408020354111000d9881c1040000b04c0803031a46c8800350207604007440700301c9686424007401c068030b4002c100b102c0100412840000007401481014012403d500d036008504211346009010795048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 244698066 1250 244696816 244696819
    0x503041b1421150c190e12031c020c0a020d0f0507080706020d0305130807050105010e0109060f1406130b031509040209040201031e0f050901060f03080f03191803020c 73
    0x10300801042c90b82c0000c1c480c020314031003004140d5140c1d074a10610405020325450110780c1d4900500922400303502a01c0a002024116181034450480d07000c442c0c0e03244202680c00400c0d0880c80c42c0418000c1144d80540508800e50b0140d610391b840743d50009000c1e01d21410202e40980d159500e5206102e810030220024000c03100060520905050029540b01d400c10900400c240e22000003030801200051042c4070b09922050309a00d0f000c042c50001c3c060102400ae03000c01d05030090000545084c2801070760101c5043c8d03081d180441d07041c2006001502401c80d9220342210302008824461415801c05000a20404605a4480c1003107032041d40700d404003003025840317418a08103000c00350340c0307a085030703038006909003800141955541c1d8420240102c0799410320940340b800300c0346100d201413034002c0b03071003913680c40d008000c4541c88400002c800e0480303000191004030203015030341d5480c080d44011500030b5020710065074415441c00f1010140c0d000f403144e09690203030001b541c0d800c040c0c04001c41c9a08050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 244699316 1250 244698066 244698109
    0x1051803070c1208040512030c06150a03020909011401030c080606010329040905010e030711030a0b041202010e1902040b0909060a091703090c0901060306060504060503041b14 77
    0x154850041410450158500d2041e040310040f00308050201110011700006c0e141c1c4209164808510b82c8035080208080480d0107000c00285421004207158010a000101140f0700b00d4159000d00c030312914010034000036036580703800300d0282d4010204124002e5100302e440c400000c0c1804049810900040c0c191414103017058030007581c4d082c810701c000304084048200340b000103d0708400a4060305c05610050900c0d40b800200c5403140a01000030200c0e18042e61812821019840a1543d1a0303d00312009e0864402800441d000543c048140400391146200104045000489003810000341400e40104814982120011030905000b56000c00c0c200701d44124440c030b003e20709107803101802483d20100340e560b041036a0800c607000610f84d03080010b04041a850b40b50900400b0b0b03940b072035403040c01d204d142e0050000605038482d0041d00207942c95039684908040c81c000307058519810241045811060580860b86600b100c0181781c0014219802c8510b0900480001c2c81504101030f02098604103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 244700566 1250 244699316 244699327
    0x15120b07021b060307050f09100306080d020606130b0a170d1b020d03080615030a0903090509070207090518030304060506010f090e06130b1003023018010f0c0201051803 74
    0x83d1110f060b00c0c1d0290244c205181d4a049030701e006003845c0b0401c0c07a900d5011300190301241c40107038154800c02c142d41140007142c0c50620300c1d0806a94941c0121245548103900701f00c18040c403455604440140040541910a000d45a402c11002010b0300345000340c8907030001802d6030009600c00c481c0151001c02c4403903032640c0542500803451000f000d11010703040c4404207000c01e1190302d039154000640300e4407088090316401c00102d09006001d81c46425030010300f00c4100842c161030071a100602541050300102410f61a10081d0f401825004010385004a0041480c0c06525020720007544a98419000001c0030325008002620079205c4650310700401c40003c0090200c60400042107412188c100c0e07000881c0009201404080d24440310003541045a0f800303040402138150300a48142844407413250b069010076042c1c0c02c140d160401c0350b94403881003900842c0c8e0305e898401010440311050300010135480b40c508000c00544004120080c010703950b8100f08917104001c803012014281e0840d01440c40c02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 244701816 1250 244700566 244700569
    0xf051906020a090e0f130c0b04090213050105270d060504060b0312030610050c01020d020c060108010b0f1008070c05031305122d01090c0e04030e0301110d15120b07021b 74
    0x11401000001040014903581003400301c0f85a107407004107008c084c3c0350780e00c54032030b200d25000c4c0d00104000380340c1300640c49001c1159170258059410352000800411160840305400d001c520300100c115681051a101c1484041542802054402e1f0700030303000443c003440d905d0f05151818402d4008043c0851041c8240a072594801251007407000081c03429039210a8105e0ba0f19009108460307184003028400100f24004440100c2e0310f90486071903100800c0705070045030070f10100d000c602c40e6103903028804600c4500114080c007607283c1c214801d840d08000700d02c502d6840d41e00c2c5900000608140025007501044149044214610304624080140000c58568202040d009102d1444000e4001040900c1c0514400c01d620400e18940c004905d680f201341e88071241d8050040683e82a400a2095540c2d1400d500301402400c1043c1002d00c0c2c0b040c0f411110049500040001c0d41010300301d041410400543c810040d22080465400380445030740c0d0341021200603181a440303009420070451000b00a2825 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 244703066 1250 244701816 244701841
    0x90215041e03080d0c14040e0f1006091715090106260618120d1a040e12090d0501020d1a0111060103030c03030f14010f06030b030a0f051906020a090e 66
    0x41d00c0801020440307007517000301603a00080c640c03080b103c1c4080108000440a000340310a0317000b4940d2450b103407401d403520a1082d106a526000e05004a12a440100721050b03d042e940f184036040f030016659014940100d40300c00c0b107001c0c0ca05048603134440f1424408401641521002c07584036000382c500700d1183c0b952494a455000b04089003455056240300c0740300d10144469105ca072200d208059032095002114002061089030842c00f40804c1c051582017414140b090f0910300680c040100100c043d00805004540d1010b1741c103e07004424900d46400086003400504074003104070002040c0461407170748a00081d510500e00724108205100124500d10010450b181903c1d01031420350620710359410150041c04500c0c0f004615203107020b0902c01d000b403212009906a40600464505da80c5ea60001101500c2800051543c1038200030021000600f0840546024034401d0064880b1480c0c54282020301c00c068042c1540c0c142e4002484815142c0e004900101400c07550b21181941e040c040912540d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 244704316 1250 244703066 244703077
    0x609011a040e010905030d090c0e0402130c051903020405151c02030a0b100807090e240f03070e07121b03020309010b0927030406080415090215041e0308 67
    0xa981d55440d4041e402c20a402c80d12542e6003140c00c0303c2c1e6450350007090b58000e01035180309450911524001142c00c01d40b0042c4207010383d400521031040c1d0f1418420540042c045c909010080c000108000f04c0c240c1c4555291041c050307980d840c01612585070405200201206000c0001d00400821002c50940348242d03146001c1c60b84030b040141c4a60b9120f510100510a581c003085d4041034110441200c00e034021881841000309a4034601038070303a1080c640d4a11042a40da21a00c100d4800e55081501c4240e401c000701c1290040414850f10707a000f010070708003140c50304a00d02d4049034500300010250080e00060941059400801c1031b10354230705030b045810102d1684102019000004145419000d400640c031036680102180e40d10305024400c10303902103074503da44e00800e110f82c040c44a080c40100a0314102c410030340350f842e0300c0c0d907855507403007641c1d40b69400080c100c507620801c4c00d015861f512011a081000100c2117170f982c42c105440e00700031a042d00301c0c03121640c0000b40e0030b1001901c00c606690 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 244705566 1250 244704316 244704319
    0x10302010203161a01090203061c03050405100215041202060c16020402070201050d06090203060310061518080114060a12110118090504061407020a1e0305091002010e0609011a 77
    0x1110041c3e0361412160452400d440702040c0e0004030004118600c8075030045020b41d10488044115040080000395003140d252006800326806200400007800c003568100c9101001d48180c6c1c0c00411046100c00303a003103054030300740d034240451103540e082150100f01317031500440311441c03084c14100c46100b88411101e8144009010319000b0541700d0459000b035040d5081d4604101042c0101030701d403900071000350412a0310522a10541c4202c90000400e803107048242e40074084540a04400ea80c030070f490a581c1d1030040d081c5c0704409140061007940c2031007009150000c1c800c55074070604225040100c0c1c200c2c507800840c0d0302c014040c0700b400064001c0000681a150a08148403440644044d1684400e41580460191400c06e42004204002c0f58421880300c59405131444098032400001c0f40e0303c030381482009210010359000c5d03103100d00300c0740381d0f0110061003841c04030310713204240d00407030104128504c030703000941c1d107402e04503103100414481c0765806076444e13000300111035182d0482c0c040c03410503c0300075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 244706816 1250 244705566 244705597
    0x203070c090b040b031f0612080702041a0607050109050d0305270709110421050d080405070f0602060403020d0e03120c01020403051614030d080c030703320a05010302010203 76
    0x1084035454030f400400450b0b00c0101525990715219006c0003c0701160006a01034038a03004001c62003010007028506000d8009880310b003890155400e1000030700d014891031142c00025860300381e842c0d0301c4900034115103104100200b07090b1440d10703195241c20100064030b01894104030402034401c0c0c6050a440a0404190444d240c2020a00e0802c0c100115074012054040c1010000880c0034005c50081c0b0454806110709043c5440f010340451803d40c008900030243c0d042501e81658803841340e41c1c1550014010825a00d0071603440d94240d445440d25408000507030801000c12050603014801c01480760a41e0518184014032000000e45481c0c06a802c034402c00008140040c4d102c5096040e00c028583c80340c1100c490110070980c0f0b00184100c0d01c144856003440102c0310040c0c2c1008a50211075158546420b84240c44e042514803d54100070410020160360306043d40c612072540b0308072194400008411a0590b0115003442e1015800401302003200c0d0401004200503640001100e001700303031500b07a6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 244708066 1250 244706816 244706831
    0xc020609010309020112061514070305030609100e100303200601120302070801060609150f02030a081509010608070207060815010809030c030a0e090106030b01090302090606040b030907030b070203070c09 89
    0x180d1b503001342580380d100a140780c84404501c001000c0c00c040c0d64030749240c64014200d0210070352100144a801002070000300b050002c0f031034038101010601c0d0009440c480120b1000e40f61034000c941404225250031240e45043c10800074141c00070800380208810250300541443c0303810308503076a0141803081c603090681a010b040c0a05200b8080321020707129550091051607030300c070001050b074aa00d0003521400c0c451814007101060107001c001050ba812500a98280701c0c85a030142c07500e00005010148055012000c004142c4e00c01c084e450281903940c0303034207070103007402000246030103490340090041c00210070030b000740d030b51140356600c1e1198000d10f060225030365000c00d03940c00c6000f8010809424400829a05800d94025080c1c001c61481a180d04030741e45e88e6800214166402c0d2090b96000c40c041078001d10140c01e00d04030055201304041d0010b4030303241e502c05c155191907000321020089074010341c5042c0f04106200e20156000a00f500c02503003400259100c0500900e1180f242e46000c80c0e88102c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 244709316 1250 244708066 244708069
    0x51815060d15080705010c0314130302060705010606031802030a0f020316030b0a0f0204140d141b03011104050108070807090312021f020c0c040504021305011211010c02060901030902 80
    0x101c0714003121249090102c0070b010b40030755a01d07440500800704280078100700840e641d40302d25130a011303d1350181d4a09294004070700e0003144560103208420681c054040c004000368540d03400030700002d4454400011103625040c0d0040c01c07181c0c00c498400c00390180710240000340c1e80c00130b0112840d03900302c103486201520610010f46001020403d0300441102c0100000c184003a1350306035446112414824025000d602c0700b03001c12072003240182010580903c1800c800c0d0308108251448081c032861808041241c1480f48514084072170b0012444004098284d145e1420300707020344814a001e05092500740390070480042c1820400a09001c10840e6a000007000240324a643c0d000850700103100c000b8203010044c0013901c500840c80c1c00408042c0c81c19070091800464822110300078144e1005d806514641c004004c05050060400c4e41c0c084130101060504181901c80c042c028010f06050040100c074a10f07007550620398018980e81440070030310078200561602e90485155000074a00011480042d10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 244710566 1250 244709316 244709329
    0x30a0608010501080604050111120103030e0d05030f0702030705090f0613092405090708121c0608010b011701050a0302060d1e0209030f03090607110a03060207080a09051815 76
    0x900403a0305600701000080d00700c0c400310b100e40c003480c006e200900040703440c520310700d10078420354500c00c514110b1500104040b038492200c9020440000f080c03401e02481903103650345160000e004520740020001600c0c0214030b001c01590000704410713598481c1d0740c542246540b0130030b10010305490140c01700031030310001107505a10120720503903c20307034080381d90810b0b107071910003600705116802500349000f010030000000014400700b1140240b00400c072201e1030341142192034000c03404028614601040c048100d07403107805910040d003074500002070880c02240c001800c080428104404d03100810f8014001d940701c0c0d02c018425640c0598409540c0e006030740c644401801c10310341c000200245142000590041b580003440c400a04400701c80042d00341c02d00c050340360320030300500070f503c46810040c0c00002050480f01481c032980051000406554136200e0105a0f800b0318000c8900760b0000a00810741031b084084000034140565a840103625070820030714410310054507000e0040e10a04c07400c080c40d907829 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 244711816 1250 244710566 244710569
    0xa0f020f060408120c0304020f120106050a08060915071b110405040605010317210402010e09090a06110c0a0308100b04170606010206040506070c151b0806060901090506030a06 77
    0x1401211042c0c940360034030400c150031940c54500038a200f000442c1e81c440e454429a1b0040350006c110b10314102c240c0040002068200101515075500c60703600280b2565882e092500405054001d000a0f1900e0302007281003030603103c107103e10b154400040c0a0900c0d8000c5120321101311101c0c41c02c05207510750034883c00286c281c60144d80c0c01401d00702080104070980c1c0102c1e04982c8580f800441b400107207480c0d2581801040c01c00c641e4040b2860130f89510f51403031441c0a40080c018144609001c00403400306504075022103902c401c0c7c1e0300403c40901080041d1080c80790b00b0740f41005403810703c055030445503218500c1c0c002c051304200e251310200e07892084800c1840d005000c4840140e55583d500c040b940405806603403441180c1c081c420005405500100b2a144520b038844041d00c06039441c0b0700140c0303400f51300071004d071407407180885404041d0440e44600344d540f454060644070b0f1215000001011100024001030260005100324040c46c1d802c60200d0f000d031041241d000e43c40755a05820f0380001c0896 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 244713066 1250 244711816 244711843
    0x210c070606060c050f060915041a04140d0311030a09060b040606030e0105010f12081605060705070506130c09020f07170c0d08100e07030b120607110a080a0f02 70
    0x10640e0002d4410b400c01c03500c092062064050303a9a24055400315501c03003c00710388004e610b400c9081c00040186890386680d41c0726106100a0b65076041048443d00c000d501100c0c11254010b814004c12026a420404000c0b201c00600d401d1020310800010241280400b0301892030158075480f16004002082c1c01c02e1402d554080c104201c015500d84004001d88004070f1002840c0d441c00b400402d4101c41c842c405010783e502000b581c1b00700c180341d6031100610b60050880007100c4030520316100c0000c1c420f11109005420507500d05484114604100d8140103000d08410f074121082c02c3c4000002c0c004007140c0302210103000e4010f0310b5031014030b0000440e100d8502c000301801c454403c400c0c00d10602c00050460750203030004942030002003040c01d0715108800e441c400d4100791841010410022204643d651011003449d010851000c80c8012410340111032440c0ac10640000d02046034441d840010305060503114070040039001019102c62045126840702c1c2c80030040c2d42e200500500b8020080c1440d900b40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 244714316 1250 244713066 244713071
    0x2040504030f1701151404090501180606020f0a02040507031517010e210f070812060f030d0c060b010c12020c0f04060e0a0b041107030302030a11210c0706 68
    0x5003460001d0105072294003140200c0e61a400e222043d860f20240309040e5481c0100180151903140d030705840c8146e224104441d825420000030034043d00c94002ca90090100015100007141c040064105480194100c0300c110740c0040c00316000d071240060640d0a69405940002d21030311202e80171805054070035201004640c5024002032204036031240110050310610003045801910640c0603240d0804503440f00e02500790101d6083c2c0c0300c075803800a181030045019982d180a1303541d9180d0700f55800410f100c030a8000c016007042a242490000d5950b084030840240841a1410310050300c1c0b918502d001808840d9a000c42c0d0001c0d900030f0b13403100086071f04031346155050b00412000a5561a100150301d0050140290011040c24640260303802e4402d104c0c030760400783e903030040244006c2c140c080d80170740d04c20340b5050428030304e44102e4000c01d800e5000c0c0e900035076240780110501042e00d80340242c0cc40d01e8101008010750329480c0c280c00e4400101500f840b09429110022201424019560050911807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 244715566 1250 244714316 244714321
    0x60f0313081b0619090b040803280b0a0602190f110910090e070302060a080a1d3403141513030e101b03140307030518030c0d03050a09020405 62
    0x402c00201c1c00c1c49200c100c03c0c0e107525448510307140801da81d01c4800c0100030b031020b80003107000154a24080c60303001e00324005104031103851078004958108003400c5429103550ba91045c1d000390910300103c001500480c002044018524010a02050203038500a0006520080d5100410464043d06081e9500c0201031400608000300c012407001841e205458030306140001c055051140820014121b0390014412814991b079024103603001c3c4401861008240c0c2e89041310b04020415417503000c001d005181c001d1100300d0766400d44030100340c486c1001c0040700269640c02002000b03500c40000607260701040f104840039505a01e141b500348400140c0d400e5040e494100031010108180790303503815001e07683c2c508081244505005440d07220700f2070000019444118180103007190a62801214400d15241d80b90603d441d81420f6290402d45811002a49405c01e000c1454141501094103400f048007452505480894580c3d031002008040c1c130a042c0c41e000001c101c5078403648213036409038001d03000b4401c84c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 244716816 1250 244715566 244715617
    0x405010c0c121406151e01030912020f0f01060f0603020c030d05090115050103020913201c05090321060d02030a03080a0510030309050d080403120e0f060f031308 71
    0x122000c81030f075441c1e07200e10030019000301e50b049626020784401804160310782c0908503121408103103038256039040c980ca4400d05000074079000303008840021254040d003c003012a20b041410002441e19180036a0b0400009100d03010040c54440200c4445081c0103030b884507200c510724154043c240b44d00e4800792030701e070410800310010741001c8a40520400030f030030303003a89941c015002ca0062001e401d41050003014a14603440180c0d02c01d481902c2150740100c0000b0000c80803800650280d004003200c0c00c240e803001c1041c15024029182c0140c0908051420b00261b00920001c0c4c007920442d40341045001c901040e04c13a210400040040b94002c0c1c161810440581000342060200b515042443d0f07160400244a00b01046044401d5a034103603154103a0900c3c010403c0811003d6601c1520312078400c010010010345483c82c400e1041762141c940c00c0304c401d48001003000d44000003850354064281000404411018201201e500c2000c560101010034040c0c2880341c2c090003103003d0501018013a480d5002c1e207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 244718066 1250 244716816 244716833
    0xc13120c06091203080a09080c0307031106010f080a1709042301050916210501030c0e0c03070801090e07180624050406140c010903080105130b060405010c0c12 70
    0x1a28081c0e161112100d07522400f94412030380700440500041d00040109500c007240d90011100e0718090322400382880700d03150180707055a10803c0c049002c0340c888070701e0110921061125a0040c0303607109001100614025100341c48554003000244004801e035451203a42141206461050802030700070051407800f1602000b60a110140c1410307a100048000142c51410a0f2802e01c20900040ca0003150104d42006030b40000c1c0c0000400c2540800400290500c4010300c101c5000b14068515601074501d0004e03840d039030000103050141111001c0040001e8160015000d0303045800b52940022045000071320542400c0032a0000514a11220340300054000150441826501403154071a81c195001420741e500724840c003241000f01d4001e04c8104003490207130444c8103640c80d000301c0f41480c05014801d0b4508546160100b180030580c1d010041c00320b82440c030880400102800020045103100d400010482d002c1d40c03007494100140020440704000d081b2003840003d1000d414600c00404551814004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 244719316 1250 244718066 244718069
    0x5280b030a020307030b0a140d05030d05040b1006030b010e0108070c140c0f0f090705090622032f190b0c030304060b180705090406080307060c09090605090c13120c 72
    0x40e081c003003d032a0f6450038103440c104448d11190202440701c0c00d0001d00c4100c40d0307800c400f81e40c2c03030105004450030798106010303080c820340c4122007141103440d0400c0072a40c0030420307404c14400c04d40351000d18071550340c004002c10000e01090070007031895900c100c0e0880d100501c0c508020148179481c008482c690b040013a84950b1140c0072281c00000050314000c2c484c0803448152410392082c084c1c00840c03078090183d80100f080718009800c181c94401c00d803003150000d600b0020403102120b0000307020001d128402880c1d800c00c200010883c140c4450b428440417407012090a118844c0c0c4641110080840740000c2d290014403a0601c090b49544540c1e001c113407690801c0303c0c29a032107410149202168508415292010796007220b04080c01d03103940e001120550065020142c2003036a8100129074101c007000a005494862040840c00011003000100410140d070321800d1098203003203050142d03548801100358011a0200e40a0b114100c103c0c1d10000b40c215584803400364484084900300388082100030f40c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 244720566 1250 244719316 244719331
    0xc021b0438030c0d17090f0a030302070303080c0c0c010806031603140c01021513030210181502040b0d05090a0b010602030406031104141207090606051804050105280b030a0203 77
    0x100c1c4290341d181400944450604c00500002c01c4880103030b80002480051b00503c60080c20f848000518107005c5000c10a0540059002d07a100c43c00410802d036003c1c4c441a84a004038000e14146000725200666501400c0405070510003007800203111500c04000880c0709110032035444240c00c1c3d032403c16440400503400c2c00403403805020500f0b4a20350000038490103114820119420f00d51362140f122007900f41054045007117000d165840440c840f00750040701007005003500c2c0501e0b0001545440001c500290607030205150061100304600710211040c0ea40c031a0100001184aa40b002d81c3c0d2400c10038440300040c055407820300003184a66000000d40142c902c142c41c20072507090008040382e203a018a11400580c032001c404041c1050500060284510501204031031500c2e44803643c10050b111b4036041240042d6020800c2c0c2c04096604c1d210a8035800b0030741e4200260350501c4007040440c84140b101c0c03296032091001000c0300009000c40714000303203d8181d8194032418a5510741010398801c0c2c60720f8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 244721816 1250 244720566 244720573
    0xc02010e0102130303081302090109062103020613020a03051b0102120c1207060f060e070306050f03060c070f17030a060905061809010e0709020703030c021b043803 72
    0x180c000e010501c22145842e038541c000c001d00501e0341c1c0d021030b03d19500410350702219055880103c01612082c100902030309260b0400f00c4d00798100104448100540c90603600c46818a009810100380c002c0b41c85900080e070b424800114041900220745001926030000f852031142c44403031103c240b02040e024108180c264252030040d08134500d8010207010700c8503245980d401c90f0070382050102c181001048501d2085801060b0107080c80c5281c000c448080e4480c03103500c18044208028150b252040201074402110500e00d03624038080401e903202002410401c018600042c480240285918000c044650141030400d5144110464074030720340068502102c07040c24402d0101c2c0c040405d0041d54810040075101d400b11004c5940c40c0410700b500030b051000695070380c1c0299191710800388004000703010340043c090307580c0c0c909113002001c860074180c00c10210742210304c0380003100084010401690f14101c0d4041204001d5103080f422070b102000d1030582d5140c0503da84003030035081c49840640014118140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 244723066 1250 244721816 244721831
    0x120c140616050315040507030f050412021c081803070507060210051008030304110a0906240305010609090c02010b060d1a040204050303120a06080d090315021611220c0201 75
    0x42d1024001513940303e03035006000c640c3c02001d040540c480d6510003480c0c64003160b240d085415640440d8001d80301517541da504038051451035901003001302040c0006c19a110980c005103030340141000c40280c01c02c0780c40901c94a6680b80c03004d04000b55541e03680c0010039101e095555010207540c40d20140146160035003005c0000e4a01c6c0403525000d8211520702001e5841c642d9503036a4540c1d01c030020366031241d0080301020b001c2003003002d41c411103002c1d0180180d42c103003103a52a1000604900c40d503004408043c140401486241c2c0c0c000c07078440c126602140c000c07582d00b040e00400c2e8003600c203680783c80d5080b450108040e402620700b50414aa020402a404008245180c1c10302050348220300805415034410040c5850520540c4a00e40d40034200c03100005080d030311002c0d000c5c1040c1030100e4a10004170600700500510501001145040c1401c0604503c1c10010304004002014004000b410b40044002c0d290060703212785040d0346010410500c0c60500c6081211250014040c0350070441c0151b103414803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 244724316 1250 244723066 244723111
    0x20301060b130504091106280f02010b0604030521070b0a0c030e1c2601030803070f02070f0b0a03140a021c0501050d02060f040b070b0130120c1406 65
    0x54205c80980200003441e41e00e07000c20900a03641d004510b10144070b5074004a54002c809612148070700020039903580c0c1814141800f0080c2034480c41c001a0348035440410040001500002e941003e44208242d15040513030300809900460007400702c0070b0f143d0f500030000c1040c44000d541c0a109111002c0d00c04010080210812503540d64020080321603028001400d1541107000b080c039403203c181c0e9207081100b404003840c00f2031480308007039008030380d02000401803014440d0854402c2490740d41c01d200a1041d50318114440c403102c0140d106100d42c4440002c2e440c0881480b0340c101d08001001c4000341056400c00c1640030000354814014511042203a051a60a001c00c41c001e490480e54020000303598404c40e602005400e0f40200000808013004001c00140b50020070013401d00240601d140621035894259488800100d8011891031003036a20030011142040d178004500c1d054001c84602c410004070101038900891240001e07241038109000b8406e20440000c01510038056202080d04400300101d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 244725566 1250 244724316 244724321
    0x8130209040812252102090604050a15030e03030c161e050607093c050907050421200f031006030507141e0118080a0204050c160605090a020301060b130504 68
    0x43e80c4c17490301171019180050440d454001e0000381400600d0035240039a210700050515000f607010900485103105101d04080e0540310700a0140a200b000d14a5840d041e45941c0882c0305003211300c00f180503003030003401c01d101c100d071002c0c8240e209901d030f17a107801000d82c181075659030400c80c0c0c50700001300340440c0800d42e409005112801d60b02060211503007281c0050000103407811003246603100e40c1d42c1c001c00196595483d500c003405a5065288c442c1d40e50305000d039101009801d0554034003010302800082001411440301585110a4007005c3d01146201c0d10020342e007260503101c1540c2c50b10401c00003220000883d481041103d12840031140025510000d00e45171031381601ca1310394400c4100ba00c003204d0000688642d00400300c140b410104c107104ca0003070000d8418141d00240e84507030100c0e54900c02c5040c00d10074140c00a0903200391034204820600c00d60300400950354010300c81910b400101e05440300400810035010780c020000d1001c0ca84603985140e058000c01000e03a242042410300103013504080c0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 244726816 1250 244725566 244725587
    0x1050a052202060702040e01060b03040c0b0703080f15040c02010218030d020712171c0c0c170a09090905160f0f1502030c0715020d0813020904081225 66
    0x12140d5100c821a0741c2c00300301058000440982c1c00540714403450004110a108001c0900f40f0020225100e090a04104440e40500e4010740d04540f800c00a100100390410411903000c00d10441e4104203503504808038a0b070840781c040864000d4101001495201d4042d0007401705e19403509451112900704108041e915440303240090b015800485003031140c0001081c00e2641540152040034403c03412901c18001548001c542000f41091522200d0440825010708a4601c0301490050a07900054132248440001d0000340002c078040065440f403840d00800c8a00000c001030f100c1000502c1c91414100d88410007410f0100e00c11512110104034016100c50388015940c07000b06480d10305082030040182070b6415611102036210910103000403000030000d0134080e101c9409035100d0030f030100f0f102905d8800040548014010343d04100240c603041801d41c0c151403501102c1e880c0180d01c4a0a00340043d2281c0300300c4206440100c0d041000884440c42c2e80600301c0895210314203104044c42040300c80c92183c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 244728066 1250 244726816 244726861
    0xb0724061a0301050603131b030803040c15090603020a02070305070b09030c0319020108060a0e070309050708010908180406120638090601021212062404030b07050d06060201050a05 79
    0x24004101f00d0131034a00c15006462103003100941c404007081d66540440515403040b02c0b11000001044200800d82040900a04c0d400c40801601100c040c40034200030024010390b030415601095a0010a1080150400540e0880244c40145880d4814500b45601c03500846029200f00c441862607070800040030708801000510f8041d0603901d5a004440d10480580000d52140341448041280091303c5984d50040310a5280002c195002e07103019130910f00c2c60307485401180d1400b81440003255901040740c0340100c0c45c004000308007800304000380003003a6582080303043c2000380121104100b0a50301036130004165120740c20100c545403c2d0912908644004450030f8502001443c0030b0341015141c56030030880500603540f0f882c0440500d41c5564102c036400003806c629640900a170703810001c810481c902d6200d010035640d50001c59607070640e4460f622008000c0d0321400d0010b01424424000e03180b900305102d409002640d55614024060841907a80800302450400482d403425000741104c041c0340003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 244729316 1250 244728066 244728079
    0x60801150f140a090e0303040b0a180b1f060512090c0d06090501060b0309072603030c0c010603060614010e0f0a17010e1014010e040c0b0724061a030105 67
    0x400e90a00ca20b1041a4201030b00442080d0703022480401600403140500d01910041d0784904d440e09118200344400380c440c040310703803414550443d40d8103c601402c10080d004404014251590a02444d041c401210143d031407070344454010544076404401050a4586505805010b03119040020b03150000d1b910310310350080315a40c030a40003504075004030592601980000880310703a101450a001da000704c500401c9500f04120600248184440041c0588450f20900c1da03100002d1102070354038413002d0600700742c050000c510365810450941201c0044c56002609110f900c0d40c5100d41d032020340703078201c040b0f01040e8100301d4521036040844048207030f40401021142d486260486103960701e030494000c2000b40d502ca00303003c0802c240402c4000100002540c001810640d080441110f8a0042c1c0003240400864001d01001c0b0301069040d2044d21124000c0340c1e5984901e280c0500d4081e030504e1200c198420f1040845c10126142d8080821655034201840064402d5403080f516803200340200c0f64880f2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 244730566 1250 244729316 244729319
    0x806010e0f010501030c0302121f06020c0906011b0807030203030f010501050a170601031503080d0b010804051011070204090506060907020a0201080f220f0201030f050402031b0102031c060801150f 86
    0x103200342c200c04413201b06400c1c014a484e000501103020342808849220303007002218139120111b003030b10001000401403403001e403a16064001c005900712001404841c10003002c1407180a5100c0c10189105400d58400b640a994103468500030f03440703800c11500c0c0c07005034008a0001800394011001c503540100e00307a64000d07000074803103641c44181c00c0280825042540e1040b40760410486a1032200103035005002a80d161700c10041c07600142c501c0f66907034504004807081400b000507400540b08110211840e000301e1690b00840b542d2007103024524001e5449424483c21100784000402d4060090000740c3d0340c085541d0710750105aa8402a03000000d00150030702001410214080c4452600701c01c0c40300a04c0c04007050140400c2c0d050445200641d000c8140010f00c00441d80c06106049000300d1000c0280710324502600080e85a030004000c45c03d010801a04680007a0b04c2842250000345039006800b85600c1d03d9041031000b81440c0c025516150300c0e09062000032a4032140c00320407612000c0304081c2c0d02c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 244731816 1250 244730566 244730569
    0xa030309030e0d030216080705090c2b020306090106020f03180a090e0304090f060e15040f180203102c01060803030a0b1309020913020d06150806010e0f0105 69
    0x600e40c040059040020720708844680369201c07855034203094000c2c0d0060031002e41d00d1402e075814a04030f50203190107030300040781004503403a101c20709644542280303882c6448441c001d001951848a0350b2030005042d4820810494442241e409180208001d54904046a032116403d9079134952201c0940c95a90092082d041c01c000c11014504450f04068000701205946103c03030400d452101900c1102d07074002140c10300510100e48121a625a8109418458103182c8140300c0300012005d040ca1503a15a22840900540c8450304803060040494000f04000784041d40743c4046032082d10f80483c424020446001d00c1108103000e1034031148010030311814506001c40203001001008261100a035480d41c4001440800c01e0000e1031060740b0081001c200701c0c0c2030384104803407004055109a203c2d0302c2d00c0604030160b00c1e42d4921560159010121021513090350001441c2d0000701400148141d040002e445d050511545154003150a010201c4106076203c0300400802d88040303507001010340403d0010840d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 244733066 1250 244731816 244731821
    0x703140312130503040b031e070c02150d060510020f06090109030c030f26100b0f190c0b0420010201140109020f040e0103060902030c100c08030c04090f060314030412110418120e0a0303020a0303 85
    0x45237052100058041d0b507030790104841c80706814504c405600300c0700780418841030600410743e000001100811070815269000745c188a50040c0243c00c1012048900d0301c1a4000c4c0490841c030f441d20214610341078040c0d042042414002c4070381c909880000d100000d561910725007070f10306170076002c0780742420b0034080840d07102c0c105a28101d26081080c07800404c004121519041c0d80101e000340342d118500b0031211003410441300c0c03150a0504581c508003101d045079000e0740429043d10b040b0791016a45880451501c0036034044d0350881d6201982240001041006680c080d001ca10b04c00c2e4140e40c2440100000c0000001307120703010001141e6081c1400c400a24900c00440e480842000018101170300c1d1840b00003101c0c4c0b04d118156000e0365801041c8140011031840c0c2c1000500c94000714582030502841221034550544d005281561a050300c0405070b603548c000404214403078a083c0100d100506000d26640d02016510010414a041050180c18011401d0060b6038241d00141594502691b00b01d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 244734316 1250 244733066 244733077
    0x20c030c0c031006063e0105012103020604030305060103020c0102040b030f0c0304170309120a020114010b0c07050d0204061a07060b03030f0433020703140312130503040b031e070c0215 81
    0x1b0030005021002d42d42c541e0b810200004c440c0702c5000003804c2d81040c0300500d034066140c8400314031200420100d40021740c009180e079845070741450301049907151503005034040e01520484552550011902090418078072020310300c6100c035400800b003251501c0c038036440e09210130b4030040c2c401ca000c0318114211074031581c011504540410200c800445a01c10203c1071038004421410050751610598003800c1c07140c5188902400800902d00e10340040c0c0d01c1c503280e468020340304960084070380c48900029540c40b580304030010912901141503041c1942021a0503602003c0e048804500d415480758441c01c001003980c9895802c1c5a040b490181840900c0344200f4013000001b500c29042241c0b614119050741c201d190403800d0307030014241c41d425440c0c21200940400301034070076039205004070b001e0b521a001800781c00080300400b00b480340d40d076418983d08501c1180c10490b0020000418482011508820000100b80c00c41c83e455031138442d84070494564944d480040e5001d580c3e100c026010f048803100400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 244735566 1250 244734316 244734377
    0x61e030b041109010b1209061515070c0602011e020f04061209050a030e0f09150f0d0c0f21030207050108150405010801052d0118020c030c0c03100606 66
    0x1411807a80758001142010709030044041020b021880a010f4140e210031507410441d5800980442d01d4001006149c203500055801c1c4910411a000c1d411076100b0720880c0c82840c0c1050300000131540390341c0041d019042160740c1004011180c0e0880d24410346a109640012184054851501d460810101e500d4005030310865442a1354101440010f041040032010141c400d031170740c0c00a0280d0382c081118221040003ea4041c034424030070402c00100f5110500d181410803100d802d010001030001c101040c1d0f004c1d50041040b41c040601003134075584048110100d5903001544d50404c503a0903400d0450303a00b50403006016a000f4442401030b580107807c103c1d40403801040c80702c405651240010151402030303100740340e16551131081c8641028100c000380400045500e0440c032005550402c081181414845ca40c00315031031408940011070300c2e4044035400e1880c48103c03a01d489244840356118896500818402c0c460340c00c03015944240742c000d42e02142d5417920355419084804114400d009036646040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 244736816 1250 244735566 244735583
    0x819030302030c0904140a0f0e0c0607050a051e0c0a1d0c1905120105030109020d0f05010209040c020f0f0d020723030d0c0b010503031602060a020703210201061e030b04 74
    0x4c0341d41380c4a500c280c401c2a010001100094201791701c0400c2100d21510500c1091818105246418030001410f5800c0d403d05550465448215042c042e007080074003034005106002d403902d85000c40c0ba20442d0780003d41d0424080e02c0340c00504c00200721030400d10b031088079110004d000c160500203d10942503a03221044407507042c54003003400e040410011010051001040010854004c0c031020881c415024020940003001400e00940000320f14403640d4200910319104142000700300802034041d602d030600040c0003030018031403130400651150242c207079001461207950010522041c2c001010301c800c07105034002e02841800c0929006080304c00c045200d40112081f1121001901d0411003c1802e2080b9030700d024006000d4503001002c040c2c1a480b0368843d5000344401d000b891801040000c4807035046070401c0e1340340246107080c0d007888044c1c0d1020704151095004140c00f0340035860424125540750f0f008101c5983c8840113400c40f00c0440e1a40d049480c6a8002400010320340300005400501400c00c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 244738066 1250 244736816 244736827
    0xa060e0109080313080f0c011407060207050a03030b040b09060a05060a110d050405010f08070813050f0106080309010e0a0806060d0c090c0201150b0a141b120406090819030302030c 79
    0x255407556220036403a121640e20400c0030466100c0500000c0c08006c413240251800c1c01000000a140c42110029a419200005a4001045001c3e4100c072115a8080207580c604010b07400d0150042070000310700341c01341e82044484c48942c030300b800996208070b00041c561958103042505101690700600403d50a2001d2850600d492882c20007009a03210001c3d914240d40768200340004003042408900b0000b0310000b90244440503030024400c6600001c008541d18007480309003461458891564030642c510351170701c4004180d40d8808802800c24202c02c0e200c0311000030b40c2c0400c0c040c80340ca50303210750090341d0084000f2440510b09105900c1000d806038089a14040d00e40807c8403c9900244005025039551000f81540990040e80340c0014018040c0c140d060058110018040c1081e5981d601c01802d400600074840b0301044204010700c0704050200d42c400c82c41d11010b040b83c1e034001c2c02820049045148002404807001811441c9000d5014401c01c0000c032035031b0140d0194002400080020340300341300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 244739316 1250 244738066 244738079
    0x16020109081801020d021209060304030e10031d072301020109020916031116060903120603080d140c19020c100c03120b0105070b060a1a0c060606090a060e0109 70
    0x141c02e007111582d1040e038244040e40c001a281110311043d1a00b590010b1103510125120003042e00c0e03448005988072a543e903a40c4ca0201c0d9800403045c09580e025520180000c00d4950644c040c0c6800c034401e2408c0140c0003402c42000356185118442c1011740503800c0320000412032580c005a4400006000205401c003056000030943c40c070450f4071000d40c002c000b4411a01c01d0381400384024594070403244510b81000c0c0d0004504400072940e002e0500c54440e0041d008040c0b007400d10070054042d01c031041100701d45034906251107512695941ca1568100b10072013440404809240b03004078801c60500d45040905188103115241d00c859080c20b40c01241c143e401240c5a04913880081480c030382d40c10081902c24a005403070680c44400c00d026851529043c8144c698000c4111121160444403440b455a20078002620b12805604010591070802c4100a070000034140907241c0c0749003460681e40d0b40d0762101e060054038020101010360103544000200003083c000c00d08000594018580003140f07035251039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 244740566 1250 244739316 244739333
    0x1104090f0f050c0a0816141b07080d0e04060803031308040504020301090e0105100e07120209030a03170901090c0b0307050712020c010f020f071703040f09091a090616020109 76
    0x1e400d101c03038400002c0c03d1361440c1ea210081c19440300e000501c0c8000700c4408000100b040d8603140003407851200008000c0f00f0003071070b901142560751240085405054840c140035450360010151080441c0048410f0306140c906800785d102a0340e503500045045a0310500950f4015100306010364403402c0400c4042115200c1d4002076000e00400c903000300c1c0d014100403200342120401040243d511808800900c410020980800e810000e1441c01107030b001c01e0840c4820003032151b280302a600d88500c5c40031104064100c004c441c5c000c01400c15007107103a1f444040d00d50036200c0b4400c0040015082e02410300642407568069a00030b07a5a02d40182041c403603584507000715040140c0030015a01c1545101c0380c5603400070042620340040d00c0a0041c10120b124600d030b5414003400348030020100c0701c55030007090f07104006880040c6a80055400055610340c4148002d04a59509803003980040d80d0840c040c0d08420b20703543c00781030000010442a40c03180381868110201281010842d521005a100400c6145 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 244741816 1250 244740566 244740571
    0x518060919030b060114120103060f0e01090b040209070f080703090f29011401020a15240815060d11040b0604090f0c0c03080f07051c0c09091104090f0f05 68
    0x407840c03d04103080c92070014024100c60442a0a09031b400c110304404039026035003e0b81141d60010b004103001440c500042e003e04a100103145080d0310303104890090100101d10700340554000d4a2a5001d0703203600c0400c554048104c03000d280880c00705404036204510a50121012074059441610784102d42d0351f41d02c100d088012111b22030840b81d200c400c8015080200345500411405103500310b0148054000b0352a065407560240081604851a44100c1c08036003000c40c0c2d0401400c103680c100d9071500d0001d01420305501940c03142d442503a55131112003a4401000e8040d1710014400c0264440c56560b090301800d441912a401c15143d056000b00d40d2284000742010309071007400070503803201c5c10441e02e0840d40700000d07000801903c0c2c80e5190100c3d400101d10342d0011a0f000308400d0f03590303d80006488521074450005001c804008c485080e40446600c202c1880005603502404141e80700d030040241c07898000e140d10030060820007004404486e40c000c0761192404100032031104450680c210484008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 244743066 1250 244741816 244741823
    0x302040f06110d0e030a1e060204060f020c01030b01050d0c090503060106030e0c06041a0c0c100504030203010b090c0a0e010905040f050103051002070b010e180703030e10051806091903 81
    0x590019030007010030f0115162102c0340389002148000400d0010380d58000700c00780030b0840c100111198004511104a401495070071242c20355035507a460300018400541f0822840050141e091100120740c81f0340a800d550f00e030160348132030074525100c003e03e0041c2152a11442801b1441e0700000e15614248001d9008201e1a100001d21a5489050a0a0a07241080c036481075000704014003410464400c0211000d154015040d100d45c01152040d1030514503030509607001d06168452401e03681c2c081c0083c41580d1007503000f480a401c900040c07000550050f40d001013101003d10103016040d1041d0180011101e05140c0103d0740c0e035039400801c0843e02407110180c161034a0f08018400c0c801c040102d2a94100000030851400c5404d80301d101440c101805181c200550744030100e5990700744854054503411110080d81d44043d0340b8900034001042c581d51b003a0048903900200310030303a40250143e03040c000030f2200c2c00360b42074000c1081054550202080315070000c404620000055980d0307480d80e016510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 244744316 1250 244743066 244743077
    0x40c051b060105190806071107091107060b09040f031b020a030f1208070c0213020909130b070212041a19090f05040e15040204110a031d1504030509010302040f06 71
    0x141070034040b442d03038104c4a035400e000202c00108640903000030328542c003401600e8500c65501603d01d21508040456010051060a00911400c00c15006004003403051142804201400f040b6041c8100c6070f900f20b034060030021010b501200424003030454030500c110b50101d01c5c000031102d13a0004540d2211a082a0780300201803040b5001c208544100b01103c0354141444082e9243c0078800030300d11015108002e000c1e82041c40a604040010f0701a83c05190004100c481d6a15242644001c05c4419000558046585501141d007503800030401ca144008148841840d0506155880c105000d0800ea0480c03100c10401c52130113024640e018451005486a8425900f0362a04401c2030746a003581d0402885036182000c1c001d21900c0000e907625074210017090342c4056955500019000f01080d43c2e401d14076101c0040e940d005150b141d40601400342e0f200c02c0d1404007102d04020995240d50041001e21407440d21310100780841d0241e809021001310502d8090f01d8a51a44000703010910b06900c05800b02d0f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 244745566 1250 244744316 244744319
    0x14071403010e07050a0317040504051303142a031603020303071e080712060b0a05130f05030a02011b06090b0f3d050325090501050f040c051b0601 64
    0x40d0a01424402c856044000c25410341403100050b501c0d04180b00040c10801c11140032483d11300741d90140da0041500070300820583c60100010b035410302000c1c40440008211040c04030440e010007040d600d031600d10108140e82101c0e2210885c901126084031180729110034041d81e5200001400d145000d640f0a81c05580c41e13052909001e040c0f51440d1161100c4011075443d0503060542c82510715038450981e1401c103901e0711650085030010030507500900340149001a895010b40e070407400900101c0c41e2524840c240d00d5498400c4c0e005107038103005099068000246c0900036620840d80d26040c03c5034002c000c921a14207680c0d00003110120315040b074141214000300010061040c3c8401d921240030480300e10051000b00c40b00211864802c401c100406e00d64445420405040356868080c00015040751103503980c0f040d1440e0f03010410360240d20007038041400480e804d0031500800e8101d0310050070300c000103500c42e03040001905048a41004000c41840000186013240040c0300700c2c442000c016281d03d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 244746816 1250 244745566 244745569
    0x603070903140102030f040b0424061a0c070b1309060f0609080d0c0323030a0506030c0a0609060e01030908191202090d0b0601051909061701061b140714 67
    0x22060318002ca60540d105101300103400104c2e001a5034819441032241400355210310303004400c40d8008282a8641280c0d841c00c8141890030750080b0161000c07881d0803511860031000300042c62080000080c0725401020003004601009809440d500310a050002c071f100c4e40300c0070441d040b2007140d4010500d03214003030401c000b86504489008040d2a015000c0c00710350f515000b001e03100c84ca000f00001c00b00450f11001c10719020f40c0e419158182c200e02c1101954908194903c5805803406491251080c0200c03a809407042c503000c4044070440329191504040a403400006940b1020070706480c0d4181901d40b42c083c000104440b0040c0240180f1078540d6050f107004071002001c440c0410b944055440c410815076000d940d42401403500f8942c001001c3e010351f911600122100e000d034014118218462800701900103420403e0602507d00b41d545201202e4000c00310319071588000e104080c04280c1c038181540c1060a120f1100201038001c41e03003030b6243c40c042d00c1c01c50310b440e00c96440703c000b801c60705100c03001a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 244748066 1250 244746816 244746833
    0x5010b010f0305070518060d0207290405060c0d0b0a03080a0801090e1203130c0807030b070804030f03090303090c06090e0915070c03020708011812091401030b0406050603070903 78
    0x34009600c0c040180c4e2a0000c1d0161039445410300034400c1800304605100b113680c40404540441c9031182095444000c1864024000038010340e4149070a55600d075994401c00035050b2207440380350001c1c0181426111100f201030b081d8003d0710042810750b11100c11050503110a900400110311400c61599a10f030306907030042039108180c00c40c0c90940d04207001c000420000180d02411400d900710107540e0790301c0300d0010a285182804c002803400c01520f400003110280400c081040780d0041c09089501d83c0c1d200001c9440400440e801030100c2ca6012080014034440c1c0e00c81030f01c0603c00d003800120001581c8900d41da1440f00e81c045000920040030a009691483c2c0c4140e40111254008044c076402c407442c4171190020080620082000c01c0900c20141442007000d200200000c2d802000358004441000d0880d00058400351784c0d00003031400d01c4800503c40e0b5880412a030344052201c0c03001228600440290940c28482c07035101c1e4031803201042d0740c1c0e42d01c03005601454107030b141d41410740d1079441d08584 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 244749316 1250 244748066 244748087
    0x7080c0c0301052418010306020304030f050913110d110d0f020408060105060a050708031003290c0a0201020c0f03090a06090303050703081b0703111902010509090414030705010b01 79
    0xba41000148494001404103009000d801ca0714100407110b10800441c4034030540f13041284600444800001c00e0018660003940290301a40d50741286d0606850b040d1102c0c03040f22581e54100728078050403100c12085071f10000e89040b140341d01d10b180039a0350300e0302e03000e03503460754504003000000050807807d05185201303180b65521002025800c15142000441d12048140b0900b4010207000886485441c0300d6011070f22803a5100800c81d80360704003090b1042e40a1414002204c0b005170144004c0a40d00211004010070000c0d072200d501c2e25511249070300450780201d501c03032082d90740a000204082c1c40c14840315174403401c130200860301e80412900700010045c2c954000b10520401103402d0021a5103c011100b40c0d541500300310500340c44401181004500c402e444c0210319a021500800b010b9100f4085a108203081b41141d00951002001c15400310304483c000b07004c204104041815400e00c0f040250703109003e000121f02038141510b600e03007503520182084030681d40d9000000c28079a005a00f404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 244750566 1250 244749316 244749319
    0x301031b0e1e18120306060f0403060e1b03060711010b10020c030c0603091203040201020304030602030408070b09010e0304120c120b010f4506060e0f04140c1305030307080c0c 77
    0x90180403078448513448000c0e541c8080f00881002001407003e03140d20040300c1201c004190426074581c2d990811100500c481d550481c180d0107455510182d00b866461120600140207001d0030380c030303120024203458110601c2c1d1000f219540b00c4102c20743c40d80e264882c0b4801d404650f00a4140902d2103400c02d400c022125a03143c0c1710700780610610808460018002e4881220000c40c55030300e4a0b2800107070b145004503800100030710700000c1000100600c40c0c000d04080c612814981c251a200c0c0c131452400e8840008250309a0b40c001e00c81003004002d0204e00081c064020403c0014103500e900b8241081001000284c40c64910300c0c004100382d6211400e070400800c0340c5d074240714540708488105401a0034000c0601c581a0324010b0031002c58645114400700b00e0807100040042d0f980e140c1029000044040303c0d00c1c0300f0700750151519032500340f60003a100440c42031004900c0c555a2a503006072181c21400c42c4c0c000c441c400d58404070729600c0800081c85c00600074064517444588081c4114039010014221a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 244751816 1250 244750566 244750591
    0x7090e0109050309190312030b09060a080c06130b040905060102190b07080702030d060608090c0114070b18070305030706050106030905100c030f0524060f0301031b0e1e 74
    0x607404204040269954003000302d070750100ca001d01089049054601d0740000e0220824500009032403078040d072101a0100050316000002d03600c0104100c100c4800b84124412034111a221f900185440310041030382e500b0302e140d021912a11061810b103980c0040c2c01c01000c103070342e40e020300011b036070100f01212a419108694500d91580d980d40d81052850140c02c2c0360500540d83c1c04112840d0092003611713607100d032124040122580e1001c00034490041a200b1411701c3c00b5502003445035500c5070a00c01d2840c6003880440c0d240028036a0744401c1c44100038201002c18810074501d42c08501d080c0075507001140900011500c85480d401e0500481318180d002c2c005045c505000b1070000f800109902c4024409910300080700c03017002d0b009401806290580314040d910f401c0030040983c0300810043c0460003030001c1800d951001000b40800d51294103041c00d6010002c1c001000000c2418103c0c0c4001411502c90341e6a442c1d485107a0031000200b900c0b2a9400701c65544030a50705000407203819442044480c49 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 244753066 1250 244751816 244751831
    0x30c11100b240f0306041e06050909030c150606070b0a020a0315060e1210060e10090209090103081c02030a0222050105180a080f030c060f0103030e0d020112020c07090e01 75
    0xc0800d80f19490000c0200c110100008200e41d46503408081e040240e04000e540040c2d5010750704004240034080d152181d020701700420000180003003503d4000036030100500c80101415240445050010b060320750103d4100038072000206c4c1d2141e000e009010448002d6101c0c0c40228001d42501c03a81200c017040e0380c031070700010003c0591110903000c60180a80d00c16214580000c04142003080003d80035801e0342c1002400100c002079144920311420110152140003034840d41800d045c1c2c82210f84082d80402e0020061001c203c10f05c005050f200d10a100d010400c80c00d2504910a0381c104540203524268003041501ca0350500800425070810700a1188a0403810400080c1040c058801d80d511940b050255112103030f2140600f00014000782001c56109100500381681e41e503028000302e0125000d11404500300c600c012668034142c80d811f8407001c0c0d04510642c240b01d842400c01000340c4c10408000e802080130902e034401006015203c4029009143c03d2038202010703900360b240c941031300b46c1c94442e6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 244754316 1250 244753066 244753129
    0x10b01051206220e150a02040e06061605070b0705010f0c12020f1b010c021b0a0302040222090218010804021c0215030a09060605030a12030c11100b 65
    0x607400b070000c0b6441a10146001c0d0f07110403030840342102c2c9400c03a18100450404070310008203019010070603080b191295544c990501c00340e000d1403203803a0a16901e4004034580d4584400502243c11080f502908880d07001c1d01c42d03d14002050b80a944841c100003001c0081c40028080d02c01a0704a10409200985a10f20000c0ca03a4101050182115070b0220307100304103e007000301f16802e440c103c100d00c0c0101c042c0e000800e0300070401d84c1c14107809441034041030b01c0031b10a08a5141d101610003414419050315680a1001a42c0401c520303600c121803070000700c8000031603161818050003a4040c010703110002d2900d44010b80b2500c03400c1c0d0341480040350170480180d03038100818440480c5001d00100e0018244042400c1402503002c87c07104000100c01c1003005071785644034481003401041d080c400150303140245611030580038005404408468024142e081c02074018005181396464440308141440c81841e0821b140c4241900c03104c1d4880307404032000d20307101042d51146041855040000c1b000030301d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 244755566 1250 244754316 244754347
    0x1c0c0b060405090c1201020c0102040e010609080607020a30020a02101106010302060a03110403030c15020406050901030e0f24090f030d0f06050402120a0e03190c0c03020a080609010b0105 82
    0x510903100f2000c05c9010038080b0300a4064a00e9101090000c2d0b440d1601d0b5040c00d100381e0400d000741400903410707580002d0781e0500040e000d400703000550060800d4180545503404607001090490030080e284040c1c3e900114030003800c101e60019240d005c0d265040c61841000b800080d00040c910070031800d10700101d070b0000040b0b1147e044039811511642d031180b90302d10035070292000d0740780703508220404500042810b03040503040c06403920602e100c03441200c0d201d101e40b0880c0210f00507a40000e80c140280c6602c0d5020b0b5000c00340c07480020040725408501d007945c1500c0c00140f40c5002e40b542c2c0401c0e40401b101128030f4203c50b0000301e07001c060003025074500a203503640e00440500c40754503500c4026505048010703030310160107024050800c2d540e403c9648170700c2d640c414064a4902d20540341080c8110300704008025145d44031006d088202c445a00d59404840b81d03807580e038056035030b018aa01c0010059903060018801051950060b045071700d01040311900b1078180411407814030400300085852002a00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 244756816 1250 244755566 244755583
    0x6042a08242101020f04090605060a09170109060e150901050c1204080d05100303020607020c0a0b0706060e0a0e0f0c03030a2f07051306050a05121c0c0b06040509 71
    0x2c0c1e0754a8041042500c400da00c003542c155002c0040d510004200c08158034840040041d03481c141c1051011568070801d1001700c1c8a40b409840011b445a0402d000440840c41c0900524800d4000800c0015184e00c864044500f104000e03001644000741d07229200c1214050a60f000840030003c10a07481c150715003204600c00c00420444034076008000404000d068000d41c0c110a1072902c007001b1500e813542c1404a100070601098015100300d0000841442c800503107100c0056010f80300301542c0d03280c4544010160044002110025125034002c02c660407401d80c20380c4920001b55001c90b90107850700c00c15050665040c100d0265811002d08080d10307841c00000c440710442140b811541031000700b82d024407003643c400710b11001c550300050352010742040003400a09584040724014103440c0a88061400c60309184505a00880c1ca14030402891910301440e1030711b80c4c0c1e000c01303840094990b850380032a0783c8a03040071500810014082d5000740200d90b80300b00d40c06401a40c0411503410620345244e07661062 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 244758066 1250 244756816 244756819
    0x609010c020d1a040c0b0a0c11010c0204022a03070506040b1003020603070c0308060109083d0c021902091803090a0b09040e01020f0f0306042a0824 65
    0x520940411034498080300300500b500a1080400f80c4103031296200c0c03001003a20300f41c40e00c50010202090b00084102190081d144a41390003016503c1c1d90b0384c0310707181140ca08003a41841000c1407c4005600c07140002d10b000a00c0004546030308221031801c83c41c1d8009426041019441800030300c0000754002640b540203a0040b107029003070758589440013180c00391500700035000309002c82880100e903081894095a14441d4843e60559501d2400440c1c0f030300f83c2071044030890f9004036100c4240203440303506c0c109901010354050300c075154814a031015001504c1c2c2c1810687d41c0d0348001c50086541801012384e0040c103442c12004102d401c0d00000c0c20007402500c6016004110704490086020810484034211005040c15049655444442c0d00c680c10131108103003c3c40c2030400d0b0b01861141842110024400d4840325070600340428440c441c1ca40000b090170307070041d6030f8590030001d42240c8400b206880e105c00b0f451140d034540300c841c020603004d0003612603510558070001744a0b0075a464519800f84030300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 244759316 1250 244758066 244758077
    0x30303040b10030611090306160203070209040602040503070f0e07080c1b0a0b0a0e0f03093115150c020a0b070f02090f0601090e010b120405010f050a0510090209060901 74
    0x2038000c40407000a085030b100030800d80c9010104009503400c800031b85100e61046041c0e590b2651075062485100e445600c001c00180c0040203003100510303196084580090003040018142629580030a15060440e0401c07118070400c01401c001d51110b03070302c5e034540c80b0b007091410011500340120411200c0c080c60120400054020514103240d00303041244480c2c0540101c4240d089040a0945c0c0e0000c0404a41200b81406829940760140741c001044030302c2c2406c06000100c004400603d100b0b44140302c1c0700f100b1080175140b4224030f0300d50080d02a450800032445c10040540c4d00e00407502003040400300f4282c6c144003012056401581d40d024a080458501e145526070701e411274030745030685940340072000f9801150802072282c074101626449208034001c0e04d8810000fa181c2d07800030800e190900c1007030201101000741000c809c2c1040059a002403040c000414540c000d40811029a4021502074401e00e40e14000c22141000d08405180101140070045150504542c040b40440c0300e150500ca05004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 244760566 1250 244759316 244759321
    0xc010f120209090f090c0607110108070c080a05030f09010c09061b0c0b09090f0c030105040b060c01050a1a04090b01050420070b0718050907080601120c0329030303040b 74
    0x5404071000c540b0001e00c0c2d00c0c141e02d00b041e07003200c5100d01510b24070142d1003200604c41d00c1d41090303400c9520a0350801c0014107884c408400444012100803c0c0c00104071001511754000351018000d03001c210055240c05440c0c1c9040c440040440c01c0082420340961705050038500034030f030481110815581da600e095134004840b01c0c01d8244030040200020b040302454000080c0c3c4c40096000b51076580c40848060091762100400e50f04006c0742030780c0c00d1401d8030080004000c40d10302a8000d1881120207000c15060042c102002421600210390162076240c4131420444002e03210014003a00020031501046800d009442c1c9001c3c1c00814001c060240340c0e03848500c0300380f04940000020311003a44e1441e42d0781d010249480300d01d9003005e85800d00803804075500351180e0006509803006480c005403000303005a0f40c4003811901e02c00c028119505011941500c0e00d00000c1a024614401d05191404a480007151001c0c1e5000c8084124040091622444c05c040d503540201c2100e420640050211a42e80c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 244761816 1250 244760566 244760597
    0x131a040f06050310020d0509010506130b0a0b1207030b030d0f0e12011509061409040221030a0c11040203160f11100501092a0f0504030c170607020c010f 67
    0x41c070319500700a43c58881c94000280704506034004281c9450f04410920054450082040c261074055801a9000f41c00119501c1280b000d0b9002c085600c0d00117010030003459131400412170962100708d003a41e50310100700c10801550380601484500308402e900800703100481c840003e2010b00114030080c10400b010400000c969a40020b181c02d83e44040d0081203c1e0710318a10000c0c000149108441006041601c000b50f00000340000440c2074001500f412181d0b84c0380d500300100081d140701c4e2400c82c000c1041f02c490744168100080d210bc004e160300d40f20030b4240607081c0300122201e0825418881e82c0108200003020b62448600b040e030003194284004640c4d1010801c0d140c108488a07011010f1060b00e030826190820340d08183c0c12500c88000802c070b80c28000134050110140c200c2851500c64054040c811114814004190010943e25059050980701c1e600d0b40501d00b180d52010250302c40c41c4400101e100b809004031034206c0441c1c0010038420704c180c03002811012510305254180700d0f5901c5e11031001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 244763066 1250 244761816 244761821
    0x150a08030301080a0c0806060114030712060e01050f090910050705070f0c090608030901020d08130501050103080a030c0912020f12030307020604030e010f1b051203010311131a040f 79
    0x5419448240c81d240c0d03840d400100e554100d802016100c00e4001a000242244081141070007182d040c2d595140e062810280410b1075031002d00074108200c880c00c6d140c21541a24420030000e44410f00d40101c0c0743d450081003100060840d4041c03841424800144050803100184c41d48030b60175181400325442e51268000d844901400314041c0a0520712080002001440b100c9071040d42c141c51410442a0745420390306589018080314607002da40712315403805145025110481d8000004450b9012000d01c40d0b40306801e5420aa004440c0c410020545540341c98050050804003200341ca49035001602d0246415001e4440c10400390154074401d01403541d035111150504c0801d0b03129003c0ba65031b401c220000940e5514111010750000700000310a000d00d40c0b207551100c050714190790700c03540480c8102c440c0001c107400c0000110b561b4031801031800b08842202010758000d5002d1624214230f1024003050044004103114000e050618108500f200b20402d070902030088a42507900054940003010b10100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 244764316 1250 244763066 244763069
    0x1b0a09090201140708190504060f1107090e010204050f0d050613050c0607050606181512160803071b1a0304050705090907050427030c06020403020d06020304050f0f06150a 75
    0xa80d840000794134041c0100a8001c14141c48401888444400740ca081190b142c01203021b84c90000301e508002d820300d944a666584100c180300070554020903a5400300004803891803071003c21694002c01d041165283c5810340031b08540080c1c3e00c803c3d41c9105030f940c15840c0d180040c80520404903d070420b0041c04420055141c242e800501516038403510340c10403136506e800844055124100425422850701c00803a0068000d4003030416546400754201d0420074080188500c401d21442444401014925000c581e40c004040707140c055540c0b4021820701c4051205004c0000e20300f244696000c00c5038025100344001c40349240039495032280c9981c036045003009015408164000700702400d00182840116200d0700312102120108002090709185805260450b03910403420720a6922a501081c018800350240310300c81c5800502e41508c0350700044640480301c3d0182c80c200ea002c0100310400900b0420303030400c21a0b510080c5940b062150146550f0100200320303882455054410009985465070340c0380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 244765566 1250 244764316 244764347
    0x9050112090b0c040312020d0f0c020f0315060910030b010308071505070f020d1805010806150a03020406030c03021207030e0f0609030a0e010f0203040608270a051b0a09090201 77
    0x207400c0d0401981c3d46001c1e802602054682c1c2d40164440d411480c00098010805113054607100525105801e0503180e100d51b400d41aa0000c1148600101c10b64081c0b101c1c65598000c11415100c6041c040f040c421081001000403d400b031811400b800400c080a075242e0460707911101140e507550180c40e141c24010740f2171012071612810001408202c6400061190050300e8603421a140c9111000341140d108e84071500042400300c005505000c694491201c00354001c0c0098a07005002d0000c520769641e940c001c82c18100000e80c041002e11071298580a40e408440b82c43c81c041d030400041810104030804041c1c210b400b8940d5903a001c5d1011b00060105e410115082810b40f203161414000040e166400101c0c4a00000e90b07043d00781150f9802810300c0000e5011a0740154206414240c003036600c0200508050b140544078008290300140c1c42001c1e00038560984040e081b141d00c9883c0031403600400c0c1b060b800710041d2503200f084154859030524001c9500c41c401c0803c1399026070005a485031080d0001e003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 244766816 1250 244765566 244765583
    0x118180605061303121b0204020901030e0f0708060601090803090405070201060807080102031e13060e010f110a09060806060a2001061e0504050103170310052d0406060905011209 78
    0x78000d1646002c030304021240941d40c000f001c2108081704a43c3c800740643c046002040c411060005800c0035400740c1010441810000788006a00c40d40614203101043c0c108001d0344400030907c94080b090200603002002820500c01031401c012815859004895072117000350f64850000e640e00c3c2c401d420240082c08407a05543c00039846041e01070107940119000e8007480e0901c44a01656640c50580c9403150004c180c034003c501240e49e5454005d4405450448415074a031140d051403c801441000b54180c071130016903a1380c0160b044041c0841c20503030322000c184080702042081e9174580c9811034103845868901072200c2c0b91030f102c8030300d114420540c0c070f40d01540c600030022034842440100c070b00b2440a4100d002c035000d42c0e60710401c01961401d000040030440088203000c1030074500030107550000c0345000d86090301511000458404000300254800c0c0c00207101d1900e01102e51052040391401054030103020383c0741010b1024081242307a00c0b0382410060b44002401800b05140d1081e091242c0c8041903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 244768066 1250 244766816 244766827
    0xf050703020618041b0203030402010c080c03030a0f0e011b0c0302010219092313090602070605070201050a060801090f0807051015030606050108040b010308093c011818060506 77
    0x80803c6a9206025400380e40b904074905111407000700c0100e51024654011451030b030700c503030044901070040d00c000c55030100c052002c0d2182c818284040c41c0301c0e03000448000f480420310707640c01d0152030303800d01c0007542a45045001144410303044204400000341d41020403400d0180c3c6012402446a002c0f40d00c20360611150700215150700c685000b08481450680341e220315004104007031100302c1903200503030005120b040c416807440b0316000508502d0103a4070040c02c1000d0760b141d0360140e840458124006035501c104024100720240300705805020544002c11041c00c142d03996400307a045441c4098000000841c43d4000c0100810400100c03c01c11101440082a442d000a400082074041114107906044010445500c01c2d09500d201d82d81000304045664130f9a110361001e030b80151201504a60b0300c0800140c1e00e50b0a41503a007900103000104922100c0382002c141c000e24100c0402070400c010382840074030400d8000740e4001034505c0039200025000f5440300010084c03010f944401c0e0483c001080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 244769316 1250 244768066 244768087
    0xe0601120e011d030a0203090d2a030204050901020708030a02071412070c090203061c080c121b1f0b0d020d0807150b0d060f090606150f020c010c0f0507030206 70
    0x3c420310f0ba20038000400b42c0003440a0520b6160b006043d0b40c0c60040e0b000b0300003180945405400e0410860140c0344503111303040503101d03001600e078002d084035441d503004036020000c5042a2113440d9005041720300031428250142c1d1f545000d4400070f002458260340109558080c061500d06805192405504441440290002c8114141c1280a05582004030b1145c000755000c080e008591145a000340355217406c12090501d09424400300300181e454400500c03824170a03a4080008007d28504000341c10713181c3c01c0030b500200040c01030750580c030b041d6000500024075107002c882c0c11002510b440100403c1942c0540040f68007001ca8500c040e5200c0c500300e041c50203008004000f000c60380d0180f1800d558101c44100c400c011380b05510002c6c4d400c619641d02150115810380c1c081964003803003060210340c500c040e07101c0b1419140c1d02c0d00238400c5403202510500d1811f0300b00e00e40340d1440d5081d0000e040030030001400a03002a8020402801d00d01c1c10300440000c00005100e100003640e130040500392206490788 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 244770566 1250 244769316 244769321
    0x30507110f0a0b15091e1509040813090f02090a0b090a17010e010212060f010f050901050c030f031810060b0301050f010c0212031b0c0d080c071518060e0a0e0601120e01 74
    0x2c1c0101d50300140f58003c0b403500c2587c0340002c944110040c10f5034140e511349950b000002d900c0b00d0400401e416400d8030102e1000543e0164038083d04001c000946c40304541d01c00c00104c440c0c1d80c0e02203241c0c000f0402c006480c41e02e51100203400c4407207483c0c044900c031030460343c41e5000d0f19514005000703035480059034005580c0090043c0b0302a03082600d0310605c68034000d00548a07400800e400c0c8001c03075802d0200c50590b602c114000c15600e03000805482c04d0205a103002070464201381d40d10320b221001c456a018022404000d04403010461000c103000e52485e0100b4220340f0b100c10300a441c0903082c9501e5a1313001380d000e66694200c850740606031402e01400f80c0d15160320b0b900030010070100041024807040301c60760f0008400030100d100804911041d07403c1d654800702c69001c51094903140c090010006000400448030080d030008903218a81503001407a007084a543c05a00420144114a502070280f43c80d0910b100c0242d0303000e004490030f03548a0100583e2001c00480030919900d04008000000d0001074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 244771816 1250 244770566 244770601
    0x10c050628180605150108010b0a0905090f0703051b0906070303061508041b030512070314040801060306050c0406020d080c0d02040b0403050705040203041214070210030507110f0a0b1509 82
    0xb52401c0002d0b80b200034171816100e1810b602c0f9800070301a8401400741905010041407030b0010341c1080194581da0b0f00108414131000c0318030500b03a50a40c0108009a5058003500b50302c168440320f04601e59a0f03800e41c0c0040f9004800c1024000c60f000302c2e410307080502a90241c000b800034914401c00d0b606242c0c00c000c4c0220011201118018504c2e90040350f07584c206400f001c2070302d5101014040b6000c01b104281080e42020900307600b08401c807003098400888080040c406050350400100c0d00ca4107608144080d520301502c0d00d4a81c2c44100001c002050340071130b130f011030610f45103000c2156482c0c5000000c171034058003804500c81480010f00007410103540c402002120702c90001c5d500c42c00c2e91402004104c3c0811140640003081507624400c002c2e00c5945115124540f1140003420450540c000c2130401d05000c60540c0800c0d5150180609075802039010345a42c08210010507108140080c042d1711003801c500018040302c0d440000c180f09506004040c000c4e14800351000c1d10502e041c0d01904043c8105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 244773066 1250 244771816 244771823
    0xc071a0711040c05040b0f040b0a08070207060914010503040501060b031501090503033121032d0e01020c030123011a0702010c05010e060a0b0f010c05062818 69
    0xc031105181c03141081d009090401d8081e84485007824501180002980e1002c1d41d0b2402c200307001c01c00824079404d100054a5070300541d41d17860ba101c0c68550300207490320500e504054140454240d0402180400900c00300703014200703113013060701e079100c03842e20f60b001d0001798000c0681d100c0c010040000d503801c400c0400c2342c110317000d0360f410389802c0d036440600d40c81c0c2c89200c2d0341e803048c02e07074004100590b01540040d09208101c11150740810315500c1400506551100c0303c00340e49500c007400b040051643c401c8801c941c1d06102500904014920703215507004025a80002042c0080104007045982c0244003c01d11014083c000380001d00d40d280c0344129122480191030201d200200c000300d01c0344498020200c52200e04041c80d854880183c006442c00300550008403695134894407480c25141043c070100740100c20034200401d00c07001020400c480c2800501d030040c10411b140c82e10a010400000f43e841e00104a02d0b01203618034100d80782e1241500d610b0391114200f506280140401034440b40024146601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 244774316 1250 244773066 244773083
    0x10c0f0225090c091509090506091509100b041805010605130b250507080616020a020f0a050a0b03060310020405010804061a0415050312120c0c071a07 66
    0x40041da8481c040c00c0c03801c50a001c01d514209002c2201d00340d0100c040c005060804110b02669402480d8000e01c2a01e0103c0c00107890f517004200e80c02c0325014458001604550144c418a014900d902c0c0b4000c000c0442c910550452006c103640788007540040010b00b1030031001c16512a10384005404220808580380d5019180000000786140301d10150b4a002104840e81c98045190080c1000242c00402c44070341e8244500d040c40e411803403101c505c41d250b4ae04c650003801000b85410070403410041c0c000d0015105500314170081000a9002c156184040c0d4100c88481f14000848085100400580c00058010404800120340b445001025510524088084541c00d00c51550078006a025510807580030448039408200000c003aa00481000610b070500c1d1040018048002001e0b80c090707000010501110303030418441c0741014803040b03c1040000c10740501d818503ca0798803a1595000b404200000360124070040380040a002600041c211806900408152500d8091255000c2042201d1412 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 244775566 1250 244774316 244774333
    0x3120907060e0d03030f020d05011e060f050d0f02070f0c09060503030a0c12120c0504030b06040509030f031f060f1e08060d06090501090b0f090303041121010c0f02 72
    0x2d00c2403400e0041c0c1400604030311508001543e0503809002d581611a00d55034007030042c148840003034420b403402840d40c0010000c4041e101c40c2c415998042e41c2d0855000c000b4891508821543c202c01243c3c02e95580040001d0819007103d024402806040e00090200c0301c1e4280703000c00d210380500d0351010745044150402400c1c3c2d503102055501e2240b60502e402060046000001160040d5889000200c84d0300f000c900340b8500c0e040410072200c5103041c00020410124040c07091021380c94619500000a983c1005681040841903640c0c3c0034046440e110040c0010004103014202140464602812106241c2c019100d40340600086410782007800001c032070001d42011800404561a6251950b80759111982c4403203040c0070b01c051a14030141c070402c0d1242c02810004d0800d20407080901e00034600c461441c100b16207070030001d070009428071069a00074001e02c0041108608480d40444048862208040700140d009036224461607402060b940392101100000703401450b184141702080e800d4139481c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 244776816 1250 244775566 244775579
    0x90601121103010c1e09120326090f0115180504020a0306050103080306040c170f070e06131509140103090f0206030a090201030c050a0c02100507170a0e01080402090f041403120907 79
    0x1c401c54415812103444140d48440230a00644001c070030002050416100514442c244001c0502d05071403600c2c140e841182800321015083c80b030002c540030401c011001c0285802c104a14000c401e41e00d0140203603403a400300d400c41d40d410742d02c0e90007540d00040911240d0f070369040044107a003044174814007583c00c0c955003104c843c0c414502c800c00706611050700803d585842d060350321100c0c00180048240030749400e071446150750301c101070318602c07003440e0a021800342400c041c21103149410340c2c40780600c0801ca00c20300c03130030071024581004100b0a1070001000c11542c104020a07000034603010b500300d840002071020319651038200700b000e07034001c0e2402c1c00030300c0c800300040700d841c4100f8090340000340e480d0b03500e100189407505060054001504d083c03400c1131760a88440590704081030343c41a20600016400c004642c104000218000003424084000e151940100d0380606004000003141d80742000050300b001440c19101005c0c41510301100d417a00d44c900c0383c921000380103a80b0019280f2514000103501e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 244778066 1250 244776816 244776827
    0x10605040501120f081621090317090f040c0305060f0901080c0609040908031f080d05040603051e0106050a08010e01050609010518090c0d14090601121103010c1e 71
    0x121060b40901c28003507400d540703604031035100c0000105c5003280304121004190384a02c1040b1449800f401040d10705071080301c2c3d8074031044120301d60042440038a1800b000890103502e5141c105107001d658265075100c0d2100010362001400d00500e40c0700c1d1802203000c2159a1541c80948580829140c1c2c055402d030100420460390030920a200700d03079000450f00d00150170008050411a800600b01141c00d55960346c1c0d00741160422161800040c0c0d001501c0d001841d6281c0d541001403020034050980034125185c01401407099004100034982c8070f00c0460740c0f40100303604807d403504003025014600e5844580080403688080101030000e081803002080181c0b000c0142c034100d4400415140c642000140150780940181e1010700300e8940e503031204840b50b20f94603a6184240b9201141d50f1307a48100300301c3d00c0b08480c264880f007185802500d040000121002402034152661169490060040c91604d070303a012001005840d00340d42405440200355400201c5040200038095608120b8420164212407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 244779316 1250 244778066 244778069
    0x106081f050f15011107030605042607210203130305010204051002030f070b0705160b180109050c09060301020706020409060f0602030a051219090b040c060207260f0a0302030403020102010605040501 87
    0x82024541c008030340e0f0b941c003c00c01d0417820942c403401c2c1c1e4041ca90b251a480100c502c204d400341d0f10101c3d20304012004a03055803841e6160150804403a05010700364480310070700b2002c06039074400c03124001d921511281c008c205807802002c0c4144040c12094403446c5c01e0f4040e410500ca030382d01900f06000382444440c000720603100302d80a55400582810b0681d1900f08102001401083c240101003000d2001814843c102c142418001d08000740035003071a0b42d031400c035420741c8100c035502d1780d150505500c0040c801194580c0c1000b000c80d580d540d02d40303030440041e0080c410710340010010f62001900081d01c21982d00202c04a980e60401c2414696840805036220b114035010704002034420002c20070b10600303100b01c8a4005064134884862642e0980d000d070110340003440c0035605405064204410091102449005005140302a051706031800b00c080080e0fa0003110a140c17152008000d10508107802c02c20503203113100309021243c081d0071500b4065120303400f502003030317006500340140460b031806c042c05801d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 244780566 1250 244779316 244779331
    0x20c0106360b060c0a05010506090109060e040212010e07080109170c0303010b0d06030803150a090c2c03010603120f05191b0507180b090114010c050106081f050f 71
    0x20000940041c110080c10400041035224505000c0996281d404000f43c842c035038402c800009941c18117070100469242c0c1684048c0b070751070504000784901020f240405401c1035058680304400e01701401c0d0030313024100a441ca07000d54403400740005035071311054010303401050080303c80d20b000c0e050b001414941403050001e616100d44c8204010442890040005c2502100c82800003800c16226505c0800c1507205451000001030814169410762500000d0032000300101041000216610748000d0a00350300c0310090b02002c160f101401241d81c000c0d1003408c2c12860024001c129440e141e261070041d000303c07200050001403000b81c50f08038150240c42102c620840c020918480700506c54000c440d1030700811100911348084020b030b0000034100f00107440140134030180301c081901c04d031000d0f041210840c00c0680d01c100c00c5400108001c240016451807441c3c400e10301000001c100d17092541c00741c181507001607190f02ca40c2d13803078508540c070107540170002d0b0941280c103000766182c1d02070382880d000082d500701c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 244781816 1250 244780566 244780649
    0x30308010e060f09070e0a03030305061306031e060905030415080903070c2d0906050103140402150717070614090c030c21011805060702060f01050f010302070204020c0106 75
    0x1429a4a0b0404c045948102c55180890003000e10201040c1007621981c4100c01094503841400b29070300d030000000d81d00340b020101c200b20451560301c514071881007101d40c21041c20011008a0140400d5070441c07032800b60400200c82c0e4966444031901e5208000c203400b400001d616030082403100001101320350505800c0300401d900c050401250450300b01e010700c038a5614500c00001d4015001800449600408000340c00080f0281f810001406640300c11940c00c1164569004100042e0f94144103140048090464107031102c089251842403102c207101038405101c0b000c55428100701a50b0011b49448401c03001c02c0c017490320b0b090b940310354800105100d40d0b030682055044144900340071403000400002049071070701002c7c2108072642140e40481000082c415a414100c040c4203042180a130820030701e1006029900e0120900a0170b008180201d911940103880740c404168408d0701239440090700100210750340d42140b01c0d950300030480b070300c18004461903003221a90740000c151a13900e007880c00307089e20303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 244783066 1250 244781816 244781839
    0x20d0e03180d08183c062b06030506040c0519031509020604090e0f0f060603030a030207050307020612180d0c0204020c070e07111006051f03110c0304030308010e06 72
    0x301890104145015a00070164841e4030908284085480084021010040b44c10319540300703615001006401da030310301450080100c04444420040f007189003001c7c511070220781450020414010304082e9102410501c144010301040c1b08055080c00110b540c2210340781c0ac3c042140c9140c160803540340c88040c12130600010242100c2415030441c000040c1700421041c90146c81e81e41c3c200c21124802c543e0800c81d40013001112002ea4200f20285046074610014500c0d4901000025640d01c40d0140c0502015008030315401044802c00550300510744c010710194850b007900c03c04249900d0300b10760070007000e854158080140300020540032a0340b081903403840e80303a20b0f05400348000b03540044e004d500c2700d10031803d0010f40d103c01100994010b200c199244803030000d00c00c003084c1c50440d101001007d00ca10300381d005c00250f03442e20921900b0960107001420382c0070401c9006d4000b400440e8014015181c00506e041051030040024815244240c03140d035420b07601c0301c480c0002100200d90071070304030440320345 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 244784172 1106 244783066 244783087
    0x31e1a0a05100c0503190e01120b060414030a21081006050409051e010b130801020301030b0a0908041703070c0608040b1504020d0e03180d08 62
    0x240c00c1905401c12000070a9580e0307056152090107140300c0724404005080c0140d8102820180d41610040c45900014058207140580a0b0000b00300c034070902007840daa03102e01c00d0a160090219404d03d41030500444e00c500444200c0ca0340b40c414000c111001a1148003411700b203180d6603d030500c0e83d018407240605155009410f440b1030a80700901404200ea1080603102215518100451252241001c0e100045050401d404580e943d040011407904517100003844ee9105200341568855904e101c110300302d02081c0002011014040c000c10400650394101d11a4031b03004110f040c0c42c04c1d0380c1e00d1743c282900b580c014000c60107400204011040c0302c1c29086410043c90344ac10112a00c0c0751542e01c000080c04002e0504250b644180405106d036283c03541914211049484108403081c440204165240c22103000781d41c403804006182880c07824100c0450000c0d0b80e010181506204d903462 = true := by decide +kernel

theorem cover : BRFrame.Cov 244604316 244784172 := by
  have h0 := BRFrame.cov_init 244604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 244604316 ≤ n) (h2 : n < 244784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
