-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:08.051756+00:00
-- url     : https://prove2.me/submissions/28bbd6f1-dc3e-4c92-bf7c-f89d7a4d15de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 739208633 ≤ n < 739388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 739209883 1250 739208633 739208647
    0x31b080403060e06341404080607110c0d21170705071502090109060c240e0c1207170a05010603030305070207090c140f19031a0105090901030201200601082a130b0409080c03 76
    0xc20081110501000c903150540ea84080d03860504c0e88a40100480100c001a14036000ec240160381d0100700e1140c50703815a505180072440101181d0021b03200700da558508404812041541d4420742d042d82c001a1610200c3c0390400070103032040c0610041c125545c11815000042c00c09490040d065020701301d20001c24140d400f141514100111503080c80d0080c0745c1540007004450380010407000b03c4000072140e00900280146050400041010140c040d6080800c00001c051389a84200e10070202c981c00c0d01c00d441e0700d07031030404266101111800000b0f07841e180e00c06841d5a50200800420340120f084503d011080004e109510412000d110f010079540c00c1200180c0d450014004200036003483c0407131521b8003410001d00071180c107020181c10002e0041c40c04003484081c070754103458141d01400710b40c1d0540e561558555104564200354070329400d18035800200d40307400d0440381c00c9581c00422450409a480c80d40100404135520403e80c80341d01d98070104040344019005002198440d0f01655a030030f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 739211133 1250 739209883 739209917
    0x5090304231314010b0c07090e0a0204060506040b1207121a01021209061e070503040f060f03020c150a020f0403060522031b080403060e06341404080607 67
    0x40c02c1008910703050800b0410402c3e54001014a81502c103040c09154617508054061407a040075070f00400402c0707280031403518610500150000c10030384216000c0c0405501c400038042103000702d124402003490b052160011400300303040025403040e094a1712290000107001c10100303484c109428905908006011941656414080c00d025582050310007860001000c2c003242c041c0c40b910040c0001c0c58108181c00c004c4000d4403044482d4660040d08a035140c90319001d410020300d00c50300c00c46021801190826808078040d0080e43c80c9108000040c1c8081030002c014003a071002e008107500c0c1d456600304145501c10710380310003500166008080c0043c10b46010315001020504040c0d40c0c99211900ca02d0120010b43e001c16030010030714031001c1c480010318851410811500031070304020911800c000c3e84079542c4000082c4144034036404020f00004504858100e20aa0016405040703e05515401c008ae010b00840711a802d001c060103509140c0340d070b030310307407441c1044010b440c0f030070000d03040313901c0c000d5050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 739212383 1250 739211133 739211149
    0xf020904081804051e040203030d0e030a030e12091c0c0f05040b030703050325150b0f0f010e010e120d0908150c0307030b060d0903081012050c01030509030423 70
    0x2425070f0100407074109800c02002c0c42c050200307048412494800001c00315281070064552200710201d061029034000346000da01c80d0810b6802c4000a40f070441001e907030600010b004d04134038007000b070761910300388001091050868289894541c58040003140c800000c0c407090303806004100301030701100c0f11814582040151003031110610f10030f900656050010520100445a80074a001d0f15034802400307203202d6503d211035181000c3c003c0d4450038012040d011b115008036185210440d8480d24071400301c01001ba20b1848a00c80702d000034803600034100ea41d4016800081c10303200092442c522049041a107920700000c114920780000c4000d8020015401c007088040d0611105151401040c609014030840c41d002c010140c0d0300300364035a11803005503125403085a0361706100b25414090352001c1d040c0034090701403c0d28546040303a01c0e040c0004900c2c0240507201c0304254081cac06082c941c1640001180600300150030005103007c1003000107192500c0c401040c00400004002481602c9040c0412141c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 739213633 1250 739212383 739212427
    0xa0507020d020c1f0903060e06161d01030b031624020607081609050303220504021303080c2b080703020301060c060c120606080109050105030f1005040f02090408 71
    0x155201e400081010781d5800411009000b080c0310040020880c54012691721030b01e5400500454640000d088014802113142031080c40c40c0d503103003203603480c030318800b1940004070300200480410000756115281d0321070340140088101c001d0450340703021a01090114194440d503c15406008204000e03280310044101060807581a400504883e107441d40000d0080740d0002c011100c11410180341c10a050300510b0340c4400f5210150480380c4550958070340c2d20305c90013030004811789001d034079000055600d402d00031070b15002985445004110700e0755603001000d800c5581c5d045064007508140781c00072070f08501e10400c034010240030000d00c101210303005003803141c1c090010410580108011305c02590040f1841b0714655021100080014000b001201c040110300c08910090342400340c00521035034000c200301e050b10040e12007005281d9944082694a51258407412111b07002400102c08802d581d602841d805801082c0d619031602031a4001880042e00301c400f29420365021903000c0c2c0340d119107420982e038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 739214883 1250 739213633 739213637
    0x42402031005090c0a26010b090306150f0d0c15020607080a060f030803040c2117040602070e04050f0616030506030c010e040c020c060409020a170606030406091a0a0507020d 76
    0x83d0b42400c84504070544500a441c0c400c0c4104820701035070b40ca00d10f0781c0411403e494000040911358403000c10300201e03070103803460350b222344221b0012484c110b9145001c0c2900810052034501500c0c00e041c1402140d81c030589003961010800040000d001200300b02c0c0c090300c440c1e20b07030140a0f42d1908080107441002c0117010a20032600d4402c06100a5180705010000d0300c1d04441c0c00d5450399640c1c9080e03400413000f0303080034a050a110f0440303040c040340000c2e1456903510174000140c2201c1e1811504a0314080d42c2316440040e0b00c015003c0007010158188031350010b016000743e031020000040c0c1145480c206550104640440501c60541190300d4819a5000300044028102544100000030b011410340311009110750b0781c401840d80c00d00c2c020041e1050340344010742002e40302d503500d442c000025000490440c000c1107855135111030301c0140030243ea01ca8840240701a06580f03840d00c03420010051614112500000d8030803460ba000800154203204401d24440030640b0b00e881c0f40c0080c140649400d50f41c0c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 739216133 1250 739214883 739214899
    0x15020601230d0311031606060518100e0c0d0603050c0a08030a0903240509060a0509070803040303030b0a05060304140d090605030a0c1b0602040303170717042402031005 74
    0x81550707142d02d01c050058051a29036810b40503000780380d08610030315400303410001d0f14440c01c05c10084c503a0010000c581c0219000c4e40310b0104003c95a1200100310ba401a900d144107501b448103d0440d10442d4202c08a800c07003e0900981c06c4101040721540c0c1c1040e100c640c040e100d08142c503c0c00404900181207124065800e0585c0d801001e016418640002410b060482c80c0c1c4a43c2c00388165203105000070443d03030920044c10281a07058840c001a00e52044042c1002c00241024000082d08022540010029031516186443c100e0041068030500c1d50b0040c0e0103200007c1c40d50350380001d035002e18005e406110100410513070301440c140d40c0c95940020f1050415003044540d0700213003900da00140b14034000c100510705034802c4030305004035004204032052160901c0700703000d2582d0180056a01c2521021044050031400180c103000c201c503007000080c803414403807148400816807660071601c500a0740c00c080b901042801542c0c0c41030580d0041695003c001c00c52402c600c01c803860028074007525001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 739217383 1250 739216133 739216199
    0x70804090203061507110d151d0c0d0c060e061207030b13110702010e150301060f0807030510090c031407030f0b060a0525020303070b0603010c18061815020601 70
    0x1206d410b510300041c0e4070403948030802c070f02400344405602504c4440202c0410030304420300320054005038880c6040c81039104000060540c1d0920015040907d5005448841c01c00d18042e0115283d0320003d006a80050b810b018251031451225405406181d0a4a020540030f51181c01d1094101145116010303140c100201841e00004220407036044940a00e84804402c0c0c05201044240c1c00450820401c0070001000250f19688105184076048075507540c4403003629540812030a49070203850303902402d091032504104480c3c40d580401c1c0429581c0c14089900e61406001220002d001c5841c6004292651165562a106481855500b05c02282d545003423000c0400001c142d07010b403c41c120300300f4001d54204010340d1844241e0b00c0e107150b4001c0841c2c0e943c10395071070905449030054400502a40c00e1a0f100003409000c0c3c08103880442811500b0348985103060f804442c2110b00d100e5455542c0070102021800c0440d60301826030414194004180e039500d0314046d4001c950900521502d5042c16075905 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 739218633 1250 739217383 739217393
    0xc05061608010b09011b0b010e0c0304050705010c02010e10050c0f010e03031315020307120501090b0904060c09170604110907021005040804050d050729160503070804090203061507 79
    0x1d030305450007907901d030380c45448003c01030303c0c41c403155000750356180784a41d4002c04010600d0346c000d060300c40c0b080c1610403a8071207444502441c0001c1e64000d02a8110413002c0c42a07510a4081e50400c030700500d8150481114040402d0b0358642c00150100014400603030101c41c2502003010b550480418802041010307259410183c43c0c1c04060551090090301d1800201884100c0d0541d02500107031050440d41d0341030070344015001c03030f003240002c0c5903090504000045006091254412aa0f00a0b000180c16038640d070316040103003c810301200034803100c80008101040800315080504451100070002810f0500708603d074840c100150038450100c86041010855001c6140d90041180c0c1202080e513403500c3ca000c140341d000c0c9030030481d041551090644144580061010200d03850400da2010f01c0d001c44c11007119002481600200e940001c08c542201d100700403161240c3c2c1030042044e039003420056a03458116a1142d40100100c41d0088240041e6203017854582003050507001d1003d15202c2240e0760 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 739219883 1250 739218633 739218647
    0x70e01020a1a04031119020f01050c1f1b02010b030f060106050a08070302090d08190f090e040804150c20010909021315020106090f091703071e0c050616 67
    0x54002d1140481c80400e00b0180101d07140c0c00894600c41c242d8408440f20303000790443c50b6000c41c05a128407000e54820701b25502075000c54400140c040c01611107040b50240043d5481e90800781407060503650860a100f1703034646440d0300345002647d030000c0303690110401010f1400000300720101d142d8000f80c0040000e02e402c901281c0f446c1000e400c0c4200c2e103a44118066000b8002e0509061f0002564030b0b01c0c4040015020003404045e050708560714051706c10100848101c00c0101241d0080745004005004013030585500c143d005101e41440741c5810b40318940c0c074003460f000740520001b00e8503c90ba11400c200d42c42c1013410000c0b00102d90394154860500c0000c240120728850300d1606540007800c40581001501c03014040c1500246000b210500414024000c007210710034100c17404d00d0003c0c44d5440810074020700b6104d075082600c1d031402c00305085400c511548007400b0074050014003012a00305408001f196182d80c0c00c0c2ea210f102c2c0e29081c500b051030800100400240e1b5405150302881c0d0800c1e0030940e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 739221133 1250 739219883 739219913
    0xd08041502070c0b09010810150318050115030b0a02120604231014010e030d0302030c070b10031205120703050618180d110303070f0e1008070e01020a 66
    0xc80410a40554a03050002e100d42c440103889181c40fa4800b0564010900040202c20401c0c1e8442005036203c0c1c08001100449005030315140910b242c0403844248039412054601c40300d540c44c00ba4941d169940e4900311501840e00c5032504002980c00c005102c101400070307600890710030040d4a06280411800c170303007071002050140328980e03d00c110f1008240c40a1144944900340d90321040d1400c113600c280f02d00d00540d2050002c1e025130b5003505d4280f035118151000c00d0010103402041050103402c0c069000e900005c1140c00015030a10440002c105807401b000c1c064107149001c45010790440c00c0652240c1110b82100040c07140c02c014442888440c11025603200850b49070000f81c98441c1c400044a840c0c9543c3c0c8040184049424004550b6000c0410800320082c03104807110400203103410b8a50250030112035110350814400205c13071328001c0c0f110a0903804c03c2d10f0003410348000382c400a03201c4501303662548001240308003044070590f0407a4034058005800d000600698080350b4078a1103d0320012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 739222383 1250 739221133 739221143
    0x70201061e0302130618090203100608100203150d11090c18040e011b0216080c0d0b15060d1e05100b0915071b09150e1e010b09010806030d0804 63
    0x81032040c20101c10b6202c0005002004c0000d80d514006d40d00107005011011010b0b44603010302c481c900540821446407504980480000e0441e02604010003002500020803a0340f280704060700d0505030790340391001c0640d014802c0c1180001c02e980303881404650f0a0080c0030180c440d8007004035000803c1c00c0e034a00280441c040300c0100380051140b01040c05001d00e4003041d0866a6111841c20140d07801183c01100318411132100d01c40141c1d600e40d06076031002c820742c08640002861003800e020880d0007010310b130301c415010340020b41c41c41c00c00e01042841d40071050903c01682d485a002d043d514045004004405000c0803c0c0800c0c1060f06654010014038460616050000038650b0401d880d134081000100d0200440301c2c0d1079400c0f41c10028003502042e1009142c2c0720881c1c1010514000c90700c0b07003000a01e92041c10310681c0341000c5c000708907a030700609114060820094500309181040c40c0d9070b07020303001c036001c404d8a601401c2d001422072038000c0d011034881d4001e040c0ca80c241550203800c0951040e001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 739223633 1250 739222383 739222399
    0x4051b060d0c0e1e13020702061c1407030c0e0f030d050904090b090c030708030a08040b060f0d080c0d0314130c0807080307020f030d0207030830070201061e0302 71
    0xd0105460041c102d0101c2c035003100e892044e81c4100442c10507142940d5401342c4900d02c5009104031000101d21503d10025030202d01805032500001040007003800003000e011000803000031940c40c80f0704905007112800c00103034039201030360300d480e07480005802004010782c0c4086140301e0300c800203a200c446c10001d0108029022881ca1500d40d26034000901a80d000002c1000b54180448a40d40b40e0840b03c0c40c1d14000e118280700086ca8140c00030890701180016541ca800e00d4556543c1c108402c1c0d00944942c0c1c0c010301d00050b600c050340d60a50780380c142500c142001580da262240106052620300c004100034140340181c0718113550b0301d440d461940300c140811a06051103884ca8010442c0e1000d800c0100244030b40c3e000414248400002403000d1402111000c1c1c1400014081698904040b1645401a000a0030800024140401030203807060260b44003804800700484050780410440310400325041c102007805034054080c410313407000e050300f1007005440981c204008101001d0a20000f4095014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 739224883 1250 739223633 739223651
    0x9120b0c0d0f0501140906010224191e06060903030903060f0e030d060f091b0f021c0c0c050a1521050c070201030b0a061b0206040e040b04051b060d 65
    0xc1c651005607070b40d00a1404020759619508081e1400c0b019202480c01103a141011803810340c0005044400140c2d01c8410051900803400b0a55902e44060700103600f4001078080c0f5402d0442c2401340d00c2c0350200ea42d0319602039050a034103002c25545552301080a00010751010f00109a0080c241c0c2d06481d0001c13404a00300e039035056948000c18001420b0b244900020030700780550400ca80204c42214022160342a1064a40400c802203a00c0e403180000105110f5901840c0c03d0300400c4613002c030402500550f490036005c001642c025a500502000000c0c80b00064082003042c0b03280301c500503241c107407800e10f591420989405003041c00c0440300c2c000d001e040c4c03540b83d03000608119021503041c1030501c14852410450755010352500a964220b01103410302052030b946080180110085842aa54002d03d03210440c180246d00400640d041c0d070000020840810141d80c000c0081e40500d2080858400030300e450f007807040c205000350304818184001d1501c488010f5483c3d41c01d03150100352140c00010700041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 739226133 1250 739224883 739224907
    0x10020a0b1f080304030b0c0412060b03070e1602072301080408040302060d060e0a0c05030c07020d020406080f0f0114181f052406070b1305030c0a0309120b0c 69
    0x5410429195401c501001140b8000d0210160003102d00c2000c4041e0701c0c0d2102052102c083c02540100303200a0505060360011400e030b40c1008c80018070290594812a842e038800c03007200c0304200d505884c1088080010b07906640e0421072040206003404520031040198071b034032540305400301e595504100201c000f007420700041d4811500110741c010b2080e955440c1c190b0304a0054041071003662108443d0000281d0f10980c0c81c010b0200d9050a50b0312a49140d40d01c559001c0d960700b100e44183d80054000320010b0060b2120700c211000382040030000c10803405e45080440c580381021044400300e0b4100401340101090400c0b5150300041001c009000120801039803602d00003400c00c584a910000904240c07619042d684424010404082551418000007841c0d00090010385509a0801000c00415010581c48038460b42c001e41d0a080c2410366409a03160146903402c0a202c640950301f02828201c105601f10305905c00400c81c41c090310310b601c03181c0c3d01d540c6a0a88000c0861032840710020f80664945 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 739227383 1250 739226133 739226161
    0x70510090528082d0a0b0f09010204030206040f1511032a0307140d1701121b0e010e150f0411040f0b09041104081b010507020405190b10020a0b 63
    0xf09803032044445070103200c3d00790300726084828050365030100074401c144001000452aa8503c680045401e00103071600c3c4039001040c54002d00701d18942d5070a110210040c0c2d81c0100400081c980900031002c802c0c1001800c03c00d850600300303040b05011101100d0802c440002c42940e111021841c81c4244040102011896403500340b00e461180703000000d0b40e05c0401a40d400340400c0220843c08980d5901c40024007550f0f1089180c004507800115140100048507034031002c4038425108106102d01d03010310282001c0c1d0b05500390421000300a0800040c07000f64103a000c100c0c0e014031011945545200d00001050a45142c8500140900d0316880300c06820480c0d80200c2d0024540103000303040e800ea56080910345500700200f503034412418a0340200e900aa070380161070503551554040c00c1c013001092064211030300741c1105103060010500140003d42da4910510348141d03020350740895040720317a00e640411956240c14892040e01101311550384541d00140740d104150303004003000540e4851720700d140055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739228633 1250 739227383 739227389
    0x207080a0b061903051e01020f1b03070b10080d02120702010806120709020a0305090105041713090f020a020f060c250506130510050114040c03021902070510090528 72
    0x3d003010b400001040400a0000c002da00403040800f180d030340b1840028240e01c00c40180c070104d540d003802400da03840303802d4a101d065030814a048070310b08181c0343d0302e080c0c0300701040b1240d250b0050310402c100700d849014010022001c07081d10141c691303280c40701c0069401d8060307524064100071040340007071096203401c4a803440b5007100c0d10407120010380c0d588248002c0c1d03100a00820000c0e0521021481c0440c0500034180142c0c0d00098200030100050201d40741600b101c03600101c01c03c1c140d00002900c1e151449aa00003284010016a40380070390070010f0324186028001b1109544482e08128a45000e4003d803a030560701d0440c0e00e0900d816211400b070ba0908440809065401007005000709440032480090405220304156560b10f00e6082140e001ca5909118050410905010201070b91400d03070321541442c1d02c0380c1401070812006007440217804000c0c0c6070440c051791220704140614038011030682d030306195a1616044450502001c42c40b00c600c034404034003c9d5000d111404e0340e00b5440d01090030203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 739229883 1250 739228633 739228669
    0x1060e120109050102030702011d060103060209130c0201140705281115011e0303090509180f151f03020d02030a02150310060c0b0414010e0703030513060207080a0b06 73
    0x402d410b070618030b00035032045e03604002640c40d013a040041001e18480d00ca02c0000540007400003a132a40d00e98001a40c0023111440d440701101d41c1200e801c3c0d02601c10500e01e407440358000150341c01a0385d101280540003414480c144201441080100000d580554081040350840f03524849018103058640c1c0703d440400e0080c0d4062800410b1740b000a0011550481d40c00d505025010b00c0f10060505152240b4000640041e8000c0c3d02402182000b42001e078100c8034100c4400e092f4070100d404a070800440c02d1440c0d5407500011203401507041c610a0041e00403150045082c03c665980f40e11401c81c0b40503210080c0260040c040100c15560b00388955017550380c002e424001c44428107400429164800c40e000c80c0700145480700421102e10886520000350b50006840d40b050321240c0310800c861102a400319070540d2280610301301c15805020000c01103109858540e142c0220040800c0303514040c5d00614115444044208007620300007580390303059034004070a034440c2d8031100080780e0100b5007071511007a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 739231133 1250 739229883 739229891
    0xf020c0301020a21020f030c07020a05131406010509011706031204180e03270310062309090d0518031c021606050301150203091e0a17030301060e1201 66
    0x41940c0c1c10054501c0320118042a5594044004e04120128020380301014501103090001600301c0501d08000c1c51070b940004e1a80d0411a96940010112401da080400e10540c54210700305001c404182d02541050007402c041d4100241c0e140000d010782d0b040c828041c898011400410300320707101840664501240300c0d41c00c5960305d80315034403c00d522060090322002940340800c0100c9502022003550200c180180e40e0074501c104a003801440800742e03c8600f5030500984020141880c69440340c0700081c00310703420b0101900c100e080711422000140403064061001c036010844030400c08141c0d40c3c20040141446500d51280034181c210b81c0b2401d00000780c040c41010707184aa810160402041205410f03800c0350a2441c0e02e090343c4545040b40d00c21038000c00d00901c0188012a0801c441c0902c00005104030b9061410200019590b0044a44080044003200000201ca801c18900d12409492110960a07481b0005140581e4034481449030780c041103a801a04203d9030758052900e590010001e000380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 739232383 1250 739231133 739231147
    0x11701081c0c1a07020f0303040b0c030c0c01060e06040b040902100305041b060e2d010f0203070812010e0601050a0c06020d06080f060906090d02100905071d100e040b06010f020c030102 81
    0xb03480c3c0030050b42c008001d4801c859569000020020859208503407001032001540c0719014420080c1d04041c004a40c0c0d1007040c026540030302024450380006101e90b0b1031012042c00c26406101c100e51a03405c0031405139080c120f480001da190b180440714500401e280020315a40e460034454040100803501d4002460480c3d400038040c1d0703202d5410301c2c40120841d00100d540b2223003c2a8a6180b01e42d59100c11414030000101a1560140380303400d00303040842c019607160459650303680040f82d005c800c00724008200c031001401007102c03922034664007403401c2c2413151504e4411440900a1111014000c04558001501142009940c2c11000080c62407800300c0341c18421000b841e40e161002100d0111240c4038a0b800038a02e04000074400200501d5031300030344030442a4503c12000340000080a84e447e1286ca040040c4503d10038440100c6900b600c680100541008030100080400aa000000400003078080c803010807030750683c00d80c0206c02401c2c80e03c42c88103401030503410042200c50096141d44081010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 739233633 1250 739232383 739232423
    0x601030e03040306060305060a0c08070e0118090501031707170304020301090f0308090c0a0f0605130e071107150e04020c070b0d021210030b0403080c0c0d0905011701081c0c 76
    0x1107086d6403240054400390b541e682d20b180111600d90034458000780d00d040110f0103840c083c452044681506140000010040b1350b2080354005d4554890b082059840f4010001e205400440e0100c2902c01c15000d881c0070707002e40b40c0328041d0705400c401c5c018078900000414115038095001c0e150290380803851080d020802d080162031410b08540d0f981060280920000e02c2d0b00d0006c4000003960064640110441e0604001b01d0321500949022075101d407280c3d2000c6030181d0380a110340d2144101740e641110600a034054107050007000d620811601601140d140c0065401200c4030703074002d80a550040e19051019004e92600c0107503444503264040c000342c80b05000d201c030380003000c0c0c40110480c0300c003080d00c4070100440d50410910001d40b086111001040001e0301c03600080c0d4201c40c40c6540c5504043c0c4001c0e01b2f80c200100d0010784004900c4a80c010400e558002141c501001c40081da00d6240e58905a0491313165000001c04131a055484800150350707130301618910840701e4200d1440f0b04207951540c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 739234883 1250 739233633 739233641
    0x915030607031415100c0303060305010e030a020d03020a120207020d150b0406051c081608040f0e1f090b0102030f041211060322021201090c05121908030601030e03040306 75
    0x707810643e516540c00298850104404131103002c1002d0511540350841000c200c0b04041c66801c220105902c50340b0020120314240214460b05d20000095a03460140c94800391500798400542c0c4145030043c0722041c0b407150004006086401800809644c4460510028502d9015080000c1254003102c42403403004c2d145074010b000c0d404040e02c0400c50151980104030007000d050410000b8001184500800504070001800510b2007041754414280d180b1340d915808c50b0441e0700b107132a440181c85402c00c0024040b4440726044503004521440003c0d20000504c0c481400d8000c000b00e0a89461100c10300e64030820403276120301618103045da161602c9034060030159440050030350300d8212805001e41940f0745403084034080d100c2103011299042100501c0b044208504800b40da026204503800c2c01102400c0c000c44c990140f1030a10403030b00e04c1c01e0104208050301d1031116080c8561142d0b401c820440b400807507014009811850503502ea07620f04004802400010031218145e000200d0000100019600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 739236133 1250 739234883 739234901
    0x82a071b0f140303160f0c03080c0c0a031a150618030c030303010501090e07030b09090606030d021c0e04060b070c0603050f04020d0807061d0a170c0705091503060703 73
    0x3241d800c55440c40c1c64080820100c1c01d640e4150810450034007004010b82c0d0344003a880c4209025228441141c8551010704e42c02d61003a07034801d00000d90403d41d1281030100105a41007103d8001d5914210b458500d2442e0880a01c10000342090010411480780b00c13800405900008001558030000c040b10139921801102500e402841840c44101e40c5180210035a8162030040c0c0d1001f000a281545049200c1c0024110405055036020300340400d40b20030640070710500c0c4ca00000d01c1142000c20606140c000b0b440c01d40300841d041145010441c0d0a0248101234080c180e24240000c0313841c81000030010038080d4040c1038811800220f450030808080d14100444030251000c11031543d415166002213841100c00035400380c0c2c000c1810703001420ba0340c050320f07440d030186600003a042c04141c50346820068007103240015038010440350f0704100e01c50320703034800d036403203552003903080490700c9280035a0f0b10164081c00d8415013030500010900c0110740308040d440803004048035280e0a0580d005401468855 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 739237383 1250 739236133 739236149
    0x60f030c0e1f031b08190b040f0902120105150f0f09040b090d080402031906090f060b131109040b1f0504060e030c0907030218060708041401082a071b 66
    0x2c07980d003800c010071131040c180c80440354440070400d82e00c0c2c01c442d920000080402002140e50782403403001c180c03101e00c118412061902000608103069004000c0407030380c07240d1030180503810402040841c11900d0001e061007001034514920031781010b4001250300400380c0e1a182c0042c11082000103000450510901400807003059171007141c0034010885081108403000383d010f500c0401a04040c821411075a0031890042d60001201803c9640300c0200000044040e50b08030345070780e01d940903494070312a944140801c200c801c100c2e00e840700c0342005d0345001d0403405ca81f20380d64032014039200783c1314a0f200b44110307010011800300ca040c12860103446a04036000350030000726000d4819289041c00280c02c271f00c0b0b241c000c10a0220380d5800900b20040c0d44050100b020305100100081642d8032000c000d0f00c0958032644901d0f403034608050301c849509d00d9940b1205c1c100000c4400b40405024501c403003003201d0f4030100710030041d0401c4002404d1144101140100810440361407004e5498500c2c44660a81e0102 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 739238633 1250 739237383 739237391
    0x61a180120191218030b2205100c03092f030a0309030314090915030f0a05010b0f0402190e011701090b0f01080c1611090f041a01060f030c0e1f03 64
    0x240404c0301c141101c0d10a00003040c04042c000c1c008543c04200301c03071344030206020903601c1050001c805181010020411211603020011781400035003580581c0108203d5450201310170450794032002940310505404c0d030001b07000c0040741ca03c0c23a1924a000c82c2e20083c00341c1105c04002240c50001c040c0240d40c070098001401840124200e41268011104c1904008204a07056243d50008144102c02c04488a61610414189804201e0300740b01c508003281c0030310000603a0002020a100900e2501040c1a218910411164500c03036200b08001d00220310360300d0000d10807000344006a03100188000c41c40707040f200340c20000448012035040f41040c4641911200b500e803080a006450f000801e4030851850300c01448100440d403040c10030b040c1030320301415040d01c140b0041404100c10340f0050303407100e1419050b01c04010034400e400100d10115208858402071035803410310020710744049007590004040d29107500f544040c2c130501c25003210314001803903940b0045000c00185400e4480012a00201e418 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 739239883 1250 739238633 739238663
    0x60b12070c0f0b0702011b050d1a0607151e1b02010b091311060408011b05040305060a0c03200315010219030c021203030a061a18012019 60
    0x115110580c901603200d0307003000c1c8402d46580c40c003a04110050603003085659a022075582c0b6840b940c2000034080c51078039a40e0350340f80d004500405440c160000203004040c07050010741140c5030803007200c0714540c0100d008000c201c0310341e00d00400785c580000ca00c0d035450302044400761015020342c4440344200d0010419003c8100c910004d038203071201414140e512200300000603c04181d00406413900d40d00c80c0c0d140512f0b0360381c00400299181c0080d000100c25a5403000075045010340300c41c40e408107650790b00305241400e2841d550280c0d00c002c010180b568142c1c03100c030b20411302c030b010f900b10b1902121510f0a00c6d1078528480000400350300206e40f140e401003204070000106500228102c140036144606882c0414407684040c0c8007640400d500300d03001610321100044000080c0090740c000d54040201203900d502d84045006580100c130741c4500341c154100728288603401c0388c001c4044454000e00341504080202c400300504c80711070030480910b902428028202c1408448241e4101510459400c3c0c88298 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 739241133 1250 739239883 739239887
    0x10b030f0304690905090a0b15150f0406140c030715050c0f0702120309030f01050f06180a240902030f090321090304090606051b0c01020c0409050709060b1207 70
    0xc180c41c5119043c141e00101448410900d03041640d20062460484200090340d9446c1c625184c41151070b00c2c980c019a1524210601e0b100c502c3c18103021414000341d0800001200720341c0c16225500c58282444084201c41c03584642c2c9c00c055032814407400c42501c0e00c469240c10902c1d88203084440b41002c0340d00d0080020b01c0300c0740c00029140c821540030b50640c10305405e03500748511443c0c009a28000f510062096a14540d410001c0d0078002000a001040508100408588108014141c140f11340c0080ca649800a020324001c0b0b5403041c040c000c08074184041959461110b50070501c0d400c0c4010324503a0100700040035800440c02124a080749111554810104e65140d00540900c41c2010791901c030742681c0c5082c3c098907641c02c81c9407801034902c3c15590380c483e0702c119a900e45c0044003140303010400b81c0100003100d85402528003024003030450440e884000070344841030038004901c1142d40f10420b00030302100b004401c0103001a010304000980d240c055201043c1c000f1035010040c1020800001c111038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 739242383 1250 739241133 739241309
    0x6060305091e0304030c0b070606050904020105160201140c0304170703020924090a0b01030e28080f0c21070503040603020304020d02030618010b030f0304 68
    0x1000c03600180602c40c05010b02001c1104041441036228841407001201280c42402c00c0c1008152400d10169a80340c1c0d45006010f541c11980001d1040800c00700304170150760820111182d62401d1044c4d10903030041752005075104c80c0b8850720342114000101d241503102c0000402001510169061010b111024507004c5640f0113203804002e400c08400000701c0d200c00030020302d6070b01034545400c1030301440541101180e05204c04568101400d51101500041c1c2e50b014030581180000302000f03440101c0090500103100c01118030740c0490025607190110500880a09480e20b1420004025540701c0d41c0407401507031041c021000c13980e550b80c100d0b10001e41d08910f500701d40c0581d41c004061810a45460005e4001750001041680c000700341050502c0181e8043c030446101d00e124241c403001480f20b21011902f141c034000006400f07503000c0000452400d82c000b040e102182d03890082c0d4820704001601001142d480744500380c440d001c05640b0868850400543c41c0d0341040380c0c0907002194650555507411413 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 739243633 1250 739242383 739242391
    0x1008061006030525030504110402030f0601110a080c280c05100c1e1103030a021207030903050a050606030d050a0e040f23010801060504050402061c1107120306060305 73
    0x40c4541101002190b019801c82544240341107510140c4441c0107804c00c542d20700c6501a000002d0382d4100708810044006240780000e841502c08509524121002c9500f16201410084c140301c0c0750741d01042481030800c101038540390701c60f030002d440310146500c031070341d446620142003844005603203c1d00c062040744d041c41007010b40056001120a2800d130a022000c0368003400c1c85e082149640441021541c40410b0180403010242e0212540409062840c010348507010303600e2181e0820024a5565a030028030340d001d0710361b0004190756071171091405172100310440d423008099005400200050200100744a8400c0c1015401c2c0d413a6041c41d013508889501c2104500300201e40c20034281c20320f90030154810000320b40c00d20340008400400082e4090005111015041c0f10350b082c2005004034003085c092100103200c1660f0a0140c0d003041d60005000e0302540009400314000114041043c6c2101e0708070b84000700e440c82c0b805582d0040382c107044103032905003144400464144500010301070b1203841002e2007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 739244883 1250 739243633 739243651
    0x12020d170606090a1404110c21090d082106150d060b1912110909090a0204050c0d050702070b030a110d0f0b01020607050423030f060f100806 62
    0x102aa1102000e2403261020340030540054042c00400b8094031140401c1020b4280248450402c6003010208016505200707030031350b5005428401e8260700d020000f1b005004450490081a14404806240c0300078000d8640303a0364012401303100c45041c030682d42d000f40701c1811545858070324240200150f030010300b816a00f4680145440000c400d90081c0b42d40900158140f07030b080803814660f518000411a0850740c0d584020032601084ca0b804181c20040e00d01c0403880303001c2c0503ca9442103105d054100d000304038001c1e0061102c03100090462101b48410b90344964010002c01284c2040022054244c2045c80142111403411020402403800014042c04aa80d00c046c40c601d10740d038180448001d400e090303218012200c0c0c2802010281d03c1c5038001c1b03801121100e80001400c40390903000900d00b010181c00001070090070801448110ba9003000b00c1c2090b054a2906860030061901013032509503131130710f07020183c0030b000240b149980f0b0842c41240a5200d10700c10110480d01c07000d507940c0720b207003d841c0c0c081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 739246133 1250 739244883 739244897
    0x1a03060607080307020c0a26011104060e03030f0301090915090c03060b040b091e0705031003030c142a0a0b12060102190615060e0f0d081c020712020d 66
    0x120b60700011584480f41c1e1040c0c0f10609900c0e40070401d0944960401c03811500720f01001034100d0050f090283c05c01115500a1083c031aa420300d00d1818131590080303004021000011414de07480420031a0042000c0d251100c0da41d60359003021320700800e04640c040700d00b8009405242d03141181c0b4001c01d1607c43d00890706030241d030724654684008005031030790107421a40b5a0411180c944e12040e03070034411080c00c880911140480328168040007402404501444018824001c68414159013a0152545402d00c51a40c50042c2009005288001030394a503a00c0f03011000f0500c15883d01d848860071001c148030f040388182841c00c0024440d024020208200303003d00a5004000c05903e245420074010300585030b201098005680d911081000d060340c54907240d00300301c100d42140e5006a40100401c0c030f40480c0014007040040e11140445a50a1044404561035402e100c60300d000c40e241d59504058680344c1c480d40480e448080c4d040b0300c000781c1c1c2c0c8010002c4003022281c00440c003c4150000b0f907490308 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 739247383 1250 739246133 739246147
    0x4020c060f220602070b071e1101290a050907020c010c0c090e150a0c08040803181f0b041119090504020d0204081b03060a0e120406091a030606 63
    0x440d80600040044000c1c250307103100c2e191080c80640c090032020740a00405a82c5242a003800341c07504a01800180030441c0a00020440a21001d4042894a440d10f0a003000c40340c084c04c2e25024105c002500150305c54511282114064000d000301d00d507400540d10111665071b1303441040f480d44411540704015030004d010006030b0f5889281100d01c90361141e00030181064681081d40c08a50718040c1080780c41c1d1000b14200c00c0030080100c0542d100311090380a002720705041d417004000d110b002d00010011000800460034600122000074010701408048510b0305e180d5000203841001c03c401040800c500d011541078160900d0f000d08040c0682c070581c40c4c0d03c0c0210002020200f880221400000c00040040120302699540010540d551080c4030150710f40d41011401410800c050030440c840704440d02d070040070f50f03e001ca03825900108040d8001280c145144085041251300c0d0107010a0840004012505030340081c1d030b64099a03035504507414410303211041c80003144429583c041d8840e40a0000c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 739248633 1250 739247383 739247401
    0x20f030d1b03140706090201080114060a03271203060f0e151306120c050d0f0308060a1e0608010e01030f0206091c1103010b06130302040e07050d0b090c04020c06 71
    0x750300514403a01c1c0c00b0000c51024070394220790f40c00c80081110b255443e441c031002590b9201845c94098101043c2c440944992503000440a01c17030b4440c2d603024191204460445620220114800d0740204060185041102d203807180c164982d0004482c0403d29000c00422401c28000302c1310252003590170403d1282d00c0d69030001e07080e070030808589603106080c48045000d500c6540107601c01400c90881d0058869003500d00741c5503203969500840d0040a494111a010541c0d012000c480c0b940c050030300741d42d15190100403d0580075603030890b56410b9154000d1038058101e26008504646c2a5a5101003030390b00c811504054400070b2101914880da91518040941307800e80c0280624440206504000b010f400401400e017181900151045689100c0c94078880c102801050030701c8104541a5140a4024080051040c22400041d001d95030f80c0320380310700c003850030010540038003801082150b00c81d4051801c1003051324222100109402001c030100c580c4d0801703009440104507a00d000c0c00b0030b90743e1340701c1d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 739249883 1250 739248633 739248677
    0x302100204050f13020f0408030c01060b030705030a0b0a0f120b070e091807051f0201060501030b0604121e050f0c0105090603070f03061505040524030f040807020307060c020f030d 79
    0x44d90305110750030041c08081441c12002003004105060140da1034166540071f503421128241c1c00100c024400300100564036500070b0480b54003034003510001406215400105c2c10b00702c015041405c802940400c04100102c1e02618400c4143c07040c80f10ba6200d40e0740d6003086503100304102950303030800440c202060301f9840c0007404a80d648505001c40b20781c8ca5484002401899000300704200305503208000c00d18542d42030084901400d0300b803c09200d540030307900114055200b98402c20000d140e24000d90000c01840c9844c00c80d1070b00d01a1004401210141030050312a8070201e0301042e980b056401a814550080c002d50b20641c800071724250a41e40c0740003040d1651400c01e58142c042659600020840c1581c1c0c1c6e0324001001c14039606c0c070361070751700b04002c4c0480c64071941d02c60b8080000a240e0000300e4410081166031224501c0500e52441c4c40e00d00d80340485000f01c8000a5040c021404040384071544058040d0b1654021111042c0e40712140341410385664039624018000f40c07900d40060400c0038a0f00f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 739251133 1250 739249883 739249909
    0xe120702010c0f061b120c0e1012050c0903240601030207020d050a0503130906182c06061813030e0114030c130503070b070b101806030302100204050f 66
    0x241c1e40c001080255584822245d644082c2ea000700b04580380b618031a544448110307404500f40200f003000402c00c89020300045402150384d031081c6815820344215520070380b5441c424407421442402542010100c00c001034020651a5020b4480c0e02c4000001c02c4440341603200041c0c40c01500315490300d54000440c0650321400e400e0360001511005500002d800700f00001d64613010384091625a0400c850140814032036a02491582c1c0c10447d0501c518172484400407034072400240c001418210036a1142c41071400c507409524000e00d52940111001c002090003071042000b2a62581c102800500608214130f0603182015800107144030000064068082540200c0741414015948404054030107010b510860b000e940d5481d001c940356919150504201c400f504048014094850411240995070f001d014005085501c0c2000890b008001c0350300030340090032410803107480d5501d46070750b90000783c5214841280144a800c02280180d5004d00c241d0b8144c601c000e000d600c0d80314401c000c01600807a510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 739252383 1250 739251133 739251143
    0xb0412061d0c0102010501080c0f04051005221404030c0b090304090f0603060605010c030834050304022e05090f18011403121b0a020907020a060e120702010c 69
    0x140101d55480701040304561446114004203880000c80d4002030035220107038403185056005551300301050792624680c1c0300840066400140d10b5541403c440f90960140e4487c0e80c20600349401c440742c01041030805407a418000341e060041034001c81d0016007602c0c08480180014554031040c200255880255a0300070340f404007143d0900b9110600c210480d80c10301d0800104555030b040c2042040028010040186004d0078155039042141e2406404403030010181c000d25004640a500d140e04001d500d1000b19420030490f988503000103002800941c026681644101c502c14000310b00084c4104400c030041046504004810301054010b45031904201d5555510042500641101c2d8960039481000b030603c6001e400004c5d45003862052100c150030305400e020b42c202c0b19003080b10800550494401c03407810b50510081d07e5952000c281402d014101c000d510455030030501c50565030001d4010712042c01010104500d0100003081a43c2d802141c8071060000001d001680244d8000c40e80b212400e8018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 739253633 1250 739252383 739252391
    0x40207060b03030a09170703050c09040f0c120b0a0b03120708070b0c0a08090a03050a11030721120e101107050a0818030c091b0d0f0204031202070b041206 68
    0x4403002a0640e0480844480060400c0c0d90400c00050006e2915450080e80c0e406888001c2c21501c441e0303101c03446003d81c1d80c0580b5210000c202042031041c0e45804040d0425841518a900d84094907030501c040e680c203440760f804040215044403164450400303800c0008004113104230382d2921f20780b5030390040c0106a80c50300c400d100c0d180c040f1349103c54403445138500c488410740e50034052401401c0c0c242c01800209066010601e09000603411a00300d0359a40d150b4244156501c0914081500c0c51061943c024080300d05a00c1d0102d81e000c44005080480c078a58441a0b0010f801c9403400088403124040c0030000d9001c0c811810030300a0640c808002d840c0030807641481e14040e40c840c0d07440c100b450981101c01c03900005403000c2c4840501d201d4005d42500328050001711090b50005103c070b0401400c000c9103103010200c1580c03048a01003c0741d0010000b00010700110000c6c120041c02034029100540e070400b1110b000303c0b5054800305465040e2144192001e00b0f040c1013051003002038022510844110340d1b0707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 739254883 1250 739253633 739253651
    0x61d0a120909050a020702010f05030c04050d0f060c09030204061e090c031803081501170f060105090406060306180e030a0c020f061207110106060207050111010f0e0d02010608060c0904020706 84
    0x2c2c901502d44074480107540503a030f80c0e0043c40010048484003d103a0200901401800a1140200119002c40303400b03d4441c0100d000609207000c0c41100304d00024945484c1458106076075030011307101c408490003110100b11140d0b680c4452070103520040704040c44503178405020b02000e0301d5035001100300c080381d1900066000d07011042c3d4406040c1d5440540103d64071340d0421811408405202c0818042841c010700001da95880d01c202c84807001d8020b405020500b000242540d00c1141a0380c0100e200801c10f0100b41c0da00e840240007003100f03000324010524080800c1e40501c00b607020f099404540580218906000103904980080714100300f00d0740305200700f200c0030147d901c0c2c82c09002c600d0348003108810281441d40001c1c000312024200c501c042c0c0d041c85000c02041d40c0110b4040d084a5081c2440e001c440003022502d4014454a4a0002c0a40c5080d00007413200034002811840c401c2260001c008050300c0340401950752104a481c840751440411000085040139005001e5051040d680402c158038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 739256133 1250 739254883 739254899
    0xe2206030203121305030d0c06050901091e0203061e0f0912030408030f1f06050d02040801020408061b091c140d0f020111030103261b0a061d0a1209 65
    0x34180c280415092000c11210491204e2110030301c01414110020302c90000c440302c0180030b02d4411000506a81e42d00d400040c42c01400b904801c2007958001d92480760204c181070841110b1441007401d0340284a980c00040803441c45503061580c1201039241000d440d62441407144220300010060030107800360071922484481a500a103016911a00c50a6101d160840d8024446c07600204104c68014240380302c415000311240781c03142613451380c3c9031185e603031031800700004041e10860307200d19000d40c800a40059225008158240200a00405c0040080e600441b130410b80c02054801c640c086000380c0d1050380e5010060107150680d1080511002d00342d10020a9401d1110801d8400c0214144065010b05a40e0a00c118003003820721140c01400c55045880f034103010f2800903421041c103044030440781e04409459003501c4400340020380fa004070f001c040c011540c44800e00441210350314186101c10486040855480c1010b0900000030041207034651121a140c4a00b41100702c1481071100c40032400b09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 739257383 1250 739256133 739256143
    0x1801120906140606090a090c091a070203010c0504030b06011b06020705210c060a0902041512031b03020c21070609030b0714030712140f160e2206030203 67
    0xd40965800a114141042140340328603004003e40e22a9004000a50707280c1e43e014010804d070b03100c141c00010b00c0c2c075100034103a580030000c5c1c11409400c880741903800d2440043c00001d042881c8203034000d001f00b44003c9000d0780c0360701607400b0050002000500043c055482504150324035034440082c0b5944013115203441003240d001040580d00c0307800840c2d0300400c43c1d4501c3d58001a0702503492800b440c2c14034420f80540c49000c00303083c07040040c3c0c44407140c6040d941d854001d50100041c08032015003040d81c6a51404103112881f0f0110701140403100380000e84240000d215100d1034058000d4542c1c016804d041190b40462a0390300003a84450b10a40e00208404002e100058012a110207407940e096080001c4410f030300070844000c00043c2004100180c4141007900e401c00d040e801c00c1d030071560784200303101c001e02a1140d42d400310381002070422542403510b81c0c095005030380014110507040003962048481a80454510340c1110035030f40890a07420781e02076184c40c140c001c1c4900241864803540040d00305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 739258633 1250 739257383 739257401
    0xe060d02180108010b1303060902240307020105070504050d03210501090605030f07030309030308130516050f030601060503060d020f03060103050c0a170c0607080c0105090708070b0f180112 83
    0x1011080054180d503041200341340940001000c00781000710000056a08103000c0c0001049035480311001c004545401034405e642d65022528168030074544900840d117a00200ca00d5030048d03003010042080c07180184115005d488001d040c501031051907840654901c80100841e0404000e83c07545070039500505d2251501070600b101c00891a02d14200030507182002100050704650030031401040060342000092044950600b13000d0620384c0e56007030011000352419030203003c0d8022000010103019147d02220b05803101191200203a0032285c0615540d4a0300740981d00101d4010008100c69141c1454040e140038401485440c03480e099602180c00c0081c280c1c02203406034482602c2074800e2821680140190500760516000c04078410f030b4003540c41202941c0c280c0140400a166011f0010410445010b0901d40c1c00910550400e440d0740f590310035840c4100a0309005407040070a1b500c010000311460744c41904002410858002c10403c04a0036120310365050240e040e012403500c20322400340000c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 739259883 1250 739258633 739258657
    0xc0507150213050a0e01030f0201170103030314072613021306030b06031b1c05060403120c090f09020a03020909040609061a030d0807140f0c010b100f0e060d02 70
    0x41d011040445400294583c03c07a034801c9185600500c03c42c0380e178000c1c00e4111390b0032001e8601901382c3c1e0300042e07510119400c049114003001c2070012040c580c041c2c1000503c880440800811540c3c2c0150441d04d0001520303c150a907140890102e2403000742d0600303250069800071031a0192241a0f000554100100d884e1507500f90b03c42f00c2c200203120744998510b5002c1030039005090360f003120700e07aa2100141c1700c800b07141c401c8501140200340a03080390103044815501c0307421141c1c0303400e1504019011507504154101c6c0071b070602e880c184010780f080c600c96080300c8049140700b204da800e00030316201941103103101000301039082c001e068140e5185440305001e03d00038840020816018104101038500aa420b403d03140f024030110b14464800040e500c0c12202d241c0f50405e250740341d0146c00c5610300c6180c901d003612101301290203800c90041c10001c11301c524207040200300142000040c0305100701c0c640d41c04008542c90580038500d01b0301420b003010100d80000c00091410251400a00c2203030080440100303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 739261133 1250 739259883 739259887
    0x2031b03090a060816020304061e0314070201090209060102010c0914060c01111803010219120b04050c0d0b040b010e060f090a03060914070515160b0901021908060d03030c05071502 79
    0x41517442d00305001d071210a5600c051072400d410600040d100040ca81642440c0c070005441c40311416109605c00b0810810846440c0014140107400074007903c1d807124140e00c03400402d00842c815600500c59419401c041d621010701540c94200910506c2c01c18041d490b401840030080ac03142c80304280300d4501d4400740e160545494040b6007520880402c5072908440c001ea20401c20001928006020500b0010141c07901d50580c00d80410910080c10141180507001400d203010b0089002c8814013400c60514404410480d4548070810001510207000d0241c2c0424012803880d049414504010404ea05000f03031103d1030440c4401c0481e0369110203034015104a40d40e981180304010348603050301c00d104d80440007420300034200310004500480c2410010414000001c40495001464803d0788256800400850240c6024003419000c0d41c4528590880002000c2c600925140900c2440e402400080c268290003519640e050b401014034072110414800c0c107000c0382d0f0015111268280b0b111320620005a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 739262383 1250 739261133 739261141
    0x1f0213030c080708062202031c0917070f060e012a170c1b03070b030a020702040524011b080a0201060e0a0903020307020f2409091602031b03090a0608 66
    0x290624205800401340c81c0c0042090000c0c1c001001c204031142c02000000d0b10303808990744000303407500f4601c8010403c0704d00320784440c5500076000100c500450f10000f201440e00902071071155203580081c0200010081d03102010301c103a51050340164443c45040c1042c0f8030890301c00041c0ca800388650303961410219844940c4804200c030400780b0000340e00d072801c8000e050a80e05882140c40b4910103108900307c08900080411035901000349000801c05211445c0d92410820340c58400380d0f01c5002e0503801542004045084040100d400600840c0101047e0240790b0408004450f4007601904a090000340160281e0100c1c0503d001081d80504580000030310610740040600b605e9001006821110310304207071040131a40100c225518254121810846100700b00c00142c8400310030303071079078442d045514001105052110014181b559003150103005c140d80e81160170f00c0381d000540c80000142c1082c4110f01030070341181004104220071509417400e00005601140c0c0d081c620341d22100010302400240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 739263633 1250 739262383 739262399
    0x304140d020a0b1801050307020c10032403051e0601060c05010212070f02010b010f02151816031505071b06092103060506090a03080a0306080304150206070804051f0213030c 76
    0x44d1072550f6007803c0541c02e5245c51603010713441d08039194855010341c11207079003459203500c01e50000c440e42e8404146c1600e0341101c500150000a12030000f1a00f9119061304042095684141050602e032010000c12542e03003020403c958201c0d01440443d019902400351601990f1444c0d5018411034850b0390381c22010700d1401009007551510004c0c1818003c4801d20001d00d958086211040301015004600490301c1e12011a009110600d00c9844c060207540850320030214501d2010003100e0042c003041100c4034076110007604880b42a01c0000210303c1c0e840701c1c80391ba0782804102010b001e001e81c900141407842c50f11840f80d0004000c0340c590903003c0e16070148582e5900341c0b01d003030054030003034504038101501007001c43c2c20a45540400707020380c40c000c02c200c1840b034481c3c0c001c0c0c40070b000070009490300c41e55104803601442007184035460140c0140c4000501c40c6100d41c02c081c0c4220b030040b005000748104200051030340c155075020fa8610740e40030011485080e00f180c4551005520031030303003001c00500d0650b036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 739264883 1250 739263633 739263667
    0x309020f090408030705160609121101050f130f0c0b03060a0b1e070f14010203180102031005010f0e06041418040302060630061b040303020304140d020a0b 68
    0x103514416407030711040c070002c51102e800f903c2d4000001d041043d5144100311450b030110742c0c1080c000f041d440c10911102c0400020b540c00f505051a2612128a00744420303410500380c0700202c4c2d61071000c0c1950b0002500401409401c0e40361540148041c100b021080d440b2040e403890550056403d030710002007801001e04112548200400244072004d003400c0c0d10324000c20542003446a4110b8100021a41c0b80902c00f0ba8292050b80c0c0768000081c03000c040c00d041c4818080e400454001050b010107610691000c5818000c80e84034002c080c00d552885400c220055804802440301403080005070354801986484240040020b025902d0240f5070000000c410044a60012849018000303600f030284400641c0009080390070404c229106020f0f40100f904001c8586034100c0c030221208883c0c3c0c200d810007440400d11314014442d40c1c400c01d27088641210314045510a0780b1005006900800c401c00c4410403050407008203031801000510720350340a1300020f8051049402c000203100c000a00888220142c0c02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 739266133 1250 739264883 739264909
    0x302120f06190e0c03041e05010e070f050f040f1104060c1205211909030509151603031107020604030506070813020919091e050c150a120b04020a030902 67
    0x10582c0b502070b0605062034000040603200302054803022000c20208128000e0080300910540c410744085801c604242d4080c05001a4030f040c54064010049a14846030749000141d86001d1701040c5405203d1003844002c20141140140490745e40da1102c0041c2c80700c3c80104010003969603011488445814052540060341002c0010300104021011540e0021010050201c0350315012001540d02c50620804190790351006901603440c240c0701404054000001d03101440301944c428820300000d01041c080791042a0240a03d80502d5180000103480398004a0440d04117100f20703404d02d82d0b40e602240c1544c0050b0402c90303070381d00010708100510f94450075203580213480f8030b040c1c0160389098008c24100800900521b68030001c40540c2c60030a25250070250007a03500c0013052016030981c03060440801200f813021906c9005269071545540743c0059101103084084130a00d00e4212000030590313043c24201d1038040c4440c0c907410000855982c0d44054104040540c0780407a00c50710500c104040211448 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 739267383 1250 739266133 739266169
    0x6070f110a212703120309060c03020409290f030f1020030c070825060606030c0302030603030301090504050a120e1003090507090b0d080f0405121c0c030302120f06 72
    0xd500b841d242140501c00002c517a0000c034905c450440450040340900001e81026181d1170034076600541c0c080d0b2540c010011208803500402044040384205044082d03500080d00507500b2002018045142c4404170300240c0d10010100c03a030a0800410060a14901080d040b1409a440e1544410341441c44464518407800702e200500d54600381e00e60191034014450040c00340400803130605881005a5103c5421034114a944d04800110f841c0c0308018100c40d004400c0003134200b1800c2d1010500a0003030345d00458005010f142547c0c00d01d468400282001803060324280701c1c001e20280815400c001d200702d100351b181e59810340d450541307040c09100480c10202300d040500c0c10349c2c44c002040c2c0210301c4001741e40110601260300362444002502940074a035014004100000382d0006003400701005108498041e034800c160f100b4400e400d1070310384440a00c0b0440564031051030002c014400c1c0150fa80e207511a0500508102207500741c00c2040302d0880c2c10300280d15040e0f0910400d45450507075944880c582c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 739268633 1250 739267383 739267427
    0x11030601080a230313090c21050405010b120706090f030812071101110702040f0509031804020f0a020a031101060b041e081207060501050306070f110a21 67
    0xc04880e42d07140c1c1070301c001c0c2012900200c141085a445415a00c240e0f00c444200c03500c426000300d00d03c1140c0603a2081c80c113041e01c1c0003900788501b0f0040701c0010041d402a00402540b1012000220103030100405c101c1d26550383d2107580e141c80e5104259825032031207100050110341d080c00c902400e4020590000700d04203041d01800c1001079104030403500506801d0f1407004150302da450323003566086001c8030f109006c3e500f420b00c04505208000042c00b50345000b104c0a0200c910300c0c001b95030440d00207881046040d0800c1082c611307142070300c00d51503299a00c003810051604644500407400c0b5001074a007200182c100c1c0703203c00b00b81a4410791109500303414000130412a40f812a4600c102d02c21031040c030340c80d01885111456900440f0380c4000c01000c822050310801808581c0315409030b07104060880b4030074640400400d0354140000c0052180000b61202e00c032003041403200341da030312004450358219407180c00c40201c00150203007614028102d6011624400080d2070802800c0b030740003140412107900311 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 739269883 1250 739268633 739268639
    0xe0a030b10181a040218030706020325260d05010905010503150f0115120212100b040609060302090d02043206090411150307021b030c01021506060c010906020711030601 74
    0x800e0541844070f0300708580050360b8400000b030128449080d500011fa241c000c00c400011800d401200401c90b9681082554025540000c02040004804100580a40c5100a4510b0580e44040c4ac0c032040d1510720000d64200217050413200700340e600c240c10245130a600c0f03000400407803d080180800c5003400e010b040440c0d14090042990b0a00144581c0020441080d00040303050301907484403600d1202c01c1d800b5503807505d6145004905000a445c040010000e404001810342e201800303a030203840c4e20b50b540100442c944a0308074041d4100c000496440109148000010389d00c3c0e1013142030981c5031100020354415a60b1102840d55500589151261310310030800c0b02c951345842116520640c8204202c21081041002c0350194440300501d1078a05000003d2101c02500000c43c491003118034038103c1400d00d041c0c0c0516840c2d51000e82440d02580c84000003039400c0410340b940e1a030241c0701414003410842000d01203425103503803c6c8165109680003e0301e105000704800000c440240540090400d03500d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 739271133 1250 739269883 739269911
    0x31106161b021509010e18180f0d03020912191506050a090c0c080307090305060117030316031811120102090d0b041a070e031509030a0e0a030b1018 65
    0x910f0103040450780500040b0095140e02515805013851406459042c400c3e2140b800c43ca103030441a200b104124058000c0d03510006c1002411144400c1140b0182031060755400e0164041d40241d0b0849070f00244680d400d42400c14100418441d90081940a0381d40e082241003820315030091074160144903051150a00c401c2d00e0b9200b1220407183d50f510002201e1070706070400c483c2c0c0c0c200400001c000c100c000003031144595014455070151b80c0981c041d1246643d03130b01100802d03000a0b613401e05040d001400040c4911003c08101c070b14911646c103001c1829200401070340140410410103c955903103035114a07040c1d00380112000c000c840080001c5262420100014040c103403640c4008204030a1880028204004005054661401520300c01c110341003554000d043d041d03410900b50300034810003092102140912554600a14112010b14541810280203c071944401411207400c5030340c0c0e020020001c1c074461002e0348160103e0000c0450142044004e00b0340e1a00100034040c0c00c2d09011076100604 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 739272383 1250 739271133 739271149
    0x1f080c031509160f060207050d12030507020a06051807210f031404030b0601020d0804030f050a021501082805030d05180105090615040911010309031106161b02 70
    0x8080c40d203036042d40c2d00c0100518098800b10300e045a0895141c0010700601020b140b80700350341c155000d8074106601d030024072040840404010f004113107412007038041503020f580310f150448040d106036003007180305446900540b00305460b9103020075800c01000c1082d0754180005400b83c000d0b0300c54003031901c07007204000a00c94410040500049107a41c480c004041c050961030505428096125450325642c1c2800488100b0868003a80135000c0c030030010075038078880c0c4900342c800c0b6410740741d0707940216143d00304030f6598101d0300c020300540c401c8805d44000b13622f5564901e402460050000c01d10840c140b8090410749040c074000c0d201a040c84408000002e0002c01030b03846030310144000040a3307a4058186400b0010038201001c154a1305081c014010000b141007442070742500d44101c54884550140300c100c511030200513109203200c241c4d000496202c3e412980f2501d00070b2502455142000300002e05202c0d0584a5203c0c2080000c0b8134400e00781c0280054480318629281d08621100302d40114480c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 739273633 1250 739272383 739272403
    0x10215010905180a06020a0f1b080c010b0406290703120506010c023304050901090207020102031e090307090c0e210709020714070b0d051e1f080c03 65
    0x80c0741c5a0001443e66031008070100040b80c1c24a0031038090001c1424203100030f41c0110086400a0800007400340e64500500d4001d0b4440b403041d8480030f80d060542c5480115810248003e43d4554a81036211001d030349a020300d102400c2d0b00c003040a040000180d140300d100c90407031105541541c0902c0b608001c40e410030300981d28074041540c00702d0f0380d988d40d40040341d0603150036400075841030921804030112910318600d0741c3c80e56950520b0a00d001103000c0c94480360b029500c030300b07a442501c550051150503640e40207490103a2040c0103c9042021079210240301030311091050340012404a858510b500e01044081c00030b00d03501c601000072680b8014001d043e941c410800301d02640c80c10700803040040700b50a0140c03008140c441660152500c5140120281d4840b071800d0310800c01003507400d9070700200400c68408444221946901d04802ca1401c0310141000400a9010035003c41d45801107952440500d803140d6845901c002c040c03208010b503500100d100342c02c5000194070002c00c031100758400081a02013 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 739274883 1250 739273633 739273649
    0x9063b0f030415021e0d020610050310110c0f15070801050d1b170f07140d0f08040801020f030717010506160c0f0303110f0102130314010b12070503010b01021501 71
    0x6a2111001030746031410031305c1d0282a0801450001810040c01320358944030307880341e03806c0d11441c0e103d60b100f021250005015403640340e00594000700345070302d45a005103410a40d001c07216080010100d0450f0034100c10703c050b558a6042014071250032103626403507690040780d608001d1910f5041c100454400c807000b0000078203603205180c400c0030031045001580020581c2d034404024110307001450540b9a1b44c00280d0b040f4912801d180070405500e800c007940800710340a03064040505058481641c0145002000c0c0e80c0301d03008010204108034207000070920003070003602090352814103c1c40144016000100c150b2060608801407045a803048200c0300180400c0e003180ba60000c180c205003001220030b0f44405090300e50403a0000416400c481c0c4010141d15900c1a01c00c08407064101500381d214058509108006528050000071003800c0800107072008400001100c505440209203a040c5010000340f503030344082410007452409000c0c20801180c03e101400c00c0c0ca2035010914850841800b40c401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 739276133 1250 739274883 739274909
    0xb250b31030e03031902010b10030e0c1c080301120209130b06060f0c1608010c140a1b060507110105070507030813021f08040b070806010e0409063b0f0304 68
    0x882e03980800c01d8680100c0c1c0c00d260100e2074488000080d009041480e8038034084c03140d520251140b28020720403400d02c140054040d00c0c0004100d0300f0030004c5400f210080010305081550440401c0c044c4015502070070340405180c60001007401080407001006000400580d940d5a07487d00144100c0307102d80d0032131015600c982d190007410341a0444da01458454060300c3c4240140707610345004002a076022581601c000f0481c40c1c0c4640f80807035882880714a1a03c183c07004000d0155962301c02c00c0440c6181e8860382d6407280050196403800c043d10000d880c0680003030300145c41081814001c5c40f9083c0c01178200d0800b20710300081c950340500a01c500800303090300080c113010140150b4607900003a15a1201c107040c80086005510381c06003150b0b83c161019a00c1018403400560510300503026140280d0050b1100e008074500301e4208805030568403801c80c0e43d1925070070710040172060b45036103ca218018003802081c1c443d614540b94000b01111102804541c0705e03c642200c0c4281c04400c0b10203603490610030744 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 739277383 1250 739276133 739276157
    0x60f080408090d0b04060506041b0509030106180509070f120609050c06040b0a09080c0108010302060705100e0f010e030405011e050c0a030807030510030c0b250b3103 73
    0x2040c0b4040c42c10029000310350140322104204020300001d01c900d03ca0304c0300300b040340c4506c400d04c803c440c0c034582040d055100c40901e08020900460103020b138440001c4c000b045180c1c0710504d00c0a1100c050011009140e110414010409810300801000d01101c5600d41c14440c034101d0104011600c4a01c090700c240da071282001c040c0001803244d40d285260280003107940341c0c1e4600340103040b940013021140010f52110300104e4041004078500e018080d050751100c1c01ca90842d020414194400e1703500b01d40714801c07040840070102280c0141802201d6005c0a0954007501d280c0241c01c0d2406001c003541180c100304801d0015a8000c50740b11460004091506404a980a4107644ca1b00c16040c441c8960b1250000c10320815a00080075840b540319650305020980314550701c00d000880601000300038440b1341c1c400384400c107407481c06840200c000f000500900000840311150040b4041d0003610b48100600802c00d00450316000310a146103400340900708581030390a110250088404018104400c160701c0e8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 739278633 1250 739277383 739277393
    0xf06150d0b0604030b010b1c0c020304091a0411030603071d0c0903070305100506040b0301140a020a21050109060e0112020f21010c0e1228050d0e03100204060f0804 72
    0x668041c1d6480341c4820500c0d61107807000601c0750022084249209945101000808c06a0049030000c00c0703160010b6040500300702a020203416200842020384881003940d18540d43d40c0d010300c036503184032204c8465403410000b0600d41000341682296501d07405040d9680b05155000318000d61284035041801d8541121400081c2010841d41c400b07022882202000e81c8011410760050780900000c403007c00030050100203050903030f0a08140190403100c000c00290000c1095002010a07800b82c0ca00095190010406072584a00406540003050340d5803005208590340d600c19100509040b1450b10059894082d030f500d46080c62580013070183c0e401c00001c4040380c890750f80504c1d005030203203070401840c904207034054001c14411b050200007858040c030200d03c60a0107032030442414820000380000c0100084105410303802102c400069002c0100000c0200c0d500b4030000340c02c20026950741041d0b001c10f100301840c1403a03001d41c842010348100001c110740303508003a241c0c0c0700c01c949052900700c555507030400c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 739279883 1250 739278633 739278637
    0x1106070c0f0b0309150103201903150b010c050d03150906061d102a0803100f1505123706091a01050c01180b0f06150d0b06 54
    0x80c014a09040400306800b110350340690712840010b42211030314012a02d030061400000e210140529074408042c0002c400c80c0300c0d00200b24900942514800551840c115a414403103500960301d5107a18592041081070b18060180c042c4400d05e0112025240340c0c6070a0b895030b0f01d8400f03079801c2c10343e1084101020359011140304024004a0010090307141c1d5240d02500c0d90300000a0300c8094040e0710b0301003500d4606426851040b07100c0355505141801c1c00f00c4004070480c00c1030002d00480181880c807030002506c2d040114420108240c6c40246146455009042d20a650b0002446c00003100600c00300c2942c40015290701c114980b0304040144c541e0207000824261001031701c0c0203c0900c4441c40141c0a000700108201e50714264100001607841585108031440701d03404481800049030000703119031203100942000c001f000e00000f0290004140300c030f181300c9403450840300754168402300700c07450f1001e900c0c2d15401603040d00c4141c81a1445510908280b089001102030309650b1407060407240c4030001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 739281133 1250 739279883 739279889
    0x50a020c0d03170906010f0b0901050c16030507210b0a0917041401030504050309090c0f070c03020901080a0f060c050705070e0906100e040809040e15070e01020a1106070c 75
    0x802490034000c0c1c0d040090045410300c2500d03600804034008240e101c280080c690707049400b4540903004a03400c00012486541c0440c18071410060140a6138844d501c051054088840c4078050100741245540b40180c10b1412551102c4841104a01c401e14502c03134101643d8001d40d4001d2031603c5a0f5103148290005040740d040182c00201a6074a00300502c80c13034070007801594a0900304098040c8500300440941c0c504550043c00303a0414804130000341880701013280c0017070b4051030071424110300c5105079046400c02034064a00e000d09440400c11350801300c2141d405404e282d0041d00700d20b9865202c0360f0310500300c0c0900038242c0341c1ea6048580750038400c00a46400551040564030740391384e03515030081444002d0b1a1000203015400c086a0ba082c500740f44170341191b14596032086156100d8840145503085944040c1d0000d881d500c2c501d1a0000031b000403104001c498159442c1c0c3d007820710004217641c0002c0011030540d0710110464010030ba0341d058007184154210b8226a480840b46010305000350554 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 739282383 1250 739281133 739281139
    0x100809190c091a011209020f150c060709030317041a10051815090f0c0913090503071101050f0d091407060c12030204140103091a09071a0c030a050a020c 67
    0x5012440b828503c8512a4840100345c1c0d944460502020500086801044000303501142e100540d08003418204290404a600160300d1800c082c031075030005050490131507001000481409060040617002481580100900c07070041c0390304e1034242e480100100c6820b213000d02c404114070005445240c0001c02101502e4050078502401c00030307819400c0301031010780b405049944040314a01840c1005404180f2400c6203840414003a150b003100031242c1d51200c0c00f250742050301e241002d01001c90038058104064880c00086641d1031083c1070000344482d04603c8503040260401040001c4400d00341950003400d244e2000089a0140c0c3c41c0c81d800c0c000d81c10452a030b15006600c400502150082c440d020414000da0004003010090f840450403441980103e040014001801076440e501c02d9002c1100c0c1403082907000d400a00c0c0c084a42d5007108104c9013030400e9400040188170400400c0c44031485880c0d040183da00f0492548021a00d90080c1002d15040100128900c034400303108000c40c0f8444c81c070103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 739283633 1250 739282383 739282391
    0x130f060e0706030605091308070b1e01060815030c0a0605131205030403140a0f030e010c0b0408040501020c1507020d031704050a120f090501080c1314100809190c09 72
    0xb440010780948010300c1501e206062810005081c91079040c801204168001c08161400e0150341e0307203030b010305806040e090403000015a01e010900301444038501030107803a11060070f41c1c0392003c02d082d00455525502c502940041d49100d241d5141c038840c8006813078090514035102d002802511281c00001c1e4032541d07058919a240000f071000c080004d00c141c03030050740500b28659010790403903502c5c5243c40b00100700d00e980c5000c00020a208514102014005240c4582589901d4941002950060310150b500c00800181000607603010010040100b106880b55242e507109450780f40d4250181010190145117136041c035008261184c0d10000252461440d03148441c2020300300b0139540d02e0216401c40f5490102c290030a0614000c020340442d403101ca03660703041640d05180c01104c0d00b181c06400c0342c04100c400d0050012505400e201400a00000b003081c4500d502d00408000400c0e5545204805200e569002d02004090205203285821000c405036100b40302c1070318140c401c444603540082c0c25a4a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 739284883 1250 739283633 739283639
    0xf0b04090c09110d241d04020f0a030602180307050312071401020705032d0f070f03020f0312060307050a0b0a03020721020a110916080402030c041e0e0303130f060e07 73
    0xf1100e8403483c1c5400c20b400b07402d8560701c80041c40040305806e2a100d048599500c001001882c0181074200c4401000d01804e01c0341d550307559440160707044806030610f00403010710500002d04080003004010102200100148146110140100d03c10624054120441c40b0344d000103002c02501151f6485510100b00c982c2d50b1800d20101000c03498844400c848107101820401c14161713481d00781c2d04440106440146008000d6540305031440c80d0300b000700c06600540400e4024082c0900160044281c450324022503860510205802d04103140c100340d204401034142884260444819207900542070300300141d80d20142d0500040e8000c1800140c03034281c464245c60310b445c030760120313902c2940c51040d8002c4940030100d40412030346000481d01200260281c120b4480c20b00d00c10310070aa0858005410b560308801c900c408074003502c4a01c40e403070201e020544c1c803420341c2020368404d64001c2c1c252180914250b091802c01045640c1190501038007001c2d000841d01c052108075406030010b808108200d0703c1c0c09035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 739286133 1250 739284883 739284911
    0x904060b220602011b051309020412030e1002030403260301060329131a030307080309120403053316090b07050c01051612030f0b04090c09110d 63
    0x152600041c1401c0c060720002034114014001d601e41c01429801074000c00d801e40c0c4003101d05400072511060140300581000454a506200800250114903007900029505041c0500b000c10382240440c010002a02005c002c164048143e500307481d03210b208400c001c400b0400d04003100300103c411405803040040001161500360b170041c89080f860010003695140542403185c1a584400101074100e1401401c152101d070341c0758400381003031501c00425118280700002092850f0080d41044404103800070521440743c1041051058909030087c01c18030342410341c1d5645c0d032100e00d03480d01d401407081c0203940007040041c2000000d03c1c1c40028858102c035460311b00307400d903440180f91014401040001c100400c181088904132201941c00074024071005080000440d00b170303405809000c40008000c10710000141410301d100c680103141d50740c04a030212694010004607403607024114072440c0f80c21107030030006640e280ca8208680b40341c1000254404c0c2c000103d50a03114154201c0380f05440c1c0686416a00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 739287383 1250 739286133 739286167
    0x1e0f050f030a08031e0c070218060102010e0102070b0703110f0d020f0c06040606150f05030f130807050a02040f0c02061b0c12130603050601090b07030212041403010f06050f060904060b 81
    0x1042d000b80120b42c0c4402c040d100051245c50307c06500482d000748001c1d11494110301030b03034000d40180300001307107181d03500d0413642244c1250504940703c1c14084244584030360305014084e074000c1041c44151800d040749807015860301c00c81d00040101da4000c030302d00382803225100a8449017000f0b0016250340c0d2500f40751000c010001806001c1520903000e10f600002032045104515100c62500c4045c65900d0302c070300b25681c80d00002d10740c1c2070800511401a0001e48120090f0004620a2005000411151040000340d1300c1c40740700100c80702d02d0400030454040c0d00140c5a03030840d005008100e11a10300c00310020300e82c070441d0388035851841011003804943c10030f10003c1c2603001c400043c141059440b2401102600c009807881800560b10140038400310071100014000f69109004450404912070b42030060340d013080e0b00140c1c05503808a00100d840c10280030752450282090802c1048c1800c03c4000340c400300329115058014100883c20044035165030f40003401501004100c242c4408801944401d18 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 739288633 1250 739287383 739287421
    0x302090a03030c1104020d021b0610061b050d090e01121505100803161103030c06041515180b0103092307050a0902210403020309010c05011b03061e0f050f030a0803 72
    0x864401c0d1b1281d02104002b19106010301c810040b00f10b000c071316080e400c8a20012028002004004540402c00046c01c200408a00513400e41c0320703003608500c2c2001034106480142c2c000041c1814103d80c480000701c4075040c1c486540c03d605030020301c9031520715000d04460351035000700039a03100025059101e204a2941100c071948230307101d80e0b40d4401d280c1d0280340d141e01806048103003a03402040032400241206141d6111505108400580511050150111104268498040c41c0701703941c40300305401c0d610701405c00707440020f01301840310a0300c582d03404c81400c03008501545403190400c041005180306000580c001e01004041751240764440308080e00a500c0014001c080015031050300800c41c145000345407003650150081e600300740040006603288140e0b550102c0d402c4d585c031000c004040c03c40340c40c20829090556800580c4500701140e4404020079a0b240300507060b09000104550304101e94440191030040c0c401c0341c07100240401003032410742091401044200c000c0108103500d8800543c0c1e1504c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 739289883 1250 739288633 739288657
    0x50a0504021215420a091b27062006091209010c050604320307020f0f2101060803040e0c0f070507060810050915120712060203160302090a03030c1104020d02 69
    0x5695500c3c81703c06d08585800c2040032440340c603028100d100d03500410030801e8800c0c13041210030904401080902d081411900900041903189608070680205224900c0341100080004c04c0389061060720190760f001103107401000240000303a03080a5034803c14486101a50050840fa420b007030514028090b810031004c041d0480d00f83d09215040b40210350303900401948100b0180d80740000c6134080c0402d05034078902803a000720b5060566600c6850740345c4106000c03002a40920038510501c3c0e17446080d1a020b5100e40600d6009000501c100d0785110606900b200d40032100c56911000403021034445e01460101030014080c80070000f40d86500007240d5407141d05080e003086502074542c01000f196481c1a9081c0601d00c0ba2913100d1034150910522074000030341e6031001c441d00f080e506c15403403101140c00c03c000c4407103607000300c180160080700440540c580c103c107080560500c611180414250303040361101608024801c1d02c01b03c1489080c040d41201034801410555607600702c20070401c080d5010101d841c403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 739291133 1250 739289883 739289899
    0x40504023d020d080103031d130c140a090605031008010e060403030615050304142b021c051e040b1306020c0103200d0609050a050402121542 62
    0xd4602e10102e580415005151600c0102d6401c64030110340354043e20480f8400304541c6810981503a89444801c03152115151003c14140e15200b002414030100116296040f207051010b000203c1d0003901440c151149880d01a0701c980d16600a51750095055000c1c0c0391035464010407012200d0702207061480f0384d0007070f1400d20040b0303980e001c0b021000030818140f200154050001c0b4000070f09140710f00711700c4d00030001110000319000b80d5165142090040c20000700c0d0800b40c0c040d83d003640500c02c03500704502003002c81004c07402c100c0c1c2c050810310449401c40c4108401140160003c1241c00c1910080d00c0b00c00303c0c89440d0284001c044914500ca400360030054441c0860300c034050f40c444d009914100d9400e0b00500482000803240800b00c4c0c008202c0b43c003201da150030012410300b0240c03160501c60341255101203898105801485a100d01d001c2044510f0703048503900c1c07120002300380003198122203004043e9201414219513900001c0141020720b00843d502c500b84e41806001c0a016a01c1c6401159100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 739292383 1250 739291133 739291249
    0x30311070605090103090503090909061506030108070e0603330109180210030b0d0f060b0a080a0b06211b100c12090302090f0a050a020a0e04050402 65
    0x140d4a124512441e030004604100c006081e5101b0f0f00080400b5114504403030401240c540050301400301200e4840c52071b481181006501c01c0c3d00d00403203400010986040740340d5410180328039250409401904026018100400c089032010418441d00e030145200d021000380c40040049400c00401000e8070781e44180c1d4002080030011031107101c40a4000c1805d1a07031030061070303003400080c003030288a54050580d1400b001590784c480b00e0701840c03501d109a00f00400040c043c070300f4104030f0381e1031440e080c09a40042c005001414001400ca1480340d00001c920045540e00000100e0303842c03e00303440000302c10400c080300001007000101c41440c01c1014a10300d00c03014818080c41201120306406200082107230300008085561001c10306411140352410b40003d580301e80109502100c2130720701d18000c81d07a2000304007021045100f00b030740102c0e4414003940761440c0d00c240108824203184116101e1a511404642150340d01c0101c41c50000215461900c2d210a044c3d1400108101d41022881000b40542203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 739293633 1250 739292383 739292417
    0xc06240108060d300c061d0d030510050d2f030705210703032c01080c181306050f09040c170118080a0e0a030b130813030c0303 56
    0x110300c5603101900e580f00082240d1560300031150f9030a0f01c900380c3c00042d146000c2501100b281a81810015200c03900501d9040c075190341150341c01c9041000c030b00d900e2066031030088000300f05800d4145581ca0042100c3c1c94031500344041610381c3d40310507400284401508100310180b030000340b039800c500820400c0a803403184141c0c0d40c029907a00c4154941c01401080c03143c1d10744440c0494461541b086540c0191310050741551800c21260025404140c1800d1000038403910802d010404801006441150082100c0003a00100002c0c0103004101c0002c92500c0d500030000480d80388a40c001002d0320740c2c11b5000d02200000700100d01500340503001150026500c1c1c2804500c06006541c090351206401d0701d041c0d80441321001d6001c400740d003552160f0002c00014031a0025451150184035500d0f5582200440580382d1040040f009019075601041000415a01c64034a1382c00031403400d0380301201e0f2640c0390030b140500c240f150400c0244144400401401050744003a000d0324800d0711501e0700c800e000d48107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 739294883 1250 739293633 739293647
    0x12060c03200405130e0f060f0c0a020c060f0c0d0809010605042c070b1c0c0216050105092e030506030f210d0e10050a020c03031b0c062401 61
    0x1810040700410041020303040814000c1c0030515500400140c40249200040c24075124084c00c2240d90300060a00201007101003038181c02292803100d241c80c00c11860000f940f17031460798410781d1044501040d5441a000094211400f008805055a50982c420b0b400a041e10b00141c030003800a601e07040d40400c1508040c4120f2050003120280ba9004900c81268098590101c60000c80b20b402281000120400201c0281c410032104070b140041409899220004990b0300344000303070865000c2e007540c80420421091400540c0c00a180c180d65500b881804105120a5001000001c1e5541068802c650000c45168142550960742c2403090b80c8910781059950b50318142d080c0310301e41042d0f004201c65000401d9421011499035440d0381032072030150500045031070780300e410101904104503c1040070740d54400d25a00139411101107003801075251000b030b90390000820b11498401ea0f4a00000c0081e00c10041ea007640203010b080f80c0e514501090800000b0100c043c0c0c00280070a061812101c075801011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 739296133 1250 739294883 739294931
    0x10f090209150f1e0117010302210c1203040905090105010e011e0302060d020d0507050c0304140d020604030c0e06010e06070305071103060709030308060d050303060607060612060c03 80
    0x10110119454640c216000c11030440318071a800070210f0740081da991601c080c80b04c0c1440410302110104441c010014080843d000941c894031040305006000503620001e94841f020509038202e40c0c8802078803044e6241c24000e001c5581e20040000d442c0000c01e40010043c02940c0d400d11040c001030720751200d800e098510038000d00314880f00480c0103010405085240d10040c0d5410007070803046541c0d039000b2460715441809410755482d0000f44506407a4564090350750011200d01c0c0440c50214850030480e20390103540110f4154580076900302e00d01303580d0300321009a000e8000300040c0c1c2c0ca03540c030300e094141003505210f003042000041c0000360032903006500c101280c1402030f03c40c038075103c0966003c5030554403802c4201c2e0820001800c40c081138804024480c8202840c0d251109090b09609019010000042509204203003900280002404c04001d881c0c01400c00d40340c1503201c145074580b15014104542201c6101e40b100c00c9100c0c281300158002449401494400300900140e207801d03000c500380094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 739297383 1250 739296133 739296139
    0x1317070f14100f0c0602041202030c01020f03031602010603050f1c0302030408091513090e100203090304120c03050d030b090901021815071509021815090403090305061305010f0902 79
    0x4142981c0b450040c906800d01940b80d24200b110001566102412130300281c003c00603540400740840110708041144c05000102400202460008504a50b5403032000420701d44201d0f0150002440b968003d401900246510006540c000c94004580503035032008138032940c80302100541c1c070311101402842103a000d182c22914061030500c1080070f00c03000310359008480f100b0704800c100d105517540003821801c014014900c008180c00091201091824121001500c00c03144100244214150700200325011a03004021500451b03030346040030f101c100c10700ea00286c0140034040058551690540c080e02000c60101d50810168891000d0b26080340071b40d8080c00d482644906c01240a031070891045508940b49210b00ba242c0821581c07110321009041080344143c54840c0c61600c114501203403c4200e0030801e0070b0048e410b107080c4442c40400345100807481d010340300601c042818144144810006181c02c00d00300c4465083c05810640e0083d2045801e4441307510b0821040300300300860040c003014540003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 739298633 1250 739297383 739297399
    0xf0a0f21090603020304170310060201060609050d02042d05060306070906021005150a030303140109020f070803131a0702070f0f06030b190b070b0c1c021317070f14 72
    0x2101083e0003d44c0702030004d5074400d0004d5110641d55144d80300440c0318011806043d10354a10b880d1000e0300b5940703241c104e070040c03103585e0b08140404d880c1e00c41c1194001d03404940128450307a800c066000c0085441c3c0d62140803019003e00e010700840355404c881c0c000c00e0107800f181e0256550120844444205020351001600950045541d44049030403007604110b11422000742038156000107000c0c01019407044000c00e480d002c0c0440350b00e450480c002c0c01007071802415460075110141c810140e21680100502d1082c012004c1981941c407000d0700a000c6038410050120b51241c0c0307801c00d0180d00100c40c110014072500070b001c200020401c002c80b040b100044128901310b420b145050700a40890918241c005c1c250100007403860300d0410510005200c2c0c0700780d4942d80d80309824030140084c0c000b0003880da8602e08208042d1010000e610f000c0b1441092080181c8502c900740c40b254200d0540c0d404020898401c140380319200c6000f16a500031116100788441c1c090340d540703420000f00421040074541c05201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 739299883 1250 739298633 739298639
    0x180c010f050a02010615170c041d070905040213211101031d01060e070f0201060b030610050705060903031617040803040321020702010e1914030f0a0f2109 68
    0x601d002d00344076071150001040c80c54071115804264440e07034a06c0800101481a0240140311120b90f09070003c5062515034685410405030106410360b07031089584d1380c1c3e490400120024850001d00c005040d00a00035560b07440c210400f240008402d02032100252001c03003501515130180c04003a41880d6004109241510342000150000d1582c80b80e9094141c0c0d1050081d200e461084c401c0304080d002c2000c2e5404103080030301c0c008003036a4212807104103681c0740c50f000740150b00130311040e41c2c1d220030308171030300c90310034a940108841134013805000400c10302c628010f00c0740442010003c0d41c0b0031028285650141150240e084032500312a4207a0400880000d0100d00400c1c0d0340002581c0c0b150013400c1690342d100c804040904c542d050048003115442e40400c415045603804260041a000100c41c1000c0540d040407103c4064119841000c8029281c600e40c440185c81c103002141c1d984102030160355244540781080d003d80d503c8508126503100141d0320b100c28a84208641d81e001c01e0300c580c2e5a041d0542 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 739301133 1250 739299883 739299887
    0xa0f0b010e01090b250803070807140409050a09050102070b090c040b0d0f020301090b0901061814150103110f030604050c04060503041b0e010602032a1f020c070e180c010f 75
    0x2101030721520b20300b0085004d28400c40103014100706006e215501c00e60b80c034a00764000900c126009400f0408012804403100d0900c610704050364207880e2441360005607516840714501c0102881d1100500550000c11508184805416002c0c0f0039620b007810f403030b1061100b13010030040b41c4a400c4210f40c0301d01c240860302c0200e0201034268000c00e202400001d004c4040d40c840007800101220170141581d140c200032f0000d01521003000c04001d90052003808414560406040c010368010f19402001d00003840c1580b040e0700c0303078001404101440b4115603071074800d064541450351013150301c00c0c0a581002c0101c0d046c010201e00712000ca0f41180d40b1903055803a07541c0e035010b403020740310303040c003105089210081404940c44420500030b00c0550003c581e140540c51925108030550320800c0c400310025818a0003506002c03540c040d0305181003100380c4191101102035002409903510401c02442117100220752b1380701c401901401034804000c1088080d80140585503550041c04200e40001d403090030300741c40c0d01c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 739302383 1250 739301133 739301137
    0xc120c1908280c17040b070b150102060f01140307090c03150f0302060708030c0f03160e0d0203070b09121c120c0c020d06020c0f010b131505060f040e0a0f0b010e01090b 74
    0x4070800c248245003598460040486c2d030090f042c1034591080b40320a1001c0c0100c64030303142e40f0102d0203001030710040c500f610400a00b83c60500c80d0100e800a50803004810f51303003d004150190603c42410040d40003400740c0100200100503a01c1c0340f80c88503e001003203070160482440212503005010516064840e07880c0321060b00054110b442e01d20051112080d4034082030003030340c8201342203020f1036450038820380b0040c50114601503450007400d441c0c007510050f80b0301040240c280d5086540d0039543c2e0408001203458a1440c01c10200d10b8014a442c1400100500d2201d80071180586e949416100728100c1030800c45041040b18400b2072107400c40d2500600340b0101140445000c0c0f40e00505011034505080d003004001e0380350b030f0a82c1c0d41d00d00e00d054840c94003100c05401141d413003408101c4602d0f0421580340100301c0c1c8c01105d21818001c41c681c83c1020042046501030440808551424100740080b48040d0166074200c03044d075824107000c0c44d0a540f28009401d034a00d0305075030360711100d89440b9984c1d80075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 739303633 1250 739302383 739302413
    0x90601150504030507081609051504051306022a030c060708040204020418200909040213091b030314120441070b0c120c1908280c 57
    0x7000041c00004003050041c8414401080284080c12600b88141c9005008140940003200c41c240703020148030840322802081d8048420543e400034003a08c0341d021160480019030b400a20b41070000500c644c1c000000c0900c1c05d40b031454600e03110400ae070302c002a65143d0050340c8092005034005800109014407030082c0c81c0d0840e00203440103141a4507240c2c101203400004881c00d05a03038031041843c602e03a42c0700d082ca005804031201c40501700080200040d50194010b000688034001b80041000c880d60030382d000f60304030b40d0f00c0200c010f51803d5920540c480c544007072100f940401c0c105003208448000305021a4600c003c61515644195229076581c883d005a0050365a074016015000f006042c00402003560f468a0040066000500b080d400346e1074203c0b40d80081d20050001d02031301950680020f84003501c41c0110387e680b42c490202291707062034601423503115014804803204040501482c5c40c0240123a1315040000e82c1c0e0921601c280808003e014411800040e00c400c40d80e0300410b400c00504504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 739304883 1250 739303633 739303637
    0x80f010e1f050c1611150a050d020d0624080a020405090103022e0c14010b0907083303011d0709020c0c0301050c0406080f0c1801120903031d0609060115 67
    0x10990100b84942c011a41c071901158280f5002115007a180781c007034800f5900764000166146022202d00c0b00030305c1c80c0103110309e1222880c1c003c07503540541801504100c0203056000c5800d0071866005140c0c000006c0d00d00d80341c002080007000443c01898580c021501545c8000e40307000404d91840d03003849544081c500700100102ca5070746984403d100014000103254800f5501c0648030030b600c0c24000c2c1d60b2801c41d417203202103a151000124440d1584028180e2003182401d050740e8035500c00d51040c800f103120900c522030f07403086022481c0b17100100108a00040000b50020881c0e90072801c0a080c0300c2d00e0940d110141070784003040170407600c10184c004009000e03500c07050740c462001d4180800d0a40c0d5003a500922010400f04042c07001d164442c0314036500c01500c51460030503003840030004019104152031911a1182c02c1b84542c01079006c0c4180341c075030758203000041041032224240100100640d000003006080b0004401428040000b2200c0c060304132680a4066a440e20b22805608506040b800003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 739306133 1250 739304883 739304887
    0x80a1b050306040902030a060605010f0203190c03020f0a0507030c0e060102100b0301290102010c0f090510090b0d06091104060e1201144308070315080f010e1f050c 72
    0x140c07004e204002c200b0342310708004107400d41094005006c0c045c0360706000085600500c01003c809070b59030b1400d102080613040c900013021650038120705003800d004240b9031070b10441c0214410844000360ba2405c990040071802211a1100101550f50409030707200c0d03005030b020413285d42180b030f52680321540c000401800010250020703c10242441d20318038084010418282440169580a0142a0080c0400c0c505000c0315090500302400c600078501a40d4004e072000b2022100303040c00742c016007000d003215240441e260082c10860f01c0190070540180c5511034142809111030705d054005880c00d440740740c0c442078a80c00c00c201c280b200380c03c0c440560610ba5901c0742d65513584030200440490180c107104503150f000f000308004942812100c220b026001d0300380f1502d10300342541d209086059600181c6003080d11038035494011406031582160042c0c00b00b01805e40000c210344001030103241410440000d000040c02d50700740d00d80f151032076131407001e90000400042d159000c15910160f4080700c1040701d14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 739307383 1250 739306133 739306151
    0x9050303070b10380703020a0b071205011e150e041109090f0a0e0d0507020618190f0509070801180905240f09071403070503120a080a1b05030604 64
    0x650030000d00e041506132060403403500803005008401884411071909051490402c003a94001d6580324081000382c141c550030804546078074440d03514000b500201210038001561a10201d181140607003005000752400c1c07200c00100d0f81440c007844100700015882d0200c10889070028030010700541030400606960410290000303544d20074203240110384080203014245044009203080310340041c0046003da00504e8005100c540c85800c071140305605940309a242c00f403440907241c404030302d001c034203900555191149035612070081302e002c104c400d209079104680b80d8a80a010300401c0a458140000d101c0b007005203d880300310407544c529184541c0e00029450440e4407454200400a03600034800c24540c0b0101940031840007105030000c502084a5a01e810b03c50b122680d1903100b4890300600c4100c4a0345408241c1d003e00419000b440064155040300300c030940c500e0266445110a600401e00800124007004424480d010845186405280401c188588140d07015040240340540c8561601c8000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 739308633 1250 739307383 739307399
    0x302030d26010e01230409050c01031104080a080c0a0f110f120c040e010e061008070e130b0402061b0c03011d03040509040c050a080609060709050303070b10 69
    0x1548809909654011104064100056000341404203841d2155580740c0140001c03c0300950803411510045038280102000e4144070190b050181d000310f038030525082c80442448000314600f00d54480036601005000009980000240114040c1402d1507121126040c0003603c6e200080000c54070301d40c00c44254444954560703200300f010480c100c1d203000800007031040d00e061000d40240c0d00c52003168648010140075500b282e0b1112940b010a100b680c9032044404400c1080d486500100300202c1611180d240c58103503202071403054401c038030851040c1c100000d112003035016064060207030f2891603030313820559846018200301c001e00280d9001204100d403400d0791900040b2284c600407440080e11056101d20101030840d900311904104443e000024594540700c08001c803029140102d0f8246000c2d221070620800a4602c1c0d000315400410460022030200310000300ba0384540000000c9030007039a10140c2c01c407640031551083d25090340c003c0c40140000fa406074501a444a09107000030002944d81002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 739309883 1250 739308633 739308643
    0x470604150201020c012003070c0c1a0c150c0a05030c19020d0f050a210b03011103041101140a031d1b03070509040f0818030601090c0e0d1203020f04030203 68
    0x3200d016030f50018030300c400c0740c0d828040c030a100c610180450509280102d480c01c21031100510090420556080d00c0702000441d009150207800d914141d82d82020040030311074896030042ea40d91000b07105000c58840e1010301c58003003d120b4490214900e00300010030500703940301e41026014142600041c0303c242c0c3c0181c0d04030218223524140da4001c0c0b802c0840e81130043c2084a003007010300e0420004005100c1c6403034003c1c410001480503070800c0904810308c0c203e018002c1c44100d115580c15401c080c0c500a900f01e84030040c5016034014030040181210410043d2008082c12211240e280c4085c41008000360280e8050000c0c0c1003500e041e0701191070303911201350604010740345145444000550380c018506080100701e010305002e0312102c0081c1030a440d416a0701000410080c801000000c0380130b800d07500340e803c0030f0403030501500b29107565865440c1c80c80541413100513a00021070705910342c640da2030076070802c0c0c0d01d2982003289031090030300a030002c070044c1d441104001030700d040070400000141c07001c01c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 739311133 1250 739309883 739309919
    0x2010207060c050a1d061813020a0507020a060207050916232d0d02030c040905040809010f0203090d061d1605090916060f09050301020a03470604 64
    0x1a8480d603802d40440d001d00302ca00342961040c2445c0607035041c107000e61661000c40781000100e500d02d03042c8461080004418101d00030071142d41d1400412050042500007024019a41c401c031640186591184422a51042c440c070600d90b20548d00d8002c2810180e051021201e2058640342628042c5e005107088200054403081076560040300040e03021404221144800141c0e51012080002401084024103a8010f20080c840384607400004145995911800c4600801c0c10200034032040c503003402d20148035001381030000d0124040078409100e0030320100844000c0a13004007100035924094481c000100188040d022042040c0340407403100300d03000c0001a0810000070f640d000603500300818070107c104040e001d8804c40c1d000c40c50f50792000305014518010769282d0301e0300b20020354210303000b1610b01082d0740c04150154400034048503c02e50603045400640c41d005150080030310f41e02da0b01c01d00e052040c0c07117807941c80c14900450301c0e06200084008030300c4080140328900385900c4095501403180461 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 739312383 1250 739311133 739311137
    0x3051e04050d03051b04181d0f010f05220302030c420c03060301020403060c0c0c05190b0c0f2505010c0c0608060102070312120b0f06070209040302010207060c 70
    0x90040c0d40203c1d4507004003a480a036022040701d48550750001d602050089008900d040c0100519052600d10036074420782543d13030003008401e5030512001010f52643c0218004654a5007001072023555056240100303801005a0350241c113400329420700202d40420314141c11421800204184518580100300d064810901103881001001419140d00441c0c0d011550254500d821120044032101d0810400c96000c202d1600076030b500ea55280000b4024452504001c0500c0d00d8241c40300c040d00c0d40100480100d0b8800c1e02120304007a268810440c81e00a0706c09424640300400c842889403012060142c412640c40da400c41c3d4001c948548182e04001000500044504c4001005004180f0b03c550500007008203081c54000c5603150f4680320382400032405040300740210b81c40031450a034800c21085004540106a0b00404650380380010007115844c00302d608030f142000c1c54004a4a0100c1014017424401480940b92621036401d0120440c0b000704143c0955500744000800301c4c40d0341c0034085a0113615 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 739313633 1250 739312383 739312393
    0x130b0910260a06170606030a20060f0d050703050105061c0f1107030807050f19050c0a0510110f07060510120602120a09030c020603181605040b120604020103051e0405 73
    0x40407500c4c444ca075801146005a003d0000d02400341c0b0040768620240360007190041c0004e0f00108140301001031414229040b4030000340c5a860303446108040c043c810850755041c40561241d090131000d8071400e02030540d10903001c020140b000f020440407807200050300742d008101c44050564050407151310300f5941c0c0c4401c0e00055601d0805600200c41940044e140c100940ac011090030105140c1c010342000b83c0e0059000d404591215024000766123004c04540b04030b0351114110705d030107901c2e2052082d081c103030b5034201160340703d40a1102e0b05490500000e1318149040600d20f8072204094807024207200400d00003103d000c2078846500035407559180c00f800c000741c0d80d0342c132000342d103107503244010941d0420703500c0d1a04a10000e64080304030701e54260101e601a480f5228010300d40440c2c0380c0132030301c00710714445c500302c201c0c1c042c2d0040d0152040b5041150300b00b2982118400f071019a400701d000d4500290030413400a001503029a101907000840e1804841002c04890940d001603032040c2d409a500380c1c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 739314883 1250 739313633 739313639
    0xc0310092901051201030609020409050d090f120b1f0b0c2d0309090a150906050a0603020319020307050d020a0c0b10051804020303070b010308130b0910260a06 70
    0x4901ca4152142828a42103140888801e0050342c6004103010003841d50b619a01c985e0295521600301614258108040d01c0c0c500d0b0381d824016000314014480c0103250200008005401c0070400c2c4841c5040b900800c000b011662075040100d150040e40c2086101e00404e00340101c0c03880c847d40003401401100000070070350100c009030401c2c113106840c09000c49045500a03240e00740c00c804415182e0b04501a110503006868262150010740000180d8015190382034000040806580d04001c045400030b0b6034508610f81c448908500764802245e0621030407103040d120406140ba10360046901a01c149031803820041d48242c1c0d40d042c0d0380f10742d17220030002e10304450000900c81070706c0d200f0b50040e5071402001c040510b4040800c09505120400002c1070481c000000c06544051044450340d41c3d002c09013294640c0c592820680c10f410003001c01a40325840400410210444021108400002070110740030408041c42102d0803020101900348007000d03076140c0e03100700d42c8a03404039002c0c4949010201c1d515003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 739316133 1250 739314883 739314941
    0x2d060e040c0815010312031a04020c160510052517030105090601020f0d050906070203010e07031205162a06230f03060603060d0b010e07260c031009 65
    0xd0110741c0c43d403818244001000020503800d28080d610076541800303d01c0400c00344c001c420100054004d16007040c000905808280004902011000682503100d5003483e02e82e000d00804001d9410b0502c040344081207005d00702283c910602c03001060810301c030141e4a00d2503807501d1303031200105400e603850038001c001403000c6e180c0f081015034043d00c284003c1282d98404c000e840e035189110084541803040000f00700d42c5948840c0111821140c01070005c3c0403a00c44041029921840b510098a60098a001340050070348141c080f901c0880310107106180600603a15082454014025000000c078480c00f94011200c0038032581360001d040030f4543c800d21400c08000c107581c4441c0000e0040100c1402c00140d1070041940f400d41e90081019a1840d4a0703a0b102c40104802c030b1451000604640485000003074550a4039480c90711603800c903680c403514080c40c1b1040c15845542d042161038205100c03000261000340034405503503c6102d0501c900c02d015900d14111080391144080c2c02c44c400301078595800100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 739317383 1250 739316133 739316143
    0x102090a080d020a03030c020102040801110a08060a0e01091802120604050d0521040807050f071d091510120c080714010c0f020f13140702012d060e040c08 68
    0x10140c03000d000030b9150820000d4540701303400801400d03d660382920365051031003581a50054000d0310001c000c03140b4010301e20000707900261101d4002a254500045950404602c004e04035591480100c40c00d90030101031002801544036400b494a40104c0e00303c015036184011030107000c001402501650070103040407070508081c0a64501405010040740101c103942580324100da507008183c9840030346036480c1000d10342c42228800b038403038030030030a1403405984040755080860340c40e6020f0010380d1800000300c506c140b40850b246509034102ca26202880d8051941301944407903146110a0f6590325070690100002d140760302500c84003211541401400003c11451002d01584064180c20001c0d001c00284000135810300100500c000700c4000045440700e4014030758050000744112009440c40f2101002404040704402080c036541c0e002c69013040c018031600c0301c4402c00d807991450101141d407418002e048249a580c030f031140e4560300000c030b80004c074003414003892040c65407003205880e01c541c281c608 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 739318633 1250 739317383 739317389
    0x90309060e011706120a140d030c09090209040e1605121b12011b03020304051005041e08040305010c0503251b06180813080c090a150b0c0102090a 64
    0xc0030300d18100300c1da42c1c0c1e0006500c03100e070158030402406070b6441c01c2c0420b074241346080c4502d0b43c0d4413800c1e02c81c104200f0724000f880d03c071141c90001c40790307041c6e602c42c0c045060341c0808100c0404078180d41d40074030042c142a0001d011000340600301195803d00001460714000200c480b00382160b035101001e2003136240c40c02000c42e801042c800186140210301891071040808040d043d40710300d042104100241c83c00b07400a07640c1c203500c0c0440388640d11074044058042d5004403400c60341801031480d84a81d4400d1b44c403400b8000ca82000d95500142940d41001030281001c803070079101d626040c440000000c0c004d010302040e40c101e0355a00c5849050642845d048100c0300c4a400b0b003035100e41582c412130707140e003c2c000b214400103000ca2400604058200080101a15a04516541e010341030750f03400c1c001484003c0010f05400b8603040c00c500d50f60485907072030f1040d1034a03540d84440101c000c41d46082c80758000303a455660309031102c40d00e290340b180d0315a80780d803025140441c1c59401040741c2c1d181e03103040d90b90f80001f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 739319883 1250 739318633 739318637
    0x307080d0b0d0c06111603050309060a181409160905090c0904051302090c0715020a03020415090302130e0601030633140901030809010c110d05010e0c1519140d09030906 74
    0x6810301f980d45098881c0500829170b80101004036124110a103c1d0201c00850807200300031000040c2c45228001128810181c954000c58069001c540c0040c400d0340c50700301102c426594099018180340801440c11805400c1d001d8416090119101c0c0307a4035881028041c0710b050740c00e120041c4075441800301319070009100c20213800090011601250480d40a141c004085510040e40c0b00040c800c298000e00450700021034110041e000001803e402070718060a8034000ca811040d00180305103c07009a5040b40a140040d800103001000028501d810113844480e1880e121500c03116820a101e4408601021404462800c0d0b00d04110001c0303c03245c8051114015550b0398190740c19134490500310b100d6803481e42c2c10410b64011400030704ca1210030180811000500d50301c006aa507041c041e0103025007030a111000d000b5039903404064a00454213188644070f03444214280f00c3c0f407203844070305000040c00f2141840f0700820402403c0700840700409607440d003508005040b07000b5003002041c00a958201e001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 739321133 1250 739319883 739319923
    0x507090b180306011401050d0b06040e09150c031b0c010204031e0c050105040b0a0c020409060e0c01080f01030203191104050c040306050624070f050d09060206090307080d0b0d0c0611 80
    0xc141e41e200d801c40780001e2301e10b8808503d1030305500c08201c0a11569000201c41c007540c500b4407400c0c00c0c000c54080038107200444081080d403681030040240d4813003a030300308941c0550824054000541d401c050494880e1a8000500b0107680381c0701c2103001d10796020712201c4e02d040f002508041001048000d00600305c00c1c649a0f0070241440100d404511030f02d64020144910801450308640d00c50308908480c40e41702b0030500c40380b1030441d00c00d5902c800c5c503c0d00314045076600d00041c2d0000101071343d85040300d80040090091810a10020103075140b40101079649000d04c20741001d56860394001c0a00030a0050301f80c80c5c2d50380c510f05001041301c802402803403103407101c81000f1a404200c454800b0842035005c1145540d15014075040c1c40a1610302002005400707616034441507507800550f40c41c2180c03569000c0d07402964500304d982da1603114880004205100901082a022030342e1703444442010000742203c120052143c4031140b8400d42c0b0761103080000d00515820034252018003041c824440a24410781e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 739322383 1250 739321133 739321169
    0x302120106030510050612161d040b0c0a0504030605040b040b070503071409031f060e090d0815120307050109150c1b0602130e060a0b0306130507090b18030601 70
    0x6444e80040d41c41800300039104c4022600075501c1c420038002d481c0021049800012038900c240c10001d04902c500c40000e94031101c06a082c01076911900d20890b80b104c512141640c07080c40b542d0036500001008002c105042c08080002480d0340300740b40c05035004481c241c0480c9801e240024281c3d10007040c50781000700a0080c045c0c1140c10060159014901026072900d40d92500e0110346071200707500d4002c0181840a083c03035001c040c03651000003540d40b02c44c0c0e42c902594604605695900445110100240500e00002c1c0355520010022015100007820342d0940414048602e240d500001d10a0b595a5941e5000390104200e00d040c0c04040f9202c0c240600c0055035a0b003001d4074940980400c20071401c8091012070410116504030b404e05403440200c010040d495000740715a103202242c000d03000340d46020340450800c3c11607050324455040100900090880d00da014009040090b203008180070503850301044951900740602007034070040c1c40e40c20743c941180040628252042c0d1210701204200c0c0c4000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 739323633 1250 739322383 739322393
    0x1c141c0516020d080601030f0c050d06080601061202092e031a0d020103110c032208190f2607021f1403092107031214011202032401030212010603 64
    0x403d9003001c00d82011010b80e614600140c0c00b0302400310310003103201c0c980300701c64004035049409010401c481e00b104205082d2107a1200755510000c2c0038500c00706220701c4104090400c00d40090005403c0600601c20a207001140c019608034200c441000c00d0402200b00040c4030340c14403822400796017005440603280300c50400b080e07170349860490107030406456001390025004643c0445154141074000c69035a03c2c640c00b034001a28040e146454810a40d1070b00c006080030b400101d00e440801c0c0700ea2a52081c050aa40d40040300450b076501300d504502d40070030a074070480c202801003030103202107595a94070900c92041086046000d1490b00350340548031600c103609070703001c0e0307803440130610900f4504c1d681c0d00d90320419490308081d441e50886141011002082141d402c82c040c2c90400c2c071036110b40702d000e00c00d81800030a807242c00000d501c603181080c0c01080b00c954a10300c41010390b40090280c1d02c3c0009441501070b800c0050b40c0e5225280900c0400400031424004003821511407080b0082040a08580d22 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 739324883 1250 739323633 739323643
    0x30705090705070305271302040b03070c11030709021c05090303160c05030a0f09080c0d151e06050109080609060106080c0d0507110d030e1c141c051602 67
    0x20781e038100180440c40038105801360b41100d02c22200c0c8403810841c3ca040e1094980c49256449a030743c0a045051499000840b81c0d00a48068400d1081c14904581c1c1e1114200c4540c08038007000d44529015171850155600c051140001800c00307410050382d1110703508030001080140841c10042a86841d0070081190760100a0702d03004440d095580080c02c0100b14119120b00096001030102d00000410540c440c2d0040740314518410a901c030102819903a4090684032041050b0f0301d5080140724114200080c0f5910280340c200c00c400d4000074201c4100341e0224244020401c1d50b03140710303540e10b0050010b581c004803500004c218200c000c001500d481c2c0b1540740c90b014184200d005000411021803d5890345000f5104140c0659800b040302e8034283c80010071200181c4559005805420444c400280c8a409502c020102c1400240203249a0b20002c0d031a06240d0003150003001a50410b4080c40c48040300141324080600c2e214034a1802050882c00440c3c002030440241800000d0402c0358180c1c000ca0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 739326133 1250 739324883 739324891
    0x1a12060604090c032916080a110d020a02070e130c090911060d0506041a0d08030a0612050d140301050d12020f03041211270a091e020f03070509 63
    0x700402c0b410340c24500307010710890342c0d08001e041000e40e1800150800c1d42084840c2e5101104900321069160903014020312441540c0340400100d80703030001910b103925a0000d074801d44110744241d107004942d0f00c80d08200c0e04034103280001a00810343c01c100405905464a8100500b41c0e411710300301d01c0b19992406040b11510500401503214001c001c03d12070140c2e100c048004002c1c01c0c050755984220410001800c04441c1c43c1d110318505203d0142c14a04444028010a005002d9440c000700303d4550319259007000f060002d003280c0b16000400c821206401c8a050039110b04002c11107000b6032030703020b04042c60149480202c1c15050004200a40d42c040307007250f01c2d9400500110104040140c100d081248110510300148000a230000d42c10f403034911064845030183c0c0c501d501d1803035481c00304480f01d0341c11000d10040d02c164032254418101440070650b0025a4440009690a080c1d90f42d4200c0c982003810b0100e20008085010041d41417540102800e00011030103084c1c680c1c10480050880c50000d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 739327383 1250 739326133 739326139
    0xa1b051608071e1a160605180d0813020d0807030f2307020f03030d14090c030c0d23010c030c1b0201080705091311070302120c0606090403120f1a120606 67
    0x803d822004e094220b5117004d1724400c1c041d03022030160070030101030f0005688000754072200542455500d00c000c1000b042c3d81c6920341c0c0d800c0c240c1c0c884120540c240c451410080e6802100000320070009400e50000380f04052003074450800189041402400c0d20b65101300d030802c558a2940000c280440a1088600d001d50407107130b045620b038024021034030314040e00c0301e9881001d180190500308144515101780c4580302c030500311045030071600c0c14191145084082d06030419540c0e204100002c01c1100400703000b81d1003000e00485c5482481d006030a4804003500c00010031350b10a1a100d5840e4807000b10b0b0350802040300941405400d079400240b8410000b05030310304001010400d901d080d0740314020400c02c4884510700b03002e80e4100301140a0161720042e01100907210741d508000b80501c0420540d44075240400c0a0021540c500c1e06002080100601c102c04003caa20443d854440d020303c608403c1624130200010f40507001807003800024842001184a00c0f041d9584660303c100000307110b60700103415 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 739328633 1250 739327383 739327409
    0x1a040308070809030a03021b010302071109070e0d0f0308060109060c260f09090f0408041403100c020604050610080c041a040c1809050c0a1b051608071e 67
    0xa41442d0a29001d0941c000d0342c140030b42d850880c00d01d82e000400c800f8480c01400c8148092114800640883c420301000a01442400d5203024052500d01d020a500405a0802d20381c6144040d0008611158000040b1031841701e120051061661001c4015404002801c00d909034a06214014043c07a040310401481d400c03440d540000c14445085000c1e124003003103071446440f10400d540d80b0041d508264003e50142c500c0400094107504809251743c0a66000010035203007900b45044640da409042c40102e8252180d000392040c2e800b030a108299500d07140354040e00460403d03150480c200074010309507022800c80d4120900c0080000b0540004402046070001110a58004c4c51032030700c044510308641c007501e014002007003960000f080c00d00045001220103185521080c14200b1a00191010740443c1d80500c5002c81003405606280482240b5035040181c6061941c3d5880c1b8000c0001030115001c0310600381000699000c11411019084000042e1030070840d04118680740e818070b105c0e0740765000701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 739329883 1250 739328633 739328647
    0xc05070b090717030c060a050c090127030b04031b150b0d060204060203031603060b04060c06290f0d0b070807170109150b2b0b0301051509011a040308 66
    0x200030301c4005010006035070350200f0100700f4403034590300300790303022200c5001c1d00e400580c8000d141c0c4035240c0705880d12100d2038288040c02004446a445030100c0c0f034150519041190007508802000100440c450a081e0a00b40b805280003421102010403001141c041c000d90000081c0b640725604100089040001424200c2c210008001c09480d0601501c450f200090104105501100440c454a40b03030140c80d00d01714500504804031a8640f20304505400240400d00a442c45821240c0c1c50760b003c0c0e50082142c10a0010124110304906860f0320182980c4e4000c61480c140603500c01441c180c00c955616182c411034865110b5424018080404c10422400040c00a80204c46880b541d120004624006617181d154000080442144104032110010800201c4040349400c440c1c040400002e0b401c1564181c41d95070700002411040b81a6040d01d5449001035610709100d414428181900d290002e01e203008140404c1e0401a00901c040ea088115100ca25003554411202180d0b4012a51035646035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 739331133 1250 739329883 739329901
    0xb06071a090a06050a06030302010c1e0e060903100507031d070306020729010519061b060204090c020c040b0906030a120c02040606020f07080102040f0b0903030c01110d0c030c05070b 80
    0x2ca400001000c0c180340c4014009000e000794409001c0e030340300390000c20854070054429511441d40c44440c130601d504003035010700c2403841a0035a002401010384814200310100d070020f0704111043c0340441400d640c44c020003110380d9140c0910009615020040c00000b44070100310303038a42840d404040c040c140c0008140c420050810249104004200d58103110410030702d0400c5098807007032040b10f2089031111145000841074640760000c40c0c240b9180d0709101540340003020b01c503402800e01901c6040e400d100014034001a406000780d42180c0394040c0820881c0841000b08a94844641d41c0c06000194100800f980300015646000303508a40300440d06a4244002c89113a01c0ea810001c0d0040c1c00c00c1c10002d4002c4c1c0000d42100385510402c02d480909440c0c042d514201d000758443d5000e403030303603d03941085900280c030000c01081c0b402400790b80c5032103100e006050a6508030756007e04d040900140201c1601202c0c03080a0303c1d401c140c60240300c1d0120840000b81240500398001d0002d91071131006c190048 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 739332383 1250 739331133 739331143
    0x91401090e0717100204080d0e0105090127170c12070e0f15180610020c1036150206090606120109060f0213240f14070f0201030b06071a09 61
    0x951001065503100d480d80c7c034061b260010f0042180108400c0000c0c08080d60280055038104101070b5104c4029240008a40342c800b03500301601c211300c8101075400b1880060103188a0322424440000707192044070f060510030b110300600f2400032103400540c024001984a10351058012184075540040350b102d030020410009a405031a03948000003c0013240030700b0350482c000f44105801c0366003450000e214002031742caa8440307044c0541c0c0070104461400120b801000c00300047d009100c2c0c0500d041c000030110001808668a40301c0100d407404d2820071003003d80340034514441d242171001d0032141c2003466001c1d580382c1c8007401062154200a00340c48075014258000030030741e40c001005105160744c0c003028800a6000c10803031001c120514202040481241c0e0b07081b00010f2180c0300c3c440e140904290215805084084540108002c685000324051b014034013074201e55010b0a0145071001080c070015003217400c3d00f0b82a81c042d240c10f00c500b40106040501c003a048041405550601d40c3d01c00c8a554105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 739333633 1250 739332383 739332403
    0x60708180a0918062304020108181006050306090a0515060f090a0b040b0d03050d050604020c0615010207060305190e010f090303051b090d150b0901091401090e0717 72
    0xc0e00c0c20310164510f4111041991925010380e03000c205501c45070043c2041c14030021696951004414085401940f10381c043e964001015030398110380d440000102c03824820015001c1c0100c503241c8000780000c0c6401d00084e43c00408140042206250729682c094a03070000300340b820250320f5041c000501b0b980f40da05001c1c003808001010a81c8a00d41a40c540c001442c4100841e8016407a0a0307a818050801116003041c140e010380303c0c0c50901e107000c0c500f14080c0500401e102e405ca43c09000c0d094042c40f080000e140181440207512044008101c002450403649900410416041105200148a01c0303a60091514110f650200718280d40d20006409003003001c00b24581d0515000c90507041c075925603c01d80c0125480d22088100c071329003200c80764050050481d4160b0000c411075203100000c0000300d03200143c04041201051407c0341000041040d01c0c240e00941c0e1050700e94032000c4072803481490503409801c000070304003e46000f5811056549285002d84c458034504038100811a9004201002c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 739334883 1250 739333633 739333649
    0x1401020601030605091f0f0b40020a0c060b061317070e070e041d071e03020a0603020904050601020610050607060f0f0e0706050304032f060403021b060708180a 70
    0xc00a0400c60701c0010704401e104680c015251240c1091180b401160300003108412000301201c9d581d000901d410240d48001a28040c102c003220104024a0240080d141c90032440d2103410303441d045030038030006440074040724034814002048854100001e98905005481800203440181d042110342d8902c0d1941c15007000d0444c80d000001c116816600008080f281d440035079040c05a10314051081000204184410030150420b034001d0000040401048400c0601c0e90554451540c1e2078010038441342d21904010006600000c10710752a0130039000c2d19421910a10007070000e86400301d00840c0c0071010703001d80c074030800c000160340d81800a190031000d2070400c02403080082150b10440300004168008058003280200d00c00050110700903402e40348165010740301c5e4400100c4000018440680c4402d485260601440d038803890000308000c1c041c4030324404d40080c10305400030100650882c0880c2d0307500d88660300c200300755030000300f150040e1044c602a804200a20a6080000600c401180d40180c41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 739336133 1250 739334883 739334923
    0xf090f02091e03120c120a020a0b010602010504060b0306060102100b0a0e010e01030501060e010b0910030612030810170c1311070c030b060a06051602060d020d05090106140102060103060509 83
    0x80c0346942202d00355034036044040b07071120854024490800c0c0240201e41007190815440f0b104200c1010004110301101c0c0d105480200d41039a40d40200f2280a8101c1c00040c0c1d903c1040008007c0036204454040ba001c4006010783e2a01c9c0000030358841100c030303010032559250300c00480784d51200f410313a1000e002e00e400c0d0500e20750f031200c810b805400c000f4402a5003170740c01d18a0004080b40400e6403241a01c03413640d9801d15028a007818414400c136041000802c040d911600010010008081180046c1c0320342c2d2440705500f80b03080d01c0321002d00300740c0150500e0495401c51a039560f800040100000c4001d0340c00d181209401104034005010b60300704404000c00018020040224455842040e00d00c2001d4215882c1c40f61024000c5603070140c054400072501c20025940d11111180307129403100e2000344403c1ca00400b0a80410036a000340d80c0340350a09890b0410300000712030a014407006000481e800440300e4542e000004d41ea40018880504401d81d502c2c00f1a00f1804107000d03444040c4148840d0070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 739337383 1250 739336133 739336159
    0xd111005030628030b040321021c0c1706030304030203150412080708040b040c05100c110f061b0109081602010806181b0c070305030909100f090f0209 66
    0x40c0c02607104990b003500c00c2a5120488074884030f44075610700d0844201502218050442e940d403514220b02400035002d100c20001e040c80d00f820240912074000800000250300d411811040542c9503554205110b40941054580c1d024658096100440100c2c5a801140544c079540d020a00750b120b1600080d40500480700e042048111408180b4015407240c1460420050014030448480c001603031040f0008103d00701090110306d80411454215000d03052024105550340d0004558040c0c2d1501c51020851404215042c45100041d40310f030700f04151b56450005105a00150300c130320540a142c10300030503c0e401c05202c01400d51051051940c00a2290f549880c0c0460010b03400c0c0c4c0f055001c90005010200141d2681801984614491082800300301907451303030703100564414000c03001100758101c10312000078013400400c1050007c501039000b4564850612052002c0d0705402032003c02411a4040c1c00c002c85d01d0740060f45800c440800c0000214200800d803042c02034400d4507402c5074030882031101c2c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 739338633 1250 739337383 739337387
    0x10c0206030a051009020c060a050a0f05040b06040c1112070c151e050a120203090a0c030c0e07050a1e1704140618070911040b0a05030708010506180d1110 68
    0x10f1405440921094902259920050000d0b4070500355a100b060b000540402e030b4105198122a401c00d103245d00120700f0342e01d14407641c41166421207040d0784207011042400400d0915215003140c204903032402c8560103a00201040d0784005003400c5e03000d002c50000c0c000b014885804c1c0448040c1000e140c0d0850000c96005c0010400341854052021407803403280340380364641c011403c0395054801500e485120000301200b40c0000d42004283d07010714050180e075030001910b0603942d8405180724034518003005060410f4280401401421310f0180041000080030b540d4102003000c0c000e04c00c3c9091507404503201c000c202c45909198650105000704402480108501e0f101c0846035603c0300c800710780c078030344c1c600862144403000e01c0c45181044e0464641030222384079039000a10038411041425107030603510407503051182d000040810020390044144512141e1188500d0b00504003102c1c0d183c2050030042d503034680050b44120052260950845c500304200060b154400c41d510010840c2c2c41c1c0c50040c1c200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 739339883 1250 739338633 739338641
    0xa0e0702121308070f050f0409020f0a0b0c0715020703082128050705070816050d27180c02010902060a0909110304050604170906130510020708030315010c0206030a 72
    0x42e1000f80d0150310070200d90740c00d20310655012203000070002010181e424003030000400e9828801d0b60845088002c0010f2a1100c0040f00e009141814980740e4554010040d142010403c4d08810810123200864000c3c01354005900070590341c002c03c4042e5103004440d008a1000d58600034480c140f05d040c81000b4290400d040444600c40080084810b880304441c1414100c50048440601040c4140315100128100d90090700894030404d685149003d0b660b1122407825500c180d8000003d0100c103074803181c030101080b488030b9051101c4503002c0c0850500c0200d100c968800f209150040b0740e07072107441c0d19007031007508240349490700a040c040c1c0da10000c202c002c20045250251034407507420007142c840190281c4045902c50390b0858003400d229119651440501e42c1d410a02121070303002846408820f6403142c0003400c1817443c03c00b60524080c41c00c2c09000404848500c000c0954201110410181c50301004a84d8441180000100f00b0103000380143d502e442c01d10300c040d400075070100070019800480d070300c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 739341133 1250 739339883 739339889
    0xa18080703031a010206150f151312030f05090d0c06050c070501020f0a060b0d1709040b0108090c04230103110909030c070504360308070207050a0e07021213 69
    0x2070280f00f0a520045400c440e43e84038080c49005a11400000b040c4081c07056443c0c0460b60000d09074001566030034001000c08095041030b41240c6000a030000c00c0b4241000b1b208020036841c07a1907450b04107540c401801a41c5021100428071100150314800d0b0382d100907200442c00e52107500c103070b035842d120280100340e600645c100a4940c401d071180420550b000013048459840304100905242c1401c0d980c560141c40c0070300c0240d8105003100d118600044075400e49100c041d46a040103a01c4008503810003054900303049105040c050705805020003407801107103840b540041a500070a4101c03451940034181c0c1c144803840804004410004010882343c41600c1c001c03d00d0032a16040151521017115803a8460041000c9075940309500c02c01582c14a50041400200e24201c00300015000498201030220859040c610041024180d2010150445082e54000481d48000c0c0b08250400c008140708164500610104c0310b1940001500c5520030000c0c04898003054040c280c45050220700194201d403640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 739342383 1250 739341133 739341137
    0x30906040311011a12010b060408030a02100207032007180615020c0607031b02040e0d02060c030c070611190804030206010801023619061e170a18080703 67
    0x5a4010380340c2d03014041d140210a040140c0c008844103941040018824461411015503c56926031541d685081c0074000910707a2101079560b502c41594001d0030500c04c0194030030407520602401e0701095024090440920000f003a50f096011a10005460030203268082c00058102c2001d4490b2448580c010808131441580f12030510700130380c542a41c8035220f00e0001d9421050503c1140c01081c42003915004920443e0b496104003503003134011809503000c420700300002e0385c030250499a03070a904004469002480511450a50821000c1410607104152015025603140c030071500c0c0d6210301c6800c079046004513440021000742401005004104119019400f6006100000078011818002c440040c240d162030f00c2400d61601d00420002c1074101c18580900320f070940542400e495021865080505800c1180c1d061860810000d0141c04c0c500080c5207500d4500030755500702504551a808541803c10002003580e82d01180306000700050350030150500c40d0380c0000c8007417124860051290710f02035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 739343633 1250 739342383 739342397
    0x150a15050a060f0c1703040303021210140f18010906210c0e04030e030a1b05030a02060403060915021303150c0e060c121801020106050d080a0c0c0b0309060403 70
    0x128204a00051a403003110301040b407001e40c5005444c031030444088803030300c282001030802c040258903003003d030021142100425030000d20303d0f56002c9501c200070360221609a0740020325003040c1010908031108403506000e00347c1c0b950940003d5981e200fa1084603506203049910b190f03540c00410000d00000c4c03040c12940e408200b0324000d08607903003240c0c020080c0c005190307603030f010f192055410300110001c000390200503403524401920b40d4140b000c0c1c00c5003070041a05540c01580e215041d00310740441c3d0301491095028030303103c00060701e5a0081d102100c6d0041030024150303509081c030107018205c0488a4007411320020b0a100c07850342d01c0b14820148d82c0502e1741d41c513030110320744111001c460b9034234402c03004200e01d40c007440614a4a10010010a890a401d4441140c050701003900c084d01305441038105407885801100c1c255034244074134001000100c803004011606512460002d01c40c40782020100702c003540307102e814803048121800c0180081c40100d03507a1b1810818071901c4030400e81e0b080b1700146d05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 739344883 1250 739343633 739343639
    0x806010504030f0215040e0a050709050604030b0a02030a0207080a020d1b0f170f0a030b13020a270f0e0403080c04081221010e091c08040212150a15 65
    0xc5001036074240d0b41c2c0301c0700e0380340341540e075408201c800c0b503180c543d00301d48100c10000880c4a290351400c0e50300540725840d0202e03a0303041242000e0140f042603000b10707004d600184010004101c02d1144c503500078268180050707480e00c2d01c3d600000070b441000c2024005020000311640c0a917800544440380305e0702a84c0308140e900f440d4030b080a107942610405440d0300b2031848000c01184100307079071644091646865500e003402600c50070000d500003102503808642d482c0b040704401c1c10200140b0b902009002c00844c50040b040e140617100031104403000c4140319034010560200b03050000d07164050200f0955003d6a80d50f1001c154481100c1103500720300156401c0080b480a0900000342c405960b14503018050010585c01600e4250308501c5200880e4044421114200311145020700c1c040c2112a212681601e08141882e04d0000c0050080074201c0100203440c5074140d00000290300258100e800a066400440210f8a0078103810703e00301c6444a480e09100004256030300c100d40c01b084090341c3c952034540e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 739346133 1250 739344883 739344887
    0x7080601060e0a150509010c0204050c0904141012030203090a0b04180605060a12020f0a08220b0705030c13062f0601031103070e0405011a0d170f0d1b080601 69
    0xf100d100d5801d100444c00e00b803800300c5000744094025441d0624200740c81c1c2e40c5580019060314025140b640d4024030020f181c2003542018017402402c035001c00b034206030b1070504104000c001c0c4110710a018601d890140c1840405100f40b003201c100400c01400100c0c240c0d1105d102603021b901a00c54480503d940300c4001c809040107005a4040b900010032050501c414400d0503901e64500800303509240794201311003840e01e031050000c3c0100c40240c0ea505019840d2500c0d0102420001828000c40081180c452400241c03403c8481ca41c4420945011512501c3d181c5181400c0e0140484a0b00704210801000c241194402690710782c00420588810202131400383c2403608400e102c2050700147c105000600110312495040c000c6030002a04481c07166a80340b4000d078001c501a90100e909035155044070303e900700c038042480400c210440d18000400e086035103410203da0b58121284401c0008035541180b02025800d54602c003400c80303001e0000e02043c180907400201150703480d80100301d1480108881f54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 739347383 1250 739346133 739346149
    0x3040e0105011e030f090602130302031e0307060218120f071211040207020111070602030324060304020d021c05060f010e0105011b0204230a06060305091513020307080601060e 77
    0x6608111190303a0206480307004c034094280c48815001950300d41c0e000e480000e1aa2004120180040c0e0202c1d04650641c410981490104000c5448640c0c84130305101103404003108655400b0351283d00166100344488000190b110400c5025900403d241a8101503c4012614034403a042d00d10035120100d8032140c411000810321a03001c1c008180b1940301c4a100d04095000b440c406005042c000d40e84501002e90b5440c04030f55811240041c1c2022081c012008400c2c0200c640e1001003403158441020380102040c40c0f8040144068424030f50014403100350b450360541e142500b40c100b0a0f48401c54254140203542d445c099840c082d191114000000380d40c48201e40d00b6051301c0059607030141e100c90100b6829035206440800340d038055a00c001010345203041840324919160071141c0d90907185060303065081200c2455124074189818103040180c22280840d409440424800b003d90072500c403001d10840003404001c00039018482c0c0d6001045100000442604030380c1e0a07030700c50121401c140140803c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 739348633 1250 739347383 739347407
    0x301080a0c0b0a122f0408060c16061a0301020f120f0106020613240501090e010923010b03031614120306010518040501090f0b010302040320030a0803040503040e010501 74
    0x3d0b148800048004d802a081442050f441c04503000c6040742d00354168203405503020220000ba64002003c00040000b884000d9000e40c081808a0501d1902800365943c01f00101004025a9540d038064420b1002068404580b030300207802151540021206803546904c401c034444540300c140c0c00007901150b10203404a051f610f55034081d0a20362a007079032001502c2603c03041102c1001c0700160501a000300c00c80d002802c0c2d0f505400105140d450410340030f08030790303000b00112051390410201c00007144c00394007840c1c9070b00c4948000683d071504c0801c901c1c1c0117101d406280c542c503010004909140303100a138818a050b601500340c03030001d50000705501d0741c2c0300c3c504032250102c40720500c0003892641c01032000d84540340c1ca0030031a6188180c0c4600203000c64009130400154a0703a99051591000568820148698400e003821407809045482d030450309900c008180410350612050220a52814002c0e0340f00c070340e03202c48190b444e41828540103446c1e8200c0d01400300521040c500000e020742c0f0038942e007580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 739349883 1250 739348633 739348637
    0xa050405100e130501020315010e030d02060c0a090f031505061e0402280c03030e01060b030402041a030303040b0406180809010c0c0f06030e010f0b010f05030405070b0301080a0c0b0a 80
    0x10181c58408440082ea800a14036564001c00d480100d001c204280000e502c01c040100500d020300981400142c100103c000482c2d0090744104404c40d1455000140b050300304080f4403240740c8822141c0c9046803000043e4000340c0b6a41c1c400b00000080058003103175440c07111075080e8248401d6407024280940302070b40c00003640303142e4600b904020702400d0035030081c854403071020072074044940442250142d000da28808000040c41000442d42416403500c5035840750394045000344074141c68240e4000280c04003401c081c1c49681d440c0216012406c000100d20b245481c0982901d8a914285c20413007003410302180d040e1000c1e41825142c01e01c5100d4211051003a907400500e0f1410001040011241c10898032070888030098190000b0580185401d045001050143d40100300403111151880c2980c2081d5410700390030b0704003102c00902e40e0304070f10b40f03600c08112840c5c196125076881c206203140c0301081d4482101c0302000000401c2e103117008143c80c0c041a00400c07017041a40d64a00750320006218000e40880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 739351133 1250 739349883 739349911
    0x3031e0207035c1b061c140907140603010b03090c040f02070c09150b07050106090507171509060d03091a12010e0717060613140a050405 60
    0x14048400001203c195805180d10b44802c1d050091100380d154007140c403030f11145001990b20700d03204201c0d4010880b44180c8028058042580c02c1213400d0181c060f055500c00e80703001c5954240ba82186141150414042d60184449081e50524070b00b100400d0351400d15500906c040410140d071940556480c1c400003070829841e42e8a80f012002c1d4940026224070a80d0141c6c15001401c0d54031405400030303408140f07800595403000c0d440c2c95644070640f640111a400d0070322901034034480300c0c0705d0b07084225001140c03081c0d036546661a100c0d0052110740c03c4981d44907d41000d0102055005607500070a9200307078051050381e183c1e80041108441000e811030740c4040484000362260509035807260f00c0034442d007000c207090380e02c0b24a121030b02c4180d0001c0b840b01080108005a00100782096203004000d0880546642d0400c2180144144400d540072100034010388041034442c1c0745c0c0000c81342e042c0840b10807640754a4039441c8500c149528265050701c1b502c1f80490100c4c1c1c501c1e01d841f8481c02055100f081032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 739352383 1250 739351133 739351157
    0x30902030d020f1b01030b090108010c1d03030702121c1e110a02010f032003040218070c0f031b030201050703060801111207030914010e070b19080603071203031e020703 74
    0x404284a10440b85c101607d5440c507189a89503810001d000c1e15501e000410323240105000103140c8041c0600e00c141a20510301840c1c15a1404070031141019010703941c8600700440000c03014908000607400792110180c40a541c16503540c05401442030000383c0940785c0c01c078241e02d08225403001e11141500d01c03541110242000540c040d5109040701c2d13403682008a0f007051601005003102025107606c408500c070000402c4114680004a188a5002d04900328031509200c1c03c0100030b6460007600070f2103406480302c903400b498007403014140c00b401880d503140700000c143c4c9002030107484195404408641050b1002c00c0949060040200882c0c85072405d5040124140c0c403c113a5480180407502815602d01e03504022403080460520390240b00000801e2400000b00d43d0b501e070250a50010360092000c0c0607441c5080d16201c244d2508151034070300080c0540b036038000a4182041c6030700110021511048d801c0401d0340540151440c1c07510303c0980701841d207110411070181e100d9040014002800503180c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 739353633 1250 739352383 739352413
    0x1b031b0201121109280612090f0f14010b0310020f0c03030103050703110a030b011403280302190309030b250c0b132003010219030902030d020f 63
    0x4196140c01454515241c5400c10014000c4076a1000580300e002800150100d40c1d080030003000620441c034580f032400307400c05a49482d41d400a14015a4200300080c3d1202ca60013005401c1503003074607081080f460440a862401e180d01104020742140c01220701c4480c242050418480c00900d02c8000d0040c0020046000d03c500080d40400d00400e4103010500c0018810003040000d580654800c0e001041014150301340708050b80c034560b801030703c504014042800000c1000d41120b04507150b40900d0f5000e0f04030000040d051007030500100c1c1e0f64110b0080912040e034042c400ca0102c450081d006d441c0458032001e112004e4500e02c01024001c2948072004200040380c1511040d03001d89010b1148034020000a1b40540803810f0705551030015946c014030f041448450701c117054200c11741c641d07103801d07040641d60342c41020a83c3c038550301c8034035224860301c2e14191400e404840c0b050000d081220030b50187c25601070004c0801d41d4050740203118550180b0812800003c100c0d103020311000051074006400040c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 739354883 1250 739353633 739353677
    0x308060a2d08010c0804140606031207020f0415050f040207020f101b050a0b2a0f0405060d1a0904030e21060f06011404030b0f100e07030c1b03 63
    0xd40095800e40807400580030100380b080034920040c079030711040c580c24142001c04949104c076200c802c0030742042090042c40c1d680000c0f8103000c01c00403842c40c1c0e01c40c5064000031ba2100c0030888403580050504540461065052803c40140d031011a10b240c030419161051204a0003010b000940200340320080700c0c5280f42401122501c0c1800d0b00d880c00a0b25030034040d104c4941c14101d0116219800502c8080810132400742055001d44940800c80307020015000c0c40101183c010381c1c041c2004d20024000030340c140a002240c000d0302014264990b5089030b0f090803401800050381c80307222400548030200300c0d45041c42c2014041c3d0f030903940c0c2c0c40764075600d0800c202c8078030a84050002004810061000c40c10703828020580b146845081d1210140f800d50005006105150091400c00720100f1050000034026103001d0707003000003c0c10030403117587e6551322407802091a40101980d140d00c1820088800c1d4503800c240075030000e03640d5444c1081c01000794040164102000100030910b54003c07a40b440004181e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 739356133 1250 739354883 739354949
    0x140a05190f02030d0c02090a050c031803040b043b0c0c1c03050702010c0504060512090f0102280e1e010c150603030806101403040503040306180308060a 67
    0x2840e0055502560020b803802010701c041300042a019080c1d5029440c1104405070300491a94080c406440c1c40002e000030303444000c004140281c80d81d0000380071a1802c000f0b40d0041d040800700c803039440da12201360000c5490021000652001c10307045c401000b584481c0315004254501c110440a91107100701141c0035006030040d035074288204020401d05080d001407504d160032603a00c0004550500040003829070342d07540e43c0f032018820204010440e8a030302204594840c2c1350a417403510142c6031050380c1c1c1d041c04040b0508c03103403540c000b150421008104001c259502002d03140f65203e032500842c0d0503283c0340d05001e100750b84400384410840440014400180c6800d03014075004050206a03564090280e080c01e9031040c1031a541c68051080581024026405c110206c4070004a00c040040043c0300f50420081c0d040c0301c02002c8040780c1006820002d84001d180d000c1c90a100460002e264200f221202c2d01080c2c1c0020031301004900c507400c000106500743d038101401e01d94803100d40d08102c091149014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 739357383 1250 739356133 739356143
    0x3090607060e01090b0a2d0209010309020a03063e0c030d1a010201060608040809010f0c0c030503030601090909020a050411090405011203020609070e070c03031407020703140a0519 79
    0x1a24101c0b85420030b109400b482880b42007040582e0520b440c880040711101c480c000741e0031500000e601400c01e0501e10b080601e03a540100980d030340c14201d004034050658104000e400014001d008130405c0140e0308101c1c441c0000700c0d000c0420b4a00e200c150343d07803401c0c601c2d090030301c591812800030340d040401c1d0000d18684111408903443c204e142e0300030320101c0e10305054103080300c8280c11500900d503a0a0007510024902c5140030609400c080d16900450320030440c5190610034980920000c0600030003600ea0311581244034880c81c50342e242442c0313440e070f40704031901030014030503481c08102e41c01c0301c0c828840603039000f42c110a040c40c01c0c1414070006081d2070300104080107040c020022181d03114006c4a019016080c4000039076003080c50041d00d4030038054601c2800e034001c1d240a002c181c5c098002240c1c0215189007602c001812410190000d00c5100c0c15417840d00c20340c4003000300c00b540005810341100d1080d09a18030301c030501e02100c0c0e00ca0a0f68000101076403c80807070304540044a59480314440c0c012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 739358633 1250 739357383 739357391
    0xe2b0816031d010e010b010c08090405090a230c060309061819140601051c08030a150e091c09120809061c050105190909061409030c070b0c0309060706 66
    0x2444803a2040d0b00b29009694641e03440c1c448400c2c5201d0300380201140d801081c20140000d03640e03692140361500522803114055699800000d0441004010340c2045607009004410b0740c060010325010001c031002008604e82c17040c949191103c0c10000c04a0717100da00b00c800a8a29501d81c2d064105064120007600c075260b200c2c0011640340360301100139844409108244030307a5111110741c4135500348a01680310a1184140a446e0f90001200042d601c4c40554000f40c5280d0380c1c0e0321004c0301001042041c2e1b100c00c181e8041c03400480d120102541007030083c4200d008407040c041c1203800d042e29000580c00d48900007041e4010070000c1c05000b0495091140c81a0420381c01c000040004c11980d4100055181841081e402c46100140c550310074640582015144804000c60f442444a0038007090310407070036644d07562410201401543c0e44815060100c541000455060000e6803a80c4d07600001001003003405020070009081c2425022a8030a020100245003468461310030844240c0003e10161001515 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 739359883 1250 739358633 739358651
    0xf01020f030318010506120a0f0615030f213509150c07021f051204060b12061b0306010203040864060e2b081603 50
    0x41070000d140701e07403060742502c0188044005190b00359040546014062130305e071354810030b5a91000c00c41e554515009a0316481c1e00e442840d01100421502200180c0100b0450010041210126003400881c0c001c4a004c420086011043c0b0844a03c8074808000b00d0b1000c8800b66420100e80501502802e250001031901070b803055150510403c22541412150405074050000f901c1d040003480d00001102ea10600b44241907011440c080030b00c2c14a40080324094040701009403152007103440600c071035140824981410301d0410041c00c04840100d01ca1241c0046030343d00c20308009600762084000080510001c07208000d00d45150f480640300604500040101107000942040600440002103000d10b8411140c0740f260f402c907800d102e0000c2c2c1c00d19214a00711020040c0a101c4808510340204034250814551030780340c01d800d01140e03004180701d05000f01c80607800340100707540d008401200c4081c00307040c28400e80f60145208400704030000c10402d00110301c903100c0c01001c1c1c1e840300b00581030004070088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 739361133 1250 739359883 739359913
    0x3010b04090506010806010f060206071805030d11010b0103021602060f0c0607020703050d0507031709030c0d0e040605090601051209010b0409050a171903020d020f040608100605070206090f0102 85
    0x3600c1c200a0782c0d103912820040041050170462036005005001640180c1170070450b0094443c00058010410461340003140905c20031141c04d800c0c000c020090441c2d0003004440d8018000c0708241030380401e2940380c843d00c0510341d4024021282e42c061b29511114240041d40c0c03c100445d0062a2071501e0404107201c403c40041c030804c410b074042e62181d0020b00e0214618509030380b500306407609050420800707010711030000e500918a010881d0407425100000d54418400c00e256010321407090880c0e105445400840710b800a10304c444004040da01841080e444c1c0041c480c02d941e040d06c0035030001c2c808108800c0042200c0c030600b900880c0040001c5036070100c01d800102a540002400d0341c4503000f699841082200c00983c01a01030708a124039810001c0208a01210018a1141106043c0c0014a29402103490fa0455004281c00341c1c180f40c0b00c0c0d40300d40009009080072182c0401c00540d80381b01003030607400707030b400d48090f55801004246000510701c180702094001c3c0d4401410741c403408c1210041c2403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 739362383 1250 739361133 739361141
    0xf060509060f01120b060d110303040f05030c060a0c020d03050415050306030c100815030a14070612060513111e19030b030703080a09080303071e18031103010b04 71
    0x40c00d85004008505003031494506151040c0c0c440c114603010f6805070000030344070181c22940510102d0f0340003d00c0100d800c1c040c000d40042c0c4001c9501d400006030201c2d52403041309802003074840a0b0200c0d80d948010354207110709446440800c1000c40d401240315030040c03400d425844a03c912078a402c03414159a080002c8100c0180c40158000c1140442081400e08042140402445c0c08036000c80442d802144043c1c61804090000c4640c0c480084400040c1d0f203040016524082d40300414000a00950b410a51516410300450780060000c104883c040c40c0706014003425208000c02a0701949000780e00800282484040c3c00d2800ca0184112490b20b100b10791254503244035036080540c0e9581c4606280304070138110400905041c50f10b00d40404503100029200306480d44001c5041e5103442c2c15030180d803120107542c41200d091100004020301540c0c0710304c80d201c0a041c0f503a0003014003a840c1000740e6040d160080929008800c040303040022580e4424400b0074000041d000003000719003180483c00355 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 739363633 1250 739362383 739362391
    0x60c0901120f140a091101080711060f042a0b0a031d1b0411070b06040204150f090b2803022a100209010210050901060522050115090b03040f0605 64
    0x1e6440908042c0c8960104400d944070003030400c05c200b10000d43c2c0e00d185080e034551949504201c598000650441c3c01850303218440541d19003191490b1034181d826034010f00d02140d045031300c120700114150700b0211140401e2400000c2c406a4058942000742140c00d07a00038240083c03c1544030101003803080200100f050304041c10002134081c0c4200d29400c64200c41d03847c000e4500407441d1414882d017012458066030120742d40071301c4502943e201c1c0c4e400a000b0340079135040100601c0550f0702c99081d0136040490300c83c205502d80c6414004030f5407a1144035181c0a440302500c000c05209540d600b5850410040c041d00c40c01d0390400506100c2c01c07440d17810325036040b041051062240c0c9070380820401c1d010011810f071005e0b00a402c3d4900f030307000c0000070744a94112032000c1440740ca6001160003040f0a41080c005400301528010b6071101003507242c0c5113010780c10510030169150000214180c4202c042a041d500d4044c0c54504c145c9280c4840100707290b000900968011340d40d0315035240012114040c19000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 739364883 1250 739363633 739363661
    0x30b0a05040f02030f0c130504090c050402031e10060c0206030907081009060b030106050a05131103072708060601141b0304060f09051c030e04050903030a0b0a08060c090112 76
    0x13030385004812000741540141c40c1e2081c0500a1204d035001114215600741510301c01e0b9004500c0103420710341420210825001180d000740040100304404c188502d8141d0444102080c41d801600c900002c01c0500d245400307108002982d01030200c01500303141c401190070101a41c12192800e956012503030800c1c10f0b95040c044103944a036000020300400f0f0041c1c51241e20210004c0201038030300400200801c4481c415503000388500d06d084c00409050fa444142c020b02180c0c01103070b50303140103c00240158420f04a04000140c64410303031103540b0701c803209402500c404100070b180540fa412f00640302d8408800d40302c600d6100800643d01151043c4020f4128825800011600d803402c00b1009061803846482060421000441c02c012580c0c0d400840704042c800c0c214141121041400d0072610318150140441d002070a2600744039100301d002005600c0b032500d010080103040c034000c080055181440c41900b816500c0702d404140c641c1d210740018460003030141450030300415410222000c0d1080e030200051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 739366133 1250 739364883 739364887
    0x711120a0b060f0303210601020a0c0f0504050c0310090b03030c070b03040b160504141206040b0105090a0b030c06030a1d030a090b0f1c15030c03150902010f030b0a05040f02 76
    0x80d103400e1010050f070900008074091828403d0004070915018100f0035404100340144c408103460fa4024018030f020035070002500ca040c15103074800859412050710035140220b00d02302c0040d070484124170942c0c0c014203195102d0b168462030b0600d0600034049140c01d540e818001040502442c201c100161002032074031184440d1030349001d05110324800740c0100506410705107036440040d891703405412101030341d000381c0210102c2c060800202d9043d40380b030328030712100d48501000e02c07082c04503944440c1d040300c0b0f0444150344940d50351502e40c0127407a200c4030350b15007540c44800c05822034035049014690064040c8400200d012040303407400200e07201c4e54a945159080060400f5090382e12940c240090014601c1551810b10550b60341d10321031090b5411141806620344862109444036000402c440c05100324640c01240c0728140144e07946020f20048882c0035848405030b0040400e801407840c2240c051311041225107080600b80e01620701c0f4400b407680170030600c402040c80d40d203500c00c41410031002c400040e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 739367383 1250 739366133 739366141
    0x40518040215041512020d1404061104060518040f1d0105091501170106181d0105250201090b16080609160e030307081b060f09030711120a0b 62
    0x26040c41807540030b041414081005010030001003070100311183c030916205040781c6104038418020300034280c200d031026007004ca400038861030783c840c0e00780140e000e00007c0040746090f90f20000300b48220700c03030700010610a001c0784a0100003110b40850855000c1d00101d02168084403203c100c3d080070090301071008500803000a0540244501503110b003c80c001440e4403222005100d0b07a542e4148110001400c1e5000b900140a00079040b4030000c0c26181c420b64010601d41c8110400342030f42c401200030049241a6020301c00c0c10500815005544142c0019800040015104100b000d800c500e0f00c195074a1300d0310b01d000903110440091144904640e001c0c9420810800202a460043c00c0b440c030960f940d5092000501e0007520090070600b860400016941c2d0700b00229082d40501880641142004110703200105560002a2034207c0c1c940e050341c0c410703952101d0501c0740b03103400c0e40c4420590b4404d00c542c8000030050f0344440583d40000748410070304a144000700386000000f000494111506400780 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 739368633 1250 739367383 739367389
    0x609020a110f0307020607151e0f020f091014040303090f08010b180907030c09090512030118090c051c02010e010e01021929060102060a140610050405180402 69
    0x8128414070000203001e40348003034815640c0d40d0003411000780c814100002c0c42c500308000600e101c20034a140ca6014824140746125601400c06248081c1c03405600303001181c080f4180c10320071201c5481076140000c3c14101c1e0b076000d00c0507140110b0a24414070882c2c040b120303050807071203000c3d00c0154400d80c0d403030f2011802d04501d00b002c43c1c0c484d48070345511ba06200c008001c81c0d480e0500b6071400c080b00b00403100396660720141d61b8178224003648017400c1440c4400c8003085115898125030a1240980112030310019003419064851009201d1400900007000046080e4005a0060884d060084669502c080d4a550002c3c4010720010740b644a4500500400d8045580088005240c0794007403c05080b205074aa00103900e419204000d0b14860807611846010001e2a81e0303000c0c01040d500b580300744480c402c0d2490b185204000c2d26058054030815001400c0c044e00c0740038031690781001c840440160744030a418000381640499180050040900c03000c6012b031505078201030f40c000f0251151407641414014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 739369883 1250 739368633 739368647
    0x318070e01030c0b0301060c0b19140603011a0d0311030d180309050f010e060f0c030a080901061a040312200309091509010605360910032307090609020a 67
    0x5a4001c0d0042c0010425150444a403108142d00500522a00d43e5000b0701e06880d06c039030301c20b0021050f0bd0000c02c02c0e0110107041e0071610500c0d081c0d00800c00003d03118031140c4031507071000005600c40100314586000a100382d403041c00c001c0c07040c021a420452000c2102d000c2c0c90040140404503c0101103403000d25a01c184608010502034891100a188640000300741d100c098902e039000d0f80c0005140803042c6040070407218916aa2020f403611100a81c1e0001c0c208041503d00340415030800c0f1b07000c144801c100e5031940148254103d08c628042c40c5585881d81c0c800501c116a0901c500c401e80381c0c07880c0340c801c4885448882e03400c0140d5525400441040544035010305000c0703007105e2418120b011500c949400d0b5040d2003040c21302d1034076108501e4039051036105400c5400451007403818801039038140080090f021240c02c40d41c0c08610780d0f503800c540d071010b42d4030710010b03124441d0a82c41e064401030440d46000e40072030f0a02a10344c169210b04001c400c0e981c1aa01480c07400d80d001901e2a0b42d82e510502c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 739371133 1250 739369883 739369889
    0x603050a110415050102100e070509040c0e1501080402010309020102160e190216020d020a09140712020903070312110a080a02330612150714120c0318070e01030c 71
    0xf10400850030640002d503141000e41e207044c0c01c00c2c1d48400c28030103c1b00401484001f404010031001d4189840d1a00410000091180600d8620171b5008140007a4204284034907450040c4d481d5061aa00c43e0011005000803150681c19130061055802000303040042d0031029041c20201c0103264200824080c17512200e4804152200f4414082031141421030307055090300035011a040700004d1864000980164100c1d03200c0107a231403a02200929100354109510f10401c0c075500c034042465901d001d54410b80c4a502d03545981900442000d200064461111050200c01c40c0741003000d1031a6900d416107003101c0e56106650702000030940c4101c0503410846403448600200042c0c1442156241100300c3c02c00d03240389000040190400a40d09449454021a02211000c105c3c4e421310001c1030390401480e001d0783c603c4001440d040c0001c072030074080303012a40c8039040c003140444c10341d55a4401d00d4030303500090301301c818402070b141c541c0a0404080025901402001411403001e501d0362401d00c2852071194 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 739372383 1250 739371133 739371161
    0x20405130b0a09050703020907021501091401060801050d1202010605130501030c171e0109080a0816140909090a0b16090603090309050d020f12030714030408070501120603050a1104 79
    0x3d20380c9000100089a844200d90b415034503c61140c64002e011390801319111288030340142607100000308005030303030003035081c1100354448a90583d0300e070300e412100d0203030134001d40f500009078080382e5001469490150a00300e0380740c400001c1c0107407180005500700e4080740b00703803107000c0d1100c0050042c051500e4503800103120421000001c004140c90154484900285902a1179040032254900000a410403060310342d001380c071207581d00c43c4100042c0c44940c040d2968181002c4201007040e100340104041000b24446034002070a04400e002000880c4030003c0c0a524203000d001c860f140022001809940070f108040003090b0915114503005204519a50103002014101ba10040101e0b41100403142034410544042450944500119041d01c0351484410b07001880c0d10741031075404001001074804a0700c50310b810640709260590050341c13400761740250f8074140c000082c10800c41d03004a11b6640c00085000020074015900d44585003801e1500200351241c8032400705858040c41d01c2d200d90182d0304505 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 739373633 1250 739372383 739372391
    0x1303020310090f08070c05030307060507030c020a0519021305090f15060a090c050705070e012d0b13120305030411040203041205031008061006020d0c03080703090c03020405130b0a 79
    0x540c88102c0030f80000c000c082c0584078005404404e000411526001400015003102c0e9502e4052820100408007141c800d0300182c40d04c0703448480544049010210150408001c012044000100e40482c1e10030074002ca0744008070b0892280c04071a68003c19101e00400700c0500250342d1000621401c001e410701a41140161171010003009580b00760035a07003a60b80a0b040064a03d0b030303c10081c1c40500c035805c4040c1451061100c001a9022000400d5050f05c400c00d03a40c4030141072008019280c510502103005074107003070f108240320000c08200a444441250700c0c61182c42d980d2003034803a850000c001000e500040d40003017000305100d58039080d604101c1e01074038210301e140b420303440c1c00781c00c24010200101003101c000041840c074a410849040038003101d10039281541451440e09442002070300c00c01003d40510381500b104140644400381d043e41d01750b190085595503144c0d086004007803980c411548400c0910012000da00d0720b109241c41502c03a1048507507000308500384006022801400d2441007420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 739374883 1250 739373633 739373651
    0x170f042112090f1208090405040f02040e030909150d140a02090c0906030a0e0f0d09080606043c0207080d05061e0909150705120f0c071e02061303020310 67
    0x5003c1492040b941c50b10040418a1480e107403e00540c03007411000341d800fa0400082c0000e1010104040300810b100716420004007030285d01d0603459000c3c0342c28182c2e1003c80c1c100004c03802c42412800c503407110380052159502352100da0720640e4075908020203c0b800d500542c82c90086060001c080e9402101c0b12420504003140c0d440080c03541c0c480102044103243d1203007401d070454207042100b14000c82d40e600a03201c171045c944400400b003041902c81c8030440d10a00020a005082903c038100300c0c10034500d000c5c07103464030301c03002c50400c40d80d90003c010202c110321544a41000303003440500701c0070b4401e0201c0c0d03a94032020100e9001345d52024080603c64400035410311480071402d22188031900058680d40b07140c0d520180081c0c2000c0d0307880a03014403404000200066103074800700400454102000260041c2c4400301c014034007500458180c228424208048001f14001c00300c20043d84980342d403011590b071007a50108070f241d04150300240801c10308490900c01c600d41801031050f285035100c020807003094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 739376133 1250 739374883 739374899
    0x807140604080703052101120c090b10200706110d030608250902030703022203030807111609050610080402060405060310030602030403020d0e040504170f04211209 72
    0x3c6420001401c2c880006504900a034401861584407144845000c110351f07074407484207108044042c011100741444a0700440c221b2501d00c140c606400026086403414030388410f0503684040722080c1031680120780c040d41c80d0002400c01109014103c0f42c3d99204042403c103200626001c2000c4011081c1070401e41c043c44070002c0025141b032020b0315a20754504010300461004001d13040c0d504005001400041000003035500f54009000b1040c00801401d0b5080c180018040c40c0107980c040103001a8041d4081820301d1b2280744a142010203c0090b50940508021262202d2980d64050b0f00303c261500308028062030280c1144084030340b41c0c00c00b865a80b41a500048880c8594010140f0800340440400c040d40118800780014503800141150b581c1024103020f5520038403190b152000542483c9850014207150003140d01803648100380d00794030009022580b41540120b8850404000d0030700c13001510340740b460414803030240c00d1020420000c200703007000e15044524142135070621619080c01c0200302 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 739377383 1250 739376133 739376137
    0x2030307120b0105070206070605040b0f0f1512030d05010303020c030307051207140d03021e04270e01110c0f060f04110402160602090901060207080d1b0b04080714060408 75
    0x65265070000032004080b6005030b43d036000d041c1c0042e400040119941041080c1e5502441c0903d01900c0407104030f0f990000300394403091084811900410200000c910440d6049038803048139100140f110f882040c1c0b60300f502c1e10b940c00090214024a45a800420034990103122005010344240c1c00755152151f1f0b43c40c2d040d03448000c181e646600560002b049800d0264202120424030b0076001901c100030002000100030b90011a035403c400c680a801985071440c2d404103c2e0300311050300000d01c80c2201c117040508800c82d041980030118546400d007074007a180c07080c410441c642ca8012100f90310358403070311f0301d84e03161400e1960b00c01c401d03600c80c000388410b8504030602c035980103600c5802e0301d6040c2c002c0710118000c1d000380003100000d0320016034100108441174004d0501d18209458002a50381d90f14030032a6508124400c41865403c404a00154288540c116005e030b0798541441400b55421a50b0302146508110303400e880110000c620101008944c9808400f499048030041009050a4071081918 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 739378633 1250 739377383 739377407
    0x30a09050105361005030924060603070c0803090a0311061512070906091a0f09010603090c15050304141f09110405040507050307081906110f0708040303080702030307 73
    0xd01d212640031a180c3e808031260112102812449018444040c090035542081c0c40d00718850268900641080a00796100d115400d04901c005069460714001c3c4525a4409441842000b420f5030074400440c05140c015030003110103d004048406680c10010a0504d01d500b40080a400903018452006001d99942c3c082039009c0b1000c00328131042030292440c1810a901200c0d406003041d0000500098039801010225806d8044040e0305103414200030092001d203840540c48500350005000382d82c426807086440500c11490354044984510f5804004e00a201d031410019800200304000c212010601400a241a03070003406000000f42c003c00c0c500d0041042e0924107903a80d805001441000d8522150150024101f04070a0030142489a101c0b126401058000d2191280c002165800082c1540d08014078800c1144c0d0490956642000f400c6203d8941c01c0e0352805000c0c0001e005400070013000d100c0d03c5000c01039502c070301e1460083c0c2010001410442503410a00c1049181c68003c1160015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 739379883 1250 739378633 739378687
    0x1090c051c0c021c031406010201050912030c1605060601030e07060c020105030a02040e04030215093403081605100b0105030a1508070b0d060b031e071709030a09050105 74
    0xc54aa02c812032820788800788071802c2d0300c940d8134140c1660350154884182480c0a2565135995a140001a0309903082a40c0c1e820030b40d030014011a41c140c0c1e075040690741110600d8401e40c82d083c10201c41e000410380c032803070039200c6030040c03c02d01c0340c0d0b5a014851090341301c5100c00070b440700500c6c100c3d002d002120130311401380c11f11200000150850249070704913009800280c803608d425041c2070500968072400c590030003a02c00d07002da0118804000008100751207941c4072014180e07102d1031224000090000d00c28402703d580030443c01200017080c80300070b0580251480d805104c000541d081c818a4211b030811b28080035843d1840031940e507607011085070f9000c0d44114002c150900c4107070014403501000c2d48910a00c3c00b565801003030500c0d42c00000e00c40300e00390b94000d226454842040d03030362034401a1007440b8034284801e240703102d41d5000c0440d41d038042000e040032070368004202c49210741100c0c1141c1b010304681001031100c005075006040017001d04420301e005800c0c0059001d20010454240030040c0c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 739381133 1250 739379883 739379891
    0x20304030903020901030809010e123a0c030201110901091202031c0c1110090618090204090906050702151314100203011d100b0309012301090c051c 65
    0x10034540220a400021580038001000d55a500c0c203100f880342d00070025940c00203076409519040e51810403c5240100c1c09140a8180b400c040b030346c0c50800c1003402c043c1907842c944d0f800316200b90003090200050401c0711903c03440c6240240d49002421185c03100c018140300b1005100c1b00c00141d9000c1224802d4a00d60301101c00c00a05c4c40c0002490322500b04d000314060301c2207600e8414060380c031a1803284414420100e000e8a0000a0304002c40d04d02d41d030740504000780d00d90038100881845825801c1034005034100d100407180e00e03801e503603041e82d200e40c0000080b82c0d00c1c0c610750343c2040141d100300381c1d002e2001d201605150070084880400c2c0003000c0c0c5040b8041c5a6001c0500030300c03a46445003184001c040e011a095800c103003d106010b90001d10984503503590f040c0416862503141d080e114810701443e410340f05131071708018011215400242402d8103540d6110300c0c2c100160303c2c54124400400e50040c01d84d030590b141c03400c10400e440f04034044004210050000f0020024011181a8800e18144003c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 739382383 1250 739381133 739381141
    0xf0601050318010507020c0109050402040308072406060509150a200708060f010503010b030d0206070c1e1518030e04021e1b10020f070209070504050607080c010e010b0a090203 77
    0x21903041c11486014241e07501c1d2200b8003040340e1b0000340c101c084100c01e0301d6226a1603590000c0108a004500c03002e0305070700342003259030700044200c510189040f10302170340382200050001e80c02c2d0842e4265000179010880c001007006d01c91074003151142c1c140080c01c001516000401d60000c1058503a00c250b160708080d03500029080030028058813024107814021903030b1510b40705c00354011994081c0704490183d4a05440a6803034100858000e017171181540003048185c0f2104d0046811102d01e50782139030400341d00d500c1d82800100c04040b2001280c09210315129929402002d10308552038580050340c440380c041884000260003020b4089844012940145c94002c04003200c8aa12000140700d01514000910f0b40c003250704000d41d403020300301d4103022581c144100c0c0300c004049105800360284400c00c02e100100c010714120054541c011480d180c00c604282e90342000c64266046440121440c1401040100305a9407d108095603104210020300a0103400b07004506040c0250040450300c0d5000070000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 739383633 1250 739382383 739382401
    0x160c0303020d0e06101e03031b0606140907020c0307090e100203071112130e18030a0c0b060a030b0705160c090207110a0e1503120703020f0d080f06010503 68
    0x5507400c40c0c0748140a100c0c950b403c5907030300c0e15184111940a10032000c4c040220b241001c403078001e1144030380415070a03002421602e0a4400343c960403e0600d54140000c00300c1e0004009000380d8008020004502003400001d80801c150701000400c14070441d4046142c4c020a65000182c0c81d04542d60504001040340d0240d401c03a00301004a03607100149800041440a2070760b00c0604c61015010390f4059074016200005010002c0c82002d14400c002c10b00c1d401e06005003d2060707000c0b50004141d034048039400610038821810b5410400070314000c11010121a400e0291100d40b56500c044200ea1400c0c0f540e003541d81d2505001d401038040c0c0c0402002084c2110b8030040e2100d088000381c1c01500c50114550f84a42c5000a0343c01580201c0b10814003140380410350030402001070950300c2400006007030342d440c204802d60074500c944606902d4842c412440b480c40344810014a101400399003d0928500c854150a02c0c0004006e900360030400f6030300030420310401c60300c512078200764240303485666910f41c0085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 739384883 1250 739383633 739383637
    0x90a02091603060e071809181709030703210801080a111207080106260c150d020d1b08040f0b070e06030a0c0809150a05130804120317160c030302 64
    0x4036000b440d1104050045054001d075810f00c0031880380d0810000c40ea00d80f00f4000a0754100f480c0600c088541044138800111070304a61103c00c510a009c45003004511b9001910b0f0289591040e544400420003403d1140d5403a81104c0421750030703041030055035240c04038507583c0c1c0b04580c001420114500c2a00c0500d03656a24150858100b200100c030115a00c90404600a01d854460102601108107c1ca108404100560f81003c0b50540203426500b00007024008180340d55200303c0c0c503140c0d0400c4507018542c0a4805040d0f4100182000285031803075080c0c101c140d00c3c481c107180007030004540421002480340e201d0003400641c414000b40d0b26880398038094403080703000c40c2096400340002c401c002104040d94844104040c960b47e510025482d00c403c040e4503100004080444401040e0005110021940085e5040440b00814041e41c05040c0c48407000f5230041c0d00400c4034010740000e200d05141c0d21031442503c14140b03408078050f40c20180004030002d04418014018060000c858000341070090741 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 739386133 1250 739384883 739384889
    0x403060e071a09090a180b07030609110702270103060c0507081c1103070207170304081606021219120902030609010603020909030c0706110109020a090212090a0209160306 75
    0x120380300326070342481524500c0380c01072003811380501d125200083c101081d41c051120900082d100e45103d0042c03c0e00c400205010040c48a818181c8031407002035802c0d5144105208181c11178042e030386a100301e00c104010504030707500010a0f031904480c954000b0071640c1d150381c1125408000064001198841074449000c0c0e07031400b81507007601044820081d21101c814444441c140002080003002a010301030040c0025501030006030310100d41405840070702880c1140d2400c6100c103d0741001d960b0a0200d00e13200501c10788280700b0342d10320410031905804010441614000e50101420101c03c0e519840e01c0c804810074400820041440100c0c0075030780c41d4018400075030040c09540c0285000314005020f0549480203c0c01005410b00040c081040030003503443c120b860380054104a841d10004039482c00118140650344c0d540d40d030880c2c0059a410711100d0007881e88150141e107480c0001e00c040e012401c000c010600b10380201d0301142c016651310082030307444022008104030140b074840c411001040507130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 739387383 1250 739386133 739386149
    0x280201090b0406020409050604110901030c030b06071a0a0501080307080a0e0d080c0f034807090b10080627040b0610110613030512070903110f060403060e07 69
    0x702400140140c51300100166110040144402c0e100d440c240700c1140d01086900c0001082030090301c01a40c86a008a415a40607190105003014070303000003441a40402e80490b1f250441603100c00450701c084513900c0d40112138180402242d032600660603202e10513002c0040c41c1d40d40020306280c6041c052940d100e07010310050680d100d01d81b81e82c0f4001031154043d0140d118240320340114840d82e140000100c800c0c2a100c0c40b0214200300c0c0300380303901c041c58030308240f061941c83c580e0780d10742c3e000c0c002c00410000741a81c403002030050310701d400482e100300d80c09070600310301849280524081c02500b020900c1d4028000303071070110300390070514515550052560028420381e840701051105003c5641034940c0640300855840fa03800b020910103455207001891540340c0e5800c148001009002080380d44080d59019003071091612060703a10308020700200b107074030001144040c0820320900020318690440c903001902c0d8134410381001e00001d2140d0103180f00003000c094481c060700c80540418084000100206 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 739388489 1106 739387383 739387403
    0xa02041412031c090309050109081b0f0301020d060302130605030d081b0403051501060809030d02090609040203070f1d010f0e03010b19030302060c28020109 69
    0x820071407100d001c00d010005010100c000c003146600e8082d01e00040c2c14003a498044c00b07821342038218134101f0400c040180814000000c82c03031304210100706081040d5580c0c00010f110241c0c0760440316059400461207d91403440c2da0040d809a0b8804c0303500005d00e5030207845550403515a03204580c1c4c1075025010030110786006415140c0c00132001c45034002c015280c4615401c543d8070035441142c030796001c06070704a41d58802082c0ca07400b400c2640b5110702c0038181851260b68074020b0030381020000b94005080051a40c1e0281100c40038080544107540740d242a03140600300e955501c4003c404299804000803017a02d003501e9607200780005031160300007819252000c54a00c2805802250599070751110784c1480c0c0d550f0300d0314002c000180d03010b414205081d4a0300a050074005449801c03a00d500380a442c86a002c03242c09083c001d40141c0e5809141010050701b00c0c05001d400802800510711 = true := by decide +kernel

theorem cover : BRFrame.Cov 739208633 739388489 := by
  have h0 := BRFrame.cov_init 739208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 739208633 ≤ n) (h2 : n < 739388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
