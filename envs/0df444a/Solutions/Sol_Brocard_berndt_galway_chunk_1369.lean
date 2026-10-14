-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1369
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:37:12.368913+00:00
-- url     : https://prove2.me/submissions/81d07d62-4452-406a-b872-7fa87b89b32e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 246043165 ≤ n < 246223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 246044415 1250 246043165 246043169
    0x30b090c130203100609081c170a05060a1706062e03020703080a1a090703021603180801060501020d03020d2306040c08070c030e0d02030312011703030c0a050a0e040f06 74
    0x1044a80540c075500243c84d0700300c0034087d01140e94440c03e03822034414000101a820000541481c66018041405400358a042202d211901540b28020300a040c24a07030b00400050400c003000150a0b0602036909403a0b62002c0c003102e104444030b03405112a01e00c690406803002c42c0f50203403000300c2c0101c0c076000303030103034000d03200c03e070082081140040c40400c0310b40a81641080401c5264808421800401100c0807001c1c0800041541c03d00084080600360031101680034043c2d1601d4203001ca02038a06e01042c48950070024880e410300c0400c0001d81d03000290008403428a00740561101c00300c0509000416490741e046d420302030140d0b12011442e8202401030701070312003641d060240086400055407094800d40301d0f100010301e40c000b4500440c1c4030b1041c0c500302210003483e4131158200e40e0001f902e580c21440304075a000505000400c280840b107031f0040707441d00001000d903046203800200310600d03004484100c0f080c040b0001d200e030440d0344521204140d07020001c20400c2200c4d200c205641c000c0c4064 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 246045665 1250 246044415 246044431
    0x5040203041208090c13050411040e030d240e04060f060b0a0e090c030703090c08060103060b091807050d1a071101060603021c0c0507080703052a07030b090c130203 72
    0x1c4000b003040500c011034011145c180207040043c00c000c01140e29030013031000601c2941c1034038030950980c1040ea01c0d40681d500c0c0901081c01180c031004038410300800c8403070002150f514100b440706038044003040d21f08554101c920702e0284405503541c0d8103103440501481280700c0016071900c0303030201d8580003000c064059018940e4401c44070404d024140444140107864003a5242c106000042c0c00500c6a009002d156104003801d000e01a0b44a12451901e20282c00c1122450b440c2e22804104c0c2c2481e00001d540311143c07000364815041c400109644401450103414014203a400c1c0030703000c0c0148003261503ca481c482d00303c1c4103145040c06006150101c3c0342650f4102d94200403001641780d100307009446c10380f40042d10030116056440c40032402441002e00d054148081445008085040103010304207580c026201c107651001a2407100c04940b002d10701844031b070600b4030120103202d076000030048180c4c0d42c0300a40c1c01d010380f00d02e2609458001800d02036580035a4100c0000040c0785180c01850294a00e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 246046915 1250 246045665 246045677
    0xc0608060402030403140d2012090d1209020a1e05130b0f0f0a030b0a060e0a020307200c0604061805100f0c15020708031509070225050402030412 64
    0x40030200400c0e40b000341c0340540041d40c0203000b802da182c00340f4020224090f005400007940c2a00d5421040c610744d0341005040e40b290040340340313508540c0d84880603511003900c9000e820319000444001e00090b1a442540f205182d846514404548904262401814400841c4400005580b000302441d46c0d150103101e00403101c403c040c07907150282e40038204820000038200300d0b5020b01c41c401d1010380c6604210841d4031540c04d0030000b02042c0b80f42c809502420040401080303080c18400c40d001e2000c0c0140071000d85a00c100104121a07500110204640c0d00380c015202c044501840031910300441000829404000000c00045103600b03d00c04034154080b07601e6207003603581d58904001440b1551001640802c1042d018200f01c548125658012148603046521981944041348412a08401011128040d0010a122210003034806140f100c8200311980d4080b85003906000303495000c075031410301c1440440a00f4036228021004400c025150252085482e882d06003410b2504441c3c44140c540071440d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 246048165 1250 246046915 246046921
    0x901090b18130c0212070203010204090203090a120804030801030b090a020a09141006090519080601030f0302010b190b1606140403181505030a0e01090503090406092c12070c0608 78
    0x600c50290040443c4140c02070240d4072408024020264842d4100301e0f8555420800419850030510181d4003506144000b094810300618020103c443c003860303d4014003d00104100010394072035080342c19260721080c01c6605440303407400940707480c030240c1000b54404203d14011841c0013147c1e10500181c042c40e41c0005250315111380d40d580c0c54441c1d001d8240083c2511000f8051401d260f01500c0d084a24880c540b181c1c03944e20716240b41000420780084801c4c1c440e84c0a240e090690901804052080c116506940e4244a0302100322540042c402d82c882c00c03801142510710042150a507180d1180c00c02c0d418040e003075900c20800700c82c88080f40c048011841403180c009280c204100d018040c2c81d840f502c550070010020b0800da440e508000c019494030703601c4d5880f188a1400a00510303840503c81c900540e10740640008010503103040b6040420f51500c0c2c007031003270461605036000c41c00c00201c05528840c44e0410300f0055080100030600c0343c03948900014008100241e500580e0f00710383c0c1313954038005161 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 246049415 1250 246048165 246048199
    0x709050703062705040302070806010806060109060f0903030e0105070203060a060f080307030f0309020a0302062107020123150901031a1b0d05091e10050a02130b0901090b18 76
    0x464803401581983c005851443c4000d44260f003d190024000d00444012559605c182890a04240c00800c07680c0c000c40180082c0d540c100500c840a0803a5041034414036214000041011040344009000c02814070070028060b4060000c50b0201c0350046d040e12024035000c01404050281031190340710000a040c40018440804401d4402d00c030b5040e43c0c0c2e6070071951000c008601814885005070382c04140380c40004016a5840001d24001d82034101e980350306110001062a44a0300030076035419641005007002414140645048006005e901c01e00070302d403a1a04d15040c801c01c0d0400d01a0420340c1c460002c8180010b41c8640c0300800f062612081169890104200804884c0e100341211000107010002d092210b9410050740506581e0807207507402c10f00c4054601500d04441480300e9a000321455020b1000107000c1d49a0080c1200800e51038000341c03c51080f40d80f0764901c40c1300300c503010102d900300050380f20340c82400c000c0a9052907940c03115040942d0800d0103401040e0148a21109402d50b8001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 246050665 1250 246049415 246049439
    0x50301031502070305070f1e11010e10230f03010f090b150711011e09030302210f0d0b0307060e03011d030a030207140f06010824130212070905070306 66
    0x3d5030313065540600b0a040341d17540200707200e84210b0072034058503036501e000003c10072901c070242020b00840c0c9002c1c031070070054000340049103041442e60140d06807001c90b10b0801d030040e0101c00c490b140c0813425040c0301d0340c02d06002d4040c01410315a2812000000000a1a002240c001815600c030500d003080409004410421105510b00d010341403094248501d0010455000e940e50b0b0410041c10184c001d00100112204030312218240baa0128401100c00d0003816030411031200300d89400160f11030072150407803080009024103801c4a0304280001110851309a035a04000b105507405400c1701c4056403140c402400d010000b40303c803030196280200b40210074010311801000b62961002451909030b0b102c80840c041c2d4803d00050381d001c1c1c007880e00074085010820050b2141035008000d428075505242c3d18a007445410818030b184214803404481059900746103a61b04140c040c041c16000408501c04203c80e0f0401c0901c40c0414054098001f03608031054220a1003000c0b90f03075003001407540340d000158907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 246051915 1250 246050665 246050677
    0x50406030c031502120c0d09060c03020c1e030909060a030f0308040b070f0c030f0504030f081905071e021201090501050a11041a09010314070e03010b01030b030c01080a0f0c050301031502 82
    0x80060340c5c0c0d001c5002e01d545080140b1064440380b1000c541600c207501c44009451201c100c0100084e800500350382d601f0340c20b002000c1c407260f00300c5080000c00860300b400c42c0d890280000d014031404100340451919038408102d8401941c0c0641580b0007015281806020310b00216800c1e9070320904c090004841910a440505620315140c8440001400c291022540c00c082403040c0070500034200300c08400302c0d20341c001d4407001c18441c1c1030843d82c90f82c3c20040d0700c2d451401490000c052060610480001035a4185100c0e1503190005194002d400c2d9800010040c4207046e9070a416540b80c07000c260240041074102900c1290a00c505100511164140025900c80d603c08c580030b136202855082000e00c019402001030850504d40822035041e00301c40b11002502c15101540800c4041c84034417240d00b03083c0103010300040c007424104044001900803a403a03420702180e440c1080000300004801c2d03851070340b081d01d045a40300c0040201013032080300a08998001e0005076001d0031180100c048030509030080f100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 246053165 1250 246051915 246051937
    0xc0e0414070c0302010605190311040204030201090b091c060903030c05040f1a1902070603240303050d2c25060804030207031b181a19050406030c031502 67
    0x344a6940d00001c80c0c2c0460030300c07800c4046548604000079aa655015804200d401d01c0140c48039003441c500d040c080740000c4001440c040d50050000704007603a0800c00042c200d54210040070780c2c45595070f001480d0b0070702000c03a004048684000400034812240d01c5109001d1090720200500300c45d1080036206801a4801c050800c110240c0610100c1800b4020f508404800d2054500301204034035200c8041c2403c0044e070b00142c2c00140100316540d418050b900c14a90700e420030b41301164044503070040001c01c500000e014024001020103000d6180ea02018400c0c101186400d1500b0b00c44000d2005c0000004084005100e160302208158030350820000d0707541000c6a00b000414a00241a5040c0400520030380550188820020210b070044000030302c02942c2090440c100781c1080000c00086000868400f003141c54990026825650440381c4080303118201e8000a682c5101c2c501050b196200da080903411a0611400104001c40c920704c030300649110381c400b1400c00d0220600c080032805680903040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 246054415 1250 246053165 246053201
    0x50d0e06040215070c12080c0607030612060b0f0a0f060908120702012003030a020307030f0e0c13060306020f0309010c02031603050307050f130501180623070b0a0c0e04 74
    0x100c0048500401000d4080c45188400b0042d03940b10003c1c01070140c552000e948030000003c40b805000c0040c40751327990210b1103040801c0781c1810000160541a071540009020303550702e0b400e0008a503100314004001034401005080160344402280780300f2410743c41440003054100c00042020307000494a40044803402d00b0729030400b203541d001101c1502d80e00c203038014641d8900c035000010500c00d0004500c40c40144c1d10150b960305040400404407410034a4403a003103846e058003000c02d6039001c51041c661000c1250030405501c051016100180b0441d40000c00c00c038800a15840101d140d0030145205520010081081404ca07200580c0c07203110f0321030541c40c090038495410780082e0252024682040d03d0f454481c0c01c20750342070030461059100000b124059a4801c00030001ca42c0e000c0001892510900740e246101490f02c0005828801c185801642e0b8105501f201d40492500c17806484c049174006201480310b05044180320010300b915a82500000d60302d6002041c035040c03600461400e03003000c0b4000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 246055665 1250 246054415 246054439
    0xc0507080d090210020a051b030312220b1012020a030b0a1415030c0618010c0203010902100801210f1101170c090103051005060412140d050d0e060402 66
    0x945441e901025941c0000e0b60354402050168590020b0843c03070034400d4008020403809401d10030301d0824101400100035a400204480b00e0b180801134500041d01c03010072400a803140b90750300c41d20100900301010107100b101d40c00d00038013a035141401e000303d00f182c0e002411180c86410001031340b00c0342c000282d04555802030800028003a07209a80d4007402d120800030321034244415410003040142d4103448041440e103031880e520314083c0415144490201c1d41146024034558102d4070945014001d03d0602000c1030b100010b43d1003e4102c8224240c1c000e1001e0301d90303041620080c00039402030180ba04c42000103202511300090b0b154010364500e800c0703858400503610035501c0e004110020040c0034104103034405582c2c0141604c0b07480a0003000130303138039241d111f41c5090001011540000c01600f424245aa0208900d4407070364104d40030f0b1a030101c80004d056007035003445014514000b840b048107119052105a0349948030025141720302880c9002c0c007462810801071661001c09131400380d805004500701c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 246056915 1250 246055665 246055673
    0x3140105030c150f070c23010c112b030519020a080f0a0302130609050f01180e070c0b010902040611010b090c03060d02060d020d0c09140108040c090c030b03100c0507 73
    0x2400b00126840c407014506120b41da640a51000e9550050f982002152001f140e030170706641c3d0b0503d4405083c81c1c54800e10505444842240c50041c421078050807000d4a108480d540b100405149030300403000b08440a11280380040c499400300304600445850140d02103c401e01c08152101c1c030f1034101e29180e007010118600c80b15a50301081c01503003455401c00000e040303074101e10011070040c0380c182c584402d150719103000e10500c0042148080c0c10010520120403000315240703030540917240020803c06059407441c00c01c0c1c0c2c0c01c1403100009421a887c100000a6558258005105540b52030360b807141d070080700c0c20226090300c0314201c646038408424400942c01d1540580a582c1c020b8009083c0441c4a1080e008180d181d88200c5110750401e4001940c2a101159809181c0c100085442d09001c01031900000300c0d407101c030380c01d40981004010000f223030902000a80100203021000300801900e8845d03100640149030352401c0c98001d015100d4081407040d0700303102c1c480704004140c452a190920a60b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 246058165 1250 246056915 246056917
    0x111070312090305010f1e020705060a0c030b09040b0114010503090613060b0a03050309090f040804031212060b0310060504180b270a050903031905100e0703140105030c15 75
    0x1c060041014900d00000400c109000b8624205006800001c801c034400e40403000315a9012040000e090040002d400084c4000032059400394236004009060654824104c01501104010552107441101440103210802d41d13514108c4900c1d6040c0d10003a1100c80066415000c101e820500b035401110029041074104e141a2022a12070540020002c0d03a180019061010320303001030351150310200e10310b825804d100e51560f4000140d864848901d02d41942d411090b0300c21400000d196800c0845085259030040700c42c0d038440f9142d0403060000a480703a1440456070011500355800302014400002d445000303a0480301036942000100a0168400711544040c000d00007045402038245a1000c000100d81c01844034160044e80b00312482c0d0030580403d05c1921000f42130545503400410a0213150000c1c0400c5079000391007072102040c240e940440c040042403403070b80140052030b4841e00b0862590b926500003204005604a68015640c8075004e02d0b503030306110300043ea00000f54044011954000c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 246059415 1250 246058165 246058193
    0xa0c02120720090702030426030915090d080306010e300a05030d05090d0806010e0904020301020d0c020c1003090c0302040e0708100c0801060507020901180b03031b070501110703 78
    0x120a071101c81c4000b00807654040c0202c8020740181c101040034040035200802d960301c0703103078611440c072264a40501007030340300d00c5640503071751040314140c940030002070100c03083d070303070440030080c901000000300c1e05000e0380d00c0c2d0084810350300098034a05507507041e10b0644002c81c088125010100224119594034801c902c440b040b207020103110344824800041d200300001c01005030001c41c003185e5404c00000c000d04d0f0010001c014002e0200c0c000801009982c00110041d00340320840790344005803900d002181c0207210311964081c2c1d03942070a864074402074000079030284c1800f05031040d000355800c2c10000c80494680140041000203040f90030400740c034080d0080c0b00444100410385600641d00d130003091501d2030f44100344043e01d8071642100105a044800c15004100c02d04215240041a90000342045814060b0341848580e00b07100343d00c0c1c010f05030b00c00100410060203da640340e1903407019031244820301c0240f0701d9501ca141340120301548180f43e0000c0024162005100060841d40d03240c0c100c0041d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 246060665 1250 246059415 246059453
    0x1090203040f03030c1107030c0f050307060f14160f0201091d150102011416030c08010503030a030c020c0a0f090b0607031407020418060e120301050a090e010906020c060a0c021207 79
    0x503100450f401441403007d103006510071410105030a2801c50350895041e02c56200300e00c203030000f4800300101c54004040302c0f004030310f51400700c410303100301c9540c0840f5010b052103405201604a1031081042025042c00c3c3c54103000340c136100740d07151b0381c1c0d490380781c0b02c08141c03070320404005035400843d2514120029204030184140000320305014a0040354003e800300b10340c0e26000844902300400381603050302c00d0016044103031411204960618011030783d28480c050125080507510501042542c2c0700b808448200e0310004c064100495880320000c040c02158011204128540064010903141050494140b41e515480300ca0715282103001455889e04444000d9800907100d25070f42401c86107110502d84410705c605400940160030b62000d42c606071094a940c00707030f00b1f410401400250b42c1c002c404011580751803c00302c1c8942090b001e560241c1103000009103180c0c00403a0300c004070000481c070580702d0070040c0c500304100400007200720799402c201e05181100f1401003100e040800c402c680c1d1840c05042c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 246061915 1250 246060665 246060677
    0x1006020c0d151e0b04150324020406030204030303060f03051e07050a030b070f020c0f0607060b030105090a15020406080c0d02190801150e03060f091207030905010801090203040f03030c 81
    0xa02c2d100c107801d440400120b5490081c25040c01c12286a4910805950030000e541c200b01d144114102078111070158000605003070854035488000800d4110481101054508103640f101c0e41e86d28040d0203900140021001300e030424801003100b40c42e0f40101404c4a810200400c0300f000c4c0c00c0c00555400f50300e194448a580160080403540d0f84800180d40001c1d80700c4c50700310040345040c1000070b00c0481c0d0400c0040840d0012655003010341e80d003410404010000311812951401640b8051004007a1071000d144c00d54208400c1088821001c94036010941c0a42c5170788030505941d240070f0041344624040c400c00b14000c2000305202010240142c0448901c2c520300610b0148203064101054100c10418400295244c0c014020300d400d1584203c02c0c4181810321111403c1000300103a116000200f4071800711403100001120910308200345007040d200703a101541d840c2c1082c200203103e500c05018050100e4103000001032014507074400c07240b080e80c1080304960105101d0303a084014117415003420741001700c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 246063165 1250 246061915 246061943
    0xc091504091503020f1210180534080303010b1606090f050721080307140a051201050904030c0b09240603010506010f020601030b04051c0e04051006020c0d 68
    0x180c548150448040781d20b14004003103245104001ca002c501c002c2c440c0c028005407861080b00c400000d0118401010340e44c010464002c043d042c5031600c210b614001d450707442030b094600b115032a03500d54110264400c04044c4844010b0324098040c480b510f2003642d0740c55004000400140341e400c4098040812003e9101ca481c0803161541e0050ba6410541a5002c0c1d08880582007004001c1150354001e14092640851000c420b101c0500100828800500140c100000040645200b44024082d06e003106010741d440b5007201c40004c00c2a00010b840b40da905103c400089014541a800140b0883c1d15030ba800c002e458003507841c3c0000317034805810f03c406480703171902071400759030700046200307248034840d03a4122030303103090002c06082d180b0151140781800306440003100d84079400700b80281541c2d00800600141d444031310f4903d00d401d007144005c1411848420782c4512055200c041c0d42c114080480d4148030a4881401c0500b00c20614805c0401580c0002800001e80c00d00940c132986c203600410344415011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 246064415 1250 246063165 246063179
    0x20712030c081912110d1e050108030a021b060703120b0a0801091509030806120c03060403050304020306090d122c061b1303020108090307150507170c091504 69
    0x90800c00358500c43e03d07107540781c6503211540a0360403000994461800e025100b07507080d103074186104140c600a40c0c25200c000c921450001d1341c1024010396621001000782e50383d540040e0340c8035080b00d8210001801000350140406000b2003182500d0f1600801707841c90020390344da06070303034800c0c0300c00090340c20075280d0000d95100d41d12420900000c00895002255600092411015888400e034001340214a000f9500740841e922401032580070100341c0b0b1041a0380d0640511034942400302c1030035035252107000e04110805512a02030742c00741d072080d4105c40140c0c58001c140c40c1c65940f907540c0c0d01d00144521451900035003c607008440c4803401c010010043d501e0040390720130820140300c0c0d140c8140d4002e030b0501070303a51049030428540115507051942170512000c0b0202c01c406031880080d04114283c008281c80c20700c24000c0300e11a0754400c0582c91f0402c20701e05417201800b07003240c004001c01c1305100100704084496012a00c21303029800502e146c04031302410032404042160300d5a00760803081c0400b140300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 246065665 1250 246064415 246064417
    0xa15170106120c050310060c0f08030406091e02031203060a050d0f120f05040504020d1d0a03140f030a05040c0305070801060911070b0a0f111c050705040303020712030c08 75
    0x1800c00c560b1190b00d1140c00c0807103102030f200352014440400504104110114085040e41000e844039031400400b404014146a4042c60381904060f169000000512007080700f16807003404d0440c030920403038003c01c2642203620300c06140c00d00d0103034240d0440c01e800340610100c00000d60344140010083e032441e030f40398000300e041c001c86241c0403a4024905503020741406a0032100000e690a10325100345040c0c00d0b000300a010317000e184034003030040780c000c10000e07401019a0844145c087d11030f101d6043c255404080d0b5a502c5150550590100300140048814000ca11040b00c0b81401400145851500d4002e151001494010002d80c0c0303d0b1445003011000070014440c080003400c0c00d20010458a082c04903035070885181c005030007003030305080280720005000c03000c0303895000b0141c280c0013881800401d4220090985034504560399800000c2da0310f06101e51341c180c40d203107600c85030003000a03030f0350902d0545841c1304900000e40540d1290200308001c40c022031044440a210b49403402903112140e03500e54103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 246066915 1250 246065665 246065669
    0x50108060f1f0302092b0303150b0712030506010206010b04170a0203120c0f0703020d0602090301060302060409090b010b04030b040b131509030e03120306040c0201021e040f0902090a151701 83
    0x40d80000f8545c007586802c103403a502040811041e0702415008208292030401c0303550004082c5515004140540c3c031003034465030002c010780304110750340d00000d1511055440380c840011b00442c2c544404603459501c0003552906841105141c2803509081c141c14a40b00540d0140e90000362260880301c0c0010386003403010440e0340c0c4603a0212500d64440c11005414500000c0d8146085d0707005000c20405680d414002c2101ca07a0030500050341d66110b40c1c0840d01406042d040650860000680003580104951291034054010003a208060340c80d02610b044078452440042d01018603207001c140030480301d0f80b83e240c0129144000070f40645155031170300100141d0100351103199943e00140030038150825813500070b40400314090000c0d9507801811200324000904098012507944607a031682038000d5044030704540807240c09008550a50528009580c49402000100f585885001403088814004c1d2182030320000c08856040741050498918a038101150b001084010420f80038045207a0b088240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 246068165 1250 246066915 246066917
    0x18050f060a061b0c06092c04060c0309020909031305041a060f120c070c170a140f070e01090c0c08030c161e03021603110906060415030f1401050108060f1f 68
    0x95202d00c3d061250340610385411300245040d001c5d10081051580036010b4507403143e88427a000409a0004a0441c0200b60f80d002c000d4001d02071009016441c5c034004081c080820f4400403c1d400c0c0b980303500c2444107a4540007009400342c90181410107540c40c184015240101036152150308010001145403800c000644240092803000a4054140500c1e0280d04015107400e4100d0380f0000c20403001e055031210340800c0135100341c035004100200001c0902400c81c504100500f1a100c1c3c0d501da08024500318404e100340a44a8134001140205602403840103600c19003181c5181d0956496110385010350f801020400305a0120080d030b240003804126614080f00d900c8030308501d0754540c034500a460306000e0380710f03400300f003036400703401c00005a05441400f41c40c00103a0344030455469510201c1c1d03050180e50080704950803940c45002d1640d6141e807140c5015801518140822086204102c1040c1402c0c09828001101400007401d01e0400c1121410a808080c140c03000f44140301a4008c010400c0b413520300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 246069415 1250 246068165 246068177
    0x1150e09100509070302250507050315060316030c140d08070b0403080a0203010f050f130204080d020c15120403020a02150904050a0501060e100309020a18050f060a061b0c06 76
    0x11102d4208050b990307501c42c181e400e0131458880c41c101070348100f4204000f146880c4c80c0364001202045000d0008100a140140451b1a54070103502180206203003203038031902034455200055641414000c09004503a00300381d1900c55181070550b0b07d070404010b14582900240604131100006401038003c00001d80915401c2d44ca604061400400080015246940c000e00500052150116400b8002c013255011250080c543c011100414450b40d90321010400c81880810002240301c9c0101e024082c0340015400e03119008904000c00a105c0340c240c80c1d1010314030303003800060032010401c5000340e0403c0c0a40111070708001c090f80003031a07050910707000c600c0c040d4020964124606140c010340e500500514002c2c080d96041140080c50f482d070116581d4803135070140c0c000842080c001c0c1d000c1d10400d500070304600c03032150b1074820200800b8024841801440d2074100000c2c170804200134107500541009214003900361610a040381c0c07000c8000300a049007440c401c1c9040004240c2700d1800020506500d800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 246070665 1250 246069415 246069419
    0x1107030c1407030302070510030b06040e061302031006141603050c01060603060b1812060c0414040207020102061b0d1802040e0d0207030312110c0a05061e01150e0910 73
    0x4840303840d110301c0e16985103612001d02800065008160b10003658002c4e90800302d6070700713042c07000c0f006410f0078989940c02041c00540031544211599140344120707800e44000c100182d00030728038012880219806110011144000d1004522906d00000081e10b03c0407464141540e01d0742842055002c0b16080f00494800203030100b04480c00e019130300041031941420003055140c04500d40c1584202402c40100da0070408224019a940030070081c0d8207051901100d20760303c1c1c01080c42909178014081c00350882d8100e0000202d92078680221119187e040c1c0c054042910343d501c4d01c400704103a44a417804028004d000c0035501d103006103d810b904600410004603c01c0c01401030100312051542c1400340d541068806582d52074000640130b0407a50305107401d03103c000700a0340040041424810b5041c441070002850015400c001402c03200d028040c0303080d1182a100c1e2400004411441c031206030f440d0691500411030520b08540b0b4440348440350410399651501e0320002290000f003107500c01040e045010003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 246071915 1250 246070665 246070673
    0xb06181003110114040b0d060305030f03041e0809090925290a0f14042903100303080406020415090305010c0305150f040b10210207030f11011107030c 66
    0x6110000e102c02e0030002c3c0c0142c04100c800c03544e1300c10f41c0104000312500103400c18017003810707503c80c0f03008541040a42e61911061a04c4011580c4285c405640b8075440c40c11000e204616000c0001c000c5521081d407510300b140c82c2091040d05100200780f074416010348072100740f10500b2542900d500c811400a1060354a007098081510b01200c02c6000c00f4000ca01043d441107000c044080303481181041c18410fa00d00c80c500d1040303480000100002c0f070303465800300300001c44c0c00c2e109460200030036050b0103040c1e03448807034134107109c032400201d4146500030382d8000304101003401050715039000b600524001d8a01500d0b086c03070aa07694000d88843c2e0000d0044001042480400e114641c402c00c59864140400d080c1804207004411849071810b100d00070a81221007140d459a112004440d009046c92600e52020711014001010520b00480c2d100313203030b151a400da2281803080b1034005038541c4800c0084044a9000c5032108141d2402c03444c075643c0c88035000300c02c400c1e14004c0d00d0414401d81d1036140500b11450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 246073165 1250 246071915 246071933
    0x13c0e0115150e01081504020d0b03100b090a1116050f0d0c0c060e01021614040c02070503190c1211010e0108040b0703020f09090c0a0201050f0f040b06181003 70
    0x2c4044241c410030420600d1040c1d02554030b0140c6074091078030401075141d02e00769080c01c190501c00320340d2007407001403130001000c00d41c0c00004805030124281c4240d0302d003c82c0707140103a0701d01001c51584455040c0004504031070640c00140700440180c2540e05103900c41608013209400700303400f034072998840d54161652000c10000782c0c405042a02d0101407080a6076a224500d04043c000d00003803144c003240c0086d40ea40708000d07075000050311140d8021103035966070700c00740c021680d0100700d8001c4d81410a42e148040c0000785800803102d020300142482d2220500c0f5003c1a00c8556084030a000d81e0a0b0001d0a81088400c00c68803500905145d10805400da0001d0416003481420301c2c144203601080101050341c040c18507074040d28508025960343d0348500901c186120350f00c02c2030341c848003490031720a09d485404081c2c04050407940081000f902c550396402c001c010200c07442145c2da041100042d0014600624054115102400050200224040321041c0040450319041000c0e5800d400b0407c2c442144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 246074415 1250 246073165 246073169
    0x5070915050604030c0b0d1b0c02010807021f020703023d050c0313020a0801090b04020306011d011a04090f0e060f0705070303050411060c031803013c0e0115 69
    0x982d018a41071440d0f0303901075812000e01c55103515840101d2070369a4000d0701d41100d2a2048440c10510140301c0e070400140c00300201c0002640081c500b00001140c0030b00018444003c03a80c10300c00f400c040300c030748180000a503121960071021405103000d003141c00311500041c0035580d20100000c0ba043c0040900010202c600c1c0c02002c0d200504202c01d02403001c6d56182104d40060072090000c81e1541c03503001280303d07080380f80c2c07054945c0d61801020000380700c2c50031b4031503010303610890548950380d98a2041e8030340d51183d05458101044000700400c440580007842030400c13601c9800c06402c00381e44001440460b24400c440103580d03034403681d480345000800d20007a40c1c000f4407c460803401d8142204014664045c4241c0181410381e14004901448030f0124848405280103121558031030b00180d00684980014103004550f00c1c800c09c181d80b1a182c18002c8282601644000f0030000c04411403410000c0b40030349038400c501c5405046042c42ca040d0303008032095210240c00101e0840c0060040d007442120903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 246075665 1250 246074415 246074419
    0x2010e0c1207090e2505060702010806010e0a26010b030d0c15020f07030f0f050301090b060403050a0501230c0d020304060e06042108130605220c14030a0302280507091505 75
    0x12880a1210782c2e0754102340c0c0c581a4081c40c000040386c6d511030050310741d403e0b9141529170011002000248204004010807120050850303003401088010342030b54241d403516003070340f03506800c01a50200c45a02c1500c500d07a01c0c40c000c021000c03002024400180072640720749000ca280c100b00160640900d504400d4040069000f80307030040707110394001c030003c1007030006005000006803105903422140c1d80e10381c00c0d00c3c040c5400600b510000941440c0c007a000340312803103a0821519141c010f01e007a400680c0d14507485074440718901c52030282608401c000a40c0014011103100743e944c2c0641c180d007241080701602c00c0e84584e0709030042c400000c29400c444100d1019400c1040007000420031003c0c00c10340d900150560099000c580342d210311600305855941180b502c800c1e4207403c040e030014460758a143c407045a03105032031405900b03c0c5400307041c0c03500207013074010303016034444100c031300f154040e960440707140d44103403a00f9800f1544a956014240222948078444454585440701d000021030f1011f24014201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 246076915 1250 246075665 246075733
    0x80c0a1508012705090703231005041a04240204050d060c020330010f0509360f15090a080d1806050709050102010e0c1207090e 56
    0x800000404003a0140688000c2c070410080c50f092180e4036039006000c0030400d402c00d0005162000c00155141142d21040d64259222898034000c09042c00c080c200c501c100c980903104c0c05020300b000034060000900119000007141c1048a0f10790000800c850040e07206507100601400450f940e0f00d041503100109144d1b8510420080110350b43e03001c0d01e150219803060003c52500c0ea10581642903005101a02441c3d0040d0222a42d250703042c507088030b240c4491110802000d13601c89010000a1035a4051550011242c2011508502c80004002940a19014030300050a0541180211100d80c1d440c103a296074007403809800c59100034008003402c5022032200c0071540ca414003c2a40e11042040c0c007502e004070000d0031400c0f0178076a801400340e03c446a1000e28120b2118a008002800b08803656000240c482c10089410740c0b06010b503882000f8000c0080072141044020801c903003500350348904a0744180100029011800d000e00d001d11528540508401c000d00440142072664484c2004a6540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 246078165 1250 246076915 246076949
    0x60e010e06220c090219020f060709060309060b060a0c02010e030d0c0201080a14041a100b030c0f210f090d080735390c0a0804080c0a 59
    0x2a00712982d840380204901c84400303462090800b100c00042c2a00b14110007800080d415246444004111401140c643d007220018958580e101e6218034040e0f40100010711080c00030098079219400901c08540100c1c4000380c156150323400107265901180e1248041800c541c0042c040d5038011072410403c10060700940100c0300942c1c4000c04110040d90024103002c041004108440000d905c403074a905030020941c13506040c2410702d049a01486d008503402ca005000000b001c0b002c6410340d0404a90007007440343d0a5468040d11640540c00c404ae11342c1c4800014011070414000040d20850a0200b01c043c24500f81415266a01d55440081c20a0301d180d00c254100625103034401c4020b64082c0f11468042c021011111110f000c83e401d46a8054406403000a10f0100348941003581c7d00405042c07001000b003004030003d0404000200c25018005c001c52040252051041e10080c80320310078100036540203000d10b5803140819085908107092a0b8026880c222642c1015039554015181321020007006a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 246079415 1250 246078165 246078181
    0xb03061506070302100e0601030b07050a0e011b020a0306020301050f0303030f130c030206030a1b0309020d020d030215090607030b04110304020d020f0d031205010b040f03032a060e010e06 82
    0x8440c09000c68000c0000040c003006051080c400ca110b10f200e955001c0c8070041c0482c4085989071400e0006466841541c3d0100300854040c0c01110a4110340c0d40b1201a280c2c80a00191001042c45248501c940851070b1036000507624084044040c0d885501d0050f240e504103001d11000502490318280a544100309004180c10040100c0b9030102a000c130341c10140c003c51070050801c608550000b1340045010091103800c1c481c0740c100c041000078182100fa4090f1131000c080b01500d1440a0181d040b00d170030400c000c0981031500390414814042d00482d0615400c4034405507a102c82112031900c6504010140308680c1c0e81401802442981100c00f031082d1021600c91140510010344024070562124010104540b034004a19000081c010451500c0700c2582c20003804202ca0365800758091880c05001240c030b10f01e0041a0b800b603c5020300c05550440c21940d00ba00d107101c41c1143c800452000e24a00c200c40e04c251070b00280318500c00c45010610005c0c0841e95400e4840c0307120280c005030000e0341006102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 246080665 1250 246079415 246079441
    0x3020a05072616020f0103060510050c1518100501050f19090f06030b1003030503072a06063807020d0501020a0e030d05041a0f1b010c030b0306 63
    0x50790440c0e40305540c2c1e1820302104094200b051582c802c0e400700400c51036a01007140030a000154000d40c1c401501c001130b800114111000e500034568030030b03440315007402d6444c0300c0d0025107403002d034544c2120b109020700549009100b0044070001010030884811704680081480a03641c0407900740014002c0d5410400050541c804040c102c43c001d40c0340c82441c0800c2125104504002c00081c182003014508860b0018054030701404240e0b1070700d0100000c00c0c1d144c0003214220003240d0b055038849013507848828003140c0e213900801c10b2581004a101210502030340c290088494270780310744e400084661405491030140780c8520242c044060144c10b002c660001c00d80702e0341c0b014200203010250344003460320004020495000c0060025171010030b41101258000c03103d8080310744101d0443e040c0c0380c90702e82c08803200e2190b805210481440d0148405005000c0000750094000380c0f0392041c2400c0780f5500d40044a0140040a078407691140b24443c0c01c0c64040c0b10f40c0c45400403d5015244e84d00c1d00e21460f5001c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 246081915 1250 246080665 246080677
    0x512010b030a060e0c0a032609090c0310030c0902041505031006110709050901050702010612052802030a120908030403020604030210030b1c0b0f070e010804020307080712110103020a05 81
    0x20b0f064450082800d0010140003201440301c00810046002c0c0d2070382003542201c96002800500d40d000c201405460094060a4517550b4034014843d000d503030707142480b40380207800c06424900c079003200180220010351150303012005040a4a401a11940390100500c000e000700040c407410f00c4001c000388600c0001052443e01a03d0180c18a5030300340d03c403114154075004040e0711122459290805001d41c822064101034060181390b8003d0150944070202490300c007014110050240d840405400400c5c20710315000c450720104c10700350300741c811310305c0c2c002c2800c042410a013140c042100b414000c0b2070682001040018024000085080c01c2c103560109400e8031687c00041c0c410040801d188400174402e07040380c507507134401500a40c4201c048081441070580035034000c8400310500070010b406070b1510401c4512074000340d07507001d5040e08010010b5824a0001d00141e8241c00344107400300c0c03010b0381003201000034071740003211688441d8181170050019000078005810140104084030420f90f102d0b081e40e403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 246083165 1250 246081915 246081923
    0x90b1803090d420c121a04090f0501060b03070f120906090f03031406151606020a57020316090b0301060513110714070512010b030a 58
    0x1c00d061007410004842070300c50b80e0310f100703104111442c1d209000004a0090000014001c03a400d00e102060f1400c0585442030350000006101035280c00e00001c00d83c0080803411440b8055108101100d4003203801d641c0d05000270341c2e803500c0303103207484007001000d00c58172004014004020b8154241900001d00c5610402118001c02c01440520388403003d1907405480f581e03a02a00c20041d40001e45009208425059010740100740b80400d110844a06c0181140c0310340c01c0108113420a0540b040c21152980080c890a40c5500382c003006800080e64610080050f081030303481c0c40c2c280e40c1000c4103010462100031845030a840d1315801a21442e11110141c107044035841c050115803d85222034034214000003031000e5807501c00c0c072440500081e507583c2ca0100b034030382d5034105004500455081c5400d940c064445c0b2a00b00050140c0e40c88801c0b031590121520703104000e14a4034001d4540c49034142000309134403074403003500302c264108110b2508011072403079100c5402c000e110105c0d902c0c002030b407201030900000d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 246084415 1250 246083165 246083179
    0x403021207051c0f0809030403020f09270606040e1c0f050d09080301061e02070614040b0417060f090d12020c0d020d1209020906190803030406090b180309 68
    0x1808015080c8072034681e01164080e942d840070a100f00060a014032404039002085402021030109400072084505580c2c01031314001283c00480203100c0004402400c08402d10f1441071041c12f20420034030054200c4c030038000100070904001040004844417038030b0400302d581c4841454200340590128182a030311540c1000050403c03c5001514540300d00d1420f000c1c02854050013500308134100000e10b040e22400d69078580082100d9240796802d0001418140c0580d000601c01c002d0325118150328800c6441050200341015a1220b80162a401c15085400c07464600f14514100000c104160b55014181d96041c0c041c60130505c00164036a0101450308081000c04c4520000d0b0649035011507002c0a10f44048503644204090000c0d180c01904414000140140724610b2404940c3d00401c00110b40050024240c4e450300c604000c3c40244a5010f100c4415100100155941082c405588a40d0203810702298240281c80c1824140380c004019600c2400c0005800302000f5001003030356011082941c1c18 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 246085665 1250 246084415 246084427
    0x20a0510030b060a0f090605030c0d0b060903030c010501050306060105250618060b13061512060e0c030f10060c080304110a0605090a21020d0305070210031a040504030212 75
    0x490260242082e07168114500058920071140c0c00341503803500791815500c035260551540d108456902c07080e948890240403c0c03280b010340c0c03000e0382d10507503c1010007483d0520b802c01c0701c008641147c1041405000c541d544074010401c0e803c06000c07117680003200740b810a10700107544100c0f6600c481070340c884042688003200100c0c2003102560010f405242c55540002603030b403540c905880035040750420701d40582c0c01510042050310f00e0b409100c0540e0a4140386004010700e942d000c403940e0203240b520409040c0c480000180c003524002038580a10168108150b980ca460a6800701d521f201510754003410120301c0c4100034040d44403010004150b4071440f8165241c0b41e43c10300c2104162445032440d404101c4c0c6500080301c2e50404010701d46050300f5100b821711030b640c6032a02880e4024007500804c2004000b2030b80ca005151a0030f40101d03c0d40709050032401c01c0120b8020540e02d005d02c3c40d001000c04c0d90b942941c001022407903101d51010108a40502407881d09035002515803041d41c80c050b04002001c075030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 246086915 1250 246085665 246085667
    0x2070605070314030a0f241512060602030309071401020c060a0c060c0203040501020c0d1e0206070515060406050402030702070b1303150903111c0f031e0b0f0d020a0510 74
    0x607001c0795000240d515202e040000207031700104903039003440804c1c0345081c0d90140c90061500c05103c440d190490700b64201c81c6031105238112041992150030400840603115500d01c4110701c1120003401c03682e4015a200e02e40f10440c0c5140c13040a030000e0740c0e082d2147e401d0f620260717030015040c046104140c0d072440d00c0d141200016206c01c8510780300180043d080000440c4030541c008050003c03240240e08445a2494103424000420441c460141502c180b05501d480c01003c0356186001c0984043c1000c1e24100300d075103810b41801c0444a100001203d840c2c10310000b13181038025503010304403c071021461070800141c0690303030700110320402040000118040c0c8030031102d50300d600001c5030021031440040c40b058484000511804104402042e1b43c404c48980e0070310002010600c89480050b1132020300c00c2d5030016610b061000701850b0030907480e41541c11012244842071030440c11003c4002c526410808101301401c1403101c0004c2c003c940f58059203015a030340c084c40c00308641c2c06444210246000310b0f4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 246088165 1250 246086915 246086927
    0x5030c0d0201050c1c020f0d181101090305060604050c1b06072607111f0203040c0b07020d030806031603050d020d02060c071401020415080a0c080403050a1b05060108010f06080c01020706050703 85
    0x461042c6451701c150070342275084034080340c0ca81a109180ca01d00a050340310047d19004214000540030303a002000080070b07404c1035448250000c54003907040703042c03880c142c0d110a0a540614018801da070030600a00400c15000342103008050f26803500d80b2108106a0150400d10500a008504005040190720003040c0188410f0040281001c90003550035250f404d0940a90700550f0101c1d00c6064444000070701c90880000c0c0c47c1d00e80c1e4000c01000b4800d0342620219244103000e485c0a0340b501a00c010602da03070704034808200065110f40068000400140000380c01d001c15020110191740154003007025501c1d0300d90849400544c0850301480a13840c45a000c1c1c020b0095410003440310001802c1c6803201c68000c01c100b031059001c030300248000c2d042e02e04d080ba80c080d01554000c01042051042100e803d002c2c6190b00e542d40c0090215146040007070b02c903146441820380c0112002e035950b010890440712940203003805403210078018118040d80c0b400003950b900c95407043e40108070001c103601040602c030307107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 246089415 1250 246088165 246088177
    0x30c020d02040e0c0f0a030218040303060503011803020105060102060f010b0c0f030c06240919020c010504080c010c0e0f0111151906081605061605030c0d0201050c1c020f 75
    0x10b401040203580105640d5030b00d00b503007001c00303109031485040f2a400345800c580c00d205413a4083c00b00300d041c20030b10000fa03002c0d9102034412810b05407254030114560b00c0074840c0860704060407041480710899410045d0031200701800aa046400072403c2022808010704060304450f281c848096075005140611401e00614a07e0b45809002c005164071042d403001400b80d0084c124508500800e84c0c114001604407040c100085820000d41000506240034040031001c1d4200149400341c07414511030500c1e42101ca00302c078122035203080810f818606c00024403980d10214114209512110700722000140501000072982d41045600700c1c00f1030078103905000010381d403030300c0c500c101c0c0031400d001803485064001d00f01803030741e503529002001843c03a900040c00803052103503401c2d007410070b420700e418840e040d48072030b203606240000c4011000c0060000c200400c46101c0c1640500300ca40703841d0000070b0940314003030b28001c1e19401c10311008800304e581c0d800385008840d0408006035966120f132502c5015000700c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 246090665 1250 246089415 246089419
    0x30a09060501141507050705091503030a180906080c04050c0c1203060102210d2403080301090b060307140a021207050a030807020f07050f0d020603010b0a0f020303040b04030c020d02 80
    0x718000003001c2d08440440e86403600112440c6800450240e10b08030a80100e440250569000a401300031504081800d07a81208819094a8108042002180c59580400000400140001e509070001041d0200d8030015005040c1c0600c0410300e8000c0040d90340a019008178807580e0f40b400428411485c04007107400a00c14a815207005140c0300103000041e40003168000d0150180d50b03407248201c418489502e01a16240c0d0007039080041c01018107000345964003005181000c81240030448180685d109002076200c1c0403035a6803581016409001d5801000041c1d020f00b0342402070020207904059181c50f61032117140c0960b1605034800b4200c2c0340c4000f02d410300807149030006d005024030001150010b071082c01790315009804e032070319070080340d6070741c0ca00341410207a400c10107080c40185860307a6424903011004240144406082d00040c285078020780c0044c101c5140050005910368002002501c103a410b03001841c290314140e1100502d45800500040030070074506041d00071950f40341040e0380394a0300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 246091915 1250 246090665 246090671
    0xa03030b0f0d0c0e0a0c080403080601200703020a08012c1006030f050c10020304121a0a021b121b0f0610261203180114040c1415030a0906 61
    0x45090031500803076107008080300e503404c0c000066100942d500030941546a550344003800740c5d40c1c5440446240030043c04143c104041295601030090072f1040f41c41c02444010040c0c11002c0c55403040064400c4180d00604190b41403544405e01c04004100702048688000e10750101c600c00c100c40c4900300210441801c20303242c5040707000310511811003000080940325200b110400400c83c002c20651150000441c40103a03c100010b114400c5000d041d800c07914440c21a0384101603501044444143c0210b81c44040380390b0204400c00740f0400071001418a411050107060750600b5900d01342c00c2392140924070b440d50800c049000707a04034410080300c5582c1e8645002d403911170510525015818400d407060850260400c01c0041c403410a071030140c0c0c03084211000800e000c074588012017010b80c00062400e40040101080408404402e011b03000b413400002e111880a4545483c1c1200145030941007c00c1107100044004002c1d12000c084401400d04000960345950752100d200d005403d8640c0000c1070710b81 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 246093165 1250 246091915 246091939
    0xc0207150315080a11041a04320112020120010510030203010c0f02061909080301091e0209031e1f020405030601060206160c020a0e01080607021c020a03030b0f 70
    0x1906500c400c8044140440c011056591503101944d2140916406807040b8400da043d9101c6160a0b40702500021f041101d8064481c07031040040d003110310545070200c18000131501c5a09001d02485410604040010080c05650416169240c81941030304000d040c40300d210301c6160901c0030142c3c3c0304400c4502d1402489603140c821010655506544012401703582040e02140c14140100c18054007017406900911071682c0b103024000c401002c0015032031101d5515004000800c0b82c0e00f0086020302031480010400e02000e4001a1400901c8480500c0061060007803541694020494580480d6149c20000d02c2c46003041c0300900341140b1203070704074082035481c520b40040e12003074018000311041102a2a41a81c0c0c443c0103130307115130003100c1c51b49400b550880c03982d04040c0100c20300000140043c103810381564841c0240000800c007a0090301003503010804000b2102c0d4104050328045402d541e55403c04182d8510103582c51002035401801c0c10b4481c40600000c1d16612000780200ca0001d02c5190150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 246094415 1250 246093165 246093167
    0x30102041503150906180f020d1407020d0905013e0a0b0105040c1b0c0801020d05090d020d140d1128090509070c0f050f0d090504140a0c020715 63
    0x82209400072103c5408400243c00e90080c4500703c11074504840d007581050440034034100610304014841c541580c01c0c0a4400000524071400a00000542c012040c5051254020b450400da480d24181003010241c2c051166903800300c0c1c0702240d500441403146940f0303a032050900030205000c42201d81080517250303681c80d0312800954482114084c41c803407403039030341c03140140010340c1c1c411100080891719100000d00c0c00010510031400c0e41c0d0240c001014402d443da010142680c1c01091100b0f0269203480c1404035a0400740b0031500c0240007070000f03000c0c0281c4100c014000d5584000b440340380c2d410200b0781d042d500719141c02814240141420490b035039090004032a40039903942000c01105e6046908640c882d6015410002c00e494004115062550310024102c0e09030341114812140c1114903002900050380c104405400c400081019281d80340324144014414442e6602c058842e5052000e803c01d1440411005030b00035140c10000325045481e00320030ba00d480543e503c50441203503118042107242d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 246095665 1250 246094415 246094421
    0x504081605013e03011401050f12072c2b050a3212070c030b1006110309090402090621030d111804050601030f020f0c0c030105041709030102041503 65
    0x2500c442e292400311460b4800c0c0c0f2050078007090003134a00c001000342d030340c0c8132641c059400380c40000d5800c10b0384d500d808400b40340101014029940314001c903103d2214003142d050642c80d4885131224080e000c15142c07074482c000420034600c0504810342c4051110842e1141101d40c11513140194010040b1359107107400340382c001944050b880e2606445829480310300000b03000c49c1c00140450300040010020b00c040b10b4241951580b042ea011520362060308400000140c0d01c83d14a482041221071043c01c4600c2c0c03940144c000c4400d51030484139070708108005003480d40c40c405419006601074030221240e03640d40c40840c0d11148400b00c0100f5042440100c0440e0b40d0b0000001d00d80580c003440c041c403c088927068034090030b008850f010001441199604409070800d54415903101805150101c0ea81e05c00800c11070032a8003100c28864140302c00100c5500c450010080b0030840c0d10168000c02c0a0316185d244e02c42081940c110410043c000001e0240c841e5801f501660301030f2013008240101c21008140140c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 246096915 1250 246095665 246095741
    0x110a09180b01050103150315020904050112030e0105160f021302161202031e0c16060201060801060b0301080717150a090b070c03050a0f02070f15090801050408160501 73
    0x28041840c0000704055110340500280c0d00000c084406d8407d003940d0b250040310302c60740d4031390401c15400d100307458807540d880c080d1070300900946200300100d020600f80103101100105555040c440b007000200e404924200840f4450340c0c022007643e045403450b00c0043d2a03505203d020403546400031942d02a01d5000701007220b002c91264504e11000650b11300166201c0c0142d920903c080e8060a10401400840c440106000000501502c07071000620501505c88012500302d00c00507952001d061080010900c14007010b02510000f6034155850503005903907a4640740a007015014000b02e0386241c80c0410096020b2841c0d031031b0a29a03e518001d40440c0040152800c1500c2095940006c50f001500902040400c180c143c6e603a00d03d055003810041c0c502d0903816914908500c0385200000f202040742404101802060f003400301c80d00883d40000b00b9460480d040b88225916000600c800500a00111400b0101c60200c4810000c0303103040007070040c0004402c00805001c8a80718000d00c071900c21041c2c00d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 246098165 1250 246096915 246096923
    0x30905091e070509030c09090105090c1203091909020304050303061512163509120405100504050d06050601030e010231080d0c0c14010507110a0918 65
    0x40346554100e180074610445081000381000e156020903042d52058004001501020f000c60300094002c0021610703040b030890340700c151a5503603014002054020b00c110b1f107049074110307001c0f03070b00884440c500c030740f64820316408178859410074000d221034240405e41c14000380340180c4115200d03c1c180c1003c0e5107903441142c208e03200399400c1405107958042c00094400814613101440c074942c2c0d481c281d1400700000c9104400520145840800d0360010007400c0030200502c4400d60710503100f51644117500c41c50054014030716900091080d850f040c1260781554104c890444441c0485c8080c1c800c10b891030b21403600a6500036411000d904240a060b401481c0900c500b84c0c0c0070025170b1100c0b00c80c1f50807400340342c03620b84010303550700303c400c030242441100c00280071100041100305941d20315045107821486103c19012400b00301080742480b02c00c0c130602c0000c05000d800840703001e2480000030007a1040f803a000b0a120030510030030350780b5154480743e4005000380c15010400b0602000300f800b03c010300044122 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 246099415 1250 246098165 246098179
    0x2180a061214010b0702040e10090302150c03160302340c1a0a0c02130e07030b0604020a05030f090f0106181b200316080301050108160206012601020403030905 70
    0x6202c481121010b60488151001031410001030b9402c00c070191650f9145044a4031961280c011501024414043c459101c0e030010011507000815801d907418008000420780d006c00c1c402c01c515000340c41c031700354642c0301d180c90300680c1c2d1844074a04946d102145410045228a03112400720340b205480342483c0101d018521604400d40e50390300340f20070080c2d004081e00c081c2c0d5007801020307040b501035031469090070b100400014030820700102c280704681d045081d60496900050301041407001c0c40840d40c0c0c103e0030680c0d080d881e00030040c00c040c2103884060010320420141038000303508060203003c40e40e1110026402404a0755a54a207500b2041510340344142051a1003050005240c030f848000c0040c004685400040b403101c4290f0003a00070707201d00314404501007044509a881c61043e040051107125881d1280c41e941050001084148020843c3d203c02e0b110142804406070001f61490441d4040d250302d4403549a1011003081088004e1855549503001090120405422181e42c2c415160295010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 246100665 1250 246099415 246099431
    0x60b070c03060e060108030a0f120f0605010807020a03050304120c050d02030a141305010e0a0306150315090b0c0a03091b090c2606150a020a0606090e03040902180a0612 74
    0x142c0e0300d51001b0300c6100201d500c20801214514010486840c4040c224240244100e40b101102c80985a0310a15401015600c0758188042e41c0c2118107607802001c2c51000384002034040c0c0d8007419920000d00058000c540c4d41644141503841088200900b80c0d004058a101082026019680f074100004600c040b903c007800380300c0c000b8420005eaa0001c210418542000ea01d01001960003c001d050070030740100d000d80000c0040b07420740c001c00280c0008044072407001807860908100b11107d210042c052541401e80501c04642203c141c0b642000440008070f680b40d00c1d01c002540205a185001000035004074219a0403141c404840e03400c99003210703400e010340d00e51144102d94410b44c85d0780641030914000110320b004a10908940c0d4890005440740001c070480d0b001358a250f801142e06071006a200900034020042d441c00b403c00246800c03072081c404035013880c0307205450b40110301a0041065012031291400092f4860303540111b0005841030000d02c0e1588001485403080300c0e0408007440c101040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 246101915 1250 246100665 246100691
    0x71b060801080a050601090f1104081b010c0f03030f0e0714030613170705010f0f0b0a080c03030406050903011404050303160504061209020f04020a090305150405120d060b070c0306 79
    0x403d10b15034054080c0982d60b082c9044c0130020b05d080080c2e05011551012241c0707035000401d00070000340c590038004160000c440758042c08040e190300c40c4c032810022000c041e9000110131b1703064000641e5160401081a9001180c080001c1c902c1e440d19070b4240c03094070400524030781c0400c02580002400d80a0310b105a46a080286e46400d801c40010f161384402d66010715411b07512805441c8040c82040082010b24620030b44000343c5010800c4413007580e5980081c100d0514006006500402a5101801c0b5513070031600000d0b1280181e03c0b500781480400140141655401e5100e650714440c00365060700707503040c03d050103540c03900200c4070344800c500e80c0745040b101d43d40140240d40c01c680e00350340c0d1100c010002c2078640002c1c2c04105812030300044408110400c50fa601e0000d0700d620010b07a0350340c1003070034070394200710b13151820812001d5881e0f00c0303034000d00c0040340d4042114400c4c0f100b0102a1a0760f042c0201d130410007000c1a500411141e00301207214800c21404140d8102100d000c1c010901100c400e54034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 246103165 1250 246101915 246101923
    0x10509040f170702030d110c1509130f0f0203010e07090806130203030724060f050a050d0c0306020c060604060e0907230a030602191809020f071b06080108 68
    0x200582040414a040c0c0005581865000b00411086019a00300009540401c0ca40703a0301d40c0744280400c4094001e069800c008016000303c0100c105c48140050040c00a0b020301840384010032801040c0c1c40361280c0102165411070200c0d010340701810480b54083e808861300a4100303010311024141c0180c040740c2c0365842800300c481038560150103400030340c50780b40f868803a02e0b120f0301003241c16010500074100030503030412844040089400802c42c00c2c48078a52200c08860054202c19005e031080c0300140039070b868248242003038a80c25036010f42c3c0c0f00898200b2030080f0000381d10080146c1e000044161383d81c40042103140c0205419241401314944a00d800011240101c40035452503001a808014800400c40b20603040040f080803aa45048054041101c4c45101d803c1552926000105640c1c0627010b90460392088a461900074001a42c054440040c0303003a9100b0300b46c40c140c0201d114801400020211a490380d481140001d220800c140f0800705031609100307042c04242c001000148078a0081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 246104415 1250 246103165 246103171
    0x9060801080312041a04050c1302120a020a03020f0f0d050a0506031b27090f0105010807030f02012109060e120703120902091e0702030f120901240806010509 69
    0x1002c1c60502d411001071945070840108180d07107a0003000d21024206404901583c0500e00850150500b0303c0300d0418001411190a0140300d480d1040040c0003803181e42d80c40c22600725459180141e40c07640b100b40120003a02418580b000d20150000c0c101042110181c000c080c4910759500138803490351008940c20840300121122505900300c030b0408098100010464a40c00c4001040002c1c0200c1400721a403881101c0c4c074000d01d0300e4100340148000c101007007025071481d1201038028000766042c00398650700e8400030700c401001100c460f040c240441e0301071840c0070311407144490540301c0200041445800f07440d640c101654a43d2528000d140301032800709224009000b01c1d03041c6450b1849a9504807088140f124a118a0990310b0340c01000590303c013030301240640e030320780b000c0380d80440c0c5802030852a0802801d800203561007007203132103d11803000781561540c00d401048840c6555443d080d403805080c82a030b50262030009458000740414000708460107407250311044401c185c0c0c07070f4000d20007141826 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 246105665 1250 246104415 246104429
    0x7060203040e24010503041b12020312040311060a140f180a060e01051309050108060619032f040509070617040209010527090c100203120f060d0212030403020109060801 74
    0x61007140c030f1603500910046030468420306020302400b00d108040303501403615800542c0d81100e4884030b4019443d0400c2400ca20f090048400ca2a241c82d43d40c032241d134540d8215100d8010341000c1082540703a402100c00c0d200d5104214041503a600690b8241760307066110298091015880120b0506982410740d0014140c5190340c440c10b0100c6070b0b00f001550b01d90003a4041006c0d5a22315070340420740390140c0c001c1a000300600402000b00c2d0900a0403c058000d0704850761003132881f000b90410200700901201445a1803014981403544c1001c00c031185103208c1d240e403070394206040c001840f001060004660b07007210700640d649105d540c0c2c401a109511902500d002e0740c040d21400041c0700d1362410b52070084030340041c002d02050207030b40c0403030f004441d100440380c460f115000403604081c2d605080d15600b071503080d01d1014500d0304a5444500504400c0640008040d08801c00009d1480d196024940200b80c1c004190350000c0070030321200ca550341d000b07000481c001117110200143e0280122000341c140c07810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 246106915 1250 246105665 246105721
    0x80d09091506031d030d141308040e0c0403051c0305070219060c02010204080a0b0a060605090108240d081b01050106050f07110402040b0306030717030702040b06090307060203040e 79
    0x2d0304204901a02d0304811201c1c14400050015050380410402406801503003040482c0180300340c0718000080000418001c00718010020350400640b00800310303001d480400700e4804d03a544174030308a03581d85d0003103400040561140349248100c0c214264102820501113581c2801f083c0d4446404a84034100c8020f5a80d0702410300c0b41c01c40001b01d01390002142202103100042c10180c0d10018145001c25810068410804890500c8000380b041d0007814043d03d03841c10094900000c2200017011040000c000070382c2901c2c40403148c0400c002076a25010100300040a81a02c10103c0c1804c0a2030b074844ca0344003000000e04076840240c848180215030484205858490509011078a002d001d03520061040391031480c4090071000d03d5880380301401c080c005038851180c4a1411605040c42c19607190082246690006003403081c0e80301c00011070344010380c10358001c00c0c1968858041052801442156036060084040200d0040d074000050821100741c5269225907413114000c02000c0690580c0c80215098 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 246108165 1250 246106915 246106919
    0xc09080a0f021206160314041a0901060b37050906030405010b04090c0314060103212001050702120903030324030a03081609050f090402030a0507080d090915 69
    0x20180d04208074a5002030682a50300340000c000c5410300400703e4440d09280b85c460f540b440d80340e50502c94100000030310340001350b00c5c0c2090b84404a40c60951555840405c5500d40014103841c0b007034020800801c0740314a441d8881000d20305407100d110141c2105001e454100448551010b0400d001800030342c02038440c50311302502c02e8184001580300a005031082c0d9219562070b1001d8445215000883e805003100320302950a600e4034034031040302da0032030003010340c068001400441d9001e080d030689405001c400e0800c64143c0b02054030500d4401c01c1c540c41c0354800300c00400d50b59a064025030300c03900380c5500b9900000d440e6800286d00c2c3c01622501d90f016801440003652040c0005815100d105142c0303403101c442c4445100107031410740c1140040780020f00440a001c4071180055078042400070909081d440681450003080e2415040190319204200c0440414255101807044c00142c903000002d407406561200d440b90b0307440840700e400d1030019100300c10025a84495210718071035508007116040550b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 246109415 1250 246108165 246108173
    0x5121603080a02030403170d1d07090f20071205040e04030807031d0d0f02010c0507020603100302130b0916021902030316060b040c0203040e0415091a04060c09080a 72
    0x9000b505960b001e61008110100c0840d22186030340a1007400601e0f510b03500c0451101c00400d0b0b903c08a0005030716010420071160710403002c80c0d00d01c2590542403002070004030600301e0303001905054007101281c0329200484140f00c00d8030300042101600803118007180350362004089640d071040d031198a16413200c0b02c2c040f8002920416405402450f9850080b0700c40e003400300b12300003400e0b040f246e0302c0141cbe1020050414960f0006504141110140002c101044030303085e0150003441000d81c0244a207a0004c00184420b2451569034007454014049001300c880c0c0d5a0440c0040124981051007684400002513103e80c0c5400d00b104034103034560281c4612211460300c0314203580d9521049074903000601907003089007036117454241218040c00c801f05040c0260f0382131000712041c20907500215041004284a00801c0c500f08a8015620681c04800c401e0450003c2d801010100b2006241036030001050350311a42c2500042d00860250008201104030a1401d030f8281d803281c4555002c980014100401003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 246110665 1250 246109415 246109417
    0x1b1206010e0c131707060f0c0b0a1104030c0603050609071d01020a0b07270605120c0f0a050409140108060106030f0b03030705060121030905091306090503040512160308 74
    0x8030a0184141019a0740216001c54103c1c2c0c1c10101384400e104c4401c011840c010080080246010b00300722500400030309004041c0300548801a02400030310010030203600c0c2613440090034100d50300307506480d95200c2c03425044d941214405e03a00002d0034200031071024075200c030100340104510303100e282c9a0f5203507c01c1b100303d030080b403114241903005288400006c201000e60321480344842da0345104640c0366040e001e6900d610b0380c6000059582c012902841240e4001d4100d500b80ca4540741d01d1029a51107284400746442071500c042c2c070a40000c02c09981141d0480c0160080d20350000e02032283d080c45a200c25448402403042d00810b6101c40010040b03e07010354441544101e80000c0407521020140210b03155500800c403c6a03168004401040034403828150a030341e03d002490100181c00316900d00516034211030103010700c191900300100303a41c550501511154690300040900140d90241081034807600a441154083d02c110300d140d1944102c081081c124101d03030b07100080c2c4002c0c25520f4228203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 246111915 1250 246110665 246110671
    0x3100c020c10034208030f25030306140609010f1d0405040c031205161b08060a0f050610090306020904020919030510020a080f0403030f0e1b1206010e 66
    0x181960f8000f205800c180500e1040402480307051000d09440f64200071104c01440103d182100f5500d68005000003900401114801d008500010b500c03140d690796480418012070075090a4000000c41207000c2641581120080315030013241050700742d1012090092034881c08a01300d00050614409000c1039005540088880b982030314100e0402c84200d01050031640c0c1504c090f102101078200401c10840d490b050342c4c80c3d180080c40c0c81800d155231140d5108001d140690300504034603d44200c0c4a501d468241220002c050441c100d90303480c02c05c403920100074145141005071140c00c0400040160420f01c0707a81800301410b40d40c0c4002249183c460700004c1d000440220b92094003040200026a51074010360245540458822071036807031450264030706502404a40311007801400042c0140d07804c0484164001c95043e04028075a4580c034048009082c0312040007019880c010500c4145207000a46244489684e0600c1e0700c00c140f05020000203460702c0590581071382c0b101c0c00610000c8213464540350 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 246113165 1250 246111915 246111917
    0xc0604060e0c0d0b13080d0c02030706063201020a0209040609030e010504050d0303050c040b19030515062b06140a05040e1f0b15180405150402090d0203150603100c020c10 75
    0x10500100c46034010942e423582070301200603403002ca5100240289449024000c003d680581084a5004c0c3c010207103c0700c40b030b400c41c190003105000768036407a4002c0c007802c80034950051000e039452070280303081c0000301302800f0142c00145417034209080550103241250b083d079074002c3c11038003541e10301d9404a024203001841d90342e5800040c00005004403840c000f40000d0200c10002001814a12400604880004001d5955450102c5503040c660321004100d4031001c5000140c4007203020300c4c0c04040c08076000b0030041c0c4403052401000241051001000c8240c008080356840c1e241ca0b0b441c020841500c1e12090840c1290b0030074951a01240380c3c0d00d245580c2036131419408134944940c0800187c01d040c0f5a0303042c041c00724001400300b40061001401101d03000044600300058102003018030a004840240316000d00d900280d002a580d603420b0410f040103a0040c11a1070a0318201001c004a21066880070300030b1084a00c1d0701f90110444c000c0c503004c126207034014241190443e0821a140701d40002d0b01c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 246114415 1250 246113165 246113167
    0x906020c101110020406080c070f0807020105070b100f050103151e1206050a06091401090209060408011a0108091b060d0e010509060709170601030f080c0604060e0c0d0b1308 76
    0x32222018041c10f03c41d10302c800700041c0c455103401c1014044450003040c00640400030003a440c0060f41011028070080d40108405854454074401a01c880c800d50b00060480b60b100e10410041c04024a01402616041da0f0b0300f034421580d84005400399200c0051500400300403450134031035040705070124020b0b0242d00a50b0105159500611111503249040075070f030507520358003040100e880e5401124014034000c242005240120800110a180180500307410650002078110030703a42c42500742e40280038a03100810010342d04071445028046c1c05101c01d4080342c9114006111401d0200d0b03140b00c500349070764031103522000b01070400c540c0b60300c40a09100d5155850000b040100424440c051160315100020320043c18102005440344400d076000321007082100410500007040400d44504599020303000150004562030010a68041d6104000721441544108000d20600740c002035010b582c0e0390141c0711100c00034020702c0302c07010f0713803a40140110404c0804503d1a90218164002e054001c01c00c0c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 246115665 1250 246114415 246114437
    0x23901060f0e0c0a03060b0304030203030f0705030105062b0e0a05010f2d15080105090c060c030a1103040803030705031008030a0516140105100603050a1812180b03090105070906020c10 81
    0x108046230400d0303609400507031003c4100160700701c540e0301054010026060186c21503144c100051214880e040602071201740c120034810b00744041541e4010481d800e4201846091206210385948255140d0306440b070b0360070a100c510611a480c07050508080d13109c100e8420000304014501481a050044580f60b140d03590041c1d10310400d141546406401c00800110710b9042c4001003a241c2031011281034401c0c4000c212006009400000f00d0300d104506040102144041e01c6460b4214090781d4812136090200000300030307a83d6840401144034201d8104d000e0601030f1100d90079542c9001341c18041c400b0440030800c624818983e49120400305220f60030398010658214038460035200143c07020441d50108031418050b01350980140c1d907004e051628100180b00100f04044481064205c0c00342200e500440c0040e841131069a00d45e04503030310800705014941c0e85141c1c0c5407840d40304540300d581a501e0300700850080e81c440c0400c02d04070360040d402019000740c81000c204185c0555880081808407050003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 246116915 1250 246115665 246115679
    0x30905190522050103080403020108090d080615070f0305040e0901020c07030209060d05010905030318010b0307120c031a01090b030f120f1c0e070806041203023901060f0e0c0a0306 79
    0x7000c4c081d62052210035291807a510024083c180301a040c03920344c2e001400a14a195400391006034460f0b0b0444091029024000040d40c052250310000380c41185031108007401c1c19007200040c002c0354000880300007580d40c0c004115080f8061005020155042103030200098030700b4080b0781d80c201d1070060170302c40c510f940355030b03568211034511208407074903080403081190150202c20364480c4401100028080c0c2c10001c00000c0d250903142c0940d044050113054004180701c0920340c0f01c0b01079503014590211640a448417029558824891b2104a41c00c0541445041c00c020900e8103042c080341c0c005102049040000203515000728030503030302c1504144415440e03940000849030700041d80540000d4030522a40c040c80c18082650014070b50f690ac600d041c0701c002032040d0029803070040a0b10700142c43d0000344200003542d00e8170218140d65010285204e034032145080a00103491a50000200840ca955620315001000c03580700c1d03514000d03642800104036220003001406030140f07525002032742940300c1c91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 246118165 1250 246116915 246116921
    0x1081f020d060815010f0906030203030d110c0615030601091a1003020f220510020607030f060f14210a021c050106031b120809121f0207030905190522 66
    0x302074551303c081000100501d44030303040c00201800f41c0840500c0780da070440d00400d56922070f01d08030342005659000010b41d00c9460314152172184104509840043c14101d664500c41d542d24402c881c424000ca200006800300907110700803641c0510002c8074501c4800304100100c116029400c541490380030003440c14585001030060400c5142010030304100603d40e10346101d00345d0103801050041115080d01101c0d19000544580d0004040c80e011512640348400c020240445e03520204a2240c1c90002094800d54290032a05000042c1c1d28140749034151394102c0c8211006a844201ca9080b0703d18840250400391051070421003070520000480c0c5c075581c0c5030307400c4454a90041e510301d9039002d4170403e013000040c15100101560f407a0751006140d00e45541e1032074450348407244c0c8a44440620345240c1401841141c0100103088010045060351400705070281d4006070302140000d03c078110103d420f250050700c40c0380a6440620350808a41803900744030101c102442c02d400301803e161a400a0b61070240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 246119415 1250 246118165 246118183
    0x80406020106080610050a12140114070f0827070308121006111002030604090506040b06010e090903030601030903140703020313050319020f150d0203070801081f020d0608 75
    0x580001102071400601034241513010340749550010901c0c01c10441c03540e8200340c060941c0d0050000d010784c9606890908540b0b160919440c103654208070404001184d404015480b032000754480200b10f8140150480f0203110417500d03c800030a43c4c102d050100700403011081c82c0360a9910445480c56141d07100c80389150895221100701c44505000c00c00c0240d0310912030802800c5a0614010071382c000350b4100e03202da02d8810001c007540e41c00700000d030342d0766640e810000c0c4054205080e10308038206401c0088560004565490100308089003445403030819000551017460702d14040d600f583c8034140114090003602d241902040320003400b810303500a11038000c2131164800e4005540c0c605034012803c0080744a0351109100c1d4004c519940184c096403c1c403886402c4d07040303802c2c203050407914001991201e10450034038a407903000325404200c030585a00071406030400d5116071016a90302e1031010307130765050b46407000e0b00452a179120105054041e0098940b04140d0349021a40c4d94407680910301e411012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 246120665 1250 246119415 246119417
    0x1a0a0f0f09021009060f030513060f090624053a030306270c02031e0403021e011209061407050d0501050301020406051e04030803090307050c0d0f030f0c080406 70
    0x5050101c1149002c55440c8000071003424100713807051030080058601c002201c5c0150600d903da2002234801034281515a1400364825801c000e50380380c4440d0000180605041101c01918088c003000c0921542000d10208084500200e8a4103080c8001e00259102154408007840c0301e404003020b41c44c10540d4207005654980c250103500302c4540c1001800d65036281d00114804100c090700c0140144034111070300361203041e52000310340c24011480492a40c407880c1c00c1100b1541800310344004401c3c410008204a900032110450401e81e041c0c1c903502d01c14401b1001e80d0103e50104408e5842120b00d802401505000d2840060708a40d00c0004400d2183c0403036041d030020b440003840c0460b2040d01e10941d805040c0c10741c0218145802d0160150291184102205a02d0040d580590340b120303035001100c010b56880840703a5103030700f1304010445c0d0f00d0308010011a800d000d1000c41c480c1d103040c410f20000e0856080358105142d003009031025205813000c1181201000300140c4440c002c1110303940140014007403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 246121915 1250 246120665 246120671
    0xa03050604060f0b0109140a0b0f040303030e0f0a03080c0705010504210804082a01020f070210020c0a09020703050702030618070b031308030702031e0901090504091a0a0f0f 76
    0x403600d403400840f0651648140450b140c124020f0301a40c5c000c0e0503070251900c140b040901036200c20006852a603050744080190f0100080384e030144551030300a001180d20a0701e0520102d400c400846481d03020151002d501e66010700040b0000c24400c00045411600f5000c0142c5002c6064903058203650302244c05551010039022000d8041d000044888201a420b217040c203820304081d91495044e11549c180c402541c6040a480034949000050655208100000855035407060600a440d1504040c4088c4d20038007011507160b0440d40041030355054150000d0900c10380e9400c140d1014004d405c0004150308114040c8422801602c0801086000e012030358600840e020b4002e80e103601d040c4032500410307298101803040c0082501030301500306029a01c02c0f6495200d0740c0b8900d0403407441c0540c0303122452a4241200003170802070400300910903003200382e0325a07412680312024081076900c01c440080034403806040307410b012125040d446401008484000c240302d8004800300058407502c22100050a503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 246123165 1250 246121915 246121921
    0x622080d0204210f060506131806140702030702010c0f0203010f0506040507090b12040201030e0303010e07030b0a051305060109051201050603010c0c030219050304030b160f0e0312180a030506 84
    0x26256070b00314140f56400b86070000e1451555401c0c060203101c18014445030311a03011a4069907411004840c1201c105001c00c682003040300700da18503050890054411601c0e01100244007110280160f201740d11540003149013007200c0c1e004440c219040c070415030700d00c8400029100180e5003809411100811050003040d141446420041259001b8016509000185a041001550b00d4007a03403c601045030a9001503611400141c016103502221081d00b400b0020000c40c0c9044200c040c0c5000d04080d6804000d0000d40ca418840d55070780034025594014144101c0b507820f501103030070036036001c40185400d81d030712507541e0003292010309070365901d03a000c1e51924100312007801c1c244152611b013652460700c64247c540544019407150714158214a50b071820100c1e00090100030011240256402840b410b028500800100103150503403c01030f001034010204281103900c22400c0c0902900d004001e0101240d01e044480c40e940d00c83c107009000806280c5804900343e0390303100500b004601036806003016113 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 246124415 1250 246123165 246123179
    0x305060a0609060f030207060e03070812070206010e01261b040515090402060a020109080d0b1c080307110a020d0303061d0903040603020c010b090702010e0d020f0622080d0204 77
    0x4145800c16001c0042ca80002c020855010140c19449400790070f0051307035409542050b0000e07084043d040091440005654000c100c1050f000340b480c80780c072500d00b030602d840d8128200d07103c10080c4a0081060799020060112840d0100300a01303400740b03065810780c034640c101003040c10210304540e840c0382505101d4008403941403600409501140c500c100807502c034070720700020301040c401600103400b5603c0800c045240c18000d601a00c0a1a000030006456079801d0b0342160103051b04c01141030150800c0300d51801070304a0244400c29203a8411000c80c110b81d2852801c072401091240c24003810300c40c8000c280e001d03884907148098094080d03a07011801d1030a103400403c048200344041e9554082803010003949490100a035803c0c1c85c1540740150340c903a000c0f50400d003d0104c000145a01a00890070b2214258055200107640d0407002c05440c00402c120b40c040e0b27281e02544180c1c8401d508045d00049000c540400e812040c1850310007089a4044bc1c2d8451141c00d801c030600e00007a0340c2d03001405110407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 246125665 1250 246124415 246124429
    0xf0509030f06100806060622080a0807020406061b080d060f08060a05060604060f030f2304060b032a0a03080301030503040602060c0405130506040608032d0310060e1807030506 77
    0x6071114600a20a030700b804004102c0c0c0f031040f0303008540c030745041a08c0e85803da0310300003110004155000494070f003403860f410582c010340d0060900328499454580300242e901e015044082d001107030f40c00000750700f60040c1c8482000d0b03813000020966042c1d4960001c240101c01d00c680002502800d001840907141000010b021184045e01041c070a14007070004028980c2e1190244162111070701e80429000300e0010710300c024041d0000c4202c900381e034410400c00004401d0040c24401d034042c2d0010b009804c600c5050544614054000e108a40002603924102411114910303101500280040781403e80e03e4031124410340003038000300c0741c9400c006410060359030704001064201c0c4900342128509131034400000c6242901c0342074002560b4680d000900680e0740c90340300000a049240640355101c3c048608000b107242510440408d01c0c003031445540504a1450a40b0300c80c01300f0110303501d140c0381040302c296401000d0b2007480c0d07807207480041c02441b14000c2551480c060101c80c1c6010801303040c00401c026130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 246126915 1250 246125665 246125669
    0xa030905031c050901420e04030302190905010914030a17120601180e070306030507080114010e06102d0816080c031506040e0112020a080c010f0f0509030f0610 70
    0x4801802c150085000e03505e041e0541c844031480c40302c501070400141b21180001c0c940d10814207003400604010074942c15400a207400c400c03111031301240d5000d4020542c8c80b401e5900038580008e0808100380b0009203041e0055907420401001c950b035443c0715555850380012200e080080c08080490184607030509240066009542400d0800d9420755100461000c41281c0c4a49900d101420740071690341c0d806a40500051a000300c261000591034494560290649075045e05150050000001d4850a4004480d005240040000c4004404158111100207451000542e540100c00300080c180f460b20128440000341a21804100d01d0201c0900004d112010303075040070302c580e02c003c01020014020840e54054422403200e01706482ca5004100319000766005466811000750000c1400e2030351944103e02e251007282c2c0300112070b0f100d008103900c52030400b01c0140814031a0118040e1140103003902c04200b10145009410046c030040001e181842c401d9108040790456001c0c0480609182c02280c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 246128165 1250 246126915 246126941
    0x5030d0503060607020d0609020307060306060e0a0302100f050d0513030806031522020621160c08250f0203060901060617060315070201050703140603030a030905031c050901 76
    0x800e610303002c40810100d100d40340d40244254144c0400008000d01ca42c070080c0c0003500a42140c512588440c40580100010301844011451070701c1140c0380e81c6000d0031100c050b0ba030302401c0d2034180c000025040da100d600c038400a00511600b07102c4940001d09600c589e501c5400200000702c0911001d0801404080b001303480390740a41c02014a40c0801080709004913004401d4a8000f826054521a5101300e031060b1030009500c80300c0000c0d2459a00c13140e07600801031000c0100c110784152900c00519040f103400b0404000411285009040417800240c05080c02048003c840b69a410fa00896445003005519080361700400391500340003542400c100c0ca13a4812018002040302c2c81c00d110014000091180500078600444000108162014007451408643c003100c05001c2d81004207019000e094121142c000092030b0048051054503d2a043c03400740601801031480c00781051b904802401c5404015556440100240d090301d040001d600c00c0d482490400c00030700c500b0002c0145007510307000e00b500e80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 246129415 1250 246128165 246128167
    0x3061103010b1204031202130806181507050d060b0706050c03191d1e1203010e06091305030f040302120610063b0111010c12020a02010605030a060605030d05 69
    0x8010000218115001543c0c3c1241c40340c1543c4e42c07841c00b162540d00f2141c034018041d002058100094004003800c109441305003040c0c070090b5482503115582001400b09640440d4420f039007941002104407241d90708582e0514060f8600052107580b1800e035242684440c8011b00300003180d905100d0a40720741d6030000c03606900300d855403c00003600032080c80031000c01c2e42165a980840d8407074418045524142d0368001055410000e0341072103200c40012941c65196543c060328a050821500020459060310000490a0000e4548106009030003070020204202c00c0720140103000410010005410b50081c11000d4036a55800d501c140320040d461482000401c0d44030a041c0b0111071040403090040c3c680364034011550343c83da0083c00f4403050450036051080500d01501d186d840c0741441c0100000a800c0c0c82d15480200180d144c1c40c02c8500780094100000c04100481140c3c0c021900146203000c058400812415150340c006424011f01030021540603546100070401401c00b4003845804050505043d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 246130665 1250 246129415 246129419
    0xf0905150a0810080c190e040506060a09180b07110a060c11071508040305040b07030e150703080106050f1b0601091413230a05011a10020307080703030612030203040306110301 77
    0x15503254002c4107041d2182e4a801002420700c4074006d0018001c103001d41340c451039800d01d401e09944900b4141c0f03000b4056040700001140340403281c05004e45000341c1e884480811103503500c0b10341d024a0050003031401c00401d40d00c00c0045000c1041844243c600a04002803009490f46004c1d0213030b030700d244144095400100c02007200e82074854000c560001c540c01e103611659200d1408464601c0355030804210900081280414564800c08036180c40006441c0009074800d445002603243c00340d154024006940745005000052184001d400010b4655003040d040a69a41e0400245003224050000541c4403500400c5101c41c0d9014100c403030440c900e0381c0d520509054040c0840003042d0709000e009119644a10511054004c00300240b0b000048140d42c01d010541c070302140a44008502c07a403025003241e00324012840c10250111005443da0000d40c9007030b216070f0f03e00550b500000c40503801c3c10381e6190001040c5000400c1b80301c2983c800d50240d1b41c0c0328150b183c03070b00440d003040d28071a88040d014001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 246131915 1250 246130665 246130679
    0x11070602060a0c020102070c0909050c011b33090b1003031215050607030206070e0f030a1401150605071a060109090e010615050d0f0513030f0905150a0810 68
    0x9201d8000240b500c01080c24045810306070f01a1003200710003800c0e0f440010000030400000d6215030b54042c03103402910103182c0101d0045842e80c500306010400300c00c1e004240ea00003699140d4180036451401914804810031140b900d04c10056040440c100c59117510420b010007002c0101c0030307440103818044800c41400d64074020800034104d9120300700240d40b04141c242041c3d440c1d19080c000d050050031280c0d0755080380b80007500d40c05d013034900101089041046044c40c0c9031140302c0c0317116400c01030020316294026445080100044202c144840e550b5400e2080d1040c0c0060f9041002c0c03d503a482c0d0690380c0365645852004040011030070484441041c06201b0315a0340009050b0807034411003030102e180240005043d00501190b0301142050a049245488854000020b040d000890040821480c00382c4050310090395802c56116400d081030100f041c002034003031550140041d40324038140c070400f511031010236802855042c1d03680700c0b078a0205038034051551149016512561403004105200d245c515 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 246133165 1250 246131915 246131923
    0xf20070305040509150405011403100902091308070503070302030306010f0503011401050c0f0601091a0405040c09092d060b0d020a090e190804030606050109143d11070602 75
    0x10300c1e0300c90344013036011840c215881c020210038081d0044c41000103503504d844c011044c10f441d075884d9011307000d103801c1140316900030320543c102c050b0003818114803907070b410381d800c0030001c155042141c01c0781c0300303000c294041002007000e805854800e4006640c0c1e1705202c1c0001d0b081080c0f10582d081008401c000501c0291601c0e4002a027000c004c3c02c24035187c0b607010b01d405060a02210784091a07100b143c0001038501541d40110746280344103851030600c2c082550610050341c50407140030348000c01500040025201d9a801300c244d070340c0100c082c0081c4c10b0709082d80c00070800c8c2c0620007002d02d0100348111000d2205e45d120f884070341c08003113501e040c0c07030240c55010130300503161072040d6160b81d0387e50150901c00290501255400b559400c2e848181c409041c13404812a800c40d00045d00c0c82c51600d800800e00f54014082c0780180c488141e25a560001e85508108030342100070341c00c03115500782c00910310341c060b150104e0035820351015881c484001c0000ba402400050346114051107984036107420404079030089 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 246134415 1250 246133165 246133169
    0x121c2d020f091305011410090e0604090209150a09090b07080606190203070c08160312090e0103030509090705030601120515120313090603080405010c0c090f2007030504 74
    0x2100268031040040c40c40d0aa0b40507a140741a04911000100c03082814154480c0381038030b801c841d00c030040d2284036040c44005460f1140c514013003403c00e002071004084100b40e90394804d070000d1005c00c104100382c3c0032441c151002c0d80c2e0459001101d0090340000c3c076060007403502415011800b0810400a52521980d040b00503000170140300381d8501203107150b22f468084130043c0f01c03440905102100540b00081d0f496002442c1030702e11210400300800c8041d40415000b81c001100310141c00c1050442d141e0031400c41c0303000c0d401c40034401900300c009404210280d0a070700070b41c065150143c4942644007401105500180304034200700003003080180c90380e0040c41408807110108070000e05a0360b040713403c200c00042e00d00540e0780941d112406580c242c500200820380c664105c0c00c1801899030310307030790041611068040180310718400d20003885070b54070072064510320310700071440020199918038040b0304031145081504030090325100d030341c3e1070100ea0306100140143e0444605141010607100180340740118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 246135665 1250 246134415 246134501
    0x7030608030708090f1302041202090a0c020d05030a090507060305040210020a081c0b0405010909140d0906210603030f030b01020c130914010e0309010305130201080106030e121c 78
    0x4154021170f035283c10410355201212440d0465450340c9601c2140368910344c1603003ca20030088031b40000c12520300350003448404142a0000e0144450741d100946250300001c00d00e0004a40e50800f03400450302c10000140205501d840000d040d0502e4010302940c10030004003c004d40d4840006100042ca1200c212280800560b800074201c90040300341e84080c01c400130589034054108800072440318202c0e84000b106a01c90300c00038a640140b2400c080d1113503d050200400f08002d041c0410107a8047e0901303201c1c2440985602c030354010a201d843c2c04856560304290b000850074001e400c4419018440c04814810900050041e0440040010708030b400d48101c0c0c00130b198440c00d2504c04c10100c114580b840d9600440240b12000300d01154035030740d802405440c0c0c0000e04120100d041c1d260301c140c0f0500701070303010303507038040c6607030a01d4800d4002e8140c6401c05103c030710541d0b2062800c504204050400c03040f845104400c91112a428002510300e941400680d00740c04000d9115591010b82000b0044c01d04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 246136915 1250 246135665 246135679
    0x6030516170f060a09090615080a05060103060b0d020d030917121b030702030303010e0a0c030e0c0d240213090b0604060e0d2406062c0312120703060803070809 70
    0x11030000c24900200c6031700c4024076500f040c0c0b014040111344c0e0020001c0c0717a00f21582c0340100c7c0e501c00c000e9981e41036402011700250001e4005001044490300700352001c030806800d240d04068958042040030418040540000328601d1041c00160310448440c14007007007010043c4520012540705120030700c02c0704900d4060320018808904040018016116440d4005041e2512503a4468440c18244401c44490060f00c1c03a00c654a080d890280c1702d03040c1501c03480f0000707140a00b40d40c003d221a0428040080d42c010a241c1c1c50407900540c1d0716401400004c400902507201d61489142108042c41908051441402c02d440c21072280c03034040686045640514000d44800c0d03101000c0740f8824041c0f980982010311501c2c40e500c0741c02d6180310f940005000d00d0360411099681e240100c80c0c2e540000111038074203400d000c40c0780c1d8100350044002c4170008014161003a2100080350030b51258050038044101a4501c0c04001d00590144a0580100b08220103503240c07038201d81d190081441180402846a25 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 246138165 1250 246136915 246136921
    0x30304060f0806190e01030c05090c03182a0f040507020307080d06090f09030806012c01050f0a0c0c0e0403020604080c030c0f1c090323030c060106030516170f 70
    0x140303900813a401199401107882c811601d520041e604800309020949000842c0c013000501d5041c000d090b20310990000c4038031030a41c0c4031011084208081c10800341725074800d030804860f08100c40c1947c00c0070414200342c1ca82c040240e500602104008040e542403085152200f006200e5401004072502c00c1e44c011800c0b541c8080d1911007800800f100e03040168103034646640440c110795103902607200705000c0c1e00d8401079540e40c000116881311603c411841002d0103a90054482107590340402501181410b02a06080804808640e0764003d560500001040308403070006004010300700002505000c0d001842e2490292006584da10025000401d0a0700c0020300c0318800d07d0038010b8407686101801130f1012140018503131075503902c0c841c1c0c8200c44140b240303400310304c0a40a20304c1041240e270b00081c0c244002d0f140c2469000d40781d900c415454440e000400900c903140c03109202d0351340640610380780014582840c02d9080c0b840310a2542e683c0c00d001b251039018005084c604c0207242d00040550750614696 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 246139415 1250 246138165 246138169
    0xf01030c050d0509060601110102090d0201031a060d060e090d050708030a061503050114010513030807051912030b0d030c1b0b0f03010915240309020a03120806030304060f0806 77
    0xc80349000401c2c00c00d14010600140240c01718016004120903078071828024000c2581500302d1084040080d40702c04441c02c05001075000c0d401041000b0080710208581c001c0110108d41d080c1e00003421088415591002404a814030090315078128507610010301d500094107001400d18800c0c040301070409000840042d511160a030040c5000d40308681d414000c0d00c12400c8003401420085c0a5016414005541209654810800d80b42c0144101ca401103886185d600d40c403056500c0810180c6081c00390000da100d004041086140280717104405200701010030b200014229802101560721030403200031481c01080c3e2048070100d5050f004040e80d201c030107840b009158042683e178041100b00002203000410080311102950494405a000348110f990170141c1e079600c0d0300c4a0084003000c15030380040040059000b946801c1c01000c1d03060000b040c01050f000075040c000345501c00c03075040c0114180c0c00510b075801a03142c0d4000806800440c101410900c000d1305003120101441c041280400001d0295 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 246140665 1250 246139415 246139417
    0x510030b0a180e060916050918060403050d061d0109020a0915030903030e0304080303071101150f0303121406040c030f050a050f0f04050d050f070204050f150d020f01030c05 76
    0x28072031030700006010761140e01c1c100d0103008121103443c010b005240004403038210202c1d140844055650860540c0350814041009402001d8440c0218080900140e1900c074810032400d80114007a4640d00e460342c5030302100c04140d032144e400241a48041700c1c01404481800c0341d910341503480b52800580c4500c2c1010044800280325801820350b5411801030410300350301580700d40d0b00b050096a06000d00000b61012a50b2031240e403041d01c069600800003d240a0310669980c03900703110020000c0b6102c1d500010b8150b4400054020f054501906a010420180c00001d03a2040205082c8148071004168504155108000784110b00464503105140c000501ca980715120304010000200040e09000b80100001c100444041c2000510180402c103160b4008800c20312490380200180341d05d9151704000c54258211a0700411070200501107080140d075207009a510034426826890744620b400000c0b400b021207110107850180380a40040c00c00360725540c0020010550a080104580125040898035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 246141915 1250 246140665 246140669
    0x31306110c1009091401050603060607020312070305120a1b031a0909100c0c05060105040902130f0b0103051003080301141c0803091645240510030b0a 66
    0x1101c02a451456034190b00002d0040542da0009010417450660b0081d01c101c2ca00280110790740000c01340000b1340c5501c0d015008003000c520250075544605429202030000b50040c00080700481c0380400d04030144c1030b18015603031780026540001d10074019800b20958204202216400405445050440313642c1070640e4440318900005e0300050071860114501601c1d000c084100901060034080142e500b20302c100e540c4042c4513046409020140d29003c10000208200b44040f6081200d00300c8009400006100c1e01d082481070020101d0b150130304000040840381c004010b4042c40494000c01d01c0402c000d042501d064650340311110a118100388006500e4045083c00c084000440c203501000300540540038500039500d60f401c540e5180417041032101c002c9240e020340d403922100c485003041c6183d40c0e845401d6030035030303c0c420700b034003209144042c2c0c1d8078500300c081082440c90703e450040600c8980310595020b01041d0340b0b01c004c112814003000074003c540c8088001d00305070320380428000e41d9482e1840c00300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 246143165 1250 246141915 246141919
    0x807060c031518050106080c12040c0302040504030806032503030e03010603120c0b01050a0b07030e0d0c171c020c1318030305061c02031e19140f031306110c 69
    0x401c9942d001000001c2a0450b0111103083c2080f0001414034050040745010342ca0342c49a6a062a0885508200b4650300a02c16a41c034883d95900100dd81c07242d01c61103000758001c1d6aa61110315108007410f01c2d01201e201070001800445903c52010075071204802d080e02c1d494580400001c00c500b0009001d40a160409086071481100c3c106e541500400380001d002d115850b18800c0d03a0740c2c3d60400c2627098482c032802522442c204992000030748078000c1d4010300040181b11007031014aa03120307100413254031340150f00d40d000100341000c90f5400802209040855082c8603107011202400001c2d101d00350b020519000d001c12400480709010306400c8269815004085000d0610b81400e000b030103441d06030b0b42c25010f201a682c80d50038150940341128140d680141c0102121031902da441d01540720000d5509003607004001c1c0c0c042541c0c4c50540b8200c0703502d0113401d04501a281d08204c10741028440080c8840c2d9a1040040c9655a070360a0014000c641160409200800d1075120300c030708102018554a03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 246144415 1250 246143165 246143201
    0xe0f0c010233010618120305040506030a24170604110f0d060f0b0a140102120904141812120708040602070816110105041202091f080a06050a0501030807060c03 70
    0x4250154008003130028903840b0442000e05d03907501d1080a6480192543c090000f80c410002801142499402103400003510000087d0f42c1e69508032404240141491007110519402c408005185140000c4251040c680c0098000d908203a81d40c1e01d40c50722854a10385c02048245041c1c0d00c0d0742d030780b01c44140215812920900500c81180401d02c028081861694800e43e0b546c2030103c0e5100b80a00303c403401460613001880c84d41b0b009481404e094000c1d0300510391241d214000140b10143d4414401e01590504460f41d405804035540c1d5030400345a1302ca000c41035041806090441c820074541c09403c161103003406802c9071110308242c80a44601c0802030000c03a40001c62080c01510700843d00e403000e02510003022520100030044a540c440e601caa55810f100d42030b500c802500d80b4815268000c11070f0f82000101c1c042069001a12194507405041d5940107a4032140c18032409001f106e9100b00c214a0800aa40c1140d036104001e00407404054101d0f07a0f02c00056644a01030340c000c820b1007000b00c003d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 246145665 1250 246144415 246144419
    0x7052b1a09010902031b011d0f06040602010207200d0f030c020a2315040504020c0304030f080714120307030902130608030405130b010507031206030b0a0e0f0c01023301 74
    0x264060f02d09004201d010f840758080c40760300e44981d0307180450a0a0140d4600c10100d450f150005540450004010780c002180c0302d124195580f0403005000801140c0c001686030301075070500720b010105c5848020301041c05030302c42800c1540c5016030781f05203951100416144826038101202e60405000c40290000312038000800d503481c41b413114141d0040e041418030600e880800c10300083c00d2003054007041403102408280030300e1503e9000b800645c6540300803681002c0d40c1e40c5071094021028401510103001c00190002845086011094044c0401c03005150010501044010078400181b02d80201540c5414007000c660700e107403181402c0945034400f400400e407209543c03038036540948666403082d2415101d0442000a5010740380d5214170503110300742000c0054809643c0d03404115100d6517002e6031080c020000645c80b108160080c00f181c0d40010383c0860b6140554a071503000c103031115003548000000d07980c90703030b0010b146449618012440d0180700000311882c070840c40c5c04075082d2410f030061400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 246146915 1250 246145665 246145681
    0xc0d03030b06040b1803161202010c080d0c090f0501050301121e050714030a0c050906030307050304060e0103110903250f18060e0906070f12050411010207052b1a 71
    0x980040210703d640702c0011741c102d204059441c007060441407594502c540e000c014100c201f000e29651030380103040020240c48656940281544071382180c0c1001d60f55510a00180c0c0c0c0d00003145c40c050a507032410300300d1160034600041c0450005206d003201c0710399240e5064040004000c001050a242c040303d0b020590102d2901c0f40e180c64241c054440e24a2841c1c82c611854500000c410610f1500000700814240c1488203202024400502c0c217909440200480c80001c0c200700010b0000f041c0541e2124000d00c0e00000040583d01d6030b40b2402281e032021301164155a40114081984000601d8521080024000308980d46a2560700c0030003880c03c0000c002503045030a541c05440f103030041f4400c21403540c50b0460f542e0044001d0702d8821040d8862400105617070f0240303003000020601414280c007060780842c4010140d8004807421514030f00c02d042402c1c4a541c0400c00d150242000300d405002454901c003400c110b407080030300c080c6101102070718440309014848511184006060044a00618003218 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 246148165 1250 246146915 246146917
    0x9080a0506041b05221d06060a060804080910093b01030c031101030906110d110a121a060424020102030402060a030e15090703030305090607020c0d03030b06040b 71
    0x28241c840280102c10081c036028691803880a840e0300a11701110845101e021850b200715102c0616401a645c166a0540350b28503880c1d001050300d5800104101c0c81c0c40024064640f110368003810070702c4113000034040002c0c441c905440c10100c098400c5a4940002e01049800c1a03140d80199040002c03410041268120066501468080c941312515148200201000606824132018080001c000414000204541c481070b003170a00514000c00d05100c1c1d522800200c411404424004203000620b510b4115114041c2000d919000011581025040500a00b184001c1e0a90286042d603500741c4a088881c0d000402c000d400000e0441c3c0d480341d0302c4910305041030b4010410308400e4039002842c4003040d441402280d01c42c0c2d501a08190611680040c158041d11a860844a903405400d400716482c112040c50036100781b150000a00000e85541009401c4490207003005e20260460b17810007420070780004881c4641a419142d8006590560508800400f803024030300f41d008100050003e60920100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 246149415 1250 246148165 246148171
    0x11091e0a06080f162606010906090531140f0d14040617090a0510240b07020909030c010921050909060f030c0d121407030206040b0709080a0506 63
    0xb02210303180111148101d503680e83d0311148080c0c42880520034400d400140c0340400551070034450320358030382d00303016030b89410721100340c0042e50345950310f004c100540b50141c0540c9400040515450b1054010f5029598061100742c0e80080b8000d95511000200000400e5a01c44480004207484c4000128824282c03240f5042c141e6500180103010640c001818517800c4504030f40d0192104040e420103410003030014a402071030580580641c04e2028089001440000f01030440a07000264980c0340c4140403e410340b1031030100f03034010200001880340c600e000c1c0c03c5500083c1c04554840c0c5580d04c400000b490743c0f1419841c0c0d8055400c0c4025942000290400c3c0c10710260800f801da4602207c1071011107003401410781c915480f080000c0803079583d0500558454030a0409420340b22042e41036000715010a1710f41204507481610b4018034480c0d16441001f2103040c210010000b0314014940d2402540d410001c1c0c0301420f25400308021400300340c081c100e160003c11420b020386031800e1450030030230348480d030403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 246150665 1250 246149415 246149429
    0x30f04120908030307030b01030e0f0601180207050709020705010b12030301090c08070e010c05032505060c03040503071b0f03030c060f05061003020c030906031303020c01030911091e0a06 82
    0x105211590035000760492010340e9940b000450443d9070f54401100909074211030365042c941c1d241244040c01c0418042d8518a400200040a45500d804040140c8200b51040c92546078818800c0300005440804c0860466001034400358842c00e490604031700401c0d808006603442480444800000840480a18121550104100704210f8030360800d58001d40c00711a2803000030609101c8031070541c080d01140178954010b0080380d04100c00c10145179800d52445006480041920480c402005410080305901c820026140e50440c1802d64178583c1c0d82c09000001080e06054100d44e1190140a103203d200134000e100550403450395038240a80f80055060741914954104203140d41c0b40d0300d02d0b02506001d100c01030700755094000c0c42c1404400a400260001c1e030f07180000c000f4580d00b642c0d0f41d00910700a850b0040030804920407460040c1c034082c0075508050505040c0000000403c1c0580d401000d0004160386d03030403503950758081c80343c055603050081412081c0b0710b0060019415290b8080010707503000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 246151915 1250 246150665 246150683
    0x30501050a09020d02060c07030b090f0c040903090b07050a0602030103060f140402010203091005090a0f3b040203010923012316050403060903031e0203060a0e070c050102030f04 78
    0x32691004240c41400b02e001e500051040d0720900113040c82c0c030041007280001000c2c1c0f0842a107030351391884c00304010344e000010b940c425186824040c1c0203025480f030740e03c012074081200c403e46640107080805140328503400240041848001e0207020700c42001c401340c3c00384d001c40d5207603141e1400000902c11070b8042e401d840d1074402510205229107049601480e0146c00179400c1618900401076180800d611079010000d0601240e190fe032a40704500006e459031009424809051001c6907402409400210245646800041081d404800303540441c400c9680800d001c150b6960010a0141c00c990b14014402c600302c0f04007107184982460b200ca601c80902c1c00901001c80314181c20100017888002c00d126540884000c51011004444550703811030389400e060341019500d45070349044030015a01640800c0e20b604042d40d401c494542c403908210805030381142103060800200304088001c0c000d00034200ca0300e03130114800b680192011009640d112009540e01d2400308030761b106188080d6011119801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 246153165 1250 246151915 246151921
    0x1e060305060301140c0a05091804330b01090503150f18100b180a153302010b060c010b15030723070b0708150105090d030c11180103050105 61
    0x142c10b0086801440d590039002c0b4803901c07406801c0b890b65211600202c1445420841d03039000d0f0300c448901407500c0b144646214840c3c40c160a0455100703014001c0420301040320f05041c0b1100c0f9409003488501e0103081c0b00061042403401c01a200703044070340c02c415854450403e009000c0d040c80b503100361207409607113001c14854840e2511003004888042c0e08600030b0b0041412139000c8038403544400e01042c00103202c1340304251402c8a9049010050f981d100e8090b480340c9819202c040c0301d240142c020482c0c101c030740080c12007100e65030059419001c01c0d24800004140e101e00743c14403d4210003904840180041e035a800309842c1c0320f008040c5036512a001d540c030158008240031514007507920030549911602200c02000c007a254006030f00500c0070940010078070010300401c41680416204a090ba00c036641c1d0303800d0060804000c5510310804030304024041016401c2d5844071071142000640c5030800007484080d501c1c0100b071062140d00b055400100d2103082980320540703250524122401a0001c001c261 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 246154415 1250 246153165 246153169
    0x110106050102030d020c0309040c020f0c01020c010807030905010f1505120c010c1212050a06080c0306040302031e0c10050f0109020c06070f0c020d050106080717070605030601091e06030506 83
    0x1521034421180540c2060060100032003580c1c00034443c40242200356840c2c00b40c11000101228041440640103a02242005403504001c00c09c0c401460001d00007040c2e0b141004000030141000103101c88200360302c95200c1e00400600350002c0c0c3c070b80c0c00403460a00c40785814500c0c54039600032510603244142100c280342c40c03443c04d000c81c7d40400c8003010394030300018040035101e0000041088044004000091880540c0d00b03000d0b20600f8003610f020703000403680a203440e55840c40d141c2d0345014144290001170078000065000411158605618010045511081c4000c06010b00941091403254020304940341c4031908030b0780c000c903c90015002c181c501d0740d880348400c404a00446904c61040d0b40301401154000b0f0007071403801c480d00064902400c406495601194610150305c408071450b80d104d0ad000e0003d0303207082c000200544881c11001c1b17002000701c581250f65482e6403280c5401d0101c000302242203644030b00b0b00940a8180d1042110100344009410645070400c0d01c00c2c40006031510010840034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 246155665 1250 246154415 246154421
    0x7150e061e15060f120103080d0509030c0d08091207060e1c050702041802041e0b0f0303031602121b0d050a050306220f20090a120602120f071101 64
    0x748241084900b803003a480e405101544d40300300200d07419144248045056403c0e20a001c901952041c4550f0b0303113814060413080d0580303001a05d007480d1754205200380324414100003114050b2851514092002e52120401035081c0000c941c403550b501a0b00107900020b0100c990052042d404004003218100c4a424030515425445118a400022002c02480d070142c9482d81110300d81d07918151004102c2e4500d44e00040845518a20980c00ca494942c500410f140b15442070b41a04c0b0b400313558038805941c6e01c9000075100d1000900c0401107251150601301d04078030800c0250305110401102d29503032082780c01e0701c3d042c00c0d5802c889450144564062000e00d14030400c2507420b01905900c1e8541540c0307840080103c8110b401c80c0954078070035251000d05a56103280144031090410703604c0000e03400400f882d0341c140c0d1040d04809240c0100d08001c8100181c4414108008507030007141950625203461500f503000e0300c102d0520304040d00c80a8140110140c070034a4242c0154842d45643ca6610030381d596907400d0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 246156915 1250 246155665 246155671
    0x503240a0c1403040827011205070e210d0c1106040b072003010f020a03060b04080601050d050a050a060e0c1f0c0203010209040c090509010801140a0207150e061e 71
    0x90b04108124401e0101c2c0000f85801034420001a82400c444207030300100c0714001001c0300e11050485c20b070140c840d40c1100c0e14000c40c03880c1b084140030500d41070030050301212150101038001c040c00311503004c400b650b040342107901d8a9110305540782e0708000a002081313a00e01d0171060328030f03a00751070340c8101928100c4229000c0720340c0040418144039070380d290b0006162401210b4141a10800c81c01c0341c5959080c46195940710020720016114444103030300500b1107140e90464a070840c02040144902500040c40324110390080755007a108000d14030b08142041030100b4020414170802d420071080050a410646110180004403401c5814a80030000520303003400c140c40b680c0b02d0441284803560710a03103016072011b002030000b52502944c080460111080748400d000000d201c41400c1c4040e1416a04150041c8502c6000340020701002400208481003e809010010790000b040410000303443c44e0b0107200d14400320b04105200161901e02e84651040703508440b4040c8444140416517104a01180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 246158165 1250 246156915 246156917
    0xf0306091005030a06180f03050a031a031207050304030c0b12062d03030f0301140901081b060a120203101701090b01031401060e18120408030a180503240a0c 69
    0x1130a4185c1c1c80e40d0000f010110b91400b8110b4016030080045070030070700038040d110300c60340e21281d6450341d880d8024121500b81c4120407000c254040030843c15a00000d90342c10170060001420340d2510103103081e40c038500c00c0c0d600040ca284084000000c0c036600c00c1c8040d000400122616840607940d0104000b900380e0000c0302080c038810009046070000700f1044018504d0700014085a242c0003038400d8041032a0001da100d0030440b1104181103810341441214103005007a007200801504c5683c034110300e481224411001c3c00b80381c01003440100e0b00d10840e01d02c102c4000103c030031952030400100070084828076004a90400d0420002e02e2441103051103541d01036900801016490713400d564030b0306c40400c070382034891119641f962804070305400c400119034000c04407e00c0c20061000180c0407281891620342624050764400e00081000e81800320845501050b149000c242d41c4411010703491100d00160440c50305445000340c0203004540030304207210401d0320004ca40266a503003042d004184c92000e04030304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 246159415 1250 246158165 246158173
    0xb0d030306410a120f05010e0303010e01090f0624030b0f0604060305091005070f020c010f081314191b0b0f1308161508010f1e09020f030609100503 65
    0x1400d440d00c12000b042e11402c020421291103648041c05003201c000000c05541c001c4800381d0840802900344210448040c01c800514155890400e820030014014412080700c9500c2c3c0c0d0101408640903401030300508000040c0c0d1003040030650314031005070803000c11100405c0c6012005952864200c0080d400d81100078007142c54181048011005040098207010f414030400781e66000302c80c0d142c05010302c140c00c0c560755000c01c2040700d04001d192282e071107041c40c140b1800c00d580c20355a41c1e12000460340700800124070403552901c0e1611065032019011000310b07500a06e111130314070410450803031400c28000d0610503084035221080034100d400c01d2144918240c400c03ca03140301d80d42443d02401751260603032445581c03c0c1d41c070403419061031441d40e030354030300d146a0f9031003070200082420070b84456848501d840700c101e42c104810282c100010740038100b460b0000c9502402d0419041d030b4143d000c2d0401c0401951944500c61581245420580d840c1d0700c40c2c0303022400950300d00041c0244500b2a40020004c2c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 246160665 1250 246159415 246159509
    0x604080d02070515011401081806040b070c0c0f0f080c0603041b0807060504031703090a3507050705030a17090607060203090d0306050a060905090a0b0d030306 70
    0x58000790300031107080703401303000d00b0a0310408100500311545c000c0007030103591005900b580000610351907000f09584030766a4600d8601c6a96034001030784583c020340c4218200425203030102e007a02d001458400017001c0d40000300f4080b403e07554030160402140d6286010b5401c454a480b46591543c040c2904103810030014000280840c0030016903800510070407010083c0280c51389402c6041000c240c2014002c00e80c001020800c221802003e10a02c200b005000d600314104030a00300d40316482d40308090041d0f41c411003600c040480c803111803641260344407001c3d481100061041760107a040b02400b6105409004c40005140c1004607501303406661280581c20040288010b4104541140501c90340014082c0056000a12544010340c01148040014401c4400c440b500400f505c40e507801490160700500f400300881504100080c050b11011143c08699581c0c02035080c0c010140640044e600041c11101c0380c0515070194001c1c000c2c1c4d1940829406944074010468140b505020295414150b0840c1c203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 246161915 1250 246160665 246160687
    0x1302010c12090f080a0b01121e0204020904150305070503030a0210050c0d020414041b02122101150801060207060906030911311112180a140f060408 65
    0x601924080c0350b00304289140e44500222500c54603540100607aa48078000075014407040002141c01090071810f40c400c99516503603130840010050804981d20b4408401190845d59260140d4a07032010241c820860001c41d08495008040240f2041d1000d0150307100c00b1803a402c0c00300484400e0142d075001000d1110790702da691002020024a605280034081c020a10307400039600041004116040c0c0803201030a800003004201d402c641021401541e21a003801142a008521042e2040080d20301310740314a19500c809181242e001100080b01c6040000425002c2607a50205005849507a4400311a80c850900f40d03503880b9640141400f1588201341004000e2181d04010b60461040c20314040040301e500108040c010030750304d45485203540d041140b102c0359075171080d0f54013a0382180007401903141d41c82c0e031104903110720340768402d902c0020000180c000f0306200300d031000000c01c03c003110711569880c1820075140384006080346507030141c8420024008000590b0501035034000d1030051a046038440d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 246163165 1250 246161915 246161933
    0x1419030f11070209220303020a0201050601091a0a110f011b02010b010801030f051c0e10170403030e19080310060e031c03061a12060105120a020a1718061302010c 71
    0x70031845c810f801444098461207010b07a803584194400e07280942c450003c14400790944000500c140e0412441c43c008000910104a0380303245545030006907541d034281408200c54101900c60346a0a6106031110303c0041c0505510030312901711411581443c6c1d1084210890984900081180c0040c0d100c40060000c10081c188111403184a403007160505055003180c2c411a03070103483c0c05000710b240401c401405082040010800707811a01d00340c3d07151070300e00304c80024030306000d03002400b003598400d030141306c003003003040303054120f40b0802c1c0d610003800310b54034108690b0740c400c44823840150021100011524014002040c40c050010041c2902c0402080706210f058130b02d0611004042c4c54000002c0c401400da4000e042081c000030020765901750028180d00c541501030982d03410007008012500300031048a060503085444501e016a0f115003020301161141120481100500c0444040c0038001450843d8070280328401c0064400c0c580c0d4001e0b14000140c181d0788042e000c200300c83c1d9603000007000700c1c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 246164415 1250 246163165 246163171
    0x50307021003021c14010603060815040c0b0409020a030609020c0a03080604060510020c09011d070c060b040606030504021306120f29010305060906190c1419030f11070209 75
    0x454010f05054480155010940581d0034401000b41e48404840104405c07290b140e015165609040c0a000d00e00043d83d1354a1910036540300ca100c684c41c000c0780801416640003c0101103a9152585480e00c3d070b003060000398050300025010030700c0c0020000c1c54810b01d000740d4092171400307405400301e100c494800361032001c07008010a40c0715540e60306c007045039500e401d120a1031003550341c010802c1d040104140400500c0681000c0c0c14400700420f5640882810100d0750340c04199481c0001002195107004806001409000c40d8068282500415a00c1d85036008610480c000c80e11000241000040360086130124080c180c0c40032160001c0a000c10342094103928143d1040b42d40110801200050840005188603034958102051004209009003000450f030000e1000780684403500749007090710400d5524080148055845130140c003060780c040d40311b821400c0030000300c3c60780c4e504196003407180d131404e110102c4c004203160407064605c100040c410361500ca1184611185085995000c0140800c002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 246165665 1250 246164415 246164417
    0x3030f11060c0d1109360106030b0315040203121606020301120c0f08030a0309030302131e0609050d0f020a090905070f06020a0b070e040204030501150906050108040503070210 77
    0x2101000304903a41080a00d1041010041440c0c40b0485203008009690101005500c0c60806000c05001696000f90b10f450500103140450f440144001c1c0a003068091450840c59080e1000000903455406030801400d1030411000d496020885141001040b941650040d41503803003180a900000070800041c00882683c041456031451160b032440180e9000341c0200d800c0c0f9012481007010445042c001801900441b40806201070800c0002580d178002c40408104140d2581c0750041454003941c12209104440821034040342e48543c191011b466000b0307a841c1004120560002da030602c14200d0030309030f4000800c0044441c110740c468030b8444a985c00140d0380196030003000209141184640e911080c0305802401c2007900c0c140740d031190b1442e554000815034100040d540c0001d848404046d41c801810304101c0380045240f800f0900074000c580000b44658030f000540301100305210000411210040000d014098491004444041c3c0070780b4000e0140d0300620001c001031404103c035600003c45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 246166915 1250 246165665 246165677
    0x80703090204060b040501111c082d010807150e0d020a150c0204110405130e120708040905101a031e0c0c070501081003030e03070503011e0b0a05090103030f 69
    0x80e40010703007110f0240c3d01c181c2000d0b5000404011550b000800c4032900000c03070000d404250118070540701032000c0d102400c000c00c9001c1001640706860114040a20040c60300a046da00f4641d0803c0456590203000b0800907110f040e9000805204100c40e01018015039524846c0d0b4910210901c1700900b00342c0c13402c0b030b07020b1000c03480400c8803580808004400d1b101c03542c803c0c100c0364031401444225114070882c006020010482409a901c0e07105a0040d00c2c1d14030307400003c542d94145951800c0c007010354040c0d1400d00c40080c13090244000c40001e00181d452203501001240c41c0c41c0c038100c0c08006507109070b4064000e2180307078030702c0403034260003656002034280322001d540c00500c400b04030301c0501202d031035500c2800410344202d441c00412454010740402c0c00d102c50b45040962004100f0441d52100504100e03020039480182d03101440000010b0002400030f00c10042c0c004002c0b2007101905000341400ca1030070510320150700e050000201152405070110380240d00b5501c00300c038410b1890b49003c0a00407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 246168165 1250 246166915 246166931
    0xe0c0a03020123030708040c05040515010e0a08010509030d182102100603061b0305010e0123030d0323070f030b0303090a090e0d050705030406030e10020307080f070c0b0106080703 79
    0x7100c00641c8150115910300115242c94505012a0362302c90300300c01c0c01240b50400700040c107440c00d030b15081141800d00b01038115942002c005650103596401500c103075401c01050000c180ca001000d80700e166030b602c00c1449201c420f480d004201d2084000050490301b0030701c0406040010620306080008101c0c415103e8003240382694005646080c0e10450300079503900c2d070290b03044140d18000c14940e0341c5440c05024a501d041490400725006000350f9014003a0000601c002040060344108596800b4090310751905280c50f0280081214003001140840e0071001c4148415141c0d122700d01c01c01c05030710340d03400008604004900800d0080754082d010f1000308908801d641e2400327410801032103866001f00d5100c031700b6807050341003c419a802009021081c81007200186020003603800707580b0b5078680041c0d024030420360b241c43c04000d041e40701c12013403000091007c0140e2044902d449039048143d034a0503601e59000c00c0b030700b07641580030107002c40b001c020061211501c500b0500381c00041c0352801040d516 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 246169415 1250 246168165 246168227
    0x807050d05040e01060e0907030f090b043002120310170f0c01030603030507020d020d0c03051c08090c0103110405060a0e031204060203031504020d0509060403030e0c0a030201 77
    0x1080c42091004254085002c2128a4049034210b01400052820708650200d0310701044220101602a8045c1034482050400c1541c4550000c1d5600f9040306d0382e2000c1e420641040e008840041080445132069100d915048440210003820110580c0e40200003000d44400700c0c0c3c0250704003616040071000c0c1008002107004030800381d0421401d01101134880c2d464194425407428000124072810306080547c00c0000c03e0f0400c05691a85406480242d1008824400110b02404602d002044403c0740c01c404005d214000648020711084030304180310041203507400750340e030050454880d05035034030040380350070907503c00e4015911903140c031400c0d031b4241503d88002071281c1d00b08000b52400034003400100041031504005404001208004071840c25080002c02503ca1000420025044042c03c8058005c0e442d254115034402d40c2d01c44e01002182015410389440b600255001d40010b0b08058000c200c504010074034220b04030000302045d1038240740d540191070306c119030004282e122184007261000b00d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 246170665 1250 246169415 246169423
    0x609020c01050601020c091003020909030f190215060906040c02070510020c0102280314090414190b03030301062f07061101020f0f0c10090c0f091413080705 69
    0x4424050000b040516258000a190039001c2c2c5104d407040040c007081c81400115090501c059079010340d45100b16554001d1554658440d8441c0640304600020340641c82d0561042d840071214420340c01e403202c129a8248502105c0300c16500160b000c9601c0020500d945031a40c01901c12802e9401a98275042c0e503040001c0c88810700c0d1306808056000f000401c0803940c1c0c10701110b1038600083d404030b98200503940c02a40c0703180f0491380040a101884500c001c040c60b034482501c12540c00200144691010400208601041a5002c040442c1c00c0b80c3c1d5540800260b0043e400f40b000040d00850540c0c0c6040011a484d840d041d86000300c0595480345900e42d004880b01c05148503010704000c0103030a2500b00010304400105900080c1a48180448050306c446001103600b110740c800d03200394568039242030050900c1864240c02c3c108c1454060050b081015101c030034002c50707529051031510303603540b8804102510b1032410322600e1004040300041400065180c50f4035014080d40380346042c070304140d4409140c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 246171915 1250 246170665 246170677
    0x40e0c030714130908031302221a01050a0f0e0409020414010503070519091505040504030201240f0b030c0f03040302011a010c050613170a03020304110301060b0409020904060902 78
    0x2400702d20410b81da9a5080045402d000550304540400052101e81c482c507200c0d010190801848002c04c0881205666403031002107454070710281c1d813090b80310761400c1e88001441c01540f00c203d04d901c0b0095003641580a103007580d110b03101e5511034400541a80c0c00403524501c00d9106140d0260f502d1001c00050b8540e403003416000486090036002e030354100010036141c110a5400b071445016040444141c6500b0b910580007141e11a000200311444005402030750480280c000d0368105140904200525905412205007408d411660100010304c140482c00350708220f000e1002141c80d0780a0400400880c1401958082e400c0300300c5600700b12031000c00c003c60354015107094005039107880d00d11403002c0e003082400500b030200b42465411074485660f1261900001072441480c07041351040c1c0400c0c0241c19140c60309100a40107060b81d01e400c0c64070058020341044d28141c901c2241c100b041c2d0503900b014032070242580d410000050030185400c11441c041c2d07002c0400c00d0742180d2107a40002d40c454044c005482 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 246173165 1250 246171915 246171929
    0x2040f09060e090a020112020306010e040e0109060507091a0d060506070803010f0b040f0506031b040603091b38030106030203010915060806270c0301030203060703020414040e0c0307 80
    0x9041d528001880280c0080900150100e030028405000141c3c4c002001c1c417481003040c1c0300580c9954480005840f03007040c0c1c04000f50800c1c00c115400d11340f2103040d80020ba207103100b1803013004540c55243d41194000b0060060b44191007100c0c00c2c541c0e10122450140c0461540c4c0440031480c0c81e155000300398541c102c0c140440c0c00e0640400180401640824140080c0644110032420316280407036054240819104a41c000d19000020600901e070305032404005180e0700a130705517141e6461400400800e400481925420610003201305080d400481c10713011103080c40c82101010030402480c6451000031403d0340303650f2240401c0e1040a100c440c024600070401030724016125803500b818142075850317503002d0f41c40603086004c1c103020860b005a0001c1d0440c0c0b094409591440a080d442d03a0501281a0404c52040380241000000c401803c01541038900c01e03003d07901d0940b11000b055040c6e0090380203420721035906030340c001814103095203e11a0b0504803800c82c1c22030f401c0800440e090065540045c0303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 246174415 1250 246173165 246173171
    0xc06050703021207150207020f0a0b0a09050102030909040b18011505040f0b010903030513030507090501080c060315010f120f0c020d020a0521071e050105070c03120f02040f09 77
    0x1806042d0180154030700310b840346070a103141524541c0c0720420714505a80f9039059603030100e10201992114900205124000b4140c00d048a8661402d000e250700002903107000074040e0940030840354404016101c00c1000603000b48a5601da03996000900840140080c801490400e07400610440034081c44020074202e80f0504451400c210600090350020b60007001c82c01c2c2486000961641d0028403101100d42510704141c48503e80310800c40e000a80e580b000c0c0103440341510106ea0b55450b503000c941207540303100403900d600300c503901803000b50f0004442608808802884100e01075028031150020b130b100c02d20b00101c2c294031040186045644200c0102d50f1240e891340c200807425010890302c51040c2081c001094409542d66426540d40c0c040c44d5000e0348285800c000300030001c106c40948a10503404014800d0540c0c030641e20070b980c0c03417003507205485541c00d01e40400c01c40d0303004030b00011059406594136903405441b296040041c180303003130404600e41d500700000260f0ac1626211180544040340c004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 246175665 1250 246174415 246174427
    0x18101101051b030411190815060405060a0306180b010602010e060702030c07180b0303070305030727030b0402030a0c08160f050a12171309050a0509030f160c0605 71
    0x140c00c488000300041980d41c0200769400b054821401500e6110b544801c90001c0400d600003c6413110000400407181d41c0102c9101195490780495039094000315407002040070380d00e00040200f034410584800c0e81090094505102080d680d0308220b03007000c1e010300c560031a40304507904c8103802c070b400341c0c009001070b595078030b80c504130400c02d00c80641c000c0010701c0254207203413600d495580c480303110748500b0300b81440442c100d584c0c0440980050510100c001c0c181c3e234498206050152007a030048505c100010540d03684103c0034261401c1102c0e900c0f1080001006d060300f107036500c803107252003d003050382e051050b0760301e210004020400071006412844040d0541034184400304449030121707000700211003800c48051000b501da082802d81180c4288941c0140500282040d681841500e40c00300d4108100040c1c4500083c1e004109008440d105801000140e0310001d040003210f0741950108040c0d00104045c2c000c0c0f402150150044803e107843e81c0865039201c0c0d4910601001540c0014089007002c680 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 246176915 1250 246175665 246175697
    0x120207020d20030c06090103150305010203040c0e07020d0c020f0f0d150c080609070804080c03040902091008040302070e100b0304060f05011208070803040c08060a09020a090605151810 81
    0x1c801c09402d0103400030a001141c140c0001c5e15030044a45050400d41e03140124000c051a4084000085401100855503402c040c108200d07060f130300340110701c070114691000c45c0e1440d10004105d40c400c040b540d616502544594200142d030301016480c607a110301e0300c0c0c0d080b000c1c9a45541d645208148030708039030040c0c607900300500c2c0c06039074007100a03000b40503181003046496181e0000550348003029241c000b015a6443c40c10340321074016120310829610010a01140d03c10146e4010040280129000c0416802556040740d4000301160010010703088100304000c9081808081f641000040d00302c502100e445401c03140140d007080380d094410b6600c486281d02e00201511542e400f5060894010b143d8101072b444020840c4500a0020a604000400a01840340824081e005400620240c1e505400c05141d1840940340d0712030b0a0344039803510440001c1c2c0300c007207100301422030f00064000c01e1400d0a15020445580000103214809018101000c00d9a5901c02c03007800d010850703071108080743c00c0b0214 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 246178165 1250 246176915 246176963
    0xb030906010e100b340f12031e0b091b19020f0d0201020403020a0f0303201905100e0105190b1c0c0e0f0c0d0513020a080708010b0409030f120207020d 66
    0x1200341007000102c074172000f10b40ca229030f6240c2150812901c50b420b0320341240c1100240f500104640b5120350030070038101040d080cad403c461151101100c100c09581c680401004100e03100d207480346d04101c1c0812440807444280000b804224510380161405005034003c2d05081401651402c4010b03580080d043c4218684820035601a00054407000426811945e015041c160f5400100d028080c02021540c0070031800c014041030500401c5025100113030600d4401e5840c0c070070081e0500c1007400d000000c0c810311014461648a1036040d02c40140c40c0e0040001c282c000c0c44280000c64200c484000040483c002c5c0d00c119021442c4030395031000c15507240c800d207103c8050303011f881c4040440301002809066070b8818181ca181c4111007000092039110320707040101d144109d0030000d4010051005c00558a03030040380c10403c41d41c0b85c400a101d80c0a900003080704450a041005000c01c09a2a0740d09103030b840781d50b222000b0400301c04c3c014a8515207400082d43d14103410403c4520b03004410240c071444250700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 246179415 1250 246178165 246178237
    0x621070602010609110703020c010815101106070c170d060803160c0807030206030103030509060c060f09011401080d210e010c09050105180616080c030c06010b030906010e100b 77
    0x105c0c50303810020b080c2d50094844a88550315810450070034042070401022115074100d400c1f000f071104200c803c0d8500090140065043c1010b503600a040006040c68040e81c1007590031a848500340c18910381404141d042034000c040c07001411030b5034603000701e4040310410040c007a00d1541004c0e907036400410300d8420f0700c405140d00074100e260001402080103889050540341500d505041c602e0b10342c2e801e00003284c1b09014000143c0b0080c850b410601c0901c207410040c940c003a10f10000240601d082c102402c0a0030b040c01c0c41100c40c0da41c080d008040415210f0300e555102051040b82c82c0c0202400390450000303451101d182016142d44d40c0c1020708003260000c2d03c180003001c0a0800c581043c0e07103e02040700280e0882c110901854000880405941c14184160001036010780415142d84400013101e540c0c0d002024260681d205030400440d42c100b6040640b032280e9401001003043da8203001220a10030350180000030400380c481d0700840d50080c20400741010917080c142142030103e0718840c00320004058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 246180665 1250 246179415 246179441
    0x102030f0405010302090f13090b06030a030e0f01110d05040e0a0c020c10110d09080606120607180b0c010e060a11070305340303060b120621070602010609 68
    0x304440d100d04010354041e102255400d00f001038a83d6200d1000c1a040c2010440f4030b548410b80642c00441c2d98032603407001520b507004022260340c03659510181940c59400c8500500454040c480300000380c0741c520b17079800346841c043c505481c400c01c02091a40c50400300c0340603d404038030082414015440c0320360350641d00c062440d030140100d80880001a45a0219003c9180114005440012007a00406035981082840b400329801505010001490000305010740c00c2c09008031404200030385092900c559140c22020058602506c80c0c1405407648a640040c160414050380000108840341c0e0019061782000340d800452149a250015820b2490080209081a281045a054282d40c08040d00c4d040d903410b00f0180e5480b4201001020b00c4003d42c5203054101403115441080f20190f1145518182d101b510305006040c1c5030014140315008030820764016a03521000070380145001c1400d12000c0803260011402c1d4114120014240300782500307c0300c0541e45807041040810502d2240031070081034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 246181915 1250 246180665 246180667
    0x5040f030305070320030612062809050601121406040305030f091c180503010606020106080d0203030618041a0903040503210a110304080a030309060f0515060c0a050703060b0f010203 80
    0x60260024428030003030312040c0401c040300055081c1c46a042408d079238400d8600703c0da1070345854a5642050705225090042c101e801642000c11200603018046078217178000080c0c115a0300b46a850a401551000d058035070000c0c0c17100600702e107030043c400c1900407402503070740c00e55030302c1c14000c00780c40e44001401c00b241640c05640039220110210381803090700032907031510440040100958041c40c00d0160002176041d460514002107150701548a402160021000e50f10703410000c1c1c10580c0c0301d020480300280c101604200343c4031031071010514198010320441d0a81c580c40510b640700014170900322480d180030b6000290501c40d9140c10000424655100a140e0703820503444c0c0c1030501c8038010b50601e0700c01c0c42440188403260500a000750750191090a048400d5440f060500401a00301130720191a050329000380d140100da03403030013243e100c1d41140601140e501251010f00880d13074080e10501034680101700600e0b000500510141c401940190000315074080c04500b002188200070310b100d415948 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 246183165 1250 246181915 246181931
    0xd0f0b0a1a0d1205090301050c0408070f06020d0507140d0c0203070504020a1407020312160b01120206071202011d06040c05010c020a090515060c031309020903120f04030605040f0303050703 83
    0x40c4a0b9014044103900003d140683c2e004404292102e001384165241d15509000800040e9145200944216040c0390112550260303038502490007401c05020300d00068111480500e082070107403006083c0b541c07040c20300c00c000c8000000300c5410840d14044540009540f600e015066180030041980981800c82d002c602d0400401b074050251a20040c5005202c140072480b001036540900c0300403d0040c1841c00130355517044400400c00c41c0c02521000311001c503103500021030f00103000001d50700da1580c0640356070719000480e1501d400d03020001c140c040031513481c1c0d0104a030007014014280e0050a002009101c6801c0625290100ba051034104c2810800010440700141c1c3d902403c050845802990001c0c4503122985082038030b20307001c1d00b41034010030b0001d980d0b0089100000104007440c0c640505032130300354507048030806034031581c4070751940740d0301001c03c907072107001b42400810284441c40e0b00d5500c1d0540da603480070213035442102c0c00e84500018078104030030f15400d030180c954400304900c2c04200040e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 246184415 1250 246183165 246183169
    0x303010f12140703080304060f090b0a0203100b0a03062102090f1320030f060601140c07050d030c021c0f0b151305060307240503060d0f0b0a1a 63
    0xc440c4104211400c5070000342003800314120704502507400810503075582649034108810103900913a02191860316184404828804038410345500541c80f140010081d19000c1c100c4d40a500080c100c18038a000a5400040301003035040240b0007169152408207407607241c030542d00c9201c80300041c00c80302c00182c5540c880041e030358003581701d44c080c5050300c0300a260381352b8812040400320414002441d014125101e0006400f805140d484280011002c035404841070900040d110341c006c0ea50140800e01e000181060040c00102a0516510000449081035560800110b000e0300c0b44000b80d020803444c810034029410b01203013810007125243c010031907080d0103030784050800082e480c2c081e200c000100089801c4108000c20541b8441008160001000d40c8071003103c01803806407a000c3c880e11940c0800078491a0201a4a81000b40780c00c1b03811400b0541a0151800d0307000a1569070701c4400b90184000251041882001847c0103220944107460b2a0340b65608031006084403044401055280420b95 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 246185665 1250 246184415 246184439
    0x618090c04150b0a030908040906030602070c05040209030a15090c091b0219081804090b010f080a0804050f010908120306010e221a13091b1a2802030702040e030301 72
    0x500c00078640040c0e61b45007400c0c0440f0b68040d6422070b09156003415000410b118040e0003821030039000d003004c43c0016584e182000120b21620520a07050340141d040305021403c80490680c020a0081000c03410344880d640394000b445650300b0802640d42d40d0514020080700c412403140340c1520754002041652100d9807481019001e0100081c107409000441e10038810601c2603c9030080400381040c018400d4074940280d03031a00c02d020714102e84403100000504024001101c0c106d164100d61417900c1d2906090a00c0b802540910899050003a824000210b5000800180d603008459800307541d102d040c0000010328021b940c501301c07480303544402401c02000c0340402c0c1003081070042040010b10900794400054040c0180b104180c3e101d0040074a445401900342c0044107094450340300d048011020711411610710015008510008140405440350406d00e01c001701b000744410510198405891004030103d614041070742c2c2c0041c1c0000c2001c00c1141000d006612500c4040740c080c1d07086604002c080c440c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 246186915 1250 246185665 246185677
    0x1d07031a0907090204060c06110310050d1a0403020601140603040210050a031d0f070b0c120a05090a15080f0f071803020405010b0406080903090d03080618090c04150b 73
    0xc40304440c0070620a00d400c000400c000c040452080d0340f22907845501400c41c804c1c0c0c04050f86c255003000001300f0085a0f150403a4801c048042240000508040c00d03c00f5040080e54101d40d00500d0013041d08140b031004105c3c51080e4401d60040641d9810004641c241e10300c44500e503401450180184030059580145a00d6007a50310300d4800e4985c0341009049018200c0e02030207401c03175250104008d104e1780005c038500c080c1c41641004c80b40c0040c0e03181514540c40c41010003500181d00304141c003800c2c09500100601c0440028a8803900301f00c402e5000540000c81341c0d1040311000106200440340c56045041e20390f00c2040c24150500d0f0340362a01742a01d02100041143e41082030b4150161100d130314000114000d181c000d4000c0140e507840e40c0c3c5464a507406801060049804140010711040c4004112007942c00058075500340e90341150b8094803d024050b202561094001d4540b11401604401c240d02c05d01200d0300030b00d510444070301072200302c4107025044540d2104124042c4a020042c8040b504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 246188165 1250 246186915 246186953
    0x30a05070e1027050a150608071403040812060a03150203010306050901091112190b060a170c150408100504120c170309030c030d05041104090506060d02030c03030d1d0703 75
    0x1c3c15540300340d4250300905507000c0159000040e00008607c05500100091103046203445021011300178004841d9a0f0004540040600c1c034100029051010302204c51904008003400540e803080d102d07510110b9001c840301c00340081c246c4c003000401c02d0001901929400011010080118042c10f8440130302102da01c8050900404510f40c0e0707801e180e8800c100507424410b6480001d52442480d10345841d00580c141c0742c00d44581c0601001060b080c1c5410054408149141c00402070404804180605c160300451040400744c6d06000008501e40103000b0310f4481c10042100007210306e81440d0908840c8001c0303506808101c440017211001642a401080c48804d20b140020707282c1c0d5541c50f00078514418074600081e1400301040e00c0620042a42046011781c0c840c4a8074440c88804074144002c4074041e0001905a0b07201768003249450034047c00807404140090207a4032800928404031f40307035070300c05441e01403500c0d503610518040c81c2175000440d00c0c1c1c804810242c12480e14644801000c081c001c61484 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 246189415 1250 246188165 246188171
    0xa111e070506090913020109150908060c030c0406030b04092010090506040612090c030b1e100b030a060e160e0d080a050c0312040f050105090c0a14030a05070e1027 72
    0x2c00e47e8000d032001c0c001003140c51010341111012610080100200d403060036907078030440c004100101540400c0c0e9119030400e0251606103071034010214050310061105a8002c0c0d5030783c00040205407a0f500c5080070812400024106050003001d00c40903c00700740891082103103250050100380d59040c00c407400c8440784d14104805040503126540208501703036000301001c116090010800500245880c400c0381c504042c503142e901c0e21100c4902581c1b0803154104904225101401020084805160043c816880c00120561212590b00910000343c0c0c80320100e00e0611400c0040d41d600c4005c0801540c1e050725000070850055541030b01e6070180400e52001d0281c0840c0d04840c0d6241041901c1101900b00c8040459040c1420806035242c90076405030340301e50a00c00022040e0320005050300c1c43d904080c02000d4030601e0146050290200400601d0385401000305403800704600308030090240481044030622400c150398401a000120750010040030040310b40c84407103e00b0106022010f110500b008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 246190665 1250 246189415 246189451
    0x1b11030a0c020a05060c24060d0308090a0c060503150102011503060518101a0f0f3f0c010c0305070803180615270c0a111e0705060909 59
    0x28500c00c2d001e070070503170300540e02092803102c0c0b480c0000e030342c540d10800c20b034000c16200c5e13183c000a815181c2210815004035400280c4000a07102c0d04a460b031001040e8240c0d80c0d6608241d0756105a2800c07940000006240072090252040100f0b2500e01000070034002040701c4101002c2c01d60b000c50440c803021b00041d540c0d000081d0b9084890001a41142d0348206541d0a59000145d0400421206000314014551034410018500700007451544071000200302501021040007080001d046d01e010400100507010318140305085802407905c41c48154100120505c01101802440e121402031a141004904007104003ca03400408a0710101c1d0400c00c0076541e5642c0c1c819a0400f42d03055803034110035118041c20440707031000ca200500e0b00e100f000c6410916840700b03103080c50390745030714200300d40c0c90081500c02003441c076030a0b83d000303182d411141c0c100412289800071311641000e201c07005041001d0031032907000c405200c041c06030300041c01d8110b0707180303007041c90420202c0d44400300201038044408512040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 246191915 1250 246190665 246190669
    0xb04061805150a271709040914060705030c0a08060a15020312060907090b160c0f06081006050d020a020708060c070c080a0f0b07211b11030a0c02 64
    0x2101194020701100c815000c08011640000390407120307291900c3ca8a01d044100c0303460500c10080100c410102580910519102c0b0501200b4560616018140401100340d09480f103000b445c07541070240c585051a80d04450382070b070806400400c1081000410010068400309200550720380c0d451350701e0030f81301a903604400304070111791542040e00040f520340040701d10650b00100900b8408011108040c007911303004d0a1150004099851401003803400a0a100072510309000d40801403418040065071510b42d08c81d413004400f15000810403550080d02070050640002d17a0603005420042c10f15900da01d0100024404e000322502c0e88902900024004004c034800c00c8030402800041d4152002c9040051010a541e40100c0c0103d4070308c035048100180d00000819440e40c401e42010b5020100001c55850b42c02c4040000d203038009001c11514030000041c41c0d41c207005004040c1045c0054901540044c0d00d541c039007406c06803805c002540011455680c008419101806028102100c0c2810b103440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 246193165 1250 246191915 246191951
    0x105060904030f0c15020318010e030901030f0902041d06150a0b0f0c0f01061502010209031b0303040e0106020d112b0e090c040303090f06050412031403070906090807030b0406 77
    0x4801791000f1110b1035051524006079000750f0007074400764100c0c070409030354407102c50a0300c034085c5050507140c00030300460f03c10b54013941000e145079104100000300c0c0186940018110341c3d404800540b4100c2416250000620400c0b042c2e400074148543d030750100390b1583c00600b030828240240030346824081803040c11140d540041d100a16141c6058464643d80041828001d15161107000c620f40d410b150000300040c01842110090500500941509034038035004c0c175048074000c41810380510003000b000628944a040c0103028103034039406049541206240100380b4807181c0801c3d41d0680015448040000d5008070104038190b0709040d10080b5085c160054074200e80008100b03401a0314581005052602c060041054071311980b203480d0f540da114490011545214004d60010031410801801030035100f02007400298403030703e80420204980100710500390002d03101040411004a030901c00147c000e403030030018100e214018046145941ca441c2d10281d4064806002d0561741d603482015101c6c941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 246194415 1250 246193165 246193187
    0x507150309080a0206040b13030915051605010f0f0506100e0a1d0a0e01020f040b1309020703030b0a08120a180503070303110d0302031506180a090212090105060904030f 74
    0x38802c00d440701c1d058680a51588003c64085400404420000d0840440c0000c003a40441e05541e810006030309060302a000b01d00d041e81000c0600a050101c0040e144001074003601840c03040c8004140e11100d81c45050603291040b4241041e5414402048680e40b681c1d04810094030300d0b407400e0720140c194640482d15004041d003100440101c20500799030f4503074908040354043e45c0c50074401c0012a50f4103041c90300302e02401801c8005e40e1002c0208000041442010b03048014500e041079440e0355803a022103080364402a002c8020076101d40b4191054030300004050000c1c08050702a020481200714202c005205441c4440140a10041000050350258151802508014044a0313016803241409081101d8044540003580f041001e61803259100c3d00a0340e00a034864121890f00354002c0c030130000c841d0010600280840b10000e00d2180e50354403903481400420340900c0052303461075500101e00400d078000701100e0150781044180207050701c070000d404d540240c2610709515551103050781103070543e00311 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 246195665 1250 246194415 246194423
    0x1050d080901121d0307020114030103030c15020d141e06101209060c030902030f1b0402031801051015081b0924130621020a110a0804060905010801030507150309 71
    0x68a9002c4030344d0000402805014000d0326924a10942070641103454402404000c000482808604000460ba40c0c20a55804103011026090000700d00424045505030a505540740b0318900c00c1c010001022900392400e883c401805240900e0030300041100c210b80d10130b220302001240400b041e00000f5551001c1d00302d5030302510604c00c044d81c400b40240a03240a0f00260b100b4064801902e032054800078841815030418803015110b0b040300c000300300007500001c2451204000f40e14046094400c00c0c07080705e00c01e110000b00000e076103003040e0090829280015001040c025544140040e9891523450442c041305080e007480e503100d00f0740010820309000c0444080c0c05400b10f0002c020508034410180c00c0c20740c0100c9800790f09030303038032602103d01055100590303010754100c1549501c030048a8005100281a5080c128055040c544105240010540c8182e800d003002080901550b980300301c004009020074600f400480d41540c0f901501c0380820301c80c0c1d0a940c0c108020010240b4003e4002120160704 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 246196915 1250 246195665 246195701
    0x705150603030412050309010806061813090b070206010806011a0d0f090807030507051216030807021f06090c02011b0518061605010b01020f0c0f0303090405011d01050d08090112 78
    0x6031a050b83d86e600070702d0032240841c0031100001c81e0707030500a00741c4030300d2841540c7c1600701a08080600021190940803a00d03815115804480425540c0303521a0042c60154000d100341e41c07400401c01e0403e0810303000240f21515503102c130001d81800800342c0d03481c041c2080c1c0000700000c49400702402170158035801000c0c250080b811505054000029005850180b0240c1c0c080341103a441410691040d140e00c5074480d83d9902d4400f0119100b4141c0c6030b8061907600407501140c0b00c0036141c0a51a0590b42000d140984030361040c48249402d0082c00c41d1502140000d00c5045486e01c9841312200c80c54501a040000102c1c02c0c450040045000820035407014024a5032004529001b8440d2042808159069070a103c000701003940b000580c40c0100c0c214801a00400c02c0c100c0421182d0200c04a003580d0501c810f100302e998550301d9109460007407012000000d40070010000c01c0c408003030164003081c823803584512050041121441100c00200c000d2a05501c00e640c0d00322030310000d0032030074002c100c0302c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 246198165 1250 246196915 246196949
    0x914120d0503011509030c09050a0905030d0207020418030804080310090518240114041112180a030801090b010c1a061e06040504020708161b060507051506030304 71
    0x140050045069802c0a1100904c0c42500d00c01a1618a550302c00103200f00c24403003080180c251550300013070f00000941c0e008940d05540d516101e20355081517007507030707141940042d020302180740034403071000d135a0001507854215254071744002e0020314004001030b280c03034800800140c0218030042d488010b402d0030b0300d0401c480e003000c200c0400c6080105622040510444d420078a00a50341e903542815440018194040c5a00b0094030341204031185c9411030300315856480710040c2801c50009044801126007083c040d9142002815010000301c0907503000c0d1350440c00300f80340403030b0b403007010141986c604490202d142c0c0c003080012510007058000180c1091440250704081201c0d110b0000d001c0c4e14102c4119a006505808030310080020803226580044200000c1005051030b4020300155070050080506041206400744119010300404032052024038030100a50b06030007000c90050141d40c0f41042c1840b80c1592456900d00829030114620168440082e5455404204603030103050003010082002d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 246199415 1250 246198165 246198167
    0x70c0501060f05040c2f190605040b060901060f031d060906042a05040b03030918040510050c030a1a180a0506011b08090a0e01180510060914120d 64
    0x81c555003c0e40b031142c0e0404198903060b510902071010104000207007403900b111003605a181e00301c500ca0000c2c1050046e080e0140078040352030045121640170f0640480c10746054030302110081e03401400c1c144118040cc005207c00c5030701c40e004450a903007030308000904000c98040d40360002d040c0b44446000380b00b10000c00503804000328155024030322503006050b032520141c40d080320b900221095402c3c04961454204141c2c5001d41000c860b0310806001c0d00d03c0e002c01140420070000e0b406103000300c1e02080c03200b80400c101080065480302082607504005508041240030520310024102042c00e81c0c82c0d011003100ca80c402c0003480f0b0036510062418415018114200070f030100200c03501141585000f0000311a9402060b00000b040040e07411030b10011408e0703403108183d4000400040d0801e1550300041861641001c560b40070348048010a0500032410701000141e0301c0040c050780b01303034648050811415400c12000c1c001e440c2c48450313207060740386030301c0c0840e80241d03d0302990585803080801010302c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 246200665 1250 246199415 246199439
    0x3190504050a170705060108010605030307081b060c0a1404030201050414120105070c0317010b120c04080a11130b0915011e03140a0c02031c090b01080601300b070c050106 75
    0x15209100313441c6c941ea6503040741c03422106284190f54254004003c407134005601100100944003242d60035005668a11400500c1c25108030340010700038400081c80c0b0380582e001428840c170b001c0341e14151413a10b03055600017006402280714050580040402000b20343e03881d540c0020540c0b920400801543ca020000205407001c1d2030410f60108081c003e007403d0705541122054142d80e0f41c0c0c1c08031881c0c5481d5061150003510300410044201c07100740800f10302c580301803141c51343c1c0a003e02040c401e140d16020030400001c130b202c0084800642740c120070720b08075160061040c0d132050741c0c0e21003140c5840002c801070303031000c401c1490b200d4110280380340c520049800d41d02c4460b1050700480c0c0b18038155998041001140d010301181400b50344248529811110422010744c41c10380c51541c040380104c21a5106d08200000b0780008415400000042c032908030030104000a00145918614541101503a04407040c00c0345400074140030007100014034094090030300840b0300c69003c002003224660758800010700e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 246201915 1250 246200665 246200677
    0x2030a0606030603020d080901270303120506010909020d0209090405010501080c0603070801050904020d050609070503010c030212040f020109080304030f050d0512061306090f02030405010c020303190504050a17 92
    0x24925091000c24000e1081c410300781a40c0e07014002c81c4044040740c4850910350030010166040052160444007110f000c075008144120642c9140d102043c203514026152401c0c5107080024642b400e010400541e034008425000c55241140042ea40d41045211390086e210f520f05a68218034a2018001040390562107103040360480c00c20346041603035400c10090944002d991000c000b41e5820018080c1c2d281824a1a801c2031000341518a5403103103507a00c60402c0f80c00c5a100c440c2d90800c0b00100594103007801500560355140c13400310f250549114080d0700d0004043c10290035185200003007011a4007440e000e0019050301800c0701c1c0c949540f80b43c41c0c0c0c8140311101c0219254025107603d07070007460144003510440d01c10000e441401d03554071028442010800f19240190584981000505084503c5124200300c2558000350792482d081c2051800d5034a5800710408652041081045044011000f821401101c041c0410542c0780c60401d035103000b11401340540512041002244003028020007012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 246203165 1250 246201915 246201931
    0x7030f031116060f05060a09020313060c0c0b180a030e0a171605010503130201050702150a03090b16080c03040507150801061e0203030c0f0c0703082101050d1401020910030203 77
    0x22030020f00071441a104c0c15606c01c1d030041241e480c11b00101005402659101e0800d6601084020558440b002500c0c24400c8110101d1813100c820001d0103011b0304c4c110342c4080100c8039840342c40005030f4155500e007040a4003038200a071380b5a14440568402c0c1c940341c02081e559450704c28030540ca07180c003074036888030304121100d03907140301700002e0030f540030701c0c00c2e2446500c0000c1e45000c003000a400540700340c0c2c0010001c82e84100c8400141c03401d810003a019100b40a03142d50300042c400c1840c5040903220001a081c00461220500b103107451a601c0740005502441c00705410b46c1703035220b0b844c11600e003041580100e80c2c2002c40401d0104c65903401541c9904885050742c40b82501c004503006110603580044503400140c108100140007107002c040202911503203d9845890703d91540c034668101002071f0401c03991058000f1b44254030000905403400070348019035041040c3d5141c6070000d0b94864048100178100c10540e2440d510194003981550f0000f031001d042001100c8640c4da00034000d51040750909 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 246204415 1250 246203165 246203171
    0xa090204110f0a090f03050d080c0909010b13051f140f040803090406061706010e0a080106080f060709080d140d0e0c030d0201290402130803090a0905090307030f03111606 75
    0xe018070f05c00c0c1180c003104d0b00600584443d240d40078048900040080441d54242003c10215101d41c0324062a01e008110f02c007440c9460f401982c280b00d0b4590859444a40f0484071050030f02c255602c41108480400c2040c10048095005000f1501040c02604030002c0d902102050000b9410030120060100c003404442c20403003d92034400c01d99260354655402d4000d2401040090300350750042c07090001c1540e0081000f4030322a954417910382034500302d812070409a080310141d0902d5400c00c000280d00061281482070701141410102603681000c1200d040821407441c683d0300102c1000011070b0f0b0464040e0005101d4048080c209607607030800600081d0080c815072030307140425031041c402d07980746051070b0f55040d0110741140b2060840000054009901c00d40c00c000d41210b0140b4070241d41d005024407400b40d0b0305c400e000001c0204054099002091640c01d000030001010000300844002c02d03032508098100e54000300080b4014074802c00e94418004000134032400c844000d1402031b0b9110710505041c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 246205665 1250 246204415 246204419
    0xd05090708192d0312060902040602030405030c0d02030a0b07051c05040c08010507201203130b010f0506090d0507030506151f09031202100921030c080a090204110f0a09 74
    0x18072452000c41c0000c10b420f0700820b100350000348200000e00c55034240020100304507448107179281c2264402e90141015900000701004241018000030300c91078000c641c1c984c21210702350040398482542d810003d000341e180100080e903e602a0099072264140142000c207515031400c1c043d07009141c00e0f6001d036414880504005844c07a81401811322550030707a9036020a01240581c511050301054014103028001c01c94420300080c411400386105100700180302002d1509410a040c1c41001a04010702c8001010800c1c00b02d40c0301c0390100d070b980c00c2c01514a407005080d036042c42400c0815540000302940a1941800404004064100e40809080328840e00b1a100d80080401403c5058181004035490800070400700c0d50031000118000034500554401017805a070355000c4075500c3e030046030000b8180100e010300f400e0b0307008010000310f96400c0400081c6103405001c0d00b10340c0010035454699803103111820440d100c40c1c10108071429030070302417034445001e1404d02c80c1b6600007400d031100141d140000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 246206915 1250 246205665 246205703
    0x17041809050139020c1f090602010b0102121c0906050a1104121103030c030a09170303070e04020f0d1406011106130602030a0e03160203100c050d0509070819 69
    0xc1814098032440b40d10560019a900501e428910316200d04107600850405c4030752a21001c0800b80b90f04130b0b100180705202a074040c05440c00c8002c1e00940704680c0b40561510b0b407030342c0024039000910180160192903404029a05501100340e41a00c1d03605410000a0000c002d2180c0241d8010b8100005c2408215045900300c0349901862040300380000701010140701080720590051800c0f20094192880e1a205040280c41e540c0710008900009600c10010800340c00c0703403890140c5902c1c4071000386240d4103181b0b50050040c05404480d0b407003070f80d000810060f4801c13400c0c12102085003103801840943da852007041400720045500f00e000c540c11000c080740c035690118441d84100c1c011701c0400408007a80d01d40900039003004141d02030f9079580390b00c0781903201c5040014205001502d80c00300e45805080c414542001c2200c42c0c1c139400c99050503114243c050b0050309071400d03800c42180000c0c07643d4a07103d965181944e1648401894015580780e4595540900000401c59004001c4d0f10001cec558541 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 246208165 1250 246206915 246206951
    0x8070309080f030a09020306070216050414060120010c0203030a06080c09070305060a09060806060117010b16020a0902030f040c0503060106051206030f3403020d170418090501 77
    0x800141241c030100414801d030a0800055a00001e0031400050b1848040e4040f030710b8444161001e0f03015a014400d0f0325139025102e039680000c3d003003c6d01c003444110316600b10344800c48400380400d8140244100c1464000024902040b07013680820028083d41c5004540a5180c0d4400c1e681415100c1c281400402c0005000441c00d02d0184003920024080c1d4851030110024078028280d0f69204258040009a0700d0340c500036940502080030142003603040000c005041074082d2616070f00c00c1d03051a001042485a920b0555031000388082e81c09047c050340d480028411403258204102103031001c814025031603480c125440c452403044000105003600c5204050343c0706024801c4200082082004d0441c007034081ea0015080000641200d084090750424a4201f85040d4112a02d00c0528941c40440d45040c031003250004440c101400fa5090440d0007056400d681c032000906a80e601191140200390b00e14211030080c1200e1000100d0b000c00c1d00d070a007020304031000082c0e84560030a50b401c03150201450b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 246209415 1250 246208165 246208181
    0x102070b070b010e180604030503010801150807050d02130e0106080d0203090a090b180f0610080f040611040f0308091516020f13110d06080610140d05010903030903080703 75
    0x1040d52403480c0c4c80c0064094815100510348503150b420801041607405d410080d6902588c802d1b10351980b04d60509044a0840d0f0400c200d1400b011640c141c104a02c03030020a80400781d5000365030f082c02c0400280040307840800c81441051203c3d160691301034081506503c050b055810103401d68015200d841c4089a81c2d01908c000654042044641040000481d9001440300440502025102a104601d400d0300440c1128a4038600d0350141c00c2100303d00c0d01281213000c224050030004500d0410b00482c12000100810041c81981e40c1c0c80c04d02e020305184001d54008005100603a1780040d1a45004001900403450582c0150301c2281e58041d018100d4007910020750314040407030800c0015408001c0e480c011a03410391b80180f40e1820001903407015000c7d205280c6011090320f941c0d00004403480040b00c24541c80740d18071b6004038050041001003040d00c541110020400c1220700f140d40d01c009051a61203078001020fa610b0000d0000405405401064115010f500d6000365030b6034006095007602d42074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 246210665 1250 246209415 246209423
    0x309080f12030a09050303040c05011215030b0c12041a151f050904090c0f0503010b130203090127030206100501020703030c080909100f1509060309051f06050102070b07 74
    0x2850022000101c1c0d24041d540c0090010000309484e00b541d200c250440e801a2000d90300543c03101414410b5581142d00c10895014034981041145140400030072030f25124040141103c40840101d600801c003041a04c0c032030803071b45d5012280d17814545800b00311013100348202450410b00200003400400c040c00305441041c4c010b400f907002454104440301d0343c4600008a5002c0c01011700a01c0c3c129201c0b1720920720740e54800c0c44c1d0701c0015030070300c03c000b00c024980c1da0100740301c0e038100448512070b5161603101d00864001d8000142c1c480e05c401c00540e014041042c950078540d071051512901d20050b641c44e01c0b0300c480c0a0b40135100c2e00d482c2c0005130b807907080d00b601070503016a000440c1040000e2150360b401000a005180550404501074006480241c041c1e408000000e0085410b002d800020038010300202441c00712414070400b010340107422408030f407081c50181a96141003400384103091160b402020050510f92507480b0102134040b00909080c064a401407280c41c5001c901c0740a60000c035106103401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 246211915 1250 246210665 246210673
    0xa0f05160210020a0b01080c0f0406030822030803040b0a0f0e1e0705061303020a0f050f130b0301050901060914040b1f030501140a0b0d11010e04110d0501030309080f 73
    0xa56028001e003540b0040c10242188142c041500210300c60140003400380240314060b1840d05c1d02300e401c2014410074601e5281c841c9251030000c20009068108a030040e01e400502d00842110042260302d40a16a9002030084e08000042008100e0341c6e0307100c240b00b4112038008001c0e440350a0454000c499548041070481d501180c03400700ba0501c0c210b03c0c40201500384040340c00e0316407510007154268000006450024190300d40602c02c61038442c00c40c50181004940340ca248514041c0018544901003107124001e01a440000c11b07651302c1c0d078000850840c805002407004d420400840c500071b080c9442909512880d007500800b0400341010064061904110b180b4055102c45080c00e641c107607040440d884074600000c001000400c203001d500c080e48803002810303c50740340c19001c1c2000c0c0c4001142d0355100d40354200c4078400007140725201c034003000001e01c4d001807090b4526022400a041c41c0180c1103802c0004242c4c10320201d1280c0129040e24482e91f640414581c0d24400c990b03480928200104483d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 246213165 1250 246211915 246211957
    0x1091208061c050606090711030a0507151802030f010902090c28050c100c020a1b230a08060705030a05061f030f05070905010e150c06010b0a0f05 64
    0xc4030300d03491a088030000300211840c2a00b401400042001141d007210a81c01050800845103003190a09902c0701146c01d001d501402c140c0f607071030349030b124510f10903080c040f01150711001e00c8100300705000b0710b01507d03504200022502d0032080440c00b10241c200e1203481810b6280c3d11040041c001d80042545c090404945602d502e200e0542e10741040e003074944034070300a41c2c415a010161042c000860100c0d030701c03584e5a41c02509200c40c146035201010064039811300240314607481d030014913400b5140c1c0104620a6200c9600001c45140c40c2e191b00608000c9240b8503d1760810001c80003000718000c0484403a000181c4d2240845e0700c0c0d0303e0484010011840500c00148485800d420282c0c0c0080c00030001864003044500c00e02c40400019a03175000a580c8240b80c03e2a90440d10449802c5074141c103000a82030300d0400000c101c0501c207034440b07014103040c00400981c00340060580e1000b8a400302542d000d50703101c01040743d450308014080c2d80003178281040042643d00603070849010700040e401380f1248603 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 246214415 1250 246213165 246213167
    0x5010e0d0b040206070b07170f040c0302040533030105340c0b070305010305010b030609070902090f06072607151e05070905030d021b090402060d060602100608010912 73
    0x3000180b00384d8001c0d4042103000d00041d09210380c94440c42e03150700c40c41d04d003003012516030320300a0703004004200418211082c4000b1441080030b01c0116641103c01283c19591090700b501c407510307140d181d08403805a02025440000074000c178030404200a03802000301d5a100f510100d241e02500710344402d6001090b99a402000e110403100203617038a10b040120200d0036075505e68642c00030448140c80060b07620700c0107208001085c0540d400c2c485080b070040c4920305040030305d00d031601a03900c61865540d40c0001c0c480a5500d9400c558202d6150080483d900c917280e41c200007007030100100c80d040c080000c480c05806401c9031041070743c1910360040f0708080205801010003008000c0a440e491440402075229150503115009183c4905130640c0e80744503c40c5420145840d1031100b0203c0c90039500700c084090f40842881c8500b600b02c103400c40305898181c4490003c0784052069600b01200e540c00c00b038000c200f25400182d074011514280711700308200c1d80d4401c122400c0f01c01c210b9005005162418802d4209 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 246215665 1250 246214415 246214433
    0x10632130207020d0b0a06180504030e0609011808010504060501050109140402030a090f050708120901171806040b01080d050405031009030e03010e010f1d060103030f0306090e0303090705010e0d 85
    0x1a1020300080602c04c06911000d000e158201e41810040d9111b16003408141c44030000344c5001100042c1c00e0100d410265005807112403041c4041e0f0007080b0200704030402e0383c030480f510aa02009504090300c107903100c00700140648012941529941d0a0800005165214482d00c40449a5072400080350f85841c0040002070b610143c10703003c2140d241c6030700c0c80100c0e40d1101741424651251005007081c40c0342071810b6060034070b841c40b00907491100744a40c590700c0e43c2010315640804540304240b40ba55036050100350340038141030025407141c41180200810000150f00403810b840000c421221107035403517242150750784614041c1c0da415070460710102d443d40e103c0703030810300744103209082102c00352002c000800d003110020706503c205070f9100c46a40c0e51140d4540f10310303038880030b03001306800042d09005070951341c131081884018100100a40c00b290120b20030b5103c00d018001d05102406081031030030819507640c0041d90072414501802c00c00103001c0d0b0081c00640310860000d4101415020991a4840c407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 246216915 1250 246215665 246215677
    0xf010501062321010b0c0c030606130b030a05010c0203040305070b34150606140f030105090a180b01050111010c0e01230c010c2003031303020c030106321302 69
    0x800014030100410483c0c0000c101406040c80340c188903114000c0312400b0b460803e001c18564080e4112500340030300d98640680c002680311441c40d01041542c0440040391500c0c0040c24007510651038801001c1c0807550120080085a0041c0c040315110f03034a5a07114081c0f8429401144804691000529500c18054070350300c10011070303005001c900302c4d100e44032682c8080c503038500250a650f440700144100c0e904103407000d009144d060384070303030410b500130900840d6848103000d45442185404002000c0003019000316441d030300d120251560904451804003028902801385901203001200545c486000c14490110b003c1c03200e68484400c2c4042c0f0006640340003164420180b614061004c1d0b210400e0000020300382d592400d4000500080b00c0c0c04020304042a82c949050841c2c130f9546192a03021002066940002c441d550441d0b1811041c50103910b84110004a60b03059400d003a000113821081451590040c030700448001540000792040f0408241d452080b16801040b54120507500c0b1529805400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 246218165 1250 246216915 246216937
    0x150206190e011d010c021e1506030709111206061908060315040503131e06030f06050904030e1c02151b030d05040203070e04031b08090409050f0105010623 68
    0x74200100400c460240d1008a00001141c0d110310356885e0159041101b00700d03000201d10070780c2d1540e0301101440c4c0c0326940454038001c80c1e0440d10121740c240e981481341800800c0d6207001040842c07658200081a81c00c50445152600114130014003541401800ca03a00302d01001410101c10545503c2612900000380000e07415100b051500c0000d80b040104071400b940c0200011501e5090341c11015100745501d402c241416001c40c0300070600e40202e49607203804d460322414080350041c0c0c0001500018500e44d48042c0c1d01038051424002810780103c400303005040b05640c40e02021704400604801d45a4001000b90000c550070031605020030080d000d0030000c0d0452011800d1032242e411481d1450f0040710103040d101340d0b1201407104601d805c2281130001c0200d1090349110703103041d44000d01910004801c420b64400803100178810460144200c8410b020024410400300f0300c80d00f4480d03a41d04218100360015880c080003c0303a070341d01071010502a410300007000c4070300c8003c040081c202500240c0c0990 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 246219415 1250 246218165 246218171
    0x6050307091413061b0903060b0d030c0311030d1b02060a1104120f0b010806100815010513090212030d0f060f0510030902030a081c0c052505070e01150206190e01 71
    0x4070171100042a248040e080c00d1359002c01d22411805e245044950001086210308001ea00d80070010703401c94a00705500b40c0600300704411202c1d10000c5402e40c821030f55004001840c21025552401e0800001083c000c0c140c0c0c2269240d5507000c00b040102c0e18855494202d2110070b0108200d04500c02c941e0b0b1030158802d5032401606230450356039601810007a00b1400403500110100006554615295001001800c0083c03000403c1412100c00c2c000d0180036090103440040c880c0441e042258002e06801e540c05004104894200c25039280c4079004882143c1d8040d0800d0101c0741e01c1c4420b40600802e4030314292040349074a00c0c3c0001c0160b003640101c00358040c1034070b4a4102d005680c05000001c20180038131134045c0d480f010502d41c4480c240c0d14098101c811894121241800d80c0c4c0030701a2844040e400102c0e206103000e50b00d03082c54004a03028010814858800d02003049005401d000303040380c10400c05040c61075501c1d0700980e00c60704200c03522010b030a0031150030003032000785d40c01086600c0e03950b01c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 246220665 1250 246219415 246219431
    0xc03060e09030415051201030b04080c070803040504180c05010c032705090a0c0804080a05070c0b0702150f030c13050612060108060409051203090106180605030709141306 75
    0x60850120119110381c0c498001140c10024200c20041d5821090801d1820a01d4034140301b0300343c0c19860060001a001140000c0050108a0014102c3d00741151010490780a00e42c2c2d2050320b41e581d4001d0049501550800194103c0100d558840d280034617408100c0c40e03a22400d101c0110340ca1504450300340c04201440700c000c0064030a0f1490b40614580d2030006110301070420301030109085000e060f000f0340c246001c1107541c2090f031180e40d181c0c216038040f41082e030320a583e17481110759000b41c5031b016000030100d0314000b0f00b02c1c0501004000491090314844400c0c01e02c0010b03040715002d070101d00802c107407081000038050200d11004000c1c00c052440c4c505034154640c80814000e8105520450070420720400740140c642e040140140c1c802011902401091240e90f201502e55441040003c0e2084011004c01c407100405c0d08210090301e00740d00e940c0752242d11071030203002800d21481420300a00444901103499141405905400320207008801d0054890041403000d0003104038069036210360303810b40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 246221915 1250 246220665 246220679
    0x30f0611090a0e070f08010b07030309080d020c0718020415140d020a0302030403080903130303030902040207060c051207050a05030712060807170f0a02030c1c0c0306020c190c090c0306 81
    0x1000700a0020f20000d05568a072005001c0d08810040840c07900b445400300041000c0c03040380003280c090703650600c1c011031081001d1401200354000e5043d03100b8405e002090f0340e5400c41000480318100c60b1183da11141c102e240a170000124440c60280c41724042d1041040c0140d24003e0240704a82da00741c1c21901c0c40c3c242105d100310101d801600e03840700025000003d1205060780420140c0e00140d40c200a946805d8080c0c81025140d803031480000c0605444000200940d07035240c0c191035a05402c890305210305011884020419407040168680b120000800f2a00c2c003481002600d80650568a0301c0d480d503116a8403d8800003801c6403820056a21900d01254183c4284540e4004211254100030030a29151565040c1428034211004a60011070004050b0b0703000210f100b50071a00351190003104c5040b03120b00b4050b503031906003c7d2008501310400001c101c03465000700361501002040e034460041a61601c8284000190b0190826510103414011190a903200c80102c02d00c6040018030190b44001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 246223021 1106 246221915 246221929
    0xf19081b010e040e1b0117040c1505160f02061b030301050a0b0309030306121c020d0e010309020f040f1d031e030403050f1c02070b0a06080304030f061109 68
    0x1205d10031607402070071000e2000c40d4415103c083c03403800341850840c007482c41c425030b80b030075074032040c0303416a180300d2000e661411507036003078144034140d07030307407540100c00030061010707680310408100424002c0c04901c8054038000a01000e15103c0d032400702000908640341d0701c80e40d188001001046034449001c0700b20380d40500100c441e18100916841703044d2400355051482008409075000d0046e003242c0008460550403042d9070341c034603c0001131004409580f4403240c000c0d04980c45258406a9113400c0d005901040340440b000a0000701941d18810290f031f4002c580a403c2c3c01c00211a0128800b80030304018101480040900d0360825a1b4000c206103d0720100c2403a050000c580c1004201c94072400e001c840c98204003e54591406080c03145039807400342c40040030b0313910300400007414400100540d022247c2100c03a1074100c05080c1c407075030301070a101c00004d4003041c001c01c00c0b0070040d0399904c = true := by decide +kernel

theorem cover : BRFrame.Cov 246043165 246223021 := by
  have h0 := BRFrame.cov_init 246043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 246043165 ≤ n) (h2 : n < 246223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
