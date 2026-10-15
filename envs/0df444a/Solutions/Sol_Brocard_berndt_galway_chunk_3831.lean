-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3831
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:48:41.296695+00:00
-- url     : https://prove2.me/submissions/30242169-473e-4d6a-8932-ad7d33c56f56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 688848920 ≤ n < 689028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 688850170 1250 688848920 688848929
    0x91a01050906062505030d0c0e130b0105040e060301020405041e0e120405120312070804120905060919080613060b06180d0c030f120f0e100f090b0c1501 67
    0x1483c044038050791030082440314551000130b941d071003c4142484400d0049071455000508104449001540040d09103101c0d1207003d0302a04240564040c0300b035040c0316034043c07254140c540905051070000c0d088500e0030010030f03a41d059502440001056110303130043e840d0004070300110700c0703240700003111600444507001482c000369807100c50000300607101f240c100c4003510720945841102c1c2c40813907106850352088101006000705400c0400c07c46603408581e0f80e0046108002c02855492001d00c11500d4034814050598056020004500b5910745106202e02219480d522640ca181d594003800381005d0301110b20100d40314110b800c0c2002c104e8a4828003240c94800c031103140c144000e103030400c4092483c0241007805400c07001d01010901840581600045034485010f80038030340180391010744110304513110341c041604290307420b00072400341c81d1500d40460040c0000011a4101d4011941404035503220010302921040200d809005040184041d409601c003d09508411480010100005900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 688851420 1250 688850170 688850179
    0xc0c0c0901050901050f0a0b0c011e0b032d0d020c030118050606040e0f031603080601020d0e060f09030604081201540b01230d02070303091a01050906 66
    0x602c80c6a0b80d41c401c05054540c00e550840149a034a40454509103240d0409040c5640228a02201d035005420000c4080c251400d4150350142141400c2d094404940d88240d2542203400030030707485103004140d44010000400c2d0034420000000c4100c0c2441b482c4d61000d0016000511081c0a0341002d01030791a0189007100019a80305494651350b4a690340644014441c544440c0d000d4851802041045882c03144041900d540301d11040f00c82a242034144400c8000c2010040080d20540c00441c4c01c03400740c03c40362105402d0390645010440b459110115005c01d840050003180d06544040040030720a80c450ba565a98a0020041003241c0c0700c81603005003103602c985140310580090101d441100c0000b0b13020a00c2110179000103940040c10a00480580306000c2d080800e8070110540100c0300003502a22056007000500c070110710640d1b65042c03039250040c400c03c046210b0601a80c02058842c1c00303403800080314031003581c54880c1406002b042480c5080b4101c018450392170300048944c1c0000c0100c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 688852670 1250 688851420 688851439
    0x3060f1706010509060d0c06050d14061c03091503020d0b150f1810051c0b030a0206160b010b07140d08011512060b04090f0c08130c0801050c0c0c 64
    0x4100c503641e80c00500940e401411903201084036519a50f076031200290703105a501001c1520762800520582005000105490422819102c144050b4034014052440035025140b184010f40034031041c20000c070000c40410407000e600054409074402d2952182c1035a5402503038440d6076030a810242c90320032680c0351040b08030100c0b03a03900d0f4140340d040ba10400301c10011140c58840c0070a01002d0785010b00581600842d004103440086603000000300303121070f9101c2d0381d642000c0992001c501140c1d080480700e60164040440b0f14050300e01031000d8039902003003107860a40c004a80e0b5509504402c20b0340600009003000c69980c041008186040f1550603503040101010340b210b03503000b0311000040c42600c841d04010003070340085500c1f0f40380300d0f90016800320041c005640d4917140089c03194030a100d0400f40c1460404005240100b501450b5001141ca5803404102d4441e8404056403000c4800112400103c0410001d9990400c1c02040c2c03141c201562450740b01c895203d08241048560070100b403080c9001e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 688853920 1250 688852670 688852709
    0xe01050705090108150a180c0c0302030915093606090103150f1e0b030c030a0825050313060315060e0612240d0503030a020304030903060c03060f 64
    0x19200484024030741401e094030307240b03462100e0380c045d5500103030400c00103807011525040d20030240340150b400b84030402401c55003481c01c40b510201c5e8000100160000c01118005160060850346541003481815140903092400501000103180d2460740840d034280c424009031030140c000b0200112540e210b0542441d00900085c039801d03050000900158159040c0040321595078428203020b101080c040119155030b032044e4060140c0300642040c503034100107000490342400710f164035100b0030103001081d9800301c940d00c0790842e4010800c03204003d04991341804111101800c0d90340407500032030146950303910300c6100f082003000641040702031504000001c8045018916a1401c54800b4038113a4294841100001c1c2c99110300c601c25000c40d006d2005100c5000c011000613006074401403140c3300480c0082060107905207000c0f60140250f0000e0002030384403441d03500210381c05031003444d0070052030b610f9690344000c40d400004c0d03440000307a90718028030010b078050001c5400382c52040310340489103101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 688855170 1250 688853920 688853927
    0xe13120207120f1502032502030c0303040f0611040605041a04120b0403022e0c1b03230301180501291c09030c060506180106050a0c060e010e010e010507 67
    0x51075001484000c80303820140c14000f0481000000c034a104c0d40075580d03810118440d030300011031194400d80c145181901c40c50394a0000007181e0722b002d0200301450075076440d52502d0019000c3c043c0c0c1034662a45411004030401c400600400180c012521500e49840c1420782d90302c8075041d00d0a0698490504100502c21001e4011003000526480201c0c2c90384c82d940e1b890103d090110041075003c01e0414152065540000d04812071082c0c09449020001480c48140458800e5103210b54403180d903084007030200119114104003030440d90f050080c00041280444e0000340c2d036200741c2c402250a103218003800d001741500d000c0d140c010216009000042c078a42140302c3c2a6217000b036101c4881500000b2001c0c90709084440303662141007040b03003c00c030840340c070b08000c1c02201040608030b640034503142c009051032a06190a01c12042410b0b2546d610b070303003003503400e40e0b55a120040190601454905400c0090b600c2c0c00750380c0d03401d04c1480c0042038101e00150f41500f524004c00a18032035034100030400814550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 688856420 1250 688855170 688855199
    0x1180606050d020a15020c09070f0824240f0903010b091014010903020307030303020301150c080d0e0f06100524090f0d05070b0304140307200102070e13120207 70
    0x17141c0380c00c8030704212011706901c0c04410740c401580000d034007020404480d4000c450b404805159480308038041c0c0e1406904203032114580b00c001041494100b0180040c20920b000315002c01242c0000903040c481d480d020202030b00b000c1c03000e1210000003e09a4450b08003070240707030213580050354001d000e42802d41c900701c4840c1e0280503260a00001a407681c0e42a8407485040c0c00a40d0040c040e1034401d40c982c240200654030134011103271003003001c88034048901e10400e003a42401c0d030401489030402d40b240351548007400305101850914800c0f880d94003420b03002440558003441000404109961400c070a00442816004900300c111500408410a4144900486014a2044400401ea04144000556513141c15500940240720304000400c052003000001d41c082c5019034204015807006e0030300150b41e4410010b0003080c0740d40c4490f200740d55140b82458031110b1001401070740d403040d80f25010301246070741c04ca981f13440440400f00c50205118454002c6001032801c1d10180451505058110030f4482 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 688857670 1250 688856420 688856429
    0x110603070c080708030103050705060a05160f02130507030c030c020a020d020d050609010b2b0201030b1c0b04110607020d0b09070b04060509011d01020c1903020301180606050d020a 79
    0x503215510a4a15516240d4850300140d02d806035402d00d500c3c00e8009010450711480f90f800003260703a1500c03a0940d0380703a41c160b56403940350840e000d00020a208407504200d507180f00e0003900c1c5005075185014503460480700fa000040368038122310020142d45400a80f070090520344000000d00d242d02055070030090b0b8040d900c8510411040c07001ca56584206040501107000300014010201230641020003003420860742107001054442c0704101c9030741400e01070012400204129001940690403140d00020010196030803a1507121070549281103c600440701b80f030342c3c28100001c0110000c00d83d110100150f0300c207818034507a6800324909200e0700c4000f4014070740420002c0c806030b030100045c401034860104503a0302c46964010203440c58002c00101404555032140305152052b2005501412480507401000514165800c1c001c5410600502c01d660310801a4003102584090044020040307003101012000c01d0350341003010032a02c082d001248200d051600020246e0384442015003030380d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 688858920 1250 688857670 688857679
    0x70f1502040b0912030c010c0c03090f050907182102010212030103020906011d04020a0e1201050f0c21091501080d0c0b0a2c0d05030126070b0d05160c11 67
    0x103035421851417450041510010080d0f0811800420355a40180b1600b000c502c280c8400e04191f468002101a16000d402096041880c000c0000d80062041c5204518821b001a07103c2402d62589607240030303400388014000000c03d0404002d030455904208180c13280216104541c119419a400203a0605000d82098100001d40501d000c1c60140c0d10080045000020070440d528121010090920010002900c0c8100c06014085c058044107019040c0b18000740300404c180790b520704441c125103400c800022210350542c920412070103103800641c18010801440140401e5200e65034110302c60384160461001c9821201c640d1130520f4109404014840d48210484071554609103424010140050246101c010b01140f1382c3c0b849410303d00728095680302c0b2003500d5040c26000b00940701d901c42807240896110315804442d8102c06156154090000c0700800d4034009640d401242245802a981d0800c419a45038148200e6170a0b51298070304010140c20403140480c1c2d162214581945580e8425024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 688860170 1250 688858920 688858939
    0x80c0c0d081605070e011d0a09030909180f05010212070215010e04240902040c020d02062e090203060a15120f060503030f0c07060201051b0705030906070f1502040b09 73
    0x400006106000103041c170040208595a5540001c44072612200b000d85007210401c404504030f080d86024851409070151a104002c9107821110401443c403c0c0d071200007a8010751008000840c040310408505009800140c0c5520303d0740c4404001000180101007950f10004820f0341403281c10300340c241110703241c0c1c245040303030b035030340d051215000c804152040010f000038100c08103101003550003401c5041c001d41c1c0030451584194010382e039611108000002617403040c0d0000d9440d1862510ba42ca00c031882007050001d2600d040001d034034440c0c194010510103a00882001540d05002207400c0040001080f09610340a281401a008240c2c00c4c040ba900e190300d90502800d56061174105100420002c6c0482e560f036000e2501407a030300e07081042b149240d03000f41400014083d1050290500403540005103104060860388030050b07036400080200c8a5000030300900d034203980e039a0058450300c3d00403040005011000d241101680d072405030700300c0d465407062209102400c1c0c0e00c02611030270383e82903940c1c001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 688861420 1250 688860170 688860173
    0x80112110402040f0608160905180a0b03010203040b07080a110a0806013005090106032a080a210305010602070909060906020703030b031902090f071b080c0c0d0816 72
    0x19120303681203040b40819607131002804650201c079980c4500440000450702088540c4111034000030f503c0b41aa02041920000858002480c000c1341c001612440008420308807001090a98100b242c0075200c03e01c914042007450780d04041303180c2d0701c41207a450030400c4803c981082071981c050014290108212240050b2859018011740e08281286c14070018281000c15101d102c40b205104180b07030b81ca4101800f02e08600c005014a070283d0707520040b18105500c0c803c43c3c80021298020318503100c0d444403540000c13070308070901620900b180680d501000e49030611110200b8040c002c040c95082500c0c0900400049902060603c1a500aa034002c01d1080203401c00c10040c040015026041c00e1000450303100b01505a800400440401c2d01960301d0003e20b0b0260b03491652070648040d40140c441000500b01c078070b003140a0b6511003810f09094941c40c085060611044d45000b10494410307000084490a0a00801000b1000c260445450310209003c0d42d03019928016601345d9504e118020a4140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 688862670 1250 688861420 688861429
    0x11030304050d1d0310021c0b1005220b04090c020606011d131a0301180b0606070618060e0f1609020a3c03110306091503010c0809070608011211 63
    0x7254020010200c0b48180504e0074039030020361220050018000503070b000114082e1f494000c030400414010300702d428120003900d00365400d511041000c0c10502d496109400c00382180d400005c040c012215901e0713211401c0140b810f080300c203454400e40566000034104006070381c2c0311201e140749c503005800400d2401c6200e8017140049220030355a52803103042841241c0306c11030400c6603000d080b804500910800e80c0c20705180b04502c0340120040c1108034400002451420310000400d516482840001114480c410b5500b00300c86d0914011a40c280d02c2e1814160b108030200021022101e0740400b410300f01c0c406400100b11707400c080c4103501500b0340208422010b00e00400b900d00b2141200d05a580a1a9465403031403420054640c140f0301c1014201030309884248079200329000e80c0690f0500502d03503141c7d001000f07941400180700d000b4a0008020500313550301c3c00e0241c4490388030141c0360550203041005885051010300d80241c010460b042e001000a40405520400204e800402c040200001007002c103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 688863920 1250 688862670 688862717
    0x100902030604063605072903060d0c180f02040803090d05030d09050303160806010f0e1504061107080c010203220e071e0206010302061b010f0501031211030304050d 72
    0x841001030761404100c14001500000c144031740700d2403e90f02c0164881a12040c0401728003203102141340310200e0307481410401402103400c0700008041202d014500e41c0d40440040d41038000007a10b0000702641001000c19002d65005480b900d0001d508150404031099030b40e01a140c540c520035520800310009010080c007c5903610080e4020500c04a03159040c9a650796105450038500000002ea078200006d20642c8168080c2c0f005a6502c0d0710074441c28001c40d00c4075021410140d100b055500901469150b11004100402c2161a80125082034103041d50a1228640c06142d80c0d800850103580c2a0380c4c0441121019008401c2d03020000c4110340310007000d0000c640192001c9041c61050014440e08410001e0851103081514103004114501c04c0f44c6600003884006e4201034240070b6071601804212504420811002c00050b40300c11020441c002c3d40c600303910550b4400103000c0b203d05080d5100c0d03044ca0019070f680c4001c500d142010b5641c1030707442c012440c01c4070401031540701210380580c4200d41e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 688865170 1250 688863920 688863971
    0x32a020d0c0204141510030203090a080912060712060501020303100b0c03071208061e090103120e030313050406050105040315050606191d0f01020601170319090810090203060406 78
    0xa0601c514200d9150f8860b00070203205d4070320511590010320280c610900071a4800d0300008090002c503d00c982e1280752940102105070741c480d00c912123100c80039208000188c865626582c0341d442c2010880242000c54405402c0341d41150010001c01101981e1090810308441d07540402e6541c500c0131064060031401008001401389446524813501e0951002d6103501482080344e5030f030700111040440d010b001a841c60071581200e881d02c01080410300381800e890410f00541001c041150783c80000a045034070080c4889000f00003202c05200d242018030400300a0042070078080d16090440e02c3d40c1c50190a940c1c0003620080d15030001481949400055078090481811755101501030100080d200500110051441d89105203880c0700e10b11b81304203803050540c01a00504116403c2c0443c01030000004584800540301c10018108003201e802c4121001c0e001a42e10300310780f181001d50041c01c081ba01700c800000315081c0303000c0d000580c1e4046000ca412079485600000d80107046041b465008910418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 688866420 1250 688865170 688865201
    0xc0a0c0503030c0706050a050403020604021002070f0e1f0f031203090b0123030d0e01120605032d01090c0b130b030c040603050f0c070f14030406032a020d0c0204 71
    0x140040441042c021304a001d103c0e000c103220980e0351811040494000700c1e8040d005a205c1004078025042c02160040e030f0310094416a60780d01e07110750345038a000d031140d4060a50805100c00300490040130b00502c0d8942138081d84a09082403401c00b01302c140c00010301010b000300c12840b0480700201d002e5031288040c41d9103d03c0c0c02075990f07910301524610409140c40b840c0560b0032042c1c803020f00c1c0b40100e64094040b01648440c0010b0610200448415001022400e6510340c4c1c0d0b6804240da503001c12186080e601032a014004114900c9030010142c0b1880f80e0810260f0b050403a8400058008a5507030705030b41c1584c1c8034585810f00380c0c3c80a4160401030380040b0038080008148445d01900ea00140305a13a5581c03402d00140c2c41e9800c1003040702408039400081950240f00d502c00050130035641d1000d2a002d00d1a03441182005245c0a043d940543d000401280d56411120659108041560302070b6880715511810410700060203500c40f0310000a140400c040c50035004c08650712940301096205a640 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 688867670 1250 688866420 688866427
    0x150509041109010f26100314070807090e07090504060c091e050d03180b2104021305270d0f11060f061c20150904091a0411100c0b0c0a0c0503 62
    0x15019281b4651400180d91402c0901c008020303001d40003070550110388002004204682ca0030451000030b1a00740b1004215004418000400d0238260242c54002c0c0e00400c000a600303140d0b014003800101c103d0703004501c030508452940c408a01c20b022075034104c030002d83e00955886083e00d4202c801d541c15860605500640e0600401d0800002e00580212a02e08001c0d00c540a880c004082c00c001d0100c8000707501c60713007406414640c8902500f1860700461001c0c1c940d0110030380d4203405100c41001d035071480d4142c0e00884460740540e60082c09110340365000e0524081c004400035915884001c014504055500b101000c600e09803117403035a0180c809aa10b00034410b00c80d682c80e05078400011090300c800c0389007125200c5c1055150a042130f40040d42040c2d5241d03e080030150601000c1c0000c25030503140c002c50078052460044814000501c11442203c21415800460040260b074456858400c0300700102c10303100100144001c294184c002c0d41d21039201341c40c0d10580a00321034508142200518501010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 688868920 1250 688867670 688867681
    0xe010f1a071e020901081209130623040f0203060f01321305060a0207030b0601020a06020f030f01090c2f0109030908010615050403030810150509041109010f26 70
    0x60300104400b5100f100e032442c80c1d076070301d1580680c0c0740707800604103414139420041c400882c606a81e60800d03900c80140d000c541c003580d588a6542d410b80c0c120b03c000c030b6202401a600228541803003108200d0100040c21800d40c104280855000840841404c2c140700404030000415407250120394454011071032580344c075000050401010381c06c641c0c900c0041e510f0070030b00401c003441c11100752910200d00f03500a1080da444d45d00c950000b0140a4405415409a880c146002c107041c4d00040284820480030207035241040e01241421320016400030170098509513025182c45d5112500340001648000980700c8480c4010ba415008503008035440202e601e403104040406800801c04000c0ba46d00328000c0000a40d01c15445501c01c0e015a0190000f950420052002038020001d1a800091224086601a888210f0700200c0c4280d00810380204170b000c00d14510303600e81805030503011554000364034207040b445070000c1c0002c0c41030350302c80081c400080c1c880141c1e110b998000a0b250040f0140514040c01d20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 688870170 1250 688868920 688868963
    0x6041517030705070503070305030a210603030c140d3002070c17030a0503160201091502030a0c0507120f051c0b10020114060603060f09100509010e010f1a07 69
    0xb54049919000700400003500d480d0100300351044035081006149800d031003c10860303094105842c6000001100c1d1420b0340c040e0744a1141d440035504c40c1d111b16421282c42d04041210b07070548000c1070210351194254601056000c080130720410241c2c0c00e2a41084d041c0c80b0b80585010600c545c2c5403101d44081610002c1c0220110f00100f19201c070441e041a400141c0c1010b030b01d1341305030401900403e030200301140101003100005180c181061000088215540e611010942e00e0704d03400c129950b8010003404041c03529441010004819810160710b800c0480d80d400f44c003441007806250510450a07a00600140a001160204e40040c1c0c1101c07038002d8128040402000d00f0119030340100c84018541408500520030790300c000000e0040020255034500070880e0a5000908054000b0101060f558294503500c1c5a94040c10809210940325070408080c0305001205900c410540d00c8420010000340c0707450f4041002740e40100f885516084104560b4080d24491840c0083c109410f42c01c808440180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 688871420 1250 688870170 688870177
    0x604050409060f051303050703081e070804050706020d09030b1308030a0603261603020c060403060506190b030403030207031815030e01020301210f0501061203030c03060b030604151703 81
    0x190703e0300400c0396441c4c1e00d0400b14050fa42010003130104100f0030030340c808240208021a4412840c80c60785201e807100100044c0110400e0f10004086a80c0d04140006c000c030a0004d01c001e09079500c0204543e00c10500d008240c0056840301802c502c0e10352001c1401c4c2d8885001064810ba04271100c10b580b03007000031200b070003000944015105014800075107191560b0040c0d0880d900c8003a44a42824410400141181080709102c00c40c190b21410a02c24541d807140302c09440114040c4074002940d140c031609202c0440c1001c450018440180304042c0000088142602e0b006a0140b40040c3c95145070300d400c0c0e51b140ca0540c01c4060300e2050074000aa24000d1007409030040f40e46660903c03070b4180f045045400d038002805003045041d1024260348402c0e02c4141c600714081d00660b002c8420442a44510f801c54a09400c0b50726038180e907224020a15416015100ca071001510b0200185031400e02480742d14040a442035108c2c9446942603800040924164009896403120501004034003140c8943d0303d91 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 688872670 1250 688871420 688871441
    0xd02010501050102030301051302030601020f100f200423060409061404110f0f09060c0703030f08040507050405040303021306030f060f0515031008010908072a14060405040906 77
    0x1800c040011406500c00320580b4101e0b88098004600c07842a6240c0c0006504014800c504600c10400b82c180401003c21142e10101020302000448165006110f0151060000d0300d0142480c40c4074034404101000040b50100e802c60740d2900b01c0006c4401002c101d03103440e0b1048950100000c00c012401c082035601207000c0307030306401d0030810f004200380c188001e40790228500441001c092101c6c85403032901400524088941c81e20191512000c0c50010790950005403280310180d205480c00d10405400052048101b1624209851549000ea440d560350b0340300b80c0a000c4c002e641311008141058000c0c0c05403164084007644509070907844d01c0005000344084804103040c00c0c01d0050020742c40c4003142d81201911006000007901203900a903040c0341340c0c03021303089078000038412000040020080c41070059031842448801d82e26951400c1104804c01c0244a6400100650070501003a551540e0782c0030455043c0840d20411482d190001180c5008552240341c00908000403c010403455600031200c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 688873920 1250 688872670 688872673
    0x319180812130e0421090b0c010506040e030304050c100c050a0302061f03081608041a1c14151302130f0e04020319060917030406050109051003060911030f0d02 70
    0x2c2c0d035511960003d11001e581c054642000c840004281080c0c9880060704490780d803e00340c1100341d032152030100517404120300d10314513503580f0207201c95440d050280454500302c02c4001c50950519441d8140c07a211104609031154001c0c3c58000203140c024002111034503008070544102ca0712504020703440d40e50440780e030184440b2078804143e010310840b55003401e59402641460420300038820348600d8059031542969810000d00c400501d0200b00d0820240d000c0542580d181c440c4502d000c0d18074018810040c441140d41001c002110a801202040745e0110b2040c90944000c0355003004034820503c80c0c8004000c040c000039014265a6444142e00c1c02c480705419050446552040d03801d9080c3d0065030003e505410507079034962090906054a541e05000d0340b00080e000c0c029644082080c54044107040c0c8011300401000300784a494070a9a00402589000340114949150b080200d420140001050346941d151a10b05006191040308074024001d02151035134032861550955691000000070010f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 688875170 1250 688873920 688873957
    0x512010b0f03161e03020a0f0303020d030504020f0f040f0204060903020a090c081f0b030f04030e090402101d0301050c030609011a07080708070f061d0319180812 71
    0x642000126150080420b01d45030b10074908083d290000400e13260b42c0c41603612007065021015036203405000e8020944201c000c004285540340107402d2101c0039036a002411b1802080102680382c0040000060200311480d01e1030060745c00000c0c0050420042c0264038030f10100d4042076035600034180c1270a4900807140a441c581d6203000381c40c10f5601c0f2402c007000081202000c1601070400c0c501e840c0765081d9000402280c40c3c2c4823501903d907504100e442c07200440c2c0150620060540003103038441c0d03000b025643c680d0b00745025000700c0c6000414070307802010050015480503d04401081c00d03506c0500042c02803009062080546006420035940749118100503000040c580d01020070300056003410000c200d0400728240c4a280d0f0f60707044403105a440070020000342ccc00181080341d615104a124410018550040e030281080e031155070312038003419510400404100300a8607091039590003603840e15004040999400c541e010302e00e03601000452081c042c14140d00034030f00d0060b101c400325005c02d5110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 688876420 1250 688875170 688875199
    0x1090b0420030f0d030c020a05060c0a0305011410050a052206030c0216050d14010c090303020d030e0a150209090906090624130b030a15050901090308011403070512010b 74
    0x40f07450102038101e041c2d0703000444844c41c5501a0700046140c4100f4015910202c465488440c10103034101c800c0340c4080000502088115014400c11b070140611504001c240d0400f800820001d80c0c3c0301e9034031028018080b514104091141040f01c1c4c4280100c07521030028070600c01d8501d252003c1c1e0003810003203410304001d9240315200007120b1031090032188849100174681411700104442e002000c3da91403003006007440c43ca2209002da07114003000d5aa4210040e0702c0c42c02d000307007000c1003e01c019007058100480300b108184001500211640c00c06507020340030300e2103c507050080c40341c0f08a054200c8582c40820040803404525244200001025036900759034420140072440f900c000d0b000100013402d54140001d0a200c829000c1006103008001343c0303601008002882d00c40400f008a6800300814a4090300317021b07501031160844a210000d21440c88181d4001c0d005031014000c00c040018004603a941076a01080b08500500002e0520350030f2807407083c0018003070620429000d00441c0c400c401c004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 688877670 1250 688876420 688876423
    0x1104080321150603010308070512040e25270312020604030905032d0703021e150a0503070c17070809042f0a03090c0b1314010c0204090501090b042003 66
    0x701c10003002483e051031682156a03228660700034507000c0e41d09204502c003a0480418542c010400750500035180e80b40c40c81d001d8214003540d4280a0141e51203581800e5450280e030b0042ea290706a2803501c107081303481405003201d800560f18070394000350860105000203401150086001030099001b55242140140ca80c42415034402c120741c07000c00050b910b0481e0303c20f400c1c03c1000d1b41c0448011030050320500c961307940000c1c80c082c4c994106582c070005000b501224a14000141c41c1340355a107105068100b0001c150060000d000013401c0c0d000388a440e4a1396000c2065540c5061801043d002030340f078590102c2d003010309458026415090040d40f900340041840020f034500c890141802100fa904a102084600c40d1180c001480300e034141501d94121800080c28100268003521100a800d6140d20310b25240c0b002400c480e0b44468007580001030080d4450b44d0208891140e41e4042c4c07008280302045203001c07401440e4021000c0c01c205210f07000e20003007080702e01c400e603000c218610312000d070807043e5400c16 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 688878920 1250 688877670 688877701
    0xa0c061b0b0103150902030d080618010f0b0307020f070e1501050c0d12090b0a0209010206160c0605071e0c031e080615070210051e03010b0a031104080321 68
    0x241003402010010000030b110588504d18107000e40344c0108034854680d010034582580101010041000a0108506424038010316180c84141c03d03415615549403086124203489a40100004054000700280b01c0a008012000740d0002480c11900090351760f003060704410b5002c0c1d4908044060f00304100c1620f41c0b09405980034510214040c02c600800e14405540c2604501110100f180d01ca2020402180d608901241b044155650141c1d4440b40500024205100108500d0084628501003081c103603010340c003d440a42e10940008250310fa840b0207994003072a0700c0284002c02c1400f41d00740c09003507108046c00341c014840d80712041800c00310341e900010341e403182d0030300000600d84000142007840d002001181800355020f18a10b400503d0b00414200c0003250200030110b00005520002c40201c0001c80460b00c842c1c042541c01e650418007489414425440148100342d120503d140549501ca0700700c03001070504500301d954810314a4003001415540c030a210040385101e6001a5052a400090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 688880170 1250 688878920 688878923
    0x90b01090603051b030715020705090112050607120b0a1410022a060f28030209130903020708060a0f0608010911090703020909010902092e031d0a0c061b 67
    0x2400020664119110502d0844e400c1540d1500c00c100380001c03c042101c2d0b10321003003262036010700103803818031041c440d4075a41a0700081e20a084128070001042021400700e800c00043e203808965110040325000c0035040d40c01d00b041e40014901400a200c0c800c00126000040c4143c500d01c2c2e81c1000c408084c1c1c0c07100740ba002044c08071000c5491035028800024084101184024082400c0c0310001c03c80500c960007030030701c0d0321340d00368254984011030060035120850350009250075843d0594900100705040c10f05101d61004035216084541014000e000410203040740c49d040720410718001140c0d0002d405215450114030b464540f02103074001040c041d43c0307241e58001c44a03000d010310803418000040d900600200030540d003072060200c1a51040300355030007490035100160702d0fa8606010444541e50f070010ba001c0110346005800c80100c01c03558500c01d10802824006100300f10105120f241700948040c40d14076005810180c03040003c51100c070700c15a10765565402101c100303008692000c0866080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 688881420 1250 688880170 688880173
    0x91c0206060f01021c0306051201020405100804020d12050306010e040902181009240905040201200c18010e07080405100c0309020414010302012709022209090b0109060305 75
    0x394440c02c181c090b40350300c01010710445580407040084e01c071540146059142c0000e840e00c008015518205500d0510492140c000b1032400e45000c000a69450f10101c8030014002068005015552146a000003407500248481951801c101c0000c0060303000321803d60110356018858815802d113032091ba0391840e8050004100072081d584990607034100104070344c4020840c9003021443c01054020700b0344040344540040500c005900c4500034250743d41d000b014201d40b0b41b104120260380d00038940c000c101c070b001008420b40420001e045050506130301105d9001180951105114010003070994126101512585d009444d200c40480d40208280c8003d032a0394003952501e1803200956002c22020041030070001415180e0b0307404102035465492101d9500c00e9034100410642d600001030400b09401030440c4113001007990304000d0200c501c1e00405011039404104410030240030000088035628003402c15800315921b04078200503200e11a0100c032036448440000403a000ea030701401e03060b00d40c80700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 688882670 1250 688881420 688881433
    0x10f03050618010e0a050a02011211070f0203210d0b01020a0f080936060406060c110402160f0c08010c0906030509071806060815010c080a1101050f091c02 68
    0x1590842c2c0c0c104241440180355589145a07108084204041c4d80a03500c188082c202451403400003405440202840b014194101168410480c0340241200c280e03540c0481c8548110000e070011901d001e00c12300000707d034101c0100024182c90715001c003826a0f000c1348001070201d030b142500120380310f01d100c0030000c044039a401d944400003a03891028040c210303005440740884011b00307203060a40c000c81d00b07050310b00d0703840c8001002144030551031202da000788241c0301881014900b0900425088503e40c0141c2190103408081c0300603a42c6030110b0b010000b080003502e000141e503080056240c055200106c03582041500c000412580601030360481c0b000503226014901c0c80c1403001d0f400f5110080a00e40c090250117004070b12900c0108400d800802a070100181c2d89051903000790521501601e68000754140c0c1d204107a00f41c2c2d0000e40c50180341d501884503078a40031111400c0d182c41240d001085000d508040400c0b20280140484911551203c030840316440c3c3c1940800c1e41c000f1304440c45800680041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 688883920 1250 688882670 688882681
    0x609100615050f07080705101409060405030a11070509040516061d0618030f0c0f1c030e0118080105100b12010308030915011e0503030310090906140f0609010f030506 73
    0xc0084c1c580d96004591940ca440840c2e40e0316030030001c44503000310b6155a90003102d00280050020381e42e2100701d800080500381800c0d02c0f00c9990b40202a00e840420580d50305683e02c0720824041d11000741705c0501242910308140c42d00c01c0d100c1080150300041c620001500080c510f00c50107040103000040c0941c042111600d405001144d070000600721113002190784a0070254408201c684800402000901560129641008845020b0682c448e2040c09081c2d0065401111408103003541645800c11416050f58000140c1c0d91400980ba4001045082c060020707003010190440c038032640c29030b900100e07034680301d0001c01068000d4003400040001500011710000300520300131900850100c04403041a0039254050750018401d0300b009060744103010511040c1d40c5d01510003c05028110051802c600c0c1080c1d0440302e451171840781e034146035203c00854060001560040040e130051944800c001e2070b10b103013014900103060f20554040c40591000052000715a04035400b0b60b60300c00084d003107940700d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 688885170 1250 688883920 688883947
    0x80705031c0503370603060c03110f0a030e0a0803010e10060215060a120828080438090f011104090515061303050f010b150a11060910061505 62
    0x1414092406118070f00168000c40e00301602442449502c00c4c001c20001d040d894420252040711a02c2414035040c80d40b80c1445031440d8045c0c4041c071b49800d1540d0388070160201c00720080d00074031000c0c840d90302945043d5070034048604011816201c900c00181c000c2e0301d6016469070418628862440160048003155200d000481c12160b04044010100c0441a0710313014002c1003900b00400031200e200300021075100320000d403070b039002c00d140da13030940f800b505001d440000d00952002040105481d50700b044e800c00301003585140884e41081200527a02444100807051007400e000e540c0441c4521401c10501c032107040502407000380031920301581c1d050515015000d40503040281c9500e01c0c904c85400551200d490305405080c80c4c908100c1c3c03c051051840c2482402e10710b1036042400a0390401c401502291134210030444610584150710340c2d04c0d001400211070b000190312000c40603004400c00c0c01015035000424410100049a00b0000b0640ea0740c0c49030088004020740e41c001c50700a1061402d201c90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 688886420 1250 688885170 688885201
    0x206070201030903021e030c1b01081b0d0213060315032402040503010e0601301e1407080d03051009050417030c0a08010b1c0209120106080705031c0503 67
    0x1190048640b841c644101040e002a06d6103d130f505583e1021566081801041280b2905000c0b400300d0710000c81c0e0498002480400020a000117030aa1078400d1600d488a010840350705951141045403100c114850030b9001c018140700c1c110000c1d0a04840c81000030350007464504403a030142920145005088100c0c00380070380031301400007042d820300c00050705131400e00800c641e003e00000508982c0d81001401004620700c2850100c85c0b98501010802140c1040604070070390f500031003450300212028079203104032402c2e110020482a08100c40001e44080000c1c50400d5600d560140c41c29100715000860446d03808a40f00c004940d0411004c201440c81d950140b90060300030071041d103520304565600d41480e8803d50b4000c0e28540005500f00460380c3c4800d401303000d88042484145040b02d08030201c400421812045001681d0000d032800300c544d120030b601d00403001c061009020142d41c9a84064170381d280ae00ca01400390088610b031000c8000180903668a9100c9a2526030554071403000c056003400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 688887670 1250 688886420 688886423
    0x201020c0c01180b030408250c140f120d120c090e04080c1605011d030d1206080706110607020c010815030a0b0a0f0b0f0d151401031a07080402060702010309 69
    0x1c0e901c140104484013498010340c41940078201c0c40d692205480b483e90b403252000c880c02c1e809103400c90b210a0014986168413411100041d4010f1007400c0c0c0d44001400c01d0180030382069201162080c03102e95071102188904e00d050045d04c844c0c10824100c000c5000707640ba00e090000000e00c40c032600380442d040d1101c40a030403900031a1254141180625842d00d0031003600414401c33410403400410056074030401100b401c560060402c0c41030724807640070990780d036a000c0c4480148510308a4490160303c1581c010f03801130581c101154101030350390202500c40b401c81890f4001600440000608141c00090031040c0f0b098180e607440c5141c1d69414910207401900c808141d85400354a99001c045025001918000d8500d0030000a010f020036000c003086900281140340159840b1081c038130160395062500100d0368101010103004012246648002c5c444040ca00007000000c4001205000085910f20582a400aa10145a11909015030316103904540081d80300310100103510041d403107074002a000a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 688888920 1250 688887670 688887707
    0xf0914061309050403170912071e0c230604030b071209050d030b010f081b070512180901080c06040302040f020c01090b060102070b03090c0d08040902040303080a0c0201020c0c01 78
    0x21074a9100746000c1d1030055405800186c0c41045948804500e6503006805c180b0302c1c0024515041d18000f901d0290203144030180032840e0a144040d94900c0e02141d01d0020b82e801a144150552a05000d1f114011a110031001001ca481641010f500300789044605980c1c01152101c110755407284121440359499104000451b2684c1410300090360810611710601502c2e00c000c507074003001c04001070840070240e010804004480040c00550600a401e5400188405200303643d1a003860514901d00200b0000702d0200c0400000c62800404c508601c106210b00100d4034503c44da40e81d14000b680e41c101294245602c4101088200010b28142c0d12120245088020140c00d019a50180508503900d81900303035800021901001141d43c0c1c18019070000e880c480c4075150070f43c10f04100c03c0e556102841c180601801c000d178172907018000b1140580d001050a0141950b031940c0341e01c1d00405000c3c043d1450f121060a250024105900600a407084160000c0050001444e032400440700300f0450151412603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 688890170 1250 688888920 688888957
    0x250e090a0f0e0f15060303041a040603420e1005030c100f050a0c150c0e1e12010204030819020c0d051b130603061a03060f010b0d0605060a020109030f091406 69
    0x14260380712714403000b8280c0350418944440ca00080503060319101c85200380405941460a0203107810744a080d1460b200306a03030241c4600140079200b01c036040a40044410302911010045040c1c0100e512805596068064503144602003040c4259844412034140104d0841d20003004142d10a0010707200004451400d0b8410424948072140c40c401200006109240c503031614080080c3c01220701c0b121343c181603079003036604102445080e0b286101800c0315881040c1404132448540c1d07094040d180510380140300182e4440c021301e05c1500b00004050028058051100036495500d07042ca0030000054001004e800b61404c900c0e01440a400002c407599401818118a6116047e0a03c140000b82d442050006440c03101c2110400e610303030903001c000348294080d004100139a410140250304403041070b4202034691401c110200060482504440c0d0015070101d001210542c0c150004503107a130294855040c08040c3c401d0807030309418180075070061047d41040c0c0000030f0401d000240072010581100006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 688891420 1250 688890170 688890179
    0xb0a02030928050a1214030705150103110406061407020d06020316032009130e06100509180d1d0603070e0306010608250e090a0f0e0f1506030304 64
    0x14070180540e407119401200e941d0544080d00306903860006000f0032260700071007518015000b04c01410018000b000081c0a0164200f010020030580717110710760290640d5102d00135400181c10701002444282c1d40d10401c00c109840d2400c181c802d10060343c1180d5130744030840310302001201b810340c020801260451440081440030400300d2028500a42020604001c04100110020113136018880300501070707030041a801588520f0321046801d2044191001c1446000c030710400340092140202e01401409248100082c01c0b40480729101a90800c0320494929200c0c2c0d4502154080050382640c00c65000f501c8031103015010b02c91900c1003404c051440c0c154080180082549500107a0b01080412030250821a20f07180a0014070f0151546103008001440c0035501c4031540040314031004403140d103101c20702c8031451056403401041100a41228424140b5043c9000100380f0a8503c00100380f030b0482c000c0c5d0150780855440719004501004000104841c80c0d4195800d0010b400203605120401000a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 688892670 1250 688891420 688891429
    0x20d0518041e140703060f120209130506040b160c050d0e0d08040f081504050d0521151003330f060519090e13020105040512010f0e070803040b0a020309 67
    0x2101d401c2c035603c3e444614200010050141e440e20f81001c414102214824805d60900078a04000140c04460100c80394940c00f40c070749240c00340668090a40c0c09030408104c140088101110701a442c40c60b030310900304000030411604050040340052003034102c440d03410b221501c5801c0f00740c05800000e1174840440704982c1d41e1905680158800411490120800c100c51301c0d041c041d40034a405003060803541843c2070f541e007030f4850b107100c0140c80c140440845c0e00da00c0c000c41100d002e02a90040443c3c0b441e90b040c590f1f0100084a180b8104c01c1c81004a0b1603002400c03031090080440700300300d0300420004001040d40941c03100e190045a925154406040003405c0c01d160085207009000c1525541d41d070340008100312030499000380010781403200200e010024900c019032a140c0c020081ca40f50b10b0095520300c0101c46a1040b030b030040340c1c440840c000050304d1200660020b20001c0d00b48000b002072521000c0c0458460486116188403504140300400400001e14010249006d881c41564608807000300003a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 688893920 1250 688892670 688892681
    0x180f0303040602011b0f020706080903090901060c150e0c1e09040807060614090105040b0f0604180b09010506090603090c0d1a0a0e03041401050d0e0d020d0518041e 72
    0xd005179152514154180003501c102e82c100d00443ca032403851a042c41c00d000c0e6072900070744a918100032014001440300e62061003070716081c80b0014600c20965940324001010304d00d40c502d040d56246800390800801c48418803c040131b012603500900010085502001613002c0190044144580c142e4a100d000765581040544036510880302e40fa10b0b040a410050100e40343d41d001502081c2c00c1c00842c5a44d650345081c20350440b0700842e404200d01c05c201d4049240010342546841d0080c20100f000300c2c120035141c0c0f80041c0178460450410410214500300124001c0a1060ba60041d0302000b4111180c01c1460003990f1001404080750f030100b6100022a07d0741413401c000740d46400c201c0c010103140d8060078002c25001048001c0a2005003a1800c50a490f80b2507440b41c254440e03284004807070943d003e00c0988501c0300313a000d4100710340d0103001d281c16120b641314400e0800501410001018a5008030b00f0384084a0310001001a4111500f040c88010b0400c041c13141c2071408031514403a103101a6020701c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 688895170 1250 688893920 688893929
    0x300d02070f03120e0c090c0c01060602031b0a0f0201271202010306050d030f0f0e210d1b060c05070501050709030203190206074107050a0b180f030304 66
    0x1480c118401d824000c1800842001c044101ca0800b48040040400080c500192120417a40890952507451803030740144940b8640078181c1d42000d2002a200e80c02001422541c035000d203a07a400324991001d41600c80ca55004020003091300543c1040240d4898400e00e0840021104101010140c203d05100c040405610001c0b60414014005086580c14016040202003d560640164105039800380a10400c1c100e640c040040c00c0d01c4000300ca500c100000920f03c00040c02d00b15000340f00ba00e01102000c9034401d0a10584189201143e03464440c841d0108904901c45484591102d9542c8030700107807990302d0b41c420410806003c3c0c3e4000c80d00038030515015490075121805c02c981f640c410315040080710003c019206149400c840c0160315214101e441c0c050348420541c000285840c1c108400010031b040043d502c0400b010f442d010b03100e65041c02d1038484104021102c40903030b07400420107804924016030385050300a0103500034081d84d5030103030764154900407c41416a02c8040100b0300d0340c2c000c1d40c003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 688896420 1250 688895170 688895183
    0xa0c0203090d1217010617060a1208131a0a031e0c080402031005090a0b25121a06040603020702010c080310170109030806011805130b010f02300d0207 66
    0xd003d00036070001c805041c0c8003034100c40480158585480074005040c1c0060940070030388002d0001d02550340c0e80702a10081e01c08055640800e41160a181d88280c004002003008000130902c04503000e05444030020390010400102d41c90540f000008602032728122411000383d140c503a04a40301140d030360064103c0302c9a80c3e078840005141c6030040514082c1031099159440b413400c5c00703001c8000e0300441c540c103985811061040840d00c1d00c03e2041080001c401c0810200702810038070308056580189042001440c1103000d00c83c40a030800288101e00140c4a80c0c1d0340200200400c12005010b50040d0898900504040114041da92100c0300f10381d004a503030140400b86c50310148095042e084980d146211000c0003004550266a40948000c0700508240c2c14083c484035418105040788003050050b1002806c10303190382800403d40303009801035154050200e0ba80c100c2d520841840002d450400072403041c029072581c246040540f00100d071080c48079101c0502008440c2d62414280003e0110790b11802 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 688897670 1250 688896420 688896443
    0x313120903061803030c0905060a030e0705090429060d170c160801060b040b0d02030910021c06050603070c0b060102160308030f0f01030b010902032509180c080a0c0203090d 76
    0x603009088a103001b40c410107020a00c00c0610064842d8415074061454509001900c00d51031603500c0e180840c1640403a074481d0b00d0348200010000b081644e910345130700d8007200c141071140c40b403070f201010381c070450781107030000304800b44d880104030f40918009100c0084210a40f404110121a90429100e11500001400e43c03880401454500344982c4000340000e2000d81c2c01c09042c202c05003220700c81c20581030441500400410080e0000b409107180e031400c0d00740c2c21541c8101c11403007000c4d060b401f4018410010700e80304c000189820000d04581c4251000d9503024144d001c00c4d0b0303c0a0070007601508250451003060602d61801c40c94440070070146004054054407071034401c0d07000e42a050010002110031444200400014a035009000d0550b0028440981c4039a1480c440d84103241c40d00300d4220040c02e0884c00c4000b240c2e0081104000c1d2500048050311084804480405903415540e60400282c5032800049503644244c0c41810301c0b00e8648143c0e032508076110000382d40000b01c2d1000f51080c05020303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 688898920 1250 688897670 688897673
    0x1c0501051807060e0d020d140303071d06120a09110607080c010b0604031a0604090804090507080702060603190203030405091807091a010f030b09240603131209030618 73
    0x10490b50000f0541483e02080c4455000b010404a403240c00000b406105000070716020400d0400071210b40c5c80281c400c40b5100c5c07038041001400e09109009060121280c01c0804006050140032201110061400400c040e154081c0c904010000301c8416542c001c481c0b1280354136640c80c0360041051900443d00761380c50702e030346950035400c503007998203d030348036510420040000500740c908451a008181c018079099a8400002c10094007020000402c031800001d03003c40e02c0710060740428043c00d015a40c41c0c560355251801680d850200351030f1294943e00c0419284151f10381c1420500700d561019082e00c0c01d02d0b65502c00310708060010b4600003d0f802c0c0711401d070709128208002c00c4008052001007480b124100502d03082030000c81d00401410005107410b002c69541c021f400c95165424040c2411100c1e00e07001c00c1c40000303210f011013070480c90705480d5040760403480e0000c2624064044210365903440960f6946040121840c0c400120500640c9080000459007620440000303c00c26200088851701c103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 688900170 1250 688898920 688898923
    0x204080109020a15140a022806290607080f070609021e100807022515171315061d07030c170601090308130f15050304021c05010518 58
    0x16a000407500f00e0030440c0707003441c4551049510001c0049200c80641d03d80c98904228140423204001c035020315412540050300d014096221a1201c3c01244200032100c405408401c2101d460340100f5803101107003401c85000d00e81134000f014514070903090a464510626510342450b04440300c10380b0034950720402501035040003c0c050752040c4d99100d0b8ac0480d5041c080000345110b0392100d403071081020307000000e540d85008225000554854400854004080070410640510035002c1e02e082c0c00080da0142d0f283c00d004021400d500780c9008050461940e52203d145500c1c4032584040e590740c036031412482074019039449210050b0248558440c42e6134500710014081c190040e2107501010b2500d110140030300d5100a1040d024a03048440b84000d0f12600e0040783d000f0110b41003c3c048900015007040d840001c0580c1e80129500e10181061480c4d88949a01c031030441140b4400104804100050062401140d82414200705038036611000540c0d8954a0840b40f0440303495a4144407040d009050110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 688901420 1250 688900170 688900189
    0x150806090f0d05090103060e041410020903030d0507030b09040b0720150c0408031209070f050a0315020f04030b1b0a020d0c14120a0e0604060c2301020408010902 71
    0x2221004200e140071003801159110341d40280c4000b0007401113055166a88640c009900900c0e420703544082a0509003426000c072503c03070f41000f08600c074151103a800005a402a034007568401000317903090002c0b200c0c000b0080c09000b0700359810583e41d0341e04114541e81c0e0300d44460245002c0c0d0b103400090300d0400001703012603000d100d4402030f0010400c140e25100307500080d5200862629440318109855280c0703641524050394020705442d000110760799520b010070300e02907480b85100c9800c8a80c042c4e40c603003184000c1503003030050305c0d00140868010700214500110440c6101020340300107107000309a14410141c0e4120340c0007103401040803030611280c00c941803030b903200c0c20300d205890320701d48840400041d42e50310306c01c00140280216140240c052240c4c10324001c2843c1e103a801030364920500c880755800280e000c444c10340c0108005032052001d6041c8403060701e0a503500f5031500043c41c00291144001030601c0c1801000b903001007084020702620030b0018000418524002003011310551042010104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 688902670 1250 688901420 688901431
    0xb03070b130f0b040b18130903020606120a080318120403020102010b0103060b0d0f020702120c120604031b02030c0310150b0f040b091f0801090c1b12090504150806 72
    0x3018400240f100e83c2c1030000312003c45682020b11691303006494181c1c620040ca11444540c041c030b40c3c00280c07140012a4100d400014880c0d802c1da075540c1d03504420010380c03404051180038180d100018402c00240200f0007540c02080f030b00300c0707410030b011010406881c0840c45042d03841044000b180402c110358090050000542c800d0906026190800f031041c7e001d805040c0c18200f000b500c407108041018500c0e4104c4140c16005030429455001c0c203043c030340c0d80d041c0d2000003501899032015841803c1c1404245039008580c190f6030301c1d0490b00d5500c4801402121390030180d906000308003110352070b6501000b20a007850015900403802c000c0041d07000600340c0c0140d01c0f00d0080d00b02040400c081111690455060b07544881caa16219440300740801d2410340800300c4503188402d900203400324590400e1752141244c1c0e900d03001740700c01c64882030101e45040b400c00c80c1c00c45501c1c140e000c6000040700705800102d4106245082c0000d50340c2c0c4c4000800340d40002c804510844c40924091000702024048540d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 688903920 1250 688902670 688902689
    0x507030e0f01140f25020108090607020d0309020105090409060b010e0301090803340e1017071110022205012c03030702060d0213090c09180b03070b13 66
    0x451075400043c0a080b40c0e2400400e5840001030680d405511a1044e50040d5040001c51340d0280040c1e45241c00d0181305503410703070205a445d400070701281c41c001240c030b104282d281e002e8a0b02030102d1740107a0242510300401c1741413050a00c404c40c4d0f1354071644030f60101e0342d00800f00410500404000546002e03c0c0b00041d0b4026410310112501143c0c420084035044950015111564480c100c0301424110200940440022400540020b40e90b40803080c0b00d0315039021945202c9100071100142c13444000404142c640c001180001880c0c0d60240c2c00260100c1b81090941d2554401c5001150807079001e20800400d580c210107091900003c1d48440c60040c04c0282000429084408140704000d0424045200503005034650448252014400d5540541d4090319050f00c85110311a510040c1d0007601401c0b108801290700042d00300e41070300645c612115191a813092446c1802c0d0044160031440d800710200d00e071641c0e403200464800304103480040424540e11a1254201c04a0f680040042d03440302582 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 688905170 1250 688903920 688903939
    0xa090c06050c070612060801090305040602010f090f0809130510060e040c050f0c0109080403060c08250f0e0d03051207050c030f0913140105030705061603030b0319030507030e 77
    0x402c880000c203007055078694101040c0e2009074903041d40203049950005441c9500f03003a60300d010160008040e00545103103400900c00d00001162881c100c81031000b014240e011403041000c00300710b1860042000e0f030006441c40d0592000000e0071400d480044d81e5041d84181507401c00c016050740131001528074002100c0c00d0103000d050b140000c15a0281c0304051078a6040050365a0104200750310030b4980da58407840c0d02d03032601d07a00d0401c1802048804131150105004a000404400000f0094802d0700d40b51070003010790782c0c100b00080b11181308920304542800354202602c15641c1c0d41c5014610554417aa540035591440b01201640055010700f641d17080c089e0500c060b008200c03000c4180c2c0c0c01003044c40071180e203a09a20b40014418450601e00301a01841d20981020081080741064142e0341e0507000c450b00d4a035180c6c02d00059105805c0703980070a64112040c040042d00c66084103032007020040c200c0e9440003000380c0b030faa003510180304c003240800c400044802c00c1541204900075000d00885440a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 688906420 1250 688905170 688905187
    0x906090902092d0f010501031b0c080307030906020309060402040e0f0c0f010917060103050d09030203030405090a1506120507030b0f010c06270c0f0303120c0c0b0a090c0605 76
    0xc040d00050800700090402d0700305462004050300c0d8a42c1d0343c020824680c0f102c1d0800a599420010082c001c8a00280c1002200e50107150780c200d0f604040050381c1d84400c5071040c142c607480c103a904058142d00030035440e4115200495034500127140036000e0003001e49400d0404c0d104020442d0f5140500402136080100420200000800d800044070020348500d03c5902d1140c0c0102c0d1501d545400149440c24400c0394180000b400080e0541a85d105504840308807000c7c48013902d003814076210007581070b0b00400050050f41008810341c0d810400740780740421080d07000b40d0f00c0d49540310613030000030014031800210f402c8a8000c2c080c098100c5201c0c1000c01440a440300410491180380721400d043c040c00d2620002045483c2d804203d80c0c3c001c0181031940c100303810344050300c6141200429140c0840c480c4000c6641d2500300c00383c02c12280c0c50384809841101c81d0003004080c00684c03c403041030248801d52080803403000d0100078424440c0380400194030325240b80684544200746c120808102080c0f18000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 688907670 1250 688906420 688906429
    0x14011a09070c030507020d061401051f1206031223030f0403180e07020c030f060705041e12030e09070e030c011b050d030203071704020d02040507020c0d0803010906090902 75
    0x40e000395a61905010340c80c024142984c0340d01c12100001d40221100b903821052000d0303584982409541d5254902182e41e984d01040003100f040c001d01701c42414121803550080b03002e1880c40e0b1048514a0300402d034203039603454080040901c000b5000220b04412510014941840215840002130360441c41c2103040400c980490624020001028040d072803050381b0088441ca0b1100004200c00c42c000329513454104402502d803040400c046009100e03001900840000104040d84a00c0d5a070b82c1b01402c0524104a00d200c5800c0e840c0c80c10031054100c1c001080d0804d00042081a1a00076140d440c032000110040c081d41880007881c030010040c1d50300c0c6001e203958000c9840c880c00c0c80c092800c0d140c40e6003440340f5440b5066010b000100203204070002401140d4254000d580300d95042c0c0c0340c0d010700000700d07420b4082010040350002d40c0414070441c50b00040c68254041c6402441c944126030084020b000455900414017a054403100c07800f01c0100070720f004901441015000c88242404108101d40c0072a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 688908920 1250 688907670 688907689
    0x406020c01030b310c030603112101020a02160518060405090312041101090611060408130e1503010b0607020109030f02040b09160806060c251214011a 66
    0x460400d6100c00d0300c00601c1d03071251860881180c01a00c45207600c442c843d094000c413062003031071010071400c03d0907089406000344104001c880c1c101c2c480242400300c490400980c2e14020380e00701d40001c411150492a800d00344082c01d0042d5094005007135540c030300c880a4141a009074002e0388200c040c2c001340c028020b00c0d04000c40e08481c00381c90201d11512102842c2d401c5004070381007450340307842c40000c11041c02500204218400310030b0b2a8114040e4803003200311079601e43c000700c450306507001d02d0108000400300002801915607410400385000d440300c030000c03c4060291400301c50042c41c0f01a104c1e46180a12500c40f00c10f400302e441c186402d643d5400038290920500c00a882a00d180d61003805540b02d0750880380d00c0c8200205145c0152400c00400039000c00e8900320440091803107400540c0c5402e00d041100c1500c440100205000d9403103d206010710721310404100c021500c0c10300001802420f10520000007485001c400c00461465a03900c4d085480319000f00069100142480c0296102c59010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 688910170 1250 688908920 688908943
    0x909030a031a0d0302010218090c0a05030402010203132c010f05061b0d0c050c0409030c0b06010e030d020106170c010e010c0f0803012309070503161407081e040602 72
    0xb0810355410910049059012805290403083d41c2501c0401c050b419402000d290801c0000082100716410502054103422a07510944a00030440c801106000d400919032061052040700d1402d16203c1c0f1071510001164801228456000b541c1072843d032010300305040200070400b004031a98500000d80c0c002500500c14203024000c0000c882c500390041c5058040c4c80c4084a0448130013200c40f030402003850004a200713a85602900b02900c40c2d82c40c050007840360041d05540e40118615258031540d4642d80050021418864100d012050640b002d0004a404104035000015940c3c90329903212458001043e81c00c050b9045910038044076030308240310310400d107800c0c600411b0015413480c1214a9055500000d001042c0100000034010103203020b00f2021145088001c80c921060024404250070544000700800c6061001401c0031900112207030b0705030043d1400d01c1e0301000c6a0300800403030380320180c15611a070700000d07070700e000120300324041c3c8015000d2050585400c0c82c10100070349803456101e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 688911420 1250 688910170 688910177
    0x30c0a0b09010201060f080f150601080604021c090615080627030f1c14070815010c14011d070602030732010c02070911120a020705030a09030b060909030a 68
    0x1c0d284010392017548000040c110b050b00f0950320a4540c0659039466280e00e100303070038034820468540441142c450940f4003d0704181c43e41e21603620340d0810000070f90008200040441228201c0c220084464080e07284150b004031000240200c2c0da00d540380407030b00b5a8100d114079901003c00d000c01c20300e42041030340c1103c0740111601c0012601400c050308500c44d008400b0140440460305c0300655400e2031000060740c40c1c80d1010071040005800034502030400300d4200c40881c0121001540b05c10080c051140c1c1114145002000b0f613501da640c5540310100303d00c01400d540e5503100036404200c0d0110701080328404200040000780d10700403000b0f550b8070034803400130900d8802000c10121404400c240c9900901c0841000250341c109082d010b000782552003040005110b00c01000a80203040e1080c0f1302201c01090f80545080e68807601003924035000382a0079550f40d42000040c0115000744003508240c031b000c1c2e132400c040c0f500d5818070310303003060001e0025032049603c00240030202c0d900000305e0342c85d19110f0a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 688912670 1250 688911420 688911427
    0x150f090b3703150f0605010c140313061e0908191e030210050f0c1b1603150f1e05040f08040f1815061206030203010603060506030c030c0a0b 62
    0x2020007040c140e0403500030790401c100000110801c0360031a141e80d000c50300d00d4820030401c2c03100716680054076564840c2c20301140c40c0c0366141020652051710408800f101c4002c0303918061400c1c0541500c00c01741c1c1c1c020070005082100b58000d06e40321020441c1021041d203440b203650b50402052640703071382e00900c100d0080c52945171a40300300704000341c4080a10786841c0c6801c80020080c10060348545006001828291404c1c00044602c80800c900500480008451500b41240c42414210750507660b900d1507841c0c03051402c0c2d04a140303c00c07110300000e18414a00c0301211100000341100356580044d000c50301328240b074910b00e004c4600b080c030001004040a030110b04d588540c00c0c01d01d80e040c0c0032400a0701d081e50001c0c7c08107940d0081a01081190948030300d40c000710040080b504100d0300b01c0010200c1307600e86080304101451003200107401122400d8400118035580750300003800c5803841c0d8070886001791100304101c590301d4117001c0e86500c554181c000e80300001c1c5120018007204000c4c011811501800b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 688913920 1250 688912670 688912729
    0x9010c090803120c1b0604111201090302070612140106110d05030106080f04060b0d0b090d020f03041502120a020606100302130306020d0908120402150a1205070c06150f090b 76
    0x40aa0020a8451401e407803031400c0238200b000c111540c41420740d0184030014a810f03500b040510400603515090360160160390300b81403007140d07100c0c0781c2c00c880348c4181c1c0c40c0c40800029062400c5218002d21031a2580001d0020100066007022070400d14030b41072290034001007040641004442d40c1c807107099143d2220b0384c0d4691078040c00503c510345400303810561546005080000d1010b040e409040c2d0700c000c0381d200d80c1c190b0130300300d036161020603d1600700d400600080200c0000440e10300341000d0b09006450045c8481c000a100c581c000c5e0700c4100041c2d002c0c1c0c0030f0004604003009001c0c00c0403490b203001e40c940005d10800c4182c5c104244801031000d0750000740c0d44600051a406030320b895602140c0d89540d0546c8400224588000396001d0384203200591030840301c1606441194075a411580300ca2030300f0402c16001f003001b410018041403e001c01c850300c000c00aa00f07841080701c6a82c100f01e02140c0d40e8286600d008040045801480b4401e00e04034041045541c2c4106010780100300c0c100c09550604031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 688915170 1250 688913920 688913947
    0x50114070f0605010e061203070b1005061603090b0a022e1a0a0905040c1e050a1d0601050c071a07120c0b0a140c07020301060e09010c090803120c 64
    0x2018405401c199000e1914400c0203080d80251303040f6107040030b00c410b090300c84500304100c62401c0c14900030740760700070800031000840a49500e03030b00030903a950254580d0740d948003051480c0c1c040c608a003400c6d081000d00d541015080050350300030300b000c1000c0c03508202417400b019548009254004414010700003140d001e24610119842d4011200b060074040010300c18030001c0890b0340c21481c2c510800b80040086401030051042a01c41c54000691000462412203014218081c0101071035031981607040c0030409884001c10100100009200000320300d82d403c5094185240290482d4100041080103c209100000740c07001a40c041000640c02940c0440154429101c0d24000070a20300300c450144441e242c0083c24010014000c501c40d800694072400810121406903d010407407044040c0801c58107090000641449880035000041d000d841e400c60038441c4000702c9a50620369160100c0d4921035600075200802009903400540c28200019694a0502001002141844408107802489450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 688916420 1250 688915170 688915177
    0x160206011a031812040509010503151807241107240201150801051e09030a031109041401061808030406080709352d0c220c0513050114 59
    0x100c02e0450b46010110402d0445680142c1b1a180c49141d90780d0000800d414046a404171103507030309561540550300c07049280b1007298204100c00320392040050200b04400c10410003d0152003c9410000c04806504000c042c52003070070802190746c101318400c2204820070b64909a04c150007070f0400f6049030380304000300d00400c6540744003624541c0041000951040660108d40500d102030050388401c540f0101c80012010151807841c0c9951040051081c0075210b94000d034003080c9440e9986142140010003d800d0f149051800b9a0101c0700d40010000c29030810070f05032480e01099002110141341c0341126403640684c1c030a52041c091920002000540310350068406001071034503103049040004040044413084a043c4400003a40740c0440d05605000950784605070a0250f600c0840450041400d9030388284013a640355a120308440132070303980d0342c64a0b4008070105500d80c68100045689000e01a650a0381c82101071290811001031400711088104003a00d1080c01c14203c1d8101d0560317000d82c13070320 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 688917670 1250 688916420 688916461
    0xe0a1e0f140a050a2a03050712051006090519090c020c0a080f2b2111030f070f020d0503061503010e0702010608061e150607030503160206011a03 64
    0x1e011820002101d050780e0200c0d025154802007044064801d80038415107102140d014078024406000b60149a84240c10055101441d4a08007040c0c4d0740d01300b100406e888081d04c80f1550020381100900441e41e2180d6801d00800d0201c4081c1c18004100040d6800381055002c0d040711a910303500b82c0d04507913000308014018540c001e4101c0042c5990307200c98607241c80c9004403110701809140d00d591001c0c5c00e142500e0607014142e2405a080043d0841c05880306851180c41e040402c40000000311000c0161142c1015132104841090b942c0c60018401420300d04000c054500340714100c161a5041c0c0c0c1d0004281031000720504183e940e0307454200c0060034032846424070080d1900c5c008000300310a40e440408a0144000c2c3d0000d0101a03203601d08030391134071800c5580441041c50301c02703600c1c80350903013001d455000148148001d004014440100307940b0780c003051040d00840c50000902c03a01c0085000084680003191000e800e40c1e505150702c0c2d1050000089041000500100100e1a15000301a0310201c84 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 688918920 1250 688917670 688917701
    0x20d05070b0406022b0c050f03070e01020a1704091104140907110a060902030f1b040f090203030406030203071b020d0209090c0d0b18071202211002040e0a1e0f 70
    0x711000340004c03000c0500c455040d032001e0600600003144d5001f5800e075015400c128070424110340e03592404a50b03551803500e001d811445260b1021b8040b80c03118003208241042000e00560350307414188642c0c150303144490302c8490201c0800c0300f08450b0607030003482d460361901162402c60b55181e007142121010000f60418001e4000c0c00300c2801000182c0c0d00c4001d0780c41c030a13001d66a0b00b4062008003502d0302080b424000c45007480820204039403610350301a043c018000f610000c1e8400584e00800e1468229800a00200b0750000602007000c1e00300042c0550304000c000341c10b03a110100d5010404200d0340100090050000c00003140301c0080503c0302c082c0a54001e030400000c00c0c8075051036201c0790f00598104440095410594802c0b02e800b00d40d1100b61050840002031300040e41d800d000d640c08220300d031944002d540403810f801100d82445000c0014800308005070b1140c2c10490200c08000000d003041da800340c5050390706070000409031001104103103803940000c0c2c88c00741d01c000180500760000c140f2118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 688920170 1250 688918920 688918957
    0x90203040326100510080a20030405062208090f0105090301020c0d1101020a020c060c1204080d2c04110c33060a030609061104080c0f01020d05070b040602 68
    0x114901a84144660200038451008035030704c3d01030110380000e124001e40003404820010f192107000c0e0304880390351040a52450b01d4010b002802e045180c00030354084499030048030a1018a80c110214908102e20741c40e401c2012000c56030b02d906181c03180a02690052102928008042e8003070404e0310f22204026000f59514020200346e107465500c0b0344e0343e80300420403c60584600340384c14825100c1c60090f80d0000e055003101e10042200075005810741088a1290150080307128485102420041031740d60010106d441c8880d00160900c0c01d90742d004100c0c1f05120004c04107403500002c111141040c281c0300021840c2c0d03c221501e00500c01c04801d65400d101384040c512064041d1444140c588110742c21400140b10040c0000d003c48505031095680801c000e04248041079880d40702c64800c0e407013020005030414030745452400e0343c2c220b60700c0b054054118040c0401c42c3d0418205000c5001024406840520b040c1075000d07200b070140e035802901c0e813507090700010200300799030f412500308009051507441c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 688921420 1250 688920170 688920227
    0x1090f0303020f060c2a0c100908100c050405010513080105090a020f0d0305030711030d1a10030b130c09050316051c0f0b040f0b010608150603010f0902030403 70
    0x5031105840000d8505109484c005164040c942c400d03240404890041c001110480b901003d4038419888020319040c05000c1d0b60030000d540361f4158443c2d500240c0c95102a843c0780c031800a01303250409598104007400d01044a044c958003a0844042d00d6090038040e40340d004003140c0f080c00c0c3c0400d0300035508643c80d000901400354400203841140510031500200f4007107200d8140640d44d0345005006002c5a800c0c008110b075140542c484846011135031040340d04007075020425400380c2c1e02c142c01010815221000d841c0c20ba0401011080586480b070a040c00b11801c02d001180403851265180c4c5c0c142503031075022039202c9225042d40d81c0100b9005084034100f0a400007580c42d060407c3c4503241c030810001c03441e2041c801c09601819556070304041000040030320f035107030403c00c41d4004008407902c00b14441d01074000303201c082c02a4080d0045171340311801d5141504140140080b40c180702c1c0d20506040c401088400c01c800c1754002030301c00c0e510016860b07860314078040d6800d40ca540950079074001150784000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 688922670 1250 688921420 688921423
    0x3030825020714040b060d09030c080406090e0606130303320310051c06051504051618030f140c030307030309150203190c0504090f0e0c1002150601090f030302 70
    0x405550201c0c400110f03084aa5040004568401620540120042c403031003116494a0f44540c2e09140241003c60b4001641d9a41c401c0c6a481703a0440750125603908000e11080c42c04503501035122400384d441525040841c48008a5042188801402c00c2008010f030b075880341c49542180d11612441090b000303601010005d408094204a40f004018410a42c00156510300700b072048103030181b901c21352041c02c0801d8880001816000300b40380c2c00c007400031088800c6600c1d24460740d449000740411141c242040700e00018180d000361402d0990f90000d0510500101e440310301d280344140d0380500c640760512114a1000e052101c070b0034000794180404100b00c418150103400076200750740f040300103a1150070a030a841c41280030030313a141195901d0702210881c034078166500c0102d96410b20704200b4103080d500d600315810744a007003560010341780d1280b151295a0710204207500c05600111110390340b45001c224000d6640803031400c40c22000007060040303925a401500044040c28000c11490304c000d480e414040d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 688923920 1250 688922670 688922683
    0xe060f2e2d05031302060715090c0b090f0108090f120c210306060a0210050c070209060405040b19060b0a090e0630070e100626010303082502 62
    0x1d09185421000e520304000344494240c40d101807945034203003540c84600e000c00c0700b802030300303c200d0b00124200071034000314a001000b9000e040b003003400031840d079851380b50417282d1171030340ea00590517102c00b0f20a0180981d200346500050020a1034042244d239035a600251074100c0c4a04422142d000f00000080080042c10007010780c1500403003140d046030403181d00c01102c0c503c0030154410079502400410450f160a400400102c00240b04451511507002801401c50307601755800700444900162440c00c500300441d02070b6100400b15020410303032401d911080303446940144042c00c00c404608110740301c1800e031b90044000c0c00484911a0700c8070010440a0704151041c010503041c10081c00005086181c041040490020340c2035a0104864854042d2981c520703c14207150854085d11001040d092501100d491250310030b08241080f0501d0207201910014074a20b0310700600d6038484c54207800410b51041d583c1100d5042c03600381000c0d0b44000612711000141455010b1003001809540030f002d9001a10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 688925170 1250 688923920 688923947
    0x403080415110706090303050a02150f011503050f0711030712080601080108011509021b010908090f0a060c0206030601050702040207030e0f101d030f160806010e060f2e 74
    0x36007082c0301000a0455071803019202c0d04000800b0940b05000080c07044014154800040c011108041c50040201e43c9035801110700442a80b1a500100016850504007040c600d0032030a0401c400c1c2041c60f20002c2c44540103140d401445048001c0e03810707200c410412901486e4002e4024941d0380c80710030004042070820340391305002031191000454280c0040c440e03174205101442c02c0c81c0c40035250a80c0302001e50010702c160000801e600110381e011440c21700503030100070310400c112641c8002c648200a4000380345001c10780211201071742480f420350072024103040c07950100ea4050f1270b640d454004032818829010003d4010380042004000c00d90421519418090120b1741d60030f8000096003400212882000401d00144a44119190b02c0c210240c0c1d85120300006002d480808070700007181d9140c10203010020281411211302003298100c2030144601400306000888040d0800000288410320f04c00c0c080e034403443c1c0c1c00016030a969031120034189594042c00320885030222050001e026044a07114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 688926420 1250 688925170 688925177
    0x7020109110f060d0c1e1106010608060d03112d010e0d0e1915080a150302060403030503060a21060b030a020d03140f2a0c13020f0403080415 62
    0x6003294585051402c1c1120340001a1005041010900550740a4000030701e0001c00e01c4001c1001d030446103240041c00703e1403521900e440c040400150000f601d031090591104c0b007004020004d000c1250b03644001c03c980c054051a00c0004c65040707190040c1444204906049000804041074504c1d40c8030155a031021543d8030000c01000010f20100d03626081031800b01c1d8001444480883c05520b4600c2c501c2400020200e901e0b500b250f00c4020761080940007115180c00f058205c410007441140c1c9008100303014034004001894180307103601280803401b0304d0100070140040071000901a4580301c895000500c4c1402c005030b044002400080498000000c064541ca802c045540055090008122001660180240000f8980f9460456264a5244414420060420522000c542c0d60006001c820303044480000640f4100420680c10a02100911f00c0b6a0407001016203150380f00202000d4202c09900d001da581d030310b40520b9400d10722880d003006028400c0030901040e81104406c0c001d58000c2c903030b103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 688927670 1250 688926420 688926443
    0xf0b10080c0301060c05010e0a05151501020c040c030209030106090b0f03160509090a290105030607020a060209041e140708040b070e013c0c0302060f070c080307020109 74
    0x590440c0c0000080355901c000da141040100f051600c600000e05141d80141c00004038030031040581c40c284960304201707440700c0d0b1100c089903603001e006040b600e4214030007070000e982518400d00084c0d2540c1c8101c5040344225641d03410052103038080c0c0c0455004180060080002c1d9454001c1880103001d4180d689000c0e4180d2230202407941000585400c000707130201242e0b40000d1400302084440ca01c01003c2d05803501800c000000010700c1201c2c217080c0c042544071100000340c0c0c0d1224103c21000141d121600c20341c010800d11616640100318035103600d03088a00580d9402240c00440e01901d040c0e01c80e088403085010340e4030502c00d202d502600c41c4068140b900410340d1a60002210114030541d00580300d1301c1081e01080285000f44800c19a011060410385070b500304600607241414119090300c4108001400b03103011102da41d000300f030f00c08505410308003560b0307000ea03c00a50341c40c80203000c0303443d068034907010800072805400c08020300e582c450100f50b66803800c0c103c020f01038140071318120f65100340f08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 688928920 1250 688927670 688927699
    0x23070602120f0d020d0e15010911030c0904090516090203090c0105090102070608040c03150b0906010f0c060e15100e1e060d020a2102032503030c150f0b 67
    0x14048401d2200b0440c446803d120751085100300a611404051680c3ea03560b040c8110130741c2e014402e101c25074403014500c015562511150005032002810740582c04101041000341c10440c000550b034a00c070b0300307560000385500300b03285c014a000101540002c40e8190504001031401481c0c00442c4254403010035140103013404001501d2034010030103014096001414240115840343c510541e205008201ca02501c03039980d103a02070014600c520707604c0d00640314200074101c3d051000d5a80e402040a28065409103684c030030080185604050041c580c64403000101603489041081c3e101400d0754040301b0005083c1700e2022651070b900c610445886050041c0010f2000103d10f00c0c1b43c940307401d1124034907625503447d4200000c2140540040341c0c00304103000040794040e0009402418410170035444d611450700c500400d4944840320788444c4041030713058000c00e035948039101c001045075414185502ca003805854500300c43c418035403103030f500ac601d440005440b6450303036004159845001e503402c000e5401030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 688930170 1250 688928920 688928953
    0x8030705011406030303190b060a0c060c14090f03100f060e0702030906040b0d1805300d020c150f010e090a03171008160914011406030423070602 64
    0x103c031280d906420034000201517076045801c42135140112200054280742078400501190040c905110010f410880c408080048600c201c1c41e06a01030306100560090910040340144135240c03201703028200e81310601a840c5c030108980d88020200704000c2c01101407910410000b071030710340b140e284c000c0f890f5004913000500100c11500031031405460107143ca03080c52000e01c0d1642c011f2190800e0566545190400304004c4140303500b00300c3c86403000d003002d00304d0203240700d042034800440e901080003650140d0928401c0c450450f0186000d1810240e1903240c529007040c10704040c00360188648148200300141d018804000905a83c480c0c01c1d650a00d0f15242c1d5142e5075480303440e0000f0301048101ca440740d03118400c009070300d41c0005894501545c1646071a01c1e2803c02e1680c004d842c6103a80c0043d000d00c0044103a01581902049201e10740c0780c3c40d8075225049011003610502e2500420000002c0b0b421702c41c23010b0000000c0b0000c04d601344143c03958113041d1541c40f038403441440c005002d100403e281c901c15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 688931420 1250 688930170 688930211
    0x10f0207081009050d0f0f0e010c0f05160609050a050910050901151e05090d080405041518110d050712020304150b0603360730020a170709060803070501 67
    0x241d03aa92500fa1031f1007800160780d04550885440d040c800c0b045074ad100041c004c0c1741c410304d03060710078030141400039060405a042074015070440c2e4207120403c001800700c0e0301c81a50f440d0481d6000c990350500c0340c446004178151010560030007500103803a040003203030451004541c0809031a065941510380140c60980b01092036001b121000000d0080160036142d140418458803030324054510645480d503035000190494040e505201d03500040d01d881080b0b1070a142050a4240031400028410502c644a5001d243c0c0b19241684035056901d038007281d103141c4030302900e4011404201d011035490815051071803540303070030500f071080c024184143c0350701c2d5052410641e40140d41c1519a0004040c0040800c011a0b506850b03038045180d00c076044501e090404c2181400406455410004400c4003021800c404c02410304480d10780d08181c51807800580320102c0ca01e007241e910300c10004500d40019140c80c10b054045c0e020104142c10260b02003202d02001c4018140c16124100800c245a0200c54101041e030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 688932670 1250 688931420 688931447
    0xe011b06200a0f0914130f020d0b040e0a0201080c030703020c01060e011e030c060509060702040507032004030b0106050c01021b0705040b030c0603010308032203020303061008060a0302010f0207081009050d 90
    0x1142106405d81410004820210124002e20109031810100313020300898112110613030107a03407151100440c9060911034001e00741c0035070018282d1018550006013a003880500a43c0714100001b00060505100381d0613660b006d440d1000034040c083d0b99115a404200d000e000702e00b50b144840715500c0b230710400602c07045c007141d1b8400c4503925410700d040401d441a401110f101f640251081041c6001030365244201442541075860001d0350702d00d0070701c903179503000301480100107103200800040c404162031402283c110340c024580690fa45140340c5800c1c0c0607024921504500381c4105040e106107038000300700070b0147d0f0016502040a165540d0405940d116000c0003140c1240c001c00061001c68002c000441c0d104c1e90728502c0d12080040e02c04501c5a59013044010340044e000402444410301e08145607001c03011031407a06110904003070001030800c80485c07100a06020354000070b84c040600a00078980201101420346901700b000e004044003a1020150440c0e85029944c0300700c1002d40503410b40780408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 688933920 1250 688932670 688932689
    0x41e1e0c060f020f0d11070902040803180d05031909030506190506150403110109030b07030219050a0f0c02120d02060103050c0910030f05120a05070302060105010e011b06200a0f09 79
    0x44200300001c0c6c5119800c01c449110600482a01140d074074000d0008100501840c001149d07141840310040201108030340c6514810b18a65103034401003480001a100410841543c0301780000c00c40d40305940340c03110344c1d20080490081d0000c01003015403510446c070a0320003101040c4903a984010070011021403a00c941c1d015140705020601c04039906405040e24000c06040c0140712a072203460394115603008550020000e0303000070f90141a400d40000c0300003d5103560906a081000403000608468500d940b401c0400c101c0741c00300f07005e41da502420040e8400b00700095800b000c1c000726000752501400d000c2540d040c410b04448076198208041c0d146e10605600b405845544e017980e0364001e40d04240a0203a41c90310802800d0380c400c0c85103030018a058200c0c1d807a0555104041e160103420403a05a0181d41406045094145180d800c0007440e09214030814907088500003a147c8040100145900c25074072041a61100343c0405502000f0140b8645a880d100c100498007501101d14113028001e0f83c000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 688935170 1250 688933920 688933933
    0x1b2416030b04020403060207050a0507050a050904030e150a2f19030201380f0f040f14070c15200c0309090f100608041e1e0c060f020f 59
    0x142442640a4a103554000b0405403074035580707071205810390b04200c0042d1501d800209181081260410050000742000d40795500c42ca4a40000280c1c50340c00208050103104098000c0c10b0f04c0e41c0d40c3c500c3c104c00d111040c081a83c032044011401080341d0140c014031b51101150b40cc10744036400001000e00c0005000c20014403822509079000041150124003c41c150764803403070340c0d01021071160900c2510341d510741d800d00080c04164032041c0070b004c07948000782d0241400000c403651a450300d03000c03280e03104001d840119a11074200310709002005071101490003181503400340004540d100011002841c0120025540c0c00c036040044c40c212602c000d09501480401d2015886210147c8050140100c00b0025a0304100620340400c6000c41d0442c1e5114808101004000c01c1110541c1510045c240b2440c20414500c0c083c1c0e01c00540984604010f0450462004a02e00b0401c10081000440c114070310658800c40032890b0008452815000d1070002c141c1041400045d240f000030800b01d100c40c0e01009051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 688936420 1250 688935170 688935211
    0xa020d110111100515180c180a0b030103021512360105072c19080a06050403021b0f040905030d0213090506030c0112020a051b24 57
    0xd015400103046818071401240030402c089050003c958a8560180003195030b25082a455940603004141c182c4545a1050541b42d060000d190442e031200c4580c05d0941c0d030b004824108100f411020302c850b03501c80030911010862006900180d41280d10030f40d21301e418002801c0170b60b450380c010358003001c0e000c001c42c0e00000c034445144e05090340c00d411603096440a07018000d002050300848001d0419450f07440b00107122003641e001d03225200001c070b0b0485144020b4407910458060101100420703204203a003000c0c90072200310445540f40185840300490b0790041c960b00d0f1900c040d0404490660150150a0340c115620a0f4109106800500100b001ea80f07100c60700100401030490314030581d00380c8400c0c0807050f810701c100e2000340019070500b108140554608451b0303805480700141454080e070040c2c4140385990360030808000345003008117009030f12800d10345821600e6000d02c0f014420700c0f9041040903859070b100421203440e12401c030790b0f41c03180a9240040c20841c130102614040c3d8150600e1100e0381 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 688937670 1250 688936420 688936433
    0x3010312050f0d05041a0601020d090506070602090901060c060b03030708091309050d02101d19140d11060f0105031213080f07080601150203040504020f090d080316020a020d 76
    0x1e8410039141e80ca508142c590303550b84041320350494084800803c9003030300008050810b50401d078003102c02d10007082ca401e60050010141c540c648942405204003141b01c40801185405a640c0080d015100c660700e0341c1d4a4100401403007a001d81640c201d882d2140e01d20351400c0102c11142c0aa80040c1c0d0b01c5d10b052208020b01540f20a1040350402e050740d210101030014a0501c0a0b0b025200a5130080945a0701180000201c8010b0540760504600d420b908481c0f0320340200d808500c40e40500c0b01d070000c02d2007a003000e000c10759800001644070b000704040425500c2c1c2015400e84130441c49021180380d59a5a40d004848440a006050703140d804141c82c03c520140c0c0000404c001101251480751071135075544400d1403d506680940220380040b0701c140b000c542c042100c0c600501101d50000c00c1a05c0003070010391030780b10b68041c0500640e00041c81c004485850411107c88280140005420401d103007000d98054000351250b1619402c5007210014803880003407400d84194000f0040d0a04503c2ea03956907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 688938920 1250 688937670 688937677
    0x703050312060d050a030e0f0301050603070e04020d1b23130203180a0501020a030509071a0d0605031c03060503010908030f0411180403020706090b270d03230301031205 74
    0x100e40c04502040c0050009505100c8a03045c40d110f0b4595000a0503180c003000081820403024a0003a8502010010290b400041e9902119544140030045454500204a501c00041409011210303207005e04041c6544003d03842c401c891450900202c240d5070315600100140f1028411070740240c1000c1b0784101c01d10340398015a000880a01d80b4042090884403050815a00704800d403200e035804260101e500da018000d0b90747c01180803001e00030b41d908240421101002c290b070000c003842e0001c6500340014005030b202101504000f400c03211440d0384020b1100e003035150346410300006800c110000907141014080d107103020354498080350940d40c4556500ca03c440004105079841340c0d45411220043c1c403001c00c4810038950f28100081d10f445c06c0c0c103000e0300d0421380c0e82c88401080084a4200940c1d0740d284180c40c41c203214090f91011200c0c9030300d4290790400203404001d0788043c06c03104e110105500100c04d1030018001461700403150281e038907200300c0c4d03000900c000b07081d04164000c642c1c080c40c880c6006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 688940170 1250 688938920 688938931
    0x190519120f02030c011e060e10030305070c0f0e04120206060102070504020d1107031116150c0501240801150b0406080403170a05070201050603010506060d0e03160c170703050312 78
    0x44904140c800e9040b90300751b401d8203003044400020719004040c02e4040d4004d18026188004012840c0d04051052218184c80d40c400901008404100c600c10403440e240303c00014246541f20303030401c603101c06120440c05003c2d20102d91042d82e42443ca02114008590b1720f21582050b0013801407207180c034007400702a500454040d043e09940314203022000742c9010182c1111406565000115581018054503003203882040f103081081c548030401442c4040e008070382680c04036140025040f44107181107400340400c0940000c440010b40c0d490b44441d81c0d110601000caa8400c00240504050709545084503950750141e011035050412060201078025407801d60071a2203490251003584080c000004514011707141c088156484d4030510400359424040d864110b2405c4000300300504103500002e80c50300c1001034446031f140d214001c21103052424019198001e4446010700316010b00303450301c01c49005040c0159401c0000500c80340307100c104002010b5003540d512200851420300c11003240390011000406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 688941420 1250 688940170 688940173
    0x31d01020705010906051303080a020601080d05070f1e2f0a0e010501051b010c05040303080a020a170901061e0e0c07050a0b06120102130503060604181203090203190519120f02 77
    0x7c00000098a441c020145100707103178060701065042910040c181501f0251440421000b07100d110041100d21400c00e51144d032007400e48052006002c112144046820006000b042d030403100401e40318803044005040c0c651021016540d4035010b001c02001d80d5460050400c0c0d0200301d4018405540580001c04040081b003003040140600c00c8101c80c03e40d03100b030b200c040000d04040340420805400c120b44c0c64019555003c107505050003413500a180e188524401201024160041ba114500c20343c0054003405241402c01d0441c414104100e016000341c0c45072100e4412044000764240c600300c07017960b80c00741d401008cc0061608031348503041d40400c003074141a8404200001032800c01801d08c014105094441194424546400105421305100405250144e4280b503c04004038180c0c2c1d0442d41c519903c00084460035007141030440c0140400f8500a405100380d68004034804855802038240c00d10030fa048a030744000304135040390740c1098240c0041c540782006054003030150007071703107103e4080c4014030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 688942670 1250 688941420 688941457
    0x30b0402031608070321120c050f0a0504050a050d200f060d0504110406291b070f09020a2a0b010b1209030c0703150605060304031d0102070501090605 66
    0x180c071003441079076543c07000c10540e0101d0420400c204117049030403402c40d0780902030b0560f40c0603041e014000040f41d01305500e50b90344d94107a40702014004c206a4080c85d00c003406054562860020141c0154428010148900c070400d100089a180000309805841e03400b06241c5044a00e05c00104030100014802c0da13070001e00140a00025115a00034092030200c902d0b003c02c40e0b0800c3d045c000180b44040c4050b5004030306050050040f003200e804028035104132425a2050308070070b0034403c1c0043c06521904003802005048030100000300203030102c10780f20100340b0000280d50f10802e00080b03200700b00d030300d502103000120388608a00c2c0005181d00305004e459480c0403800656586e950440100340c1209600764008261191011164014294801840d1009500e403034011004c5c036540c0c103005e120082031240c4400782800c0c5000d4542041c4001c020103454152a41028038000c0c1016401000079000001017889810456100249030303021108180c42e1100054140103046400d82e2290114801400c50361 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 688943920 1250 688942670 688942693
    0xf0f040b0706051501020c09061014070804060206070c020a0306020705030c1002220812030721050609060d0c05060a050c1c02070506030f0c1303240f15030b040203 72
    0x4000304001c0d03100e041d00040707501d0a1525030119601144000e4110f40c446511100151928000950000021a44580382e1039501c1011950200b40a521030360076500460b040d0b0801404c0300150065032003c0c2c0079100700d503460f50400c0b203203031101c5400654000c2560900b0030228510740d0003015034900071010340346050b500c1000c0c0d40c40c002519003012280f640c0040c4e651f1490145200d400710541250710300d01d4016180c440907a83d02c101ca40f240b01c014a6000010135040e5010b0240040c0d4040341101d02041c3c56100010783c00200b5007150001d000b80f9a190009182d0320b000041c0c0c035460390748144c0c442d444a082c1000d100c0700d078104440c10003d1084c1080221482c100130082d40d042c658010144840c1e09513504c0000b810101d071503005900a690600c01c0c007030364014198216601144818085480c7c02d02d080a4101c0d01c140c4e170380054144158120700d185903a00800081d80f84a030111001e02c000e103008d02d48001140e1b5880900e983c0080750300802d1001400f000043c40d0068002400c440c08511407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 688945170 1250 688943920 688943939
    0x9040212130c0b040b0d020a0207050d140c0a12060b0402040b180f1c060c0203040302060c0f010501050105160b04020f060f0406030b010507021f110102130603200f0f04 74
    0xa03194101440005140402000303a0342e0a00e034054500050001d0a0519107241d144182c00741610800c88543c02040e43e01003140700300031031030050000405889411001d4141075001d051400149070090203084910303034860808030051000c81e214520540568110b60315201d0040607008030056016800b000300141340403400d005480c81e000c1070072203508004441400c001c4882c080507040384c0148e03903036500c0c0707440a403501094208441e00305601054030030310345008a04600c40da070002584800003181a0207243c50008045507191031a00081000340d803200019545409941040f03200001400c081000207803458400c0e60b00288058604082d5289400000700c403030b0808400385100c0200480e00b0845d859042c021296010b07401e09005150403032070740202d62115842100f40e042c0c0600c25880e202094400c038104c0c0e49130b121500085454008507950011020481d1050000090400080c68000b083c909001e0342058100f00c4040e1603d121952622019000b2120240100500b40000241c1c03c04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 688946420 1250 688945170 688945207
    0x181a13032f0705090f010b271009060f1121070f030305060307061107050108060d0209152e0e060d090605010e13031d030f0124080d02060408090402 65
    0x1410005040c9aa050000340081d180300141604d00c4040480010031204c0c00e41d40c101c440000114000e401c4004903480c0c0c02035840c8d00c4400355908174240d6200684010790010307044080e40d03980c2d524030324594442803080305e003c140c01105181d203030401c500001c135020643d01e10350054990117444904041c040d4540404004140105034080ba4440003040b82c07a1506102040241c0902d0803c0f0842800302d1400d10360b41c40c00360042606219401022400d030740e0f07420702c0d02820141e000788040790364941205100b0b446040c2a0980d4004d101d003000d000040d00703101000b8001c91480c1c00100c0341c40c940000049810120340719089400507002c00c0100f50b4103005025490b10140202004203c039407601d01e003400c41e404000c1a10240c100a0400c2000003039110309407908014040c000074460240400000e0b0400302d4980c41e200d01e641c40c11400066459000b081e042d1104103802c044140300e80d94034501620780461034140740c0140c00440c000380000d006200900100c1c640580014240810384500c90302105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 688947670 1250 688946420 688946507
    0xf031103040f0b09030a1d01050919050405060d110409020a0f06031e0b010507020f0f18041407030221120406030902040608030f1204050a06181a1303 66
    0x1214210100d0902400f000795a8114551100462800d00e040200402d120f42d02d81c00b02c841000e0410140d400c5a11400a0703c80b803001c010100f15010122042c0310103a18014403940d4061f80c280300c006185490034a080340103c40c0c00c40034044010b0841000c1200031714240c0e2003240c0c000c07206640420701024208005010b450744e0b40740001d41015941c5056080c42d01400c0c00f0311030a04280591440b81da11505580c0c04c643c1c1915008060032200c0009200b40a1022145400640302020b0f07d0b8200b00e1450f64070b00403800340808100300f00f0391000c81620780a241c04043c2d04036040e02d402a0380100f80c000b02e220a060003005846c00118200c0000c4140d17030040d4040c4001903110024201546840c6c4250300041c00440019841e00b03103408110203850180c517128421a51982c0005014000c082c00700111103544810104450ba0a090556005103419001541d4181210001280300686c0e85400c03030080505c4035604901e8152603500f2240300311800c22030700303400f500c0c1c590400114101c00d000440e480f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 688948920 1250 688947670 688947683
    0x9120a0f050d02010506190905130512070201030f020c031e1317150106081801060503031908010803040b03131109010b0a120b09070f110a080d0e031206010f03110304 73
    0x21940303032a0090a603207019100b03602c1141ea032101c007010a0310021f000350885129843c00709965581c44940303060002c2e14000035145000c0e440e00e00210b030400100928999100b42c07000c004c102c9028550340200d008035041000c0c150b0040200e606a0981c00c19240d0303034070a4045110349407410320407200046490640c081010300c801d8412110030030300e0030311040301490140030206d00158034126004103d8500074204c03458800c200700c21188030030801e40100d0050720002d0110b940d610440b59019601910344840d4000040c1c1800c00400e1200e404000c460446048d04011402e540343c82d603109103401c0960204917898440240e40014540315052000e008011005040d619031074003100240901c444030110042003890078040030380d955580f081840e042402450a9651356142100c151007101e140a0041c4151043c03081c010304104202005000e11121943c00f4000300c41d070f4007503640e980d02520140020302e000b41000945554803032400132071440c06914000c501040e000c2c0c000d04041d8030549003929607 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 688950170 1250 688948920 688948933
    0x607020a0b2b181704120b06010807090b030403050d060e07090512010c09032a08010c0f03060e070e030c1c0501061205060705030702030f0318010c0801060509120a0f05 74
    0x900107003001903500320040e000c240300c2c010040041080940d0f48403801042000c4a492152a030015402500d001d8041109071191503c441e09150b803110350212500ca0004600e1030020343c1082c400d44000045403001e00002e404c545031a42c2c01d591582105900d01e5089503501d00000e1070034110102e050141000c1d485410100b820681403100c540b040c020003109681c142801c0d00d000c20742c0481201c040365000b00141520380d2010b40106007008031800c0d80320b0b51020f2000e012980e40c0042d8071409080a1503280c0e11846ca503180c200354183c076040c0c414610400030560000342114007030792190703281c0321004054968a421000c00104031020310901c1c0d04480c50001c0001003017140910410300a8900103000c40b8085078540d56541d07039540028000401c0040200100f40b450f4000c0050b184c115000d003c3c00c60f10f03450000d41c200c03071107a54000c490303a00d03600f011100e5820f80c1c09507682506032501c1d03a03582841c01c1d0b41c060a000b07403d00a0040c4000d14030407000481c1c046020a00076040040c4210041c148 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 688951420 1250 688950170 688950217
    0xc1b041e05190b030309090a14010303020f0c09071704030315080d14070b010540050f0709060c03050904060b1306020d1b03111e070902180607020a0b 66
    0xc40c2c0d42d20790110340041e01d000d000381c01030b98000044d40d0b008501100d81c0d184070742c1c1e11003401c0c1c081c1c075103501651004c420010000c41010340108003940b0b14262542140c403c1030002d000c01181c4041901c2078408150b400720313044801c2002e007000c15031090180c240890013070410049450308265a80c480f00141c0c00180040d030f4400d82c80f4010002c0055004000c82c00c010345c644510b648003074184601807151248030180d00070304880b03c284209045a003000d807002c582c08002c0c0c491178000c40107036140610303260400092180042e6007885000784c2043ea6a03050f094101001918040d40301181078051000034003501c03440d6503440c020480075003041c0400c0c41d2206038507100a04003507040c2d04810155080300b420b1686040d8400106040700044100c040402c80c044d05007030718020800c00250030a400381e1940c0c07a020b01450360304491206a03a07021181c00035901e000d90007c80c06010700041039600e41c55201919841e00d14040c01c0d509000400c070542c141d030344401c01d001c1d03940076800314100c10b03540301000708 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 688952670 1250 688951420 688951441
    0x30301060906020102180d1401060801021905070c030206030a0e060c190507050d05160609111306030308040602070c080a110a0608040305070f1110030501030c0b0c1b041e05 76
    0x1c00401c0705000946c10418800c005880c050300b5038007001d010f100405910307800c0c0510b18010004415084008004076611420418007035400300400c41402c420300064107400d0341c4200c08032240207401a10b021401c134115030800c0300341d510140040126580b01c0c0e4040b6100f200c1441458000e03110782e007166990b2848010101310f00c00c681e1244006001082c2b2002011130001b29080002c0520f502d00940e4a1508035401c804c03013002d20602802c014581806039080086080030f10b480680121000110404030884000035100c09003c0140003031594000b081c000342154000d00f1101c0e21030121030600a4031056814035100442c1016a40d15220040c000d00504065100e180030740014035041c0440d160548000c1c000b032007400300c01400024281c2d0400309002203904441885480205419880020060010080c240030300090b54145a00000003500960240840300990031000117000c4004c02e4140c03140b0701040f07000d000c94001c0d0302c0f65a03125007200042c0188420804100d00021507007082d00380d48 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 688953920 1250 688952670 688952687
    0xb04020d15080102030c18040908070501230702070608060607050d021510061413030206040609090b0f100f180308030403020d030e100f060b030f060907170417070f0503030106 77
    0x30b1564810028810900075001c02c440440a062200c10703400c1103c54080780080c0b00c0100081c0031700b20046850300401034103420041101c01d0320603400e850410104291403c3c4a0283d03010009a03210340e000708009402100d0303039580b0441c005c0c4440d05001032505d40c0c50400205681101c0140c01c036181581c880d148498070035401140521080c00510708002001d00290f440c64508200320300f0118801046c0f2621100e400b02031a405010035481d1075686c41c01070108800f40c09860852802c0800440b078504081a040001c50402841c1300e4030101d00d81815183c00180001c18800c1010580c60031302c0048030030011200441c82048401c4e5a0302d05401e000b0305001d260308005c4101403c06038142109140016501c65084902c8000240c80c0030741c80c0c0b000e004012941c0400050680407007004082884424414405c21b0b0544d200425540c1c1c6c80b000301e8080c02240044c007144010040420046200c1c0715100e04800074141c882d6240c041e29844240001c9450b007402c44e201c0d403000005010f91617115118 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 688955170 1250 688953920 688953929
    0x105180f061314010f11041d0f04020108130f03120506121c0203090904050a2d06020d060b070c03020a0b093d0203070b0f090615040b04020d15 63
    0x1d0100e505000711606108400c081c07000c1c262a4100c5014901c0a9003940f2000c50300c01240000c222082d0600b52641903608140b00c0e03071408140180461814800c1c00703000c0b034456038005800401550310341e401904c8540d00039180c80e00e20380a0f903400e140081c49607006c0069441c001e44601c1e018081c40040101070310001040c0d0350007001c02c90b030000c10300000003800d08518601c14a14091020789000203d00e14051800d01c55400701110081c00301f03008001c0344501106015400d030440d510300b19417038841c10000c030810110400352403001400104000e03501420f6444007030700c4085a041c0c0c3e5400c004506401541d02030b00c00000140c070030400c51808400170300c014070900301144e046c10780d030308000b803028100f00651180700000d84900300c0916486040ba0480c0d030440821105120509010003580ca802a5100303c1d40140d008001c980300c5030080d4601445400500020034803030750b586258100c4103207810203140e086910f500501c81190782d41d0000d0036a8100401001507114001080000a035145500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 688956420 1250 688955170 688955173
    0x605040b0d050a0b0405030c01140f1605030103030f0c170c070807050607022e0c060c030207021018170a0501050a11030610090e01140f0f010813020f030105180f 71
    0x8440015404100584150f4100d40b0100055485090031b81c01c602c03800c0514a940d510307103140261050012030000c0d0003981d1502c0e2400c000d940d054203407107060741c010030b101000c1101880104006071042c40440c44240e650310340036950901c1566980c0545072001d06140b01a000401c85500c0c3c000200b080c003000340f849500070880d00d40f901000c00c0b024030031518080d006402c04d40e80840c1c1e40c4d4250784d07a00e40349801e410b6607805104141000074002d814403407040350034034107010403062034a00c01e000361002150014080342c00003c050206503005d0003c03030311003c40490b1a80b00060425000d070300c1c000c105030140c4080c00307814a403071810900311040204240081403414178100000003030300c01070741d41c46002038803000c84446800109503504030460780094070328003000c0300100343d04100c0c1240c604010340c05c3e99540c003030320740b41300803c031400352044075490001312080c0005844030700040d10700c0400c40c006403002210100c0d060101c0d003911030446041c81440c42c1c444d40c01d0158082084821482c219220 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 688957670 1250 688956420 688956439
    0x120406081e0114312301061b0302190507090608061b03040812071d0f0d0321090b011a130605030712050916061412040809130605040b 59
    0x4003298078079010360000c20b02413800d00580d40008401c841d2440c40841c161441c10390b68061422010002d0034040c2e074070b007030320014094141e05052821030b803550503140703291616141044001d580181c45281008282c08500c56078002c0003848035000041c141440c09040038158090800481c60140c42e400d07400a00b480d07102104114645c6d00e00080d03140b02004044090340d99444a0030b10040ae4000c0c051508489400d1109014402e81c0043d2034107001803540c50340b00b02c41988a81040400030344400310700c0c0c0000c440c200c0e260000b84a404a412503142082140000d0100452200121507071040116540c0b8040801440a5418548800c00b200041c441c507514010009a04000d050110321828080c414040003107281c00d400740c044002c0061700e09004110030324010005955491158101c40c0142038038540c0070490310711507246949944060515280f410361000030050a00c3c0b001801a81d14080c203200b884240d5460602d4018804001007010a9041c10202004201c034480a00349105000b0341 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 688958920 1250 688957670 688957679
    0x807050604030f020d1718090115080a1e02040e0a0e1905070b0d0209040e010b03070608060f0612090708010b0904020103090f0c090c0e060c1c02120406081e01 70
    0x1030111020350354009000b01c402c1c04a48081450100215002000b4410303031441c0c200301c0090100a030080c2034644402440c20300402c8244499000d080c001d05081c0c0d10a401d0b119440c0c1d018582080e000412544c001490064091459a58a040044c80000c45400040c208241c0d40d1809541c0d07040701c01050300308091403c8120950381d44940050091107c02d034848601c06104c400d122650051120543c107699500b16516418025400034201728800ea2074000c08a25000d41403269240c80e40000d4002c0501504290065400e04001410594004808074055a07243c03a40c2001d09013000314070320089490308000b40e10034144051364000d80c00aa160260003919942c031070303010030707000754080c01e00041c00481e5040008641c2d401108c003400c002d17414140010031b145c40c0e0740a07001500c00350740c818040380e459a041003180d22401014107059032001c43c407500306160350000341c0141005401158100000c03803590603041c0e0081d5100300b010032840400c00c00d242c0a002c440c513806443d50001c000556042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 688960170 1250 688958920 688958929
    0x102060117030a1116060c0204050f06060301050607051c03020a080c0c060412030e01061e06030203040804030210110609061009090c09021602040e03031b03040816110d0f030801080705 81
    0xb83e201d40c90401041c1c1d402e00a848000340b04c5840381500600b04c608120b03884442c0502120f41031442240200c0ca0b203c00643c0e42c01c03202801d00d003d824010419407039a4a02003c1042d243c01c03203102601e06006039000040c191401d407044031048255a02c0c0562128103d82c4094050b0030004c28500050408104402c0c1b0729402144995020307a0202c05540132440804040300180111003121003298a080b00214901d840701005c4000001402d411014032038941c10b04505178002a900100110740c1030205000500d000643c1c00d04004241c500740110b003c10b03580d1907140c280140c0e40100a03401c110b06000019000681c0d41000e061081014407030700c12a9a80d64081c030303c59102d01440e4035404039601c0310fa51000c078407032440b2540041091085480b41d1524070380342c1d813081c0c0e03046041e4100b1141180c0300d44800d9054034407a40d088002941042c00d074070700040180982050848003500e1072006082c81786c2c5c81741c0440b0b0003540692000c03204100c0318a806442d015040c0c12021899004800c03c100750381e036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 688961420 1250 688960170 688960177
    0x60106020c061305030610030c120512031b190215060603040f021314090115080a0807080d090803060108101202060c0304171b0414151f0c02010206011703 68
    0x41500d0b56551003910000c4250441055000603030b15004243c14021401010864001a24018000b0349440f13650ba4140c200b002106000040140c1c001c0c0d0f20320320340304601d0806140c2c4104000c0381400103112503e078040030f65100b0707925540112440400c94107107c3d41000101d10821035691601c2d80707800c1100018035280001000240650781001446045407076802030281240724107241070100301c0700b0180d03040d0030000131a041c0d2210b601c4e00200300f074080c040c1c038504000c86155402030119180c50307440742121644510000e03a85180d04105447c1240450301c07540302028022400151030342400d80004006400260020100b00d6401c1000d00c04010246140382d500c0d94129401c0b0703614100010741c1400c4d406164080584040c90b852240d00c0110081088445020081d4401210034103007000c00c0101d8003110040b1000070900d0000800c500c43c0040c191005890040c2681c291164800440201c1d1016145280001d840c102c3d400e002c658042140341c1c094101d0702c400784030410004607260ba0343e02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 688962670 1250 688961420 688961443
    0x60f010506031311040e01020a11150c0a0c0218011e050603011203020c1801080f1c0503041104050103060b01030b040e030313031106040b1008030c0d030e01020d140f0906010602 78
    0x10300303907001c0004c2000e990f01c102c281e00e0300a4002e00100d505003620718000e4005006000c049070071200001d20640021401c80c4449000c0c2e022412130f621b0728800c10505801500d400000d0141140480c000360f513a824a6010f124901e1000e038a166050011040481c03e903025462100112044203001a80e140d034240d034150341031301900240c05115420f0403881c0c040d682029540011900e0b01b00740e1540d815001c000e06030340d8000111181d139016150419511580c0c065444480c101c03101581003040e100390029500540034811a4541080e0140010100d0700280e2040714050342d10420b003420741d60540260112034400312410010900c40d488480c3e2648401411585101c82c02a680020180075902c8840c1540c1600c003224514502440c01c0032400e0703c203880625001c1709110000410990020444904181c400d0280a0a200400e000d9015001c00004802c05540034001501c42070620712400230701d030050700144000390501000036204490040c2801c61540c02c25401030000d40c0d00018001d4455 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 688963920 1250 688962670 688962691
    0x140901140c01140903070c0e0709030b0c090603100510170105040902150301290414090601091a03040c0519030807060906092f011407060e0d020f060f01050603 70
    0x54070500701150042c1003d030100f81141c901041400810b00000020304036052284401c1c0d25015222080a0405c850466601c0d0001e03070090011f00c00540301180e42c035040ba00d801000360a003104000050b00c0d9801c2140c1000d00040380c040c08102c40c0c50140095028103030070741000002d442075018410010241405110302954031008180215107680709056010300c00c2944540d280d50b1595000b02c207541071a21036640d1500b5417000e03904881c440e00200d0703040784c00318440d42082c0c034804400d00c800c6401c018001030604c8a407100005000d4840b18405c002500285907203656482e0502e080c0262020603042180250360704070f0b401c10032750014080001526000b07070b20385403a0342c483e01e404800f60a1102008000f142070180900401901c40d00041c0f5003215149030b044204119142d0341c0c0c240c03644c0e6141c10700040360310102e802d80002c040c008040890158402003a1144003118407132504504038005170040e40301f0244040c0285040c003100340c21241d003980030b0ba155490140080e07014000074207601d030381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 688965170 1250 688963920 688963927
    0x2031803070302061309060918060507120c0201090317040c170102070614040212060f061e0a080606030609010203070c02040c020a0c03031e0c0203030706150b0f070314090114 77
    0x40e550801a84004560051545035076410000b140300600034248160041c5500300130010443c001d940c040e848031504081750080f00c1e2082512207901808021741950300784900d070400700128000b6805100b1070194150008180c01d00280340060a288090403815509050030b07050200141400c0e88990480e80a031110b01c84280002c010340b40240f08080b40101100e14000c1084041044401d909205500031560001c2094144010303a0312500c00f04c07824408005a5000a982d500d03207000b9200c1c4056684018408050304030021480c0440b8039004280c0c60340c17001c001c00c84240340411500b68800c0e2010300030341c11030400700800b405100d034144000b88516100c0d902030420500c20480002c0558010b03480c400041d94030304000c0c11070030708a09114000e241e00c3d080395020a01072035590540307a901600070b515241c0d580e200c401c002e001c60a20140503e07040000000e5001d58100901a80030340c84404a685025611340642000900c2c0074a250320b0505020100c80c3c2d03030708060307030104580155900356034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 688966420 1250 688965170 688965217
    0x6060e010c080301121b0602100f090b07080a02040e01080c100f020616120510030516141320030906060114190909020d0603060c0201060b1b010b090403030510150203 73
    0x11030109011b40f190718100e140c0e07000035510360009224800321004a03041294500c108480c40a032180800301521803c2d00b14042011380c0d201d8250103500c9416007400504240d00e8107140d41d005442a07000203020780c0701c00701d03112080c90401c000d40d601e40da0b94140600101c448410103900c40000914010604c007440e0403000405000e44c00b0300d8a49105200100180c0c5031404030a80d4000d90380c0020340305e91040d800110214003483c0c02801c19140031080300c00300d4681c040c0402100070f1000858020080d02c4a95002c195100c982000d0001d0000ca40034a403030b450400e2040707240c004020300f4030f4100041c800e0101051000380040713401c82d00c0c00c80c2c10403990299280080d90848055800360b502541300148286800c9002e601000990744a030500b071003041000d030b00407403c0c1e4103180540c00c4c44520410149421218050b40f8403500c8135684004502c510150300000c0350300c10121001e4010a03100e108010412280188074070281c4800d8900d41010f03540003400a51f41d00896003c2e00b4043c11034192400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 688967670 1250 688966420 688966433
    0x70603050a0b060d1416023313031e120c020a05060702160f0b0306060705010b030105010927051207140601030515180a110414090106060e010c08030112 67
    0x715508000b0f000c1903a5018546100001080c0d14411601c85016600c04904810703007900c1090f00c9004980d0081401101215490212200d03a030b0240b20343d45000703007207014011a6014041e205051240c3d02e07542000c65424090094481103020040541314241840c5900ea0071440a010f8001e1701000002c110305002e000307900c1c18188039009400d42c403800080100103540001d500003404000c05c0c0805000d44c0d0703000c2d40151f0810030b0049040c02d420034000030b040b03801c2010192014902490020032010354210120782181c50a0300029000c039180d440440100f0505881c80f103503512000c414130320f203100c29140d076601d40010705100e050f800400604c3d8028480d9607135102d1810507200040d10025692840d040f503071084c051f094004062199030000d1541c14600c0552109045818060442c1003a50380c1c0c0c40381519541c81d581d0b07611075581c8003495260480141d903144941811800060711a0030500003402e09036030a0011810001001500c6000400c1ca45c00d6a0449030390010100c5800f45528103103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 688968920 1250 688967670 688967681
    0x32f0d050a0c2001031a030712081e041406092817010b03060f15060f0f070c060909021c0507050c0d08040308330f0d03030209091305070603050a 64
    0x600003c10b03400e1198422010f45406050002c03090300c04208910fa050005900310385d80d0001c02e640b6820040f0100b050100001912102e01d10034400303245000410700408220380502e0a0826085034089410711520a2514212511b444100d88081c149003030400080c2e94100700d0003245041e222a03090850b100607021141e070340a0301030001d20351010300202103a40e00034074400c20721620a115040c0460200380b801da40d014003e00c0d0b818401081841c01c44180300316a130044514546240c1e0401103032180300914000703484540c1c450f8000b6440c0c90b14145000b04440215007040300c40c1441040391942c0e400b5000c50300c01e1400044500825503580d4000c007a65940240c4d650081d1602861100310710090307001103e103100c1c91281c1c40da0341d0103803944840311580d00c04803010404284035052458002181003440c007141c0c1c2400411401250582d900403511100e0482c1c4200d021070340214240303a4510302000c5595101e1180108003a04241646559656411a00c03d8034180b55549011460001d00d42d04007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 688970170 1250 688968920 688968923
    0x4020906121903140406031a0a050102120c0a060c080a060e070509010e0a050423010b1c0209030a050d030e011a0a1a0d11031608060f010f0c02030a032f0d050a0c 71
    0x607142d0f541d964019000c8c2481445c54011114500d00c204101d260241d076141c02d03194187c0c02002c02c45060b45202c0659400380000c142648074058280c1c001589601a01c022040d443d9901d50b150f0070514940015684507401c403031500031041d8204100c1942c41003d4a010350710034a0951061445800401c007001c502c1d400c01e81d000390400c0c49540701080c842010034001c044020092034980c2e650541c0742428004c401d50710350001505494405030300f090360042c02c1c00c08001020b03920924110307600d0314a410044020302000c41d4076007800d031090900070b00c0780080b480d181d200011090b82d44240016000c9503103008612892010a0b5208800f1103000292400c4504286d02084521400101c0b80c15580040f5103505514071030501e000e14045c030640001b4041d00024203152041030703241c3d005650b0740c0100540f05003040403491040001d41c1c0d08100b21a131950194840051109851082e4480b0348001c2d4501000e01c0c00d01001e5000c00000041c98880809151800c030340c032601c902208403a041030070b000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 688971420 1250 688970170 688970207
    0x8032403100e0d0c210c0c090204150201090206030a020c0327030d020a02090105210703030e0915090105090603030c0111040f0b04120b0a1107061e060806040b0a0e0708010504020906121903 83
    0x4000c00c900c0c09649c0200151108039840f125032004220b8100c1c01e80f64040320094010304140049090800240c018102200e15101500d0410344041c41201d150109583c120403080003030070440606003018086c0b03400c0c014542c8081c00480205030086100c7c01418481c0f00e000d2044e41c021216100095002001120f188100b600c15041c0e50381002001507001c01d0466101d54001c5000c00c0703c8084200c9040ba00110103060f141031070307103000d080018810004117403c1c2c160008200c16640c1c91028441e005038030141c0c0303d070561914182004050386c080160042d00f021034081205001540e8044a81500182e0280e01e680e002d6032a103400348054891b4002c0e0126010002c00c00800b08015074111018841c501125802c0c08049038050b001038540324440c416140d0040310200300458013a00f1015030005401101150203000c43c0c80407407504900703034000120782e5511014003045103443c883d1190064401c6030106540503020310302c1038031101d10350384a141f4080c0c0b4460030001c050040c14440d680c200b2200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 688972670 1250 688971420 688971443
    0xc0d0e0f0d0f030b0915030102130320010201090312150b04180e060c040306330614091e1207060f0201061208032403100e0d0c210c 58
    0x4582659000d01d001520042220801030700601c038428415030f00d8240000782102c00784d44400703880110100c0780b400c59680554081003181075608507903040320006c41c803031021442859680c0e071b49280700d036030300d0900780e030469040c80200d1003c42e50201e81c921440c40c00000020781c0301c14800213081803400c03980c401044d040012034009812155440190a401d08881d03041c03100e6081c1807082625404200e940c611401c1c0300340014008034002c0d0380302d00340440b840079452503941c00000700c80c22140c1c0001000c03001201e41c82d00a1060340d0307100c501000c80b0700d508403105042c0b200c2c1800041445128503885424070061400c52410792b03848245444071180c1c4241030716035640d103c1400070561400c182c1e00b03a01560800d240080d2004a4040344242990440840c90458650042448408a0116041113001e007480c0c18060f6640e000c1c4109410300082d0308000071910f2003028424103107403a449044040c04840c007044070102e00d40d40a03580080b20403254620010030390390019181c0d5000050040c102c0080c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 688973920 1250 688972670 688972693
    0xc01060905010e040201120908041206020c0303040c03051209180c1908061503010b03040b0606070c0e041101050903060c1b011821051c0605030109380c0d0e 69
    0x120343c0103004034001e036117080800042407144000e0ba00c142030024002c800801013001424074801d0441b176000e00c101c40240c5020601c04840d0701d1904282c03800d88540c01503402c1001080130070803a41811580003502c040c142003400b0006034404440141e0000d03c02c034082d00050340c1895076801c48601c40e001e0b03130070100c0c40c06480e207008007c010102e490901070362280500b50807400360102034038100c03229101d14921316655030f0741d1940e85407400b8114681100041c8030340d40004a5201865010b4500740301c1082c0070785018100715109103850b034840c41c144a000c2104001c1528007240d0682c0c0f2102e04616142c1d074566960954085034141061084a54a044c1030492032440c0404000c0c0401d005072500300b00303514040f5186001025035404440880d0b0b0800225241818603814020005a12000041c00982d45d201107429030328a900300b140c21102e410680d080000c451203c032580c5200904241035082058610100642800340c0381440325240416200208211500030032148441c0200351074603007401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 688975170 1250 688973920 688973939
    0xf0f06300b03060105031f02160b010b03090d0309030c020f130207050f0127032106081c09050a0618030c03030c1104020304021c03030623180103080a050c0106090501 73
    0x4070791601c60b0164400001d15032800080707018441c05218610324503541c40c1600000294459007052050650b103184400101f0302502400d0f000300249a00c065407864408c5000341044500c032075a00500d40b4202d84400400d40c020380306815280d040d075008140902503000154040095032894090fa80009908406c00c100841c603070580c200350300002e104082d001c2d00e0208000c40c0d080440c05007540820b8504010034440c04001a840c0e5451003207e80c1668020140c20a6030483e4104201a601c01402e1140901c150940d0a82c05a02441d15148642c10b02c0001000d00c00e0078130030b1030100048a500d034811102d07a02c0c01680190307800052400c44990720f1070040d2040c016500d095030584000401c01c4144d051070300840e48666801011500308081c0903800b60b40303161850b1015801c01d036841074081044010b125031100341c000c0300c0051808a0400c1410007800202c5019107041100251004100240001007601c0c1c90400134142507840d003a42032090b80c01030140d50304c04401c1509200000030a84078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 688976420 1250 688975170 688975181
    0x908100c02010e03181915050403030e2d01050c03040905040228050d050123100501021204060302030c19050909010803030403020606060315040e0f01060f0f0630 71
    0x2901d8009020580c0d6200c0e5003500c0f401034403a294007000035081142c0c51480d0070340c00050b03035404224208000316104e49a00c002014542000c2000c078400040510515810290040c100341040b24441c0401c4075541496002c00d40c09100c10b030038103c00c20740c500315980c0110b055407010a2200d08581d01c3d96943d45140b0003800d4142c40c10780c0141220754480591030806000740c0740d00907031101011817035482c003000d10903040c0f014001036071155a1954010303401030500c4186880c0da518080b502c034060600039112250301d4120307480681503510034480e2803035101416040da0102c0f00642001622951000083c0d8624411a100f2500f0130303196183c26040103400401074511508192120200c0380e0b00c44550603500e00c41620050702681c040b0001540d2031602e400195400700340440e07100c09100040000c903050310341c0840788001c950461202d682c0450001d2080000900707000c1c0503144100d1401c040a503c91703150340504030807c4a00d4909642c8642040341015110b601105e84111104440c1e070003800030407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 688977670 1250 688976420 688976441
    0xc0111030415060b0307020309102a030212090f0d020f0a030311070501090503030306100e03030708030610080105011d0301090b0a05040c0e06010e010c0204140705030405010c030c05030412090810 86
    0x103160800116180c4e0303c1d6000d903882451141c0003149048480c0080007405e642e00302d03400040200c02482c1c05040308411000c0d00c101008044c4840d42c80c1107900d0081c0c1440c045104004c5c0e4240d040c00704000540c1c90100b032814224041d02d0302507501c80c882c000304185ca01d60320545078111011080000c20142d00404080d1200745980981c0d281ba07440341c0044501c4407162044660640c424000315115152202c1440c40c80b441d50301300040c4c91030011000c03904581009030240c3d91240007200f001407a0528150700664140b042c030700200d4035030500340040c1c0094102c1081c07450300c2e04586180c842c0e0361000d41c0902c0950780c200004503114038000c05500081c0c1400c940c00c54094101540024010041c02240c40c016001612000c103a94509401154840c510080c00d030f0f8000d0f00c0ea407030b2032107144000d4002030007040709940e402e0341c030b00e03003814441d081d03e01000003401050325000002c4c1080d0341c04000d41c2d4216500900c4181d494102240407100c2440d5604031101e24040c0030030745e45590455500c1001ca06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 688978920 1250 688977670 688977713
    0x609050601240815191401030f06030521090d0b15030105040c17120307020304031e080301090c050c06100602070e01120219090603111f0c03050c01110304 68
    0x41d03640301e000221812842e544010501060100f681d11145009402d0b070448007070021440d00b0004400600149810390000250541c407444041c0c49503414050626196018007082c8103252a55031810340d01c03400b034001880c40000c800030088945110034125081e80c1001403082410074224141005500e10550301d19520300d008040003041405d0602440303101da40c000901c000c040340391815103000003c0484002d8254081c029130344c400448080d01650041003654001c0d900c07a81545404900514011900c0140081e01e1a40a0009100504603410740e9140800420000c1400500366428090700060b451070340549070402004091000440c2c0484d58607608075100640c0d10524000d4940003030140c1116504080035040150a1105144100c80180146890030756903490155084420a030001c4401b003222801c0e600311884c0c000c411031b0314107100d40b0600c88030000081019080e11000b02000303090003400718a090106400313502c500413420346110055901e28040c50000c00d1080c01c00c8020307040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 688980170 1250 688978920 688978949
    0x3180203070b0c4605070603050613020d02121b070f0206121806060f18060d0506010f05031b01020a0609171804050115050a030f06150e01080603030a0e0d020402070609050601 77
    0x704641303107041c4002c59005005050304904150049002d00300041aa42d001100c00c81c50b5903c415051000b0030881c205d000005844101e115403424903aa0050003a100f0041003509102891307103e9011180c0085e841555052400320500c081a01c80c044d118002040e0034501d070070040f003007114a0517206080212002c2e00c5c06a55070380c04100c545074a10f0380c02500a0b100c00c1003540c5c61603485c5a4507070000001450310810303038201e68030645840b400740c1001104440c800c03001c101074201000207d00c040c80c0f40200340100d210782c00000f0350303d864070b0401a00c1c8646491004061200031510550780d0b0000f2140d60740d8880382c3ea03419820802e50203000c50301640c941400021400c900900700741142032075607039181c988910400b08030080c142a02c04130300c0555036458005210090214141d03040c403007a46403070031041c90503030015001c82c000400c254029041004106940d981c0641840313034400003211080860031450001c50300a02507440d0080216140541c0103040c03207000110207040b5041d030383c1301450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 688981420 1250 688980170 688980283
    0x50402040b0405330a03260a080c03040c051002010b0a0b041d0a0f05040c031a010b0f071b060908060106090303021207060b13060603180203070b0c 65
    0x4a50741140c0c108100614066a030840c501c141d2080c41342843c41601040500c2d11950000b4120912a8011070f4032030040040c11045a601280244403500340b2003200b803c00c45c0720b9030302a04440c0e008201d822400c030001300060810150503c5800540343c098942007154401c0702003c2e0003821a11140c3e03204410761100094050020300c100c03810784031100080342c6030040107814480f20000140c1103c0300c00786c548512020242d140d01c10180b1840c000c890500000d880d42c101038000c403021007600d21035206014014441c1104480460305400d001c511280e5942450f810000e01e481000c00080e4400b16800200242455001d03035103009580389401680c9190340e90f10b0040c2c4550605100c000c0250700813074046030300b1000c6500644915030180d01e0210b80d40d80710800007850405507040d10607041e99176006c00d010180d418802c4090b1f00d221248813418215003500081d56505161041103084d031000124a2100c44081c000f907100100141c0d244800100380c0c500f07003000f542c2c4400e448c49010042444021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 688982670 1250 688981420 688981429
    0x5041e09050d1b0c0303080402150a091a12071b140604020319050601050d0c052d031203040b04062903011506051911100212010501020a03120b1c030201050402040b 72
    0x40e5144e020300500b031024503541d8192400c071001030003030342e0045524002107442c3c00315100070309029050755234034072506003040c120052102c02c3c10150142c0345400e000c400c0314a9006416160002090300780030603402d00300c2c400c2800b4200f24581c018003040304c420000042100000d040c034001ca10807019109055a0a00c080140c50a80300b80500a40d00c1400108000e0070042ca5080d4214041c0d400b00c0091915580414034010822a0030070300c01c1c0c9483d09544004070400005114924210080c0c001c0c005e02c05440840d80c04041c0002e40407941d82c0300400c0406c50315070310180c0701c20f5030b2401c00e5402002d0190a0001c0e01d08071441c050182d400c02410464060558044030251100d0351a014100017802c510313005140003074404041800001000400313034160401440d04030119400c0c1c09030ba140d001c0f4441200b0050180d201078190761100c1c0e106c80000e50840c1d0b620700286a07014000880d4143c17100040c28184c140b022014200c54a80300200600d581904080e00c072345c0c000e49050101940003020300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 688983920 1250 688982670 688982717
    0xc06040b0c03071b0203010609060806070801080d090603050c04081e010c020613150b09010f090605060406020d2607030e0615060a030c05040b0f04060f030e0705041e09050d 76
    0x40f000031040064800411560009101c8070f5001070300000d401903c03400080219465600070b00c925500200801250a0b4018041c0d400340c100580a400c1c000c22a0102408200c9140a41c50605413074400148008010300700b41e0307009190356800c0b0340c032210b030040c10740c0e01d030f00a44800c200982d400c0503002d5034591300008015000300208683e1409210654541d503c0c0441c000394901c5c226a22140c2000959840d843c07044c6c040c01111810110b070500c2d040a0340c003218610390000d800b980085c0410003410f130300400d8032090207040d403d00d841d95201103408258a01d003050f150900800f146410b0020b902c0c2c0c15400360f140e80720004200c44042d03c0d07141203010041c644400c145d5001d48100960b04500d4465000f458503030000781042030800d0785500e5041001c0d00b240148248400000c10104802c0340d011580d0300440c4080c1c10100010450100840d844140d64020a4004c035101c078981c00c020b04d41c4642101d1150760351082000641168a0312685075814419034074001202c40d03080607e88181c0e0341e140b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 688985170 1250 688983920 688983931
    0x140117060f1206040804030b130f0b0402180f01090b0109051804051c0f03050135160b2125110a1b1d01090c0203070f11030601060c020d260c06040b0c03 67
    0xc440c022215036510f412104bc020300407604801c103c80c1c04590400c2009a16020b410350317092032019581003441001c11148000d04035410800301c90302c1040a03442d4850450702d143e0110244e03840075070b44c03410704a1038541d4403030740c03210820411450400800d42c004c4400e03032102c0300741d5010b020341e985e5840e2000b0308ca019416958400b0002030144c414050001c0d8214a41c1c2c05003500f0703540d0355030b04004c81d00304101456011000308040040c0c88511400ea000700ba00307411b50f400d00c0d501020308058640c0f00c0d1582108080915404000c1c0040780788070701620200340034650020803212801c08903c9c009002d62140c1014084407031a01101007807441600d0354400780807511034001c41c0e0980c6001c0b0250702800a1004603015400100314201c085901154008a094014a1071076080c80618050528243c4168007810030013007213240d000016a500c41c0d201010382d801c000000b00c051600a841542c010000080e13520b002c0001038407441844000c940b00340b0490003841c07a9107840e6aa07107813513102c44c40101c07035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 688986420 1250 688985170 688985183
    0x90a020c0c0d05011b02030c060708010806010b09060d020d24140112150f03050d02030a05090108060a050406180b060c0309120a1b140117060f1206040804030b13 71
    0x7210150402207a10401240180c00101e803032100c090901e81c3e0751300d420003400016000040c102e09403140c10040c1a4100840d45402d000a40c17401c0e070000d071200c0f4103000c0c440c202d03040020034840e150b60700c6082e140c15030b0403400304641e50014000208010308000c245901c0c0540d8102c010024001c800d5008012109401c8080c8000442c8500442e2620f8100c48042509641e803512006281c4003001107a0140040c03284a1a2940c10344c10300515125a00c1e400000310340c02007200c6490198003009440020800782060110ba80780c40000402207005501b0980d0010b24105000650003440c80741040440d40d08201040301c1005a828080d29114907101d51080d64001c2089a415090890103144000c1000042d40c0040c91107076140c4001c0000b0402001d94244810030610038144200c01484900c03409080441c1060820550b201c0304501c01021548150301440f0040501d4440d1700010004028010541c0c25030314040c40e04650540141c0015940d0f41c10200000707142e8001520800481d503000380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 688987670 1250 688986420 688986433
    0x4150e06090d080706050c131406040302010309080c1618022d04030f030f090501020303160305130501110a020c150301031104091e030206060607080910030b060414090a020c 76
    0xc0070b21810358500c0904480d070030410071214000c00c00d907204050103149002202680e4010040c90070020f441c4641102144d00344030340341d04130140e480300c040764102d070303820300380425414100d080149082c0201844240f00b402140240060805c04592010903948080c40e101c0c0440307000d600c00c0c8203c0c020342118030102c080390000c03015081c0e541800c244501c01407103100c600d0139031207603940e8903102520141100802c3c2c003030000064880d00000604050b140a200440c211b150030005421345c1220016510305240d6140c0104128001c103100a0a05e01c2d0800000c0c801c104048800b41c400d40d00c1144528010300400c0010b0b00303245040050503040303d00840780035003540d08540301d8081d84030700c810a455020b0303a00d0001340d002522640b040e0f1514a0b8a0cc1d00404607141c500b406802c00500070680c40c8603810400070840003903a40c005450300c418050700c42004c0c030b030710707010b01500207241c02603030340d548040e010078000341f51f61404035041800d91054502105c40d07220f04031070000fa805110581d604a407c103c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 688988920 1250 688987670 688987687
    0xf06062715080d05180d05030306090912070f051b030709051f0806090f06060d0f050c0d140f070608010b13050a0f03110901030c0512030c011104150e06 67
    0x141c20070480c1c864419400da611641e680300e090b103031240c08000500031a002080340c1044411002e4a40300c9103030107480c24000c2c01541da560640381e2100a21740e61003881180c0202d580050200194007000074100601651a00325003058105459003a40480c0c45100741e0964100c5000c44140c1c40d44d44001c06401005111b00b0411800041d00c80104150703541c41d500041d000e085800e407088030000b8000c0c400904402d040c20560141030121500f46886d80380d1021041c800c09864001e900d600c015000301c1503101c02e80b06490264185202207404c036074091080d208000910113003035103d00340d10102c0f0085506146015846030348680712440380d00040742000004200d840924401411829a40170344c212040e0f494000003150180c5982203140f22425000040c4104a13002812a0f040c0d0001c4880300100d40c59940c600c868650140241c0b802001c201c41102141c01d402c0040d501d5180f402030090003040c050800a0346584c1261040b02d6101c3c0c034000505484601409c0c905c0400d03c0040c0c80189400303080d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 688990170 1250 688988920 688988999
    0xf090506040209040305121302010e04110d0b0a0509070207080d02070321020f010603062403170a020f01060e040b0a02070c0e100e0a1a090f01091e090f0606 69
    0x101305505010042154904814030071800074410409603000d0405105103000041072107110300c48441c080c40c43c00b00128141d81400041e15448004083d01082c441000404520605550b07840341d90006154414840503c0d004581c62081c1e42401d03003194108808800c00320303501e00d600d11003d4401c1038004503412144000650070700700c2828500480707444846129125003166003c1c0d01c181d032007554540e071100010030740e0750b0280d80a4038110401004103047d52106040007100d0710100300e00400c00140008050300078401800100f802308002c2240c6950385d01000b544501c00c80c1c00311060070303913076002802c550014805d803084913821080c6003417518144100f90f180d070314000e00b84582103191064009082103640c003120380300381c14908010400b0070032411420441500c14030054400c00d0014104030302c01741d0310000e0904684499001054980381740203001c440c24405101c03d00c46c58148103400003800799208003d54503901c6007804104403a91000149018254140383c08800300c220722441190740344 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 688991420 1250 688990170 688990189
    0xf030307140304032006070e0607150f0b0a080109030f0c08070f0804051519030c020a03180b0c0f0d0801082e020a091503020a0801032021010f0905060402 68
    0x32900b084915295240c43c41250170361784100990195001030200312199a0010703107424101000e90781207013040d99503541c001d82100c0200c000c05d40141d503403180c4280540660409200010080d1900c13442d40d0311500d0303076406000c02c1101540801d150b04404444944141d01003041c0e00d400c01d01d554100421f51380d588030f090584d002e0a582d03c0c4020310011030035503200d54045440342410045169958410113810b07401d4030000800070141807610382d02003001c6070089240100c044c3d0619004100450310f4101042001850300301e05804503010480040080b000228a451101c1080c00c80312045846141194201000d0041d0750498100007042c00340318045120300c0545201214001781c804140107a1f030750803a0403100c03404001030740342803040100d07007040348141400715210326003036140011410380541a4241884001d22640340030503c0c412003920540907042c05040242603148034a0b1004554103030140300d941800ca075529101026940130a50f100700300c0007a5002018000c0c590b21070702000310307009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 688992670 1250 688991420 688991423
    0x50313080706110f09120a05060c0307030213320a0b0c01140a0b151207140c06090102041a0403050705012006010303120609020a020604060f0906020414030f030307140304 75
    0x161903c00100d0b04095050190414945a00805881e881a80b003040714000300d11940441640240302e0031400300e140401e12661100100380aa03540303844445046000740300d1002c60313094007071a4000118201040c144071030b00b01d5400058080e0100310756000006400349061420f54032188488007003185007c0e64010b0005582108000240c0c079140403142800010f0455401f13801d5a501d085c40305403840c00810303081480070b0b9402c0b8907050045e00d0340b058044600162a01c014028002d45191017501c9240c102d0300052202007d944840c240b14507100d02035007003402007402c0ca00d9218200030302103071803d00350340c201e0ba0400020314005207007000544a00c1c0704842004854214043d007113181260030080c190003140f10f540e50b14400344060000204440f42500440e00190042014444051b40095525040f50700311600044034a004081c2c04010105000000e0015002160004040c1c5211340340030201078040e8255007500c0e82c440800d0340c0303900c0219460000700d014280e141000031444005540c2c020b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 688993920 1250 688992670 688992683
    0x30d08060103141501170c040614040909060b0f030c0102030909070905031c020c0607120f050c010c050d0b03030a0804080310180c0201060e090304030605040c0e1014010503130807 79
    0x40d030401c0d2450f000c3e114112044405003c0d00c05014202d540d0241003041c01c60035680da84841030a0903103aa030180c1c861032141c0c0003044400b0851031a014804001c40d0005e001807070040001e820039241c07400c05003110010052181c81505240b40c003508000c00c0e241c506400503406940b401c481070f0708105a5003c040c040d07100700441d600000c04c5a480401007084606051040d01c0c4c49184803180c024907100021851500491040c01241c0c00a45c2d4522100c21803c03450401d01003050100c5400c0310140a20700c0012501d42c2846c04481800d23400000401400081000a02080c035031841810307941e1042c041000e00040d02c0c0c400060114000c1c0000e503401282000e80607041980e52500601c05600c5914072800940d6102c440300039142c0c0902c2200000d09103104036074510310300803111540b28007a030310002c0c01039070319100094104059024464041c1c00c11000a00540c201400e484402c00c01c1409001c0c59001d5440d0103200703560103030742a03d01c01c4005410701c5101e4007007940c0d8000190004a03049511 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 688995170 1250 688993920 688993931
    0x6140f03101703030a180c09050405010b0616020114030702061f0b0d06050429010e1201060803130f241704080c01061d06040518060901060320030d08060103 69
    0xc01ca82040a0300c94251844021134503803c241c09207804461110101044a02e00b109403c070001340010303928012103046090029031503640341484da0152440c9180c032680300c200010007500d030140001c83c0320f80c102e000303a0352000411170080c02103159110980d4400d000d64800d4000030340c1c103000c284100210000d140c006070700c4140d0392082c03041c640c0c0240619564690301d4a03018042401c051146c07101e291000c9202d103d400160440495032081c10003480c0c0d040100400020b040d0b916035600c2d00c2d9203410703190000c0109594440c2aa512030f00b112540d030f1917000101d0070004002031010400c10a840358165500810442c1d0200c1c0300c413144441442c481400815044050036500c401d0001384100e0003609016030b1040e1078a283c07401c6a03682d4011070141028030303404103040d40e0348a03402c96100106403000030301622003a02c684101880c0304444c3d00c8600c228800c20000386419080b040460340320b84900f01c141444a41405d0301400300c90440e5030182c2c001840c01112502c04d03840300b034004c201030500180b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 688996420 1250 688995170 688995179
    0xa150b120d02030301090b0402070c0e13170d1d07060e150a080429010504020c0106050604060309050c0d0b0a05150301151d060105070f0501140406090b0106140f0310 73
    0x140740d40c152601c400b42e0004801000421304600030300c840e40c101218211301e085066134038000d603900c040c000d54260203110000100c10043c03811018007110341011051411513200700068000d1307842046550710180c01c03c001526142e4000b9030f004100140c09001c0d00d5841d04124044a070b029402c0f001a0740b18054a5440c0c0c12010440f00404505100399220112403403d800e1012004c403c20010000503000d64207117601c1040e0307220303442e0306498040302c0140c0d460710981c6080d4003400b0283c00460f48510001800589207406511041c0305512400542d0a51951701007041100d20300c0403030103080d418403a000a000c0c000140e0159611800c520003204050000b200030a00b1144030150003207100500780420b0005145140202d2140c2d030031508207035120300e03107100024594003608400a02c88050103950904022003900148400ea200d031f0002c04036803800d414014050031001d0000d5440c04050307000841e4491090041c0003070b00c80e0b041c098074540a00d10092903426400281128201400c2040c0481c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688997670 1250 688996420 688996423
    0x7030803091c021c021f05100f1d0603121210090c090602011b0504030f1e0f060b0901050102060601050d09120503010e0a0515060703020a0f1b05030a150b12 69
    0x8182050f42c010700242c01c030f0029a06201150349100c01c00d540c00302d079102c00c04100494070258165407035030f404681610303a09220b044070b0f055900300360081c2068000101306145080d0400c03a5080b040d200d0141c2c44c0d1103c5040c541c482d00303803010170361010004100c00159042d9591109421810514100d6100b655a01091089642010f42074002a504a000f0010f0540c240160111800c5000030510b16502100340079181d441544402451840083c440b81c050101c80c9038800880c0315a142e55640c2e561061904218620750170100b01c030254607094505040e401e00d0b081540c1aa0010380081100e501d0707840040d68550015488048100e4581d148680001d400c040030038264489900d901d500c80d414900615410100240030450051629040003429841088405c0342c140d0107580c116078a5185040490030100d209902030610401009044200f140000000250340030351001101515250400c05895402d10003000d00101c00d144140d105010b290751110290f058028035041c3c48242d0301e805079 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 688998920 1250 688997670 688997713
    0x80a0e1c050c031014130206190c020406081f0e01090c120b06030d121d06270109020906041a09070504090b0901080a2d0b0402030d08090703080309 65
    0x1200d00d07820860486002d03040030450003c00c5000400107100c06900302e0031452a260000b40041c2042802c0b602c4002952641e0040303411501c0000d908102ca02c40821000d03000c0000c0100803401030380341100c00201040e01089040000040321415051085141c4244010744400041940c0656a8041010000d5080d5210000500e40c0e043d19150804d118100504c407800001e02d0039010760400d50030010300d2a441000728900381c1c2003681c0018825070900141c500340030154419140c40c81140180302500311401629a0b01c0b2002d04060070551414001007400d81e503003150000d40182d54440071400a28054000c101d00c80f01c05078040800d0405540003980c1c03000700340c2e131150220b540050103000012a5020b2004100d10a40b07541b000395242c6056150b5980340902c0180040015414968520307182103070603101c2165001881d06c5540c5542080303039080310141c808034031078841c8010074000ca038003d00034940300e112540040d110171451501c0340c0e07030140c0c0000c00750403080c0200b10300c007542034018440c3c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 689000170 1250 688998920 688998923
    0x41104120b0108030406140a1205010314060a020a0c14010b1809190213200c010204080609011817070602040f080c1f1d03060406020310060507080a0e1c 67
    0x240c0d08030400d641050699501c040c0c0140c0c449030401c220a02035903810010f0551088034150035107944454400c07049032440340e01c0138054505810f00c40008240131400c0c0d16121407018081c140c40075510303626070403400c901c036401c280d1011030000442c013404142407600c850281042d1390008500895008005500345403007000c600c001c46040f40030300c80180401c01450444031116402e9a00358035954000030912500c00d007403c500b140c0c4907490034010f0600070050159000c4a00351607520360b02e00440c00782c043c0d0000c0c000c0285620803080001e040e25014000c1e850450300004c4007030413040d0340341c84180040300d8013608980c07004410040310700001c00710701c001c0000f40710910f400c4103824280f114071410003090b034844620071096000c0b481049801013000c04800001810a90b0458a450031158a40c08005440641c54021141080140301440c1c004600c1100c0055001c12402e0f240c04090350f00f8041c0c0d100141c8899000e20201c0a460301505003003800c040d002f8180c5980d4103410045d18080c1008100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 689001420 1250 689000170 689000189
    0x705010c0c05100504020603010b0304080714010c022103010b0c15190c181401030e0124050114071506170f0106050a0e04060c0c1506051c03080a0902041104 69
    0x711041800028400514007646a1805004504264001942c2400103010340c07240c0000000c0414100203000003241c20302640b010b60300d0f0390139000c0c44041b0b00074085100c1e518007600524020312003001401114840844115408604603403c203030501004d80c0060300c02c0d640900c642e50b251845103102d404000d10500700100c58911401e020701c40e80064805071052101440098164440d0071009203180400b560440812100c0042614004801810348010084102e51030f200f40c900741010510619000b00f1040c100c8031800a949800440b403400f080500110180b4051110100042492680704684000e078000851542c1d11650040750003d0400e4109015500440d03034844004000e024542c0140412900c90188a2400c03c0111800c18001d00040c4040d944400040744580900d004442240d00824009203a0b58407480c1500101014001c0f0362045000304850180000c442d44046806035142d90f452103107403103084081024200c100c400b20b9000d500c8180701c2e985242a403003d00001e004024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 689002670 1250 689001420 689001437
    0x62a1403180f07150e030a02010c031224080c0310020a0c02060309060a0b0604081f02041a0a02010b030a0f0209060a1802090f0d08030c070305070506070503090606030a02031b060705010c 82
    0x252519241305880c516401c1c003441d0307400300d50280e03804940300086540a090070551205140f9040316009040d1314803903d00c078a8001044c0c60000c1a1400c1c00e0740d100c129805d07e03295510384146542da0707440d10121640c16880355018203c51107498000d451a5089804c020502c1a01903001401c82d8004a903000180d50200d410410b1042d140c1c01a02c1c1000001e1b580380b45408d080201003a00c038590780408212220201800e03403030182da5036040394018008202807050740e205200d84081580c2c007407010007005600b0424000340301c0c83c01144210005900881107081003416500303024140400030113099005400c81c0c4009012030340103641c40b2840900031801a80c0b0101c5904110841100302d401c58003a602004a040c0002c1c02c2e04200c0e900003201c68031054803090140f030b00300c60b24480c1c04c2d4014054050801440300c2603810001650007000c4200c00c2e280b0a6032880305059591200e520040e5256000c01c0083c102c003040b0400c1e09068480140a080c5401000e480f403030f00390b84140600e54002800360 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 689003920 1250 689002670 689002679
    0xb070f0b040b192c0f07030302010c0f021504020f0d060c02010209180103050d05130902181c120503070323070f02072d0e04062a1403180f07 62
    0x212802e01c01c00d140300c034041160b2480e03c07a070031303040584003070340c22a0064451003100382c00c1c101000215110088030048401c4c10340c40e4500203018212203005000828a5100403d02c00d50011803040480e01643d201107225079956020801d445103810030a5400155002041d40411803a01480f0141c9040e074002582d128410810700c80ea080124001450340b40d80c120051001a10200b07403a02c4c070380b42c189480d07525401062442c100300b220076882032131040d2001030050700300005c040c3c1d80c80014004645880c5064035010703802d080011004da00624040b1000c0650721010f005201464000b840f5240004d0b904980340c00e8052010601c00900e9800f0b004001040304040d803020240305450040d202130a00245030290a00925100052a0182e064901d81c80080204c2d0780d040d140084c003400d054003600d4207190428038018211018947c020b032190f1410000c01b0540440717034040701040e668400c129444070315040036064101a090340a0b10540940429980b502040700c804c40802c0740010b48142484c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 689005170 1250 689003920 689003941
    0x170702030d08040c0f121203060e0a0608010c0302193f0b0111030304060e03070b150102060a11090603060402090607150c031a0f010915050d0e0c0a0b070f0b040b 71
    0x10b41c4840058154080240315210032143e040080d5903000c0251080d0014447c030641c0600001d030000188232422000304901005c154216104807111a0000c00c10460400021401e84c85281029030031000e86003619000301d0b100300001040c98881d2000704d030803500d040d001409019910040c84d0b0029a00e450405080800340c403400030031080909081c106882500718003034036800b0041028014540d43d00c0c03008070142c020f104507485039500207081000c40c580301c0f56030000121600c12080c01442a24002002c40c08a40302d01000350780102c840b117043c0106c8100300000713507000801981d0003540031b000c040d801d0340b9a075025002451043c480c8c0c0800001ca0807244d011650b401c282401090b007440502c6c0000302d1114185a20302f42c0a45c0d414040b4a5206d00507150307240d41e88c0c000400e90341104400140980c2c41806040c242c20b010b08244481280008001d503a03000341060aa40034000300c0040007110440c1c0d001303150907841008002d81114841d114115080070403141940c2038a02c1c02c04000c4034001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 689006420 1250 689005170 689005193
    0x80a0e100207060b0406030b160903020303210f0f0c0a030b0a06030903080f1b2a070609060305011d1003050106060c0b01240809151501080f0f04170702030d0804 71
    0x2065508201b46851900d90b030005800242000c21080a0b000c00107540740d01c24140c08002d560090100e9030fa88803000303010b8a80506603072010585000c14008074100311803d045036405010783d0034030400c40c1c1c1c441048981c0b641e03111440850a0568440d80e801d1140c4039900c403480149182d4400180302e0405003800340011764002e01031a05501e40008101080c0c643d10b0500609035042d0180d207481d0003641c3d4400c0d03009410f410008581c008403510901c06280009940026100e00d5692461299070b0b0b08001d034207841d028016003102d81840340003039480051210541c2d600103180c200074007800b83c0c2c0e6100d05003121019001600000c6410004c0c105210800301200e005212288003444440c4007403003119400b06032070280b0010043c030040441d1010400304505070b03030228490103a022508015940d00c108511144070302d07004c5034002000035514991503980c944600c03803480561150b40d84550300c41c140081900780304d00c11a0002d0042e00050f85040054a1604119441e00c503c00e040c50304200e40200d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 689007670 1250 689006420 689006441
    0xe0c04030b0121030c08090402030f0103020102100c1d1c05060601030c0504030b2e090b04050a02160f15020c0c0a090c0c0620030c0a08060d12080a0e10020706 70
    0x5011112a02c0f1000222000200311074151401002c500703268509000103100b00d00e28190300c00e0010050102c800c0c014036000341200e00c00d8003120101d0000c004e00c40b0030340e004e01801001041c24001c0480f00c00c2d5040040f241300100c000c128103000482c2c244266001c40c21018203031195480305080120650b01340c850300240d06614203180d418145140d55000c0844401040418001d40609010304440c03160b02411046101d42e20003a10300a4a40c24001c0045c100f624180d0b214500b008003041c400c06062003200c856002c0c4600341e40359060181c440704850001d5103421909180c0600c0c03060720b03000c0d5503c080c08854484002414007008ad400801c01e58083c66080540c99a00c0c0c40304080c0c0c416004241101a0b41d0320803408139000d28907081c800100021401941400d500000800200065000040010341400e4031002190f446840501c880450013200080240c100000030322403070b034000d0a4140d4400010300f0046042100014039500700300d48507990351744441d0082206030800049002d81510907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 689008920 1250 689007670 689007689
    0x70b1806131130010b13020705060c03060a1703070b041211070f05040e011b09061205070c0b04050f15091e0d050f190518030a02031e070e0c04030b01 66
    0x1480304103110003081510000010b0f15007150360219516100a41000740340300b02c0241071121b441680d80c003407000380d40711200840b000e00030840010030180e03400d401d8074054000581902e034070608005040c801d50304070780407803000380c80188103400c0024000360304103210368400c692041c03900003245c0000d0848100d01c3e07580111600003000c10b1109842d40d21a4908a170303012600803c400c401000a076004220451400b0078084c694105500c0c4150402900c0040f01e001c0d40d54002801101e008807821200300707a500c41c000500c41c144400100e8001807085802c203004109aa01040030504500d01d03200c4e0070078111107003500000421880100510005031321010f030940280b1440300c1405d165888410b203610200a003c40800c9600c00d0010440540b0601d45000340c009480900c04140600306420407580e0718000d1041c02500c41d42c6007000318080c602c05a01800a140b14105100c41c0240411001240318580c86180000100c2e400c00d081c103103000b0507800301996540d60960601c1034040c2016001a5040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 689010170 1250 689008920 689008939
    0x31704020306164506051804140a24210c0819060b0406080a02090619030b0412030b0a060305070215010602030a090501090605070b18061311 62
    0x258901203500c682c05490403012020398a020001924030b0030412005881c45003401181200c11039001039141c04855045225440c03c3d60b04c464480a881d4903801000d0000742c09214007403190040801c21a1b0b0240d0007000811425410176404150100440703900561075211400b07100c0107000080752500e0034181c1e140031a0364605108140a45211403c07003450600021004101880014546600902180026108007130030b20300c035001100f6a0a00305513950361905007588918900381c860b00040b00c0400c805000c0000d056001c2062103e0024015a0804078254001e81d1501d01e50003ca40518498500308205040904280030311114030040e801c249440c105c070740d0500c2da07035820410007210114034004c61581da0720030080381445480c0080e00c400051500004c1040394020028000e01000c0782d4401030042d684800454688000d4800d000c0403c0d010865440800d00d0130b030351998030565404119040800d056000d89c50010202d40d4a021310302c07120f000c0d10400146080d001074246040721108038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 689011420 1250 689010170 689010173
    0x912170f0622020d180c0b12060f030a0203010e010c0e0901030305070b07051e0301060f080c041a0c07030804081605061206030114010e0a0e0703080714160f03031704 73
    0x140701100211a6410390301250341402c8140480e01100c43d08100d1138024403400300310b0181c2c0c074401c0c92105000c54040300703401c4000c1440055541600c003e44401d042c030500b1a11980300303001407864043c1c10380b509401030040d050b0242c0c03024020002200c00d010700008001d051001300401c8450281e4040d441146d00800410102c0e500100340e4808039048034001d010794a0f08003003030381c042c811a0455040c0f10300d44844560303840301c054091412154917403070b0198007140a12040350480780c215040d1010070400d00c001e1041d40340300c0c47c0c03007140506404025071900d0041c54401b031804040e503000f201d800200003004c0c002044103000c040b072030813030601c0a050000c0c00d10000458034041e091441480c421f4140014115035002d4001c42c8003c13200d84180c1c5110f503142c45260a030b442003181c2044c0060b0405948a03c55500000c8120440f41c04c100c60606040e4181e848550001040e02e8004403071062507810504600b0041c4014010021041a01162491458050031104442d00840700c02c401b600b04200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 689012670 1250 689011420 689011429
    0x906061103030610120e0606041407020604140102070c08030307020123070e04020d05070e04200f0a18080a110603220201110a0303050604110702180a0912170f06 71
    0xa40200f4125a028580c46456900f02c4501441d0100c5280b00c034105042c90782c0c000c0300426400c2c06240144c1e0b0902010801d5449000051000d0303c48000590000c00014003150003414400280181580058500141a140c01c3c0010b50725401140e03854000009000400303030240b20300b085040c2003440307980c55030209162101c083d14000740503009000d044d1905410f56551503044800162164000304801d0802c03100040180c0d18140850f8099880c281219150040d244030741c0c2866140c4040c0240b419841c130320307000302581003403003088140845041140f01c102003007051180641010402402c000d50303207050404040c142500d00c039006400c1002800305403407010300d94500301c03100204280c50010103440120741104101110710818040d01614508055240d004a401020704907010f02c1008a10010703400a4422090000d5100100401c0e2542440d050303c11183c0c040603618002914841a0311400000c0d80c81d0b040e00b5000480b11180c0c90302010034045203907005945001b040009140200219 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 689013920 1250 689012670 689012677
    0x1e271c030215091f09020a080105130f0f350301180e0c062d0307020c100e060706020703020d02060103030e0607020a0b0403050102130b3a14010906061103 68
    0x1400d90b003184000601c203201e0800503c2400c4260310042440a00c80800b500000d1404400c00c900c105c4800c600041c0300c84d81405807038080c4d00c1098042e12081500d90742d100c1c2110384804121294410041c0040205e440070a8103004080c8041c00e13140d1000501068116a904007503c14181003424001880140b8040c0d40041a194111800081c4410031036265450459940e030b540344c0c44507000888441c40d043d01c2c0c2e0009802c0c0c00400413500030240d1070360101001d0100700c41e1840140e000400d0100d0300d280c5060040703003008a50400d2511030783d9400203c0c41652011030152000e135000500c020405604200450380250b07a44050300303030b40d4110f41d0300170100401c0c01c40541c402c0704045419003d40d079030100143d0040c011100000c1e0748654900e00a8040d40001001c240d910070500342c00603030721907040100c070706d1749115602000740181c03a100c0c201603071040f5145400c215218200704103c582200e1050200064940c60807008946c50300201500b42e80440d04894100072028002140c81d42001054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 689015170 1250 689013920 689013943
    0xc08070305061623030a021920120901030203042303030609061903080d15080d02060603070e010e0c07080c06040b0c070b180c030d120f0207081e271c0302 68
    0x403585d81e480302c05408000c1c5c041e003141d40001c0e06c001e8000b04002600b002d03955113120484405203141e403000600081e00c40100d49101141e031401003107801120740c800c0d8019640710b0702c2210525908160b010a224251040004807040342d800002031010501d41841d441d54084000ca03100c00c00c407030400b09000c80444051100400883e000b1401207950081c0b80c00a1f980042c803400041162039075820551ba65500346c040200260103100c3c08103c00d1305001c0345420556a800040030516440c000079100d1402005041c004c0009041c0920000039021100412508106100401990070300e800d00a07028480a4440c100d881000c003c0d1800181181540a43c07107000d008280707240c40403441d8030a0400045c000c00d140e0600980600300c0d603040d00004442003a07049500208001300302d04040004900c100540540708244c10320007641110000b0311500c1441807107109903403c200001d1000041900c40c0c8071034004801002d100320115007021101000d142e848281013102d0040581c401a40b1450140c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 689016420 1250 689015170 689015237
    0x271b0903210412110a0b0c0a03050f0405060301030812070302030603100b0d1b0305010e030a1d0a05090a06050f0415050d1109010b0426190c080703050616 68
    0x102206909048402e4030000c020703500d42845404400e00d0a003402440d4024028854400c250010450110171001d4034030790907004006040b5288540c0342a24660404500c404521604000101d00c03511042c001e540210311961400d601c403a01c010461903510701c000c00690800d4814000c1046c0c42d940042e01d0800c03c050100d000031441c503900302051180c0c0c265100644043c000b8111403442209882e02141183d000d00b00070008072060f60303200d41e182e100d2003002c0c000040341008501d0452440140c1ca00b651480200000090b903614804130741d442d64200e8805041e540e88030307000c01040c00c152001880150048400b0001e100356450b40c1580884280101070013080000c44140400111060070100000d0041c141040d6680d038885003001d0b580240101c0d1036001c1c04102c82d940c0304800c0c003010246040703030718040c0c841520316240c00004a9102c00e0141c0f081002a14002034a1009100c4030300618026005801cbc00d2505010041160b4a8000c0810070041c0c03400b104181e400c9542c0307040104d0400b001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 689017670 1250 689016420 689016463
    0x909060112060908030f0f0114030706080702100905010b121207121403040510180201081b0d0e030d0606140313110303180114040305071202271b0903 66
    0x62481c010880f003100240a240c0010501c0707900c400b0101c0a5100391412807020700280c3c0c031041c0e0301d007100c04182c50090700343c2e102400c24040c540c0070346420303a030050641c411121a40982c0100c001501c00a2074181e4459558240505150030a059603a90003072000000340146050002075881c1031140d080054014592202e000d44521f10640b00890b40039400f04405881e0700705420301e5a00c03085200e8880d00c01c2494a100041520407076907168480c15016102c1c2d8415995000b5100144010707000f0004640004002c401605d01c43e81c403558a5808500c4025034455009401000071102ea940221043c4112040550000f021050841e940002241090380c0031101300e251807d01c080240c00c0307a6a00d8000840c5000b818114002060f80c0c2c544242e0340c4900074002d04050f001940f056010140168001039804d00001031014501c1c50100d20281c014401420b91481c54002c40000b408403101d1b881308141441048561882d4603c0c191140100c204d1502035217a0000790b4806c040d5404021b40d07416007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 689018920 1250 689017670 689017673
    0x90603060b1803070807030c150804122316050c040e07091a1c060506060a02070317070b0903040f0807120b040213061205062d1f17010b0909060112 65
    0x2446002c00070300d80b020486d0340080e02da14010231800c403240220b40560307942c080c40003406481035070300d1070045810130218241c5141b200300449a59030001507108092460030044628092175100512000d00c03070704000f84e4046082e1401c0e504101c1b40104041c4110b052180c080c182000100d448800c0399a00d00c00011070703a002d548441003407810303088206e6014800c580c0e0549081d01c40700c0c80095280c0718110400c07843d030310725080041c9405414807500040e4001d0310240f00054108907030300070403100f4040d683c0c00d007402d83d9100458513000310340c00a070641010404200b0010889081030151550002030080e1a052690076002c2c804421006020142d00d03002140a6480c1d0091a403920803c0040c1800140d0311081c03643c81c05c0c3d4445c10f00321001e10440002821800b1540f5640700000c0d008105424516090000c617100d001014119107203212281000030903a070620303500c0e1030041034100b1060403c02c0070401e950703085800d9042d00034025045d00381000040000030501e14103603a8064000174803c0241e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 689020170 1250 689018920 689018923
    0x70501020c130b040c09080c0907080a091403030c040501080114030d210f0203220209060d1a0f0709080109050d031104170106031e0c090209060904090f0201090603060b1803 76
    0x10b03c01c01903001883c102e1110303110b90740b0601200c1590643c404483d031000b04882801070000085a54000044141c40400c24234030480d0402080503012700d4584031114902e6103458215401038416032403130f51001900b0003607940c100340450300524030100c1541a00441034082a02d030080700d002d5800308100f000364210f60402c200b10516924512110802c9403d0008244034000d6100703070748488074040c0c0d02e40c0003400d40800240a040d10b9a0241024001e03448860030b02c60100d207540001c072481340032000123444240b01644514403c0408440d4115107051580e0060988240390f003104105034106040c1e200440d82c0020101515681c5241c00901090040406075480c091600b020f02128003003a8a40f10a660540005058a02800359003503644c80018a0031002c2c45c6441d0000c4c078010640c5020070400c0c032554041c0c4900e0348090069840c1c0980080010b04803000d240080768481d0a5040785819540c1c0084900c01600407414100031560400c000c104050027440c0c1c4440700c40b0103949038260f85840 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 689021420 1250 689020170 689020181
    0x30305070809010c0b04230a03050d05040206040b03130b011703090f01051c022a100209011b0501051f061407020a0801020a081e0103020a0b031003051f0b03070501020c13 75
    0x8120100f40d42c1030070249002c0950040c1003a0302c447c00d5807452034006110304046604256940d02d6100e042c80c040e00e903140728000e44001082a640f2050510000416041c1e820041d4403402141c07c1060551026180118540d00c040e0001003006100f69044004224000708490407c4801c50380600113200c4000120388910072202c0c4041c90280905100e054440030f07402516071014040103d0110000c5201380d484060107844402629510501541009040ea07500030005117606141040c072170038004014003000251302034100e44a80d5160704000c081030784031503801c0d14131100f0100001d260b49080002405044c10030341d2080203030741c00100d1104550301c84900c68002d01c1c0d404001c0d901c0380452000a040d4520450702c1003040385501c0e005090308142c108403039040e01c0e40140000b002500703084180a884d0001082e042400c94a2403003c00861000c1121000c110141c0500c1c0c02803c9048a0039010390342514a41802076000c0c540601c1541e8001c2045014401c00741c81e0851540c0e54120b0460241c0f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 689022670 1250 689021420 689021423
    0x50109080c0c010206010b090109062a0f061a0a0501050c1903030905371a15010e090603060c07020118030b070314151c020312040305010605010801030305070809010c 73
    0xc800601200c400e00082a14180c40409030240c0d0380d07680c2e0320300182445100d03d15103540018180710f01800001c0c0105950f0000410888c56440199550000702d20040c1803003070113440190b4880c401d5000c120050090030586020000341c50908100000070442507070250280ca4148440881c81c2c08408100300200340c3c100c04c031203d141c56440058140a0010400c4402c1a03a4a0213180c03004003403d4844c40c0c1d60050341c02c2d0740301c001121905010035000d07183d495880c11220341d00918188001d064101d88641e0269400c41080e00505034003038005050425691282c1d40140032001c00c11074140e501003603c6622600c2800680e40d03800d9107100403140180201c40345440d00991260210602190506091040c540c0752000c1001e501c1e05d404041d11200102c0c0c4240c40386050840907540c608003004142542c0540b034000e0b0f00400b0140d400039041080a50000d5045c40000c02c0030400e100090051200825080c02c02c50025411901d008003903110f80e55001d00844030004407417020b40d10030160300300d965 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 689023920 1250 689022670 689022683
    0x5191e0807121e050c07030801031709030d0f0318240209090c091c110d02031e060a060506040f060528110c0a0b1e0c0d02030c0d0201060e01030807050109 68
    0xe03000c020002070340c1c244160f60246519040008001e100328004542d0070580607140d0f41156840d5a50b03807000e414450068104040062041c0c066545080040310320b030b0020307611410090070061100404552080000005107100c0181000110710151120300070700000c4003002103003040c06100040079200e102e546a4110050b81c0c03c1109007100300002d004000c0d4100c80311080742c2000311426a0000030880c02804804d90001110418605881ca0755a07480c800b6003512450150041c00c1c040c018800c0156420382d0b00102c1c200640d0810328030a1401a0a00f201c1c66410035040c5403003003442c82c1690046c641482000102c01214692600b040008200940b040701d50740c0210110042c9940e42650a0014500c1041032275001850001c030f01d20150380c0002c11840c240a108014061085844007618000990402c1500c850407418407101e007003040c9a40003155104101e510191901d08038481d51400c59140070000d05c400e514903260241180c0d00701105a444200505280c0e00406001a008000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 689025170 1250 689023920 689023931
    0x311010b030d09030b1f0e07110105131103031305010c1e15051e0a0b0a080601060203040f060801060507080a0e041d0c0f0310180c0605191e080712 65
    0x1050f92100c1484150383c46410640000d403110305a0154100242d0003943c510024410103024503010003407480e42c07100e03091901c04a00c01180410304d0850b40c00b034034148146800075548000b480170b402d6103003003042c0040c1c00440c9045a4801e00040c544510b010710b40c10002e22100b0001030201804080314104651074240920b14214a81001682aa5031101c01c2d000e0410f00028a1f50704010041d800844080e0003114003940c40f0018a4002d00c100c015007540540450746c046804241040518080d0003917030011942c9504000c0c17010781805840d80488200300001b00103006040d40282982c01d541da200d010b01d620349000b244295844501d40b20b003030750401e00d06006060760302107c1150451141600c003d89403007001910601c01900c10588805415901142c8940c49070842031784400e02111b042c041850b00750507144e40c2c00d0150325440d4045070005e140400c0992540c040c1e469110003442d00790800141c0d8142c440a4500d40c030445035040d4062228803000501118003a03078207416a80c540706010070a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 689026420 1250 689025170 689025193
    0x3080606120c0a0908190204150b03040807020f0307080d12110a02011b0219140a02060d091a0403170c1e04031a01060909020d1404050d031103010b070311010b03 71
    0x190b40c2001d0030f00030000d600364500190075100071600d0404890315529812002d00326809100103040031141c0300200c1d6145400000704401d031540a0350003680b0036072941da6211044e00400c0400c0c61072165280c0300e81c1121100304140c641c00a051a41e015182c1094100840d504181e0740043c01c041140d90036907000040e40340b19007035041d440840c0541110100c40303032001c00c1d140d00b282e43d140301121660744010b00d000300c40c3c045007007405c4ca600010210011200304001c1c80c0e01084554004041b48610706448600c0c0800f04002c0340b02080881c041000810528681620000c0c442d031104070040601d209880d0115050382d100404842c81c16064415241d6100e08060035a40c0952091000755081d4040d01d2201d0300c040c130140310681c100c580c170b40e60f052001c2d03040c0340d01c10009601440140014540d149500d255200c10340455501c100c0c022400b81c594502c81c102d02601740d5a44062042d11528200018804e60300d031082a50011600740c90051309060001e00c007140103105d004103449d8103102d111890b04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 689027670 1250 689026420 689026441
    0x204090b090f09190212030f0a030f09030503010b07020d02030105010b0a02070815010510020c04060311040c020105040b0a150f0b03070f050403020d170d1e23040308060612 76
    0x54a010654104105039100b25841450031030503a220030301600030044d003031440f10100c229244e00500080c400c5104007070041d1035900d1940400711541d508034000ca040131050f070709442001c0418040c03490070b0003150307031075035000700300d44070500414603030510200e080810b640b1000c4808544580c0900200a103503114001c121054000140e45030041c400e000c404907060038085106510943c00103601102c50b42003104010b090b89400c51544114460514603101d01d9a85000307a000450240000d0072040d24250180801e845510201c0800d42e13060200f84000a030714103a406034031083d56400047e200030080540c80786100580d104003030481d00320101061804000c0c0041d4040c8030f1035100c81108640d96941910540658440a98400b442d0701c65400400d5150816030400208200c0c0c061810700c07100f42300400c03980da443c1d240b03840150662240026802d24459004211480b28203e803240540300c03030400b0040b00c02003005040080d410081282c0e0b84814081c7c4181e148540c00c1045549030101405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 689028776 1106 689027670 689027681
    0x10f0c062904020c060402061614151008030909220317150d0219081e070e0108030a0809070503010c020f01050604111615020409 57
    0x24000884510070340001c884411559091075800c2619400880c51040400b800355204102c0b48019100c0010540c0e07105034119141903540d140300070146070690f01160000c0c8058507092035540d001c0408225144000f020b4006401c503070f5208554405003244620a4030b403590400c011414180c240340c0e00041e8000e002c284e40c2801c4aa00301c0d4803144144403103106800281300894490040151070050f0f54100c3c0460b1080002c000080c0c000410660120714000e20421681000107211403030420024010103510040e101c4a00030b54a41000d2507844e40455506c9001d090383c042500214904090f048c0c0d41c03031400a505002c0ea0f440e0646010700f0141c40400f0b07503c2400380003c1c45603402d014022043c09140d016005110003c0d00c041d0945001030308440c4505d080403580655481d42e40d00740c070200c0c0c042c0d020507002c10550f81400b11451064009901c20107000042c0030800d1502c07908103 = true := by decide +kernel

theorem cover : BRFrame.Cov 688848920 689028776 := by
  have h0 := BRFrame.cov_init 688848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 688848920 ≤ n) (h2 : n < 689028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
