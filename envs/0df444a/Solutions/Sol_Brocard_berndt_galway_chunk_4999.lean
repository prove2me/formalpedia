-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4999
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:25:09.1698+00:00
-- url     : https://prove2.me/submissions/e91b2763-d0d3-4f5b-9358-8d27301f47c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 898920863 ≤ n < 899100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 898922113 1250 898920863 898920871
    0x503091c0909050a200a020604110607120810080708070b07170406020c090c0315041a04021204061a01020703060218060d1509060803120606191709150708 68
    0xc411840049100e005502c42d43e4042c1203185000281a91200c0c40306400c10301511004088040074040d81c50019008503100368816409804100114060341c001071880c02100806804d0a4080010a443c0c541010000340580d08221a4011640c0d03590101c035520240c03030088281c10b4001420400054001902500c1250300c0380d62200019100b0244884054002e40d021400581c440c008105003030401c00b2402c0d0300310550768001803071071400d80d420703034030342041540d406008036034894000c42d010048110407050700c0001032041d0b641e10f000341041d40d8008070544050361158684a40d0400105401035890080101030f0007404001e840d60311442c0007500041c007000904540013190b050300e540c030100103060f0203044030700010703043e11100e04924240540d070300061000351810900340f140072000400e07a21203a100390741810702c2c4d55907a008076469010302900105860580c0e11450314298210248800640310103d05941d50745e07a00d5080350741d412100c8130b0001c811000001146516105e903d05d180c1c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 898923363 1250 898922113 898922117
    0x70c0b100510020a060c050a080402060721050d0506180f10030b0c0a02010b010905150901020a060e010228050901030903020f12130f1805180703060605040c0503091c 73
    0x1100d40c1d2100407030340c0985140400001a04424080c4003000503e1240e4840c0d07010614215041803000307034010304030030000f8202a200d040301144000800103101131440300e00403030310494081402c41030030142c01c1c1d81090258620440c1400b001130641d040c94032031440149000c6500231581d8a41d03120000c010741000e0680c2c6004a0940000300204042c1e40c0558000d0039480d480d15900c0029075002421221002000d5040001c241c1040180c0c0d82d1f160400b59006400c8602c182c2d4440030500180c0c6410100e1000610b02c60410541e04054141035000e010072002e40004000014040c3c4807084142c10061824808103034240311202c90b0303501c0b961088048034884d0045520080000c0101454091404803083c040b9600088100743c003010a81450001c0c5030b070204682105d42000702d5401c801b481c01d040c2d6451150b550002803500c65141c0110552005050284c404c6c943e2682045005410a4000d490165003068a0f0f205000d200e14202d034070801d03105010300984407080e030480850348680030310241 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 898924613 1250 898923363 898923391
    0x13050c04080102160309050117040212010b03160609050a06140f2106010e06091e010e1c050705010c050d0c03050d060806040b090303100b0f071e0204060e070c0b 71
    0x7501000034802425580340d010103407060141c543c03800601e9074000e0b030400c03410410314158400380004803105203038001d5812141c00d505211007036800303401080500742c015414803981d030090000300c03041c0070701c4820707074805035140484a5102c070188981452140304401c00145600d200c01411101c1c0000b40c603400201405880c80e203121240d1901c0c80058103c419440b58a1201c18060030750780282c507101d5000307026034105080142e000c0000f9600d91042038810460f18000c801e007103c40c0c2c458092079011840081126100054090240311200003140b01215503105401c0701050541c000c1c4014810164000001d000c85144603004682041c0e0141c01202405010700000941802c1e901888010b0030f8940000c281c5031400341041c6d50033004c003400790a0190403c00a01c100341c1c01500c9001d06641810380a0345c1d48414016a00031144240308003e08003034541d0074281c043c00d074150031010409008075424400e607503c40405a10200003079502201203409031120310006078001021076401f104454801c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 898925863 1250 898924613 898924619
    0x270a0c06030b1809030a260c030a0608061003120c14031e0f120405030f07140105090f0d0315082b05090109170f0f0601061106040213050c04 62
    0x204182415080040801d40352a507206081c20300141214111462542c0d940d92410302290940d128881e441c402c0c010004000b000c101a61441041c401c800780e40c41c2429140c51400b08005080c903001900c1009840c1c0c1014000034010500007022800b40e04004041c1110600c1c40e55a82d0810103412540e0b810303c01420316807404901e5114075040c409042d94003856440800240818100f038101406c1c600e454070a100b00e038440c98405042d202001c1c1000b0742c3e520191100c0c103016241d40100c12840b0480c41000034907004010b80310707138081d901c0102d0000a0111b610f8040d80707640c4581e80c10b06800261340c482c92a11103194171982101c0860004844c100c81c0344c41e140e220441c00c00460a40104900c25030b18a006072041403482c0c079060007200c6103461400c0c041d009000804103800c9100b001c01600d9491480b0811050074481d90b03068840c224112890301300650b1003a602c4071003d1252101080d81d488800d640f40c100455805d107c1c81d030040c1040042290348012400414020704400401d6000340004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 898927113 1250 898925863 898925873
    0x806060d031209030210110310090c05041809110315070503100314031905070c18180c030b060604030312180f08040f09180b04021c03080f01060305270a 67
    0x2103210f4600175405850f0380520415400e090369207001c503100ca458800c0042000c1180150303154800c2c0c4484000101d00301010b0f2008407074900450300044820307400f003000810092200c2c1d1112004c4e511407031040c0e030345903a0601015260002c00002e0019007001c0d4000543c128030a00c01542d0040d4104900c0042d60f03166116600b00130b0142e48c811b0b8403640005000c01003504a000c0e941c82c244d929203440c91034400d45a5420400d11a03901c00d140b5000c21420040c4121140c2d82c104082c410b00040c13a030407244031035080c03132190a07030541702c16901c108640d000b00f031560800c80100c90030f60b5015103c951440344109a60002408400041c0e00ea4800c0000d403400080c0c504407001c035001c0e004c2e08019803114101442254080764603440041c01518180076582c0c048040c0030704c4a0481c1d0010546c4255642e540040303214103091441800c42490041e10003401c0540110040e03002d40300310a0500300a83c1c0f0384006800312001501d4450140d044c48003d0500004c0504440484010f07a109842646000e0790711 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 898928363 1250 898927113 898927121
    0x5011206090516081605150712020a0b0a0c090618060e13060f060306090b010c030c1109091513030e0603073b010311090105090f0a03030804020102160806060d0312 72
    0x4da20355042202c00710760203041c80700a04041c0104540008070340200711a0002c1c18420114003d00e007007120003481c0700c801c0c000e210824200780c200d0ba9945840c41c1584081c401400c1d0110078030080307404200301050b03c42c401ca81d0540038101141d0340750801403d0607400da804c189105000c5900000b1540040b003511072070300498004118020080340b20504010018043e10003a811400c0300c2ca2504400c0c041581c0c1c00840040701940504040c03403082d8560425480340d050054000c0e8005012000b4030505940026101102c1309510300300c55442c0d07c0740860390701c00340189107002d400908501c0080000d072500200850700b1008a0620540e44e0301841d0910100ca04a02c2c1d900e00140c4080009c45d99400e00161a00e000300f5013440c040140740300705140301c600e5004640080e070400c100402c1c106110748801d001c0108400d8000c240c1c40960740d5a1a005040c0c01045404034014090301803100764810602200c482a200a44080c14269445009100c05d805c54004180d080003a200f0000100407081d01c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 898929613 1250 898928363 898928369
    0xf04090908031b07080703121d100c03060e010e19060806061c0c140a08071e0e04080909041109091e0f0303061203040305060a02090f0405011206090516 67
    0x94402d890f49000c0c4605110004100c0d6003003080c071010000400054000c2e012160101c5c0d02d400c0c400394100d100c0118030000c0100e4241c60380510450009841b645d9000542e204400700303040814400804000401c800fa074189100d0400f0320035040006120001460304a55404952030154040c0440c2001e4210305440c15035010009640029080c4406420052082540c0300d103003416044901c01c0e1b5a94402040310030b8403441825022500301906995501d0130304200801592017180c0d60a600c0d0000306246031551407000a00900c24140021107a452441aa1140e80c0119020f42002240c0090100120b4010700440c1c83c074240320002446035858454250140c13155900820b481c0031448100d5000c10030b01c04030890603900108082803803480c00000c07603a20400a50720420f45500340603407145540240d0b00010154000d02040094000841c1d0240200810845901030310307010380300a0000b180c0003030243c0c5000e41080032662000c83c2e00d40cbc000042040c80382c8101d50702400e2100c1c0300c41519403990 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 898930863 1250 898929613 898929623
    0x10509190501090b0c0a063c180f08090a0b0703050a020c0103051506160501060602030a02100615180504050109020904061410080709090603031713030806060f040909 73
    0x30905001650b480401403001d44029007205241c1a26400403c0c2d03280e045150040c90300392661207003404014403039586401e40604c01c60611009228405110031248080700700c0e0180b9140110300240404001d100035502ea4000480c941000029210b010880c1c0c07011054580200c00c54400040700407810f802001d8440c02075907144e491f041e020710001d0030f1025810030241050f017400d051040710b48420701c921000e41000ca99a95548820000d600003004070300308042c045501c1c00300c0c0040e040b500800117109041c2e140d400c0e55228240300348040304807a440c0c0116443c501c2c20890300c41005000c2c03461601084100709c488183c080c0da40000405986098003d07540003500441c09800a062a0060402400f41a400c101600c90800c0100b1110b0311002d2404040080a00c0842c90312409031100c07070060050a1802d01c0059240d040180142c0e0300b0765a00900640810005103a0145140c200307420780e68140d54442450311400200f0680fa00258030700c815103501000000307100c146070b1207110385a51182c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 898932113 1250 898930863 898930909
    0xf0e04030314010b0906090409150c080708010b0904050705070b040606090b120d05161209170606030d030b040e061008011b141b16090e0307020f040902010509 70
    0x989001416200304907030070300d01085000300500c16110362009803000c00c0b034140c4140d07482d00d111000040242c03c0c0701f1806440000d101c00c20041d1150540c2101c80d092011781c949214617222220103c5038000240b04155a00304103018204030303441c25420083c0c10129910340241007900c562104440c80100703880c02c90b0210759a61041010031013038020158610750450301e04161012070b102a686864021000300c082020000b0786030301501510703407074942036a0043c040d01c199003906280904081020b0090808000d10b055210382c62020008180788141c4015002c0c0020010ba00000c0d0082c081c00c0d0340c880d85c456201d568a94079003400f0400c0078483c3d260428100d03141803405404508480410034200c0142d008200c2d84130302c0075000410700111100040040382d440c100d1106015050000030706d030394010f0288a149505807a2a1044503003952141c800c20420102c016105a80e6842001002508913009440c03018042c68640c3c00054000c0c018102170b460030b40340030001500d020b43d082c108542e614503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 898933363 1250 898932113 898932121
    0x20031602071a07020609240c16050f0d050f0d03050a110310140f0d0b0403020d0e240904020301030510060f0501050d0e0a0605130311030702090c0a0203040f0e 70
    0x304200c114010b2030390901c00301d4030b44040c1c21031100303d01c50000064000c42c4001118035158848815081e001d10748410070880d440300005445c03281c2d5100750700e00d0b1014450340304250b80300400b80c80707800102c82c4000c110441005045040c0b0070742d44904502901d0300e01403003124080200e024030100c00e1204066400250901d0646012400c035544038140f540061014410010a802200c0c201400c1c2d404c0424074500049030180003a803850640070007160070044400e5248100a031500000740198440c2d02a00ea6041d01030500300cbc0c000c42241c004591002d01ca010390352061104040747c00d07031941607002031450300703508101080a90340f0a901c05c0312142d00001c0780390546049132044902401a0250700640e00c0d16202c0000c0c101d01440540b003a2103907a07060840400c1c402042641c2c88660f001d0307814012440d0000c0d84550101c0206800d0b03000c62041d940e16130140002000b101c1140d030b40142802c0a940f43c408001ca0a6000481703030301c00b54442080085621000c2d040050014440ca5074121041c2c54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 898934613 1250 898933363 898933367
    0xc0611130e01091112041403041202010305151507020d062f09152203060b041503321c030f020901140c03040909060204090b15030406200316 62
    0x2005074010910289030003844000c16003040110b40c60700008070f4050110b41c070346091400007c244584185038600c40003070005802c45003071414840b2a03000340ca041200e0fa45411511154030460000d042e4001e030300d0700000f01800d0703000028012542c0098a061030142c120307600d08088030728018044031140c5012445c2c240c0f800d0208904d40b80314280d100311509020352040801c25030800350720300c100c8600c000b00300716a240702c0c07071216006080300741c0010030070240e03590a101006201202c040da0149082101c0124044001d44410302280c0d800002080c5a40ca22800461b00ea41c43e6107504074000d42007407994207a400204996201024208040d09690500310800f40840b2250b9107004407080c0140548600e40c0e82000c120940b5460b405041661005030452030f900314402c54002c441a941751084d1981840400c0e40900281d52444508024503105081001f11170700c00c070020302440860800c00940010b650340c01540c038480c0104c2020710710760340300b0303504813070030340080351046c1c00310000c180030072110381e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 898935863 1250 898934613 898934639
    0x1b011d06120402030d0906080c030406091a1609060903110604050a0e090c09060315070210020c0a02040f0b1c06110d0f150810021b030703020a050c04050c0304030c061113 75
    0x60a0b03003424041c9907e804406840d16a0080510115071000300010741441070f140c10100c946a88524900c40c444100c0c40c0701d1203041e4054440c980698a402c205000b1540543c0050301520b10b583c94440001d40703580d4509101c48801d441140d04100b003880700082030349480d05014054080c1280950725450045006841c080d2079143d06885503659800740801078801140c1d15203034000246541d185607031781c8241a4640000001441d041d1840015503061381500490705505852086400b070220741000007024003902c8980041c01c0e8010b007100804911005510702004c07103144982008201034072803508402c3c1603007003540d5951806403182c4c04081401458401c01c80c0076102441c100a0850400c1c01055650121050000020740e00056142e0381828507004100845019012a6542c1e03000f407400070746854450204503241e2007407011400d01464a800780520480140312500c0c110f550310745048030950703121a01a280c85903640550591403c6000042046c000c401c840001d0346440d2201100c068 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 898937113 1250 898935863 898935883
    0x307050a0b07031b0c150309140307150b010906120e0102030f2d070c2a0806090c0303300903090a06020f0c150c07150906021b011d0612040203 63
    0x144c8481802c130020324030a03002e83c26100600c198910029080b58258010300510f803010748501d01d0350300540604500000107100541c4a0a070342200e800441d02c0c01810f8908041da40c9004c07400001e404d10405109070700c03405041d40240c2c004141d00540750401400ca900c00da07586081805003100308480490301d00c40315604142c02a4000503000c032110102220f0860140c0b88904014102400744140034030000c0010401d034159694100c001d042d113800a449005d07a100303480080c099400003461800000c2041d004c0f0000141c0a103142c171000081000740003585c0307890141900101f8203d021110344641d07406109191840085980703040d00010040d4015183d808034045500400e81003001306008128900c0a91081d604011100e250342030138000d900500d01000f04901c100d020005200c001802a440c01e00d5464035031201980d00c40f00220785900c0d40504d05095943d03c107510b584a548100c5070345a042e4104a00c1d02e0f42e02c00761034000f0b83d095020840b1010101202002d0000b9450140034a1404c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 898938363 1250 898937113 898937147
    0xf010203030f0a0506060d06090518071406071707060f05161e05070f030f0e0901030b16090b1606050604020304050a0326090109033b0307050a0b0703 66
    0x194903120350300842c0072000411050b01c0503102c0c8003254951b02d600c2e003138503440001c0c4541401040e844201020060004641494011070384200380442204049603401c1540e65102c44503058041e40401d00c9503c0e44080700440311040000900c5a4105171a0080c003003d6114003008038014500b504000c00303461024010f03204a0410074a0070044d0740d0004c0c008500324010403011004194800c0303003607401d40686000601900c07014020b690815921810f032003d07036501c070b40314102d582003080207100440c40f007404001d022039201804601441d04810802c40c45c10001c4c58000407450701d030303108600540c200ca485c0070418098050707040c0800030300307005081d4800b10542c1e0440c20340c94561100c80d501c150550001d8140f040d003039244041d4084080c5807a0b4092101e00c0b000f16107007400c010541c001c1c40480c1c002d40024101e444909042d50020440030800982c000500440310004c140c0d119880d01041d03155603151040500005840d115591a40024a032a0002c00c0d15508907080c00307041000c20600805c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 898939613 1250 898938363 898938367
    0xc0c02040609060b0912010f020a0c1a010b0708030604061e170c1c0f0209010e01030b070e010e01110c13020a1115010902211005130b0306011403030f031003020f010203 74
    0x40801d80e5005d481041000700c0700c00000840c64500366006026120a9501090000994400b469042032520000c0c512522a41c5100a626010860410300031b000c0c15008074400c110000110301200061504204010400101e43c3e6440744298840000c0302240c0c2d510341d21280040100c02041d036a010396154194018150008280000511030581885a005174140440c0c2d85401e0040e01000c90600d0755000d018042e85585030001d8017040c0509100444400c1040000982894810f54041d01d4074103040e19a56691240c0900548146007940041c1000d4400d0f086800d0701c13a91207002c141d001e0740c0f410400590300c22560000408001a5144681550b800341080b4203165043c0031070181120139410740181c4030b102448081015020310b0405a40442d01c001c01d10459400b2607001d074084440071180b2218200711004418140c2c1d40310424581e06030040001040440240010a1008000101541d2402c1c180300d11108142c1c01c29502d8a00501c00050140b0850178442c4c100301c41c1110900045d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 898940863 1250 898939613 898939619
    0x3020c190524040804050111101a0a050316030b19050a0902030d0c0818360106090b03010e0411030d0305190e0627071413091707150c0c0204060906 65
    0xf585105c0d91003101d04002081004102e212414029030324010700b031400c00d0000e842410b1500c003012603180c0e001c0303215500342c0c000081c1500e000610300343d86030b640707000401c001451500c444e00e80003070040c82c4111341c0d2350340e818180005030988503c510860000c03d00250540d11801810303e01400f03645040288550940004041007180003654008110300304079204035070456011490030311b5401c15605000c0e030000300251003042c0464101c05100c00451076400f04e03a03aa0170085412100351b00c90102175078001c10041c0044e41004483c5540580545810f01c41242014046890141440030000010f0750b110140400304902c00b03090f01001216480074816071040e000711684514001c0c00d490100c80070441070414140780c6215141d501440e0b04103071010390b5a1000e40c846981d080c9504188209114840c020070942588076a040070b90304040321035a6082542c4400311694410b040070b035510350301d09807991920211400790703950603801030f503c90003140c5584c4140003c1c2c820079004458290b0a140040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 898942113 1250 898940863 898940873
    0x20a090806060a06120c0905090a23070f142a0f0d0e100210050a0605041112060112090203030d0212100e0c0a0306090e01050105190b03010603020c19052404 69
    0x8005e54000c502d00044045440b01c09882c004565800540c01c9403c1104126a402040c1d00c00c48020a001c207440704d046148500c40440e40b039007240e0f900040780003480303203a40082c0300d441d00307808032510f102c00b05103010310310300801c1c100f01c0a05651005207004420a98490002800201c0d00854060010300e020000c01401a003601e080c1c007400c0d4040c25100c02c0300031461303100304074200c0c8085100404100c0380c200909900c012f000d142c05014000c80c10302151600d900000d4084901480d0420220f800c0e5440c0c25004407162822020540354841d01c402104026075030902c001e00500074440b2005030b580030342c10500212460300901d05458131510303007400c01191045800c16540302d06520103c668909083e401070b0014851600002d1691340780c140d08502103041540240e0603110202c034080b428a0030400c2250003100316001d0080c07082c0342800104100c1d40a42c0203440c2000d15001507504541460001c0c0070000c00d5940280d0300c9a004109002401c4c00c0e0585004403241c551402000521b0180c80b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 898943363 1250 898942113 898942127
    0xa060e120414040203131b06020c18011a040b120103030f0e22090c0e1509010621090206030f04061a010903020f041d0a0302070918060c0201060504020a090806060a06 73
    0x2d402e0159400000088491500501008440303a0201440c2c0c0e00c1c002ca0303140840e4401700d074012000903109041e5003800602d0700641050340340d402120950600e80c20708640200c502041001090404818030001c555a81d10300003a20b81000340c0c4000c000d4943c55400d0080104d58044861800d001520407903d071740713868074107004101013100e4002c0161440141d80510040c91074100180c5804a01a000b02380300710b0380c610640c00b444100001000070b1000100300115120f0a01c101000308903262215580c4c44161a03c07d82c54140182c00091445a20b8021480c16232088804900c1d0020880811003000707590b00c204c1c150003c481e080f641c103088605002070601d0490f0300001c1d10948d01c4050700c42c0d451392a40c001e002280701922110320340c810000c000b03e40c0d0b05008030044001d8002c029000c200e0504c04d10940ea4070380600f10444d03d49001c1a2030b1000200003071900e040441d521401c0c04a21030322540010700f8030300520382d00d2000c1a45043c890034182400580001c3c8284802ca02c100003055001c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 898944613 1250 898943363 898943399
    0xa150e010503150904110d08041a0901020a1707080a050307111906050a0617030301031109040c050f03011104080703020319020102060711071203052805030112140a060e1204 76
    0x1e074100d4903100c1e03090600000b1003009401f07500c81c2c5106034140402040c070005e442203580c0c5070503140d50052806d1060702107025030075005006912030300c041c001050b00e56425090b0303d016601520301d00011501e440f6620f505c07030b52141000c190700109008480740c0c00701c2a0302c000d00910001e07003012000204200703800185001b014008503100e4003c02d1314000c45500c000010528410501c00c3c0310110394005440340c00034032090780e11040b9560010618104081c019200307580c00101881500c1c1028104120503d00380a9103805640e10f01c0b068400b210503600400160080c00010004149184101868a80c50103041080b002030740c089440180d030009038064204901342060321034400800314041c5070402544c08111000342c03940d10102407640040052108442c2c05180f0082c0d020060080460510f6010641c80000c004000400500f12005462400c0078818003842081419648204d4501284000d0a6640c01d2303440c01c1130a401d03402042036024a0040c441598100b03464095030b1600c0702d02400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 898945863 1250 898944613 898944619
    0x20705090c0a112e020f0412060b03070609050f010c050325060501030b0a051302030a02060f1b1e070e060d08090306040308040b010b04121e020a150e01050315 70
    0x1041e0400900e0251001ca00c460040204072207031030315058410b6488a03880c180700d01d0410900390216981684c94002c441c0050826180e2614191800c0103200500429460980c1c20b0780e0b80340c6e448080c2d581c06200d1000149082e5480c010f02da410305d000c203d007412000c04007a041c089480040c00000d5004410380d80d00800300007000ea0f148032758a988a9070100501c90040c9203070f01d0301c4004420440000c01d82c6000e0b003246841004603642c0e0400312944200e00750b0b0080e600d503100c01c6404006280c030f000140500908600d09a0070034090a00080303070452002c5040b00e01e504030810320001c40e0318584803458880c0014000700310103443c1c8440100c01c03c0010b48094050700e2040c1624051050744c2c0d0480340c010f1800703012201140f5050030001e201d01815034086610031302200000801c40007101c107403015640b4050b01010f04a00079545c04402c8030814819000c0074400062600159850f0003011008240101000c8441d02c0850401808810804252414000706000f44440003404580d405200901a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 898947113 1250 898945863 898945867
    0xe100c0c1e050f0304080102030a060b0f0d0f0b0406175113050d081608090a06050430050316120606030614031516030e062401020705090c 61
    0x1d420aa410600001c80307040c0f4a110000d400034220300c0540c0110b01c14100c000080040030b072516034040c064071502404404c3d128041c0908907031200e10b6071105150946169000402d08065030208068403a254400b80310070308180c850050a030b0050081740c042c51704240c60000030041070402a041c0d0460841c2c8a0500801a81d4014100c21000042d41000d4103080086006187c403031213905e91000c00c0d401c100c606000e40d0a03806003050245640501440d462003110340e0204c0303060001c8a070000001d00e202c4061050844d0071010174407038414680124010360a4040300c19100076001811140420082c3c400b90307002d058226513540c0f1070152074001c81c1c0046044640240c040c011103128041b1008030220f80d140c2000018000e40541c80902105e0038078400c82c4040000d8000c00d5100c00c401515549003040304000207021600c0101c0403480001541000501094404581494000700300c5104410021310300e25440700d4080811446001682407000b4041c0a0400e00410070408014001140d05800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 898948363 1250 898947113 898947173
    0x90c1c09051b120105010e0a090804050d0b0f0c03060a03030c08070b0f0108100b130b060d06030b0f010509070c1e0215031b0703050405060a120e100c0c 67
    0x415001840d40d40d400c001103030125882840b0702e041801204407641e00c204090360150340c1105040c003c090481d041161a2480b039902c1d82c0424014060a4000b210001801c02c0003191039909c4a10902d80180910004106131824105d1108004809055000c03030301001d00c20854159246210201900d41c10300e014400e0324030600d070040d00d502444100404203441c040400001c041c1c10450241282c0c0350b40100ca2200c506401c0b4441181d000c2090240c00400e1148040412101034101501145010b00001c1c98207040481140440300190000c0b1089000c5005003c0c500395808a0705014142c01c840000c81c1c0e04140c2c8016040c000c081100070601d02a1801c0c0301c0b5140000d00100c146141c025010b607201140411107140c00e580102e4501485420b1500141c290414010a4078809039154940c1464907050408104481d0000c4401408004440403880318440c064020b0175501034207400185552003034010864140c6040c01680420000c00c1884280420202c28401c1c0398030042c1c45220000901e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 898949613 1250 898948363 898948417
    0x80105011e27060509071e110c06030408040806090d1403160e03030f040909050d0f08241c060b061c09020f040c090303021c080705030613110a02010605090c 69
    0x1c0c1360300041e4800c1c0ca040810526a40042c10b400b40700003201000c1d095030794244026200b04941c800c02145650099840c1c0c8100d040160003103070818054080079080c6940c5144040c40c103541202c0f2500c0941004104901c025000184140c0b420441e403200c2e07065181c1946d51403400d0a4100211040010300e00e032000b1039440038400c607503440d90b256049585e0346031940011400f600865100721614882c0c804025183e912503c03a06c101031180d0303503e54072180c845605e28019081c18000e4035050740c3e4041020f20099580c00704211a14400c4910101202543e0070724a0403941e64030407450003050100180658021070411085550110b410300080741c44144c00030030840c4040500c80ca40052600c0030385c048003604905c401084a11a41c212040c00c0c4a60140c8031070b91080d0050702011aa082c0085610b080c040e001650b405203002e002401c540640c0094101a10740443d850102d9400010303140a0302070342805003002138041a114040303181007121558503148078024800980e600c0990006004070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 898950863 1250 898949613 898949621
    0x109031205210105010c080703111c270b13122102071409090a0515091209030a020402090a0902040e0a1407020706030b03070e01080105011e27 63
    0x640100c4091094a0306010103803595005040201c046150b50b821440000d1150441a0580d501030b0741e00c0d49100001da4a801544d0009101102840b017030384d504044070702c42049140803903c039805020300030b41c050004c050070072501040c010f5501c1c0c0b10032441201c0b00058072911801c9650443c150344c0d07980c101400300e44400d15543c2120104a17090743c44601401120301050380260800308200b03100c103038118001d030780c5d071034146c0314101c840c0070f051400c03680e03528010b149264042541c00641e6038400443e92180e00704111001c6131140b0340d03d01028041428003c118070788421403010101031a142891001030780d2024400e100034031680d00080c0141e1603403643c5212100500079000c00703646035900c6106401d101c0c5000c0b0b403c0310314903240c411400702c80d0114281581c01182c0580185c40324600340f9204030050119088619010300c0340410002e0016840004c00d8000c003400c0c0000a041d50415800b0760800d10b406060640c4460b10610030b101070103011000c200c07490304180c0410b5080c0c844190040c050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 898952113 1250 898950863 898950869
    0x80c07020927030d0f2706020f070212010905010606030c050304023705040c03020301030b061e100305040b0c040315050901060b0403120806041505090406020906042d0e060603060109 80
    0xf4000401c00c810050b01c61341111001c0380740e01005004a15800c2c6000079a4038042c80743c034100c410b5040b143d0010440503170041035481030310003043d40b80040c42e40108401d958403141107902c50f0b45d550200400e202082c4500c001810385440c0c01c0c040e101c1c030341800400707600014101078450208084a080100320085101203019540030034041d441211030032035411561140b050138055420281c1e80d603419442403003201d06803580702500600315103813001801640895103098148480d06184080069035840c4c2c1030400349480c50344c02140c1c40c41c0c1407408159964000e0903038000e0345028003007800081c440d0351107980d050988001c000ba0541e80c00305c529000d40340c3d039800f01e024118005404428000805860f101044850b10307543c2058590348240b000329240300ea010342d514920154107102c10710704452056040f0b07008520150a10f0307445000a0803542c801d51001035001760007031121346511070100a00d038486611401801101f0710f400f6007039011000c018000c51150200000240f034607801040141d000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 898953363 1250 898952113 898952191
    0x141501031503122c010804201306050f04091101110a02101e0f09090b031203090a03020d0309050307060902030a060501090b0f030325021203130501080c070209 70
    0x8000102802030484c50304e1140921000d0f02c0fa802c030394641c0d02c10f5400d2151207039060351003c406540704e440c1c050601c04c40d8005100c1900541d403040b1001d42d0703203490200700c86c8a1220002038442c0b408081021640b404a03101e4015070071302c034080b00405d10700c40c1502d94502c42800c207403103801c003240b40f240d06020104400961040a0205007141181d00c0003400c11120312a071340e40c0d125820503600035191041c0c00300c40d42001540c0250280000300c4036402405a49074040c040314035405200c04030382d856410850b080c1c01c03660304c0070003040c0901d503040003200c484802da070400f08003501441d181d058480c400e6480140407942c41c3d007004011902c08011140d65582c10400030851035840703031055405010081c81c41d078854150712a030341045140100441d40e01011058a148e0905080c0700010071808040b641aa8003400d072600012902e0010300080c8500c1030802c104481c0e9a04000014200c410301602d0020010014029040140c07101c41c0c513280c04c580c0c90340765103942c0007604242060b18860098a120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 898954613 1250 898953363 898953383
    0x6030411220912030e0c040c050c060412020106151d011412100617041b03021504030201021002121b0c150f060301021c0209030304050411030703141501031503 70
    0x71466a26445004250300c10103440703414110803407080b4292000c00569804603000442c02658900d80741d405501c2e03891041c00c04904104500010a05040c021902522901000481018801e0703084c030034a0050107600010004020042c480145405d59110f801131a140016500040c00ea00441c3d940c0d80c50605028050b6440c00c000c0c00e14619141d0681e009898821985000709400d80a01508204074202e07a800300da09545d81c1e1101600c54089c541540360b00c000305000440581c440e640e1100d892200c203422550f54514500c002490001241400d501952040c00005a802c04000e11f4503042004061070410406002021002522403240b00510500c0307560522041e1b810044076107441002e0f4080d1091071030b55960103260a0780310302814104c4a04080345445680c4030950f0103045ea0000107411a401d1648400101d03003160700341180c04c00900000310030840c0f600e43c0343c01030300c0c0256400d5881048505200c141c40d010601c488008605141e100c801c4c01c02000303c0105280c0007585c10450000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 898955863 1250 898954613 898954669
    0xf0708040f0914220f0f02060f03041109040809060d0b1c0c0e160f09120b0a050709230d17031f1a030a140708100801050606030411 58
    0x346040f2410815000d409070014403441418104034629613807419415030076113200d581d4a00c108101c80e804481c3c5400c03003080314015886100c05072554100e64001c0030f42c0d81c18a8103000003840c290141140c4039640c6442080000b82034a01514651101924440c0d1181c998952080c050304082c0b410341d402c041e0085052020302d0314541200b20b041c5c0120182007540e51240303412160800704540c2035140d0502c0c0200443c690703100e002416607000c0c1614200c42001d448200711180c0300010001500c0000d000360a00490b0515441050782004003814032010180c40c05100881d00b4820300c0c035034060a864110007440076240c51024100c0e069104000510081032550040c941d90401c0e241803c100030041c5d48400c0c1d82c81d1050280094483d1400d20403141c1040898280407588000c0c51240d409480340c211205103540c1c000d9183c050702c440d0b16000268945403000000c0d4080035441040580c0c100800d006042d1140000c1300c0d0007941000c0724606045100703001c90340e486682c00480042e1040301c80c0d50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 898957113 1250 898955863 898955879
    0x60a050d0f0f0614061b340815040b060d02040207060606090f3008030403020a11030d051b010b0907080f0a050402030d0f030b0d030804060501080f030f0708040f 71
    0x60301c1c2c07880584070410540c1d803143d44004245965500c01500240f040003c4000d6144110910306602070070342c02c403580718803049000c604010f290394840e03460701c10400881001c8070000c0c048001400f0740500030040e202c0e00146810224034003902c05841c0f1a405004541c071034a40007450140b69030054000c0d5130ba00c41e40e1402c00028010351284c0400190207200c00303d403440340000c8240803100000d280080d84503000c0c65070710030095281058507201e654070701d4110008042d00c000d944543d01035005000700d130303a1900304004000e030340c41540d42c46900641c00303150a0541100c00d0740c1c030154000080340d00015841000d140101a1034008590000f28a02000100c5503c9241c180c0705448201c0400c5541e21915210001c2d43c1c429240258142c2011001c0c4402d140b0401040201c01c0007031502103024808000401e00da120b4014050b00024081e03401c10040c496680110707401000320400804c09041d07030410355501c0b801202c004c011300e8000001c1e2041031211443c00d4030007400030348015410196890a42e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 898958363 1250 898957113 898957121
    0xf0e0304031b080d1d0f0a0305010209130221040f020301090c0612060b1207090b041203140301060903020645040504020f06070807060903020c0315060102030702060a050d0f 76
    0x5035100b06091020a50403001300f0340800618440c1c844000c14100401800d038440c01d1807091030340121200307008944980c0e07084183c200840c05480010b07501c080c24024058060400d10780401010f004001182500404940c0740c00c400c034140141e4049625186020261918401400f940c150b0030010194180000140400b040701c00f03e0f10f800c00f00d00802801c10054840912441e14815410300114202405030740e00c06074001d84600d002d490711900c407803c028003604541c2148400381d40e42003901c070415401011000241c131160030407a04540c942400208001414040240280c4000c035040b248228203039000402c903040481c00380341d0782800b1134559045071804103113102c0100103280e11040c5030409104035400741d40c01074010101c0c09044030038040c2c0350348408001c42d00c0140422810001c0b401c42e12403083c035035200368050500c4000c14800c042c501820941140c40c0d0844d40000d200140c1c1c0c00004656000d036050302c41d40d4035088490015201e80c0280020003075090b00f03002c2000c82c5284141c1c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 898959613 1250 898958363 898958393
    0x60d0605010807080c040b39010c0c050c04020c030d050106081e07080a02130914011d100614070b09250608130c120605060301050a090f060f0e030403 66
    0x103561a09030790744503012284801c00361742d0b00941c0700c41004140184801c410003042c106041d540044083c030350007002c01640030030404d0001d890350380c80585045140428001e03910b010443d8034000400d40e00c151182a12115280b035110702c00c0da800038406071800750501c19250124070780841040300d50381d1190080c000c160215074201d4044480001c900760f0345001d95016002d0101c7d40d4840c00300340d403400c04410095010f4012548458044040002d0092040c054480c1400b005c024480c1d09524180b180b00c038a111402848015122610400841c05080154801101c21030719140e10308885000e0b41d003200c3e100d03030308029110380003090400c1440c1c40c0000c1e0010382e9030b070f520f42c50220a112540f0441c84d114079a0045000240d410340c007103100012144a40d070b41d03c1e80169421100310b40d9503020703070212084141e000c07620300d6114404c00106d13107420b10413603030312254076038080c000702c9007550f2401d00d02e44903540c0c01042961354a02e00f88510a242d8400014443c0d5036007120f5031540c6900b807400006d50000f03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 898960863 1250 898959613 898959617
    0x1e03030605060a0815031906021329090f0405070f020606010513050d06140907060f2f070503060c1b12030403051803030d0e06060103050c1801030605060d060501 71
    0x8a80000e41e03090442c201d071000380ca503940b40622911a1040c3c009802504041d441d03143c46030300541e0200d900f04168212402c0c2c441d20005955800c100400b0500c055540e000111340d00d2100140c00611003064003052a81044c481080d0303032603000d80001500b002500703040a400c1403a00e8100041190001981d01e0070501d80e8007180d16a80e00d200044a081c40303070018003803000944c0142003000d410143c26602503a40f090001203201c01c01c0120036502010121085691a07000c6c4100300403180d002000c0801d1a102841d00c907420304214080a18407100b055082e410044940396178086000701481511302400340202501d060781041180100650404503c165010030115014408100e000800000050319000c5071030841d1382e00d440035205030f00100d090f00703180e01c0504501051903030140000c210b0220075031400148810201c080c11b140910042c800390601d807400c4180102d03030000c0402c1d90ba152040d0807010712515a4040120081e04032580241d40000010a00c0c41e4089015044201075460a07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 898962113 1250 898960863 898960871
    0x606080718030c05010521070314010824130b2409040b0705070203030d090c171b1003090204050414191e02040603140601031515050d0606031e0303 65
    0x821160716555030391000a02d5031105000c2001594018400340800450100400d090040131208044c03410008880080c0040e0742c032074100100c5524031902320301401a50000f00b4660603000c030f030090581c4900b122000926100301c00a07950b5048220060115540304203900c01c242401c03090300c005400e00042d03c24441510b03010801081c00c014209501c0b5a070810060403003a12640c00c1a03036658400d480c00c0c2e030980410000c0002c900c1140c0510315201d07204903e04010a4a4991071110fa5030b154100d8a0480c0c000c840c1200310400340a0101507404000c07030784400021140c01e02136004009060b0020342250038a01004103010902c040507501e80010020741d040e8280003099002001a16000145551204084105100310101849081170f01c00303000011126180c2e100d034251035840101c01401544200c00600803c04807000a4205c0520184140403025440f903210440210600400d801004480c031480d05102c05134205000860300078400300c06144144440c17840c40695010305a000c2814 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 898963363 1250 898962113 898962137
    0x14060f0109090c0e0c040b1c0b060403021807111009050708160605180409204c05180a0605090409030915170906010501050708031906060807 62
    0x62401241d082c15401050b0400780742c14107044140e610000390601446250510020608034105801050800d584018464003224040700100503110340d00d0050740952414030080005071911701d40540282410209401a95501c03441213911481002401c1942d1092440b00e80a81400d648210801801081500c00b80380d201c80e10301d581c82a00c4105034004410004040009070b00c50409030086a00e034022000703200021a0010b42512030444094480050344c1e0f5850f040807101041d00342c60200c0c01d4641c0c000800c0c800d83c503680341c052a44141025851064180308400c1540610000e91103c0d0300903600d8403201911000381540c0020704400300701251000d250708285004044030084405a0f42c440e0f11303008260b002d1102820f0030079000c605001803001c1c00f20321000c058103503000460103541d070030303020030310307640c120042650041c00244854001100602c1a640d1003002c0f9020a81c003c2a0702e41c0c2c944590360f8050409210b4080341e24042d1915101082045d03114403400e01a21447d603d1041140e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 898964613 1250 898963363 898963379
    0x18020102071205060c21010b1206040e0d0e06130816080102040e04120509032a0a081507201515030d0807170c040608070813031b14060f01 61
    0x2a0600030f0515801000000c224482e070302c0003010000c448030b50020980018111955a100c000e8104000546010444813190262842c0d00d941c0800c0c01c0b0303001c0c00620b030790300d10150b15240c50b14041401c2054450317000c3d0450300c4200031580c00403514500c40042c41d60751104c0b1138640d01e055455507042e03041d00e04001444001402694180d0f450a941c80426440d42d03601d4246410008103000248842404450205d075800e226414406801c074080340c22400d02c0c04681061041c090b04a6880303003042120520503400e00241c1c400e500d01440f101c0060030340313580409039248000e8280f00c4400e0b4a0080c14100001c0c40481c80c205411428030482241ea110a0f0b9001d8207810b0307031840c07150180e0102c0c820f000001d00c00d501c1903400099a06011400180c01c0d00d80855141d401c460518512100180420007558410200c0f41c1c000b9039850315010718203001100340c0121000c0e0340d010301040f140312000c1c0c40496400030a12401d69011107110034001020104070788550b01101e8034010480d8030000018260 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 898965863 1250 898964613 898964639
    0x60a0b01110d1b240b0112020a02121b0a031d0d030c0b0a0e01020a090e010b04030b04060b03101b02010c02030c070b03090a0c0303180b070209281802010207 69
    0x2000303490302e0f481004404040f03121000b07036200955801e00301c404c40d6041a007098000c903041508402000c103240000c080003500c040c000c1c40c56480003501c1007090555003035001ca40001c800d00d0008640ea40c07020b04180e00c10200340c0d030280c51314807070180e280355908160304200892140066017618100c0031603d4401c200707010a80c1c10b80a0080342c994215100019a415445580b108907644001207940300304e1141401c81e00700d1b0f00024042604240240300c00d0350304004950041c501000410b240600b50342d00e441502c01c010340018046900c51079800d02580d024420160166151281004032a0400808007603110541e1001c0300954138007150100218400f03c2110622142e100c01003035641e24000d40c900c06540f00511401c1d0b40c4c00781c040400c002413221582040114000c0d9034120041c00c803014a01c070781c64400ea04c00285860200700317540060715100c105580c0849184104042880800549014606842040c0c03c00078a030864813941c0c00c122101c44600c00b4000e0342224101912800c0c414520 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 898967113 1250 898965863 898965883
    0xb0a050601080a02130f1503051506040302010f0201060306020d0204181b0e03070b0c03030403080c13052803290c030103021507051f0f0912030b010e03060a0b0111 72
    0x18075814001060714009030002d049244800324400b54066440612030340d04182c51f003050040d0419030308104501d1381c0c03500075541c2007030303401c158440e400404400146061149200080c180f041c000402c05030907000307520220046030009003c0d540c805041550304020342c46409600c030a1000c00ba844d5030583c2091240702d0a43c00c890076510800300090070142c2d40002000354140e4984107400010501c4110380e0043d0645444650081d6140d0406283c050705081004040520110080c000d41c09042c05c1d003404070046440648000710700c0d085003841741c0c0004016040c0c3c210398402c80040081000582030039031004681d0321113641400c109540c420141c3c503400351368003034445100b84010320161500044001100034503080403403909040d613940c1800c00c4202082881400c0c0c0a040c0c017070800100c0d000f55000141030400030000b030002642c50954100611a5160415544044c40303031141c2d00070588000411070040844803030b0b00e03012084c68080c0c44110b41c0c40d07000440303040c000102031100140c0b405507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 898968363 1250 898967113 898967117
    0x23090a0e04051c0e0111010e280501110702010e031204060507110d0309030b01050a050f0915090a0c030c0e060a030b03030f040b0309010c050c03030117010207080c010b0f120c0105130306180b0a050601 88
    0xd4148880700901d272030401d410328216243c08940808000380b0244180705c1004403c00e009610303010310b800094541006d2044c52030203a00620344011520030300408071010b803401420055248c824500b00120821010000560000b10000368082416001140141101d128034040c107203030780c0c0391024010740803014413400d0b070806038600540b80c861605048080d0300110030581c82c07106020b03080c00501c1d00101941c2d108901a6a81080c04a055042c003c0c201031000d14241041c9207130841001c1001440342d0215030082544d202a940855034003401141e100004604580b500c0f030752161400002c540c4162180415507181428180310740e0f0044041e60350b0400304c0c50156082d0381c6440c5800c006a007281e00b500916540c00c01050000904103c00790600c2c0d0b00d1400001004060355043c04121081c1c01080340c0700d605444c4200c06504c900291400c1e104c1420300c0d0040e190300703000100d02e180030300541005000608105c0f41520740340c5540765064595003c0e110484450312250240c90413a10f00f41e5041d40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 898969613 1250 898968363 898968373
    0x6050108032515050c0c060702060c0a1b14030a110106051005030a0906020d09031d090a0c020a050a0b0f0106091a0f1201030323090a0e04051c0e0111010e 68
    0x11550030960502c125400380d000e0051420309070400404032075080300d10140e800008101580404410041143d103c281030009019a0410350245031041c010100c1e010b041000b0004d50041501c141000900e16562180b8000c0503006004c051031307140c0e00850b01c924000740341d109100c510120140150401c84da00500010b400b8103e08100300c0720750344014142108151603c2d0300e8130004d061403004000e020012603000801c007009150040c1a04a61558015400c842d1082d46100e0f642e510103003600201d0100300040c100c0d10710b2130140d051110501014041d4040d41d00f40b4024080d08004091080400000b178a56680e210201510000b20a00500a504d00411411081402450010200e09846254180c14a01c03c1c1d4003012001030b09810885c0040c091068040d41c140b07803043c41ca00345005000b04142031a1204c404503c03080034500c00c1c8841c80403280b0100f014040248429544c0400d000f4607840c0383c41c030f0440068524159041400e00007101e5201059210780d0600c202010b0444030b1000c2d207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 898970863 1250 898969613 898969657
    0x60901030908120702100b01080727170a062307050307030e010c120f090f0602070326060307121101081f030f060b0a0303090e100515070605010803 65
    0x1001030070940000c8861150801010a0380ca0900c03010341d20500d82c0c0e50081040041300d10442c01607481c08040c040c10b10030610240211540c00c0510245003410345101001100100042c020660700d40c0d50280f03038200e08102107056425808941e92035180e01074a0706000710300500050304801003108000c91000c49004001c41d9049202d40000e40d0415098a00810790031150a4180e00310341030708150001086000b8117103541528180110030004030700b881d04005412080d01ca401c0030040c18070340106015400151034013054016144a1200381010028070310000b246021903a030b00b04191031080c404e00c507000d00040d140d881911002c0e0969440540c20303c1700d200010040d44c0c450710261040b00644c0e02d4004414842038001a804000c6000c0c0303000758000d903034074100842200c4e80406002e001c0e0100c81402c5c8082500819840300704c4076014549000b95665070143d80600a89800240e8040020005260111034000c05040c0c258020b0b44d0401c0666601e151840d0f482c03050350100079004104030300034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 898972113 1250 898970863 898970867
    0x5040c110d08040302120c06090d090b070209040620040906090506060909191514030a03022a041401030212012d020408340302030c0904060b0301290306010302060901 73
    0x483e4100380b10f801280c81100c040484961150000d01c08000f040e070100c01000010101004030083c40301290801c180703124100240c0000c01d125001e00a4054424000070404000d180c0d4050a2100f030f0f2542c0004002121180755074180d841703441010b6a0b103003000404946105184a100d010780f00050034146000720410072f10450750401030000917900f0082a001c420b1003183e0252008120245501c07100c02c0d4200b14906100c19070400b2030070700980c440d8241400081c0c000400710104000440340080e40d00ca40e94140034101800310344950854180040f402952511280c40c6068920845505004581e0909841e00321a200b6801c140700080c0305c1420300303082c0780586504070880c0d03c000c000752070302c3e8442c841c1e0b6191070503607060042d880c0e4281c50054a03490340c580c485401d01444124940810740b9540000340d581e44418403041c49403000d0b038082401c000440e400040c40850150091022044484554a0003c100501740c0b481c00302020103802c0c03501c0d0104150f4180c0381c0c02011542061054001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 898973363 1250 898972113 898972127
    0x5060f040c0509030109030207050418051011040801060e0f0a090b0705090316030b0603071a0306060d060306050f010302120f150a020702090916060807120c030f0f0605040c110d 78
    0x10301c000d110041101052684080c0101644940a0707001010502d03e00346c2880100c9900701102c040d110b01401d112000101c02040700e0902244050010a0901c07100c2901d50040c4980e038000419581b0b441d800080748880301e9456842806010b021084039a51400034800391103035848018818180c0340c00190500f80204090700080d10301400302d540558520780000805e504603001603d0101124080203c03602d130820441014210007880500003800c00707600a8144d002c050082d92065501107240f8492507500d0340920021900480d0a0080e03082106680038400004e0005a008203000003510003482c10003c2c440c0d4020103090700a0034032610300d1f0801e441c103407409041904181d80130400e040240c1c1d00c05140f98001d5148a01070306441030865802030300240558000800d001e54081040006034100744c40d01100c600300840421840c0e003001c01100140034100b128460680703000c1c480c01c0c415000d81d104005a41003a1010020300b079000300d0942d00f09546016445003039115000108929100c0d0307035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 898974613 1250 898973363 898973381
    0xa0f0207050411030105040c0309050709110d06170f010c051608040f0f062a030e13110405040b060f0a14120c07020f0d05100e191a090105060f04 64
    0x8190303030150340c5900015055a4414034400b800305004001404070b440c0078422070300f0000081c1010043e991036aa1040e42341c214034482c0703402042d13403001e99000240031340d0308903012420880010030100ba21920841948880403c1c1c0e1101c030312984850074018481449807018014240d21858200010398800f04030300720035202d013114084402d01c8000340300f415804204015080e8508030100c0182400f00046c1303a141070300c41c0e0f681c00e80038580c400c680c080c16040740c0c21900768040c07900d42807200d03080020a0321940321019507002503160190b100454281d800240c01a0740c030845051003050641710400c02d450041d0042260811810003890080782e0080c0c0c3e0100c0d106400300440b5017043c40610713031141010011116500d502c0300002d050002c5251010f00600508011140380c900c050081e110309540d501091a031b800101e55840004005102c01c209980c61400000c2c80100001003a1604c1c40000c8a00e10b070700c00701402031380d020524540060040ca48101006007050505250080401c8081e0903c94 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 898975863 1250 898974613 898974617
    0x240b0c0102070c2408060d02130b090f0711210a0c05070602010b15070c06050315121005070206010602030304240203130c0b0a051c1b030c0909020901050a0f 69
    0x14080021a4034405800500d0b11410310022000c00c0050221050500041031341040401400c004c45070f5200b030356410a0503015128400580e60782c41e810802044000c1c582503016400d1002c000c01202050f50f490f22a5085a80d01d0002004000420b07555a00580031004401068400030780881200006800c200c03002e403034031114104003601d41038200031041e003041c00140d4544e0700d58103542c1004c4a24002d02c00d400d01407913140c0324042d160b03108251514040e00d8108080000807600300c03a42c150a207154524004d00f03c041840d40d01e01031580e16106410300994030b41c20140001c425900200f4694102d419031740256295585a6880745070032400087c8201c1e86844501180700c101000348055449422417031461800385c0817601f0005042036680d400f40380100001c0008440d0180d01030241c0300c903104420f003800d0922401e640759602410665000b10646031041405441859064220f050540160385419402d180c45080d518280e1180015090101e41e041000114851040504981d45071840c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 898977113 1250 898975863 898975867
    0xa090e010609182d0804080114061e0d020109051503090606030304061b0804030b0112050f30070803341707110f1e150f0a090803040303060801240b0c0102 68
    0x699485e10b503038106401c048883e84d5154400c12101501202d0070b900200304070b03440e84c160100380508407070081d82105a0b902420010058104590040c061503000e0680203103040ca00201034520f066160b0000c850301080c40c81050045102e5080c0401110291880e81c3d40da08103c030f0000254041c01211801e08481100003003000001084480c0d0209010304060b14949200f6406420a01d1400400101003407a0381c01428809442c0300300078032290041114482c000188010b1100e44500600400d44042c04400c7c00004000f080088000540e039088454000b07410041d101c240c000c000d81403002d01080101d1b03041855954140c1000b0384866101c6070b0751800385907011301e00c48030f1400c15100f080a5190740c0d00c51800a4000304001800444c4209000000d04440c00c00794080c84000307401602c00e42a06413441d01080038010b040d04000a00c1d41c0144929684c0e04051500500404a51180f10000c2d46003014600c140502200d51550058460003500145420b06080002551001550316032075075007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 898978363 1250 898977113 898977203
    0xb0a12051810050903090409061b020d090f050a06030b03031e090103060801050c030103030530041707050c13060f09050a050c0f0a0c020a090e01060918 67
    0x2450050078820392003012801c400009080c00145000c01107024108110704080420500100010954132075450444020400f4504c508165004204807101e0b04107000345c0440070f00b03125800155422000030269107843c4502c1d52113014100e0038015000d60b42d8002c0c0c0005040040e58441d4100043d60000202030700e10b045514102408400080d90440d00c6450010940d2500e030368052040c100100200c200a00c01858149007001051005020007003c1c031002140e0303401140c6d11000780140f111405195160154041a01d00d040090110780c221068013410b1a121030800c989026190069800402840c130f03650b0420401091510081103c2100c6603035460001c1c0401d11031120500500c1842000551428002c089030180c0d64014110305400000300142d182407031070802207402c0c4100714070780350b22003940c1880040d000150fa548a01899800c200c4140c0d280c0b901035000c0c40495082c0d034800c10140403006a1403105c80c01d4554050030740203034a44014182020214441ca000200100c0444903801e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 898979613 1250 898978363 898978397
    0x32281d01050f03100302040b040207050a020d05030403141606050412111c06090b0f040206070605101503020a020d0e010e4c080c07060b1233100b0a 65
    0x300c44804e080c61800004209605251150810b20b980c1035174250300d403400a40340c040d03840681c5240203000301c2241030300c9402d10205000b544d000d15440030b00304005a1034600442c0e61100ca1080d01542e0700607016000450a005d08200c03012140e40d41601e0f007080e000d035120b42801502000841c1e0300b000e160083c903400d80081348240c40115100d5000015640e12078141600030078001010b40309030310868028000940d80c2e01080e148140c0c0e020b10085030310b40c1c03071803010603158060360310500e4040c0e110610303440c4842d0541c0141103201201e500b29080045a00400c440302050185101d000ca424140c1994140c200741c060b8140580081031125034481e81c1d10000c0030181400729154005840c629a4510310b04813803032100c0201c0b1101d151400f2075040c9102c071401c0510070864000d01c8650346508031041c1d40c543d10185030610103408181c40c5840200060f50b0412030840348002c5088030303a120540a0a007080300c1c0e0a0003000c51200d0040440d0a01e00b09401c1b07580325045020601c5199200011100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 898980863 1250 898979613 898979617
    0x9050403091518080705090f0403030e01141e220c0b04090b1206040b160e0a0f060e090c07030305091204030c05010813050d32281d01050f 61
    0x10070640e031081041201000c006000c00e03c19080380300640c100e014204119501d0708102d40d04030111525610950312181b4041d0300401e00130100300342650038903600004e40d2100c0301041d8407800319030329000833043c1161401e4030000e00c00c49800e03a600540d010341e08115402c20500b9003c0a10170461080d4454643c00c41ca0b00701d40087d802004603603103c04880c0d0032800c041152000c1003a0441c01007085060540c1c44e04014440117000701c0c0c44454070f001d406e00301c520a4000101a00001c0e12500b803594560b080e100c500b1446004650204484d40d000040302c3c10801301440c0300c0c0395007915441c100070b400c4e68224054200039050010f14440c0841ca08003c0c00140002c00055201c0c42c100300c081480e100014012040003080303180405a0301e004880840c40c04501c0c0d4034080d5081c98100840c0c900600d0724003101d0320200b490203c4070f47e8a4000c030400968000144051641c101076105040c00075070305a0820745105001800141c041650400c481e60344040c0384010780414100181000000381d111a110f03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 898982113 1250 898980863 898980899
    0x15090102030c030d150503060106020a0206160b0f0f0619092a05090406054c020a0c0515070308100506120f150a033917010c090905040309 61
    0x15a0743d148040c1d001c1c4805400030010a0147c01401c040d40c500707070010b5214441a907000e4021080001c0381c0c0101103600c0c108007156a400000083e850910510010180004480103480450303003e0126680707150101350928908840d0740411805410441c03803401504003001800865411a0010003076140c0600e03108140d04031a80d511a250400b800810068400380d501050048251b0065801841024101400c500300d4107440d58030100207104807141c05001a1107013210b07403040503d01030b580541c04240ea00c8024007a8001c103511580326820441100d038907a0310001d14803000c00c540e5002a005944107a4070011180303210742029a00c40c0030404581c02803100003d040700040800600f85140e21807640c0181c10450714004421403800460b100401d0b9010291096418502141005c20350345081019400350a0220591880c0c0358081004801c3c2c40c082c0c000300954050600701302c0d5405104071607401250750340e4910b102d80707009056001001c0181c800d6040016880c0f010456103d02c030515004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 898983363 1250 898982113 898982137
    0xe070203030f07030b0a3606030506060f0625022125050613120501020a1e05030a23070206070f0908060606031003240e0c15090102030c03 61
    0x580c2c0750404a030041c2200c0200070714107061504c1c8000c802915a60015000d0300c5072400200d50051003044600030b2a260b92010140481140b94004c28003180e6402a4040303d08c641d0446185845500c200007103607518030b52241d08400284124284480b54000c0b85640305004020303d01c8010080d0003041c42801d1202818000124004012000800821444610211400488910341203071841820560000c1c424944503801c0440c80708403190f182c00918004007000c02c000f0721003400a19195020b034021090364000f0480f004191000701c0c1c550481400f6079000e03540c1305c500e10707510000c80c9401401d4840000445c21610400070b14101d41031080e143c0904d4923500201440c2c50a074100038901d0031681da00c00c0030007608100800294800140c1540c20000448070780381c880d030316001c03100d00f0600d2581c0043d10201e0030308540982220f40d0072030504c0c07806c141c0c00240200f900d20008203650300d240d00032041d00401c0c80c1c515102c410f6901030140c8070540e41481035910b0640d0301402980340d034202c1034003500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 898984613 1250 898983363 898983367
    0x5070303030516030902101d030601081501080d210b0907030b09010f26011503030302030a050105042711120c031e15090102040b040303020307062a11070e070203 71
    0x3c0300100f2544503103a02c1842c045c0401205075000c80c080c2c1d601c4503410400c1c8071288109032048a0311000350070346290050101c860560b502d40038140c2c2d850304500613603d01d062040012076900b40104080390540c1c1c01d911414004c1d6a60001c0c0745c14980902c0c801c1040950f10241102c2c1030f034495203a02d0207003246942c045040c01d4100d0811070300c0340069000c014080d80b4513204015801303980b0f181c82c0c00301680d003418054144650110601400c0c2c4400003280281610310b011040541650140d4081c4001e640100116078030748081c8021200614414201601c0186414454006500300460302c903100b07444961404044030302013980e00c0d0300f402c0c01c42c80340d8010b0740100d000342c1020002c2d42c2028440c2101e6019950450600d01d4983c1481664025035024200004090b1a400d40486000b48000584541c0e0750341e807410000c0d180c3e080390f0780c02c032a403600381074146440c40d81c4001501c0620064203440452000c034000d00352080b0005104008040c05074550000e0054801c41119108140d00d030003035a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 898985863 1250 898984613 898984621
    0x3050310050609010c0320160e0903250c0e090d17060105070b04030507050d050301090507180b09011b05011e0e1b0d0507080f010c020a0b04031803050703030305 71
    0x1100d49a441d000701d8000c0c01c0501400c2c446aa001841c1303800c0d9074050070820070120103091983d0f8000842d41c0c0711000d900c21710001c00c031040c003060b0706401100c401e0718000e0f03401c3c0c403400b980a44038030640c10405000040000300080030303462a10a000712920038028a08a641d8030390200764902421100100c044d00110324411050b60450007141c40e0340d030784000aa585161070400640385001c4d000000d4840c000100004041501403404c96024030307004005c4032850350341e00d10010a07503802401100e844c0341c1001c0120f18000d00600381a00301c4174004031124551820700304ea0074190340241d0b00d503178100503013940c0040741d50a001800740070003030043c0c2c008174600104807140c2c0111911403221030f215034a400030700c011980d408100750340c03501800e042c15412101030400103145480500c00241c000e002c2d10ba07000800342c40000310304441e0740b0008000e00c085148110141d840e18208400078020784409400180020301c86c4124092926aa400c032103000ca40360b880f8289000c40706c0d001280402c1d50b40c0144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 898987113 1250 898985863 898985881
    0x30203091f1a04061d0603030c030c0607110d080103030e0310020f07050d180905070309140d020d031103130f1208040209060d021804020406080a03020717010e191b03030503 76
    0x303590618003d4405000e0181382c48030400350a5012084035401d640384001054041d902413049400081c40503007100c2c2c0f075001e100840d40d02d582080d0f418001040c00e502c0fa091100c1808900200440c149850f48a0380c1e80ca161400d4510b45030000d6059414028100c40b00300c0e10f4040d1002d0091a110510380f540c450015107041c62400c503090000c94180007455000d060440c2c1c0111054080e5038a850000c00c2130303198144168080d100d80341d03009041c00004901000115000107021080c410281e0880d808240c5800c2d068040b00c60708061296200000c0000455124031844094091031003154000682031803912043e40c0010307204440c42c000744001e4180415468a015400c0d088401101d1101d8580c13482e50002c0c1007615824950005c140d0300c0400101036541713582c060030050402c80c003a6001100d103450001d44800c00e6026014005000c4603c035201544e05214580e104004107004102242c0314449030000b1020110084400302f64100c0200145144681c0c0780b0021842600c640340c407410300c0e000d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 898988363 1250 898987113 898987151
    0xe010605221103060a030f0f0204020d050402010f03020c0c09041a0106082d042909030d1a010c02061c0204271a010e030a050601080c03100c0e01030203091f 69
    0x4030482d007000c3c0207002c4241c0d03c414401049a500140309040310f01c45107801d480180020b00041d41c05840403d1812104015400503449076200343c2e80d400d00040d00c1141a0124020034681d003e00c4c0d4003140d000c620505092494903042805141d004442c0210039045a90710030098102e10300040c0c00750b06000c8034a207020440200c030340072042a9090000714401c200010b290003132010f032041028255244814100b914800c13000c282c2c00014408500d415411940e40742e02404804001c6460640046040781c01040c03240c2c4803417016911901c0c2d10007075400300aa145c125000300b6070b03000c1c1202c20758031940703003e40b0041c002001d00078449140401c50410700c403980707000c0240341c15a142c10540740044050038004240d801700c1090802221510707164010928110510000403c04d00c558030021070703507440020b98407402c0c0104508413606465950103010170b940409410a0200340700f03261458440d03000c1c2d006181d10003680e1080324036081540d000b00d8510782500c0000b011055441044003056008021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 898989613 1250 898988363 898988381
    0xc0f0f0307051f1d0d0e04200304021305041101080703020a080a0e0f010f090606051005090f04090501091202010f020405090a0e160603060f050f060a030e01060522 72
    0x14506000c0740d0784440c1e8030b40e40c800e503440320a110701c1c02450966600307941c06000f48102c058080d403e100703c1850215640c0c2003049044010450f620341e4821030746050b0059844803801607032061700c42e540e0b5100d4685140c00c05481241e22855034603800d45659a40d224441c0b00c1c038080d06680d505a0300500001d081c508003d03018108041c01001046e251a07004416a5009140240000b880e101d0100540741051900c04410b8010350810502c20034100700c90308241242e501424003041120750b91020404211010320007800800c0341401900314500d041191201c0080c006040824103070070750383da01401c4a00c208011a072002c01e50203540010f0703a09114106d00040020000c5141c2030602d8001104414000d00c400940fa445140c0c55884003028090301486040c104560f4402980300c050140240501c0d0144103002d04049100068a1524100342004c0101c050b009900d00100c1d0442280903002080c0742240c03640d21520300140c41e80300d28078182c00c100c04101000700e249074a00086415500901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 898990863 1250 898989613 898989643
    0xb01021e011a011103030708060a090f0b12011e0b0114031612150b0c011104080718021e07050a150209040509012003041b0b0a080f0106050324060c0f 66
    0x100c200864000000c01c1b0390700204d90b414080c1c40759845400140c003241560300800380d6542007a01f00300d0503485a0300504400b15089400040b0003901c6442c5508036107245101030a1203000300c12030035140240b54400c001ca0001031600ca5406003002d0318054a9500030740d124054100003141d2114581ea0000b40700881d035400c00c4082c00024641e42d4001c1c803c580e1030103000400000040c02d1920700380d096000406030300f140000c0c1a20b8aa40d50019922102c1e17510034400c82180407800100324640501c21140a484001c204132001c10f14042c0440e180d8000440c101c44a104190009012074444161003101301081100035944548a0081c40305542000d01045060b80c10084c08203903a640303504200d56421951406180c59580714100403d18003210101d801d50701c92103500c08110044400010041d00400c0e4540d21116103d4800f4240440c50911980c0c2c0010700610100c0d40580400401c0c00d4022804101c00d0000d0f442280000d00950050040c040590320020201619407028410002c07042101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 898992113 1250 898990863 898990877
    0x30c01110a1709071a120709032913151109120109020f120313060801053d14030f01030605221209080d110115180b01021e011a01 57
    0x300e140a507294003a00503170181e50500c016808042801e0000d0310020341d00e003402c540351410003c0011348190302d6400141e40c4400d03000200601c111191101030580410400200c40c255284425090f0076981140e007180c0030001030104000284640c05151000003000803001d0366011128100001420940b4000c880c13a414150214090703a5240401102c901040e14a008080d01d03540c000c5065120751540045a500c01860200e10365901c1a01d4038142c480982e0100211503201480e8000c0b071001180e0300303444040d0759480194501c0d544c810141030030038900f03102c450f0703128940c1500346580044072050950190140104140113403401041d070400c8181ca190740348620304c0c00c030386400102c00d003034040d1807075030381d069101081841440b0a02c01402440300f9950b1003c56290010103007100c02454000960038030340101d46803402001500201c0304541661a600130350f000480c0058280300c1c14090641c0200c00a00c00d064079070603803501c000c80012000181d012a04240300c04c4071440803403035504002c28 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 898993363 1250 898992113 898992121
    0x15021c211e0b03030906070f0c0303030221150d03020120090406050609100c0f060e010c08090601121b0f0807080709060b030a150510020109031407050d11030c01110a17 74
    0x8000c5a060384405e41b1000d5549040d030a20f5145210b10315001805850895400820315501d03a0240c40c01e41c0c10341654079500c60080d040c000301c085080e2142d9602c103070640c0d081680c5203400c14116131003601c81d00021511f0303400c1d13400d901c0040c0303e02c0702c03001c561030400542c008207450903205580180c03a003111424146042d41021548590b140b48401d02445001c10780e103000c0c00f03480040840c05603803106050007040d0500c80d00e035001c0d0000d0321968011400040200781c502c64042409416201c1c01060b40081c5100f5450b2140c1b4950700e0070b10102c2d001100c00004c0b8031108401c1c182005441080c00410060307103000001494014a5804200a18601281801640c004070200ca400a00a41000c80c91103010444400b41405640c0441c1e441711140d0161007500390190030249500e4007a03101c0da0080700142801084500c50140010315503008040c142c40403d00485640e0316514414080380c4c10400740040c03030b40c00c40e1740d0840c20302c04900002c140d03a60865442403640041205000d003080c1c00d420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 898994613 1250 898993363 898993369
    0x62a01020f0a08040c180b01030b04091509230f0d090e01032a030308060f3a0b0a06150309030c080a260f0115021c211e0b 54
    0x144002c03103010004002d02140900050240f40c00142140d20382e01940307a0701803000310000b040303801d51040c013203400c0c40003c000c075181c01d126030240c280c0c001d16605803002c100101c000050a0444d42207590142c016005201c0700e40c0c00c600d450305001000018100c002410440d140703400f003201c41540400050010034404629201581e9046035404860303400e40c00119048045e0b4050a84003035070316001e00820010600d1f501101c02405403005603030f2559800e030818203102190007107030542462031044900340e81c12000c07010b00b610040d801c81072100032003031200c0d0341d1903e04400a4a4400c6890340f1003c042c04501c0c0f00300031820305075031a03042c2001658416034014054040c8540c003d0808800858110804c50086000d8120392039100d5815082d000700f96003103d10000150750001c0805214000460f07072104a5000006408079900203040c0d00c906505c200413003120b10507207441088600440c1e040005a02069801c502c910114080307028908080c00e42e10107000500000c0710542882100c8140362 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 898995863 1250 898994613 898994617
    0x81207021513022e030b0a090c14030a06271d06060d030e04090606030507050901030c090507020316140d0504180b040e0f0f070b07080307050d0b062a01020f 69
    0x640c15031300c51040090110070300071801c111654090390200001c01d034000c00c0e5031603400301c1103408044480746001a02c5801100c202c0d690b800e11240820380109030495441150000380d43e010001a01c00f064890b200d0f060500c2031044c42255107800f0240c4004200c00000a000303540400c03008030300031045e241c00310100d143c2d00c3c0703400740c0a140200200b1144409040c030806861400d4030014000740100f1501c0e24010700103110700d00c801e40c0c2e14040d070000400d86182081c0074504036600715400140090401076184014080900b002003544001c22a4900200601105540301c5000f02a4412170b00c1e203400c201818005459404d500f0040200400d00c0104604100c103608049074040025206c10f501022034001c0c0141c05000d089445548201540399400048510140c25010151140e0580e9100791040c0c0d401054801011450184005508244100d003e42078500040101096140c00d140c0440c1031030307028200024404201a811000f5022100e10020350a40404003c5203401900c12280003d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 898997113 1250 898995863 898995901
    0x708011a03040f0c0806151f020c1516060e10050712090302010b0a03121701050d03030b0627040c050313061e060803041404090203060406180812070215 67
    0x70f0443c43d0805414803024031141400790034a44115480c500304054054500c8607649074051003505010504901e0501d00d520040c0e0300740d515002032481c82032103400c00010044000c2d00e866040010311502d86200780300e940c079810300c5019050001d5402540001c150910005103841440da80c180010310040310f078001807010b943c5002e00c074002071851081c80c04030301401c03408001c50b80c0318009500200a120624030700b04d003011142c0c0c9034501403c0201c03045510000013441340700c0e4030116091316400464000e400c01d4003c01d0008041500e403a9401910303641c030171180e9805440c04447c103006c04925080910903140d0101c11801c0c0282180b4000c404401d01d02c13500e9500803c6103071100700000301403000541c50420000710340703010320605480c0c00383c06a80360090b1003882c0c1aa01441c0315a61181000d1040101a40e0003038017410b82c40c1c5d40ca032280009481000c100d01148a01792011070b01107420200075220085084154400c14144480000c0c40d01c074102a4840c1701c0707005102072013004c41407600c106070340d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 898998363 1250 898997113 898997123
    0x140a080103080c01020c01020403080c01150806131e03020f010b01030212013b09010c0e0d030e1c051b090105060414030c0a0329090304050f0406030206120708011a0304 74
    0xf951206007a8940a4042c4680e178081640c0003280c0030042160620203020221a490000c01107001149881910b0708458400d107000764104c1d01c046810021030140030500030740208070000d091080600c0a100a01c0122800c0d1700680112a883c00256428003c103e0034034001d2130154100f40e81d002020032801030621030107018024503eaa2a01c00500c2d50b100207050001410101c2d840100c02503251a25a0444024a03254079004c5150061801100962402500502401107003203540e41c0c2a0b49106030b80204541c4000b4644528082c001484031a90119100f01d014181c01c090002c10007071101c1e0014143c0b0700c210040070041c0029118002a0f9048842d50b03078441c09050031160100b03003030403480965150031441c034800c00f1041c0902c0301c04001e01820b8221840c1ca50300040c1c80340e005080402d8070542010b8200300010021843c00c20309100410034020310010f41d0350350325400580d4517408242e2541c072120840007044001508150311a0041440480e0415504100c10403d41103100040000740 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 898999613 1250 898998363 898998367
    0x902211608100902031c111009170c0c06030703090c0e0732120103030f020d080105041d01020301060807020d051303030503070315030506061207080c01081e0a020a140a08010308 78
    0x401c4d5981000102201d8000303140c0d20050820000c070090080c00c08810720107041c81070709621a04030842e442041070164010241c038080325a481c0410b1066402441d09107003522880d42c41c00942c1d40c81c07900460066116403030014044a051a000581020b41d5200801c01c80e90301c420014090341003042c000c03840c508941c110390b0082509260300c4c101e407041a002051200003145400011460f80d03132107410389000381c40f050185003c4440480c2e51300070503034041d00000e165038010003c0381040c1e00300e08450201c288003001d80000340c0040303508a030001d07880b400000c0c110400f030140468060105451440152070018501500c5c200c90115041440c4130050400c84008006050140f007680200003d02c0c2c0c072240145400d5423070610665502065601510560901a082e0b10100c400500d02d411161f03100d024141120741c55005441c0182c0c01072001d0005000703108540e052580e03221440d4494420070300e0062300d03a0101c541c0144600d244190254100c9010404c1c018170a80010700d440c11642d01445050b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 899000863 1250 898999613 898999631
    0x80405071206020a1d0d0209070c0203060406021308061003110f060c0f0706091d040302011506091e0b09100509060409020301030b06041401120303090221160810 71
    0xe203465415441018150800c48650041000c15001015070084940c0c81c00c555605400805c926003080c1002e09500000000c101401420510750040d4402020300741a42c400c0c0d0321f43c02090a00400b16801c684059001441c443c441010000100c081c02031940201031504e80b041020359016082c0c08080c0440c143c0600c4a00da40d40c03090000b01901401030300c280c0d2511300d4031118554520343e103c10080c05010b0202e021503800d100b06048000c0310340210440210a03900c0c51540360014001d00103908554035845c00501c07810200019000509450f9a2040400d14003180390b40e60000c5217072403510b4002c2d030a07010400412140306541d400c074801c440e80c400c281c00c0c0d15400e492911030600110b80001c40420001842081c0358080c5048901030024204280c0c1d81c0b03010030040f1130030001b655900d041b8407001400390f44010074801042032703c20304001034880c41c0c0c0d400180000d201c0940001d880702d98001d40580f161400d0140724190844e00001894460400d20720640300c12120b40d17407055a0746d0760030500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 899002113 1250 899000863 899000873
    0x150f02100203130807050d0801050906130b06160f0b06011b0b060a05030706051213030c15020d051005040b1207150306030c0909020a0e010302030d0e18090609160305030a0804 77
    0x4494544d610110f801d0766100307280f40c07064030b65000388030340d44c0841c01c104000681c0381000d829041c843c0000500c10a000d41a2101090082402804d40354102006100401981c0080009400c8072801489082000909407401054040c0014000e50400040740824130b1444169189912207640c8840304640650b2a080031450850b882d610041d8188601e1704001031742500200107024004041c003004c440e039030f120400d110000d4018500100068242d140510204e1814800070412580031a40549000c0e90301c100740742a00c0090300c55100080440004000501d014070071889060400e0b28101005e20049401a4648117a031007000d101405601461060724400d91069001d90b0303210300c0c1151000e40303034828a00240340f41c4808034040c1da043c0d0000308107040c04035107060403203034020028003284000b03120488903041c102401d1a00031144140400c0b8210307440c504c040c03048143c03400038103043c03906000003454000364814144242641c010b06001041c408000c540d1105160304111a00b5100c61603c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 899003363 1250 899002113 899002141
    0x120c340311030109050d030509012d110f070b15010c02090103060b0d1b0602120301150f030603051005040303110a02100b03240105031b24040b13150f02100203 70
    0x100405d940a0f40034090402e035010340c000c90240c00814001c0003003c000003140c03200e485481c1c1d000784d845422112090002c1d002d0350462004082c4900c00142000784040710b5120301e800505e0200d41d402410400c1080c080c542c8407401070741c14002d01e071402000d81c064001c207002c2c21041c040a4982038442c9903500c0b0a842d1402c03185c0d80349500884444040b10752900481c48a01140601b00040c010314540340c11244000090701e040e2085106040f1a0100c010700503910201000d1003007051503111b40d000004104244101892203d0004022416286c5031500500303c40c0c0c0e40f5a0b506005105026600c08030368005214025280c5a0b000050108020380020b807a1070400000100c5141c202d40c2c189000707a80c003d10300f504030783c426011104200c1090300b08807000341c00580d05a4006140030136200403d010701b100c1a144843d10840c15181070740b5410007800c5544491a59600564001001c0000c00c0315140800021489450648034070401d804009407240406001400c0503900400450f48020384291 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 899004613 1250 899003363 899003381
    0x40b130807113c060309060a090c090c020c01030c020f0304060c11030a0326041e0f05030c01020a11010209242506141b0705120c3403110301 62
    0x400b0000042d06a03040309038103040360745100e40f11650280c442d0a041c903d00b564054201000a0806581c030818420000c001e03c86040d202200d090b800040c0119952007803500c055100c1e40034251240c4c2d00740015045c1c0b4500005481107502440c1600b078542e2010083d6015103849242122140e181814124080e0385481c05440c2c0c180075400780340c001c05410981100302d192185c10700047e42d289414034048400c1040350050054018140350003424010007680581051180060107814440364032079130300d1034211010313000c61690f0014852000607081064250b00000d40002035150004000100e407604d0070020721a18055800c10b400c11100100c0c5003070b0344142d0710980341400401030019000018a29180d019101186130000c440486841e01c8900d030310a030701250510880c0301d03103229074480360b9003c40c0702a680c81c0500242202401082c20081c101c03140044014413031266040c01c10102a0a000d40d000e041798031030b62503120010181c10805003126006603007180c1c90241400400e025000840e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 899005863 1250 899004613 899004649
    0x905010f120204090c05191110090201021c02010c1704080a0e06190302120609240a030b0903030103140f10020f0702041e050610050d0509011401090203040b13080711 73
    0x420305c00003960000c080c004403e02007801c034803503203040402a00c028880c1115030302c2c0c0d900710000b840707011911a0049640b5a2061048030141071282c88100070000865100c7d40050b51500c03c0070f46019445007043d0300c4000d0011180351681000c1c0d90b005110b1144180400521040e500f500100b960340d001034902e8440340d140c00400500140c01c006000750300c00024001c1500000c4041051410b003150030034440d00d10ba00701c0c40355402242c15071308a41068405241d07403041c1c140070040001841b80300690f000d0384803000199203a50440c40d2011180c4e0ba032061a41c102e601010443c518584e00040e41c21105030710b2500143e9030825144101c00030300c100e0704040e41007824868901c584055540c0c000003130b07041c0e0b1b140402c01900e42804000c9100c103001c1490000444c20b01585855030040c0c1e0000b6084203410000044c040c141c1007000c200c0d04000d82c40590040c2e070100c20002842007050380154018a848039a9881d4240342d03807111000c0c05001c201410a84c0340185010254850070b40b8410a03844d52 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 899007113 1250 899005863 899005871
    0x120303010f05011806083903180c03061501021203070f0201060503010b06182b06050a0501050a060807021513171218010603021305010509070905010f12020409 70
    0x2420200200007441d214a0380040d012408800c0e000c821181c2c080e064624507070f05d010007078442c41c4148140400703584005030449400b001100e10942012a0700740740c403550300d5001b41c891402a240f444085101640c049107900a117a00c4a0316036804601c6130303808010380001c1c15601d0061f1004030300d443c8408a00324410342e400424800b0701a04100d50291071880350f40284001c0d61200181030984898542e000d41112050000350071032100c0d102c08003d44407010348041c041504209003071515880903c141c010301c02e40c0e240d0601c00d00141e40222544201d00d00800e0201d5490800400c14403005440b8040401ca407140100c0c0c0d16a100b400088503020006101810f1070030314240c128407240e1407200880c0e0129040d40d040b540000011305648805044962010013a03440e040481c01d41a103078014140340e9540c5040200041c0d580031121504041f00f241e000409604110620400404c0a425a004d1182c804010002c13a0ba1000e11a0211000c0f0326061441c00c440b02460f1000c2d0007950010604c0c2d90038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 899008363 1250 899007113 899007119
    0x10b0f0c01150311010c0c151803080301031e02030a03050304050109020306151011030306010c0212010204120204060503010513020609190b0a03060b040b161e050601030c090b010e090612030301 85
    0x4001c00c42e041c1c9026030a41284001e40c1c3d0015039a04101300e5000b0f040a014000408c5101c805602e00c1155030100e08007801d01150745080260700071300c0c0390030480d451b15011006000f0700150b508125521480c0d20002c03c1c0c601c185070002640c4480940c401001c10400200003010408290001c4503001d03806000c9907482d04200f03c0040c0c41150b0000e02328000d1141000181d1ba0030b205141c144410318030355018603d141c8071a001115021002e40c1c0581c0c0180c0d49000c045600c180902c02400100404c0c0103005d034800a40c4100016110194040c1e4400d0707041c02c2c03d00c21501d6034240c8284082d54112030141d5101c90040100e4421035422048803501c1d581841c000803048040b000500703143c1a103540c1042181c0e15401c0341289806103004440c0a00410710608441d1100e041d810001640a88006592039030000309200c00069212802c59603500072400400c20080c50b0010b58020b409602d10910843c0854400204401a4084024851031944002c5103260b1a8079400078150303044181900c3c1d43c4c0da1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 899009613 1250 899008363 899008391
    0x3062a0c1510031208090c030d0c02060a021e01051006080603060a200f090a080109031e02071206020909070f14090a05030105041a07090506040306021e04060306032306010b0f0c01 79
    0x5c81101c03070b064039000c0d4012081750341c030b40895406425901c40d03c45a03150300860b024000260802d40c96481548140080840b5011b810741e09102024003003000403a06150035022402e51510b2540b0103000e000240083c451240d6020840b40c2e4844440c240004441c10481100c40220000ca003051a1001000407080802e03801d510081c0030199003074070f146031242d1351b41c0300140c01c0300c0007400042c3c001404c0318507007540b450858030b2100c081000c0e441269011a1a05610041000c03401c0c4100d40725507002903a409241000c41c402d0f5408a0300e4184aa140c400b002c801030419600c0c0140456034090010718039404e03554200d0401301922001d40200b0051800d4034281015800d08210a461510100005959a0301c1086072009607034014140034140351456503100040c1d045070021001785110382c108a82840302c01e40c00b52000b440d81380e81c00b007551490740c100000807003440c0070800103042c41c5404c1d038803140000140300c034115900340207490b6946980d1404c695450007003801d0103056500b0103a407408140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 899010863 1250 899009613 899009627
    0x17040f0b1f050d020603040f14061314010c02070b0c0f0102030c1e070302030a1b0f0b07090803160f030c06020c0d1202030601121a03062a0c15100312 66
    0x1c106644049640b1a41002452034075004000e5000004000050024400810041080d489105038113298007202e260f042c1010802c440c002086e0452030140c40034001007a14915a12038600001c000d07281b65180020f49654039401104151907000611825082c0104940352440d841e100086403a8240480070b0300c0e442d80710309105c0e40b00e000c00b43d000610541040c03040756030941e1300da00190300c1c200d060032060300c80b0890601c049203500b03a645001c1e0003084c0390400c0c4e10042841107200d00468600500b0162160400b43c2054031154028004504070500e07a00030941915000f000303010407113005180454505050b010010103160000c1180a4010400640604c1188083c0c5600c90580c0415404908a00048403001d00180313050b07201c1d5403196200c0d484903141601481da01042c2ca810040032a11700039040c0d44000c800c00547e035800460905c00007401f4034807031301c0010151034216000c4007103a89601211003280d1241460b03010800c0e20f070070350f2405802198441c1c18405c00042d5128003800701c5c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 899012113 1250 899010863 899010901
    0xf03090d0e1507020112180506060108100803091207210507050d030e190909080c060c121612060602031c0b03071a0f13080f0a0317040f0b 61
    0x308180e101240c0c1d0301d182c0b03900c00c0750202c9644140d0505114042d001180c43c070203044a0100c260b5540d4031080e10060191401c21001c60103140100a6401c10700300043c01030100410110280c0101c1e007003803100c402e010040301e4550500b210100400c4802c54045400c01540f03501003005d5032120561310a480000c9040075200e2070084090703c03842c1c1d5035002884000c200c030500042c0011841000b1601d1490034480c3c1c8207030184151005408071761200840011154503440c00e5070760080108414540301d0003003200c0d943c0316099010250600407805001d84c29a030b409030565001c11003082006500c41d110b040c00c084204001c50003030040c0d65503204003a40303d50006440e1591802031000521000002c0c0c00340c0b12079110040c0040401d03d2500300c42e210180600300d80c002105c0403c11511200600301030140500c801c1448051988034580103406d032411000340e041052940040c08003802003600308070014a454a801d140c0c07061036840780f1300810505a41480101400009d509001c0000e500010000b04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 899013363 1250 899012113 899012117
    0xf06080702010c05091507030903050303011d1b16170409240302030c01210e010c1d010807030b010e130c020d02010213120c23040c11060106140f03090d 67
    0x220443c914001c071121310400c9001604000c5052120700b07814100703401070000c14001e2800c10700701a140c0c0e0307403d0304640c001e0b80241041410800c29940c000b01c03112010303800c80c440c000d24480281200441034014014842d01c1900700008036844c5044c0642c0d40e2548601007945a607040d0703101c0d2900c4001c00284022008032410310141c031a8008078100b094002026203400800900c141c031a0f100045800e071201100300c23208940e28401038013140000b8003842c4075450294001049510041708002c0c140d083d07407880c0002990710700b02c103072083c0e0740c06c42c6507590008954500803c2c040f480b000142d0b80c60901c0503a440d003019200505101e1015140d00c0244d20030345550a881c20031140c82d00484c03d03401404644a000c074940a401c000407108008001d501500c100ea908241d50740d075120021802c03640f0f008689110440c0400c882c1185414462407128043c0c60401c030501c010a10003035a59820305000321003d001d010f01c64001c004030300b0030070b4a0340440c20100040e0b61740303083c62880707440e10281703030404c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 899014613 1250 899013363 899013371
    0x20d14010f15080f0616110a050706080f07050319060b0c0a11150d020a030e030f0c010501060801030f060c031e06080609030f0a080c1e07020f03070b0f070c0f0608070201 75
    0x9041da408202d104e82c8404e014020211521443c55100903154609076500c14407151800111500b0310601c0741144042c003420203082d6552070400050b054060040c940c1c1440c0685404000c030854028007900c0c3c21101c2d18110001c2085800c07028402030031103411515581d880400c40300000000094601c50041c8a00d00c0411441082c0040c0680a00301d1150108191414070200b121002c3c2c82d07028020704001850046086081c03602500c0c2150700c41d5841d4051040c000441d407810034403d000d020f00500716403070031201561561301c6080e2840301c100c2c1c0061149490b01c8070146014807a81084c8094030b035045480d01d481c109030a161004150610a0034141d000d91000500c40c924044290394000c0d035001c514925003407401008886040c07005000001c660003c1c01210008809000c004100103210040541c0da9111801080051904900e04501c02c0d0b1100703100388071401c401001e8468aa240044290b107030301c03451520031080708443d080790308003000f41180041d41c503511841490240001c0e4000300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 899015863 1250 899014613 899014619
    0x15030f080c0c0103020328090803010807090e120d0e120408010b010207050916081306020a05030906064005090705100e010801050d02131b0f0504030f020d14010f15 72
    0x13406900080b2a0703854201c121340070759401e81000c2c031a00b89040d41314030b000145400c2540c2d90b841441c0c100382c11840035075101c030801307203c2c00010344a00352019200c1c0005140c10180380b864048540b182528000480784c451804e520400005c100c4c40135880348a150f01d98a40340c4980c81a030003040440c0820f401442010070004080c2042a2814000c1c0601340c1607031890380883c001601c00300d5005c0c103185201d1100200150101d2081d101400701540c02d0b546c1c0e40e9403802c08448041c84c0602c090305980c490341c3d13000c501c07a000e2001da03d44071242071000311205220410b1180c402c111081e46000320000d0b00d05001c1006544d444c04682582a100c045418503400c600c000021503a1100001515000c1440700700180b001c0e19014028108441c4001d125207100c8002c6941041a501190100910413405001c1295030315002800d11003000b17468505107040500c0e649078100c01000c05130340640111707054000d10040c49100075001e591b0001c20402071044803602d4030894001c0001008a200d100109030004c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 899017113 1250 899015863 899015867
    0xd0f020f04090509030f070b0106030e163803040b0f10050409080918011505070c05040e0309100f03050105040b010c02040e100626150a15030f080c0c01 67
    0x198020311000c0304900d0500381441a400c00622024041540c0f9101c28000b46070314506840c01007105521401280d4525450030742d000d01580d800d8440c00c013150f04060b007603c030303000301c2d01003424210384124410111003400030310181400d182a090000b403220184500b225981504001103000b1441208254049c0d525502c0e80f940402d401ea480c9840b19030384200410640c0f4003600000b0207140145512890b040490b000200400342040e0202035124864004120889000c0741030350381c1a055040c4145410030710750314484010a94010300c1d00c0345130f031054040d40c4c0c100c0c108107403240000054080014075200306009400c01c004d0000e00d4001038108000442d040c24580201d50f42440c045c1c40b50102e501e456402c001c041d0850303a000100c6807090210580032035149004880c000c003d0b81051030003034061a8994070416640b4511420668800020100c00e036205014840c0c0c0404141c0c40014401c0c0c5032003241040e0882640050700421003000008240071f00d0f40c6c010f02c001c000110840c0c06200c400c1e001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 899018363 1250 899017113 899017117
    0x21030c071e030b100e0f07020705060307051b0c040c051201050103140402040c11070f0302010305060d122607051c0c081512010207080a09060809070306090321020d0f02 74
    0x1030444070750614608100207122400070341d400520352007004098a0310340d00380007031100041320301000d0501359505000e8400c0d0103202e850040d000558504d840c603d01070760301801511640180f400c20305458a440c003031401c014022418101002071007406800d14104c1d00400540240621031201c4102000001e503075070183c4100680442101080d805641d9542c082000514101c0c00c05018400d42c0900143c02e00300502c00500030f450100350005442d42180001012204001e08141c045c245115991000c540386401c00800c400062620312142545020840380310464201000750006509d01405021350300500580344020300e0303144501c24904120300707410a84141e10760f0400810144400709840504070140b4640480c8080c3c1303000740c000c500300216400ca82c01030740c040d100d030f08003c2012a8083d034801180d400600f501d01e000340a60822407107007034960078a80b01c020034482da1204e00e4030805024120180351901000da820000c291050703009000ba50045004408003032a10402c11403030640c92003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 899019613 1250 899018363 899018399
    0x20406090806011a180a030308011a12221a0f090a0309170a0b010e01061707120f06090e06040501060f060c0204020702060f0414131a010e21030c07 65
    0xc90301080c40000d0b11003115640300481c44060f1002c0301100c45c0c59a00c80a4030f0500462003170b50b46609a42c500944403450b0610305414405000041200004042007504810342202216074000d030244455482a8801310034900004c09030070101c0001003129003900c0301544a44250201c00d041ca544021166803603810100c401004500b810009008034084c2c0c1c0350317144c0041d00c503100b103d071081555240d01c1c00095091f40700c0303921614068010b12009500040482180710048028541400c008002601000b26209482c10f110340d00e072441d10304043c154115030018510751600f0071032010540003041d1030702c5040b281a180c66090210028842803040d92002c01c0702d2580c4d4442c0504010fa41c00c00c0301a62002000341da105c4000d1009102155000d0b0003040240071060412007404245020b01103a009004545240103250114809002d80f001001080007103003403800a27011b5800d100001c440c8409115044003908101c2da420040080001c003c11686101d1421111000c0e964180c050160007461 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 899020863 1250 899019613 899019629
    0xb0a0e0607110c040914010e010204050a1503110a0c03020f0d021504060905070f090e03040311010804021801081005090f19170a050405040b0405011a160203010c020102040609080601 80
    0x20010704402d1049405285a19841c0d00782e036079201d0305800040035540040c1054880c14100305030000c04c00001d21492401c10f60340c40082d810f00d031a160010310812140d203e000c41141400e0361104c5c0041c4664400300c00700c1c001000150b100c03500450010f24406a80e0300403000f610804c107080b40d081000040340e0f60032030150f41c0107101e081c0081c007481822403800b070b00890340151a00514800154103000e104041e0801840b01e00c0c4403403030b03d0004004d84d800f80400c848070303400030072050000ca800340c070300190188001e007050421500d840c4003042d00d409601903401e000040000010804000102d4010310142183d002484103880303200e5915101d200c01e0408607000d40c89807a110840c000c0117000f1426a42c02014895455440340f8080b003c1640503018110002d04002018003040c80c0a00c540c0b000e18030143c03801c00941d13040107640c0c8440302e00c104da035500013080441d46144403591004030005065000e4001d214041d10842d019020350002d010380b001003194142c003c41c41c40b6001402c10304a400329 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 899022113 1250 899020863 899020873
    0x105130c0b0d15030317070507031209020105090d120e040e0601090c0203130b03040303050901050712020d0b0406030803270a02010f030e030a17070f120f02041701090b0a0e 76
    0x4204415440d500551060b800c0079226000300030700c02c0f41645542c00840c040c1d15242e00100002c005004c4290004081c5810b001c8140451404203610020b1150054414603001441c00564001a200c90083d02501035200394084941c1003000b9408035880080b06a030f031540c980c8071101208200558180d00150421640248010030a101483e0800c0b40c824005006480c41c110001105004031034444d0458180910300000b4402050b91622405031700040c3c0300001c0140303040289000b881010f503450700ea5090b5402040b824503500d42c0782d20030711b072602000b4403c010310b40e03403842c1c070489035007045801c000b80a800c407052094441800041c41440c000c0302019204000f8030798010340300103010380d012504065403000082007407402040241000070560b00e034111448604240c0300c5109e080181f030388040105640c0802142c03a0811031400744079101035070105d41d800c58503038200003d000307550260001c841c0b00a40f030442d008040d403060351001d00800b00300f1601d95a1914110503184d9662254400da401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 899023363 1250 899022113 899022119
    0x5010b0316140910080a050606100516020f0126150108010312050c011b0216050307050a06051b07062106060e0d03210209030114101703041a0c0105130c 67
    0x205440c0300d07520413813a00281c403032503803650f803000d103070068919040b603e0b6803090041c00814645000780c80314242c40b0f03140c1a860041c0b458014a01406844d100a000d2807400d0002d8000b03030300480548400003281c0c2c60b00d160261004809420380340c002c1e40c00310b110340545540270205512980d80c1340d05998202e6141c800300c00301c1c1441200c0581c403007030794607005559410300d42084121070300c154a8440300c40e41c014513506031842d10804541002c0e034012442030703100000420542e22207826003411504035003010b54503501c11580d20700e00c81022900000084c050341d04085540c5402012045541083c170001140c00710100c0c2c0c04001f161030500900004c190681901c0f0424030340750642c10a683c0c4a0702e84900000a403508400105000b451410100c5802090010740c505091098000c4081d105040302c8160810b0159010b064445025a044181c072900d1040480e14003003080364000c004a0502045102c40c444000c100364001d8030380c2038102d500b1b02004c01e090b402c02c0301003400e40365040f0522842142ca = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 899024613 1250 899023363 899023369
    0xc090801090308190209310905100207150e03040e010e01052b051b0f01030212070309033c030915050615030a05090f0f1902060d050405010b031614 65
    0x20700c0c00f44420101d40800c410030150301d400c08003607c03802c2c07108806c100078043c0e0f564125200c620074215424191500b078a02000c1880041e140d40f89103001900140d9500140c100582447d80c1400703483d000c681080c55a95440740004000c00807036180348401c1c600c0743d0702d407285424020801e102d040e40c0030790b4440388194400225510501403001323702d84005501c005980700d60429504940d404442d031608805054282809110006809801d1070114a40044524003420102010b0058010141d440c51040c0425015054074007100c0d209070161100a04904400c008420300b4854030128000500c02c1d10351510301034000d40c540150701030701001c0e0080640b500900186002071a0962021900d030b85500d015031054020f5004144004021910340303490080b076882d260600c1079900040e40003909180034020041400c40749184900d1a0405103207075030000410600074150140032680c545010300c02006015031215625810076070566118002342c42543d01c03020f85900ca5041d6181c648400008146 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 899025863 1250 899024613 899024641
    0xe0a0f05090f01290d0c0e190509010e1806010b0304061d0a020d03231305060307080a05070e040525092303010207050a050313050a03021020060a0c090801090308 71
    0xc00464442c03810844984601d100b07980e924922030002c1941c2047e406c0c842c8c28000350302281941010700d0054400e01d0302c800324204000504c5000003806140c0302040390051040140590303084500112509940c407244041115401684d0494800c1d1800301c20b202e501440300c0002e201d050101001e000302c241d031074080c04030076100c1c07120880030044090740c1d0820070b030722130300708403000c42ca099201c0340e110a50361881c0c20081ea03494010a21920042c0100700903680c2c080d03c100e5020143c1280854203071507446d0700351070446091401590141c00d2034100055480c42401c10050740800a0403e410074000d0203060307c0284075401038400414080a024003110301800d0100c1c1d0351003000d000180340029079142d55042c5140d100e01103942c0d40001032080350804c080001e00024210846450b1030852960b0300181c49404d140310410203201003200b04554a110481d078800500f4078070800d60311306290404440006104400351180410010400803406401c1482080c07805649615040c10607140d507080230a9038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 899027113 1250 899025863 899025929
    0x30310080a0f29011805090115060c0503090406030b0a0b01090e06060a020a1403030103120201111206240406030612020f1507080f090a06030e0c100e0a0f05090f01 72
    0x200c0c40000c600b00c100d600d48150a4005c25a85091442c4685005261303415a8005040048545c1c103045800c09140d02c4180c0150440701c060410000454041c5003480c11400307820a5a9030007480c02d10004148440841d04900c20145904104000790072540151000c0ca202d0107400540401400010301d503041c5100180415071050040341c28a040e01d40d01c1119604050700d0b2401c40741c10200c01081001103406402541100500080c0301c14400390750030311600e008038154030f48456100004940661200c00c10100080545440000c800750110ba00360015400752084034000703403030a080002d0100e100d1483d5800664001c040d100f80c80500810084035100010761140c0701801000244000b400c031000604d03031030080d04040350725222144104140e0501340e900041c1410b0500c4011a41710030045216403070a4402c40740003685401c4d05900300c031103014015a044c1c008840b01c00c04110600c1140c00c0e00d044944c110f40e100c1d566078440d54a4008035074284100703041541d65010001084440407110004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 899028363 1250 899027113 899027153
    0x60106140c031902010516080406050c09190608150609100e09131205040509180708150105030d0c08070303050c070b13030809062a12010602030310080a0f 68
    0x4041c161001d190565000c1510011812604090b111810ba0203010741a80180784c150a002c110189046c0a01148401800204a155524001800c0320724540580d001c184c1d0140103550310066007501c40b0f8100900d40a040082051031780000c3c844c414400f101440504041e2026007808200303010721240180103402a014401c4946181486403190b40e1141c0c410011038196841628050030001b0980003600f54220420104200038030298845041d11a00042401504009050810b00c00c60902d1b0070f0303812402c074901641035600c040e020921085d0b8140e9038110182c0d400504030481c10786d451100d150000f00780c2c0c41c0c00d014107000b09000b0f600c500d51040e140b151040c5025082d1b035a030030b181d000c01c8414501300c3d00c03c4030514081c540e001c00140ea01c0100b810003423003141800e42d000704802c1e009401ca207030b003e610111003080b609640340540e45c41990300900807070035503100e1401a450760400c039001008103a0f68000003400c4640003c1d0240440d402072003c4400003900c3c1c880500c10099000001c107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 899029613 1250 899028363 899028367
    0x50d02070f0501111e0307080402010e0406050310060e1609120c05060d0c110d1209020a0807030c151706061b070b03090d2a0323031602010c0206010614 67
    0x450402c0c01000e8000000c0814150388618031044040c0303217000c480d400201042d0134420030030781c590030076546030f000b540901f4100b9500700c0d001e00103800b40065420098043c00743e00103540403442686c00c10415a44c40110038441c540d1061003031800007026000300400200d074030000b003107000c07003140b490f006507801a05201e250f251140c0220714107921600f078901c04c190765020149111940705da140c0400301820009000004c9a046000f00240852a030282c44c042d1303101d000f40c5c119941c018075900200384c00410f45007125544c1c104a086004240b2849417140d00d20140501010b100d040344944038514003400341c0d00d9494071024804a50071403100d6a00e821803d00c8140d50710a0100400310080c550f0010080ea207150414a1034240400700304550188100342a03011075900e9185204030307003400c002c09001c4010b800b0782800c40e1510007099500c1a5820140c0c48588900720301c000551103a0a003c3d1501d1003000741d004101e0803a10a00c80703030401a00408018084d07184100c0501f1860010424044c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 899030863 1250 899029613 899029643
    0x3030503090304240806010804030914061209010609202b02130315060f0504050402061201080c090c040303120b19060206011a0a09030305090d0c0b13080d050d0207 72
    0xc0b0344103038103203900342014071030781c1c801301d4020340c840d049507485803080c80c0450840c20f1654014214040500401460f00f80d424402c02140c1c40e102c0503078030540c15401c203052031810010318050092400b07008820005013048030b80340c882c00c00e0907262240084920b02c168075040d110040401c0c5410443d02885040b81d500188580c09000c80c0013400301440b051520004407840c614001e481c0b210a0318a2200103424003008001c0001011802002c5440555003c00c00741c0c0d645c400910707070307100f2020700c6e0840c44015000442c40720000940407140c000113442513106601c50f0200450203000d6480004d00146d0b081c400340300729080c1e0b90450052400040d00c40f8a8800404040c0311503025950081401a80648010088040f0340d85001c0d084944140855190046190005081c103038140005800c1c040c0008040c0702e01d0721691100300103543c000030480351b803d0301c4a40d00e80320340d440300c150307514460311204000c241040e000c41d04890115054031407524010343c800c40340019402491043c0c5440036640242 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 899032113 1250 899030863 899030879
    0x3050f2418070e1504050d0807170d11120103031d0301050a020c07090905030708070c050a06260925030b01080106180b01211e1d0c030703030503090304 67
    0x40d48a50348040d002031072624004100800003c0003000d040c3c0f003540021400e0104001d104200c0341070700c0c070a13030701801c5141c1e40b400c014071103210b0910020709642c00c1040e54400c5a10b0440900002e840e083d5060112600c0840520481d0140d100440c1c80003038200d0040001030300a085e041120034000429010054558001908458007200e01c00d40f0300e80c0000380306040000c00d10215003c1e086103141002172541d1512484d03030364000e00310024002d6900140721005d20500382e044c0d2000701401082510305580325680142030010400f07035510131500341601050b080f5640c4408501c6080108000c1601002c181c22840b004c20400e9145000e40640d9840403004c178042006041c081d00900001003642468109034200c90032296a071218818a04401c20100780ea0001c0c500c0d5410310703c5011f60707286a0120081c10010807a00a0342030b144a035a1914a10818640d049400900c141011035004c40c0c002c0300b0066242c40c21800803560540000409000180c003810107150000c10000841c1e080030f8136200c071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 899033363 1250 899032113 899032129
    0x3030504260d050c0706140703050318070807091a0906040b0609030114060319080a0f0e12011a030304140d0c1a040302031b010203091203160f050d03050f24 69
    0xb0401c00035000144012108100704240001007001e4a82002800941d1320400741070b0148500050421000001060b485004485c01e00c0c140c40f11541035840461b621131109545d07c909101e03007040f0600740b8400b80c20207841040c8000301ca50000c0d10a20035070340c0310000c0200505444401940c01401440f002c08251000d1003281e401e021008441d80c0c907410b10f10101032600c02d0b040e1040c0107103403088000c80b001030307814401e03180200039900708010820154881a15500301c6440d04640054502140208074041500548000f0320321803007012101101c3c01c00d06880c1d10441c000d40d00c485003800c8034900c15090824111044a000d1303e800c400c01500d41140014040401004070ba1285c0081020b005618080c00700c030701c1400c0c48144100092440704000b03502ca001d04c40c6500e11a140d819007040f607000c414411940c2d0340100b0301c1500340001640c41c009210300c0d2070a100342e92a12403c07a10a207458024030a150240d40d84888424181d500c0803d4403124403480034060305075407884190280c6607296004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 899034613 1250 899033363 899033383
    0x15070201110d150509091c090b0a080a06050a121e06050c040e0c071a040f05010c051b0a03140f0c1f0e060105012c1011060c040303050426 61
    0xd000c41c0d02c0301c403030326070552100c01500020b1080105c030090091041002030302616814120080e9005e00040d0700302038a804030250312030303010801c0014a5004180c0d0003a8510300c038407d00f1404002941e101c41c140480c01d112800390340809a44802194081045070201d000c000309000c13807080303060f00c940d580d40b8282e40b42501d5444418034007250030700400000018055100e05400c2c82c050520480b5100c0550f4910b40340c0d00f80b500900e501c400310301401400d5580c03900c101e03003240090120307d00400c00100a50312081000f841c2e05840150280311800116029081c08c0d050f6507090500c2d0b203000c0e9600f6156218210440900104212000550006101700858040210380e41001c405540c02100c099130001000a04d1503005600103003e070381c0c4c2104407032903200001440d41003600b48141c0c4031100403000554040c0c0c80b41c9448880c146440e444600d061055010405640140d100c81e40f4a0556000f0740c040200814414402032259904c20140c81c581c0b000c0c01d8652020b0510094403541c10090110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 899035863 1250 899034613 899034637
    0xb0403030c020a090509061305030d060e061009080303391e070c0e090a050a11040c08010b070618080304060b150a1d220504050d0e01021507020111 65
    0x1907100a6240c2820b8040080100203c03d00c02c600d00440819101d41c402401520030801911900701070100c200f06441e0070b41101d0108010b415101c0281a2907802c08450b4540b0802c8000c81d00390303030340f4803e018407030031220300318011425504c0d01a2003401c00080a40074140c140b140012102035040f004c0702059035070512008d8141d40c0d1040c1c4500e075640e051142d03d40f1950b000e04000c0e00e400a298000042c00315050b100c0d60001640300e084086080200d0b05c94060a1403042402c40070a001c1c00111110a0341d404070340c00c21100f03c1e941029102c841091096070b2420300c05012420110701d80303401c02002c92070351024001d214081039560180d00d40003544c0c291036003a03940c0090342441c01c000000301c002c1100c1148880c24041c28900041030b4100e03480140401f281080e00e020a940c8078034400d0341d2206a00c0c60100392010040c0c1100004007402c8900751910712608010b8030b582402060444400361301a400b80050324a01f006c01a146007024060b00115035031492a490202d144c00c1c00352890700032079 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 899037113 1250 899035863 899035877
    0xf14060f060f0315190b0904050a06090e2821090f06030b04140c070602070f0605010803210601090303081f29090a18090203010c0c1e0203060c0f040b040303 69
    0x104203008203180011a4075103e0039172010284103030408182910341c0707158103c0e80410b035996000302070b42c0540380581c04070019030f04000d07401110010100c0c1d440ca100c03070324800ea0240d4000070300d41c6104540703080c0300103410856240050301741540310706815102003072a401e0407280300c0e99a000c24840210541e21480000703a403200c441c4441e2400380100700000c4c90340b0095030414100f2100d00c441c1881402802851254001510801c0190102c101c41c0e2145e00404100300039039580d18481d80300e92042c40100e900402d24110741641d0144010814094181030b5a40f0300442e0666030f050b610312001400b813420002000d880701c2148295020000c01910441c2d14101110820702c81c0c1038072203c0858a0400c0705201882040c1d150344440230b6800842e1041c0c1c244090400c0301d400d00c0c000800d10000081d4040d420070380c02c951802c0d0081c1048404a114500c0c10a0000e00040c04180038442040020340c035403c1400818881d03400c09001d050b0307548010105a190030340d07801004040c2d81c01a8011004141c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 899038363 1250 899037113 899037151
    0x21009050f1203160606090c0504030201110d051c020c0f100c050301080c010509010519081009140a02091216090605092a160507090f14060f060f03 65
    0xc4a90110710880098412080c42401c01007119128010503500c840d800300c42032000c00c1804003d4002c4c2000704807c0004202468901000a000354001e00041c3d000c1780031180003800300381c00001da000441480d95030781d50420490401c000030400b11902d643c40d040d5002e01c0340c02d5012a0900c4102c2c3e0035540c040041030740c1c8c3d640d501c0032001e4a9016001c03106000d010300042248100110f01491045d0b4246051039491441c840140d0b19801031540707220800c16000b1440307103115044a02c40340114610360400401c241d0354a01c0d0020b8440742a0140100100900484c4080c2c1c425009001d0805000f0b295840d004011000a468880c03904082d21400f02820010400000544a101c02402007500c0128031468000602c400807a2442c00c400000b8229503030921444024100b9502c0d102c0e81d802c1404106142810060b54651650103140a0701389440000c10b18908940b1810018810001d00701d8016a620810403008013860710546d0b81089007009100300907102240154400c400c1340d1680c00381450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 899039613 1250 899038363 899038369
    0xb030c09010507230f0f0c1216060504210f03140f160614070903030f030b120a031116090b0a0b07050a030206010506090a03120e040e010204092403081602100905 71
    0x45c000c0e00001d1500406c51661018001140c207000050041e103100c080304000485103454242079102814903400c02000110b000380d8028020300032944181044652002c06841c1d910101e4410740000341400c80c4d200e4000002400342410b0f40181c0e40c2c940d0200e060452140c5009040e43c4420716003e01594034043c0201005240d215885400c036081c0c4000c00e2918041002400f040d041e4040901440707242014545d810f84070f500031345200131010f003403007841030b480c0d0904680d2894030110840100304040d2034529035420005001210000c1302415040f81c80c50000803600030490000c400740c020716802c3c00410054600401001c280b4032400040c03902c002e0a040c0281442d10682100748601810070450b125640c82d80ea80070250707900f02c3d1110444622079072091307900168600c8159002410580c0307082c001c201c19400341c4200d814806c3c0a000c0c840c0d140e40244602d2030460262522500b04000c02d00105000030007520b00030041140b260301c0384074150001000c600100039180c000501840c0d090049007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 899040863 1250 899039613 899039623
    0xf02031f05090714060f091c030f0f08010b09010c0b1e0708010e060603060d12050c12091008060310060b0a1b211803080c06060105040b030c0901050723 67
    0x580204040c04007181020400885204e03800c00e1a8810280440c0500340c4072144400c803500c050004004101080d43c0703000e1005c011001c0740041e0003143c510107804002134010601183d43e050565940d21960b800d0810000e8160840000641001140810b4400255044202d240205455540901c080841c0c4070748026000b001490941041110001005110440701e00c00c4c1d0001421110340342ca0350741d00400300d03001c1d20300498003600f02c2c2c80601e56265080d0300800101141d082100a4503007003034040d80c05030f582d480b4000900f500310010030003030030340c852080908a4101c600101640c58204403080010309445151b0807005105600244900e002c0d0703084420780c003400100d1249002964590f0f114020701000300442001c075844524481694588140008421842d0312a440c84d030003501c074106454160007007070140708580b03d201c01140256000d0b406807811600c4401e4210302d950b9408140d00007039041100464140301080c00202c0014003c41261100d1082c0d215480b0003c1c074903010018645 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 899042113 1250 899040863 899040871
    0x182d010e0705031e07030602091f03050f0601020c090c0d20180108010506070b15030a0803010503011a03121c0f1e11070b1b0406020601030b0a02040e060d0f02031f05 73
    0xa10000c05110540c0480450175404980e003000005071100200e5001c24000c0700304046406180c26202d44030641c4a4040e4000c5000307c1c14000c0402d1a07a82d8000166542c92507015a42d92000c401000500d400c12284006c0030344142070000442c2d0a111818481004542080756020200000c1502d0914000c80011145280403d1038445140d508d0030300410268441c40c0005450a0240800100700c48692500d4005142e40902102c0c00b0b4004c0e424012410f41082c083e1603c01c1d403c0c02e00a49102c5500c0845811f01e82c0001e000e401e41c00d0002c40028066809040b20100507110041014000c1000c0e1280d07166100c0f00e550049215114101100754641c050000b2181e42490303c1c070314110b80b1301d444058a801a911406000d00743d2542d8032410181070342c0c1c204c0c51600c0380d40020049242603020807018103e070311410302121035490312a9040182c0c0100d020b01d091510f40f07500010600e1803d4212080c0d070501480308850400e003150046030414031000d0040000c0c8880e020001d07440183c40c4a41544 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 899043363 1250 899042113 899042143
    0xa23090a2009042102060c27090a06090605031212070e03031207030b0a061e0201021c2009090402041e050709170f0604030c020a090c080f182d010e070503 68
    0x9107190004407c0346502420404100e00304241214001584100100001c90400103081607018078150a0000c06407410f07001d00e1203d503040000004071810001125a250f50032811901d00f0030010011050145600911000400030308500220301030714180020b060314102450f01c41810314000c48064145c1c3c20000c010380c010040c01c031041000070351025440310103c0b0b40100c0490121200d05040707019000303100c442d48640c11701c007084c4100140507522640c400e1039881010303d030b059034040c45c4000c1800bc3d585d1950704071640c64001030051900341e102100080c0b1b6500c840ca29844a140c17001e0840700111401e00202d000201c003440807404000602c0c041d040b00c44024000300448000954032894007801c005c05100f002540c0e00700719990403042c61b0180c601c0070f4041240b100c03260390051440100351103080316440960f01241c01090300803100148004007034000c0103000303002d00041d8071440d0000c0d0302c112104210190103803510310a00034515000d903800010400303942080c0806041614030410211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 899044613 1250 899043363 899043373
    0x60e1f090f0203062d0405090f06010f0806100e011e03140708070807053f010b011d060909040602090a030303140a09050d05130e0a23090a2009042102 66
    0x85500d5018001c0e17030b404200f90b0380412152a0080020b00d49194082d065038640541030010404805c4600034000b12a40c8908851050b04e580c5507404600c82035018014ac01c0c03400768010320509401490b901e203400d08070701078004100d40d01c0c0c03110344c17566040080c1d50403990400301082110610030048035028080c1e040141c05400e1820001505103180e07070340e10840742d0100303265050001d40e81d110180151041c1c40c0c4403440303c0d40d004042c1c6000f012200b91441c00308146022030707070100c0c07a02c0e090802c0315007000e00440d103000103c10030041c84a000520440340103408200a100343e8840000d00750080d4403d442c0812200415094415040c0300103101142507494000305202123080082d04000c51099401e1142da5060012043d42c40c6045d41c0e00003603040c05c2c4c000288080610198440d400c015507541141c070035500391002c07140280c0c03819600902503510500e0b5000100701d800c55020001d01410901c01000c88610012071503202c0100c0e0203030b0744891048846000e605070030340301110f50030031407010706 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 899045863 1250 899044613 899044669
    0x60203061518040902040905030f040905090c0a0603051b0412050c0306040209011502210405120f0705210d02030c06070207050904080901020a06110405010e04060e1f090f020306 78
    0x304061902c0d198480d03610b40001c4410764075030b54001d0410a8201c019640e407001b054141174120341c814800c000350145840000f910420703009c907007460764040c010a489251460014202d0191101038101c0601304c1e5503400c41c1e6003136011800200000d06049601e02d43d01c215500705281046991151280682c00c40d50070040107035290380610f03064460904500300400d4001c84202d1424141e107200300340d0300d030050b44a007208052030006401104c0c1c04640d440390510030354802d99150711300000307640c0c07407a40281414801e510308007020b1846403225150b508020852015980d180400d4050000007603000090280c018807002c0c07002d154024070078001082e00b43d24020206245620050014100c80008110344210ba07100380546881d40f40c0120041c48907540910b0b0742e0001d0360051041c117000c01c01030040010b075810b1070300622045800b000440d02c9181d84a0031a00380e40d0400c0c40e2255103803105160041410403051280413664200ca01c40142c0700e16107142402a2000c0b0040c400a030b0281030700d444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 899047113 1250 899045863 899045887
    0x31201090f14060f09281a1212090d0203010204121a090309060f0c1506010e3a0f05150a11030402010311040f06180f0605040317160602030615 63
    0x16089449081d40c5c070160070350b1041c1a03550440ba5141c0d4044809000841c55115040c00d40c22000400355580c00c000c0b507940c80001046000c44012821403555000340107200c0c43d00084002500010b0708c05002180b1403c50350340000d08991140e04150429008000200c0910400703c0c19055003001040e0200c1345800c008078455600e000d8050724900c01d1074001004011005058151703041000d140e4115030003a2250300000342c2125048800c03a00144c0c0c0b182e0010058502005c25006a0110123503060604030204bc4040ca814940c0341d20f040248801b01a0b4400101c6176524070035550702a0010302225070b005204e4000284014208042e034508010300440140e0704076044a402c02d43c2401c000bd107006c903100001d910350060394032103256008583d400107181a00043e03d1001c03039044c4031000000315102d1040ca0810089800f0f0000043c40920040c4009003a5456000751040302404103814400d031586031041c143c01e00b40e01203440c0b0b0380100500c042c0d82032043c2800e8032505011003050501404c2c4e001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 899048363 1250 899047113 899047129
    0x1e0222030816050c0d11040b0103021801030b0d120504060f0201021e030a09140a050c040608120c030c030a05360d08160605091905120705031201090f1406 68
    0x2c41051849000d140c5000c22000700a4a80d444070080c0521030f0a0a090611400044080909600a908105014200358131074401c0712070248008800401c00d6035000c004500070518200183d40145c0d08107005400b08820f00301c40750161352961b032400e98460821324018090a0030901d10000e5a0061116450308119854452000b40c500c013104d507169a24840140c1c05048028800b90034034405004160503080c1c00b207111034900303001744100c406010340d8205010445020703200d030003256000400a80202c80c1d85034001d1100c0c80f410740440742070030000030f00c0b507085070301c40200328001c900e00007500300b50f03045200381e100c0c0307403504142c005141000d00480c04500c80c076940240600c5640c0e203108a07c00c0116410a031b0720f010041c00041401c00d15030b880c021004040589900c105486200801f210411444525000c1c4c42e500501601c49103c00c0b00340c00307000d600404811561740c00144040110004400201d9000308009840851420010240d29089405003010700b20340400440400805c0e8680c00340c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 899049613 1250 899048363 899048377
    0x2072109030b0621070618050307030620131802130e0601170f0403080c130e040201030f150302010f09051c030516111c0f020907031e02220308 63
    0x2081d011981d840000013480449456079a4181107460328403000c21200006980055031155140c0011941c0d40c0c402c480c100400e00c2c030a2641c507a202000a000080080e0090031071410420031904401402000390240c903080b40383c48030041d032084002000381da00503003010a00e41450541c02c500e0032049082c1d0298002450156410302001100401e1169200d800c40417610350150260342050f0820f032142039200d0a080d5070640011700c1c0c410201c4c010704400e40403201c1314074080650440140c030b440488114408020010307030615544102d241802034250062a03201b08031b041032283c1d464154030000d4840002c890040382001440c8905012540320f00c3d42102c0c0704000300c000e00c0d00050980ca03003142d00e889031080c0207404029034868142040144e81c24400c075941d00700c07001c242504411000308c43d02016242c01401d0700d0707024080003004d810010790300d0f9000140c52a0101d04498808a0050001900e000e4a00c41540c00101e1202d0141d0302c8044405d40008a1103501c0360918684800f00b19000d405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 899050863 1250 899049613 899049623
    0x310090b04030c02030f0102040801061a040b0307081906180c1107030209100b1c0f020a050a03021e031306060e0103020d080f04081209040506030c090a1505130207210903 75
    0x803e40300039580c040140c207000a11007070080d03588039100e08041d0b0280040e407207680d82c01441c41822004080d54601030300c040e0b60b07101c10a942980c1d00c290f012920300030b000c0e09000d200388080d000045a145240540d502401c141c551814140d03400c1511401214840a02ca90801c00c001400746048500170810b541240c0d01240c185034a910740c2d2030342505c4a515039110310009040000c044040d00601d0b00183c0301d040c0040d078104602c285d01301e1100b00307901c1b501c02c4103030000341d042101c609100e001341d0107840c4200301908a070800000030300d0b40501c958000e451500041d807800c9100d00400005010f000c002e003140c3e0b40000c03000e514580c04210310720007002c2d00800c011004100280c1e48485101614003c1c13001c00b040310303403035070340c200040456901c103501d41401181400009681b908001a0030b1004c038501401100c480c0e0740e00c0080780e0080044035126048802031074000103041d900d90b00341c18803a08200300c005a8034215803804441842d00e040207115034940b45551400b04075044102d40d41260b07005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 899052113 1250 899050863 899050877
    0x3020a1710170c03030304050d080a091205070303091b141f0e01022506110c010e011101020708030408030f070c030806061e030703050103050706031109060904060b070b060310090b0403 81
    0xb648060030141c850590542600c000300c200320a21500180403452014240c0320308001c0d403030703a06500081c0e4003404006402a260780400005c114031a10003840f009001c1e02e40026078080644c0c4d039000301e01100e00030f0344c2c01d00308501041c040ca000441550840c0c0b0301c100c072515800401640d210640c01d664420240a00c050614a001280d00070700c021080a401110340440d0384180c0c0c0c14048441046014a100090200d000b40488803000520804223400c16141d1080c0740807a04011240b5001e030700101310f1555004c2c48002d0008034244082d6020381c3c07241c20142d84a2a01e03404c001d810311002414072040119860801010a4009100702d4000106a540382c1c4e0f82c81804054400c415001c1e507d050854000204005a0581c10b5006a040c2c91041050700c080551721282182511012009440400d00400c501c119a2910304000c1000082c081c201181d0340380ea03960901c2c013503084a070341558651600c1080020034681070062a601c656551010002c0d030070700740c13507484445800500007010702c004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 899053363 1250 899052113 899052149
    0x30601050409030905100f120b0f240c01050912040b0a12090213090303240915170a03090519120f080a090f0e09030a210c03020a1710 59
    0x11402003d405400e014080d1b15003e900c68600070a5140400460f41c00208038101c900c1443e456170003041601d80000306400e407991040020031100c451903000f003100000040c903541e01c200c0c00c1d400180204010034000010180307440ba00d568140103002c0c0e40501a079200300400d01402e14a9010b4850300031061904441c02125541607000500a0510181d40305110007a0080c203440075806ca041840e10a550600c404845801c10320034083c903130154030780442160402800241c000d5841580360254543c40400ca8a0f51500d80e550024800d00350b9240c55046000e40e6000e0580007274051000b010181e801c4a00101c000e82080b03040440360042190b120007042003181486094074441c203d19800900941d0f64000442002e000307403030184180700c0c86045032000050329501c13000740d161003801c0d40b00141d0f14181740e00c04201d402c0440c0002c00d0784008070382180001015858801c40d240307080746440040c2d0f00c144032100604082080030304002c0c0d8009031f00c00c000d54598071030340e440704036031038604804240d0b40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 899054613 1250 899053363 899053367
    0x81f120804050a090203150a0806070e03011b05130b090a031e120e030c0909060a02070318031b08030c07053615030a0807110109050d11040510030203060105040903 72
    0x81640e1010794400d0f407410002c82d80c100168000c601811064000c40300488040040c400040d82d03a2007988000d4000340c001410481c040e104600c1c0c5907000a000082c0d1810354801150407a61154030440013620200c0c01580108850311058040c20328420518148030146000844031801404001c000315089049824035075401c42204915550103044c450710400f0074480145030400f12030000780b00c0c0c0301c0c1460104290411071541c500a000035405031090341e865000c55001303544002d03001ca042020111190124004c04580f51001e5845804800c407034030b248510b00b401080d2150011700c02600100400b010b9620002080d03012a003068a01071407000020600011008400c01c0c5c950051015a404411102d410070842d4420381d104509298004400014181c0d6804031600080c00507408112072004110b0850f11481c501038140350055540740c0b5100810b1b21107140900c208d80c1c0040c0403c1101e00743c6040e01623194442503040c001c2001c40d00d180c000030b40d926010301c203032402160364102400a140c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 899055863 1250 899054613 899054617
    0x606161704211e0b2d070302180405060f1005041203110f0706081b16060b04140601050a050c0109020d030207060305100e0403031821081f1208 63
    0x401c0115401c503152910a002c2100780c8109042201c010004410061010300414051586030703421489000c401d54680d021008001040d072603c031080c48000311202d40b00300ca007040740e03031094a00d43c3d0056107a00d020822507810249034483c080c4901c5c01c0c402085915250406101039001048a00c80400724410700c2c152a01d120700d402111a810340080d142c0c09242d0004010406450b404007100c290f00344000d02d85444604a001e036030001100c035000b0943c5022201c0398031403400e402c81856485e0009070354803c102070184000884981c0d45521002e1550b1803c0d2146125a07080982484520300c0c14200003001441046038035010700c2004038000d4903d103425031000040c41d40c00380201c80d85102904002c2d503102038521420340003a040c5800141082c04082c4954100c03001d101460107191034959007500075012818002c60000c006c07501c85070208014a00d4258003850704071a201881c0c1d21001c00504480c402400803024460350031640b10754501400740c007001c842100070f052040225a180590240c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 899057113 1250 899055863 899055869
    0x7030c0c17030418020a020a080c010e060a0615020a0201120e07031401020c070918060504080919140108130f080f0403120807031b033c050606161704 66
    0x38030148000070300307039050000c000c00943e9005208000c002c10180c0d405001c2e0710942002c100107820034101000058588005070125610b20000070401002403902d0916082c422a80c44905603100e101c00c00146200e02c4045941c07034664400380c242e04d8a07a0b00045c18100d035164490909030b98a01418481031001d000c224041d5030b0080c21000c00100003c02e85010703401000c80800540150b00d00011520381910a44803d0040780801c01c10300003150311000000c08000348291214141001007041702d42d5030949035603040c9001c40342584614204204940424140013007a414096440103100e02c0c516201514032050741c0c420074030051185246400303112070055083c41c212a1601042c00301c200481006480300382c500541d128041c50303440361801c0b0251901e40c0e03004a080d40d40b1000714a05180309412540c00d000700c1094a60a549a007003c616810160301040e00600c01805982d9040e03082900034207030000000ca6816080c00c200003501440c1280002005114a23508101c0d4110154144192001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 899058363 1250 899057113 899057129
    0x4052d06130b070f030f08190c27030b010b0901050f25030503061905010804030e0a050604031a0a050f01090203040f060203090d181a0c0c06030403020a0b130807030c0c 74
    0x303c40c2e0030b260441403035000d0f45007100400c0130008000201c5101d22400c62298221000841c580540280120014284402641e0401007044c21525804c04c210100480c0d6540403101300c01740915609107000e4050046c0c009080403401000014910780c0e2000c1612851005208110394030a09400f0362000e100b13080b20103803861706003035140348145504500518490b15040d2160007041c005282d03070200303035403660241501060414001c00c2c082440b408604482a42c040d002c402e0079511000000c1c0103400a50084134440c0c10040720000d600e1144c6980ca41210441c003080c8083d08040c0d18018080405000c0c030740c022540400000e05001420600001058003c041150f9038200f000740d50b0f40340c0d480b090031540400e2800d0418104421038001c2c81e41281c01520901900343d164004213402039000c4150403900b8840c015821720207a0318800154000ca11179002000c070406180b408406174940248455060080c40b0400d80c041503440d421a40c1d4944c1c10303c0d000f48452124a0840e007140750342d400c1480 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 899059613 1250 899058363 899058367
    0x9060403020907080f160f030203070e130603060e030a0c0f0f0602040e090c030a0309060e03030c010f0605030d020d0f0302090d050d080711061303051c1104052d06130b 74
    0x280d08000185d01070110b00007030729002c0d0b0b07603801007450082c3d006191200240205006a22441c841c1d40659040451454600b140d03016550014881e941c00302d240c9201c0903503942080080060a101d290002e0368088051410620961405400c000c92803101a01c00c146000c19a0200a44240d0042c03410341d000c0002c6440c0d0303407140304054101c8412100b45035030f481030074081429880d001420b44511940342d80c0705075413070741411f1044500003440d0450075014842072042c0d030711424083c002c40429174400000000c206e8a808105071070144241ea42c0d005642002d0400d82166a0150303490450a01c58200540d8944910011500444c00c1d0314014080340074030302072068055402041d490041c0c07d2503a80b648040c850704030f41341d1969001d8039104c0c5540202e0f0000302c0068041d03800f41a00a030305040200000148240d01000d40e4400d03070101c108000300240900c414a0710000d460300e203840035000c41140d60080081c0110802c5a13a01ca2840344501040081c0a403182080b450b010309000e2161503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 899060863 1250 899059613 899059621
    0x30c0105131a1801020102340501050405010b0f0a0f0603110c10200f07021215040c1a12191e14060906010801212102061f030602090604030209 63
    0x290011503008450b0f4100384650b1800e98414002e44040348602200155182c0030303605090f19205400c800e00c029040b100d000400481d9080c800d10384114002c000111b4403055510400c46808001440c203032141c0e0440e4014407182120a003510181c403410f040004030b600071940910b80502170302c0103c2203031384038807120f01c0080320031a0060000c4607066a4400d200303c0d2201070303031961801881100030302200c2c00e004800c054501a41c0c803000c1756070408280c3d154859990b0b1254151501103e00781d0f40c2c40d14aa00800c4074903948030207207140310600c0b882c01d41003040c036071012081c500001d000c15001c01c00421440c00c0a2a80d03903c298000e41100c0c0030212602054502500508085d043d406202242c06000075810309128030050302c1000e050b5260300150b801c00f001200030729160044440c51025400b080e10002d103582600340440d0700c0042c1220b050308100c2000030300c0c1c030f64002d14110341d00c40300c01840049000013220120540743e0060000d601e0310303003075400724234503028130741c00030f0742c4400010244 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 899062113 1250 899060863 899060909
    0x1e02130321030c030606050f03060a030f29042109080732010507081e03070509030f0a05072928020a03020a1514010e09010f0605030c010513 62
    0x8035004061510b05000340154403074207900b194074034450b20000c904100700700711428030102c005503406440100340440498036a140c4802106103444115a060340826070303201c81105515030580c402800400b00c4003035292680c5c920030103004980004842034105141d0410b15070013050004094032183e0304444400ba46c45070110641052251314581c203e2200204014904120391b0610303401a068450b545400904c2d940c1070f0150b4009810702c00c2c84c00f0345070100c1d1509207a0f0402075000c0d400035540d5946488070b5808042c00c20000000d070018940c8200205000540003095007000c64040304c1d0b13980c3c002014250094824051851408810320300001c04192140810180500d1851080ca020031022001c01060366250820240600076900244110b400200221407004014080300400b14525802440c2001500b00a81201e64403d102e1403c12540038401d05c0b540207011300144044c011a450400404c3d2622101e61390603041000028411148420b0802c40c1e400810b481d040c10a400172103181c40c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 899063363 1250 899062113 899062163
    0x50402032e061217030603030c0703031d0105030603070608060f180106020628050a09080d0f0e03041d1510050c0d0f08060f01021f0219031e021303 65
    0x407100c840e5140120202d219000007030007030b403103d5000c807140070f480c5503000c50f0084582004211903898401000203800b881d40a0000344011886600c800f0203089060800c1d4043d1114000c0e090b04229090041013030035030740001c0b468100c80e031038285100181c480c0c102040c054501000d0300c0da00040080110f140c1c0102c0c83da10070381212030707550a031880d5490300321400d00902140c8100e40c0e840b40450036071001c90009580031503007021030076000141c1007020b6500c001d0103400402d0070710074041d03a441409114100700c0c0540310800d20b081025624241c100206078920b94003c0750399048150404000801840c24580321844000000b405c00f11841001c0d1001804c1d030f03011461002e000d02541d0032980c3e459014003841c0110320100d4031040718035910b8030203000780c03529007030341040c11485007802aa90501340d840051054042401d0050f9540e4114900044115291a210000c16141841c030781d03181501403142d4018550b00300405030341c17213481d00d0803c2400340c0e1580015140b210a2610454a0406c1e454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 899064613 1250 899063363 899063443
    0x327020f04141905040305040603111e0a02070501050f070818060301032603010311010e1908010f140705030708090a150506030c1813030908030d0605090a0b1305040203 74
    0x1200040740d080302c2c03c1110541c0c00075680140030075000e000034086180613030003845040c41c07440b1000f81003029290450110000c241c0301c150035800000b80202d2184e03130512001c4080d00003820001c3c44c25801601c00031142c490044003034403100000c60800c01d08100544400768000004125944a584a04101c030100c8071400011051200ca620f041c4c02d031584800980f8104c80e0001014802402880010b48041e10041d0400f941b2500504840f40d0681248284001420400c0000503250b4800403140048074800c0c500c0f0740c2d80d0b6042100704400349070712501b03c030360040b41483c01c0b4007039071542501079240c185c0c1104010010550f203003400078a0300250744501d00c9140110104c509a04200c420700171b85c1c600140e804019a54a0400940c900c02003910441c0c54a10a281c0180040d42d00c440e40c2c2e046801c0214068946601c803c001c11441c0f400c03503402c581211012000704281c6441c0c100144802c1042824440709030340f520005000d40da001d205051121102c0384c0c0440c01c1c883c05540819107145040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 899065863 1250 899064613 899064631
    0x1803050303090d0e0d02040b0f0d06150f03120315030506040318170a020f03160f090636020d02071b080a050a020d02030c1503070f0327020f0414 64
    0x4403d111000f44070381e1301c034051080080d11507040000c02c1d0b001c0c0b20161004049140d0083e04400c4905a1601c540200c003030950301a4100051500303102ca52080506050b41c030602c0480201c40c0180049900000c03480300503040c50030f0029542803a01018010710020f80c1c0084c04501892007004149908503d1001d1503407407100c90f01e00003940300c0000c0784100034103442d0800340c1e0340300f1039050005090940564804000090480b02c180504116604903031010740c1145003084a400820480c5842a0041c08050000b0102c3d9240046080310039141014110f200c806801c0c00a20110062594a0381200e00d12003444205554511761070400443d0000140403911590404400004c0c003414040341d0301180c00da110015200c9074402c0e800b080a000d110050680e4507014101d003283e00c035958200100411840b40010544034900000042d05203540d40e82c0440030b250404109941da074850f0344003004222080c4d00550f54032039150000c520524582c0d508141c102d480c11034540300c0d14800d203907180e01c144648 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 899067113 1250 899065863 899065873
    0x5040504110f0a03050a021303060608010c08090a0308060d081603090f060e010311040918120914010f021018020f040b010c0f052803171009020a180305030309 70
    0xd005800d07010710500c00e14a8882c2401e0006203089442600300c0c5811400d071041c0541000301c0043d007030b0100c1c1f03090341c82104c806564510410100900f07020704400400c440c00d0230505072501090007a1218411303040101045204000a542ca03500c0900380360341560002c41003038881c004101172140300400050240e011442e5070100080c0090625240c070103a42056644200ca060050015000b501310708802c80d86441c018071001c40e4103041c510407141c40303018160f040c04031484503090184119051495507020004c400b401484041150542030009040c00e192100180d02c3c404800c0381044501d200c002840c07400d25000b454004d444038520103500d802140d0034040441400c00300401c90345000d90041c08106482001d10216071504031318190b2034003c1c4d040d03a440e1502d4250b0f00b1540e0b80124407041d4900140454407041c15070040c0c54001c0000108030020060525001c1a40e00d40322600c1600c03c500c4d00001d0607142c1c1807142002c1d0710605043c0009007020713502e074540742c1d40301d030003c445c214460320413 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 899068363 1250 899067113 899067131
    0xc030f07211d06010305190620040512030307210b030f0d120608250e3309160e0909010207050d0c0317041e0b04030e061213050703021005040504 64
    0x8040f65090480340e000c0c0003080c0d0882c4030307070413082d408000c1d40d402e444e80d40c2e49071251400240031b00790103945c4100030302519a460742000c082011910203e8070300e1015610030300811260b160000e02c4560b89044401c04000d020100d0501000a4905007400e43c2d01400351280c0c0d0701c0c46000004150031410415280c81185180c088481c104844007441180748561054480c020030801d0f400c94080355070440d00b02c101003580c40e4010a85049001d4521110a5103070000c44458000d10344c50740c4008820000d11003030008134410021b0026100a0f10001d540000d000550852500880480e202041e004d041c900c21444c0c801c5456000f5001040b095030b02d4003a032410440c0091154010050341a03064442c103503605c000301d5002c600b454008008513000c889405541d80720102403038810310038034800e00c101e45042c80c1501c0c0080448018032003441c003c0d00d003030150242e10090300b80003230381c0503641003003004404510307060540c40c3c001d02e070b84041e4014aa480c0c501d130b1030a1b808002002603030400d031014091499 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 899069613 1250 899068363 899068421
    0xc07022227030c0b040305040e0702060103031407020919061503020d0e010c090e1e1501111f051509040503070c1203202e050f0c030f0721 61
    0x720308030000d00040648035280e001130405194150000c0c001d00d8910304058440d400c075000481c0903505080941d1129004104056101144800d20038002e10820b08101080c4d000c00c0c1002006010040c60b07140f103074016960151103038048001041c81d0604d5029840318218054020f40c000d0f101c4000003803e1503a0050b01c00014011040b18035010b540d900c80841c5014040008a40060702400c1007030030000905081c1100c16070014001c5207404035072010f0b41007100024045000c089000080f98202e0f51032400103c0c0040d052550a903134501c4086015600d441108078941000700c07181740d02501110600040c01800805021028400c40c06165040c0c2c0764015444c01c4501d00c032000b000107240d006c40c3d684200030640e40540c180354420850340b245003145452041c510400c900c1920310280c03c41190f0705800640502500010700d0f4144c582c0904240d482c0041c0c92000230601300d4040700403004101d2142c4104811160101c0c1c4c10800103006a0040702100600707051104c40510346220b07060040d0080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 899070863 1250 899069613 899069681
    0x11120c041e14010302091f05030706050a0f0f140d0207020907110d0302120c181503070207090204080c010e031005040f0c050f0306060f030a06020c01020901021c080c070222 76
    0x130b0f400800001490350381d507952103001e04440003030100902c0b1f91400014192010044080581120744a05845034110faa0080217480071940e983c08005404402c0341d4110340141300502c0d50703056101e20f1941d4440501c5c20f04064410454000d40003030142c41042000ea6014605544803000305040c0d41c20001810012810303070142e55007014101c4141c401050359081480014a181c0110b00d1034050344401038000240318000300920184081400010003110136414003042c000780401200071410541445c028a50300c0300c901c0c0c1b9080c140542401d480131a41c4e8104061040c3d46030040301072041c0d103400c0c54207819100035500102c0d502c44c4040d00100301d1b443c00728403c600e4041c000e0000c001c10364031901000b503800b6600100c13a4041c003a211007200400c00500003000c00c280705000240e99100d201000a29165446100e004060b01d1b2650801d05987d0082500740c0111034603d00b5030303da07803150000035007402c001881d081002030b00752040000c00c2c580e6008218045010000c1541c6801d0b2060484250 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 899072113 1250 899070863 899070869
    0x30708061005010e13020a0815041109041a131a0919091106210609070c060e011d0c010e04050c040506071b060206090c03010911120c041e1401 63
    0x7590407480a100c2548180c40059072503200400490000b8454005d11040364003010a18000039032050803c01d450940c101500c04c540c00c281c40c100322809510083d401540143c00b2014030594a0700700040c40e2000401807803281c203100501103000115004000c00040200c0b03a4100e00a582032400149145030000c0420721402004110514080581402100400144404643d20003c0d82c01c00c3c400c5442e02c902070301c01581d44080e0314114429000d0b150024000040c9040d10031100e040810031880e900101c62001c5581c8401c002c102c0e5601a10031a000d0b080ca1b50030481c04c21940d031310300c0405800004030700760440310130789404150303014400500040e520111100408003030200003c011130b04054000b4104036014cc121100c081000c00754240c0c5c101031035804800180d100100380210701c80140001c6100d40011402040b4284090755000c078601d8410452902c81d0030095240d810002c03041c0601120201e00070420440e4038202c1d40c40c06e84400503a440003220600c1d041041028076818815581030b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 899073363 1250 899072113 899072131
    0x901110304020f2407060e030708070b04031b0f120e06250f050c0108070c111c05010608030a1b021c0206040b0d06150503060108010e2a040503070806 66
    0x145603225000d102003e506841c06a03000b81c2d009200b10150442c0c100700802d24113040c1480c0341d80c0d00460074418107941c0040e00c030712899001004407c0004d102c18084a400c558840d0b60300145541d94141900e042480c0000c005000301400740c000100220303d407240001c00d1191408074184040d409046900800012120380c001740c0c1082445454101c003140c6040c4031491500d006501c24803a51401820309500300c00310380d103a000412031b884560b00115496840b2043e4541200c03100602e454207072950903040303100b5000c0c510351268200301581c7c00b06206a500d40120091149603a81c007006a500e034400602800041c0c0d40040ca070001603800994048801d03002088014044900b40924002c2000034100f00da0202d010000082c0b4552444003400d055540001c002807010320380103110540700e82801d42442000010020040bc50380c0004038076040d00d0291261502e01e659440c2c1c843c500c09010f007403d0722226002d00e203003610406660014015200c05900340c0728020740e519416695a0301c01d50b12840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 899074613 1250 899073363 899073367
    0xf090616201e0705031504020d060b193b07051306020601050109050d0f0b0601030f0f06080d090f14040609050c0901090e07090b0c0c03010c020607020105090111 71
    0x34801d00c50448100d606004055180080c9164102a494115111071001031003100305403881111006110f01001410194054030603a8204c09103000515001407009100740741d1020440c09009240e4021702e8070320b5010300007071280d50241105600800072480f905d007000e01d0a0014120b8800c0b440c031222f902d950500303510001c0002014190040780d800038010700c1040300030b000300c91004c048000d841d00200500d4028190303d5040000040c102c0c0074a0b003120340101440d006000021700d40c100e100e25040e822100c0384030640c551070012406885e00800e0482404e080006030400340740b131540f0403400c0315003010031940040e00482e0243d8901681d0b1186250800b40c5100400c840c54001d00702c9080300c0802000025140e44407000c4001302c0e041a614030340014008a8150b882d542c0090140703001d0001031100614924200340c0003403001c001070040c801000c0f4041105422404100180310202e80010000d103c05050420000d5403080304480c020010360819001c52010181841a000b001c0c4003241024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 899075863 1250 899074613 899074651
    0x100f0506070b1e040b0108060a0614060d0b0a0914060312030610050405040204030303052a03161803030203070218070e0609030f0129030115050103090c03060608060f0906 75
    0x9801140c008005003041a58428182d06643d45061201c0c0300f00e10441e03003044254100307400b1604e801713802000d00314245d140171428801c90b6019100704005080c00c80e025651080030301c2d0703041c0140c5034104280c0d42008642c140403510034801e422292481e010f941600c60300f40e4441041540c1d424920307103c42e802280800205d440c0d4285980c15070103103052400d1a07882c15a4400100c0c0407640290700175800030b5511b406020324081c070100108030521080000c000c600c10030380130321240c6101c09000100000301c2000c1c0300d0955030003008020380c4004500c2d01d2103c80d0341d0340e00b030194513a401070200301c0c480d100031000c413101e070705914181c540200304c203965406080c12203506006550740405089070389441415010404041c090092400007141c601300000700d1440c114142c280c80400d000e4051003a4181840d1150144582c1c0c0c0b15001ca4000f4a0049a400303254180f06d034103680ca43d08060036440c2000d20101e81d12100151140c003620a040d41e01c9060356480300c896484606c241c808400c001e035004506 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 899077113 1250 899075863 899075873
    0x10303091518141c06150e0f15030a080418060b0c07050103051e0403020a030e061c0b060906030709140d03020c19080109050a05160609030312020f040e100f050607 72
    0x40c085801810400304500081410740046004680485d40d030703600c861035030030131100100415008080014488510381403e88000d00d003980c0c018250380051099100f842002d94007080032500c131a403c80c0502d0703604e640b2120305000c00c800da002e10420050510702c00140005c50941120560302144001c2d00c101401c00700114060000648031240c1c00701c0041c4120200048ec00c0035038050383c0b0a40041070882c52600c2c0180282411000d40f40c852a4184082189015840b07004448a040e912000402140400c001002030045070301c016000318001c82002003043c2c00c0060b1005440b1480b1544d08002c1a203410070505400c00400200140c1001d804200716082458041d5524640c840d0140c0c411502d031071801e421a040d030340702954194050207074182031001c140100045000640c0704250642c1c2040e00281c040080c9220080030003002400c0002900d000f075041c1d03a640010410341d2580d640d507861400d02c07191000d907841410044040780005001c16000d03071110444801800060920700d0580314 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 899078363 1250 899077113 899077139
    0x2030708093607080c04050f03031b06070e03030906070803040f02060c01020a120510150311030709090e010e0d050f0c01020f0a091a04050d0317010303091518 70
    0xc4590480d26410101c4560101001181402c60a044661540c00c100644010510501a0807001030200d003000340030a5941e000c00b101c055400580b1004400c5a41802003849e5106148401d1900b2801741c2500618440100701103018001d95941c00d0728104603130003015101e00c13500b044160b0001c0100223400010304540301841e07005008141c0d0070403080c0c1e40d40200c0c07216449003010b0780c280d9500180390b10055030805858581400d04800800541c9014801050003102da8080c0c140c05201180091b280284290407901e0070006000681d074807800c0108001c0d01002403809004c0156080490001801805100341824140c00c2070003010601071200040c2c4440c1e0206841d40003101d0100b0a003022a0024001003240040c0e591801d41c0e0340060503002000051540c00100e40f40d107140c2503110349180d840e420b03a000e0724400c0340c600c2141c500f180f4040d0f918210403200d4a49120782c5400000c107060300080382d5000c0b82d4464000c45102c403202c3c0d00c1140c0740000c0d82c08034048100301000521030b018544079 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 899079613 1250 899078363 899078377
    0x207080a1119080f07120210210603050115060c051e0a060e0c0901050d0c0b090103020c010507020a120314010b07050c0d080706180f0311190606141002030708 70
    0x72180505014070a650b040d803401d80010f1550f910100c0f2a4400c1c800c100420002081d8095280640c4041540080c1c4100b190045080170000401035000b410800d160002440d101c40240030408503a0340e180c0700d07019001210003a00303c00d000d03d00c00a8254000c015009049600101518000b01c2c85c4c20900003030300f9441c0d5580310500c10304a2901c00200c0c140b01e81c142401188000b031035020040420131602d440142c101c1802849400e61a10015a40d5095401928000805a52100181d00040b0024081c2c504500325542c24081800030b13103500420780c2240c450150b5540c244038000f00005800740c900ca004000e14035512800100411140e001c041c15007540700d1010741c0c040740d0307a40780080c149910030300c015582c140c000a000f00400c21103210f042e9110700545104081e1848584032041400d42c0c07120007034140100c2c0303210f41e42c6510090004010782112118800f4913680103061940c000e2525001d00003030b01c14002400440ba2030301070102030040f500c541c002c5250103200e540396040791f08100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 899080863 1250 899079613 899079619
    0x20c0a060c02070b0f04091113060507030e0915011d18060409051203070e030115030b0411040501061710320604091b031a060c03041e05100207080a11 66
    0xf0408034039000300c40000c0c0900f04020004548031410003603c1340071201d100c9a140e100b99400c01c58482241031110301c0d0720440314513040054595030b503801c0590703100b03000c00d070f419601010010821010034488002d011440c034082e60b07400703540d80b075021801c28161601045103030b00000f51801110814805100c1700e60010300507102240c3c40240d89d452914025014483c1001204003104211031190f02041542c0c0c4110120300034081c0003403040d8800e03008040d034000905030040080014080c0402d854281886140c00f610400c46907039601700c010314101c1c50842c3c80e4156496100413800180202c40c0b0340f0b06488880b90484003c8242502503000c102c0c440046500b00c02802480c0032103551030802a00040851400103d80035601c1d00d8500382c139001950028052504c0c146c400c3c2400c001014141e400a44242d58440d40c0f0010300c00030304c0c6540201d9111a505006211107161208100300e103100403907105072182c07045060030390000e0f0f860307505034028804103a2122044001003005c5407820223a8a1010f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 899082113 1250 899080863 899080873
    0x110d090201030f0e0a0201110106061d040905071509080c031c020f0109150c02031201090c09051e032b050901030615030507020c010c150f020f1c060603020c0a060c02 73
    0x100e0405001c1d0703a048003d240440d00301d00c145c1c00c15941c110b0f5101003003540d000c0082007600d0410101400b51140f44406c00c48010840d4540000b948859002c3d802d01e035080710449201d150380701e00b00885100c5516100c0001604030740c000402c28000111100003441c020064003100c0500000c428404c14007481c5034046228422640d10807a10a201d010340c014010011400c2403c0c0c40042c040c03c3e03901620340d00c2c046510420004210308600038009040d6021200302003001c00e8100800c641103500b581009600006160303054050301c02c1d914030a0100c0e07000f0f0742a2146480f030130300311299441720750350110000c0300ca00c0c030f0f2a500b8600c94002010348004c1418000382c01034580902000c60791582e80c0c00c801107541c8209101c211a010040155100400d02e065407440d102c40c2d0300d190ad81e9440010003006c03180c0307488150300c01807040d8041e5517441d441488880e0721601a0040c0d15081e10060000501e26890304102107141e43c8a40211040f6200030001814075220710780d51040104840c1102c00114096 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 899083363 1250 899082113 899082131
    0x40b0105030c0921030405100c031b060f020412050d0509010903110d06140f0a1a120106080a03050d05100308030402061b060903070c050a2409050d24110d09020103 72
    0x700b28040481c01e003030034015600c860400040c4240701c101c2c500c000003407008001c555400607500c40355504a1640200d09046c0020b5144cc0001c050546403e040c50314600200d0042207100c0c00c10008070205014008840000c0070010003038881c0e01c10141820300007441c100c000d0020810843d01c0342640c000c09450942002280d448400840300f410400030b40702400c0380244014041c0542c03003190801c2c0a450100207018941d403010001248101c6014043d41d4282c02c4401010820b62001004103040d906032500580b9074030b0000d2440d8030115144140c036162201045996100000c01011340e58000d01c001e00e1034440da002c11001c0c1d0440d003590300e81c96031000c846068165050002600031011070b0002c5482e0010342c81c2140c01004c00350000c50080f00c3d01c0500700411145107124042e54040300c0448007030311401d50004c59203140a600302503082580c4280780c40406c1200c611110000040c0030301194100b00d1120303420261142200e8607100e035101440305025401490748203403062841410001a8496 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 899084613 1250 899083363 899083399
    0xc05060c030f1b0109030e01300c17010e0105010215130206250c0503100b0f040c0c12080703060504090c0501050c0c09040605011403060f010e19020c07090605040b0105030c09 77
    0x1505039007100003403100107d841f4103582041c00c03540c010440c1502082000400a0003c10351690704550700d000c65241c0c07044a00036806000f5580007aa50001b84502543c0c4605170700b00361840c28410b050040c400c2100742c50348103d5040c0d000c0e02900b542078941030002410f808110b42030b0071076039141400c1c0a0180c50322400248804c1c10601d0725116044440082e89000300701401c0100c1034241c088101c2c148107500c07081e50703501580001d40b690100c8000401440c1910b00b140c05101f8041d004020211110030022916040348406215182580e001d000035a00c2c0d0b001d202c16211242c2000301f0030103040009001c590b0040c4007a16901c580c2c901240d8a42513400001980050152002e95080781d8880c01881f40c00c6070380c03d044a034008140c0044c070b80c500740b071a4400e00aa505100b68840c420703024000c03468420304821528180d1007076400541d125001c031304413103482d000319100b11650540780c03203400034042c18103006000324801c0507101c590445d51112400070150b40641c3c68682c0c41007038070f45403892100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 899085863 1250 899084613 899084621
    0x92d0d0606170d020f0102040602190804030c3302032b020d14010b030402360f06030601051c03140702210d090e070c0204090c120c05060c030f1b01 65
    0x4261072004008205043c0c001030f0a08076415014501640104800d0100302d03000210307855110f03160106190b5000305424000400c1c0141e80008000341940c6200050410071601c50381203554540c5e849845924600d0780229100284e9820000985c00074044040b503058072800c6100d040e084588000c00304000c0115100490380160201d03840c4e5035407204000041982d4401d424003404501402c07034914101500080c0f0300c50029030903520ba0701141101081c1085840071554001c0b140701c2031103540d9040c40d40f603144840d4021907955009225042c00009e1514040d000b581000b5144801c081c840422610122603140700f82e07080850742c000420442d0010b072181d0003803175100481c43c11464280c0c0385100100c1d09180c1908052313403c000700384109000360111a403040c0d070086494100016501078034408240640302404000d0640c2c0307a40300c4001104d00d9408810340442e80324204103032031141c6460030060075020344881c401043e401445189001000385000b40030b013591440303444d1604030620700814291 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 899087113 1250 899085863 899085899
    0x1501050706062115020a270b16020906030109030e010507020d021203040f1e0902180d05010f0e12040e3301030501050d15050a060f0803092d0d0606 65
    0xf01800c03a841c5041c0700580002c4625455010401e601c0e103010803034018088141d8650402503c02d5800b40210b10354041c0780701400034003062103029140d46003004081f04034010542c09a024a01c4140010080d14062048802d02549030300c03880c3c004010000119007503040503008981003d078103030840740940c0d107600514001240c0640207507691070410310082600203003540081c00020b220344031602088070280d0303020b040d102c84110040e140c00a18001c0d0305c4240d40300c03949035000480246070505014040d0407020410320980c81c180107040705004c04659444042d0301c07107220000c003800144000c070404101290013001c905c803c414000c41c00241800398000380c03034910785000d00618004a165030180034007401001d00301c1d01d180c0c460415480f03a10711441408600e4550325a01d000090b181c10246d0700c841d01134620704001901654940e110550750340c1c403220b41203116910103030a51000303042004904900005108650355031001c040d06000005840300d00881e841178907048081060300c034019a0340c0d20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 899088363 1250 899087113 899087159
    0x1320030601090518190b19090309140607030504090c0302121003060515130e120c0c18061c0201050d0c020d1716051303060501030503120609150105070606 68
    0x490030031114001d11180484d45030039041d04000d6500b240c00116101180041e50410103090055a030342c6200494100007000b0007a5a40c41c14100009065010f14003034151584007142d0503e0703d840c51f00b000300c0f50044a8000300012400c12040c41201300306d410616251481c5c0c100541010950f121050341008129000e81c81c0248401c404c00078050940101c2d030300410700d90030100c83c2284c1d01c00402d500d100606d9400d40e205844058088010a042046a81e0300040d03003c6c9580f100d43c03014a86446500745848684542a00d1b28070035000d2100144d0b0134091600100b160000010300100c01c01d0b03095280a09a0611000340031013184110203020700f08240140398058120350410a0300541440710000e400115400c0090420031040111b01107000d6194050030240d869209a0450008050850b000101002e0801c8000010000c0c00030160851034044800c1c03010b1969050203200ba0540111041d907510b031101d11840b215235000f20018005240180c9002c80ca054607000c460101d08002e40e98076103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 899089613 1250 899088363 899088371
    0x70311120607050d140f0c0a14040b21060102032b020d060e07030b0f0409020a05150c1b030703020112020c060f01150201151703070c0801091406132003060109 70
    0x80d801058030801c5c01e00a002075002c003440c105005903005a0000401a5807144d0000441411460042c0f41121110b24410803440c2d44589504020344541c000c3e045804c690b0f2040c03c3c261100c003407000445441040181e006500703080108503c94140c0414442c0002c0c4811001410080c141290008050a00510fa07002c00d0051608414130100000104480200351902d013101040e0740d5683c10070041424112004030b0034021500003d81054140d42c445a4002d08086c14481c010705428080c000c0b500c144819290303183c0c00c408500e46130111003000142d040d0826001800158019000c10150350b510359001030801c0e8002000d50f02e80307002620700c1400400c00000400103142c04d014820881220792000344480d8605011078040c5071554040e00384c610b00e450b00c003000505001c000f0760701c549800011031070803150b41c1c0da00700d8000d00f01e17050305a5900b4002075809007105400186c0a0056031035808081500c1c005032210880280c4040100324480e00190361542269020401d081c040c20709154002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 899090863 1250 899089613 899089627
    0x915030308070201090b0402040509100510060e0105040e041e060e060405070519030206030403170a0614060307050d0914010c0e040f061a0702030a0f0302060f0f060307031112060705 80
    0xa030074088010550b000316030404900400041c0d6080d842608568140e0b004540c035120000c4440c20500c907106801c442030314000c100607071008107490080846000c0c0c2ca86001d858081d100450701d0f4880e602440e04028203003c041000203020320203801c000b60f14003558140000c0a0759429054a070003074424511680702500344028014140003042c000c140c112402c00c2030030b01d89071201d030128a4610019100d0300003c80000d09140c0501c501e6000341d91400000d408900e000f0014600614090240009406a0654000c0d250074000201e0307004002c1c50302c4040c10b1011410f1904064072107018101e03904034610091040b52842402103220802c015182c856140308024280002c1794103c0c845401d1003418480208090907600303000c1001c994111405a54400d16800480d160a0403039000614a08010200400b4580d000c107915000d1015484140d409458241e0141c1090380d0503180c451307040c0c00ca25010400a0003100e070052040c440030b041010303080c04c130419490511004031609408940c00203649 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 899092113 1250 899090863 899090867
    0x30c010606050a0921081204030f020d2f160603050a11190302121303030b030604241407052214010e041508101d10050c0409150303 58
    0x40d024144a25000742429004080108403132078600c1807802040769a0f130f10888504a0008011455800507085541c0300020ba40300005d202007110240c0005502d0754010800600c01b04400790f0846050703403861800c2c000c191110305591021124900d1904070311542101c44503081c04070a026010002600350041d103418800341c1911801010124020710344a04039207142c804000b9240c52042524040c80742020104055000307108407441301c1050714118041240c1240300d070f1a0810028841d903810f0180b1480e00c01819520385050f58000d092400c05560b40c60b51003c100a000d900d80f600140c003003481800c0d54940e8070303503c41c151001000038800103074580e0b1701c030307440d94540c4441c00d00c40c40045071003407409142d00c1c03081c8061050581006868500c01c2002d60303840c2c0100b04a17141e620200810380741e9411317000c0e5071204401c0d8075244084c01d0103081d0001d15800f5812040010a69000d4002c10098002180050100038403520031060103002c0403890110b2442584045100341e0342c4080a48c2c00d41c280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 899093363 1250 899092113 899092121
    0x905100b03070506031b0d14010302150711011d041506090e04080a0e060702091e010503120412020607140a0c090507121a060a03021b010b0306070c170c030c01 70
    0x40c0c54080e034040102040f99031a1403040f25400b602c0702c40034100700c1a09401a000e288201412480c2c0d85003070801c1000c0c00000820800e0499200b01c491030718040005400c5d6540c1c0c0107800011780000c10b14803d45801e54003401811005610580360203400a01110005003180c8001c4a0160440d05910042c0001a0441c90b0280a004a85c140c10018a001ea980b519140308045010301001030440c11010b80c1d031602070a680c6101c3e40140000c82c6071070189d030348602c1040b50300c01005007401000c00014003410042031310000000740103166840e0908002804201103400304040f604007004001c10804034101e6442c030b1300c503290514068010342620382091105143c440d00800030f41898003040c031006a41010015884003c940004940601c00b00c10a00b945400303038580035000300c07000501000d070a605030f004040d4a440c01680590040c141d0319034508856990684e150140d0108010554690143d007000340038520a01c0c0f224070b5090300e0b2a940d103558000c00da0219081d4030100d14500c0c41d0302c003809 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 899094613 1250 899093363 899093381
    0x2220314120d0b0612190b0f010f321e042709050106141201090c1701110d0b040f050f071d2106090307021819090510 52
    0x18a031a08128450320014803807003515030b200300da44403140c0341541c507a4029140b10b80c2d00314083c2c1d031461038116085000350020010780f4900b5450440600303564030f4180700c940d400a0060b5039030341e1401d031241d400761030a01030901c02c0c0e410410b1036017804451401668400c0048030201481a440d01c0c44450343d0303061002030040c001030000090101344500700700f5040080e00d0315225086030b1007200030803440c10000c200c0c030340001c0d04c0c3d5402c1030030201b1b0185412440e071010314410340c0c00310079044503218001d0889204140080c1000316101e010045608004482c3d60b000e5102c1d0f0000070b1040110742204659400100340022482d120391004103d85028806d2840801080000b8406440c04001d00340440000401c040c0500954521144420840e08060b802c2e00401030043c2001c0d04440c00c4001001481c1c03c00e6020034425040051180303540032040e07548642d03002d050003481007846510300c079a0550050a01d11000b1a00402c000490b010b80180181c0d540144d02818822020080d00026925148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 899095863 1250 899094613 899094653
    0x120a030209090a0b090c0d020c0a0302070807091103070c03090b160c05030604120f0201140f040605070f09030f03032c010605270603010b0604090f141e0901022203 72
    0x82000100c1c0c640011060f0b1080d81b0521559403288416000380c0240540f8280264510800c40e004080680009006080e1280141101c80203603035800d510050313500c0b204140c1549a020300c04540035900841103071090324802c5c1040c0c14019141e540d280802c0d048240ca5050b5030040d00c04120a00001702404809004150060240c502d0305840d000f50401d644413868040101d80c0c0300c4858194400c0d840001094941710b00a8080d04006000880c007240c140d41c1940c6075071410000c181103500079004204240c1650b250352048601d0340e2521103910380661019020f041e214080c80c581000304208044007040243d070300740d800207a06000300b82100c2e43c5401c468081c00303c1c1c1c00140c5900860428089a2444000c40031009030f0759030380440d0140c0041c0074401e801400225010440c2d0380c607900308205807250b182040110700f2040c04204800e1005942d04822080f03c1801d01462030010101e04d0350016080d80050319105501f10348200c3c02e10b07807041050350340411060a10801170000a1031440e01140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 899097113 1250 899095863 899095871
    0x2100e030f06070914031f060b0a210203010503071509271b020705090c1204050d0206060a0e180c1201091707021c140105251806030e120a030209090a 66
    0x2d030101f5500d00345d48132800c0155600340c4030019071045a400107405003040c00c0200b501c40f42d1189001d007400842d4000150310410341020030400352058401c1c0c0e8101e55005000303004044ca00801940010080303110b600801011002c042100d41440480840f03503503e5120700c0c107241c115100d60504a801c0c40c140c090592042c0780904083c5640041d4100a5840c100e49800040e180e4412100541c42400c0c180984403030b2100402080c0540441d8101c058a110703025669540d40b0081002028000f0b8042c0d079000301544d80100c0c048600800044400009160031a0410b21204000400544681a0414283c1c1d105c3c290b1904203c40d100d090f4403100021603459080c420300e03900088102880451406041001041c00014001c034203214011110940c3c000700454208061101420400076914521041313010070a80c001912540310241200003044008100c117007011401c13006484240001c5030030b48518010300b41301e5030800000309113007156a2001a5208082e40034810004002007a005c5820b00d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 899098363 1250 899097113 899097149
    0xc0f0804141f05030a0216050111030106090e0106021504021c121403060310090804030606030c170316082d030403080907030f03080705071a060f0f01050702100e030f060709 76
    0x5054a8200141940c05078543e004800021540000100c01401c10b4ac244025846201a500002c5040e10543d42c0d42a400d651103025101a001d0284120001a440610141140c40b142034031305820610080240c481142c40c0c6040301404c01000c10306072004103007840c1030362107260000c1d141d100d216a40002542140740450010392078290040a039809182c4401c0b940c000c200c1d1050445000d584d1110341084055120b0501c1290480d4500074230300d000c0000e81785401038400000c2916003104044c40c1e030b0109102c003580e400389560000b4074040990110280000c0100c00e520701d46005075455039812584034a0b050038024210030f000341080c145504400703024400f04040714000c0001c180c143c2411501500c40e20021103d503c114040980703440c901c4444072844460381c842403409004116894042101c0d00b03010030020308003851a803030100704200300ca0001424502c00c0710322910040d0618804042c4a0340c003090402c00103900381141508000100003079650800609406000489481041200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 899099613 1250 899098363 899098367
    0x17060d0506150d05060a020307090609050d020409020a05041a0306010509100312090e2401051c050603010b060715050f0601050a21180c0509040506070c0f0804141f 72
    0x203000d081c4007940303a0b2890281c0d5594540b001030940e05030740035085605034580411070700000d4005681260010b800300000088082c880c03a03008007516401408590000d1043d03003000014018014104e800c0a4100c2d4002030980d21031040c04061451500d204178188000030825081c004160081c0303126140010034840745450b20b03803e03442070300d5100704000301d8403404400c2a94000403990005000720080c004000880618503114141c0f400d01040c001c03050440070300159058024140c4e84440401689030403c181203098004903000030000d000014040b0300100404d40f1507000000c2039424902c05035070204984c000e407240781c0d4000d000781d440002c581041c1c0c000178031503c2000862001c0101040070ba641140900302280a1500c180e201045281039400190000c80c001700c03801d803024190303070748006000d090004240d84170b40e5114000d0400c583c3d0b03510007900c12080010050314605c00e0503c0704070024601314001c03c094944400f803051240e2242c002c02c1602c3c2d41c00f22000842d04010203401402755 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 899100719 1106 899099613 899099623
    0x3230c070b0a06120c091b020c19080706050310090c082d0f090709110a05130b07050a060513050604120e0a14210a031805030d17060d05 60
    0x4050042080d400b0740503203c040c00503800411095160386401b80050000c12b16045200103001e072580010392410600b41c10690200d000001030200d10614000b040303004014a21060040e0003210000420314100a000c850340c030621508440c40403100f4030512042d6009801059000b45450010241501c20964200880b4024410040703a0500140038a01010945e00780e054500041135004540039030080c2100b0b000c092030b031240414800094801040d1300c5000304010300c1c0e12103041c244a01100c2e4098214051074400b40301c801c0014001141e0b46610903001140d07604641c2c00542c0588080740e400340007a9009030140004900f401520140410103202034076100d5414980c08900090b42c0c1e40d00d08804c40f2944a52220340c0007c1c0b2440300d080071020181181c9011564030b0000c607142c00240510880800c03948412810071550f002a09a4426002c0302d1012140361070391a03c507258 = true := by decide +kernel

theorem cover : BRFrame.Cov 898920863 899100719 := by
  have h0 := BRFrame.cov_init 898920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 898920863 ≤ n) (h2 : n < 899100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
