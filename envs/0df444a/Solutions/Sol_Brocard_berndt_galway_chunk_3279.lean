-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3279
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:11:29.526972+00:00
-- url     : https://prove2.me/submissions/504c7452-5b96-4e9f-97e8-20231c02810a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 589568345 ≤ n < 589748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 589569595 1250 589568345 589568351
    0x3160b0c0c01060b041401020f06010e070507080d090201030b01020f06180a02060f0306030c03060403121d03160506071d040b0d0506130308011d16050f040f0e010f0b031602030706 79
    0x901e140c00d09590b005809024400d042c40d48100b681b940c00024481c010001540107441c0c82d81c41d0000e0000500c10040041050181c01c00008002403201801000410500c44000844010900004081352000000300c0e0540d4059440c6030f02c1c40100050301d80e4012000c0050380310300d001150342103003032820380c140003504024081981d1150801032400380d0f100d254140c084460820600701007681e141ca0690f405400f0a000030301c1084005035030340001c241d03118801707101c100030030007006072504c1c540c0000c8048104070310407003005040007000e101007074000301d1f2460041c7d01d0503181c0c00d0508080b1513118600b4801c9540c1c200c401015120b440503008880e030010191070051804100300f11440280d80b00441c0090304810010914650400c54810302c20103030f801080143d41e035022240c5848519407000001e11070309205d0440d07858083c500802c007030408000b000d140e59190039035000010506130081c01c44800715810621180543c0c0040c1e9a121540c49444054076500500c240c0c114401e001015061a003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 589570845 1250 589569595 589569599
    0x90b0f060103060503070303080a0b090103080f030606090d0f050f01020307140c010b042a0801030305180103091b03060f11070f24141f1514120106020f03160b0c0c0106 74
    0x27400042d004d1181c0000c110610074460020700300498032100b400300800c44035050103d042e00d4001000030316400f9001134052803800b9038103030000d0a203103d0040200c40304024083d10f02c007040024005858409114030084d415401c4c40c42c1e01906001c1d40c0c0351440000140440c0143c0201d0094100f100480301c00b0300200189005001241200004c2c40d5142c1501001c07241c046c604107115400890483c0e4040c5d03101400c0480c1210060321040c00c003010b050405072070780490f1011801001880800c907640b506640400342c507510305001514601c030401c85005107068049005000b10300f040f10001c039880700984070517045510341801200020328a41d000c812035006914a912401e074002d49441080150901b8160b40e90202d403000c030404c2a2606102d4200004200300008080c00399180d1824a420000340044000c82000c203641c20565240e0700040c4034400402c503960b014446020240d2a00c000303107142c44022400e40c0c02250421400508074801c940009000b032a107a000c0d00c0035122200003c0c07048503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 589572095 1250 589570845 589570847
    0xd060b04060e012309010806191403010f0506030303060909150910060b18060c01060e0a05010512060405251806090501060c0222090b0414070603090b0f060103060503070303 76
    0x3046142c03241c0d003c50302e18030b6030340b0200a0300c0d0381ca034080180d40c20704503203080002c0c40111074118020b40400d8000030f244155245010710032007850081c02d1803070400d040c0c0c881603204060a59142c01d0000c5141c502c3d00701400819240401260f030b2284042e46e81100316150324507414901512180a0800c542b00790040c081c0354000840c22203421489440309001351626011190036a104900780080c040b54070310f40310945070420601405013540c00d000005416681c692018800f0601181c900a40c99941c200500082c90031390340885207104550014001c0d850300d81c2d20f04c0d40d00c080080d80901c42120010b43d00580c940b01c1590301d4040c200c00040c82031028020380d0200301824503405101041c03030403d03001080f0305202d201e0351010903030000c215428804000e01185500d920a07810444440d0702d40040c0408644440034050003644102420045154060102428040e503274000d4800c250030240690041020f50010b03540102003078001c01d40c6512038000603001400c003544a5074050160700c3e0000241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 589573345 1250 589572095 589572107
    0x3170709030b07110d030917042d05152a0a1401020a050901051804060b0705010c02010c0905041d100204080115060206010b1b10020c01140f07050d060b0406 69
    0x2244207008040c010f80b15048240c943c100e14070b0314550036a12800c0c0c2422114442e0300a40080d0340074000d2902c10382d4078000012041c0c2d0254001d1010340760f90004603005007040043c03e40346e02c628101c0c02e041e2203090200207504116800c00e24402c400c4e0103d001417a44140000c1c244181503046011514001510702c0262141d2022005903444071803038481014041e018001c540072440d0750755a4074a4000358030015180750300000840c8007804034200402d115629103100301c00103000c1c2c43e50019214100ea03d0043c2c2541e00e41e4001d1800c590404a90741101c0380c0001904058034011a8003040324106051041800d0f800804c140000e4440d00c1d80c00c8014401c16402441035600c420300a001031030070103141320000305c1c5a04c10080181e100704c0c010850400441c0152901207002c0b6076042d61580700000c81840c5c42e24485022202030b5001030b0f07107801d91800740b040b0075201140070503140040c64100800c0034960360003082c0c0c2e0144000050921072a0702c00d584010f0141c0748100495454584a8400600e0303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 589574595 1250 589573345 589573349
    0x5060c1f1b09030c050118080709140705130306050a0e011b031a0603180a17183f0613020a0f0305060a0213180507030f02070b040f03170709 62
    0x1c4140001d045107900380309498220a880d00314100d0740d40903240c14011074034a400814052080100d46030302044114061011600900203134002081c03607104049074240042000e441101441002c000100100c2c030b807001000c00300c4e5000000042c45a031244011000f9081c2040c0015403540380101c80031510f0000307407200c500b900344c4795010054a40101480a1600c240042c025805501880000d050580010400f8448082c000a42c2d500592994641590340986850000341520104402002d0360440709100d101c1802103500f440030035164000b41c441008100c03607000740e0745000c20742c190314040500e41b80d102c00e130303132040880c2c0d50303460012111030745003c1c6140304a124090203071000035200316040c40130f02039a420401030f19158841c018001c0096000d1030000401803184400000c00c1011002c4820b01240380350300105992903d0800241180c00c40c00d2062a854818815000440c000c08a01640300c1d03485612090100b0b4103050030ba980d211594411100c0e00d560101b000010303035000b810401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 589575845 1250 589574595 589574621
    0x15041e180c080a0809040507111f0b011d31090203060705070b01060c050a1208070305060111030a0e1f0203120604060e0411010c2f0d03020705060c1f 66
    0xc0040d850303103001c649a0705032943c054210034003400b203818a85803561100f40c0102040c140b4241e80c14001c1d00c05ca0400c1c54410100a14110008036000c4d054240d0003041c03558142449c045c103101c0d555540024003100400304141c000d1b81c0c9842482101c4404600480d040106003466480d203888460841c0e002d00100c00d4124000d01444002c40d181d24000c10581e0081c547c80b0410780026802c0600c1211084024041501c1500c51064041c020801c0180d40800c0c0401039a1000803d2501e51806802d440c1c003e00003604111118480084007200403090780c0e00625a0f19124a13442c0e4104001000a10210002108083d81041c0040c0c4c02d81c000004020030301140e0500a0103544030400c020494101e40b19880318003160100003000100c240c0318841c050001410320198091440d120345040d501418090001e0868000462020b43c1e40e010b230280529004459819112200341d81c000e440302d020340f15035406001c0108400240d95402e101c4441151115080964842d01c0805004068184024580 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 589577095 1250 589575845 589575863
    0x709030f171603030e03070c03120203090603180105070e150a030204080f011407090b04030b06061b07060905220b01111207020414070e1203090d12080f15041e18 71
    0xa600b003080403050710b031f030340703800103215500a8610b032035480d50b5040da4100002140010001d00210365109000755000301c0c641d102c03200032100e004661500310f6a018060304280a52000d1541d00c607a503029441001c00b000d4100703d034407078010240590190017583c100302118000c44614610300f40c1c0c15400611204006145103100d40c0b01c071401914a400240914040085c4c1080207002043c49038601540100d0003801c00e900d440352404141c802c42a01c60000c59064001c00404c10825074080242c070301034007084500d000c04cd07413064100c2070128022101c0a40184d1940038000e404d80c0515010512500c2c10402c1d581d01032200023211810b07034840c1004901c55443c00b650311136030382c1d468120140300d00c8454480840180025040210391130205c52105c049120400c5014100e40794040c4502c0c00500c04c5840c01303440c2184010141000000500ea43c000b03000c01410040c0c42240304d45e00030344240041c0c90018249020b00a0303042d8200c008801c03050301b5401c120445000b0b0414003526144140500242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 589578345 1250 589577095 589577111
    0xf140f0f190b030c070b06061c020a0e09100503100b0a050d0201020c1002030c060714070b0a0e150115020303100e040c090c0503090c010509010e12030d090f0b010801050709030f17160303 82
    0x8001d501401c9129070300891030124270394441072258020200e5084605140300140468400140108004c580c025000180c0c072804000b2401c0c01c200b4945070380310b408014040c00b02180041645504a4410103100f8241149580f0559000341b1441c1e5048402074a01c0d040600d111030040c1d0b5a902c5051406003600c0f0364400030b0180c81c0f1500ca03840018000d1074040d0300e054150384801010a5000d010b204400d56580c00d81039070013904010550140b5060421000950b250001c442003505010381001d0a6402c00c00c204404001c0007211041074540e040140715181e10b0740c0c20b242e080c0c11900d0f0010b8101c1b520b8030b5103500c4542c1d0401c0246108580f010300302d44440c011200111201e004604105000c50f6403599078400310f2526948030711407040c0e544c007201e00740459948000e05560121100f40c03051030700414040c042c058003150b168054002500240024200000b0080a00d00544406052002c070079001008100f41142c080302e2441220860741c0e100c01c0c9841840301c0003001405c088000ca40f600d174403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 589579595 1250 589578345 589578349
    0x13030c0e011505032707060801050405010b2a0706080411040c120903050702040c0309141209060f090405190c091a090d0501060f140f0f190b030c070b06 67
    0x5418140c0b514201c0c00d00303028941281c107440a8001410034004000440094240300c00c1601c612031300200707920001d10107180740c074402400215040c0c11042c0128107203c010300120141c0d00854810707400000d810362802008a03003544809040c10f03011031321405810400100c05905c4a1413030b02890080d11144404900d0b8420441101d142c44c41031808a0400302880c012070340b842d801000c409000c2e0401c1d900e13004850740064210b800c2d4038521804650f0307941d50a001d0200455091060b04041030040480e000400f00c100c0c0c0e24012026690300c9100002042c80000382820291615154061b0003400a400d0641c041c6090a2203941032403541494444ca40d00300a10440c80c4000701e500c200321080000403912035000c0150700090039070b50001c1e081c03c60305000030b030300f40305180c010a0580c0c42d1050444c2000c2c03d00070005020303d2914466181d1010320441c41d0b50f100c0741e4030403a0500b1030b0615000045260600102000c55008035070542c4040108a040c65015004050942c49050f00e01d40a941e0744003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 589580845 1250 589579595 589579619
    0x30f022b0912030903021e04050a1401060f0c060504030c150504050105060105040e06090403110706020a020a150818010b03030703020f0705030609060a110421020406060e0618060c010213030c 84
    0x406400100084c60400260500d42c0b03003031004610442c030400381030035103502140540b50b003038540d0502c5070f136a90150092601c0204001d8090001850b00710381403a04004010306a5602000c044c19031565040847c08041c060442c0d40a0150301c82c654100740e900000d0b507000249000c0b00e0079183c5501703090028a03030358481c1c02110305403000000403510f5a207a0741c00348405254010b004a040c400c4102da04c2d40300000c10485003009050702c0e8005c244405442c4140100e00790303240d1103003802020024180090f1900610f40c2c0d90301103a203c0c908bc0b51003600040150140010107400c40c0c00d800000384083c1415408542e503100da00c2c001033164842983c0750103155880d038089840c2041c5820050110b5044403454000b80701040480d03801906140d03d4940000201c50780d10112003061450458240841c00c09015450052101e030914107409550031000c03c1052095809814440102801800165588070141e54181022000864a5606010344010601d11600041d40c00038440c40c00000c80b411290b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 589582095 1250 589580845 589580879
    0xc0705010306050a0905040203010e012a0f0801050d0302070f06120608030711221d010e011a0409030306030c0902040323030f07031b05100e1207030f022b09 69
    0x2131310901d946413500802c4401048003400480c0c1c90354035141c4481410409000b0380000350b519000c045014803140240e803090542c849103c1b000c0c030406070300c0400c1030b40d004842c0d241100e0040e5440012810395103422801c16030650001030603560741c1517000c40e2541c2e02101001002141d8102001910f4131040e80950728019040018044a442024600c040c02d2010104219a524540f90b0703c1c0c4010300382041c020307103284160220980d80d564234030005541c403d0180310089441c02d0300800c82c86041c0b004102e0001812000140210740f03416109041520030750000004603048040d40302101d88410064002e9401448250303200c0c50032850a850284003600c450405d03c8101000790714280d244504181d058000700700903410b200c6008209100030006a030514800d6105001034000b04440000d04411994001c42001f0194049110244101003102c110742d6a10f40508014003d02c520034402c0346008050100d2400b4840108038a0040080c10003d9400039001d80d01d4008156484141a1400913620 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 589583345 1250 589582095 589582099
    0x30605091015050d02060d05070f030b010f0e09060d1406011a0a05030402090a0605062116020c062505010b0906060a170408042117270d0f03050c070501030605 70
    0x400b81c20801407904203801100036202502d031a0a0050128800048590484402c0042510104100032190b850711071211022000d00b030034190480708080040401d641050050b00826545c1c011490325078610100d15065544404d01b2010419007a4010340c07914800e104400d00485121194502114010240c50090043e9502c05085a9454017005030b04500502049081555000081090b886140c01882c601c14190070b580e41d038441060a40c045060010701200c0c16400d15101220860390100d081007844400f150201d4452a0340b2003000d2150110b0150300500d86071081c086c0c010807206400c440482c5501300c0300d032a215a24003040c855a4131a040e0b250380020b10220148807c686080480b40c1c106005100003801d040c0c580d280c0810555469010310041920448203000700500401e112860382001402142009548549a141222541e50010490f86c54603014155500c9003035819518640005400c0c205480c5420094142da010062003186406104008512075000b0b0095208417640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 589584595 1250 589583345 589583381
    0x130512030c1c090e0103050a0b09010c050a050705010f050106020604051005061c06060305011d07051e12010905030d020a080604050907090906090807120908010504050705090c12010306050910 84
    0x10a8840095218449003003400c1c0086601d01040e0b81d0449201c04c1e000c0c2d8441c50042c94000c1103402d0124280714000c03d0201168100f00107030400c7d6a112040d00c09403000c40c2042c507118034582c0381490241c58000d4203400c03900c1c07a003c00083c0103030b40020030500031800780c020759409542417007940e819154210380483d00500250003404074560000c10028010b8043c0038000307046510390340c600d400d54103054003030342d612036660300d054588a100344042002442c00303c4c0c0c1402e403402c01e503480c2c142001481c410780e44150400c24241645075000c2d040440920341c04400d485d0380b00300c513000c100000d42044000310002603814001031b40c98140351283c14001c02400c2d005054252074481e21801170401c04804984650321042c4690000360048040e11100b8400c2c0c00400b20400d51600c000d103800419886410030b43e041c0b40900010a4010407644203034aca0594100c16243e0f02c0c0104118980b04d81030740501058078110000080c0070040e440b940c000c4c81c0c500700b40c2c3c401010b00300c84039098541c04d0307081c010766200c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 589585845 1250 589584595 589584613
    0x2070302060d09121107080604020a140d060c03140a1a04050c0c1b010f0c0b01032303030906060a1d34080402040605010c050c24130512030c 62
    0x7400c0006800c03240c02050340814a4842590307040e07610607052002e0004240102c5011016044c10301240020b407280000030304e5036280c55000245403407124030420b920030a010a0030015500d0701030a001c02203401203400d22080183c41c400038010402080103010319200b50f00403a42c896805e006d001d81002d001d1000410607e9210200402001c0207000404204c404110b401a03042c014000d80d00c14481240149200030448400503200c0c601c1d140e09101000340300c0c040500003400300843c060640c4d8021141d91090007000c21091042104030031001a82c1c030010003045641a000580701d44100307015079244d03a8165950b5081d080d40140d544080a400c07168400046030310008070140e03240b03080c699044562030f001d4a40d0080000b524848480c0018130700c102044107608141c09503000600080c80c000840c0307416a283e0030344413009046018450743d03030305d452000b0f80107802001c503400c3c43d41d48004039985d80240d08150000031440c45094082d0584001000c607110b0702000741c66006448401901c2520 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 589587095 1250 589585845 589585849
    0x9090307030806010302130605030a0608010204120809010215040809040606020606030a08031e010e01081506100e0a170d02150907260a03080a0e0c060a050d0f05070801061b0302070302 81
    0x702d8000c000d81c0c1007590912800381c80042610010006010315106c855403420144a1b034802c0e01c000b500700c024a43c0c01000100003c0b290004400300b829044095642c50700782d0940102d0074290322001c00c07103004440200f44814072940790000c09100c04100d9040002c10b603202c20523600c8020844105605400401a0502040d01c00c0300441d8018030410f0f0340e00543c1c038074032008140305000ba0007900c20f942040005022000d403c00440c16120449000005103280c802c1c001143c111041c103d4100300030800401d030059031504614000a080207a00342905410620260340d0b079101c074002204014440d8402c04503100040c40c0480d4040c1d035140011300f0405081c0300c5060344048039a9a4031410b1150031003100d204a0040c4002c55015109a60f5400507080010041050780e161080324685500100050900340d40c81c84212241021181081a00d036a50300144000030203a21103052101b50a10080001d000c0d805581c0c135042e1002e82e201d400c1055090240c440c0301c0d4902d8a0300401580c0004010f00240c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 589588345 1250 589587095 589587107
    0xb13050f031f11040905040f021009290d09051f0510050411040810060303080601210f020705010905010903170f01030305031302120d140c1506061201230909030703 72
    0x240809448a07032a00b0b0b9650708190842d80221415a15848d80d0304ca40004c40ca012462004078008910f40002c0a90810301644007449480078218030035500c0b40c440c400b150098400b0f40b184510600f034100a100f40c01c2c14455122002c0480c58005044410140c0081c17805c14070855010300080801d10a1031401c01c018400140701c0c2c2144e42c1203607481070000103440d1004000c0b10000c81402100032a0303040c0355140240c13240b24041d10080c148100d428100180b900003580110704400d405601040e120000f00300b4800920134604c01400369401c0012940a00c9015080801c689111303649040055069201ca400c03da082035a0a10010101d03c0041000c20b20990203540c0080c0020700701c020a480030360004c0c2c8045d64031500d0700400d400000002d822142c11803045a8800ca00e40304940c90300d0540c08031645c8580002c80c6e0010f050b140314001c078249071104416107100d200903072181482035840398105014480007600e40ea5440c10b01649440c000e042071041f00c0d01501d2120011810510a0781d019240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 589589595 1250 589588345 589588361
    0x6130e072607051e06390d0f031b0507110301090210140904090510060b0a0e0123040806180102090a03150e1b19140d0c0b13050f031f 59
    0x200c00100c02d14101550741304000c280302c01c076070750340d0381d200030041603100426030043c1d046980c6c040b0030329900d11902c10b004600808914a0307450502c0c100005580c0680c0100314806207100002a4408601c0499030020000e04d00d01d03000d4651024070071500b8040602b43c1d440903000942080c018014411441e000ba030901c0c11b02181e4001305402c00c0244004034080303c408120903102ca030b110300480310009225115140103841c1c0048540d140513080318000d0000d19010030410f041103420800c02034109200a00b100c504034645440075900c541e1340c82d29035524607041d10550b15411503c192201185014400c8030004070000d0071207041035256403035407038200d0f800c1804020055241d601c20003511400380000c8402201c407107442009040054180254403048203115a5041d01c003050038800c40741d80c09030620541000b190110200d820174586000300d40025031009a4100c0f02089080000180813070000036070380180e4950005401020030560f40c3d003242c1c41343e8001410b124a600c110702c2225088039030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 589590845 1250 589589595 589589629
    0x603120f130b030a0f050a0c1d04020c01090b01032d1106090d060501090c05070215070807060504060605180f010b09030705060c03040e010f0807090506130e07260705 73
    0xca80340d403120b442045a004460086210340e480f0001e90000c006881480d80000008004201f0000c0c05040508200100b100701c0c00482c3c02c51807964031035690f9404540c024485c00c0001d01c82044140352280ca009030038001224922503c284a03c5061142070094120745043c04420a44620a4075584840c002d03501a0903001202081240800d8603060140a112880b401000950390300d00540b52003200d0310f5080c40410404208501e0015903200c600141100c02140c60440c0d41c0d01c5140b4010040d84100e100080c055800c03e802c01060001d66400007046034003d60782c0742e01214002610201032101201c40c00a44a98140148074401d41d100260181d40c06c0901100c004944070400540640c012094405040e4400603050040c40d40f00c404590060074801a1400020b05080459884000703e0007490005a0f4400c00244071f6529000d03002c00f0001251001c2180301d2401182c19120a0903024051213035026603125000b00c0250240c080710790701e040e0003a2036414180002c00565000c031019684d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 589592095 1250 589590845 589590877
    0x9040b0607080f250323070c050603330f0907051e16060b1507020604030f08090907020307050d0e031902060408120a121a010e1807020c0102060603120f 67
    0x90700050780c940014003480c2c006e450300301b10b4a4003a8807840303144201d40f05100e00240203000000000c3c1101c1641c0c002c1d1281100c01e181c89680700ac100211410a0b480b0201c29a403400c0b96074810001e00a000e100400310980328510002c0201085c082d9078001a5143e400003482013000781002900a42c901943e0100700d40034030b15050707401c440748803218082082910b241d659005440321034940900e001d400040c80002c01801d0006980018840b07002d10b03c40500b40710702c80300100f81000140d03c01c60300100b030000e220780e00074101200300a60b00e0b04940c0c011038443c0302c0c01c0c480a181c140111a800c0e90400002c0080254921100c0d1a40312100b44d410100c0c0c110b18248000300d0017030400d00101410107400f0b42d40d103850300340040004000369098000e0a4080c1d1801200c900740c0c2d0720004410300c68050030b0800d60745a50b00702010402e00004040d80300000c1c50714030144060594082042c51300d03c1030980c00c0b5401a100d03801010b4458110440011080b00c04100d1082c10100180c042d000082a9030300c92 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 589593345 1250 589592095 589592137
    0x6050403020f101a1507031b02040f02220302090c0c030c0109050a1a09101a03010f0203102c040309030b040b011a0a020d11160b09040b0607080f 64
    0x11030b1612408200c2240fa080d140c0102c120f100c8084505003982d080b00f05c41c005202c02e03108040308003074842c103440541040703101082040e02c515086501041c2d070780e01601c10002d0044012004000b50000b601302c5051450075000c50003001030064040041e42c1e0014003a00c81031b00d58800c0744580f60301041c041d00070346c0428480f5541c0c0a03020301c1030074200c0b4000c10103480c041825280040c221000320030b030740110596000c18003842c480c001400003100076840300300080c031100011280d40c2c40c0c00045089170b130641c20030412110245035500914018500301150a04007034441403d8060104a604a16200814400c00100c4460480c840c3c0f80c106001c2c0c00d1016405880752181c0910f244208d4095454503002c800400031f0a1241029035060044001d07401c1c1042e419801c003d40f036890307121010082066990303040c41c40f40424802e41d1251804810080440b42d503c5183c80c501d6007094a0040c41a850810201030038108281103904507a4000442803801c1d0070005400c1da20b0b0010b00034a480c0488804031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 589594595 1250 589593345 589593373
    0x150e07090603060c030509030c03031b04050904060e0d0e0f040c030905070e04051c1d150a020f011a01080f090111120a050a11070807060f020f040806061008040605040302 75
    0x404010b54050b2001081c0036801c50300244c02d85031301400350501d41e442000844000b400110950b40c004041012021800700340480003407050050360801584441038101344410805c9984c843c40b0845207500645640740c64884055481c3e544d02800680c004501d030003805000c2c6815449070350803421034103001401044d50b441c1c01e803a01500e03030051003c1c80c41600610082c0a41004000601c0d040c030700e080350b00c030104035600629614545c0c8101c0300c4c8040c10351030301e000342d640d5030841c0e060345600100b00707070f02c611000d0742c001d40d110341c24011000c031946055040c0101380030080c42c01c03141c6e80041e11000302c2510355010280445130020081100741d580c580480e54251400c1c1c004005007485002c041540e4103224009004941c00601503c0c075444c40c004071000d480005005a4800e640c205d6500364440c00305040142c0a01030405110362914800616007080041c01000740c400d90307007440200d825642e1010709004004008002081c0840c02a80008002450a40010340e00c180320340b05585240104070b031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 589595845 1250 589594595 589594601
    0x121c091d10080d0c1509150b0d050102031006091208190201090507030c0e1e070c0203031201081f0e0c040207031e0327110925020106170a150e0709 65
    0x284a000a00c2d45042213081c8260b41082801c1e044c0c10701010004082c1030f03075801c0406c0100003694811745407601402400c0d0f6680c1c801c2d413690a90050000d40d60b924001444205901031f500840d4081080090b010501d8020040607850f000d40c070000b40d501c0e1000e03480c00512529601c05215003150348425104000074030038090701e002144501c0b1041c4046007090042040020002d0401049406550a86095105c2e0056064200c0c40c14146000c0381c981b1030010904511665607070410540c1100e0000424a0b00080c94800344106402150480140030703601130160f070030640041e00030390700094240f025460140e00030290540300b800d0031003000401c208080c041440f20322a032004280c4d40d82500000d0b0a50300000d01d0996028012552045010755800581d03601d190043da005032415000582141d110701a081e0256054201d040141610010000d001e030800b4040e4960300040b0308410039084070700244102080d0780c0b1940190721002080310710001804100c40e0b515152040307810000e10040c0d144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 589597095 1250 589595845 589595863
    0x1d0127090b01060e1f0e060405031501030b070507051f0207120807031a0625050a0501052208120a020d24050a0302060f0d0605121c091d1008 62
    0x786031805615000e00078140b48001d80705240900d609415002000c02c504204600204850514291400c0c003200440c4103401107811054041c0700c0c11002e515800c119240982c101d911812000c20295100c0d90304a03594010404010102d0780010000807a01070320682013028100038450041c104038440d02e078840c9070980022034801080d120024403411640c14007405c00c1044081842d01c12128515002c51224800d010309410f010f8000619008a025010050900707107030410122070094480d41807140c001d04c0e09031041180c525000c8501d0303d0704040c10013800c440b141c21915413400d10b0540a824910140011b10b180c0d450707a420842d040c95038015104821026480c01c2031440d042400b400c01c3d80c0c01d50b589404c01480760000d60350400041e9a0b40044030070148140448545a0a2241ca15806440290082c99000c03001e131103092191400091010062512540c15255007441c0b1034027603502200e10301801068400c0500f2080c040b8265441454004145041244040ba520038105017400604 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 589598345 1250 589597095 589597103
    0x3020f0d0e060105060309070501031508010504080a030605150f0c0703050d0e04230c0c160311040506040527070f030311060709060207060f020102131e1d012709 71
    0x70301d4070458400c10410145016080586249141d41000d0035a6035680001d486024105030301c50001400c10042c0500b52001852010000c0c021414540b42c8011340e90011060a0f001030310f4a0800190307840c20015411103056a00d0140b49030038a100c0340f04009a0101c00003441c00e1051184c0000051400c000c506660f1525588503019406001d00704401d480b40344070008019901610401d50039000c07804c80781d810103890f00c42d95035100389811089041811081e2501804441d00c40008144400d44c01ca030311100808031010021507803104200b10403680180e8819040302070007200001400318114020800500d407400b00c89009569100030900c00d44c2c0794204800007000c600c101c0e48000d10801c100e41d00300304541480300c1c0142c2040c50003559035405204500401c59191860000b0b28000e42c102e94820348040c20034040580c85440b0f4958844142c403840800c20f0030b0040006049403840d02d4401040003880c1c0141182e486c000d074a0b02c81504220fa50500c100b002d4103010060745451007131040080c0301d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 589599595 1250 589598345 589598351
    0x70515190921110a0f051804021503041716060c03020c06010311060408030d15050a031a250f020d0302070809120c03060a06030b010b03010321030204170f190803040b0703020f0d 78
    0x2000e040c080c1030500782c80b00807a00d079a0b140c203100050317070b0758ac5110f02078100c0c40f852281c503076031141084522044002401800400005000b00350841d0303c0300340c1c4038410700a031020300c07800346407803000c5080744244151880160401401400081ca0108242c01024402000c060401b62500381c2c3e1030642e07104640b5540013a55900841050385152042d0400600c011612411454a552540c0703007255008285810711410703180010b0010820041401c0204405c4040300c1d04520346003801500c510300070181c61000d441a40d0844030180d100303008a81caa242d204801c1c2d82003030511014405800018074580c2c15034040c1201480c0107480402900744560285040447c030a80b4504065600740170603040403035074110410041c0085000207043c100400a0701506014001403040220b0081c000c54104604403a0740c1080c0c1c40a82a00250700c9000051041c1074a00b2011011a8040c804010000003010403e0500014003c44d943d9001a075101407079007070143c40c0c0407045800c1a015440460700203100e0f9a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 589600845 1250 589599595 589599599
    0x2090a14090f0408030f250c020a09020a02070515040e1e1005012015094902120f180316090e070515190921110a0f 51
    0x40c00320402070b04095003040010490806440d01c0340903100c014080d4001102c0c080103d140c13031582d1850104000b501174440700084491140052004031601e100740d1060286020100d0340d96150b00c02c0b1104608660010124140b0304428001052480c0183c03c01c0002c00788000150b021590171203500c15060544550600491042c40741907014014240e0540e440e0240d01c01e200c40d9030080494845103441c00c0b61000c940ba400c0380094500344101c01024180491102404039a1400241801000b0301c41e0300340e945141c5040b40341421031b84240c280d40342450b9004000c0e2010070440d1941c80f1000010340305a0711044804520300242c0e900c0800701c1d5000c2500003c0c500c001c0604c03044a2640725030102c014000400c02c59810f6800d040340c0d8011b50128035501c141c0040344200400055008003400740c40b05015181c1100d20285e00d8110803102c80c05003048540c50281180300c0d42011040e690802d007118000c2e140c0e807000020300030740100100c4c0c405076a01032450050781d410010700028080f2015900e40f8038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 589602095 1250 589600845 589600849
    0x90b0f011d010e06041a030f0d020c040504080f0c070803040605070308010801050f010306020c2505040501170703030810050d12030605040207020a121b08070807050d2402090a14 78
    0x1500794081d010071409550700601a500d40a4405500610215008141200303850100550064405440c1c2ea05200c1c003644182040b001052a86001e4115001c1e1510078071000f0900007915012200144903400422400301101d0b40d141c007400d1014098000c45600b40d4868014a1450340503401140204a0124103d410580d110300182d02403c2200001d0207641001030340b2071008001800300400c0c031038010a03000490982000054860354001c802450640040d03403543d50000d046000316400f40782054000b1541c0d0090712282c000034220003004006072481c54604880d0105c0c0502551249400c0c803070001080d03074521184000c0c1601684260b0300060740b404025084074a41e90000380603500601a84015a8500340660300321b501c4071104801201c11303450400441220990061441c00b0200d0010581e030340005002410f4400c0d643c00c6411f0749495000b0000c0706150220300404800d075510004030400c0f90342d03a11170070303c2c201110f002d41005100000609405803039004028002d1083c0b004200038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 589603345 1250 589602095 589602119
    0x5030309010f2711040c030509071706070e0d21020706020f03070206090a0911132301180302060a0f02010b0411090d0f06020f030103201012090b0f01 66
    0x72203500c010800040c004514503180c40043c64880f05400c1c0109040d21090100407180400c50070300042007000095510035024000302021345690f03049201303244d40480d81518926840e031008030144010724482d904c6040484e005c0c1105020590010148240b84000500d88551043d0b0781ca4441490110040c11440c02441c18160b58801c0d0211340c0003620eda6034100010084034102a0113a0380385540d034104001140b2485102e40c8001d141d0b51501ca0380c0703020400c807100038205001ca450014002560750300000007e0316400d13400403181410000f00e03200598010702c10800c01424940310342c0203840d601e40000c0c07580d4020700031050120f80c0d00c2c903074044d000340d0a200e031881400044070f00b00300325201000c4200340c90003621f41d00b40c0120350304100d0401340400403080303103260340d800001590b603000744802c9058260001c2c44103c034100740305682c0c1040c0c00071041c805c500c43d03070300585400b5201245a0b0222429064140d40311061544d60301260f012485601d825442204081d42c103040030b51400d6902020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 589604595 1250 589603345 589603361
    0x1b0102160303141006110c12030a0801120c05060c1e0309010e06130603020f04080d0f0f0314040206030604110c0a02090601022418190b0a06060503011802070c030503030901 76
    0x400e50f80c80030865141c0c854103440c025600f103880c150f407401e0601d40d0003d04d040f044080032548840010403000083c540000280848859507581c10032036662003524000740010b5480040000380040014415030030444080c003030909546040b21404480010410300301d401164100c0055000051012015604807984031001c1000391140ba01d003185515000d07000083c41d0081e10101900000d8a550710130840b8183c40c0906400015282c415910040203890307101c07071131480780c00305000c2200d2075822406403241e4000c9001c0641180b505945590800c0156840248055031169441e641044841803010250103204580002820000010f00400c214114001d009a0456001c1070070440c0c0c0541510a44000c0c0088081350441901d90f80f410140c10f40f0b04643c420304610031030101e440c030850148154005240140c5110461b6121115280251034075400b0b5940842c000304010014800d040000950500c9504001401c00320705642d0081010400d5106460135440481803041d250004c0c4140aa = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 589605845 1250 589604595 589604621
    0x3032d05011a040810360b011a0904050601090b07061a030f07031b090c030b0109060201020412030c021513031502030f1503011e0c030605150f1b0102160303 69
    0xf0401e4540841da41da1280d015080d45a125142c03002c4d554442c20820129460444a03440343c40a443e0119982c410000100415511b03141b10600010309002c0380e0104456035811203c85518124112082c040139201c0504458100051500d000542e68242005402036612400002c103007090b00031003840303001c03144070f40d010320070381080c03204420810380000d41e0760490b0780c0005000b081440403c07034010814a2039006071400741c180240100a298554490006018242c03030700b0300c2c041d8890300100c1c200e00650040d4410410350483e04401b0034061089100010710040c0980f00380c40c0400031060f8260059001410006c0c2e160f1001e0082240510301160070740d00c032000071401d40c5805041d0840c4103802411940032400320341c0751006075407000c0d0000c00d4110b0301f00b842c41c100e11070304982502c0240000f140700300c00240b5229002c165807521000001010005d440b089003405072444003001c40b40c2c4100650300744c61100c0601035000360020f0000d801070039885102c8401c04040740c1000741c2a0781006d2600c007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 589607095 1250 589605845 589605847
    0x806090c09060915090406091a280b120106083315211203010f09150909050105070306140102070b030c130e1f08030703032d05011a 58
    0x1080d00c0d20750540c020380c00003049546240302e1300c442c00c0c0005400d07041026a81c00c40f56880420090280503001108a144150305900e182084000c40b800301c01c1d81034400035403400c00446032805101464030148009a20b40f807000801501050000c1d40c0034042040d00803050751140310811030304400703201c51462201d02c80c01c400f00c680f500a8881d00d0b0080314aa000c4000306e0b410780490f5401e0100318242880e000040e2612061342c100d014100c428121801d4035410912a1440107862140c004003980e0403680b00e0060a110b040c01c06a0103000f41640100140407200d05180028801e0068000e0b05010350050000003480d085c0380c0402000d84545401c40910300320801200103203130340d0000311703002114103807400141c5a4a13001160140c520078501a01d4011350300c010080703400101c4c2e08600d4014112125a40350605444942c07000101040c400d003a00d54005000f10b6000c1fa00070b400c111a008a460b505514a419210807000d0417007903642859070b13065403280140812102c2c5410b0100c42c40c1030300406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 589608345 1250 589607095 589607113
    0x605030a0c082509050c16050a060e030901080105150f0f040509100b030a0b04020c070b09030f0a050d0e010215071d010305162a0308040b101503051905010b04080609 73
    0x20607a0783d5640c4520000d8554502c00580d0340c1982c2420303118640d503101d0700c00340c0031042070070a10350b51058411300b5038400b0714020034121180000422100070400c10784400a59a01c2c190030003181032036030030b4a902103a5041081c268181d800c00000c3c280340400f008001c3c1c40e075080c1814024510340040c00882d0802090000b0300110032550181e99221000c94400f1810500010118000c1d0003680008007442c86040c4001c5140444000503105815058044520b84a480c6442540e101c0341c0740400742c4550040120300840a10503105200740c0d10060048900d034031080000c000442400b1219440040d8050303842b2900c445030000c1c0c0140c010000d10b4180503a0070040440020107540480c640f01303010020358030b110300b25684200d5130001443d040e0940c0d05034100d41800b62419000b04c0341102c0d007040d480c000424000d0295000030503204c508000100704005280140e00400e009060078008603100c011f011071a40c0b060003118041d0054400e0a91168a4805a03515000003c1c1c50041a0303044510b41c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 589609595 1250 589608345 589608403
    0x180e0a050f0d0c03120e0f010f0c0305100f0302060703030b032b0201050121030905061201030308010f08061305031303030f11010506090412090308030a1b0806010e130605030a0c08 79
    0x18017618880c400c40010300f00321111601c6203460a8030003404019401c01d090b10b0181901075101c0620840541c0301446a60342e40b0509654210041c0207042940d805c10302c052000d41800c1c0003034401e0922a0030000340e03000c0b441001030300d4500136110b1603458500200a00300d40c201c0c60042040b20000c240024006541400400c1822421a400884c4080341e44888401030611034210031004140207000503940300e40c24040008420004d001c03d50108030b0100000403000c40400a50003112450009410241c4461044101c070208600003562940720920a000321101c9c5030030a5802188070b510f55691649850384007401c0c0e404c0070035010980e43d00d000d00708401603e5007a00c0325817280e48075090304019103c0380c406603045c090503003010303061010100400c449815280d00c48000018603c405085590300f100040f03400c0d200442c0c0b01030005d41c520b040ca1303e0310b01380001a0390014060300f03004110305840c0c80101e442d194a0200646180024180c100403c4005103d6448205401e00343c10011100b41c0031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 589610845 1250 589609595 589609607
    0x61c1a030f15130b010b0c0f0a03051210031a0604050606040602060f0709031a0a060b04060203090904020f040e24060a0e04030318050a05010c18180e0a050f0d0c03 72
    0x8402140c42402c40000308a002c000940640d40f40d84140c0010751561208258000e43c1c101c034040b42585c0c410b100a940b01d281d800203c03100b816925a540c1072070a801490101c082c0200902140c402c80d85c142404800190300f2050032004511112602c809868408201f0081d01e00103040f6500580080006008039540455520741c80b1040260170180ea894688007107800244550004d04070501c40e4016a8411600700040c5001300307018034003408034640310304c4030035210720480c800c01c1c025038020881c0100500b0400d41d4664460f000802065a4021000c04102583c0045020300080d0300000350034841001141e00100009101800100e02468032001080011080c1c1c021840e0000d88400020300b058441d402c803900d03c00d000682c08885131120b18285a403850000002c0b1800c0d42000ca1218001d0320961074007071554160509001d90b20301d01150000b2b54424501106101c07502e618061403202c0c01040b81d8003416100d40b00030081d44180716032140c1000384086a141c00c10a802d139050011071f030b00c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 589612095 1250 589610845 589610863
    0x50402090f010e0312040f0608070201020316081902040609050108150109060c060216080d050f100614221a1801030203060d1b06021905150402061c1a030f 68
    0x20802c41400d182810010345451002c0d00c821420800014007c44c84000c14266142202c0c0992650350691300d400c001a0700b40e010884402c10f5810808940c0f08840341b040541701d42050481e0a40b1014140c4900c0700c0c010780c0e00580084012170780c0c400b01007104e03503400b48030369502c40f100f5178141c07201e03468501c0000c100c0707a00c61081340c0400c1144030305c610501c00c003a030440f481c1e9442c8800f489410760b03480c41c18003859042401d84210103460180003900c001080001c0c2403203480020f00d0b198800c3d003041019201d03401404a03070100130409004c641c9183c04030210389100844000c000703015261a00700010000c9200c94100d0041d04814403002c02166046945a51a0b030000d09000d41c4030ba81e4a004038240b00722140e0003070128204503c822508180400064081c0e40c10355007604e8400707090030540c107017403240060000e182e54020001c8200e1654030020064100744001c1c42c251615107605003484600701c0a101f01c800c003d5a9000300d00c903c844101c4008542d41d0194040d01d40d641496606a44035500c207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 589613345 1250 589612095 589612097
    0xd051806131e1401030903170702030c01020d020d06050607080304230d080405072115021e040f06080402090a0902010306080a060e01050124030f0b18060307050402090f01 75
    0x125055100e91299510900034003420301c0b0399842e0140c03408003030014400b94440c411064108641c2080c681d4802c1c000c803501c16806445070029a481003d0817005c1e008002d0400c800c6000a002c05000313140e080c002040c071040c111401507100c5005410100803914940d0004c0d201d0881001840300003526441541d50141c0c1000b45c003980049805284050340788070102c0c6c01c81d907008034000038000301d800445c501d0103240a001141e0030161280402030300c1102c40340d00030f000035140d1550100010088062030740ea141003000e025003409000552480500306002c82c08000d03000205092000602c1c90582000a003014500003490741400e0300030414070400503000e900c105403111004019039009420200003040a502100c0a2900e581000070003004030710201c0702954201400010341150496018242844481c00302d000d0910802c020340040a400d00f03408000750301e4290640c410350380c18518000454280e11009000c0c941201011309052031500070600c90703841409082c08a407110002d880340b651003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 589614595 1250 589613345 589613347
    0x70611070b03041218050d060b0315090d0f140f13030219030507050f1f0903080703080906132103141e090d1706060c0114090d051806 59
    0x100054508180454020700ea60510000c02e00c01004058079030702d8010700840c0d5807a04032030b070207251030b80d10101c45e072090641c090340344020f41020540e26804154544001002c45448444021100c0200314003152032410640191149010ba03580000083d0b40180852400b90000501c0168400b00e40c0a110740c1c0003410100070540048078510580d4860203150005d1008003c2d40480102072041c00f12408226070703e0045500015031400d010701d108140040080019800d104007036a6615120b040182243c02c00c47c1e960304c0040815810f800400340d17917009507182070341d40c600054210300d850fa024040340c4206450040c00300c00700700d80708000c6181010f4412300710725508056008502400d034251f1406608001c0750240710034003006002020541c88c2c800c0748100300303541d0700b10b038103448c1c10003d081c0d800490300e915803d6812904001d42180c0c0b00600801d03850a190304495180c0c21a40d28141c40c050503036014080c00050fa204020302c0c01c001510746001480c2c0948000c0402c080003c1800241c05054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 589615845 1250 589614595 589614617
    0x1106061c06141504060504090515060312070b101202010c12030605031b0301050708130f030522080601080c130f200304030e040e0c09041103070f1d01080706 69
    0x4058100500102c00c12039500082d080020031895110b5100404904c40e92800c0c0c030003c0c2d1824140a065861908071025014204004070480c400b600020851030b03150280c03034070b4100c2c10610440a0412540240460310303061030840b5040d41c4403001e036044261450140519040180e0740300d00e0a0540700d80c40b0031040194424500c4c02c0c0c4c050001c5030009030741402603914842c0410214002c23801c110004030028040e9840e05075068a41e0300c0d0a481d80c03d004c144442e0407201180b07180d0f030b100340418424549030f8600064007651003050078507400b00c1340446800c100c0c10050044100001400b406294024018007605c00300010f017109a01484074010a8544005050050742c95124410702d090030707040c0049120010601c8078071688119012070205100009071070307407424184246050000d680b4014070050351000204000c139030005004442d8140e41c00d404d5105520305010000c010140d4180720000030703003403e4040480d0520b00e8400b54160421500401005400040c01c0040b075100d800c207196a24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 589617095 1250 589615845 589615853
    0x209150105130b1c05010602071a040e13060b040516080a090206030903030a0e0309103027020105091c06140901050901090b0105060d02090d03020d1106061c 69
    0x100400c1000950709000b200c0c0000c08094500c0280700e240103440701007000380041c1035038204a550038003450340140d00c1f920040c00591f503600207028420321a214003d0801382e8911010b02004005c4500c0c01c007072820504c2c203000300106402001c2000604036801d110914101d81240b00852032800c1d1030b000c0005190210b202440c56521810640380c0181c00182d0f81c0c9050300c5110350741d600c00c0d640c005816260840700503202c0408401d549101100038400c04112183c00300c111107880c6240d404964459020ba81d469030b16582280c2c1e0082c0902c10540412902407100c015190401a00507188903c83d030030008800603a0300c08111802c0c1503040303901c244031044500441401d0917210324001e105d240342103402c00c802e8043d072410350f108485540c0288626580d40d007105099410405000700020000740040c000d518009000e0b0200310702d00d141c01800c0200800c0000e5020f03c0c00d42080e005a0403074a28000010b90002219040c0c0c140100104080e0400c0400301d03003070110720026010241142c0c00c1e034030100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589618345 1250 589617095 589617097
    0x8160c0c05090109020a1d03030f28030b030f031201031b09091b1e0e0a02070c030804030b10030b1b0912011b0c030206010b161e0614040209150105 65
    0x2a05000d00721a0b80d03580c58040c00c000952100f000c14000c9034800408840d900d81081c5220050040600a0b50901c2d8000d1840711a5800002d01020f01d865101c0c80342130713071692800f80f499030341c02d8070380d40450751080700020325003070480300a0000c0c4c035034100b001084000c1500381610b80c1101d6002041640d122400d5111404026040c0c10666869007410740c12070501c1030f030030380c5c420751541401c40e44c140f0715948214001c5c0008101000c1c81d159000d1031810000200800310b02d0340d0090400d41e02516100c041e0ba1541101c41c6907400807500c2180c00700e824420710079040c124030750240c40e5a1043d50303028110b403075051900e00700421000d01b03020022088070521348100240c0e1034440c80502013062604c803a154448c007030802c192884006000180002d0221441080344408064040c1c0181c01a40d0a02107000c006a001c04149030241800c81040e400042a4003482d2481c8150302191140e490250f141c0641601c03124091411490803a009100159507440303030351500240c90041d0a4280d682e4500140c5007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 589619595 1250 589618345 589618349
    0x1811060903030412020907032c07050a060903050c040b0607060c0306180f0e010c050d151d18030a1b03030f0606030b2b171c0b030d08160c0c 62
    0x500000c500051021301100090000d18404c686540711a521400114100c0d18188505581d078501013110080410703810f00e4503082600000d054601e103a44032800309044000c558481c100041300b1500801c18058140140f5449210846040c04840103180c0040c02078003642c040501440c0d92003140b070346c0c103a000b40d00c810003d0442c2000c6000051810000d4401401d06509285c0300c2424004089550103062080445416071500d55608100a408400d40140751204007010b082030000f00200d0000f4070361078510100300454003449828500040c803407050200035084402580c1c800d000c075129603078110350000440c6c0d0300e0300d881755089045403c084001d00079035840e03903011900d4620040795461b03168014492152081d108050403e00c240704c0c800010503889820102c00041951120004003240800d080e500c2c1c604424600709904034440510302100c0100d0440010f69038042900141414040800f03400c42d41e080942c07061034030545245140382d00d2516841000b1600e0402c400704030100c103400d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 589620845 1250 589619595 589619599
    0x31b0f20010603060b01030c02010504150c090305030705030c0d090e01061b020d1101090b0c122b1413030f050a03020705120a080105030307080403060f06051002150a18110609 77
    0x580d0b982d9080c204d00806010000780c0c00642409200320009005008280c0079a5011810801c1081d0240d984001072072110f194504000c03118900102040301003010701030300d6004901a5036a50444048240380105540707202090009542042001c110400d40c421304581407428074507200155100408285000c01000940c00300404464200b40003505007243c82e54a03017030b00c4201059840d0f1900460301c0c054401c0020070703a40030401100ca00700110300506010501c414500e52022001041e0300c1c01060038820b0b140000e59104000c500e14100602c905411038241384034401601c2d21501c0c01403818102c11048070a1100c006040c8007014800d074120f580c4c041d000011380745101443d440903c00b5038041d40da0500003c80441c004a41403501100f110721080d03002103410320301031459a84001820480703c0c510080d1399544000226521065580c0f482507007158094103640c1c850141e0401e50740800741211031500d1070519264000040c840c4030300704032a00700350b04500c001152800a425842103000440d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 589622095 1250 589620845 589620851
    0x51c0206071113061401032c072102010f030c0206060904080d020a02100f0209010203030f10030c0806060120150c0c0d1101062705040507090608030901031b0f2001 72
    0x4100c0c50f216407001007981c2210100302c0032641c3d1040114207071400506e000320b0b4030b0802c00d070701201d02601c40c0e5103110506c0540d05645519a890550159040310700800d000c804944541d0304045681c40901d213510160142401c2111140c407010095540c800286414080d1a455000c40d00340524102502c0300d610700c05405554813400c1c010025111004030f21706003401402c1000000c0303200224000e6a0304041e06034000c500b1695a002d2407880d9140c09054003002d1004098080b0107e042e08802070054031401e0000d048a00700710340014403200304000131b41c85107460030040c171030302c060081129003003c0803ca403003542649901c0040302403031144600e40c2c6214414452180142a005080580600c071028000c1050325500c0f50882e003440c2400701d040c00090300d090806e81d0340962640c004c41e00140500100d413841d030b8803424918100d841a801601041d400410341400a40e03160154884862965003003c40b818004c0c0000f425802909100905000d815074442040c11440f0241c10b040c07801410081c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 589623345 1250 589622095 589622119
    0x51b030901062309040308070509030d0e031522030e18010303020609030c1504030c05060a0203101707090b03151005120f0c060d0207020604030b0a0501051c02060711 73
    0x103008003094032601e5080f0f02d01240c184500500d100701d411004002a221008582d116070701140c28a00c01880e0406115003808001c0c81c540b41000030000e614055141e080c2c042c40d40a0030145050703a9150000100d2101104200c0c404041d02200550f1480c0c45807184442d00640c03070300303a0301c060340040165007107201c6c6002d00c0c1244288100460403030f40070b5000d44103507403120b02c18103449114103c0c4000aaa021040b5005505c801c40c2c1c0544e0b01078064582464032240c19500c0034200001a01d62100107a0080244020410780d11800401800c0b8420245201014501c2980c0c03100f0041c03080c1440f440d0381e210100442c0c1c6090140325035880c044620903003d481c5c8a07984120351503060003085d0090800c0744139950a40000223001601240c0c00c03005203c550411000c0203801d600084a80450b01e800303022003001629103c0107800038520443c0000c503549090141c22044400503480248130f0710006150b003035140c0d241c8100210590b0103650160740d0b0050b03403c140d00c0040c0103048080c0c1103c14115030b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 589624595 1250 589623345 589623361
    0x40e280c05091201051b0c070311270a0c030e070e0a0209130e0129100210020412120203030c0a03180804090b090108060709121104020c070e0708040c0306051b03 71
    0xc43c4106c84c00103911134101007007074124103640112598400d042d44660780500104004114080c41c4000040a0ba04486210001d200c9002c003c0340c48504510040c10078400c9070300ca40d00a1003c401280c0c0380c1005082400c03050169903124502c100780800d1101404205101120380448011840140255604440c5802c00c0380040002c0514841030f5444d0121004000c01004101d207003002000391911590b11600041050705080710714000d0542c401c08000740540da038140040c0c80180701140301c009001d00c0f181803640f0800e02c5c3c0c032102c00454000708204a0001806c10a84021105602e80040c194000c0c120800140510803c090488400800c00190100d07064000c080c801805940060a0740d030b9030070a0568409041c2c1e842030214441800612503c400003800020407401031080e85840702d4a040410100e900105145240e60002e02051140022100701550403000c04d103409581480c1684492031101042c0c003000704155250004510009840f200038003428860700900c591f64205016 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 589625845 1250 589624595 589624601
    0x615200f0d08070e0d0c03060b0102010e0f0d14042409030203010f02041701060e0109021c060f0503120a021221010b2203021f140d02040e280c05091201 67
    0x4083d00000d9000102e6807181c03d0502040101d654800c904078855400d5950b00c1d4080d003850490725045650396003a1082e500000c0040001c1025084054200d4424206008000b06a400b009039510a4100304c1003080014a5000c881c0f80c40051643d55540e00c0101170072500c10fa01540302a40c19800c000070142480110340c020000c031859900c0d5030b86070115508815003603600c2446400056001c031001000050502c2d0000c24206c14903070181a41660204502c4048414640002002c00c0402809101c281410400814110040c5010318200f002c0d0b024002d41da1001c003030003561414808501b105a04200c1102205043c40300f21581c1030039a104c117070100203034208030402d481030900304607010302d183d004440c1031040d03d4010b00100307085400580c0f07040d000b0080c040c16800f003015503040750441010380b001400b00c14400d00d101690b00c9245c1003000e00c0703010010740002c8900359010a03981041049502510594140502c007089004001500f40c032180030354030340d241e0007040c48005c00c00b502070198 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 589627095 1250 589625845 589625851
    0x16050409020f1b2b0509150304030e030303011a0904023624091809060421081b0c030a17100506120901020d0f0207060615200f0d08 58
    0x4842c00322000e228100d09a0b01d845100445048070111303624680140b42c01042c9074026070842c01c101d0310340200d54001c60f20350403604142d82102c05000c002d120400da40890f074180c03042000c1b0021030a5504050fa130111000300028811003601c3d0025130f4002c29216034056407075403480342c1c51120301c2206045848070000b0b1400a050b030715208202080b0403501d403400102c2c03000c1c040304d000a400080d0b10610003055034000c48003164010303402c0311074042a4a40800040c842c035508400b5200c035041c91b1404100740e4480548c05c03590768407244c1010048991240d440365001c3c0014103014507070b1290b806642c540d84124440300707080303020008003000015000310310300709001c0a080301a9080d0340d9042100181558074029254010320402140011203081000706030040c80301c0c0001072901082c0100c034001c40310841c01c0d20a40760340105a1105000007845004003d01104080c0c0d00540041007000705144a448502ca00c49403030403d280c00e503000100141c0d50945204011203400c51b126031f401400c030002c11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 589628345 1250 589627095 589627117
    0x31603090807351206040b0d151a060304080a090305250f0501050412060e0a150c020706021903110a03090f0f060c020405070e0d0605010f170616050409020f 69
    0x780081000c14590b8540383c01c10020980c02800c00031040d1040414803005000907030b1181e101c0c00002d4851b9500c4e03126003801d6124140002e00c840e0042065003d0f2401c86807203030800000c104000c00c003921840304507540030398802031480d0346010042090303071a01e00c5504054200d101e2142c0c0c41c4600d402c160319803d0000744c80c880c1311a603141e4940300c400502c0ca06001d294000f4009220800003500c0060380850460710505011132030701c01806050b4504401014240e45d01e194121689c082e0704014402c04810502c82e101610701c090408038065a681c2c20031074201e028016a0b2562014540f00310100200301d03d1381c03002d540c0340c50140c0c18001e20801b168060000d45244005000841d0004070100100b190074607100e070640703007035590200802820000c050005000c0701284071009940da000c850040c0b50b10400303000410754103004201d40c040043c0d030031503070300301c60048030040c58803200069040c4c0c081007038075841ca00111148001c590a01940e4806003c2c42e00218000f48403d60aa01070480e14100f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 589629595 1250 589628345 589628393
    0x7020f0c0d110d151b09050f0109050f03031c090209130b07180e040c06031104030305030a0207060b0904050d08070c0201080417041806081b06031603090807 69
    0x980000c1215000d50070030300418020a02c1d071248400d043c015020444140190558410034401d00e5000040d142e820b8003480c040300000c0e175082622a00700091174003402d816a03851048150340380020303000e0350041c040c0d5031080111903210700386c1e03650410403502c455195812040101700802000c00c040c00845ea000c84c8960100e0001a8864005410600755a030300000b8840144d11000d1054030201200400040d524048000c04102c0404e141a12406a0b100b82202c210a518110340202110070550205000071010001040860ba00c0740a0725044859513400603901d503100e1401314000c007071400c4000e400440c104104418020007140d03603008803542e92140303600c40d590f0140c01c4400c0c08000c4c4c0001d0114841d100800c0105104403028081000040d410614003134239650b400c81d503842000000105c035034440000f0700032280700380724004d20f007108080a1140421208000740721400000d0110700307041206c0c041b66804611a400582825402c144c40d641d0380c80003810f00040450042c2e00c1c034144010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 589630845 1250 589629595 589629613
    0x80909150d050303060a1a070f020d0b0c070c060e030307020f030106050919050a1b0309030e0a08030c070503060903070f0501060302090f0a0c080f01060e1201050f19020f0a050901051207020f 84
    0x1502a21f00402c40041c0340540e480c00c030340c9a0b43c14401a10600c0140e8100e0704e5080044002400300c85118069680d080d80251100c40618120f5410041500560100b010f484106d40c2d49490000c10366102e941d0440348054161004c07400301340188160f901807640900180e040c0031405000851099040c2012841402155905220401a82c4100c000700818056088180d81700f603120361310680e4058480d2400c144601c10340c40008034042d0303079a00701c0030769038000050442100700b04000850051505a0150000386805d0104944038014020003404044d40320b6052000c0010030f41c000d00c0035603401004c0100030b040083c443d207541041140d40c410103034030b0008210a41401484842d01c0f8105502d80c2d078034140e0070141c040390340b80e48014142d604080c2c0054103020211081c090f082c800d1340d800d40c50307079482d107080100d0031040b04842e41f50070365883c810001c2c20325081c444d004580c445246070401a03a515082c0700120780600c60f42170000400c3c3c4000c0203100316150b001c58080071108440c0e080300d428503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 589632095 1250 589630845 589630859
    0x21002010524030309040c03050603101e050910020319060902090a0302100e1201090b100305100213050607030c021e1c051c0207050a060c080909150d050303060a 71
    0x540203482e0b480c1c4003091030b88207444103a441c41000c1c000d00e070040c1c15241010004070204064815038034101c00402e480f6403c00495080400c400001c0802e0703040148910b52010040c1120181d0705042d603c049500c40c000282420b030108400c2c500c100c002c1008560300d1410070b8050416141e48645400c2c8542000000201c030241c82c02550a5030200810600701e441c510390802c980d801a042241e0280007100c501303c0c0e265a50707450100480100c9200105070344c8030b00d01d040035429000900126040144120600c00319000050540c040c3c05031202c0140d0f01c0b07945000d5030107684000e83c8119405200050070078205075011518007500c41c400d8403245501283c043c80715030001003c00328950803044030b000104180c1c4a184251f01300c1401001904c600c18200d10020810207401765940d000360340a1182004075040c0811a540140ba0a00d0041014480d0717a54088513403103010441c030301c0380414002242500f40041c2c000e012401000704000040078107881c2964a03034004850f000d07c2100000c000044513 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 589633345 1250 589632095 589632101
    0x16051606021203090c12010f090b092b0302160c060f030f1a010302070831080105071b11120705090c07170708040504050118050604061a1c050c0702100201 68
    0x20101c1102900301c024040007031080d1340b1801b0008400542d2100100b542c1903c0a1140d03502c198007c030504000c500e02070350768900e032030043c10052055454402c9165241c0007400088804075540340703005660f911024040000804000c00040c160807030508001070020f0304140135450541403a1000d004551444510104a82a005018400020042e04e2620961280d401000014412118a4103014040d807100007560807481c41c009051088081e034800508510603200002c01c80c560080c00326241c10301000b041a803a10390f901288015140c0440200001c008901056410113440981c0711081e055400740d039030b0303c14416207000707881600212305c02168000880b07000d0383d0400d4880300d481c0a1040c03011200d500c030240039a02e85609010204469403103024150080010014080d0340d141d050084108907440030340090f126a2030000c04000300c2100aa0b101c070355908404c035494407031107030742c5408141c9010100262401031508041001c01d1000300080c04d405070095850004000c07820000340c0c22 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 589634595 1250 589633345 589633351
    0xc05010e030f21040321020c01051509100302010c080705010902130501090617070608280204050120060402060d110c160b04061b140d080106030b0f1516051606021203 73
    0x2054401183c6c80032081815440450302c5a8200600c1c000380c000e005400c40e1020348039104292020100780001d071400c041030507004201054028603c61950b4000b81541954040c010180f01011a0b40c2081c80303000c1d4001181281c01400c543d137125484400440144001d0282c0030500e131911001007071203101e529400c80710301503541c0108070180c2040c10954030010000c00714454681036020740310003009180050b1800c00034604001d40c0b500d00344800034010300c10400800315800102404420700780320009100b030300186c040d1640d9070764641011108014040d449030182a00342d000405825042002582841c68030194407022500c907140c04440c1001d00c40d41c820741e00050b036a074212400280404141c03800b050702c02c91880307504c01c018002d0242803103100c41001c40491386000040107269003600820301110f904883c0c5040181564002803090880078402100704080826000c84126458a0303a00d0300c5030f0803004540d0594103510b6005c05100e818003030346005000b140d4071000403021410580380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 589635845 1250 589634595 589634597
    0xf01150903110f041d010c0905040c020a1202011d07050907050a051b0c0a08061b190e0d080c0609190f1104060906091d03070c05010c05010e030f210403 67
    0x750b0310101c60200140c2c3d004240d2040d0303200c2e81e00e50340101d60105520340030210000c0d0100118883c60901005040c220043e4031581c0942e0a00008180c19a4049403001c0003980c411441d800c0782d2000e50b400ca00410b65a65052120040d180c04070085041c0040d00c60200c6074110384c4007186aa400238101d46501503540c40c0004114140b1030302000c8240c1a01c880e0750300700070781d0031180e40251a8000801d01d807440d510082c4036402c0710090000203101000c031018803503800f6210301c1ca00300041c000124007580340034400301041351090b0546040d668115140784c80d1a0469138031074032440700306c8040d0b80b00c113420b4401c0b65441c40b4054a13070000d0009001031511094100c52210b010440a407a208003000940850310703401070755500003091100f40c07440303203201400c5880740000d45031a884403040b0480c1d6507100000300700e40c024884400010101c82207202a51028685440c1e034011515003140505860310315882e0b60b001c0452924182e0b0148130150560710a084026502480030740d84000701d614058270054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 589637095 1250 589635845 589635863
    0x11203090e07020307060203160806030a021e0a0f03060209210601051011010507091a1815040f090207060524042c0d020111120a0f02040b030f01150903 67
    0x2004080d00c031207540c041c0890040e20720300301c400d54030001241c0c0104c0710543c941801c240201d80d00d562202d11503901100943c000c1c001d201043c0c0024010f029040002440503950304001c035450b8903024800c2c2e0040c1070259030316032050b450745402030103508640b607034502502c90900c540200070600f10700d030b0310310400c00310150603a80d09100a12004c1515004004280404c0c0c00e14030841040901c03c0703502c68031550b666120498140f850600d030041010301040c290070700900205800e0b040a4240c001940c404841c1000904078100c40c95119020b903074082e001165900c0c1c8000362846440d002444540c2c4507410401481d51a550b00103002060b40c810003e01204288100019040c5940002d042501802050b203540645014110002c104036480d240329421060aa14429809014041e2080180d00700c0d43e007030000360b11800d040001e0084c0407888140e200c04008a2200742d1703a04403000b4010f0b80058940d603141501d01c0c0d00c0114020b05c03550f4000021460341c0840288110360590a03a68030200304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 589638345 1250 589637095 589637099
    0xa0f03020d02090d0b0f090d0815010e09040602041a040e191d0a0b070e1e0604030803091606050903070e060a0f15021615050705010608030d0603060501120309 70
    0x4500075000030600c1c01085508014420459507030700405850140300c0c000d6802c091500f01d00030308038a84054245040382c0e000c02e501108058000c040554040c8a410080c6800c440c2200100c1d1481e400c500303500c2d040000303041448244074481e00200181c0f440f0010210000c610b000341c4510601c100e200b1414901c110314081001002501d480b614003402040303021030703800c2c0800c00650b1000140c80440d030481e480b51101f02c00b000008410700383e21200c0c5080280b113100c600310200340540d000e410101d82000000c8141401a941c0909540181d80c00007440b50322441e10b81011a696001020705500c550781c0d100c00000d4840c030440484030002400386c080c000e1185419080f10706004090f00c0b050303010700108800f00d03060030b184031900001c080c60060300c0c0b4110040070001c0e04243e12078045070a9646030310024401501c01354000d2011940714500a682d40c01c030b0307040403401000581c00c031080d40d000000b8540075044164100c4400d4a001e00b6080089903039072000700700745c035064081c0100072890f03201007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 589639595 1250 589638345 589638347
    0x62310140f0d0651033f03050f0604050907090b060904020c0a1a0402060a08060102150c0d0c081527070518030118061808030a0608120a0f 61
    0x1181e0215607540900d10f1483d8910444034248410068007414000440d141d104400c0326011301c4440ba000c04896602e00d9a411910b40a049081e5400c100c5c103041e5203d9841d50402c4542c006100d001c0c84e942e84001c050084a010080180c0000d8400d40010625080811910718043c0324480c003c40c4408014001f81d403070600601e01404e4862f9500c0e506c01000e101458654031140001c0c1000d1941002800c4059040d00e40840320840e0844614044a0103004100045c0c446004403100010399050040d856035400c40101c1c80c10004000f020141d50b1405e0901c15084085006442c40c0c1c0c003210024448001c2c612403c69522004581140745510b12108814003810190351050401e0b90451001c6400b40d82102511002c99058600340c00142e400540700300d1802c0c040484480d810022402401142d9064901080c2c00c0203615025081d26900e568201000e040400702109042e40102200c1d140d145c1804001c0052005114002990148860490741d1000341c0d4100d5900318103645403010303c5041448 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 589640845 1250 589639595 589639601
    0xa080118060b01050f0d1b0c0b040201030902060405040f050402011209020d020f0126060109060e100305090c120609060109052a0409092303040f03062310140f0d06 72
    0x1000341c14044d0030014441c514911200030410180701200c0410060491802c0c5091403813050207080400961020b1900040c0c6800c02c816041902442c0101c1e07110902e00000f007040c407665000a5000b0300d02807034111403544039002227200b03d000b40c03900c0c010040d10f041200c080d07401c200380003940091752841c80401071070104480380d8803803010301d0250b076410401c409141404950485182c1110000300411010307680c80b100c1d00003c0c01180c0380101c076802c0004045440c00740e00d08512414192110002250a081080110100301d4010302803084815000d2200c0e0b02c03943e094680142034050322001085403040750041c58080c100341500b05901109080381e6108014544081c00c010850400c00010708030405d000b8012a20f00812952950300c03c1115080c116040c0c48141d0f0a4036001070208000c0704411080d684212500000d02180a00300d016181046c44004158108800b43c0081071081041c0c44d80d20368015650248001038483c1d0f2000f08005076030449601142d804644400c007a80003403101d030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 589642095 1250 589640845 589640861
    0x105060708030a090204020a090807080304180504030320040f0e0108030a14130f060f02010c0203030a0b01021f0e0f010501030b0a230a050a140c0a0c0804030807110a08011806 77
    0x43c00094451407030340010144c5e0320000b1000c0c001070360b00406002c2039909201d5100180560300041d490180380103600d0045640021810b0912a40d43c8001820f050013034001c3d035481c100380c095900014000405025454001c4e0080c03044032440300c240412000c5c0320104850603955004011800c022054204603440c0410744d101c920881424000c000007101004d0954010b4030740400701c485030701e003000f40007030200038220005000c680c10310900c202025004001c994104ca03c2020202d040409140181d2902c41c1500c3c220991103c180003014580c081e035404459051005400e83e103020911920047c26a802804003600d58140d207070114140460503480411410110b0b4a0350000300c0c0020341602d410300003210080d0b50035845d20100640c8401c54401c001c00103130780716061207285c00c0c455000d0200e8090486144240801e6004400074801400280d6005507885040c8550320009841d00309003032400020388a0145031201e40c0420310300018081d44941c425450700412410506841d0035010340540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 589643345 1250 589642095 589642111
    0x6170604020a17040501020405010807022a210f0f0703080306190330030903020a020904060612030c11040504031e090801020a0806180606121b0412030314010506070803 74
    0xf800d01e20481200c00000701d1049018200041c0c0351441c04c0300142005900a050104642260151480950040030b07000c14501c14480344e1020f440445000ca60300741101c03404100b6040c880000ca40500c440010000c5903c42000162030f1102602c0d0b480c4c5603141c003a40002801803005200240550604a18192103d010340101d2000c042d52612401d0582c03818000d04514078515900042c0395400159a1840d104601d190801c43d4074900d4400070340300c01900c0310003842040c031f81b00818103000c060f42100d00035103012101d500000180c0d203000703000301c07142810071502c82e001c0484405c00f07407502d4481e1034403954140e1142e0301100d1624540c090110b440d81d40d02c07810310841010115003804244041c001c0311825807501c6500c0d0401100300000c141031010b1031054003610b20108002900d498041d070729003c03a8080481c8940e203c2d010003820000e01d40d1450f03000351030041303000505018500008555507000c0d480c20011603028440e090324400090080b2500514200015070018809500841d070200d26 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 589644595 1250 589643345 589643357
    0xd1b0504020c10050a11040801140c0307020712050109020a0806040c0b09101107081009050609030301241103030408030412110706050706111603080c12061c06090c090606170604020a 80
    0x1c042010006d81d0025042904240e54504d48000b0b4070172a00d2820f038011001d003010038250319041354025990b00c001d000305039a071100549d00b8000c001d000d401000031540d009183d8542c6549900d04160340310001c5900350382c101004400003138000b40c5082103544100001d40403401084c4e046400f80c2e042d5500070010000741c440d1030000540102c00f405507201484200c0c00100f008025420840e16051001d00213a40359041000100310194001200013041c0640440d46075a01c010541e094a0022105074405004c5c0000804c0104111400009621891140c07222030700e44c02034400112502e021241c03402100d40c1c06110240000d40c0988060030503640f0480d07000c28641000288442160040c01021060083c41c90904c2d0815802c1080103910040e02c406c494103000380034441048140c0042c00d4980903054950000301c5e001c08040e0808d85a540101060090020a20f041a03002d0b12611070181580e20b4141c0c0421824403030202d801c4010b40200d81c40d802a02c030202080f00940c001c0c02d1800034403917 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 589645845 1250 589644595 589644611
    0x1c0605091b0901030201081305120a03060509013006180303140f0a0509030c0f160503150c0a2706030b0604051e0d1407030b010e0105130b010e0d1b0504020c10050a 72
    0x300030002942da0f5516078010304c2d0be0326a510707400340035207580d5001544654141030040c04000c54180c101c0301c42e4488506051480c0c5404040c1064840c001a4003a10300c9080c4030b4415914007061348080f022620940d0204003036807441a010100b03603001d6031a2070b248000b03400491201400354120b585c020b911602601c0c0792aa5482c8040d18014410350401d155401c02c004990140e000991003400424060b4041e154005000029401c8441c0c01003900000c0d03031000c20100c0d03040780308003030070b00602221680c1e419042c20501000040d0003424424080000d04061904125041580c04ea800303c0b030001c2c00000d003140e2407040e0151250801daa01681104040d4a0703500132075001008403003038001c80c00140180b2400c60412007172603903050300181503d48003403004021a03100c81448800c108607050001481d404c0b244012038500c01c080301419880740c41c0f0b1081000707000c1c20400c0070119140a0303903000026981c40050005074050244401020341000110504140068103d01c0c2d010b0610440022500c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 589647095 1250 589645845 589645853
    0x1504030b040b04410712081c2f18090405160303080a0f02041d072705270103140304050405042a0e01090b1c0605091b09010302010813 59
    0xa02502c6403041c00203001e811350f141c900780d00f6840307091130010402034518641440381c4c050034250b101d00000d1807914005115064500f00350748842c141d100403039041c007d151039030340e81e0200d68a440c8410403194500190408056070744600300d6001145030a41030045608903010048920801001520f440c024204000c602c46140c007028800ba6100e61691103150400d5a080070803985000488003c06104000c18410300005218082c0200c180400248240c0c1e5050b030112940c43c0014030082c0119400590100345141c0440d40b0300c1603502c00d60700d90040302d400149083c00d0450b2107040e92400c8c010700c00140042803203515006c2c0c1030608002120724103a039541c00318045600807141a20400801140c07450020860032410040c145024240d4030103505004007540040410311039541c4069659a881c1c42c0c588811010400854804519200c1d1448504146000d8401160b006905000d25080160781044000001141c810003074a03040c2d4a81c210b0380103441c1c0e030202604581400501480302800a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 589648345 1250 589647095 589647143
    0x1091712160b09070b031603020c0d02100b0301110d090309080d0825140d0e07090204060305180d030f1413021005070b06040f02070210050301051504030b040b04 71
    0x22000c803101c0d8041c11080c03400c1600050401a0058145070465074003000a0b00c0e08006803a040400c0001c003624404600f9030940003481740c0c4516032158028055014032098002c2404468241030140500c0444040420142200d001000c00b07031382e5000521000500c140a5880880030720301c40d0401160603a00c032101035281040e4449a80c00061403681081020340001c622030500d00b0318804160080e9a46400107801c00401c600880031000c00400c000d4003404150704507203a845c076003038103803020903071580724401c042d40c0580904000b0a00340740c040380f41e6004640c2e844e0000101c20014004401d01e480046000c0c1440d020942d10903600e801c54240c0d458615410f50707002d0004136128023080400e0b07105004071101d0b462342c810700784a0184966800304002c0481a0351002040b100019210203c0304514003d02540d140a500980e1803079441044036003041c01036068810844681602c882406d580303960520481c000185031070303420000f0030b0001c2c40543c00c580c1c22a200b2440d0f003250501d120010001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 589649595 1250 589648345 589648357
    0x905221e0807110307090209030616180b030a050606040302031011040308031833091905060907090603080d02090f030105330a0302150706060905090d02010b01091712 73
    0x42d1095100903c0914040001800030701011100b0350800488000017900c0f2500282544540a08088248419441009900d1200481e00c3c1903100c0f503a100c4000181380d810442c3c84050052034034011903030900d0320805413000c8a80c0207005000204810650700050081c0c0306140342c0140c000d200200005440802951042d400c12030303d100e080c5075091003d4a0104440250700d00b580b01c0080b000c00b4100d0ad01c202c981719a00100c02d030486a120460803d1404441400d0742403c8440040c100080003000b044690050703071501d045032002c80d00d88126000b20782e428400140340c60010441c0100106258010b880145001015075003554070510229003502e401310380c0103a840240030301c0c0011812981107441100a01c0c4c40602c464620b0090201d5211512800060f02c203008184201c604104500300300e03010b0342c1d4000703400e1010a80c1d801416000c0e10707064500004130700650b00880e0059205108122445105039a04d0201c145030600710b80300c025800b03020146901414903400c07540f1003807100400d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 589650845 1250 589649595 589649603
    0x60a051536040b0d230304090903050405030d0f0207091a210d050f07060e100c080708010b192303010f032307060806010306080609070905221e0807 65
    0x1281e400c11400708412201c154072072900c5a140c91001c80003007010707240004881a9025403540c0032500555446143d800340743c1c4121195410103052034101903102000d0800ca9105508840009442d044142d0b560f141055805006034040c0000300300351a00e5403c810440d20701c1c815210000c40300c017000b183c400050b0403404282200e100c50020607222040103400041042450518182803410350300b00c20710703c94488058206901d40f41c1154084000b0f01c0082c06150b6107010411200415210252408a044840401041428000180c1e20b2140011500401300d030041c620b030110b420410a0740c030185420385410780e2261508041d11071442c084011806041c0072664800c00e2440c500c1c00c0c3d9407016404e0703c81e50b0000780c0c2203e0700c881c80c24006004000d41d6090305046813190303100401240103250765400081c80e40b04490a00c860740601181d00c005071001200140056035031010700c030b400c51440c402000720840c0c3c210a0744011500c280c0340c1565141040b004141c3c891004c0d100e1085982201c40151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 589652095 1250 589650845 589650937
    0x30c130512011b02010c090509060f09040b040c050916080903041503020d0e010b0108041101031107060f0e01052e03170a030f061505130e01060314060a0515 69
    0x3041991000c51100310f180000c4c03000b070100d000d01c40030081024143e4416180581c01000201c2e001d55160f00c0034622603480034115800a15250401d2411309000b80c4d03041e5003007101084007042505202d11110301c142182e6034018000482908100c0b103078240100844c150b0302041c407020442d00c03d48862082c44400b242d45c00360300d1f100090180c904903803030f18400041c582c2c500250b00005d41d80200855030b1054000c0b0922013007802240050380607000105480740100f41c0062480100001a8480d902540c5100801c010896007200400d00300d41c010f50b440c1e07070075414140c98032400500850100d2091a00e41e080040401ea5a40e034036030003800c8420703101030007002c04207035991540d90612a92801000011041c0042440c080f214040c1c1182d44410400304440080c3d19a10800d00d00700440040051060075025981d440c03500500800c80341d5052415240d402000c2245494200703030305000d03280000c11a0181d06098081125030ba44481810141501a0070300d010081850031005000801210200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 589653345 1250 589652095 589652111
    0x1e03060f0e0601140a05040909030306060206070801050a140112050403030c020f031e0d020c0706082d010b0a17040f021002010216080c03090402041202150f030c13051201 75
    0xa0440c030360550002010440c031401001956a40301041c00c0010711082c980c00d40e15110800c0840311031140703410800d0080d040c4000b100c101035140e400300d402c44900c0da09032401078840315400c40c0c00700d00a1050b542e02c80005802486184107100c10b031616200b050608140440350020000e0550700100d0f0190003003661800982c03d4580c05000516143d03007030700051450074400400b10007001d841010340081c001400702d0101c0202d03907140c0c12944541c5c4040101c1da40a991404000d081d4901120744100351407050b44001c10f42c84140030020b0480c400016588010785c200f280e80035040d0882c40311041000060f2246200c0c040084101c84e0003640609410407034540f490043c4060351444280c0313030085a1042141d05c8810345064101c8079080d6000c850301c0e6540070744690861450181403482d0740c0c07081c400640040c1c074603882a0340e084540c0c801d551480a603d007030390000314507004e465000e200141c0d04000140c0c01502000051a0143c1903861001c031494072040850003030b256103003e001c09690b481031a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 589654595 1250 589653345 589653359
    0xe0a090f0509030c070603050613021b0f070e1302010309020d05031801110c1207081e010b060408030304030806030109080d0e06010915031b0806040f1e0818011e0306 73
    0x192035200740e6030b03401036140802e103018a40e80d50000d407240608142da04e0001c0340955035184c01c0f0407201005003500b59151042d001da8034090f9150046502c1e480d100354295181b200102041d400d048868405000c0c0710303580c4007603a00c0c10780006508101c3c100341c0d40f0070b02580141d952000d411a06800f820046031612080d600d209841c460060006040c002c21003070941001c080000c05081d000400c3d14200c210b041c0805680c0d16040080d001210075010b04688649640360380200c000ca54804007000380013020300c1101740551303407160303006001c9113420400008000c20b02401c1d400c3d41041b0081c00000d040030310f0781c40d8058150403283d1140b1040f52185500954000200651805450101001c00c8840040c1d01c001c0e04812a6120007040c1c4c0b1500900c0030610b510a00d0000300410648003984c185103807500d80441e00300c4034400c04641b80800760110b14401c40240495090456001c0b10361446c1c102c0100c100d035a40c5141d040c80a0422803a1041426424081c0f244841d0030192610049110350405030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 589655845 1250 589654595 589654601
    0xd0c120c05010c080901030f1401080d0806090136090303050a0f0b0f0409060b03061305060a050105060301170a021e03150c07060525050d05091b010e010e0a090f 71
    0x44000e04100d0003403c44000b00e116641100c0e5070180900380003880e640d01e091240042c011042041d012640c0d20b0380009035200000c00c01b2801469165110610344d602c0c4c10030041c0340042801130001401848100303e03002e03000140501c8000b11586251840f1010040149099848042040700060746903001d01c03210070035a000b8103616014809082c4042c44003100450480085604400d2059803a0301c0c0103030610a440c2c1c007108485101078181c940601c0c0000e0b1040b5484000d071011101441030800040b4050300394401e00341640c80c0100103d181d039192115426031400c4684400c00729000e01c040440050b61403102a0303500b03e44100e0284403100c001d01c209404c010403164032501e00b88083c8200100340a00c002100c01807548824001a81d07151001e907990400203441c5060500d84030398030041e8a4980020241800100400c028041c0c0e642d10b819040d190405600040114203560701060740310341c0101e00c106440101071405102c5103458070001000c2514686c4140d10003035070b4029840d013510481c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 589657095 1250 589655845 589655849
    0x3051209010903170601051204060204240e0d020402040801020d0b1309170310050a030501020309100c020a06110c070f1a070317040f060c12150501120b0d0c120c 71
    0x100811140b6000d4401400301c1c81100450700d01090b40ca00000c460f68054070584071b184254a400460f10710346403805100030b41c01401543c03a103030030124402c0c10101e8188000b90428156a495482405801d402c0c001c2c001c4124a0890340107800b0b1002040d1503d003403024081c0b0104000d4041445192030060040019694503403951140c10408040085070304101c3c0411005000e41059030380365113000c008a9484542d800140c1d00c80b41e800c0000051040c1500030f580070760701d030708107440000040c41894011103001d00c04071409a081820040003155040e48444100c1c440a8609450030051000c00f90030545540c005d0720740105610300c1440307040d82c0886002e680e0340c04041c5c40d600e082816180980321f00c210840b04900f0b8040d940015040203d07003d5410001a8400c005200c0100d08038800740401144001034132100e46002400351100e15110390301c004071201a100c010303030b031194001241d016082d440346980c0c00181054072140044c0500c01c00d44001c1801503c0c00c000301009140420300c8031000c1e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 589658345 1250 589657095 589657111
    0x70b0411120c120106050a061d030307021807030b040c0f0201060b0306090c070c1d0411040603110409020a0f030308071112040909020418081e0705100c02030f07030512 74
    0x107481c041e440303003200084a440051007107502c100280d1000b0803040c0585216000190040c44609000400d26003003100ca08880340044c92400c48813a902050540e0f80c007901130065031180d41c40c52006c411860200c007054200503d0300e00407401030075040124064480c1406a0000540e02c2c5154444079542889504060240c00c103001e4a1801c00400160085c90081e0040044e0440000c03100c08110100014170024450b1034100c0d0044615010745c0c5e650301d981141c00f964402c4140541c1002d83c5000e10070a803d4076404880c4c2074420240c007040c040203140c3c10780101d030403124259010801804004101c0021880b80c0d95561940c03400342801007080d42d00c00122151030303000ba0b24038000b2100381016581503c10118000489a000d40009000f900b548a0090031007040840b21400707101030b0300001e20b00d00c86040000050700307441c83c1164001e403084400140ca650800456101d00104a40006112a4442c4122828014001c001120319808150b044020910000e410b480c16501c00788041d40c424a1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 589659595 1250 589658345 589658359
    0x3050408010e0321070512010b0306010e1002070306020c07030510020c0106080a0f0213141501020f0c0603040209151c11060f18041104030b0907090207020a0603020f0708070b0411 79
    0x4410542800507548620459044036100010390444d00c0b46051f19004100c607500480e580d6911940c000c0c0e60f500588000d4005803916940c18101e003020024421000309036401001d01d9490f544403500250031100c010a291f024042d00000401c2040015801001e204000181e4a03090280e105084803960307800f1030a940c00056207040401d80c504404c2440c590192640320b030400f0310400d480000c0030916801e0300c070908100180407160500740d61900030b6400a8007100e040034900c80030541e4031000321402c1640400104002001418010692a0010081c59810039035512030000a80030f000d100c01d0940f1b26540340201c25040c464101140d060b07400041e07940f50b14200303a21424801a02c280c0000318030001203c030207442551241e503c40c0b182410040c542c00e440b99281c1c41d00450300716040e1401ca800344155070010079a000f681c8202c51700643e00808038007032645081c1080d0060340007484840c0030807005200300c0012035804001400d406102e00212101880e0500d40110240b918031110f6026401e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 589660845 1250 589659595 589659607
    0x5060a030c1502031e0c0d080c070f0c05150d050c0301031e02030c060d1e06211506090509061b1e070501020a0201060807120308010509190903050408010e03 69
    0x81e080311198103031081d208801c041c0c0c1054000c10b80c91441440e02d0b6110a0381d202c2c003926451004e18001c0c000100a52046d0b615101310207408480394401995130100d040805c024600c000b031000c0c50542c02881c07059000074000d90381c80c000a5007040103a4401c0b0003111000071260b00145080c490b041d8020310f03080e119400c41d41181c807586003504041180c001c9006401300d4560540d03074100322030300300d4102c0144070a594420a81c0020040c14040351142c0d05a1b110541d00486424940038101c01e030740c29804c00c1001c0e1103030b80e40d00503100d0321011015030f030011034601e480c81281031501849025002d804004980ca04144402914142008011030081000800c0c042200c807019800ca0303052500c034083c1035110340c0581401103818825080c0081240d03100117802c1010369019007190040352100c5041e41c1003181d458035003802214140b48010005407004005100c1460601103083d00301c0c9155100012a8011001c0c00381200c00441084d00810008942003228503424020b01070304480607800795007860 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 589662095 1250 589660845 589660853
    0x106020f150f01091a0406150332190f0606080f0403120c110102031306060b28051902070f09090f020609030c1309050d0309050312040507050402120a05060a03 70
    0xe031040c0125048944c44175944002940100c40c1c2e1001480018010007800e82c2e07902e0040c050420443c414800319051840000c1480250581d071015440c807607e0064000240004c40c40600f40c00030182c2d15000c1108109500c0340c0f030944078040c8090b60f01d00340040c540307007018009030641e00c0003003404038500c4811041000107036000342d08a840f15944600454203030010b42d0291804581070115150760345c808010451034002c3c500c003501c013040c098481085400e850340c914102c0c030310800d4503620140740c1c4805080c1a90462015500d8050070525000d82844d07260b0943c1045100444c0c80d44006030f12520b07045c4440346d07004002134000c0c0900c02d000c200d554407540d200c00a1201e03c400c0070740f00c1c01e0041000d00103518148012041220000c005052884120401400900383e58505407414030400300d448209c1ca000f842540e440d0364200c0002c6007005000f41e111130703444030011701c21295030080920004064540b80040d00350921594605151842c16000c8401291f00c01054a031040d014480100081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 589663345 1250 589662095 589662121
    0x30717071209050106050d0803040b01062c0a030c080d090501032c03040b04080307060c020114150111121b010219140408070906030b151c06090b0106020f15 69
    0x154840407010400030000c0c240240101066403000b5040f4145149900c00c200600c3d00a6205078810001180540d0300c407103080301e001c1005103159100190900c80902180e0031303c041c401010800525010f02c3c240c80ea55201d40310a40c2c1e51201c45030783c1c06901c081111903000900f9501410342841d0070442c544043c8040ba8215051070300320312844410b00116207030b8200034011140a0240c903200741d50782e90f035030354580340c1d89500ca00d40942ea40c1e0715010030280000e00c1802182c0d2115442d298908594035100c007a12300703030096144124103111080f4040e941d80b030414010000c8030107400390f005485036100030403001e08880c0300e1415220f59104110203d503018000d03a007000741d1281850002c01c2409584000410f1348103940180708544690140001c4007549504600c0a0b244180240e508980301c81d803500c41c1000f207050801ea8444150200c02205011102c40d107a00c80b802a40b0119104030591a80749200c0342c2a040301006030055005c404420004001035840b032210f0b540c0c0d044485c5803402c660380315 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 589664595 1250 589663345 589663367
    0x90b04060b01020c240d06080f070603021206060a030207050631080315130e0c0a140d0209070c0f1202392b0215090f1314010b03071707 60
    0x1220309205142c110b5030b805c0c0701600c0f07080e04214410481d440e00c0d2090b060b5100000c604010242c4165540804c02d00e11a000381c0d4008030422842907250b4803021304000c0140c00c5240b940040603030038480c6a0205404100d21400b03200441c0400b00c1c4000703481182c05540030240180c8242d20030412500000410a4044030ba10a48250b07580a40000c01c5001aa200c0980c0900310405818002d90440c034840100700704145403c22a00c0d601c0085c0c2d90a014543d00c044a000c0d81d46c0301110a060754051b050800650794021210326107100800f160740da550392001c50410013615011290000e02400c0d5404011200192201d5040c14250740c1c0300c0c1401d1848801410750441e84460381c2507032000c00b510b44405d288100b10741d006a0741e8404607074482c0b00036881c0750361030142d1144003040305a00340250070000310388940b203018000c1c8a41001c1c240c14404507141c20440e28181d0b9035102a128029624402c034140039202c402d00c03440d0740b0b06091100401c80ca034445650415540b0741402d11880540000038202 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 589665845 1250 589664595 589664629
    0x501050f0307030603140f0c040b06070f0804090612060f0504051b06090604060e030c0a08100504080c01150303120513030818100b0a45090b04060b01020c 68
    0xaa00e50340c9070030031009810241d100920140f00d40340b25560166000c00c0c100c41c3c4847c080d007150490007118007040182c2d0307100d000080c1c000404005840c08540c20070f20204440e070180d144107103081d42e518844030850303003036901c01201042103c03503601c20440f281c001c4c2c44240210f800244254106034440c40e8480c7c8000040790390004090501200b0740d1516020785084d200010b00594950f0342d2500e001d0410200d40031002e1281c0503031010070340b080c035240d26844240c2d00c01400802c1e102d402c59034140002e2078068030540d10070000303000c1c08040c06001d000b40c001d845402c0c10390203c080c0c03451901400e150700d218a841355150034032040002000c507004451100d590903241105c15512000031403803003e1001800c0f96418001c510700700c8190400d68000c580d01303240a0742d000c0d0b50341e50303103c4854400800c01c0800c0c1a00c0c078144603044466070140e1a510384000d200314404460011240042c0e001c070780c4581c2c81140d00c40728000802c014400700e8458144424420f00190505940000001e140050b002945c1c0c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 589667095 1250 589665845 589665847
    0x3020603010b03070e150307020d020d050307180506160210030603110d031b110f03030403050d0302090310050a1e0905100c0905030114010305160e01060302070303140411040e070501050f 82
    0x409036841a05170030031440004d0008481d03080c40402d02c4903150b0040f06c0b0744001d03200c1c42038070b001202d1000448102d951174581c0e03140e0447d200da4400326a8003440c6410200b0001c100e500114403940c4803001805034144200c40e011240015206000c8021115210942407500c2c0c541c041010400040010139018000c81d0130811071b0740585400c0e00c0d105d40030007014614420b858041000c028107646825410f00d030455001003a203030b03e90704065691045002c018126003049440c0d0750b42300c3c0280c0190481003401810369044c010003030769542c02c4482c03c0307030b032034482d2038480c28407001c15924540c01002500b40d41c0008e00c01c001143e141d05544004403d071003494940d40c0c24408407003901c54411031001c0d010050090000c01102d80b0303604c501010a00068480b8015502c0c03907902d60800309958400ca400940c020191a8a008c0e410340c02134000403000e6041c540c0ba1401c001000c0f003402d603450f116a1140c2c0c20f280d00c03012988180401c0f11107020f034511056200c3e120034007290b81c200e0142e440401c0010307905 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 589668345 1250 589667095 589667101
    0x80610030f020d1b03030806060a050d0e0319030c03050a060506070b0a1113051009030308070c020414011211010801180504053a02070323011103010b0c0609030403020603010b03 78
    0x1c0380343c1d2407480c10054031250340c661604c180700d0300c84500603084030300036943d0010316214042002101d03c01d403007800b0007180040201d18030403512034200e05400c410f200143c84c2088500c0c00c4c402e81c0c2049000c900c80010343d40e0180010ad4540501c40c16810680707c0000300189070411020411a00c1000380203410400548001884036003650441c0c2070500c1055411a19100d80241c8100c006080e80201d61040c1c00030080308540d81d1007408007a080f2a0581d4603c40941c1305c9000568410b00b84050517a00035887d06c4130010f541d01400d0030341f8020102c0740081041c032012403c01e0705140c00d41d540707414100309840004000c060004013868241010042c0005050303241d92400c10b260881e18000c4400a001000c0c1c00ba045203854029000711404d440d40b0f00c00030314100e400890f08d0f1042404000d042c80d000d124021110784010803012024540d0380000981c1005000d01c4240310b400c264846401820001034205035203805010464011100c500214140b6003154005030441c0814054148100300200c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 589669595 1250 589668345 589668349
    0xc0a050903010f06120203010b090903040b0a02010216030e030606030d0905060c07030203060c120a0204080316080d0509032208060a0915110909090a0312150f0b0304050601080610030f02 82
    0x240f0020340d203e040113155511a0001e00750000302d40180c5c8254a8241428042d044c60701c4114400c64009001e0741c602410008d0440c0740c0e0f00050406000c543d82401004e112605407820074141c0c1d8080c0e12a8400c003003000d020186032110041150380690041c0307421799804c0c1e41210343c0c0c0c030039103d0071241c1c2c070748850025070b140b4580465684042e505100e803d0500451801d40300050010400744007450040e5516a01440700741e206510950803e580204050906150200c00b440d500c40e1181c1c2101e40303011b003e010072105941e02039030150f04542000440208642c01c96152200c0b00c54418841030280c2c0c40e180d0a46e071180301c010080d2000f59100d81c1c40c00c08005840c03454040301914004100620400d0f00714001c607540040c3c1109005640c004045220100b0004d040141c480e45130b51040c9541c0034803610000644078a021118050704102c0012035003665201c103450107405248841a140d103002e0400626104040e4842c4429800c00800d0040000e91007408105403600941c41d06154101840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 589670845 1250 589669595 589669601
    0x21430c0614100b04030b06060f041508090d030b0312030a090c080606010e04020f0d091707080315010c020109151806051c110706090c0e09070e0f0c0a05090301 70
    0x10020300e00380c94940015411404050240d0246003801800c00341241ca5100c40a5184035501000c3c20f142800ca0020303000d442c2040080202c2441040039034200f6640f01514010004a601c1c0800401e18000030080d0079001000010030f07203492890284241d2100e1320119440300008070742480403940010014048214642000c0c1130a5841100d40380032507907401041b030b2208803c0c1c609500091a1600305070b11481c1ca802554000b00d84241a0751a010400390b00708010000b0303060480703406402550103142d5503c1040a4603c0600404030035035246013900003400b0440d19840c1e102c1c140900c14072110090307680a0b45c050141c40514019504e00d68040038140c41c0344405020420400c03050304804264564007001518450040b0b1202d203c0c69210186d44100350796004400090128041c054040400c00036045880001d0040c08030300b0195848032030300c28109404590005c04d40c0d01c0110100041d08000c0503107035000003035420842d0743d4140710704e0000d49442080701010802001040010140c1e07400e40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 589672095 1250 589670845 589670867
    0xb180a09020d030c110405010e010b0c0a020306010b04030213020a02070303050f070209010303110115060f1407060203010e0105100e031e0f060f01150908030d020c032143 75
    0x5000e068814200d00e0f00600400e95020f003118504440314005115040c00e005240c16034a1b003d840c219903a0070800c805003550045000030b02144100440b040150b00c0c180007440c0600311540c180c950b19421801400355100100c490040d140f803040000252107580460394400b5241c0c14941180d882c00070240b50505070040347c41c045c2d40191000000410590071442c01040b545007280240500004043c80d10b0940e410b500c40c0d0720200f8210200031034151b11600c55154a8580000018181032594803840203e130003d0700061105080180103104600c1d01c0b900315545403800749011030140b0410408a07840e5440c1e840c030000600c0419540d1081d035007090001d00041d00fa40000c0354454074000d510514013403020b10524007034004d400035044065218113551000d56210400030340ca00341ea01000d03100294070036600101070780410f1001884030030506010760010006401c41042d04d08041000020280d240540f0f421403003040c0783d0304c0684501c515131049000c02500d519603050010040d0540d20081c4903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 589673345 1250 589672095 589672099
    0x9030503130603050a2306150316020f0d020d08040c03050307060c0305061005041e05030604030309060b1e19080a0f1a0702070b030a0b04060e070201050a0b180a0902 73
    0x21501d45407400d071024908040707a8056406020540b10034041d10100c0304a5030407a040c81c5001c1c200140d54411103014103401c85806080b504000c0c0208a8000140d0810355986010105a41d0303500600369041000088a00007540030f0a0052400071020b5034481048882500788040d03000020140010800c00400840d0400240c80d500e44040ca00040140180d038581c501080c5020081025414112008408401c19441c0e092074603041110440c400000e480c1e2003028281c0510001c41d050702c2c24002540a64401d4a0125540046103400001e031114090300034080c03a4003002e84050300c80302c440d02d16000402512609400b10b9400b80c0881c0d12119a00054090700c1208840000c0041d6076420300006402201200d0034820320038005001a90182c480d840180d00079101403000f44820002140c20610396440003070381c50011700110b001d85902da48039155112450080000c9160207000e42030740b0114a4404101c1205a007000482003100402e03041030400c141000100e1a410a5005094042d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 589674595 1250 589673345 589673347
    0xe01030b1509090a0209030a021905270c0310031b080105100f1d070503180a0b01080c0901180b0102010914010203061e01050415124506050709030503 66
    0x140014601d5544a40e225034000c120391000200a19400e200703680031a10b000300940f0704030520f03400704040711092003140c541c440f00e9442c00141d81d5441072160000300c0603044510100105003e12281031040060947c40c541c101081003111f0b981c80c14101d64180da1b031002c0342010b030700c8001c941c1003540020358200c1c0c61598601000d00400c00481120300e0304803500e900041041c9038954580001002d010050400000090b01c081010203000d50051540499001300710602a00150400c91030140403a2040e1050448400144403000d0300f0702c4548585034007690300d280254076011261034204a10643c80300301c59a15014801260701c00e412042089800074940e220070980301614074000d42c4162030711441440080c00400000b1001ca00011611405840340384c1402d1402d81c1003241680036100003002c201d1301075454140c2e00e641d880b450742d022846c030044103199880241e09a4201c51028201300250003100074614980e0020b0610052070f60b807028021a02e525041c030140c07240802d50704000c103a404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 589675845 1250 589674595 589674619
    0x5010c020115140a05060c0f0304090c080603060415050c0c07030503090f030a030804150209090403020706180503031c0207050d020d35070212070606081005160e01030b 74
    0x2a054201d480400503100b80d00c500301d070340d07030010f4001c2c00d44400d070b195044001240200203901e0210040c0a480f44940265a900445111068195070254004140c1c3c0c50781c41103090a10340d4091080c43c0d00c02403e90090100342403546441c9001401000b001c112191a0400200c3c03a001900654101912050407903181c15100e14100343c60343c00c0802c03214021040c00440200d64030740003030100c55840e00341c1c1b5140c0564940e5202c502d6100c4815a0086086408021280080d1210042640f0550103580500310721828010018040740501a0314013510780018018442c80c2d80200440382004c0c1c4860755110700442105614001c0d00858402a00600800202d4002c198003c114040703c8151b07541d81c052007188640d00a80c0f0741081d85442007045184001e145026998403c0c0385802c84c0d5107004885060003c00300c1c0031020ba21001c400c4501d20349460f01009680d0080000c2d0120300700040d405d03c4149080386120b00307401c602c4c45d144001c0008004401d80c050b4000d07480200c51041c06428105480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 589677095 1250 589675845 589675847
    0x409060e0103140c060a0e0d0803070c05060f0603120d060b03100e0f100e1005060412020909121e120c0a081003051207020f1305070206100e01030b0c0705010c 70
    0x10000b44801e40c0d11507003940c1c3c244410080440e0300f50800d240200440c1c1000004001214603028114800d6000b07081d501d240303004200c0031400b9510610940e95501c0064000341741c00c40c1803e5015058240e62903803801400241d58001c40d040c1911814075100d651102280f00c41e0802401d165404024002800400d00800c08040e02004081e555030440c8907005854085940094200407540c03c0552005150180f2420f1101180302e504a9401490748400689541c0050306a0380a0341c04000340d030000306541d00450904101459102007103001900402c02c890016040a00c15014140c244d18030207007a001e0440101c3c000e0340d48200c802ca81913011071412441d03004265000943c4600810301e1103000846011400e0040c2042d6a03000c03000c0c0281243c11980d030700503500320a50803070344044440144503841e202c45104c165251001c50000c900d60800b8003001e0b0400501400800300100c9019061181d08158540c182c11240c0c020100c00301070b0394078540c0d27504500450b030340280075500b08881b0701611 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 589678345 1250 589677095 589677119
    0x3050c3a0203190b0c0706021902010e0f0a020d110d0506040501091a071202090d080f0d0b090912030703020c0d080708010501030606021b0a1e06031401050d110402040906 75
    0x814820b408443e05640d0f0780c11441c684000900c401030120f0300040006246040103c080c24045200307450150400440e14954074840014544c240c005079074800000b038808204201a885003110b64003e01614075507a004188100c017a404041c3c81c1d69079030b020740c0c0c01c55242c12600c2e03161580c004090b00e0031400d10345001030107091074a00030b03245a5450402d05250b410320304001401943c3c1619400f1000c105400144081e4112000059001c43c500d403015010600780b02c01400d00c1820111519035440f07000742b4a1007100c00032403241e8041e402c40c20030408941000a443c0d07060b1041c1411281d02c07640c41010440c040d00c101d048401250080e1540e204820390000d20302030148501e034499000c1ca070f813550011021240c2d188a6140141c2c40400c515000d42f070801020f440314000541a007000544a040b400310802c1c032945e8031040303031400800400066915116014034194100d40c1c42d6041e51420000542c0c0c84004c1501400407090301030529030665555040f40d005190811040c03164070343e01c030700c60144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 589679595 1250 589678345 589678459
    0x8100915091116030e091012120e030f030d0501240c050c1c050f012304020a2c0709030b0a02130f060f030e030a091511010f0b030c01030603050c 64
    0x60166101041c21f0501c020400b4098030140c00101c00b0700303c2507071a0700c50030000002100040c030403801d1001005881c203004c4865480c0e4540001c5580d00e96102e520411294140d02c01c0750030300300d850503080040786e01d000c084c0b4409401e450030100750f0b500e90501c941018036074254654804c101d46002c0c0c14510303c0d03c1c10410642d004600b55219801442c8409007a2a002c2d403a001c0607695043c45d0000811418030455041070000d401904903076156480807103014040405010702c2c44071071100c1d511808a910b491940001d45180098040345113036500b103541030b800360070817000319004079020600c0042c852038800207107445964480c01c640d850a01800001100110500282c10410500006040001116808030941d40c1d804c05240c5071a4560341408200803050041201012280b000694240510401301c0000c0c2000580b64443c5030030103203440d8400b592a0305043c2000420804503001042d02103607204103842c82d046c8440102481d00c04944200c1800f143c81480c241140e40f4400315401e9284 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 589680845 1250 589679595 589679599
    0x105031b0405130902120607090b0c120a030504170a02100b0d051b011b082b02031f080d090b030a0b0901030b0711191712040308100915091116030e 65
    0x2001120002c4147d04d4060880f001004141c88400c01c2124544210082c410206181e055400703488411000c0015503000c4484040040c0e00d460503c0184a107101c51400c54000224803580380c0150300e2030217901d0b208400301d20b042c42d40e5144c0328030070503072510349840d951280c7c0b10f03043e0340301d4108400c5060707811440d41a08070f00007a0702d003400c0402030b00792040d101101500541040e04080101c45000309040400b070042070f05a01192070340206030300c80d002850107900084030040c0304100c02d006241007103119034020385995003c18040c1e0641600702c61350070255031420382541d5503640d41c40009000350030314030741071504440c18034000010b02620a00035402110740350340d2412004a07030300055942c1c401c18032035201c446405d44583d03400030310400d001d40b4100018404407410080c100ea11125028000c030340540101d10f9410401060003110741d40e0102900d02060100000381c0d100c0318555404279640501b4410719a10015110101d40801c103480000c10032015000c001105490014804151045098 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 589682095 1250 589680845 589680859
    0x6061e3a11030d09030803130b0123010806010e040b0a1d27250902070b041b06090e06041b050a2d0521070c05100603020105031b0405130902 62
    0x3007154600070071481c03844440d030b540b2032501d1410f507199415150b2002c0d00c0b501044411108036000600f01141650003003e07400d2801c2080c1000c0d15465400aa00c8809c0d41e040040d03c00070480f0581c0c2203042454030000c25540015240e40c00d402081040029410002940901e104040001c10100054500c118111407881d845040c65001160318880c40e1455402280c102c070510982e580d04200320b6501e600c070302e031202c200a00d548092000c2203900c00c40d400d5424054510420051000302c62005103002800401c44c1e41103850628014448040c0740603400065180102146242d5240c1d0012500403544c40714445d450f01d14024041c0480d40401620390100b400008030744041103100100c0c80700000705010260301c45002c11800c1320694000794641382e445160701d000500091201c9020340c03040909444001c5241c0c2182095460300301c03040c0710100300c2030a29000b440103036400703000e0f40e030000c014030445408901007040c0240c0c2d034005ca4010540250814920502c10740d8642c014902d4035000b60b54071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 589683345 1250 589682095 589682123
    0x1020f04030606150c030f031116031b020907050703031401120203060f16080c0712050901090b040803070209070915120c030e0a030e0612041406061e3a 67
    0x10304c111004007100c9034041103401174003101180c002c02c22040610610f2a00003103561345145004216000030b1488464003110b900200c08260b082129000079040304140400b40045544c001090120300400c0c01d41009400300c0c8020406000b508124103414105400b4240b40d81c4402e144040c1c4160007a050b40720740310b80b07400b1507401001c1030b2420f80550407000000b0292500d892095544400207803054102103410072005000c6030780d0740349402800c1ca955940b90390f2801101e00040294661303820a2118003002c10003013241c2040081140c0400342d0540306075000c1c0d907903450181d410761515400906d440850060800090303a0060111102c2c1d5284282008001100b4104404170b0780300495200f11a0f00000480011030300664403504a008010142031500d4030fa06822044180103860031180f190044c9030b4200661400c0c8000c03544030038255140c2001d0740280f002100b1840380c1c040c2560103200420355807550b0351548030090803640e0916104948000c4500380f00211505031a41c1a42c540c81101c140b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 589684595 1250 589683345 589683359
    0x30c07052109010804080702040203090106090c020706090909020d0b33030606150409110c0c031c050d0204031e03180501050708222405090d0b06040b0301020f04030606 74
    0x101180701107200311520305010b411001900c201c4000350054403603000600c060300060b6564002140b046000d94000b04829145c08250010342c1e2101400400f0741d00701138400c2c0501c45d40301e140c0d00d0480350304d50404940d071500c0c1c0c0046002601c0b4080040d1074004103508100101c1402d003403c1c81148480d945070800c0041011141904641e08000c0c0355240c0c00400101c1d400e403400030704c0b194440b104117400780c0c038055803900080c04036440c3d46030046048034049140c21909209001c2c0311100d176020380141500d030007590001000300202d084810184100814072032801036190b030680d4059540841181000e004070304c0d050340129a0544102c0004880d011080800324080c2140e000711a41a15010300b40680c0d0390311614540c124210440b0034140600e0002034100c4040da20074000e1580081c40001001982e4000408849921030401400420010000c0d251140c10340700015030303080301c0d40340d149440d00c1c8000b4001e010240e5100e42cbc150300114105810040403401041220300c544010020039030340e114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 589685845 1250 589684595 589684633
    0xa02090a1707050a050a1512021b06010f1a070602040b03040f02190311040908190806010807050405100f1107090e070501174c050f130e030f030c0705 66
    0x40c068106c211090200103403074003501c1484540301702d07080000e10207090610550480e04141d01707914622064810308142c0b16010b01203103014000c4401100382c440d0030f10850301e0710060880900041e03035000155910600c042d59041d200a05004044a60340381458284660b1781d201c0c100d420707480b9150503440c0028051030f0742040c3c0f0072603a02050350070140d01c00200304001007500640540d11000c1c10840e190000203022000031f0400410380f207600c4641047c800040c01180000c10480c18060104801c2c01159142c1080c91003001e07091070600d8000005076022284040e0100c280c00700d911032200301065254850b080105440740140450704001d41c3c803001101c02c40310b250030950484825902292640c100903e0103002180c0c03120b5596401e51205102d60803501400700b103000b60020640d50416240c5d014401100100004c40d403251418140d0302c0000d440041c02180100740c2ca0b40c0324690b100403031003841990a41340e22813100d90345a00d0809141c40c05a8030206044942c1d0003007050345420305444c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 589687095 1250 589685845 589685849
    0x30c14060f0712140613090515041208150d0201091e080f07030b010314010905070e060a140609010f09151e020304031a31050105060109050d08030a02090a1707050a 72
    0x45010041394403183e003804a02c00a10300403094498548602030013140040149031104071050400c48420715081c1040c0312141000c2908004102c0d503001448a822101442070308841e4044400381480c01e110310050741c20040302d912240381c61a150301c2411017180c607110190112a0f020094a1203a038111042c5512031005e800300400c01d010031700040c40401c0088441070072002111000149091450312424501081b03640104132100000301004500d00f4201c01003c02015900c175a008a984840c000401c14014405e10904006c41e850700100068425404140142010761412000e43c0c030703c0e44010841007558031807828101e80807203040c4202c0c1c030002c109c4d03045030b400251f802600390003581441070104010304810f000d46010900c4a6600c5a42e00b5418010280002183d400000c1d61400d41d09441005202a0600900c1942004651103050521106650115100340e1b01da413000f010000a0144407040c5402c41d40780e51011884403d00001c100d80c03c0000710031101c5046c2d44400b001103504c054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 589688345 1250 589687095 589687121
    0x6030f120d1a030303010e0103140c2b0c080a0c080d0504050d1401060e0f0a050402010f030e1c030c18050303040e07030902150a12020c0a030c14060f0712 68
    0x30011000c00c0c001540c012210300d214204020b0803210601d0000b403541c1c20a030040d14526038490010410000700c0307118a06a1480203028001c401c0b07240c40010311910a00c40034407036141189800100c1c3e03000e06141214100d81c000d59101500f80c0310301c02140d40301425441102c1240041c8808030f600c401c005044461000c00381e464038a020700380014489500c11151088540c4160381208000715502802403002070580001701115614054500004101c8040c0800d003006203000d05100141c0d921510b006140d5148c0d04020881d190143d00c62031805a0010108050201c4100da60212503070540040404000380e540d090050900901c00b1100b0b240c05200721a40743d4002c0004100d2644100b155540c03021560400003100400c50700440c0924240c0480c03425184070026004902c550465002007a08501110450602c07024120555482e0640c400203010304c041e00c03600b1000c024a09401d0480c0444000540e07a8505110203841032208050302d003280810064500450f0181c580d2080c01d42074030308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 589689595 1250 589688345 589688347
    0x181014040204050a060c0203070b16030e040c0c080c1e2b020703171c0f06121505041e0515010b0304030815041514040b1801090f090c0303020606030f12 67
    0x900502502c50342c0e0b1b903010490300350140503000035030303a200440507040000750f4254100e1150060300d0010881c0184c495110b200703c2c9403c5081192a6001d4620030740241c1c04803009503100380303240380c0500c0c0070780084e82c120000e00d04114902541e0b501045000b941d1260300c900032007064208800011000900d01720100690103000200081a0303c902d043c202078807160300d064540303074101301c10a080f6000c000ca0310b00b45a0b151040440f1580161117044020a640c0e820311000708041eaa5840095440c8020744418030384071804076050203044048144404442020f0741c1024610b03240c51900d031900c81c0d00c9c01e8444502c0000000720900b00740c040340d20803549a07850040d80ea13644d540700400c030080341c0d49494009694000055880c8452038001025050140303142d40c002d040202044150384172541224021000b0103180d040307249461040c82c2c11340300c2110000c1141e003001440c4070024079041601600b9411202c03000010316801091845c01050300741c0c25555a18a6503034010f5880507004100440060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 589690845 1250 589689595 589689599
    0x909100203070513170f030f0a050c01020c1e01050108010506130c020c03031308010506060721120f0e15040201090918080c010203060126040809181014040204050a 72
    0x3540119070181081c1000d43c18150a4101990310840d6500029041c030a514003c00034a241000044488010341000b149040c250001c10a214000c000c0c3c1c0406006012900381050902901600c01f41000c40c81100c18603034407400703002c0d0070b02e110f2002d4070b030103518000c00403804180c18000d80d8400c5070b014015010b00d49548843c1001081e156202d04114080d66aa038000c03039078140000c06540700e290050762482e60400750051300316a006880b1030303c55141044030310000f031032031760a038048615011206040c0140060f015524100e5440c0030801151401c031705954000300d02d50298204807090800c90b081c401001004241502080c0c0c0c0c080e0100b403041c00b080200c90f0941d00960480342c0b062954080c016425a50446187c00c00c103c0e4200c1c81e50040200f2103556408040503101c0d04400c41180b5161092240002c0d4402001d84007a01225001541050b1910795202c20303c03140c0c05620740d00055184c00407490355035010394055282080508010303401d180c6441d009a034151100200540e451038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 589692095 1250 589690845 589690873
    0x91609061a030415050412020d020c0a050405071709030a0e0906180a02040314030a1b080a0e012703030305010b25141501060e06030c090108091c0507110909 69
    0xb40008200300c0f00d80a012889541d00e040502410f401648603c20070ba80c9a1000c401c040d0820000902d520b08542c44204401308a42d0b138842c0d01411a030003518009980d848160701207070314628890301d00d041d40354035106010340c9110000050201c0700166407043c0c2211001420000c200c881503032000d80c01350707403462400c4130a441c89034060740001e07428000518050361b0341c1ea50b0050041c803002c41041c91300003088102c0d420303411003140c4c050783c9440070708120440b019580d13002e9103004540310b140800800d050200050f07400303840c01c19107207813402014141c00410180d81030441034650208900090400c00002032040002d4250b804110040d10316202a4050b08407240d0111520b5500340e4400c040740d84070150501d41400340c101004140c0501200c5581021000b400d0801c50f103c8990241e1400c0041040302d03544030060700c201400c2460001d005850b0f105401d860030303440b0002110800c1e0840e84030301c141604040103101d0075125850854100d000744041000c084400c65401d8116004060407030129 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 589693345 1250 589692095 589692097
    0x40c03020a1d0a0f0b0306030c0d0312090501201b01020a050a032301120b010e04020d030c0302070b0f0904051303050301051504261905070501110a050303091609061a 73
    0x282000f40c051603115035602e030000c415040e1584041210500082031000605052060041c4680203440441710803040380d0300200030801640c80c00c048141d55221050401030b003900071603080c0aa888110040ca40080010305d40e55000a500184046c1d1000e4024040c80040c029603260b190030b905d4040c203020001d2416030190000751080703c4d0205c0c0c0388003042e411482c0349060324080c1a24844020a85041c1e181c0309058a0068000c12200c510a104110050b683d500d805c041a942c10b11b002c580120482c5001da24001154110190910b40820307010a526800000303090403802c211002d012903240c43c13240c600c12140c0404080c00203102000180a5410546000f44503001d5103941c2e90b2500b0341e11258104c3d00c9003801182c81001440704050344100f1004c01141c44141d10362010a24404550768a09036240381c54410380e414481088125a0440001c0c02034040903030300081560f03917914292502c0364642d01c80c400c0303441040d280190042040c20192085000b0b4580780070402c030b6440040d550030809 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 589694595 1250 589693345 589693397
    0x90b0a29010f03020909010b1201140a150c021008060102011d06280f06030b0711100e0f0601080604020118080c0d11060703080a240302040f09050a0c05040c03020a 72
    0x7450b8080125000c5d940341c442c3c14500801054204a8075141c08120300065000103a1002a9420354403820a403142e9500d0504800c50303072084d5041c440c0500c4508203403091140640e01a61007800e0080d40c01155401c0400b90f48613007400d90081260540381caa201d03030344d07030303402600100a41e01105c001509881c4074148130036540c0d005d42400a50390280310810013500c902d0300c0381e40071983e00d6003010410005141e18040d08003556040800c04c0d10383c0b1450701c90b91100111000c800140c1c0700c12001e03ca0040900c0594641041003050300c41541e1144401c680d1071805803400c0b070002c0c4134203920145000000e079030b15060ba6580070140845d00640410451910007007002510181070020b078621040d9185001851164420780750b09515142a0404200f140c500d0340c008417038890b040c3da030896200c0c100880c01c3c1c2501d504031000941039030742d0044c2c4401003a0b141002403061007100b0083d003c1c0400401001e08a4408071800e114001d200981102640034100c1c03075134081804101c6000504040f61421703c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 589695845 1250 589694595 589694597
    0x603030813020f030703121404030206162406080d02010207021809100e0c0111011a0613050d0c140319032601180b040507171504090b0a29010f 63
    0x1000c0303e2000290034088181c2c81200c00309070700c0e45420103650304208039000446100e8103640c01c051564001c1141885246100b000002c500c000c08400c00032950100050308440201c0401c48019010b941e100a00d118040c0841e14403400079a42202481402147d11403a4041c0c801101d080c040b585445111030043c00c0b0041c2d50149038001304c00321203d8441c03003e0000d03041e40100940c2d00700c1c41c0003400a1080c0388803c041c590605200328000300320f40341c25844d90b0000703548941d51200c441000c0b5440d406d681d042107034400c100c10000b03801d00c070a450342da40540715441404003035060701c0810140d540b10f401c0108805d2004088441d004240940c0c0c25444021150808035881100b010500c400601c098100c026103880c0360510045004d0184942181c01ea000e4400b04002d00b88480042c1c08140da2014401c0c60601d42d00c0042d9a81300043c0040340603400180c0140550360103031400c0c1d0000d94003160341c0180b1070314088001042190700508903042e00b2050211214040780c40004480750040c000c0124 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 589697095 1250 589695845 589695859
    0x60e0d03020a081c0507091a0c1609051e01031106071a1609050301020c03040b0a140c0a210c0311030c060c030103120504080c011d030d030b090a060303081302 70
    0x30b011480d01c00003402d0840c3e003140301d503801410050600f000c0b6200039104d5400c10000100c00c1c00440c0604048800039000c91130110744a002d503541440c60011504603c41c0c140d102c4400c000307184041c80e081580995182c0482c114644060140100c40ca202440040c04080341074844000324100741e0f0007403000d0740c094852404035031000309416003690300136a4a100c3c2425840c8018504581c008402009420118020751400ac403160249503640124000e000e240340c4c002a204451714050f002c0c0ea141e0012140c0380a884610325915951902040d0340c041d200300060402c1a86003503489000000170708010384402050b8503c544007140e03080020014010307584010061010b06040411049106484a010043c0c0d650305500c0c09103002413143c904c0f2010b100d000c1c0007d01c010040031405255201c1d003803802030820500034900c0c201e60482d140d0f1141c1c05009009052181c035a02d40c201029144040c0c3d0030f242c03651100c00103e000c07501c0300e100280000d022200800c0c2c20b1040769603100e0203680010515 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 589698345 1250 589697095 589697113
    0x703061a1f030507020c031c050c0a1a0709081b040605031501080d02190318180219080606180a080d020d030e24190e010204140a060e0d0302 62
    0x841c0800840500c00114060800881c95110380d05009181e40301c14984081d10286601c940800d58418800c1240219401e81c805201c850301e00c2141030b00c00e030590b00706c112007100800c1e00f131840b0b2822680710800307144441c4038000340c121802000c145003146e02c01402030240c02c2c1c2284450840f102c01e4000a5481501c58400181e46d43e41040300340c000d40802030410040b9454000007074030b0711250900003000e5410428000780240c46c002c140d568a182c2508050408001c0f00c02070040746000c81e0002141c985030014040c1d134414103680900003001c880c110480e080d000845058400b02000c41d282a84072034108030300e00c40c0c1d1403d20820f1140442c0542000e15040d2620b1701d5908200242c458080142c0c4180024a915649400382c4208000d41c103028001d01d05051001000540d8118045900e0b201c0b40c4011074040540c030740311400000c40000c01082062811403105011390f009100e03180400c501840d8290091500071000da0486509440e22440e18504209021102c0719100d03090f010340c00f580280d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 589699595 1250 589698345 589698349
    0xf010f1d0a08100f0605060a0809010b030307120e0406080705040c05090901030506040309141302160b0903030603010c020106180c050d2f07050604140c061303050601050102030c0703061a 82
    0xd00c5010700306400c05408440c8040083d4012070340520682d00309030341030103000c004a40750b080442d03050000d41e2401100d140c1e80c502e01d040c05040101d010540500c0001107800900c1001e48101031800742550b01c600c2c414891208020944d82e060091090942082508011300c2c0781071340c040ca400089030309101c0d003013080f180d0028420903400d80c0141ca16400100c1003204055001940d078000e029071070340011741c4208510114407441541d0001d01107040c0d002601e01d840110880c030031700c0c840350700c04d0700d4402619140010503220380058070290301941c240016119404d0041c02448150b80114610b80a0480342500c2c0201601a0345501c0050181c10000480b209019014810300d841c211070b82082d4048003190035900c20300e442d0316581610722082c402ea100090300441d04ca03820940040305464050304130304016040940c1150031a50101001131072810051200c002c0710201ca018900340c80840e03a90301c00590304c0c0e00c02c0d40ca807000141c018600901c0080c41c0342d800400c580391070072207406280c010840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 589700845 1250 589699595 589699609
    0x1020c01021c020f06090c040e0304060c02040c050405040c0306080f0f06041b0305060c190804030c0605060301021b1606030b0a0b0c2d06071b0b04060209150301140f010f1d 76
    0x9901c900d51f080318030086510f0400c8c0c050b0000380707100c1000841c500752030090020205050102d00a00c129180d05800301001c1c4100240c40c080e0a004104001c81102c84e03030094000d103841c0c82040c800c4e00900e41030a0120401140341d1048400300c00143c12145d036140c0c0d90400400d05160030755042c240c001008804500c00b0400d2522488584286941d0b80d4804a803211081001c0c014040402c40c1080802000a030b00480f000c031115400500407507275441e4400003901901a540390310103064117003a840100c1c10400075074076102c0c0b908031500359085610781c0000c50584029074503d60300301e000c002c010000461007000410121074810141d558021001d45501180014600400a000d800984000781c0b03450920070310703804c01c1d20780c00c002c642c100020702010070b40c1071900406071074000d14400190a0025903011070b110240b004202401e400c841c9a51507116070070a01449000c401352501400c0c0030306040111454050341612030041c4441d04c10070071102d03040c0300581c007449510940d6030386249480b041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 589702095 1250 589700845 589700851
    0xa03120e010c02060f01120c0603090303140c090f04110301050d0c1211040c09050109090f3905090d02060a23041401020307120c0c0b0304080403030e01020c01021c020f06 75
    0x640546074500b0451241741c800300040e00810001400b8040100000c1c62802c500f5084552034140817a4000c000d0034140c00070400305405005861010041011a104040c02016180f10403201c0520203039004060004540343e10b09101700030705c41000103101c0c41c030304152401d0344248680c204111071500c4444a20003000c22100c01c40380ca0304003101103015450140501d5402035110f141c044801d500d4480000c1410001c1e110344466582c0d22a402024100b542c1c100c2503400f409040d24007886603d101c80318044000c464000690306070903020300c560042c030a0044072090f940041107400310050b1902008201d900c146400000d0102c6800f0b030502c040b0341b411a445840c025406001d4a4610f046084030b01040c040c01c642e0304540003000400006540401c2c8214103040b1841c2c150701c4003d440c50080000003154005408040b0040100000c0041100082068034401e40e14050311134500001680d50710000c1c0b0352a40580c124440c83d504092020b42d01010100c41d40c812075031003606400c91241011426 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 589703345 1250 589702095 589702097
    0x1230421120822050a02011b0c080304060f0c080403021c2004050a06030b0a09081b03130510051e0f07030210060b0a02100b03070306060e0703050a02030105030a03120e010c 76
    0x184042150202480d6000c030f541c400c008151120010302a83c40c5611100b20410081c14041501001d403603114044400002850740b01d540d44a0240d03c038002c82d562a0418441e9200007401c43d41000b080341e10458910b4002076000000c03906041c110707800c120040c145482134030310b0b600780307a80003002041203a11105840c0100411901420010b44180421b4400c000e1140300300f9800c0c12000c20002d80c0e0f809410303600c038004400000719280e40d464000d4481c41002c0320501a610082104180c441d0040000d1546010302c0a42a45150b541e5040c00591984060070401184d03052244881001000c0c054110407115031f00743ca860002c1300302a84580340c1040c0e400754010303404400110200b00721441600b02400040e00071506040c14060001d6450650720261400b01e0345039030010506403000c000e8074020310783c403c80521a064581c84d1300b5840d8038044540e2130010b4244004903500da00b84d807084074140c0300c024002c5c010552558900b42e07480607925500f1052182c6d110014820904284a481190216 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 589704595 1250 589703345 589703357
    0x450c120706031e0c2d090e0c0c0111040e161d04241701111b07080a03030207031b120e0316091b170403200a0305090123042112 56
    0x144180d42480000d02e0005a1042c051104c0311700125608041c910089a480050b5000141c1c4c40b015803101e50300904411a030650300303041242c000500c8205c050019503490240a1205585641c050680c000300c1d0001c9c0c10114040d042110a0f101c0405000c05400d100944041400d01080d11104602d43c0b40008512488100c440c013032103210005011101c500304c1c0d40c40248408080c140068020344a14002e4840d1800c0304000103105110503c90070000740109800e43d96506914100500070354001d0400300c1c0001d01c01e0b002c40320300740b208a903030503442078000c1030440129224982c10303100f1000011500740e140c032074100960a09007800c0000405851119008200324001270301410503000d003041d440050049040003500103425001c0d00b154020740500d003284e15840080500549003160f001051a28090400c40405058210b0010314904600383d0300c85c07200380b0000c110304180e036240064107420f1001c2013100b0408008441d0500c01d200d80e11038240c3e030b428034150703445140088a000c24030001c618 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 589705845 1250 589704595 589704617
    0x102030106030c0306050f0409020d150207030e1206010513060e0405030406090f0b030a02070611070507080714031e070815070e090f450c120706031e0c 67
    0x10b0305010740169582c0a0078180301d00750a14000600d5403800200c198001d079039501c02300d800c2d5600e00d050b44051b00d0700504216401281942c810740070390312150050b0042100050360039218100040300c100310b1183c003009030105900301400c101002440d120b0301e05940e61101000300d50b006a56010a014a1044006581c0c56141200c05445040070f07074003c2c003641030240700030007102424008583e40241d449000594520303061506078014a41402e0780070b42c0b4034000c29501e0030000005070740c4054445074022200080c3d5200c0580e07504014545155800d9088940c401200101201c1c04840d00440750090ba504907881e444801e00d8a03560580d5510391142c03020501c842580c2000b05188516401d803000c0d80545007000300300020319030142c080501c0c003104041c3c0c48042021005004007a410744001d20050b550b0411a400e02c100000c09658014002c00c9110a9a4586586842044042d0b0405404e005242540550041091020700541c01c1c003803000034400441c59206851425000c0e85a58440c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 589707095 1250 589705845 589705847
    0x40614090f070908070e09250902070201120612021f12200a120f02181c150f0f050702072d0f080f070819060207050304080706080c04150c03021e0102030106 69
    0x6800c23280300000006d0942010070309a088512102503c2080700e02603901d0489100403500c1d46039424811600500e407140c04130f1030121884140040b82d000300c0d8809083c001c500e042d404010400809007001c19150400c002044000e03401c01a41d40300e004081d007400701c103040c12504055210135100c00c0090410400e021810b102440340c0c000e5030304050021401d09800c11480c40d46031814210b4a03114030341c0c11103100605c400241d0038895007580501d03d008005440c2140301701038103000003154529070070610010240c544510449100e640180d004250042c984041d100d0801407000091000400c441c40f20000a6101c18142d0001d107440420760a21601e000213890410041c420003030102c0d08503940810502400140294a50109514414820405140c400001d1043c10030040c080d0001040005171544003043d010110b0b001c0b0b48541c06565502e00e8a03c070070344282e00648107080a800440b500003031080e482d65040501c070f80100c03004280b2004a007043d020b40741000c200143e40020045c40301e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 589708345 1250 589707095 589707103
    0x4030f1209080c0d020d080d06090e0c03150c09120a080d060b0702090a020a05091f0f08010e07030504141b010e010201020a05090922030c02040614090f070908070e09 73
    0x14107401014050f400c41000008025003409607019120350070444034030081c88000011038129074104c0a0821449903103000c580040c045280e0800002d0242c2d4010890307a00f03000c00c607080c400c05031107024035550361030660204080d001903a0054202c40c80d0150f00710b684404128465580f4058401c094451101885c6401a80e0030364100c003040c040c0034041c6100503216451201c0e040a014580540c4508611408464500420029551240000344008000c0010a0501d0402c02c1c1e15581e581e04896400f106035a0b003032003031082001200d0000c1c001000d0310f120b90320440d04030788940401c2c00c89803047c840300c5252070551190182812030305600442c2a40c1c0000003600658801e0000b0340c05d00c2d48001d0082c2050291705052400392120760f0000380d40c03c0783d103281b5296181100d84646000c06850400916640009804038001c2c1c0c90120041000c1e43d403200580310040005022004550303a0640d942081003019000c807090004c03c16021824800c103010b44409480c80c0304c1840d01c2807070301c0040b843c90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 589709595 1250 589708345 589708349
    0x31302150705030307030507031523040903050403060c120e06090114070c020108090f0a08180303070b040f1406090c03061807060f1106011205100507020706120204030f1209 76
    0x3410000c21500c80068008010749a10602604000980355103600303040d400744ca84014042c80b100410302010943c640541e0110b40351244807410808112100018082101c403002c10203800b15800384410030024016820441d4080741c41e2800b2480d925504130f6080a548140b140b00716143c00c40010411a1142445000600c881650901d030355400c000742c011b004100e00c2da4010303040010880014249910800c80d6500d6100864126041c144150810361619084030114119060111000c1c80003860000142c65055812440c40d00d62900c40da680d410303266441801c01c603010440c018913000c80c1c0c9000e0010a10804215003d0400e0b1403000d001c0600700b09004102005850b0700104035880c2030310000b8140c0076034026081c10102400c40030000e41d208400903039140414411a000400c030903031004040c2d00603d1040c0d01f00d0300409034030504482034500c00c4404000503400308004006040c41403c021545071580000107250644a072141c0c00d40001401341078034181261480c22250642c0042c0c4480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 589710845 1250 589709595 589709629
    0x60c02011e05030c0906120405070f12170913060806060a231005070f03021e030304031e0c060905011401050612011512090f15060b0429031302 63
    0x280107200410050601d00000d0580c480481005c502802130340c03a440d048131140180601d03240c80b149014a411551460340c1d0007900107001028900045080d900002c600842e548800700603c2207000400058050704402503665000007400031540c0c50003c40d22881d8007500101c0042c04003881c00e05c00380000201c0075481625560a00e80030400003110b0b0b003c0e00981c00c81c003201c0492060880b8001180c960103807407000707000314441d51041030403d900050704420000c2003040070b07607906c02c01d0303030615403640001c032005800b0580200c2280392070b01c0c50350030160f400401800c1c01c0c0c80801c000c0d00d640007156500c440c112560703035440c062041c44105503e401801071404680c101e150959000315840105010302c070704400e110140341c0684d01103000d0a4007461a0a0b688002c1020340104d04103003500440110040c1c60700c074050580300c03081555900583e8280c9001c14002c618041c03070094200301c181881e003041c1d01004c0c00c125070304d421301011000440c082c002803048505042407500405c041144843c00c056 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 589712095 1250 589710845 589710887
    0x603060c050f04050907090e250305070e040e030c07060512180a11040f0c0c02120304061d1201060e100503010203071b05150a09061406030a150f020301060c0201 71
    0x12101e640c080f1401d85038192000c61040c3c50303c010030340c0d00c8030003500b0010050080b20200070f03c542c1646442407a282c1c0d00c1c14000001c8030b002500750203d410a80c0ca000004034200b40340c0050b4102500401b401e1914602200d14003c172000c140b80c107204141c0c10031800110002041d030310894100c00d0070360308801d00e101030b046e40034810a455a84c139001c20800400d1200d104c5c50b01c90040d80d603a0701c41400e54980810074800e4926039100100782041c5810304921138200c1c440c40c00707019440081617800303440c400d460305d10300c2140390307100b0401c1c40b5420444281e0085603018070f01422482801448014000c200181c641810000081c171620595078020b071f4040d030310500810070a11342c802c400308030071030204070b0080c00018141803541c04e00f07445006c02001c0d0800c400900c1480300007548180070240c0511030403c080410300da103941c100101591080d0307059002c581d04101003070400032411000e100103080004c2280005940f081aa0400d07808503001c2007443c1c80d190255600f22503400c0d40b800752900c0310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 589713345 1250 589712095 589712107
    0x5070f020a0324061a120702010f090b0a230601030b040b2e02011103010605090f041104181503030f022e0c020c0a03120309080d2012070e040603080c010603060c05 72
    0x796001d002c0b40c8104202d100c002047e5010700030b50043d851070340000d405010840c0c02d801d10469042041d00d50f4445540341c06d40d12180300082d20030040c0d112442001c0f034462900c81c40011005082241003055020303580300020a1f0325610030b81021407903040d4440e003c212226110304030701d942c5025540441503905005d083c807d0120150100e9040d68024181075448007134000214001402440e1100c0c0c020b490400542c21010b610700140044500c80920000400f103518a0748040d2004000140000715001c0c1050000074080c00b50b21100b292184110380541c4206422104408800c0d0340c0695031010040c080c040c02c05a034010034a821301a40000d03c143c130340c0381c4041241c0380054030025102c21310444007154000e00c81c1d084480306540090440707840c0d2003c0d43c1a54001c1103000c00c60680103072250140c40e10318508000352111a00030340415412030351a40410b0b244400200002640030380c0e5480040005480d82014250a4030004000540c00d4107524202d4111070360b50b404d032820f00405001d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 589714595 1250 589713345 589713389
    0x1e0a05060606070305160c030b0405011d01180b060103020f03010f180506180403031e0609060609060c08031b0a0e011106090d1809020c0d020d0305010605070f020a032406 75
    0x21282c400b01b601c8004102210f00b810003800d0820700d13400062688201c1c2040c40b05000c4c05402c0107074071004003221244094501c081c2e0780c0c200c41d42070a440c090504000c000002166184944940c0481c0605001d89090100d06040304654401d8100d0100c0c440e0100041c004040c101154100404c00460204000c0c10002c0016010608108500c041f10750f01c2000101090b00c01c1c0c00040c00803411134010b2500d03210f030345580c0d80a081c4d40c1c0038141115141c0900054814403804000c411200d6a03101c082c01211035450310740450f40010f01445048009801145102156000030700041036140c0d605540300303000400060001034222001e005550151341800740a03080807440ba0140240ea04021580c502007040b04180b51030b5580c00b10b10014800320710142115004100c03084a83d00a9080d545070316002c1c0c5080d0110b0b0f00038080e0078000351060114900040c0010300001401c0e00081501440302e540b5540c080083c00d581e0360402c0b100401300c40d00016401140141c00140c1030164600c0890018141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 589715845 1250 589714595 589714597
    0x311031015030b03031611150906180d030f080f04080912010e0a030903031e0e06180d06020d140c07080a0908030a1e0f020c010e031e0a05060606070305 67
    0x29084440d001c24144200c0d58000e9018640c0d00201a00b41c0e034850340c07501503d00c042d0400e030500b512010086030441d00103103485c0100c0c000540c041541c540c2001d10040510080f0b41140c0702684043e22522400242582c0c0d481c141d1908910996800c554208a0140200041e4001c0d0010b0011102002444002160013040d074864660550b0302d0712141c050b0000841c0940396100c008541802040016018540e2001c100d100366402512240080000c500030208102900e151600004110420312052403070310200400c01070f800c41c01404903107080d810000d00030f8884001e04840095000940d200c0c50a2a40214403c1d48074001e240403103494500e21030000c03885000030042030394030001641c040c01e5002c2e40ca40c1c2e001c2d01560003120b032106440d05010345403c5415230100400d03164103400c0e07100c81d0320800c0f00311002d00a5901810007120b0107070042d80d407004030600155142c01042590285034040c1c1540c485902540d400401900c0c0e050b0a0081c18190068409030042000b040342001033a0004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 589717095 1250 589715845 589715849
    0xb040b190216230a0e060f0901060f0c080705010c09080c042013080f0a0b0610020c010c0809120102040e0901020301061d0a03081605063601270303110310 68
    0x34000d011280f850ba01c6201000c0000c5090342e100c22156004501d21400a10700c5100d24415900b003003a0340c0d150020030414580910440001403c40744c032012002e0311900d004001c41d44a07443e5242001250340d076035400d40d420000c6010005070f2001c410000300c05d04002941e8500300603941008601d50400c1002d034034052001101005002c001000c034801202a82c51100803d5800c054078040d13508504039070388462660a090344c0b69031024001c508149000061201d400c409078000f802180800300040d620030b28244010384008a00b4042c0322400e03154844180c1c1d00020344000140d03101d00308a08100a07110150190043d42c0c4144014401103401001c141550398079070402040b59070a402c0050004102500010f215100114111101a00f403c130504280d5100d00c0c00d444041d501e20031007104848040f00700c52800e4104202f2413550641e80c02d089142840c0c450004101d10b10b91100003410340b0401c074440920500400c0320503042c164503210352407201151440e420b10b14200040002c0c902c1c2518 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 589718345 1250 589717095 589717109
    0x501051c05060f0a030302060415020f04051e0a181a0307030201141c02091e0102030d02130302030a050f07090b010207050103050c07140606032116020a0b040b190216 73
    0x41e00100e42541e6030b41c00207140000009201e58040d0307803030b860001d4483d41701385c90440d904804213000e00714091280c002d0b14180c6420131a030b03a0400f0302c0c2400300080c0c10705001c5644400121584a018140c46900c040c60103401101d0100100b0f0b00b90400e080c0403200c1500c3c1180004541000802032503034085180c00803a80c091905400700c0c0e690014903142445031142482e6100200c6545101c0032030381d40c000c5d08424800b214516200c0b013200202d03221050600c2c02242c0142c200b04203e8814102d2a4081e200307107152003071800300b0b4540329404240350481c00d0100f41caa5030710000004a241c5d40400c074003800780c0302c0c41c1018003a030900f00c00044d554101d0ba000c0d16062503100c3c4001101c0018542c1a142c0c126000401078441c841c403105020317100c0310240d800d24002d009030340c06070a003c05c44012040342000324070316045c0b4240340e48a01e030304600070500d422070388010a084c0003e60b12900343c014001801440c1155661414410402d0000301c6107950744106540045010003626040e41c85102d0882c1c2e09 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 589719595 1250 589718345 589718351
    0xc0606090603071509090c020303090607030f02071505161103030a0917160318050f060c0102090310020405041406010c060e100207080c160f270c03050906010501051c 73
    0x703035400a8100b40c802d4106040c15049040c5880c41c0e5a400001e000c200c42d20820300f00048003000c481283c50b40301c103e810200b00e9010801003458607101c0d0f4032509204040c0503005051900954036124054488140045a103490b82c0074040c0c411403211920f042c401507820004402d404d00c02c0190344900000b00402000c40c0d64044100078004a18090800c2c032502c0741c4200c0c0e5034205002c0c54901d549040c5014ac0004080303017020541400048c40000689a00414046110804400300f103001e0340501c014007011f540911a00d061528204401c1e400ca000100015880c0d0b401c04c410301007110861075072604020a0715091021998101841062040d0030034004140e041402e211580f8040300d24018111040c80001c1140604c030034080503240384548034040d100c1c40c112105a007205c10b00b550160400c1c070680c01c0010000f0154249446803803440901c0e4000000380164215422a004040c8050110752a64104101a1018040c0c180904000d09100d0304140800210101900100c0340401c24255 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 589720845 1250 589719595 589719601
    0xf0f1e0308090d020406060f090e060616021804031d0301050c0a0305041b0b120a02040302060a05220b0909091204090e0c030d0201020a090603060b0306090403050d0507020714060c060609 82
    0x103c0c1c1071203000894002c3d0081c81714940d034800003048026a101d0000001d15400e42c0442c1c040382440070039008100090810f403d0205c6010003280900c01110200da00a454424407010032403000301c12403255001e901c5404d195000b40c1211a09441d130a01c0c00ca1203039251034104801c03014940103a40300c08550789000136566586252a0600750038038000c0c110613040038600000c42055400c010b21010303141081d41358103515505040816800340307000c02907000c04207100c0d0000301032250002c1c00710658060841c0e04a2554807520704103807042c0c2d0f001a9020600010404602c2c00c0c8a400d036500995050010700040e200360302c0ca181c02c1d02540c01002986510b03801d00e80002c003020441e00140c00c1e00141941c20816103407a01a0003980041035000228000d19000285039019100390000c40f04515429460750380c5000403c0040c4000420450a0000038011004001170901c10305110300300b55002800660305101c1c045801029200040d44035050400c0101424800410115000801a0b441c00101c2d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 589722095 1250 589720845 589720849
    0x103080307050306031603060e151506030c0d05010b09100509011706240405010f0c12051308010c0e031e07050402090f0607110910080d120e070f0f1e030809 69
    0x401b15185080303140f84040004014404540d00101400c94914111070310760403201ea001d84071513011600861042c0c1a1185500181008002140d1021a031450307945401d0058120f40211842078210045540c00814281814280b0240320301468020307080c10b0303007440c0380c9100003800c0600181d0304035815002c0c10040341c01070b01c4429004090001c11015816170503000540c2000c2c48e045840f5842c0011128038000c0c00003030203041a296840d03008005030065025100050341d603036028001400d000c24082d80c0008161030300384542180c0c2c1300302c2da60302c2d104280345804141c07800c41d02910314641c46101c0c1c50300b418111400222072003110f8042c1c5015031500b9421000450801c4200703a216002640001e1820401001007600c00d00201c007245d08420584800700e42c6002c13a161401072011030b070b0004404820282c00703080e00c0700c1da0b80d410300c002259180c1c41c0045a420a2440e1f4000c000308043e54505100380d2285044800c042e1150303001c1c0e02c1243c5400758400803054520300c006400a040091041c4d555 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 589723345 1250 589722095 589722103
    0x14060f0f030a0602190c0b0c070f020901060f03150810050903070b10080f0111271302090102070b0f0f0a0e03030f07120f09061b053003010308030705030603 69
    0x10140041c1500d1200d4031504286020f54000e031042010201c2c5081c5080c1e42901901402ca049600a580e5000c1e43e036800001d0700030f1f50b000040c00d8541c0c0001448000050380c2c0c0020745030181c070b916030700e0300304e0310800800c0601030b181c0307080040c400003007062014842c0d000002203a01880d03480c100041125100c1d945a0744c19072203100d0016080c00015000c02002074003400980b000c41e1408070445a45041500c4011300b00c03a002020252900b504028610007076051810300f140540c28900c030121100c44200009811011219501c0346542e00451035207081d44c0c042c07042e20000c08030710700954a0f10050b041c5000c03541c46444081441c00c0380215200151605c01c1c10840b007141310140803aa03540d9200c488800e10b513041b40c0b10481e0150407001d40701040c203114003401d808008140c1c44203e0414203040080c0c5400300d21800b100c0302c2024151010300410810483e5070064030010000e50031400d006c5400b0a0000391100000124600c100010800500d052044a0b440417081c0b6025840c2e4071900002420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 589724595 1250 589723345 589723369
    0x12030319021611090c09010503040f03120f0b1c05280c0828050c090a02091e090106020d080a090212010f0c09080a020a09090804030c0605130914060f 66
    0x2c1c1946050300c460400001d40001400400102c656101c1660f9110580c64075204041040b400500c0c2030001c01c00084900180111951083c00c000c20a28140d002420032a4291101c002041da1551780000c010305189401222546030041281541c1906485843e074600c068000000e5159424a4091007207100800345015140d02101c2d025901c1d654940403991381c40c41d002846503444000100c1c000001900c010349101a920801400e4000000402c002482030020240d00c1d02540800c0780e42d9175a40c0d02136000001c9038250100701e01c0000400207001c00031070140c00100079984074600003980316402051096000c0e03280440032500f441d0a00c04940c814041a030500011341c20300b1185216280c10390441c0a88c0d400c0b030f0360f40c1991345590718130560351120140701c0a900440c40d00014401800250451a001402011780e1442c0c159a0754900319600700c6a480007002480100744541466a4020400020900c5020a01000510f01ca079850507000c00344c411803181d518450801d0f0240c40c1d240f040c90f2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 589725845 1250 589724595 589724617
    0xc080a020a0c08060108010f06062111120a0c03090525031205030610180302040b241b0a030e06090a0305190c08010905030a230307050705010b1203031902 68
    0x820980da83c002d5a640c060a0040700460750034040244402c01851040000711419907458240e031581da4944641c114030003141c243c072000d0311031148144a109000040c011140d40c589c40e141a881c0c451111300854000c559900c00f05800d0005a0003c25800140c01b1b44464810051800c4144424505c07001e91850ba4401014641003403280e8400b00d82103000303544581c2c0e09039402d0140300d0444038101c44543d10050840301200c02001c040c0007608003903000c03000d05000074100402d001000c144010094524402040322810b0015045c1182c010b00b0750800c080654560060103002c40503980907004e100244229801410086444100c135519480740c0d000444d040016a03401a03050005e40072201440401503450251518000844000c144245010140c02c2000b0310300700f14450300b04a500c0703104401c1c81c000d0001c00700d40d0741d00d4910b09040194050546902c1e8207590b00d1503880c000e401e60b0b510781482403090f84070901059041700040201d0350300c810801c00f003c1c000c04003001450024009c2e00b00f510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 589727095 1250 589725845 589725863
    0x152909060d0822052d0a0b3907031b0338180d111b190801050103060e010b0102100c0908061603050906070f0e011b0b011e060c080a020a 60
    0x40420b0302c4c600b5082c0540d1046800e0800c21140d0b030800d004180d031007445075840e5a0020420140b000402c8c40c8000f070480360080807907403c5001c2c0da00c2500c18400d150311500d01d507007050600300100041c58000715000500303082802d040030700e5030b100c401800190040749002103411104c515548058403509040c14122500b07506c0c0c803800d280b41921416140d00742030b54000d200319038844040758007841445800c0022100107008003501140092000c804490695800010b0307000034061400446409030042d00d08100000b52035032440c1400c1041d9050848601e00c43c0c1d03d08403032100c4036680442d80340b10b00c410800020818142802d8103d450400e50b80c441001809100c090012000032800101f035448601da8040c40035031915108180c1f07480098800d000810800a5002119801070184044080701410040f4140660191030909204924007c4900c0c0c0d100a0042c0070990a420940d00a041405115090759041150280441c2c180d004054480300d0f01007243c1340b803244200034000c1c0030f60b4400c04603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 589728345 1250 589727095 589727119
    0x804080c270c0d02160c060516110a03081b0d0f1b02011808010f0f020a08040f02040609060602060603070b0901020705040509010906090f050d1704152909060d082205 73
    0x65920100041d0481e46d200c0020b00c0003d046100f901a18012914000d06080703c044542e03910320381c0c1075070940350798100303a0036000000410106d002a2036075906e000c044180d83d2115800d41070034409a000b00710284002e82c100300a003241d01c00c1820f04003844010810b070341e4014500050b0740300d03500c01d40c0480c000e4400c94070120f4510b0701034120044400751760205004c602c100110400c164054000300600203a4120002404220000000e0210f64009040056180e13228049042a180e00c0e030469800b6038410000d01071103050410920b801403442c1c1401e181410b402d00c3c0000c0d1240d400b8403680b0b00c95501c1b8070110303801000030340c032400740d29611003010401001d40c1d181030802c0300c6000b8001e44060050401c6c015480d070207002c4e24110105200c1900b4020755590741ea0050100c2e088800030292551001000c20603406c000c640d00400001d00401c00280340d40c1c00c10061104002403a1601490f81070400d10005070060003a240c0c9000c45005070341c241c40c03c880851310344852603842154000060411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 589729595 1250 589728345 589728367
    0x506041a0c121804060e06030c101103160218070e0d170a0806011b030c030c1121160812160b0f100b12040201050903011104030804080c270c0d02 64
    0x201e0345140000b0f44051000540d106c1000d4006242180c9103a0150800388003107400e40f40040003d44244241d003015071203014244070851030b50300319440f051803104801c6a043c0a5240040e00380d98020b01440102102e445d20100041030610cd1849643c05540e81e6010107040080c5168480b21032450743d030300103031030b0210705000600c40001601d007030740401d04110300b450103151140f201c030035283c1e0980c035000030030500f03590106c1c4c40140910043c0e955091141c001c09041e61010300a807c0c0e02428101c110003540340512140c1001175000301caa44141d010842003090302d44c003146902003140b0810340540c984e001c2e0038800350220001e45004010321310103020040c0d40e03d08102c0c49070003000f1100c2c0350305e0a5030f124035050310144141c3c00f540b044c0207803110000d0b006620540080c000380c10040d0012600c401d80399200700d51508640c1048585400c0446c080c843c4070b4003000b803c02c000300200da04071950a182007a1074440010910a00607e0022200090364a0700d00b00031190b4103410614115690806200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 589730845 1250 589729595 589729627
    0x10f020406031d0c1306170d0e010f0918060e0f0a0f0b03101505041e051509041b050a0320031b1c02040c0809070506041a0c12 56
    0x1c1c20020928007281c03101c45910a504403068014158014070290308031008001c406140170402203c02d03a2900f40106044441e0030340d61040700341040040000424911f4081c03c0c0b83e40c09118541000030034802d00071140e9210300207004031111400d110603014070491040c0e014004680210254070401c030103000300f02071444451803080900000800000704500e010005842e90b1a0f1000d0749903115004c1030510764030962003021400c20240001c0146a1b0b1180401e0907100c00d800b40c00b084510410756121103a10b5401901d0f403004180c1c40c041d126440b450002041d03814013910241004a0014245221621189600001c2d0400400c54a0200d9991402140794080070303003440424105640c0350480fa007000a03080c080d0901500503541410141d2050003a4132415000940c01c12545491140146e2250701c80c400041078980e81e03184007407138808403c0d4900682d42d032140c0e0150302c041104001810650703005500b800b5410400700d60307804908a101d072611001da01c8082807041e0020703d64024061500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 589732095 1250 589730845 589730849
    0x70623040c080f071a09030c090106180f0e01060807020a1a1602070e01051201060f03030c0b07050c15041103060a0c0f0306030c094101080606030d20010f0204 70
    0x1400c45603074818034021241c5030081c80c400d1100e94114800d00b0f1303c80120005c00307005052009000c43e013000f110800090300b48002a4009004100c411905280109110000d5006170080304488816503107013345000505074140720b030724104280c040120700464424801400400d80100d200c02000d0362802054050410540d0070a0b04051600c8050360003d001141140c2211505000c2031030b96031801040c02042c1800c072640e541295078900004c144807014950a001450090ba100704075866a49401e902c001c40240402d428010b0070310813000d010030000303200c9080c0d14400314440e4007034469241404a0b880c01091403685801000c04204454003a0340c000d5580195aa5840f480c0a4035150190204ca10074000504200b09126050140540c035401210100100348040c400069003440d04130449500c51011003122842c0e46224503105801403546800343c009040075008504002000a584a00c0c04203580d0a0000100728410400d0f0fa140d40181c200195000900202034208a001c0c0294040c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 589733345 1250 589732095 589732109
    0x7050106140f030a05210c030f0409110c0703061d0d170a09021315152102120a0b0609130b1f080a02030a020d0c03020904050a0e03070623040c 63
    0x200080b0401e8680001c00c6844107802c80c02600c0204480c0c0360441403400702d03284448007140108541600c07400c0820007001c0b021001c0c0252030300d450812598106031044050b01516aa005001c00f080600c404182241100d600140011348958000004c016050809480344014003e000c0200c035201d070008030f0b074204501c03e0301e0000f10a0f510030080b5411545a0280a034008202005001003c40e00b6445004c81c00c2c8030b51101200700b50b40e1540550000c5450648000183c0120a000072800707000d081d9a9904452030415401e104850300110044000149030920749030321008100025151207007110101880504140741c04501c2c1c484920185c140070720070310300404080c08445120700101d0101e4884030383c41d60701d00c0700310b0b25a14040c00c0039400281410021a500b08250341c142c07012485840700d540306686001d619603610900308012034030001c0c80c0c060087e0821002c201540c40100880e031050390300c4100064a45604282c1c0024501c1b003400d007030a407600c200188003d110320065800226102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 589734595 1250 589733345 589733359
    0x1806020c0a15021506040f05091f0218010f0c06050a060e10060c02011101230103050606030606060a050a0e06040b0c0706030b060a031805060a0c020d050c0703020607080705010614 79
    0x10b220500241c1d007018400640068100102c00c00b410341d130118400303410003001000420000c0c1c810002a084035016118000c040d4043d100303141d1541c52889024010a4245c04110b080c2400c41e00012220400516038030f04000c0405004943d180c001d4800000d041c0d0400b0b4108254030f800c840c0c00000b00383c0d038058bc00001d001000060002070311200f40009a40d2103a540050394206e550040d90000d450100c01380e00d65480e81c2e50314030122207841c00300a141307540d17034000c0a031540342d402c0c500c1c00e108010300403e001380c010340300f044480d407038480844d501c8041a14101340c0c0d5800e04002241e0481c00d100460380c1c030200004000a984c2d41c550050910380300490b0954190a039030b514254100c0361512403060b044607040c4880c43c038041c0681c0c082e00140c160501040c084040c1c0b59100780c2007007400c485a0344020f070b8800c8542d6085a0400c02e04065040030300f007480c504120415129501c03442d62000a00c2a40006032000410074002d0913108210740c000c000380f20342c944500300042c0311b0100041741805105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 589735845 1250 589734595 589734599
    0x622020a03200405010302031312020102070b13020f011d13020706050c1312031707080a0515150d061a0a02160315050a0b1323040b161806020c0a 64
    0x240071901007211076015200340740625000054002e500000c0c03140141d9141c9103048800300c0d05d22b03800d664000b11240e00069440380546030000c40e408015001035440c00c2180f40c650016240c00c500b0003032400c424201015100220032010181c5086004a030ba04003005070707050700150364a90082d00510b03100ba5418016680c1d035103000c0441340183c404070001a940440100400341003212002c0750140a403901001c2c81d251802c0303103135034010141c2c1c94000150000081003404070952040d80c1d0000d88074000e001d100c01a040010f01f080c8064030310942c1d0a180090300310030740d07000c0340d010000400300e01564030b9141d4000c89201542d42c000c154170348054004d40003803880c2c1c00c0745c4c104c07c082a294005034082c08546000f041c0300040800a0207a5030166440c8038405140d600e8001e03c0c14071209188002c5030700406a00f02c100d031b00c000c43c03558000c42c04ca10070030702c80003035120108036500610070342d010031844000d02c204540d0300d80725a803a464000e424083c041901640403418041c00d003070541d01580780325 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 589737095 1250 589735845 589735871
    0x303080f0a0c08070c0804090507110606010201020a0c060209030f0a0c03050c1c03050711060d091a0402101d04020d020c010e0706020607030b0604050901082a0a0b030622020a03 78
    0xc5114079004000350f10980022100d0b4041e110040056018051490801c1c0c0c8130003601d03040304c030107a070503c002c035000a82c00b44404404124859001000780300035428100035510151811600c1000200455008184d00b101620100300908408800320304840f680c28039400e01c0d10203000b40f40000c4d502406803020f6004c0900748269013041c0f007030b8400b400342001000354400300c1c6d080e0840e85040f0788a0911240307480c10b555a10000d8403e94681d01d600107050001450201e00c0e82206000c0a00c10785800020007000d0b80d15074044090195090034002c4100c0d0360000f07803804400d04001c4072503010f403011401040c903080070385c0900072860265000300f10a140a5003038030b0f82e03041140f2580c0016402600003c5250344250007145403817001070070003030925850314000348042c1800d0f000904660b00000b44840201d0f06d0001c03200142d4140c011042c1c0b110201000702c2c00607040f03030050b19000360b00000800d2041d11900140410b205c1104d20f40d01070101403500070b10295100ca070040c40002e0030071184203001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 589738345 1250 589737095 589737101
    0x1205031e01060e0111031204140118020603220b0907030605010512060c09030c061207030b091303200d080f2410110a080703180e0a090c0f0303080f0a 66
    0x290740b80761035a0f0b01801c0c0d44001100c0c1c4a034070445428940c0003d02c1440452101407685034080c1d40708510381c116081c1007400580c2141c450303821000941c1101c0c40c03140c015890b001c08030307074001080c0d484224a181700f074000765204071601c85e001025801c8410410a80d80d202080b140c041e28881c550912481e41c0e10000c01c10212085000d240d82d54020501058550b5001d40003018102e80c05811f8800d14408040014541e0f040490304c0d5030950548400c00c0920740d8140710305004407000b03d50301c10311401c5c02c00056441c0f40c039001e0014140141100044d41042c03c1286012420103080111341c1e004019810007421248259052030204170660080303011001e035076906080c0c020400c014001040100800c1003602c0c081e401c100d10500c003001e811130016820a02504056600900304039a80d40790f40d1034002d14035402c0f070154404240380b1442c00d00c2076118a03412184c02200154012070716030000e08120600d6460f0740d00908055901c1e8100008158003d412248565654809400039554150200c005c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 589739595 1250 589738345 589738349
    0x3060403170c0309030909100b1c11130303030c05270a0501110c01032a05180a05130203040201030e070602010f050f0105030a0821131e050601120602071205031e01 72
    0x4d80d4200b03005003585801c100c0400340d4041e9540442c2024950786001030501ca07845411000e503000c034494480107003503600740201141600d42116140c40c01000c0c919484400c40540001800c240d110302c82040b015108d0025110072114240e1104c07058540c003041c0c2d89100190002c0f05010b20000c180004180d0300400c2c0205030241c0c0100a0850310407801c0045005050411013030002e4013441c61b8604803041ea15107040e465004a450700d507569400141025518114030008501c202e80881c2c040c002500c0d02c0880600e050000c00002d601e90312544011783c094071608010a501e0301c54200005103040d0305401480400958400400082d2104030301c50350506401d006064259000c00c86400001c0c589a00514407030308400031703043c410744001c40807001100043e98003000b136854111845060007014800c54509806117002d681080005a8903162600070510920f5030160380b00450300e003171043c0f030b40441c2e807010341c8070100d006043c0d56448007419642043c1d822085404403a0750f422032801d0034403400340c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 589740845 1250 589739595 589739611
    0x50c0732010305190c05070803130b130807141009030815040b061207050c06010e1b120708090c0a0305060103060b0a06090504050a020c0d110d031808160203060403170c03 75
    0x9119000098883c0145c011520600c04200c4108100700c08526400051400380d003c41a60310280002414001400c60001e00081014440200080005603501d0111400780354040190801103889440301e504044410305c0302d128050400282208041e4007034544d40c4120003403450942c0c01d0400c202404126000e00f03c8140d08294104118403040782902101c42c0d02101718138003e8582114900340c40d0a00100382c0c090540e24508005026411000c0300600864400c581500ea003000c260020200c1c06800c09800311040c031407040082408004140007800103400060188124165285400c2d82d842000b44029035146103040502115403400c41c02c404120b5000d69039103480182444200001441d000d85801340b240d5080100d5400000c00384a00b10050050341c4800d01e240c5240d00700c45007804a95925201094540f407004c014a05007400d54805003a0000c0340c094070703011102100d024519659401a501d0702c510740420040544c040260249540c00c0c0c0c00e003c8080c4c45180d510706090100755803c0b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 589742095 1250 589740845 589740871
    0x7110304030c050906040b18070e10050d0e030f070302060901060510021c09050d08030f0604020a1d031204080708070504052806032a0f0302030607050c0732010305 72
    0x854500020101d40000d0010303c005000b0b5121800221284940244403040b0300323501082000c0250401000c05000e4401d81c0c0800d0b500c0c000000082652046010f440071030755461050001450701002620718400182600075a035103100c0c20060760f65182151110355543c00d005000c94107060055a0350b02001c000d4000f0101070300803606602d02203002070782140030050a10320000c4d050b80c8181c4c042640a0045c0724095480c1014080c802c2c868000038203090286004220400c9460382c0512500500c03403d2204d4590060540300020342880f1024640c13101e4a003011402054001c40800d4030401c50b035000040300c505543d10300510040c2e0781d00700c1d5100810600510900c07040c01166445900d4071000c5c1400040300c5840c0da844003c131051480c0c3ca1851100b003105515404450808002d001d010900100c1804a1540c0c0c006543c0d08070050500c8100a070104215022180c1040404c0c080d040d2000d0b03d5100ca2213150070046508080c00211207a024800d8040145d0b5000b0710501c1c1c040c45141a001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 589743345 1250 589742095 589742099
    0xf030a0503010e1815060108061504091a1306260309040b01030f240806061e010516050303040b0703020a0c1b03081c450b0702010507110304030c 64
    0x2034000400800b03503c03200b0800c015034400c1000a201400f174442c00c0a0072400c09040c108001400c50720300130701407405496039400c0ea8100c0d11b031060551f022281590b10104014640940c0020800c2035050b010390059990401e4400c607040507045007059070000e80e2812000751011440d01e240c108400381103601768204210403400390500c6c0c0c01c0302c8e000403c18100410780c1da00b210030740002c941014a00b4440c2e00390403500d500c134488803040c0d130a0080c003200d001000c0504081000030018003d520350710510b0941c030259800664002e2041c0c4800d070070f9013680900d0422950078519220351044800301c0300c002c2d000c00081e40060081c4251855858950742c2d2914821641d91f40000480d0310044a04040840480000c001600b501c02080c001541100000040200c01c507203405807460303102051100484001c802c600f541c146a1401b840c454400124402e540320014205413071001c2c614040d040d00c84400400403142c0d0150020b6004114a9503a0784205511032032103500c070b00880c0401480d0464031503007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 589744595 1250 589743345 589743359
    0x501030b0903071223130602010c050a02031204060902060a08040302190506070c0203070915050301110f0a120b0904031106091c0309080906040314190c090504060605040e030702030f030a050301 85
    0xa0045e891180c0c40c84124110a0f00c10f0b0f040d00d03a0068444d001c40c1d1090300f0402d00107180d082c0601c0245103090300b0036505000c00040701035264058003001c5044001143c00003000d000543c2c0040001c04e8021341907d23171714076601074020f144907c03c82d0160b001d0f11498401070807501e11109011011034002014000c50348501d007088419201001c0306990600c52b0840c003152404d002d11a2940d44d032005a409044585080c0c145425100b0040722075024042c00d008860940e40c4d200d0845242071031500d004107002d801250340b08010b019444420b50031000da10200420590052000c80c0d00c0c5800408441e202c1c2c0d2104501540d0744503a00c43c12103801840300032510301e43d020350070240304184142d000c03606180c0c0480200c0e00c0394001e5401514000030040d05928203081c00d0181c03061881011072000501501c2c1d450f01c000c026218030510900554610008081c0030041d400349000e810000d1043c8000e90212800c0c65594000c2c4509910a000d194864030306924000120780030741d922900d031541140c0c079000c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 589745845 1250 589744595 589744607
    0x402060703030e03030a0b01110f06011e1805060f0d030504121a0705040608010902030615071e060b040b040203010503060a0c090f090204090c0509010903170702040504060501030b09030712 83
    0xd000c41c24036444400501c5111024030145115400e1703203d000071204004d200040c1543c04641c5031107256000b42c299103030000000700b80381d419140311032040e88054181c540020605880c039405100350741a90f032007869110156411a50044004441550000c03405a0400007080c2020f4030044c081031040004100c20004070f000284001d000704000c6100b94141400b5400700314007100d10301c2c00548006014031000d0341044100307024100b40c0c02c0031400c5290100214800c10781e000422200c1b8100454144100101038004620b02d00b10b105100c0c004107401c6c41e00c200944181100580300303c1c1803843c440d04504007403003135034102e071801070060a02c0d8070b800a01d00010328180d80076500304801128085030705207038056250002d29481c20700590326858a000c94080b5095000e07070000b000802c100200441c0e03441121042902e40240d24440c024a000200d448a441840002034005041108120501c0060b5201c141264042c12405e0041d65480007466180c3c4112a4020000b0601200441210303114030307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 589747095 1250 589745845 589745857
    0x140618040210210902040c230306120d020c0f040b030c040f060f060507210f0809010f092108060a1e23100f1709030409110a08010e010e040206 63
    0x42080607101d0f003180f03000f00d840d4185140007825140c90b5610f180031030419205003180320750a80b4041d000d011401d400c60422124108031810303112408001f140340c1d07681d0301d0440d200340c0b048401200c84c4d1006074a03010b504d84030f4108015103d5001d24000d1180c1d410103010b07841205000030040c2ca00410340c0020840204003101910398440e503901c7c404a501100340d215000036045640380c07161640b12920b01040b41d030031014990f02e6081d20349440400030a40100900c6000800303414002055943c410b036060040c82030301480e1104509104c900c509001e80b1264072428910043c001c50111a90039605844140048d22600e81040900701e040008441d400050050146440c5140c1d006070394402951001454940380b007003000120950008507890701c01d20b122866103250800c9044c070f9280610141c140c00508007001c007102c1100340000c020b0741c810701c202d030050448148108588050710308041003507084100440d010601c410f00120b0203600c2d2580c064103c407843c8804841c00c0e615942441007030703003000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 589748201 1106 589747095 589747097
    0x109050a06030206040e190501120c080106060503010b0708071a22080a0c290708090307020a1206021303111005070209040303090807050304030501140618040210 71
    0x403400e5a00301d07031654105118035a1f50304880c640c150000e030301d0004014680800413801a118409000405000f2044905066100c00005080301c12601645000c50740500040250007400c0c00140788036840340804500703026060f56048490f642d800180460304824030104060403040c404030411104100860a0240c01d4503103660b9150b100703019450741040140c000c03800c240405808084100142c501002a0b403203d80174940c500b1100039211400090511008100c403041c00000342c03901c0765002000b03c2c544c28500300500b00d2414080c5022103c580c0c081c04806c440244090354140214001c440e1200703c24103007401c001219032049036110038460180020030150715520116030703005515040029845015081c540440c0c012140010a14800028080104101908414007402a01881082d03070f48800c000c002c1000388052200305c4146054002401510f44080308407000102 = true := by decide +kernel

theorem cover : BRFrame.Cov 589568345 589748201 := by
  have h0 := BRFrame.cov_init 589568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 589568345 ≤ n) (h2 : n < 589748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
