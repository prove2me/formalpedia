-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3385
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:44.013442+00:00
-- url     : https://prove2.me/submissions/a78ef84d-1204-4cbd-818b-d5d6ccfeee30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 608633093 ≤ n < 608812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 608634343 1250 608633093 608633111
    0x9020f040c021c020a020415030203070608090604060c1101090803011d1306150b0c01060e150d170409050c090328030c1a0415110f03010b0717030103030f030b0103 72
    0x3929201c8042070f03611020200042c0c20100c510812070842840d400070820001d8103940362500001c01d01610049029018003000044e9242c001d100a40c424080280500312503501c0e42c2c1c454008000140c0d4400500000004030440000c0900c0b07449010b40c414030740c450b03580d4100110820305002c00315100e0080240740781040342106618490609469214801040e0640441c51b002044000307a000280c81c040041034103c0302001c15000001140e401ca0414840307134988000c400784110041d6101134101c5250b540c8400050240c166007850080d10440703943c1855180e0032503005035501601e00070916a00071132022100e24042c0301c0940642c1c5003072007980000140108007040344c42c081201506001c602103100003804400e41c607101c41d0041c06c100000302440d2500c4c2c28070924a0584425200c1c500d8698172048e1440c05504039811044450000ca0660780381181c000c0300b0381e07c02c00048450261103039000011041e82805113003e144207403913007140040780b030200a04a90700100b2417810141408000713 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 608635593 1250 608634343 608634347
    0x10080d031a031605060309010207021201051005010311220b210105180c0a090e070c061a0a1a04030203070f081501050d0206030702011407030903020f030a020705060d0f0f09020f040c 80
    0x3160840d0750595261b0f40300d549400b0201d009015890001e0f4000a85200c030542c51b1006502c0f1522580c01c084030001d200c0d40b200c0c0114101c43c3e00e81c03041b021a65040000352100c0c003440f1422114400400c00209049444d504601c3c0507421000c034403050851400e042a45180f160a0300c140500015214642d0584595607001889000540321302d21400002540d19415403103444103101400744405161154100f41400408240c01c804056483c00d103001c0c282d64458205104a640c14180289404001400c000b052080d44004003018009100c0400001006031003d1105500600c481c9858030b40c80791424047c541031550145000005501210040c00aa5200e50202901a8040d11303000e480341e48000042e03006100103400302a140315601c080198080d850b030825078a551080e030036542406060680650b90307014090305840540c002c2070090041d0b05000002c0c0058200b0801d01240b80c9800000312002c0382c402040c440140790300e540b401c0c000d600b0881e8a00914080644081254101403180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 608636843 1250 608635593 608635633
    0x60d05190311060603120c01020f030f041101110309011215060503180a0201120507020c041d0c060315090402031f1415010804060518100203040618051510080d031a03 73
    0x111b804a0540840c0210301c038070096040d542c0381400242041c1e5a410841d08800c0008011541102ca07000360b56801d01865108d81c1c100f5030090800e10045040100350030064031100040482d0010302545d4028421803200c4040001000704090349a6036130360700380282d010300840000b812046071030340700340d0704400180d90003130403038040090b44200020a80c0b6500300403400d100d403821710b1540c0a424120301c0c3d0160144904501d4401410344100d8040350207940c140100c500007190100380b04950050710415070f0410148603584684000c041d030700205500070511210308440c41c0d02c20311040e919044031510417001d1032003075003114100342754041e040f2806000038140b520082004144548910114903044074504089600c20006020340c1e030549029805d09000f90002c8a040c0e0b20207040031400d410150703002e9500c0000c240c00c0300c080c0075135071600040110380c014064124400100214400501c0381824040a1143c0071582e4011880c800c803800440343d50321440318468442c0e00305413000210b061070410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 608638093 1250 608636843 608636863
    0xf0f031906140f0a050403111c0306060e010e0d050f0f0706020705010c02130b030c03011a1008010e28050106020114010f0602031c0e1203010e011208030609060d05190311060603 78
    0x2030081861b68461404a880c10145402c0d800c8034840c2c0410f209061000042c45e55500c1e110355000c200d003a41d200c004031010500750002e5404240f0301813051041c0d00742488148441400742c2c02300c03804610b800340e4061609a22000c0554250031503401480030560520008004003000d00e00071039044182d03000110004070b404031072110320360349040c40b502e26141448508000c1d44024001c202e50014103110340403210305a0b050a2040c4440848600014098181581610040c0164a52b5a902c1307035071402c1405659580c03005031824100e0120003e80d10340c0102c03406801668008a00d085101c110b44400355030681110f881ca168103c0e0074840070780d00005445051100d00365018009191022810080c43e00c40c14071000e81c020507110b00400c1c90101c00860495580440303003000c070380ea1201c840c005001e0480004040c10b10030000b1071034900d44151507941000c03000304010b0840c0308558074079181004c040000030017541020103840c20b00d44c0004000f4142c3c5041d03406040c2130b1810034002512404409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 608639343 1250 608638093 608638111
    0x60603100312031a0915130612080c01291504082e0603030c02090406021201030b0a18020d26040603050115030b09060f0f031906140f 59
    0x10000501549804a01500442d0044070304849402510402406825060404006882d000c01c04c032030541440303c51140300c4c256442066501140d10800c00a00c080c14420b04124641c481c03034003040c0101c440343c08407031003482441d05030350381c010461903682035449000704481d4110718a54806583d90000145d0350001e1012214034603804104041a4040e0003150060301c0180b00e0322030700131003200c0000400340c1503c030501114030740f0000044040059607007038003000300000c06030001d60005051410303503907800c14410200581081c1004c12018188030090b48261401001601130220100c480d00c11140001590310074440104a15008510b84140c801001002c000b1051803400c24071038600c40221021050401040c1c0d42e03980c5510047c013403c17084c0250900c03110300302c2107038602500034464120301e554060040c0003540d58507400c0244c4e610200c15042d400402980003066a550706000c0c81d62038501c04251a42ca98005003001400c030b640340318105081c2c0c20382000340200d0340b184c80b503080d511407260 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 608640593 1250 608639343 608639347
    0xc090b041e0212010803030c04060e010903020d0b011503020702030303010513150f0e010509090d0c06020c0d2d020a080c03070209130201110c0d020409050f1603060b0312030606 78
    0x50008a001480ea2540c8007501d40c40407540540940345a4008281c0e41489115001450340c035980b01039102d10040d140b0b99405203040204004850040480018821b014100320090685ea07401140661286a500311450030030a80144940840707064070066014151500314101110b40d40401e40c0c0e448180200c5201d2130340d180d101d00b40c1c4000360b0003210300328030100904a00c6036920310340601101d0507030190034500c0a440d130021545080c4840e1a03441949190000c140c008080507090b688405500ea082c1c80c0607400b0000c8100c503800800035803194040642c0d481d4203094507104042c81e0801c0c1c5a102001c1000300c0da02406041d94001441100070750460000ca540e50300603808030b4135512403854000d410200110070066000700b03002d8040340c4c42e4001c1e01c881004841594403181c03200004088240d1016061085002500b070503407013181100d20a900321490403075000303001842c0480440307480b016054030140920411465020b20403045406030014408007581060b9980d680c00010f01e628029100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 608641843 1250 608640593 608640611
    0xc0309070b0d15031208090303070c020f010905031b120d080f0c192f0607050a05120a0b011d0907030f02070c06050d06120b0403080910050a20070c09 66
    0x80e4404801c10501003496407032503030313285080201c440010724000041501040040c401c0c00020080368804e600e26902c0c0d0b803c070900c0c0c1d4208004102900040b50400c4010b02e000305950b20b0800081094011096044040030400c10401c8403a4103203000409040d00a41420031640307400c100e07026009440c0841004185d50740d802086600c0c02042c802807500e2140c02d800d040300b55000401c40041a83c4030705c80b41080003d0b000654042d140c455048680b5600020005980c3c2d0b10410103003c280506240c007501d4141202180c003c508400d4501c849155a00c043c0e072580ca60b0800c0c18503d5a180c2c4480d8000c074410224006403034520000c00580c249070711703030700c0c500783c403c40c01c1d4101c1d400d05a1003e0000c10b1607460340c0307005280f908016800e1101c1c1c1e15200c004200c4007052000c902c05e07240e015855540a541e207540c00c0398494000b4001449910461810607000c1002d401660b1094500d11070015003100c491000785022070300102400250310f8100302e0346000c500002556000d0320307140400030514241c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 608643093 1250 608641843 608641867
    0xf070e16021606050306040b1e090c160b2d06010518090f0a1d07180e0f0a0309090b010c020f0307090c080603070e010b03041511030106050307080c0309070b 69
    0x2010b200c0032140641c0e078690210b80d45412002642c09940180c0c1d08100c540c81510a00a17900001c2d41e060801c7e03242d00c05010a13038078000c08480d80c0043da50b440a814840d030a2034404c000911503404440c025220410008181102a06458107003001e07050711082400d44c0591306524400503044c035042050000b41b0001101b100c0088208040380501034640c5480c10100348a8841400e42d4200a00c80c00d0a00b0141c05640c85c200c01c400d071141c0c03c0301414000b881c104082d17a642042106075200e50b40c44100180c1d1300602481060000e0304140c000d40303041591352500518048443c4c100000d4580b0745810184541d90014001010781d0307041c0c0d0700800ca00f00c1c074400286402c0e002e52040e074100742043ea410456550001c081c900413002a812200134039200c561004012409015240a8004c2800020f01240341c0545c4502180c108102c0002c0210220b85041031681c400d0b00301c42d02080c1c0c004280815254032141003a803098410040c141542403243d4003980700d108500c5000400742e80404e010b050b8138 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 608644343 1250 608643093 608643103
    0xc0504030812070801050103110901080a09020a180b0604060c23030c010b1c02090601140405130509060f04080409090606080615030d020604020f04090f0f05010e0f070e1602 76
    0x590401103031920303030500789010800500c1c100c900c000040c41301000040d80d0350103400f8a0349600a00c0300c01c0c0303041034425401101d1401c0c004142c4c0e03500c0d03038032404001c0150b01c80e1950b05016004441c2e01081b40d43d00b00960b141920f00308405540100003c2204000580d0b04c183c0040e50f2580c0000044e17400d500710a2071051310050101003044501000a0302880c41e5015841304491304010349250b001510344010002c0d40c40c803020307006500700d221b000008065601c1000c41100d80031981c5241c9040903142c00104846a84031903043c00503982d140d05001c6000d07400c0104540c0020041d20030070325440d00c1ea455441030f020394441c0400a40d01e03281705604015583d0003640140c100785040b00c0040c0350031003218280f090303480c3c40355000340103500c1c2010040b803000c1013a52103141c0150042840e03100c0281400010019107a00b030b104003101600010014000200004035140079400100c0e20030708000500f401c0103485a105551544a50401c012040c3d2190740d00307511004126035446500f00d214000c1c0e040c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 608645593 1250 608644343 608644349
    0x10050a090c271505040e220b040f0228150e040e031b030f2506090b040605010b0702031507090503060c0d0501060507080d0c02070f1211030604030504090c0504 70
    0x35221500a2a4070b030300c114540204840c02c80340c02c210260110b4400341c545128500458051400318400a078a00c1610303c100700d07172401c00c0c81070960940040d80302c4a03203032001914205c40003c40c0c0000f220940c41d14480301d00c0084005803099039121494160b000d007a0a10784070751415041c1035040100118080c00c55600a16000f403c14000c0304404041d480e100d40c44010101d0002445a00c1000c0e1820000140d9650543c0040b8003890162400001001c010140c10010643c0100c09000c80c000f40490240740a500d10880c01c003211401c01c0c1c589901920b20503040100e040000340400c00240e90000345004203944082c0c108421600c07865411111000542c111035090303c100d60a01980c015640020002c1d00c184039010000c0381d896000454092040f40005006904140203c0c843c10714260b0040c3d15001e000e00445440550300c04a0a06030442c69121000c0c1c0d0103010a41010300100400142154030101c028051134139042d50080c00602039405179407030443d940e0f05da0362000380c0200122409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 608646843 1250 608645593 608645627
    0x1020c04110f0c010915090f0b0a0617030a0f050a0e0108040507080109151406010509120114070c0302100b09040b222f150d02091302030f10050a090c 66
    0x9900b0014400501901d141c280c00c950a40c0c02e13442401b0070101324800c500b00103038003e4000d2a501d2031500d500c0f050000c0600105d103040d640d9900000c1148a4070640d441c98803a070005035440309103c640260101049054030700610400304414a100381e07000041034020542401d1005507915541001450322443d5044040c0641ca000300399014424504100e60740e64600c0082070003003060119545026a20558020380403174001d00901440780f51500c0c1e80418080e1800001401d1134101001c88984d25064808d0304c0864904003c0c4014154140914140550180000d1008010300c00100700d40680c020700151004041c80c2c04910302039a210782d40d500c00c44104481d044a240c040c2043d181c1d04404800888400c4502d0000364400f010600300000e4130303070740188404a4540b003188000000d611a50418403050b0b0b0030032440d282c6039200d80044140c00b20166005803203140084406c4052080500b1702148590015400c100340d5640c0700003482512583c05000c5004800508240c811b48a15050071035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 608648093 1250 608646843 608646847
    0xc1e0d06080312100308030a050405190803011d0108030d09030212071b0e06030a030f18170601081207020d110d0b0603191110090f0f0f050f01020c04110f 68
    0x2400700c000101a11031050074890050154031815000c003200f034014400200943c40c01c3c40010107109803035106e103600c68054410b5580491045054460208404504036091a8040010721030300d4044081c985c070b11005000508500c0d4140032a5655a0140902a06000c4e0312643e00ca400c2604c20311262407882e0701d40c0d62190721703055545010400d150600c0c00010240c11503010025110340044042c502500014014104c04401da40301200c1d80c0f540c42c51081e09200106844c0360440741c1c00d415481c000c20b403164150384542c452040c0c0d2800c04106912060043d808200011002600003040722441941151440d80081c2c8900e07054020403008440d42da40a64410803480500c00950a054818181101a200191640001e00161100580b0081d040b00c800c115440c0b01e45c10100151515240b0b28140f481000343d071101e14442d885a0b03034002d481c0b207044605080010040000121016203400c54089645403048030000f51359813a40c9040511503529402d800d004c002c8000100c440080c1d00d03824840d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 608649343 1250 608648093 608648099
    0x31704170a020304031104090807020d02120d030209100806150703031805010b0a09021305130905011b030b03030910032a050c1006050612040809030a11090f0c1e0d06 73
    0x2a440e5041340c8000d43c0c2140d088040c0c50580e18151040c1e402007580b003881142030030355a80910510703448140c022a0021408400300441c40020011040600f80039640907a407420140140a03810b031001c040c0c041071251074024043d090b55040d200003001d41c40202805d03210b29603814100c0107440420386070704a250000884206002c01900002d5030b8250a440c54130480380d4800b4040100d2240040d0f100481010002c00e12043c070780746d81d190118803030344040440e0064964580c5800c480081001458080007101128503554040c0110307011a50210061414042801c001c42e03141343d10032140000305955003410b07021450901c1d48400c903c2c5402e445849803024410800360007640160341e0404613218010a04d07018091078003030b46041d0340010b8802801c00e24007425107034003924090000c8421140c00c1c0165510354408208445200d0f004034914480721402000784030950344050302e06040c0b61646000c0001ba880c0e04402c403540b104024000360a030740305070318050303240c0e000321110030440c175003418400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 608650593 1250 608649343 608649347
    0xb0705010f1d150f0115051c020c070b040510030507030e0f2503050c09100e250c0b1f050d080a1404080d05030a063f031704170a 57
    0x755049842e5900315981c0100014403090004801c035580d400f0001ca16006118400039090b603103004820904100b82001d15011a140c080d0b04001d80184c0c50744d80c0441c0410011504108890060440e01c001c680b41c5428200812200d003420030946088c107403201d0210301882d1217540090000802d00003640d4480e00701440d01c0da215802000002c0c40035003000e01098840c60034544250440e039020000f04031102503030052200c4140b00070542c03082d08142c0f0000148845046a0080c41149060000d0301a02030751110451755403903404a641c10440d21045140001d101007070201d8120a00154004104110081d52410b5450a41190b03802076940c00c007542c10042c0c04400390110305410b03144c101c0354100840c0030240350300580c422560142c0c40100040101c3d4001c82c0299080b07454401e0104030240c850500c2001c80002c03050400c060400b081c410741c0c8210235100e812358844a200e9050f416101a074800500a100c0054032032120041100450200712a00d04a10b4204030305114903501d46c110f020740 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 608651843 1250 608650593 608650631
    0x10e0a0b01050a211b081606050301140d0503091008040c0608090303070e0303160305091003050c0711060918180d0909050a0f06290406090b0705010f 66
    0x411208448060004030b078602d8010105000e0301d25403808040d0188401c00004410701c4803000035680d050b000c901036a20240b1809503000034010309401481c0701088404d03811003081075a070002040203818401402036a00c071040300d0400050849280d00c00360b03428180f00742903218980486501404d005608800e41d0b0b0046aa2441030380203c1c4102041a507d000940d0002012640b000346901708000181240e4010540c4641c00c01024040742d0501050762032401d0355040710075054003c01c8002c100080c5034a414400c00220f265586414000340c1881001841d96002d1102d005049112041e04959030751566001c0c5c4a030b403d402403840320b80200b81e1881d008100f03001e0b1340398002e03c550000d0405021600082e415040c10a030f40d01d800189180020100081c03001409440000f034580c43c0c0c55208440034010000500b0780e00c0d28120242540003040000c6850715200d000e0482424041001340c150000794145c1251a0384600340d0fa83c80d002c0c98120b00502c0c9003244400c1a525224000d000550681d603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 608653093 1250 608651843 608651863
    0x230a0e0c030d08040f0c05031f050a0c020705010f030f020415120912200d0f12090f12050705070e06120303090d140d02030903090f1002031e0903010e 66
    0x410344110158490034540c90303110000c030b0000424843c4001c40c1c0004c680c00010300102d409070464000719070710b460019090010b01d075200d10402d0400d0b00300c0c03040c00e00c2502c18103400c801e11a00c10400b07010070f0000a174803040d891003818140310662910201d80f0b4041c0d0400c201c0d4819600046580b60f031201005500402d08481c8000040d00c0c10691408940840c0302d5825565000888640c0031086180200c800d0140b0341400200c02d03c64480c0c00342c211808000c6680d0140e2951508050f600c0c82c088002d040040c4400001061400d010700100403444c503030070442c6a190820700d580f80130b06000c0780a440380d2190400080075481750171800181402250a0b250242c18202c65010f800d0b0101440d0703035540d0209981d00c880c01e0b080314681e0321a181c02140c02c3c0e102904284602418001d100700c0840490f0022940f20240e50400551a4041e00e0410b500001d0a00115803001c1d4000340c003035000b035803030244030644144890761940999000040f40300390f0301e2880c40103009005d021840c009294449040712 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 608654343 1250 608653093 608653121
    0xe0c0d09140d02030a1209140105070c0b0627130f03050c01051e06090924011401050301061403061306032010051806120f01061d060d230a 61
    0x5102c0c1403003a1020048900c1010a0b684d090742145024482000400003020112031071032440d4007681030044207000301489030700b05840e484031940c01400c010b0707034400c00101036030311504484080d144400119500310602502811000d0100d0b07131150301c07800055400c000d0140400062000100815600200030002c00d2003000003031247d900d07041f448174405030001d2040c0380e00403000f03030005080381803040300300742d100007050100c401d031503558a03015041c242081202240001c14074014000c0302c000c88040084240280f03081451580740c04401840b5100ca03000c41c5040140000128030140d0f600403400d411001416406c120050340c0b450072240300c0c03641d2810040d001c401e0b29a071070854035000395800441030302c9440e0a0700e04482c80e40c80010f149990080d1941c000d400707001e0000110920505203104d200c07101c6410205504000d000340041a48000c4a0542800052180c1041d00d030b0a040c0c0f85907008005020810141e010500004119000080c1c15091480c0302000070340310050300b1121f8500044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 608655593 1250 608654343 608654353
    0x9060f0c0c060f211e09070314030405040b0f0306162f010b03070608070c03270519030c060e040f0507020d120524180a09030f0f02070e0c0d0914 64
    0x1c3c8208030180c03030341102d00850340080c5880000c4a00b1031701e07266036400079000c001d94051940341c1c1c4e140002d4051030b005220b55079002040c18440744c20b19115a07505201c01302c48418040c0c204c503001981c0c0d4200108a0590341d144442c1c2c0e201024054500048290010b551804200d12240a802034000d000c8152001c07039070800100c514582004900b40e07040c2c4826564111a50703440c0d000030b680c030b8074048208a040202030360030340800d8030001e0001a400c0c2d00712001c284085140808020710b4036440d05110b28011a90b0804000103052400d0700f0b02250300908041d2840014000060020403a03091280c1e415400c0100700030000340e02141e120201c2200e501c0d103071804400d0140391030880d001250b200604440241d00a006072105808054600b50003d01c4084001602901c03000800740a031001549541c45071790b0001010b07044085c525001c0030900d000030b103600002100039074540321441250040b2110030041640c4080d49011590074501045d01400702082c540303082998030b800004401194000d0f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 608656843 1250 608655593 608655637
    0x31006050a120c020f0a05010e070501090f090f0225021c1509050a050d0207052407020f122401080c062713021e09060f0c0c060f 57
    0x380c410703520091080d54804141808041001e0024003400340b04009501c20040b65041c0c101d0308000050819200c1c20010405000d41920b0f5480d001c26600054103114030100c4c02d001e0004900c2c5d605080752525074010500b0300240f89400c00074404d076040c00303440c9650040d101c2c6443c0041440a460107101790f4020404410348002d0b00c00344807084100420700303410ba0317030301d40c0d00c0e112580c0101c01c0d01c0340900140c0d404449150b6038246850f070a03039281c50150300002c4042110349000000c09010800070000321101c4800b0718004411445032030b00080c81900d40b00840d6099889002c0019441d060b54012915400c6605454080d5518980906440321400000200e0302c22004654082e41e0880507041608145100502d281420750f0741c50f007801480042c03803821940b66078014100354181500580140e56440480080c501c1594088900301c907914100030011340d03078444c041107a00030740070f101c1401e0b224a00c125055052001c4081740703c1e8020404190340a0341100a0001c0483c01d00c800d54941149103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 608658093 1250 608656843 608656847
    0x30f1509090d0804170403140105100302062a030408012a08010b28030903030b0405040308240a0602011d061012111201020a020c031b06130b0f031006 66
    0x5001c84610145400ca010301031140ca004a044982091040c00c0e1140c440e000000c404480e84c002d5401a03c5002c0b102c04400030200b02803041503049002c0e803d80c14021400c5401150b40f510868000200e440306001600c0004000100044114150b110681ba0358680d6828541d0103407030130102c0c40c4000300294030041e081964120304400080c0303981d1581c180700d80c42c00c111403400d600240c3c244c5107403411001c03c403070a10380501c24a9500741c0741920000b40c0c1300c10702e060003421a1580c9840d94010380c5001c00740b10100b5005032603184e114021907210407003140d8441042141e90f0f00e82c0000c682003454140041800e54040d00442040c1c3c182d405850242c070000090399541d10020b40344c8074180702c100102440301c5030350b590703181c10080e000c2e1404081ca6840b54010680f030950b45030406545950100b503010350294103014801070b0040c201c0c0107200300c40c40f420f05040504000c1035428400e4800040c2100070007a00350300b05001341091840a038071860780c0703107500c10b090380102d070701140d4410136032000f0a181d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 608659343 1250 608658093 608658109
    0x2041104080c0a051005030405030d050708010e0703020705060c1602040f090209221127010303021c0504260d17060603090303061011030a0207030c06020d0c110114030f15 75
    0x70360040c2170141d80c0c420301e8000c1e921548050710540c1e1502040042e4084805507024190051072940ea801c0e10540c54138640200b2840701421840c2054010421070020420004000750400c0240c00d8144e5a4603a86611a0142040460082d0000d0400c00c648a00003070f5a131054031300c10700940c1c0d6001142e503070340101914a080148000334920804c902d140c0881d600005902660318003a01101d58060040c00d4080246003880c9100d1319410701d08018410103505200030200158a406400d07064646440d0244c0680254003503c03c5c0e41c90314581c420a1100795051540d040d86400e81645e5440c24901c5004040d1071081d1001d40612103103c1c0821a6424568216071050600300f010318107546640e410007013000400f44002040141c42580001e0f404807d200408203026a50010901c0f5491460700d5491500294008815034000039140c441054001194001a5501c140314495884214006076404400c52800301500540442002010181640b0950107059554420102050440c041240314 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 608660593 1250 608659343 608659349
    0xb09100e01120906061205031b01021608340c0f0302060a05070c05060301181506020307030c031b06021c11040b0c07050d0605041403030405060408090d02041104080c0a 74
    0x601c40c01607030003041041da07011920f43c900c21103010540f02c0e5284060088a0b4800205032444d400000d0002092035244094000f001e40d908025070400d405400510985045198040c1c200c080c0007882e0203000551560104802c240c1480386d01400501c009100030403100030710102e540500240c40800e6a01441100504491340140400e05c1c1c0355038000704803800e402c658802ca80c80249100c01151568481002c0e5000c0e003103146540c5400d8840e203c000741941c9080f504100c00d441022001c0c462140c1c0030040700c4047c3d8050038504102c662502d012100c29854120541c01060358501c260104a0190004c02541100c1d8001444a40c684c4c81ea4030101e40c28410001c1d10f81104100820001a200c0042c014141800e016184841d075185c0100341c0362808040201e44860b681c074100030410840614030003402d4508002181985030668426075100005040508050008260070b4207995034800070700c0b040c6034003400510101c03a20700000da00c4ea41060185807000e0060703403854121400c10800000407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 608661843 1250 608660593 608660597
    0xf05190b030a1113080c1305060306040b0709031b0303030c0509100e01020c130e0f0d0e04022a010504050c0301091a15180a06060309030503040b070e0a0b09100e01 72
    0x915260700002c040141210110000f412400340004456440800d0030f8800612044024001462403002003145180040e00764844040c0303080244945624002102c40c1d0103940001c0d94615920b4004058035119210391004020340701d10307441003500b007122080c21400c0303d210792001e01c080f45840c2c0043d00d8074040d8580542d00070000011809000d4440c01e020150441c0600645e24030051000104561101d102c1021071001d0700c4051203080440b042025400550702c80c1c0c06070140c49240c1d80021300034001040c180780b0540d008100b07800c10380c0c540341c0520600841080b0070340403140d040d6166801b0f4502240c084c3d5150144c840c0480b41c03800e0600842c1c42e0181d000000711a03000a0100030100614090602032241c0c4004641480e25141d2821a46000c5400a070303100080c03a01001107002c6c0c0d12250400402c040c1000310b4440081e4000d001d0740d4204d5030090141d2810b5031500400c071000d41390145e0b66544941c10340b800040c000300b00801899030130400d42d446440c0340317055882902d5072907001d0340282c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 608663093 1250 608661843 608661847
    0x7050301060815060c15060a060302040f0611031209100c1407060510120807060c0c11060d090204021b1204050328061103070813020907050a0c0b010f05190b 69
    0x200c4221541c0020140c140101285c0c03c0951882c0700c140303015000d0104a0000d2144828801d2520b0400c1d1410010682c515056180a06040d000105040244203075004d00174034400c0c003051084144252150200650760100091526850b13041e5201d8150342d80346115443c080010a03480d200b5524103240b2484070035403525142c1030303030380790b00050070010492184122140030120b900104980c0c0301c40c01c24007807100d00d511220325080a074102e4980780c00c2d050030300120301900030000e0280351042640721400c0781c40300d0f19001c8000801d406080d050030001d510620001b64592080400b12021000403607802c1191001c5103400b11000480c800c03409000c0e895030055110303400b000c10300c0c81d182800da00995028203c44010765111415a81075030301e0f03034606030404000c104496a119800552000c190140c00703000a5064020821240000e031035241000000034000d80c0e10340c028480c0303183c030a500418989040d83c0d04c84800f49402d049001320342c42010072041058080c01032420240c180c070030f114940d40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 608664343 1250 608663093 608663101
    0x80d0f0b041b09150504050916020607050a0c02060904090b240d08070605280504030e0907200106030c080f010b01110c010c0c0312020c0423060613050d060b0405070503010608 77
    0x903450a500b14005020170104100101e201e4848595150044581000c6440d0309041e0900207814001c00614880c1000414882840010b6016810f88490750301034a9295803460004c021070b001e41700b032000140081d9800030038030454058410341440341001c0c4403100740c90031031060100400400e000c04083c0412a06104070800301d04a503000b1a00302140d03807207000c52088001c482817902c202d504404135001d5640c000700424590021103102030745400700c8600105207458030b000f03402e42911402c4c0408014a080c071061628000754030500c082c54011104008882da503c50f01a514003104c0d04281940d400d045009401c4d50141400c000e8803808107001d01541175110004440300c0d504144140e8408120102c000007142e010080c108030040950b0140005504c91010302064600080d01d611100c3d8500010740c51050707070b151046400541c11200c1d5070341c440e03030700c0703031045502c0126044558000c081404200400160798072171004048191810b020300da40c0c28106a0300c9010134860600451510400a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 608665593 1250 608664343 608664359
    0x17070b0f090907030b0103140f0406090804081f1116080f040b030403080a0b03030c031c020405030d111203100501031d0102160512070305040b07080d0f0b041b09 71
    0x908a4403000d4445107081260350000a416648143c0e03204002c65500d00800103d5640350007814205a80d46aa00b44641070000080301d9050000f4030240413990780d204081c1c00c10801104540082104004907481d41d20a00d4440d108404030350394400c0e0795450140f0300041030042c441036038051115000b10043d0440305483e04641075200d0150302419090030007010801200c01c80285000d54040ea81d41420341c6401c0030020b04444440c4103592081e8410312100314203c000104480100c0301241018000c20081d02c1c90002900031604400d83c03500540c07211074005a400030009071403400c0e000c21905c100700702100e14042440245d4204241c44803070502800594040c3c1c000c28403020704440040356840c98801c5090072600011303220b9940340c0e95400000e0034040104509000c1728420540580741400556020300180306a10640f009510046503070418040c00400703890000e040004140103421499a80b01d0040442c80c000714840c0345041c0d0050b6503950180005104500d840c2c580c03080c2d181c01c2c0400c4d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 608666843 1250 608665593 608665597
    0x30f01150b0a0e0a060c0203060a0501030b0a090204140906070f08160f0c0605150111011e050613020705060106080a02270607051c0e01050307170c2205010917070b 72
    0x4005001c68003d841400d52198041500100074680e10200304d0f502e148105070500034041d0140d2034440c2000e0050000c03480750f050131504000c09040c000b603e00c006102082c0900442051404180000030130441c5071007007c81e4080c41132505540d0450312401148007507400c60020f03690f000c003000400cac1329041814058500c500440705c0034101960518055540d0038159042141c41403180701011040458558215000d8000380040c0c00080c81441c1059400100912071382e5003000c046c40d10f175004900107482d548007440d803010010700d096542c7c401c1c0d801c099030303501000e210780d2001a028000042002d00103109440e21a803410904901c0801c0c0b030f99000c160700c60701450807580090704000603400146d082080c4e1b541001013650b09480c0c540300f9040685500204481f241c14401c04104109001d41d0041c4003003000d0000c082415415201e61030000c07410b003d84503280d00c0703641003400710365110492840c4010840d2003d85e03c41082c243c4855482e00310700203e40c06220241d108c080c06112110200c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 608668093 1250 608666843 608666857
    0x3801030825030f08100b0c15010f1d07110d02061b0319240602010501080c120d05030a140108010506030c01112e0915140c03070e03010b030d050405030f01150b 70
    0x80b40ca45c00b17a4540c0f0409255034000140e017415540800048081c09124004480c01030440300c0e58011020701d0018407488408580c2400119203031103000088015000f00c0c82c03100001042401c8510310185d0b04806540c844c0183c03034004880e4807001b41e00448041c1181100c0c403860125912084560001e0407242c041c01181400c480350014000344104410100c3c102c0c00c0007441d80340e00101c3e841d4507204070181888003c901090144440600034200b65000040803490192140f511603603d54442461000904220140043e03106240e40002941c4605402c50742c01140114141c545080482c4019039040e10781c0c50140f51240c000107054908642c4100c1c00035040892029007108489204403040200c440380241121a0042112146d20104013840b50b02e0b284940c010310390703149042c1203800120502000b00702d41c08111601e4402081d588003174000d41c0c0780c0c100107400c82e1500d02043e44054415005401854040d20403013101e120252070500079182e9206e4021001c2c074a441c1020400403850340040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 608669343 1250 608668093 608668111
    0xa0914030606010f0c300315030f031101020d050c04060f0305090706030b181e010902070209160509040501090506010e010c110d03021c020313080303043801030825030f08 75
    0x21017030b4a03451400c0e0140710f8807a002c0441200e54040c50441c09002c4070881541e00c003803054108c4040c00001c00d6480340000c45900341c20711003004801070301081c0c007901c1003a4410103800e0912041c8601440d02401078820307504542c40b01c02d451000c0301412412680304031001d10303240e441504200041406903006140900740508561480c0d4003035603c0300c18490f41070321014001004800750082684000e9a82d40c05880c4110701540f03007042c03540000d026550301429000c3c42000000303010404a0007074085400c1260041c0c010320140da581d2820708001c01e0101e8415010560380e40003201258400c0860194050780641e11f192500d641d40107004518110036400c03002e610500d108034130100f1007407410b209040140d50045650341002c91141400c096160f00c4020954824414000010f1014450240300b4884d081000c6d0714a5030341d06180030300001f2403441e42541c001103002105000c4040d004140c1712044071050000d0545441c0d42d81c520b20b030040300c060f0008501080300727944030b072003a0402600304000c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 608670593 1250 608669343 608669363
    0x30f051e04060216140d08010e0f070f1b05010f150810020a2a05100c0516061d071d01120b1005180f010f0510140f0a0914030606010f0c 60
    0x2540d8921204980000c5204654001100c0786d01d00c41d80440070a0240a4412080140d81860216502620809444134091040c0b07010503003141403040400c103800e060707001c03c1014010310341c0c107265000300700c603000010780c1c207007402d046070040d20403c04103c040f81c00103402011500c1144807880e0003900103500d0b41c8100019503200704e075808921000307118620a00b0200c01d02010242c944180b0b409a400341c1c0c0031900b400d2111003c081c42d00002510540d900785058a043e850081c41c280000707140c00700700540c83c00300590002d80c01a10003d50401920200c05440d0107070001c42581c0c0321165000d106040c28a500221507900041288204076084001e19100b021a0354455000440b5203440e5490284d03200340c0d1804000c40f52902c103002500400c246500c4100c0c007401c200105011015103c901010f000d101001c0c568818910b50403100605003400305141c0728614540003c10203000c038490140c0b0013682140c1d0030740707501d004259680142030584809000130501803058591851091094031100c1c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 608671843 1250 608670593 608670637
    0x62a031b180e1e1905060f0109030209040c1815080703050303010b1303021c03030b010f0f110717010504230c0906030a0f05010e07080604020a030803091c030f051e040602 75
    0xc16426500038164610404e960111203101c4004940006012622410319540310703d0301641c1000306035058a8055410880300c0c0e030359050041002501c0c1d8808100800d01c0800c0b550f414060b60b02501c489101210b1021306141e640104543d10909400060065001000100311101c290b4000340f0f00120002e841d0009284e5a40005d0f6400d00348140150310740c6d442c0c40d4000109a4144690144110b003401d04590200303c02000400c0501010346600038020070760301184a003481000710500800c0d1315408086c0e181e0b04d000400b400b071302080d101128410440700c2001d03489404541e0880000b09854000d0500760540000c21540703550140060f5018029802504007068041b400303104441e00490000c24024604407013103180007002d40c001c507043d401813014480140d591000c81c0301242d400410240d00e039143c298070b040c20001c10304203840d819910040b50b20b07810340d010741100c0200c0389004030030090340c0d4420f02103a41402c0e10482d0004078034a8000005c000602903070103008401490340e01c0303800e0388032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 608673093 1250 608671843 608671891
    0x7081920011a01210b0105090409060603031701150806040e06101a0f0f2104050d0215071b032601180c0c062a031b180e 53
    0x11444210162070394440009440b0030000800c0c00154010038a0b01d04010b6101020364400040c9a07000d1182d00c80d00c96810020a0784104142c2d01c102030002c108004100d00d6280a41c0207190030310040f40441c0700b10300100070b0761101500503412100e407414600d04000c031103481202d00c128010029907109a954089071400f0208002c0e56102d11010815404a2030900500718607114029880341e100b0798042280200200a44055504190b00500e42a03101c1c0311112074201070f051002c180350614540a0108000d00c00d00241200c2c0429041e025210342002820343d401ca0400c0445840c1c0100f01240b080201340240884291001d5001c3d10303000d456010303030f00030300310682c2900364040c2d49404110b001403182503003180b10343c2050b25940000308500101c00101505140c02043c020700010b41d200030840c40000c0891001007108000c01d40b40c1a103803403150b0098001c000d032124514121725201035080c4098059100052072588001d006102c017841c00081b41d40c3d141c00188000303141c000d41003108265030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 608674343 1250 608673093 608673137
    0xc1203070b22031107050a0b0409051e04080d05070e180703062105010609020412170c0102040905150a082a0307030f0203060c0a0507080304020f09090303011406070819 74
    0x50b200303036140000c0d0310507106040d14045c0d130341c0c100394030500018004100d4000b0a40c121001c503181d040c000b0a00f503a0b107014202a010705c7c100d0410303075800040300f0070041155050080c4034050b015030f0104401c2c1c5810300c007211604115040182c20041202d151280b44080682c4554010040e213400f20301c0381d403103460420300e05080300040e14140601c150004100300080c0a0700d0080c0c6900e100031418076141148428000000c40c001a1540d4031248000c1810721100080346d4410300c11800039540c0f160303544070f000010413044a8161070354481c0740108dc1c00e403034825504030407103a61100a2400440b196414003c0b1840d00e084418001d102d4004078200d81c6007408008002d60043c0440b50501d800c0340141401c0c100001c0078044281c00400c003071042c103a04042590301c040d8100b001c650b200c1d034461000c280c0b1103440d00070b56a0b00a04000400ca01c0080c000000c60580d2007030783c034540c03000c00100c0a00169001c0c0c80d0b001080c011007800380303481114003895183d002000c03500d4902c0c01c00303c16003010843c03c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 608675593 1250 608674343 608674411
    0x4050405011b3507031e020c030d060e25050403020a0f0302010f05040806070507020609132702030a060e070e0a0f110901201e010e0c1203070b 63
    0x460928640b81c5401c280e4001c3c0d01d80c498072601105031a440624241542d0600001c04507428940d555000030345a070003281e40440405440d480855031540200809581d0382c00040460740d00302d00f0018042500b41d042c03105240646c9604440350301d820145082211510011a001404c01205100000c0507035600b1007103d000b018125207401805085000050100300719100b406c0c1400350400c000c00c502e250000d545a8082041c1c9403243e02c914040c030000c1c0b010711410f1802548001480450b98209103542d0141509039201c00092500240217080e920020394070740c03000380d4943c02096044010070010f4000390b000301422010380c0e401940340c00c8040554241900c0100110355174107901c0340c0d4100d891040c10048440581c03c24204403003407000800310070801100041c0d041c9043d5010900000c1041881420400c02c2180114116040c0005000b4014061004040d20417040514101e003480d150460769610b80030050361426065454060782c4290140c140746805c61028002c000207140d5141e10950 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 608676843 1250 608675593 608675597
    0x40b01180f030605070507021c0507090204080303190b01050a0309061814010b0409020d060c03060b16110411030c0315030a0c030201030b030606031b0d0c1202010f110c04050405011b 80
    0x2809003581800030480d4401171800c01807150803c808400341e138070300340d1a0072619110300407808890702c0c602d849810302d00a0b81c8030b04502c5002250110341148003102545c8501100001007540c0d05000c8101000e403604198440c0c00714504000c08682544240c210340c220342e006007408075071a044030f400031124102c403410507580c00c080e5000500d1000800e0240e2900c40c0d400b15000d005041e059000950899410080101034581e1042d9554859019070840c000514070503240a4583c0c1e141120f082480310195022104820010408010340c907081c8a01100008686403060a40d0303540703070040340e066101500382d8060303016800700003410765800c200610340c2520030120f1342000c518510014055420b2000101c2c4682c0015042104a07180062011883c800c01e4240d6808000041c3c08107054800c0010003821403c014800070541050854400080520030b0341d82d5400e5401702c10701210100c840380718040c140e411015191301246069008a6003060141c000082c1e100014050000486400004400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 608678093 1250 608676843 608676869
    0x8070e0a082e050103080a030504061401030b013f030c060218040c0203070f08031e0f0708090a050a06020306060904050901090501061505030a0905071a03060a2102040b0118 76
    0x122028494018840b0b0748034010600c515415035981c92658060256404101b40d542c0e00090140b00a40d0040840303007040300e20403000c5507100c0c00c01c088000001d0040101d0240d0320946401000040507400720a401402c01c206d0040c030b0049907100040621100039000c10103501540c0010038128070051280e00c0403400c01e4010b0101c04014031082d0340303186c495a02590003d0003660b0202d112003100101e03643c0d210742101e40e6591a400341c1504a014205100348174000641006221901d02e0b4280340118160748034030440790744ad03007034040c0c0da8298403400070225040103246c00c0000b80e0326000355412140080c100c40c20941c0b0301300801c084403011280d0b500e20760344a20708801030000a1090f8006000c8010300c0000d01845180c001d4854840a008020001d0381d528405c030500c0018044500501620b071072103045140d129620507070b00d410540b8841e2103030001600008064280100c0f007040c4902040542405030010b40822004110896149050125003500d0f90360801c10b405148024188205c1460 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 608679343 1250 608678093 608678143
    0x3030c030405100c020d032d0506181003170d0c030b0a0b0315091005030a230607090e131b08010b0f0604030b0415020d0c1e08070e0a08 60
    0xa20f49410780d4426a080c6141101400d103007a808503070000100b10794180410900f0345102c84500d04c4000c01200d104012140c4000980311030150400c0d0300a40045078200b1010215641010380e84100391031035849000c030b903001040010064107144140510302d0003201e050240002d01c0c0c40c240c407000d1091800013941d8407011207982c504281d000e800350818001c03042c11341ca441c0411a400c0c0905c000890300c2106c0ca4800508010300c4d100794200030704000f90654900f00d0391450211100311203070010b80c41c0c0440740420784880c080c0000e00144039904030740d6000c408070300d049506424600042d184001c8006040380e6030011919a41c00c10303252a83d80e5604079005840c0030724250071280914289441080c000314000f06a985505c03e9509a9400030542d00c581e89483c9001c5800380d8101010200c001d00100311940c001030380e688003410f0404180c40d4201d07601c0c0d946010550140c2c003424200c000c40c860341d0205408600c1800a90007400300642808070940d11503c085140c110640000c4009030643c080003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 608680593 1250 608679343 608679353
    0x1030303050702010605090703090c03050a060b0a0605090108040f02031e160602010e07090e101803080105180a0e03090d08041410080429041202011805070314010e03030c0304 77
    0x1c01d9120440344000c0085901300400146801d20280801081603152110720f0217111802e9503103002544c3c01000c0342e4503101700e41f5007040030b8054803c0c040d03c0750340b644030001000b40c02a0b04441002c80140d5810f0025529030762141c14001545005a030988aa0002e14001d61294429035040303034841001046101e60204084005131041d410113011a4142460364001c0000000c070041511206240441d540c040d07892050310707141c055840c40320351508040b02100422080100c07458143d0090b0f4a0104e40ea880f0b00501c005d0920a1203a0414030080c000010b0054255a00010741d13034102c1c0c4141c1c0d180c40000c00000780000880751003606d18660000b001c000007501e041e58908006c501307640d8181e60104007480540101c00040000c4e02201aa0001c420b2405038440c01c42103c001000415410b82050b060500b0114031052200d40590b18214551482100380c000901d2043c3d030110040841a0550b910311604408100005450f50b489112000e84010140007851182d030030048920380307c0c60a810302c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 608681843 1250 608680593 608680601
    0x6030f0b041514010e0a0e031b0c0d03080423010f060e011e060e060d0204140102011d0a0f2306070206010e07120b010c05010c0306050411040e071103090a0e01030303 73
    0x1545114641425403e07030481c0c3c5201030381185d032401310305c110795520214441c0203002d80300c01c0d502c000d0000040c0607100080d01d0703820411812949040343e103141440b030700384a0111045100900420140b40001d00007a905000c0c6940a119043d2019030300c1701d01040290a54000d500e40250440c0c85400600c15a10102c40c4640100341c540000200b20319007100c80d06e0024502d0141c44c0030041c41c1000000380f031310703018101c0300540713180103007196542d5440b0390702601c02c3c0d5450006070055080000b00320000002c141d0141e02003486002506039501d05607170b503400c2ca003d4224100d46940d00d121101000948100d031840902e0b180401518841c940684024204107058000c8120024140b081c1f0901d2548802e41c1c10103040d182d071000960b4080140140c0d0887e0074108000c0c40c030341c240909551401c2c0e06400460840b00705580500420386050410030190260f80110100131140703c4c005170120b0b10a0304403000280e8160196460f00802c4404585000c2007a00041d11001c40382c0d00400405615100d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 608683093 1250 608681843 608681873
    0x15030608010b090c07020118080703081809011a0a1407120f050a121a0307090c030e0319030203070c060c021e16060f02070815010317040608011806030f0b04 69
    0xfa0b0f8885a2814003400031160281d20006030401c000d440c8110b95a400ea00000000380006030200c0340501e540b80341190701648400240d82c17a0a0900040c49103900704102600d040e20421480c4514040c80d0142490850b00b00400c0b81d03040086107565400111803800003815800c1c003481111844440103200648200e60043c00d04041100c2001203c4050b58003d003440300096580c0404661343e07100128034140301e800240340503414080c062000031080c082c1d44c00361155400944044c80300d83d10a1741c1c416128015000c40b0701280c1102002503c0041c40b80d8000c41d0b100406051401e0a41605c0c1c84c3d0104907481b450030324016034081c0b90703030f04001000c2d001c141c0c4c6070340c15690040030a09052064521140140d2042d14180300f04a00210f214034000e03c031600142003520101e404182e0078864028010300213100c00d8510715400d6504012401000c42224183c64150701c0c1c1e80d100b81d10300b8100f52460000c5000131510546d5900004c400100310701082900540101e942005c0b42c00c0c41d041454180c04452 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 608684343 1250 608683093 608683099
    0xf031f0c0302130b090406050904081204030e061317030a050d0f0e0304150e0402030c0711060f0a0207030b0a020f040e070e09040b0a05010e131509060513050105010603060501120207020a15030608010b 88
    0x102b0000050341c9141142c060a030070b450100b103162664901a90b1840b40c614205031310007004920380180d02c2a502801044540848101d02e00c901d80301c095640f24842c0c00003080020344d0411070840f82911680240b26089407030700001a041c0307024200f0a04680180e0003214070709060741600440e2a500c100c21810059003140c0862450500e00b00d1040680710380b00c0d00401c0c2a51079002c5141a54030001500c18002d0f4041007aa990349080c50020340b9041603000480d103c045c480085200d400040c400d54030b6400c0c1103100b00d80750506009542d4144600100b4010400044282580c8603440ea0000d050043c0d03c51003609216082c081c4600e0262501604440140c0440804102d420001c06144407070b101e80203040d8484120701400040003500449402030861802c0509106c8407040481164100e58003640c0204220f07600c60400318280c943c54814180015801c01000c181101658001c0241d01d10042180f6802c90f40e03060030005018440c4501e10120703603220410004504280a4002481e00403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 608685593 1250 608684343 608684359
    0x71e08010b190504090218181e0303071b080406030c02060622020f0c03030c0408100902010e0108071107090e10061a07020d05060906060f031f0c0302130b09040605 72
    0x401c0c824407070300c802c03441064131139a2165401000d41d01e5610b262610420001d40c6c490081c80c10b003076806030280007442090950322a2030b005007610030101503088000714981000d1842c41d250010200ca1090040c42900500108500d199000900010080009114a032008207200340c42c8980a0b040030743c0100254020100c3c07801c070000034440002c88441c50221218010303241d500e010455851402101c2000c0c0d058440041480404020f11014104613946070003110482003d101158080c1e40d8104402400701d420107031006141d6020300081030740030340a4500354102c002c06c20b103e60b180651b03a0f1305c80f000d415641c0c1c0041d80441805e00201c0c000040d0711005004881c5040c045460301488c0d90b80d800a0801c000c00c02400315543c001611524580041c211046400c01d10181c84e02d81c6419180705100310920000c8607540d090110f084000c0301d040c0700d5084001400c2402082c090004100303401c0426508212241c4810f1104080f5406084010a060386801c01c550500084501680000c5d2090325030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 608686843 1250 608685593 608685619
    0x110609061b0a060c2d031d0a060b1203041a12040303140108030a090b0706110d0b011e0f030b1c03020609061f061107032405060603010b1605071e08010b 67
    0x2580d40c0f154820101c002180040c1c1000c54120b0062800c1d15401180030b0400c7c19650300d0480008511440310b004240c20031460318510100044401035802c00707680b83d0000d2108210003600301c184507480602502c00030b80b030300110b004d5050128408990413008a40d40c0c00a4a034151817041100d405491040000d603d001c0190764060902c1d0014031030150140320000d17000041201310381140104c81a8038071215100d14205070700701c020b041043c040c2800241002d07045818035190921004081c20503403650f1800c044078070011800f070000f11250a800c42040041401155900011040090b000c1c0d40a4501410411850b608000c00900400c0e109184060344860528000d00c10300100d50040c20b200d0f8000c3c8001c90b0313117401d00030b0a60014084021101d004110f06071405882464001e54076002c010690f502d03c00c101c03c0e40028042c0c40d100010a005080703a0403400440d585649000f00c003200d4001e991450b2038002610550180702080d8241c000c20003d4503424040e400a002c4103c490b8005100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 608688093 1250 608686843 608686877
    0x709150c17040e090d020f0304030c2d080325030206060d0515010b04060f02061909020a03080328110909071209050f0c01030603110609061b0a060c 65
    0x210400041c0041c503207485010706a441c008115001401c4070010310607140742c040e020945400e000c006400c050b007e9590b0700041d040d00481160103581e400001c000c3c0340e50406104d0002040681d102c00041c8021141013003001211403110030080c41c000340110386d240c2c610841804d4200071a503c200c1c10209807800c900020340c01042c407030742c452816104100228901e041a618200809209501c038040450001c40d040c0340b908000e00a562454890094035148030b03404076a076050031a0410b501c22501d150f074004034440c0790452901e01c2e000510800145450391076641301d907031081d510b0381c44058110403407000051060110300e0440c16601002c0004110103030720301280d031184020151140381e20b4400903038102e010300d012420040802000700258100c61030625951040002521070511601d00c007600c4541c420701810050740d5009030342e403001545d05402d1054580115601c02c0c0d000d0001e100d00c4880d070b0140c8000ca100d04800384c008002d01c080a05200045644900503181080280401640750750 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 608689343 1250 608688093 608688107
    0x40b01050f0304170d0e01050103031b1101050c03041805040b06030a0c05061b2d010e0703020f060906180f0a080c01080405190302060a05070201060f06110106120803070915 76
    0x141d0882c0d00d5901c2c64507051204c200031700c180c2808100592a180c94110b604d601544640e041e41d11a4485503241d40c540c16140e00003210880b8005e1a1395107110044c0519441030016240030030011040b6418540c0f292940e0500010428409103400c1c0d861040005016070028419008401034000c3d1a081d0507035101d0810b203e1160042e14000d0400003540030100e100100d051021400103c00d0760454070403c05401407020304640c45040395000b103880c89100e42d406129003180000321100074803a13140740d41d007448112160f503e142070740218280904412034417260024a031000b2283c26090303000302c401c0200503080d13a000c0019402009016802d100018001a025050b20424280100c42d80e4503403034124601040110001041c03100d00714008105500090b0040c050002d020b402d000540c0d40f03120882c2215070521420103035202103102000014010010703507601407071900000c00c900b03443d100c11041180c0048001c6403070200000030400500c0d8000c0c201e8010b4002c2c4100f03100d8030502c2d840010410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 608690593 1250 608689343 608689351
    0x31b03070b0f0f030702010c030b0105040f0e06030a081209010f0b0906060c07031e061404020a0501080406060e070f0e0108040b0c0d0b0310020c150f1602030c07090506040b01050f03 80
    0xc0c900044406a0410b64429102003211858480c0da40c0c1c900343c0f43c028064a4500d2030400481c0c14507180e5481c40d80150700395010b030750071400e0100c81d152070806002402c801c09000944c040c0145880c910105040314020014170708118181e42c0e0030304202d60b13158212a41040d8415982d494030000030041d82c2ea43c00415002a02190981c0c1ca54680c541003500781140c41d8801448219036a0190210075407200441507054082c0c201040728080d00c0034003509841045030001d500c180550005e0200350b0080b4030803504036002c0e0000280c520b03203510003422071441c00c0c1c9044004c14a94060350b4071040d404401c10006110030b08c0c2c441d04904050b070300c050048602402c0102101c40101f0a5084980c8640c00750700304d290010112032840c844140480700941c0008039000c81070140e450030b0303d00b1080e9414100e008841c9216034aa00c2e945000100500f62103c2d030789581180001c00100000c2041007110001402030180c0c00200b03414020100310403920b0380c3c0c4102e03061000070b01407030924050400c260b03980 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 608691843 1250 608690593 608690609
    0x306010e090c01080a0b042412020306010911040e07050702040608150601050d02070b1504060f06020a02060a0c0f1b062a0602041a0403051203060622170606031b0307 73
    0x89444000554000c0c0490078201e0307400a00c0c01048d452410202c2c900803c0d0a0080750201003107a03242c40c22805004280c0784003035090340c0200300410908030550b014400c011038803030b0721034285a1a400e00c03800c0c08005035070040001d0804101c01c1c00b5031415129400090006400801850200c0395010954100050803103061003404203070900c074200d00d501110a40c0381c3c88606a2000e1070501c0d520b03c00005015070681c0954541480802c800084440b8981650415001070625035525402c100a5074440c11501c010008600e2020b00040c41c032103995a062403041c3d500a0341030b8507070f141d6020b09440650002d0204841800201c041034030200d56000e0b64a031580300c803128030517a402e04601034800c59100142c640d00810160204401c414041c1c0b007902d105030b0a8514440040c800d402c101e0105503442d561110f070400ca4205000c01850b241d1010b603290107042d2500d566542010b4004c0c800071001081c1e50703004981045080c0c5010b01c0f00301d20400322000b2200d5041c02010200b540c48100e80141c1c00c0f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 608693093 1250 608691843 608691857
    0x90f0b100e030102040b040b0d061d0c1303140d0221070605090c0a0b070308070c0b01050f01030e0631030c0b07050f1b0c0108190207150204080c0306010e090c01 71
    0x7450340b400c1d011075003d0100100704e15510303551414550b00c10362145041e00d020724640400810001c0100b6070010710200200340d000204c2d2100361140809a00c00d650111114103c4180000050140440040d4440b03c80b00642000e00d0400d8002e401e0407003c804140340c481001c01151080c03449401501c1c2415003084c130000c0d5541c1c40c031306040e1401003200c10305540075010f5003002030102030f868002e01b4035911a0355012110b40b0358500a4480350a0400018003883c01c2c00014407641c1408201a11141d105150100c0c0b040040c4508a0402d5402d4941418a82c8080c0e81c00d0242100c2000314030f0020702625a069070003816450041080340030f107030000c000c0024400840e074003903c210103885d0503840c449191a60340b031703040c014811140702e0300d40500514041c00250024642c000c15020f84249808100144c114200e00c01460095112080032155000d02c0c420514262099101610107030000900030441b0b0f48a4000305071070040164000d100c291031110400c14401c80207c0c40e494906000e0030900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 608694343 1250 608693093 608693117
    0x1080615120a230610050105070f15061508090607030213030c12140c011e09030c090f05010e070f0804080906030f0105010e0607020102120702121204090f0b10 70
    0x6200903101d25005081445441514010301880b0419080700c1241c0c05a84581159400051622940c040311085030080403590100425401580206006ca10620b106c2c1c608440981e18001c02c0e124021100700019038030041030100b92010b261840030840c00d81002d42040c60300e204403680d9407400130000410180c0100300c0c400c074a01f16000400255500c0b0b07410403801500c40d11f00303018454900c0b2050740c91001840343c90b4881c84c000309050b448400f0607912481444803c040e052401d03036811442e0020040c1482000002c40c0d03440100c41c0c05005240d0001c95000355050001042d0354042c0c00c8051041c8854040c04103d40e00324500d1840d80704241000031250341c483c100394641d80149211a600404000700b00628251500e8259041c3e500903200c680326009141c0501440340162400203015074440e44400c02c00813400e802070030090b44010040c0c03c51408130442e650405094403e0744030060030100d0280502800303400f070f4a08620340381e142007050b203004200050900c0040e00842091003003038401c2c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 608695593 1250 608694343 608694349
    0x408060118021c0203061309020306070c11030d020a02030607090e040609020d06090b06040e0636030708040f1a0a21051005150310060f02010209031906050f01080615 73
    0x600e0804a5a5801e110249003c441d01c901075402103600c2072044200c0008038445045074455512442c0d0040c006003d5030b55000010380c1c040c00084070030744416600041180a41e0f07410498080b0a05c52980603120182d11841814500079001e000c0300305000050070309200050300c40c6000703944240c005030042880015400030407068040400080d081d80d003460300b441c0034000b00818290040005440402c400e0b101c400d002520f0700d40036581e070601100540b11b1a40c294170a25018122044000320355482c10300200300003461588000c004031410040801c04221543c040f0150300c0040500414180c4e2100301c0752210309007846900c4501040c0607058a2031451031040542d2100c0050300801c080203681000110724413001c00c10312485105550a0f14501182c03400c80059a005811902001c00e1403030604809441608594001008640d820303c00d25006690411514252030010111055106a141080010380d400200012414220200108010f20002950b10740c0700b54400381d8110504060000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 608696843 1250 608695593 608695597
    0x515010f2102030403081f03021c0501060513050f0112050309040e1509011a01020318280303030507080a090b0606031e1503060f1015030207060e0c1302040806011802 73
    0x41c101d214408020807081617003100003180a50303842c5681c00d810688102a089150103140802500030004040c0405180e209903940640544604004521a0384070004a10041d03001820f404100b91901d06006805050501550152054082c404091010b540341c49a591091440c0180516034501c14849103000510041c134000581d21103441c054241440414042c1039801c034a07160000c2c041e2900d21181d0300010071510b481200c0c040640107254650b0810200e41c0b8200580b608120341416000c0c2507040141400000e103101e40c80004a5091000000b0800440201404115403400e80c1c4e04001c1090b2502403503010004442c80f541d29610718162601e040d0001621203d42144c0b581401a601020300d141c0300c0d820025000c03a07820395039060201a0011066038441c4442c01c50701414041c0301035598401d600d00c012402c4c0980361000d55030307440c030440ea0700c4020b00c1ca840e0809100e40c4620b20b000c0c0408803511041860941c1000e00307220f24030b0348070300041c49040c241d481403d099900c050300a0301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 608698093 1250 608696843 608696897
    0x1060f11160f050415031203063803060303071506090204060207150503130f030e100e030633030f0a08070605010807061409040e0f0a0203010515010f 66
    0xa541446141215180101c1ca082c0900701002c81c0c030250115007400e0600c1554003403101c083c0c3e41e070000ca1840d182e0780701070041c0340b144104240d200c00340403031290850119450100103484101e1350104540320544065980401140c5807000c0400c180318407580c000043e0b074502c60300324030040005002082c41400519255006400c0c0c0c50000c200001e2182e008200141101c10840d140702d0404d010200403606031204840014500441a140e10003098070860305505071880782c20044288420000044d0109028401c204006400d1172026516414284000e94101c54404c0420118a58001985603154003111140d20000f10002068100307660400949102d03001080a45921084504004049521841042d20b139181802c3c00051014000604c510480c2c83c7e41d80e40b4041c0c103020001c00b0415500400f581ea40c45902c0d25000e01102c0300c00e0280b41044540c20008006091145c03051600b035400c02429012541302416602c2c0d0b090341c100c00c001855101c98509401c2c005a034000d0b42100d00c451003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 608699343 1250 608698093 608698127
    0x3070e041506111509151506030109020306100305070e12070512031909080c0918010c1d010206220503041a03012102030a02130608010203091c08070801060f 69
    0x280001603000d802400c80c80c0b84400030020f8400700f050061100440800544d051701d5164415034089040c11a010780c007641284500742001e9405440c94001101071700281c101c0740f00164000180007551610203468440f60406040a00091900f0440913041e95200981c2d00d0041c0060303250002d01c1d400501050000d80070042a074000159041c1c03d4640d00d41051303203801040e85c880020902441d01404040341103e45940040ca08404803200740440e414000d00004002d011100090140110070b00a41d1030750b0190b9503800350003450001c1001d081c200040d40c0107041d5044a400d12110280070034000d41800c8806000320f840d010585005842e502c40da9010240003402a98200e900464580c02503041b41c13030710401d180c442c20100743d03d4104101c0900e0300035415030015103044014102a1a1580101520240011065a55948142aa80102c0317044034a50084036011000003082282d040c020034091400030000c0c505810007905429041c007451007409a00c11500d001c00d881a034079207280c0a000303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 608700593 1250 608699343 608699381
    0x60203060423040b0601110d1b150f0506240903120d09050601060f0f0309020a1203020a1406060904151508030702040f0209130e030c0304060c1109040803070e04 71
    0x107410b40040b006003640c045070504a110045130403980300d4098041002100300140581c40c0400a0540e20b5040881c3c11f8580c501800c4c0d0600b000c56141042a2003502117103901080c01407000070307060111040240801d102c2e003180c0f911600100030201540500d101980070069841d204100040d00d000040800c100c442c0d000010720080c480810307000b9220151080089030502d9807030700070548143c4808000e50b4000307160192081c0089100fa00554411382c009800c940d0040d480f081c0c140640360281e181035001d40c0c00703010100e0420400c0b40500700c020307181c40040c02c0c0d182088400121400c20180015204040b03030b000405420505a022880c00c2c4842e12a1961860751800c190361207821405050380b2a80c90230b404000540700c240212008a40d0080c10451904815a02c55004100103400d0750360500c001c0c0100401074000308003d1000c1e10254690350201ea45502c0d1940040341031030a000e000d18411003c2c000003a45440961b03810400608040c88241300d103901040040c102d03219450840f90301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 608701843 1250 608700593 608700641
    0x40905100905100f020a080a1d0d03020c06010801020703020c15091909050901050f130c080d0905210303010b0702121b012a030305070504080724030b0d0602030604 72
    0x84440c00b00b50f122609001c196048181c11049000d400c101c5800700e140c0a00040440c80c0c15405005244890601c0c1c01c40000ca180d0750300d203403401d040a4003002c03a41c0040c0c08060b407074081080c07500420300b82e8002c2d8641151540c2c001e482d00c101150040c000d0520b5405821002240f000342c54841307a028200e8500d005000f984240c0002140c840c0c0f0200b03a142001160340e02e00180103461240000c01d01c00e0a1130713218416401c420112000c410303203841c28202c20125021070300707011040052465035507440d80c26041204104040d400e0a119400b61200c28506080b240004804e0b241121a011511a250b4040d40089061290342060241450045540203800e44015520000c80d00c00280e84444085121004903000b1025040e4401116041c00080c40c000130f01c60342002d0f90004446c40c2183c01c0c5951421444d00e0003245401a010008000141c140c0000c58441e64212094552406001c43d44250700416940072400354090150380c0c0010014100d51102c0e0030040c0c954034110580209100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 608703093 1250 608701843 608701853
    0x140d060213090e0d080a1a010503180703060621170d0204240809010603030e09070201090f0803071d0105160804050a030c0f09020901082d0f040309050402180409051009 74
    0xc3ca084c11400881c0440000c10b605240c075102c1c0d00092205000b00c4944084000d0042d141500001c042c1402240c0300300c0032204040081c00342000440c461980418441d0610404071455425080601d0340c2d041c0e0220705c140410120b040b8000b0030031154204980c0d4100c0f41d40710394060301c0395030041c9031610000800c51038800303007030b20500030101c0140c0d941510b02e46070b07110428240c07401440060000361040c0901c08d842c1c680a8880e540003901400001040702413692074048600b51902c3c01d0781c15090210400031200d410804005034a05c1d040e40034030601500c10006001409100240c46811502d9140c0008201c000401c8401500d4024018040143c1e41e18084041d032003640510118031072b17084000a0b20340814000d445620340140c480b1a104d45e1025100d074000a0300780f88240c141d0f540410f0b54071504070b800034006d02800380048400b4041c80d040c140035010070f245600090140d441081a03202d1221428030082000d40200c4e00800c1c1240942081d6280c0100380c0b101c0d54240f4944251002000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 608704343 1250 608703093 608703103
    0x51038010201060602031804051807080f06090d0903030c021302040b0702031204050d03110a080d0911010207060905010518120a03080c04031104020f1c0b0406140d060213090e 77
    0x220240d00a202c1c054940d102240c49020301c070040090910031007100c8801d4030302034105580c44015102c45140c091103c00c092480c05103140d000e400684c01400303111406c0b0034107000d55607002c1400303401406440003001c0000d010f4025844098100203042d6034400865442034440d0003004408541552900e46508441c0a15403041c402244284601020041d032a0354400a031411160000d182d9104410380d500c0039141d485850313001480301d02509180320000389a0703101030240756003100000144445c6a00c0d06002c10701140050034103561001000300841540024554142c92080c0b8056440e103400e0210f000c2039060403c0300b141d101034181030701000e50030005844098180a5175951129840360540a442031045001c050b01014100c07013803413100d040c260000c1c1010b601c00c29130750b451720b40b502d500307044280c040d42c410300301950300d60090003036a1030903004040c0580a0342c070f40d4a0441c40c4042c001002d02da1500c000800140e0082107069207080203100202c000d11403000c052000c03401054800341c0321 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 608705593 1250 608704343 608704451
    0x7120c020f150405060a020c07031b06030f0b10050906120108030c061e06221a040501090212040f1a01030f12140a0c051204090b0406120510 62
    0xa0301c540000700d4510403144403028003c540240290045855902442019501c0744100316018441c0b22030000010b0001d00007802c040c14402808462681805030040582c0c1d134503035006050a0511200e000d141e503800b041450400d415081c0355540b0131a40003c689280100190307a1040c03a88100000f650360400300c0181a50940700b01644d1040d5600594401950b04013644001303409000e000250081c06c003507603035013100041d06480400754801d0015040989003107845002000c03058001c81c00c01400d20380034490140500000c10350800b5040c2c40704070b04201c4010005042c8076503801014081c4008020824806019548520f2243d07840341007007071442143e8441200e849149034142d81c9054824002031190605a0782000c0c64188050812203d03146400000d03a842e02483c4100410000d204005000134503039040003094640e1001d04120071101503921403501d0204101c03010740000ea0204d001307028201c40d04400101040032100310710131500d5810400c01c0c1e02641000780ea440702e1000c0e03a95555 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 608706843 1250 608705593 608705623
    0x20705060906060d03090e311505090309060d02040b0c06040c0608010e0703020d0e010632011e02070b03042d0803010b0906220515031005040507120c02 67
    0x12616038905010602c04d05440140000300d80301c0061040980d144c050581114004a0700442c03003034005070302e01d05007000e48006060900741038002c001b040050803c0c0b9007450324400d0100f1451a080003000d8580c4917401c4158890000007810b110768256a41c160340103840d5034140c42d500c4801e0a41c603a80d071140c00744c40c1541d5041c000303500010340c0c1e84542907050607510082c0300c101ca50740b83c0320002d402a420a2858000007030300c401c10152481d4091240c80b0040c2908005403440002000300901003100c0c5842c0c000c05032001c8074020000340d8122110b00034100c1403000b034901041c2494400c9080451036005400400d1000060000340034410729154190245038201884900305031740d040000c80a60007004100702c03428401044001c110101401000901405048c502142c3c600d0303030318002c0d00c100d50505290403034441c06d100504011524801e41b8400c1c3c4180740c83d5060201d841c180c61405441218465034451000901c083c0c8201c640c00450380d0440da00b480307061969200030707484820030000c901c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 608708093 1250 608706843 608706853
    0x619030504031d180414010912110304080703030e01020f010906020d11070203060a051e24060f041203052a0f010c080a0e0a0c08071410051c0f0207050609 68
    0xd4501e0f0b05141840740c01005001070211140351080240644008100380c60850961815010102085c000c280500e0b00c22201100c00c10341405000e482501a030504480310381c410310003408108e00004004040c3c03601410800104274007003004034079162681c510131110b5403d101081d010403c05801810f01d4040c0e4007030a100c51070204481c800c2a0080b214041d41c540c1c841c5c4080b481c2051140c0c00141c20040c00201002d000b1703504030460000040542c0e520070012003002c2e440d0f80650007410151601c04085590301c0c9840001c041c0c2c0301e610301842c0111039081810100c090708050103541194000040d080d00b400a01c1a601444406010401e4000c100c50080c1e4104c5000507406200d200403180760784d21145001d4070388400503801483d403080300654a03c164803800d4082640c2000c03a000806084000707040e4207003040003440e0403503447c465842c003501c00191003031030b01ca812509646148100030b061030440808006000050302171142c43d03c0d03403948001158014803001140103840742d801401110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 608709343 1250 608708093 608708117
    0x706110d0615140a1d0d0515060306010501140d38060a14070606090518070e04020105030a0506030109170703031a0a150c02100e0f0a1a0702061903050403 68
    0x10b00d031003c000c4140c0c030068604110b0000c1d924000e120f44258080c0100c2c0e00d0380c4000055021507100c2c6403e41090380d540d07202d03e44903815107620910140d404401500503101e15490040040d000400d01d8181c0c200c90b50b4049003007000e0344070340e902229584d072000c0c15242c00c04071110706a18100f000f01c0031500362840710036020042418a0f60441d69240001d59039001e12151a01c1101c211b50042c07003040781d086444180005102c00c075809418018107540c401441030250070000a45040b00903441078156000c2c1804010143c0c0c0c2003404e481d484204607002003115510030300000e0041860740401000c1003e04011411850210300207003040c2e89c400d8030100b200202c2e1001003d02410500c0420b80e008a481800b0f028901d40186e214102403ca400d2400c501c0d0001d500180c080002682c00100045203ca01c090302890140c10340c450480c015581100414100f455000c1d009800002d143d00061000401c04119203520b022106428000803240c94890289800107010700b500f130350182e0004a074081d280d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 608710593 1250 608709343 608709347
    0x1030b0f0a0c271a040816060e0f01021608012c0c0609030a1509020f0906010f0807050c16092301030b040204060b120703052a0706110d0615 62
    0x1003121a9683c440fa0241c0032022038045100e004105481141e4024071070025956420390803840701510000070040d140c40c2000105840c2a90030070410b0442581000204030544c0c128680001e81302050300d507505103001e00303c0140d18000007011116404c0c00304c0240040c01c40e0701980442c3c3d40c0c82e4550b4440c015503074042c800c0780e2140f0400d50280d1803504114008845480e000c001040f01031005402e40702c4001da5500d41d501009800d1104061650300c444862007180b61040e1640c104a500b20f070b05600303900708880002c08a40c5401d1414040c0401080440d4045006406440858508004580b4005110000305031400380500c140c084c0c040c103203000e404010140847d260480060b0901d03250444c1e20310703161420b00284c081c0050342c1096444001040903881c8030000c0000e01d1141280d50014100303504014100d5400130005006103420044200c030903a5000c1c01d0689101060015036100c603958207114000300381415000c0a1118009025405543c05400c40000c46000f01d10101c40e000340d440d02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 608711843 1250 608710593 608710601
    0xe060703151203021207030e130207030806210a061b1b030509060d110702010e09150105093c0301020a1b05010609020a0c0c08030a090e070c050601030b0f0a 69
    0x744444104182818400790089400000c08035000e031045401400c10340125040680c0140000d400050142c001401d407030400359102034900007000070071450682982c40013000e800015100c207100f0560841010f820341d510300d200c014942240000e0303074810012403030240001c010a00d02002d034500b03d030004501c110b018090b0300106030600020580903908a0390100c99a90200000c00e6126605202c41b001543d42445490400000000e21982d0707880c00e4000908801500003a283c0300b10151402c0100214040345e40e00e0010b002030030401d8a500604000506140d1014040c03030b0074504180d40c194040b8480120b00c036010343e42c42c404404c02400c00c4245801c5c0c2c851202c054000c45c2c1c00d040c0c2c038420144442070142080340118000242142c0f2078070030070141e900022130740000456580304c920034080e46110304401001050000d61521480c4107003c3e00e800c400380718468200900e10b00080c60707030f80598030a2148561150035256030b0741c2c42c1c0c46c064800d240305035101501d550030390300001c540b00d815102d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 608713093 1250 608711843 608711861
    0x703240e06060f0d1a042d080a1202070b0f0711010b0105030708090c030714040f060513090c030605010b1e090a181e020c2107080d021209010e060703 66
    0x2100000014450050002144c0b07101c0341182c0b0201403101d085904411300c20003900480c41060103103048406401c100a0710803510b4603a651841811040c140052210b200700e032071100950507d004200d0304030503010024022000050000e150307050422083e05100490701c2c0c49000c0603220a00420304102445007243e611540140c081042000420822801085039580c03061003a000c98a142a240700824100505036002100002c2c00f03016114203840c25001d12884106200c01c00c010507458500018100d81c03902c1901c905280d0380b0440300c024410031045400103035401c0002400903513900d01c0711048541c8080c6e00c5502050f41300c0031200564294904444901000600701c02025042c5004504140303098a459104165101c5007000d0382c0344900d0740301c41c2d5009030400c0140c5400b0044005402d1501d823405a084e8010828900c2510a03903401c15117840c1c42e004201152200081c008400091181d5840c0d00000d400070307010800903034015044590b0407055030085d030b4196140c0f0314043e004c0d219454 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 608714343 1250 608713093 608713099
    0x10f0608032d07060c03092303070803092a0405180c101209030c0209061009120206070c0b18090603070603090807061b0906020712140703240e0606 65
    0x296548419680304062241000c1d09030b01c420725090043d40c455044410030b11000000c251282e03400024080442d4400118030f51888075000e9240c01a90342544a01c99400010100030010000c02c050755020040414584101640c210304044441d0700700c2060080124a18803550916002074500c86440301d8010b62010854000c121416142e420840002403120507842080003010035400c41048500400d05003a01a841d240c600c40514018803400810050200340100c2460000307000103a484a1003a0494510203040c4c50314411501c0003070658420004081d19402d5400408142200c803580201a00784469840e01d10411551042c4040b1802c101c5545034140c10101c01040031038001c0d00109955882200d078a841c0009507a240403c980141c1501c0b2808613040540f400b00a42100900020b42141d0004110640c900744a00c40c510700c800c5802001c0c203e40112600c4610070801c0000040c40d032201c4600015855510318195840403c0d100e0640e0300d0414110071452540070500d40e00440000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 608715593 1250 608714343 608714377
    0x2a0623010e0a02130b030403230901080f130b090a0c0f0510020c130b0a030b16120e120901030e060c180607050705090c1c09021806010807120f0608010f060803 70
    0x40590745c005600020000c1d0180002c241000c1014203003004441c1d04c1c1070724040d5080e00d6060810005044d000f000713016484c803800404c00c1c0291512600716860030b159001c07241d680b80d03944096a8600b4402040002400e02003050b4001c0b9800392106601c806951081d00c18183c882d40c16030080b070b510442040c0c0960000d003006d41440c1d00b40c01580045161035009007041031941d50320f54030b0892048040b03404021141074444814149c651080c141083d803000d000342480a01c80e203010103610703916002062100c0c071030000346407401d0b6406504a83c0e05d00c4540419900b01d807400342c81c3c1030f103258411180c0c0d490000300500c6140d000e142c50b8054803110340e049401004414100710030303c085903c0c080d00703c0700b801c0c03000e0150080111a00390030001c020240038001c038080c4101d105000709910020b4910ba40b84c003180b01005813036680403500c0c561240b5189400604002a520040003e01000200801d182d0401d50040b5066505420469028980c84810445280c1ea50b049503200d0151070007805d244590 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 608716843 1250 608715593 608715599
    0xa08040b0a1812031811040b130e010b030d0918022203111309020117060433060203030106020709090809090109090b072a0623010e0a0213 61
    0x16588000707a0002600d40700251104100b0464004001030701d808580b140760701d40e200b440a42d410b008816100e442c50b10170702850407071642c4180c00c0c3d00d08041200e000f159a0349240b0b144d50380740605485907540c081420852400800b50701806007190990141c002e200c0c05001e00c07112480b590303064040300c001204c403031039864070385003000069409403a040c01c60384284000d400040032407110060003140b06203080b250306124a0300f4070a24400303406001c0d90440c5031504190140c4d07003100008171f01c180406102c54440d90313204000740003040d00c4003030150030f40402d40f56007001205500c040700e00c9034241089a01c0f02136407940304990700c0c4803d001d0f810068000600c1040699029044805034078460b900840c18410b4600104007068401d0340104840c58980c80d601c000d008078422450b400582a00e0408462442111094402e00c40510340024802c1055a607400b8400540d1000c2d40002c65241c2020500f03401d0340445100d2a000c3c018501d811a900012440d2030150344225001c8004030f0103061000b1385 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 608718093 1250 608716843 608716853
    0x20a05090c0a0e0d02120d260609060118120611040f0b070503040b0d0c110c010e0609030304030507060c02120d0c0303050702162904120f080d0c0816050a0804 70
    0x48180c12154100b0844144e1000684d1100c40c180c1c0c841c1850f100420000259010060059400c0020b0744070540318441c201c00c000d0f259145040c4c0c002c100380c0d01d0298540302c40c00102c1d40400001d02117030026001c0e02010510105801000043c68050708080c01043d182845414040c882c61041c80504040340c0390410035030221354007400c078803170182003524185035071207496001ca44e00c0900d60721425569848060542a009403d2031035a034046001803005039002800038002551941050744503402c041180c103043d580800031036000e0b40d4040155651141c0d5440c005d00401d1001c0403c91007510080e1804411400c00100103204a480b91b0340c10354a010f854074240c4c0200070143c80001140642d4207401c080d03140301c40c04d0800400b074031111000b4031603420303074100c58044280c2314034001004104010002244a9016882a00d070010341c800c81a402c18645500e142c415031504101031810a40c511400542100806100c0d10050000c0c012800002c401140c280c854041c8020100d0032400100d000f0138 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 608719343 1250 608718093 608718107
    0x3270b060d050f010b0a0603140601050903100e03040501110d050712051b0f0715050702040e070e0a0b040b010309020d0f3207080d0f08040203100203090109020a05090c0a 75
    0x504041d14946008045440321800d101d2207101401050f9121440c845203401c140c0440700c024071881c074080000c600142c0d000c000d5800050300e0607040050206401c061950184000d020102541008000c062001d040b450f0700c1e5003044c0b04031404940f00ba241280c00704000306280700841540c0d65424917055056594001035012407182d401080000e00c0940c10452148200d00d510245901c000e15658807400d1a00b40703450310a40121140f42e2244848102454014051305c6c6905d5048401083d40d0a0482110b0701e40307980e6500010450040000340004880281c1c04502c4040d130545040c0301041c83d0100540c00e4984d4688000d4000300c40b0302c0c403c1c0104166580030740007248121031a810032022041d117005200e044c03804120030254a000102070718001045103000802c1c1c08005000e0054504c0000ba040b415170980000600c00010006011075509002211610b00070003c110340b0b80c1071940d540740c0208581c1400f2030041b40c4184011a507031500b21070552250210002d2035203815002d1100710340352 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 608720593 1250 608719343 608719351
    0x100c03020405040603052505031b04090c060f030b04050c03010e1b040605091c02150f1314040f092121020702010941150a03270b 57
    0x65007808081600d5036240644402940100e00501c0810041c01240303c0b5000b04084082d40100c040d103041041c1e03100814050007450740101d005051107102000310b4050001e0150040c4400d141800c04030303001d81c00c00c0a01d840801156000c106445a00e01403008541b400d80d4a9014032106100410030003984220076907022205040701100079030040c03191041c1e608030390095000300d4404140d0000c00e0902d8100c01003082d03220101c081e2090610340110b034280300d0040005509d1100010321600c0314031a401110541c40c1e050290000e080e558600c0910303850b00700e00940e803103141019203000000803103000c0c0d0650303a030700007103a10000c3c2109441a006070364880480d205000d2100c1644c07840c84894020300140301010f88015940340454030004000c104a9041003900f000c0c081c2d1420b081c040c2442d00c1d21061311801c1c01205100d424141c1003281e0101d644015039205e200180402c0c042c2d00b1140141081c9000c585007401024804260280b860340303c0240c0441c01310b88040b290300402c0c01d1480581d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 608721843 1250 608720593 608720597
    0x21c080f0a0203130b012c060f04021b1605100807020723040501090938060a03080d09060b03120f1e03010308030f070e09070c0c080312060411070302100c 68
    0x3138421250340d880d0aa030000d81c005580e91060030124905695014a1100308000500c0d40000d140f030010000340040301080b800c2c03401580e01041c60108800c007204904040180303c01103403c0551b540c003100180d8411409000d001c1c0d064080d0011007180581d002034000d41b103580162030b4503420150000c50030201d0b12518000c100a00f0382e441c9e84d5456600c6814007030143c0707040100d4840c0c0c41d410050400c40a412400c0c500d40ea1582f03216080040c000481c2e01000f403106020041621540001031a0000540010b000784cc0c00040140c00c0b02155840304040758410282803003248803150800d41c039540d4071440d11407501c1c000c019040c1d05200c04401401c120186e0010384041401200080066820980045492480020500841503d2001140d602009515109040341c10240115910200180c802d070140035000f010182080245400079000d44800710449480b40520b00580c1c110213000e880450189113850300068002040100702c0c1c1030160150018088108542c00d034a000307010701c1d54200b003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 608723093 1250 608721843 608721871
    0x80a030c05010f0e0106030c0501090b030103030e03100216020a0f050d080c100905100522060203060109080f010c03110f0f030702010e120c16081e10020307021c080f0a0203 76
    0xf0051103403051944800709840001b600c82d065280809041140d500050305208000b40c0800000428030210f0741583ea062030002c0703c1c40407070008a1328200b14002e51101c03090021605641811040c480758551600803112241400c1c1c0e5030400603295501030240701d0f0040c25240d415400307d51031000405030005007008881c5070303c11038a19002160300c2842d080b19181c01504002d10850541d000d071603044000c000c2c0d01ca841c0310071000c19090580d43c0807001030016401000051142e8012903481008103c0e010130b0303503402d184e4084400d000b80900042000883d00e011485c0c51501c1205c0103841208204074800741c03501f51a184600c82513000201904210343d01c80072089911241401081214141c0c0e21040e91034420f5515010704203405018001a5900c540d5403c00c4031a80010390b8041c0804080895076503a03011400f2103062684c00154624014000401d100b403c5900040301904a002c00307140c200040013140c802c696004c41a0b035103a608c6030101c40420903000c0039034001d41e008801904105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 608724343 1250 608723093 608723111
    0x603150117010303020a0b0c13050d0201021504080c0f0105040203060705090a0312050d060e06030c1014030415060803030c0301050405070c0506040309090c052701090f0f1d01080a030c0501 83
    0x8125000c1c260011001a04035040170320400c401042540d80003001d00805604006d586900854800034600c00c00d441498115a04070941e4024000006852540f81d2020082c1c9400d06082d00365500825041106219515080c01c514006200e01c030301442d07005003e030090351103440e021109504107000490b440b29111070004002a07240c8000d0f280709145840741601e8124280109045030b4a42d03020b07146400b05042000520fa07400320710890307120421555007510038150300c0100c2d220544800c1003020440c001003844240311001c0e8031001d00460070700c001d03c8a55140c10800d9264001074034a400040c50500061003076240641049600c01040d00e0001c0c40700f110380d158245441c0c42924103501241258400740456443c0f030080d1441c01e051401c1141ca4801c080150500b9000407200e007000c0e120200380b20315120703881841101d000f4a40da101410703009407640191501c0d0100c41c4141c1c01148150000d0480411010301a40d0480f526032014246410203900c0c03d0b81e400021100444455503102050303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 608725593 1250 608724343 608724377
    0x807050f03160608071b1a09030d0c0509090c04060c0f170d05060909070b04060315050312032a0702090604110a030603020a3c03050a060207150b06031501 68
    0x30001000341383d458490a052550000e4030040500c0c41861440019081402c04551406140c01841c0d411401014259895555050950081007505500581004881540340da4880060710600f0401c07100d110a544491809030542d105506c01d440100b000f19041030041745089903c0c041c07250003500b400700c1401ca03010121410f540030188103215030756100f05000c0d240c02c040050300d40c041c07140401050180d0030b00c02415003c2c010781c852541019152002ea004404c0c01c01d10307240c010000034040b1140745044c60b01c12070041d002112040040759400750501c0b440b80d0342406400c034000b42d081d000c07440c1265940074403154040042c50325070400e80311110307000c0c9000c0d610014000c1145e1a03070001180d90440c0b04010725001180c0c0100300c428100d5100d40b1a60005128180b684280b20064101050005840550411855001810714040d90220b402481000c2d00207003505071050300b440324003004103c40e100c01c5402514079160880707814130008518003901e00048a0720b640504041c070b041c103910900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 608726843 1250 608725593 608725633
    0x7080409050c03040614010506093601031214042312010213080a0b01051909020403030f09080d0909020d060305060411010e011d0d0f0b070c12090807050f03 69
    0x1640a00b40010070041030100030f104030003c402540000784015454140092058024840300c14424180216500c120b140c1d906a02004130107400452200003234001b0752a640c06000344000d40381036110165003500d151050041d501800c031120307001c1342000d00381041c2d0102404480a03003010f400025000e43c0c425034420030700c411100300c81800541d550310781000d0b0103c01151988504503541c440e40202001805281880d030554405803200740781c103001d24065050419603980100c0701103100090201c141a440940e5070004080e030f40360810743c03079511080c0a6407070213010301110000760580814007004100d9002420b801150100110301c2c1522501c540341403190680d400c0b1004000351203080050f50f0800d80e4006a807009007025104089000003d10700c0c040c044205a200d4070107208a0810020010140c050150300103140120520f02201c01800d5100000d005842d00003018001482840c8503100050554950f030700940001d61404003031080184801000c02da040c040d031001007607525204a1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 608728093 1250 608726843 608726851
    0x20c030d0902190e010909080702060c07030b130203060a050a0e011a040c11030a0503070318050a03020f0102031005041a04020f032a0a08091507020304060908031603050708040905 79
    0x20000380050403441000040300c81c21102e40d240905040f0100301c4251807aa0260450707114200201e1a101a498800c0c210710400800030746c07107000400d0b0b0949070324000503070303c051368071920001f05942c07280e0b80300340441c004e900e20007585540031a0000720039450170b0308010b4010001d604041110204041980e080d60007a851101c21550f18201c141000d140500030f02f039064940c2e06110003010741952040c4d032070b40305e00368511090010000c04140401d20903400f5040c0030001505800607098140351a0b0740f142c3c04c01c182a030041c45840c5070200d080c0f0042c8212405036201d80c0d00d00c031420b0314240038440502040e5402e03060004088c040120b07981c0320380c0024040309085181040c0d680c5000c100a040d40b80300ca40d00100a943c0080c8641610880c0c2c078104c0760a42c070181050049030340e580b900286000088100b40000d40448000e00c150690000040d000b556aa6240c62408030781303c0b50300c0d80d545d00403400d0040781541604000004640a0320007011841d001c1c0300310314601034a400d192001d03500f00707803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 608729343 1250 608728093 608728117
    0xf0902071e020307030f080d02040e0103020f03060709090902060c032a120a03050c0c010606080115022a1311030105040f0e0601061115010b0304030206070f05040605030703020c03 79
    0x803900200200740c1c01e210400c594a91820280705040d801080d500d681e5404002e04000f01c80903c80180f0007100e042d00c0c03002d070f2481410740d0f64640310250b00000c6a0284822409045141d0515900380740c040f5029218041ca507640000311440c0803952409411103801c1640c210004002d40c9442c13400c01d10040209440f1107510700c8050050110341e90790941e0a2203c60304540044981040071101d840072500a17500b54070340802d01e5201d0000180070743c40f402d1011681580b8002c00001e180741c00640c40c41c121400365501c18203440191500f03a889160301c41d2139803100e00c400c010404945603d10001034030000060300d00e403045100000300804850b1150002050381d403010004004038039141c001d00c3c0001c51441e00034806503d00181c9103030b42c3c51060240d20b0a02041900000703445a04018120481c100c8804a001559450030503062680c0b0680e030540050154100081796035010b58020b01007002203550707003880e05192840403500c0c1d800140020017010b03004c000d0000101e10405c084c001440281e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 608730593 1250 608729343 608729347
    0x1050415150e15010206130302031801090b072114070f0602070510090c0f060e0f011e0e04060b070c0608070519050c07060806061e2a06070e10180f0902 67
    0x43c6002900e0702d00000c02603002d2034120800c540000e580802a551140b40b10084130300c8080140c801621140080c1e000840c02010102e000810701043c24240c07030020340c4200404071001d452031f400300d4a10901c0c0d080d00c4c40c40c000402c03c2d980000c00c4111008403d43c0200801420714000ea82c6e218141160001107818507074a5400f96000d100080101900414040340c1c0c185005141642c0a4503a122428007144030f85002c9042c400641d0080507003c494986100a0450204842e00041c10402d0034843d0240164a0a000812510001c3e01240da12a070042c40400c0c43c40d241c03100854090350010001c90800c1001d00c07052429030365a00007040010125111243c07954080712141c1d1420355107600107006c0061000030300083d078035002c08685d40d03943d40003190106d4010b4018024858412058510045502d000c1041c9035400e080d1510742400c20154151001c07501c07510022100960001c0303910781c4c802c0100403041c401c01d001d803110710019010140310102e440d641e40c07400390f0301c012a68404c0c1012a00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 608731843 1250 608730593 608730631
    0x6150c06090f0515130f0b091f020a08010906050906100504120b010311010e100c0203120f09010f020f03250209010303030f061a1e0c03030106020304050406060201050415150e 77
    0x552580d008103c81d203620350480941d06c0c0d0000440c5494409003070080c8000215a91307490034000ca01500200c032041c0a40443c00c013112200079800a15580000340c2003100100c0c00c80454083e444c100e13200102480c0c81d5455500c20042254190f01d0440c052103002c010000d030a0329030362500b032603207070003066042040d40c51400c008046100c04503a460402200d0f00920301241e89469201b80f000c0001e150400340e900302440071130314285004001d0000c4180228898000d040400c0003000019002c0c6c0e203c0e03441042010060380d07503a041c1c912100702a0000e024180c040140012a10380e089515142c80403080c24540201d940100e00380c1094000a4550303030302480303c03a03140c0184c40c0200361011907145001c0b00840c0c04107090081252440800b804141c0041d0034180340d8094410340700d84101500e94a59483c00065620b81c0a03100c2e450041d030402c40001641030044c40703007038816900421040d0110740c1c0012110000c10b04c200008680300022200841c1140c0e40f00c54030340c49500040260f0042c0b01b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 608733093 1250 608731843 608731873
    0x3030711060403210e040e070303051b03160203070b13060c030e0d060c0305090a050c09090307021c0c23013902030106050306010b12070e0d06020304140106150c06090f05 75
    0x1c0310340c0601b40950700348103404070303240300001d056030840380c0501c2c18540b00c0100c101004001c42c00345100303c4461102140041c25540003100b0038952610880440d10b040d075540d28030407454000c0307805d40a101141c0043c00c109003802080010162072107894010088180fa40000c7d500d250b4080050b5906652084145070b1039405101d01e0350043e104600401d40b4045543d115981e03aa08011060300409049000ca01506000c2043c2ca6216500508155000728013400078440a0101c10b01503606400c2c5a600184000055415090080004005036008c802c800015940345100c0c01000c80d64044840b0401056940c02c4086400e0864a05801c030746055137004040c2928410b400161003604154010050310200b5030403500d036800c1101034000d0a0b44c03450001d640040625200540180c0b4898040003000b10a6008621646c1314040b04440305803c1d050007422078500d406131801091010079542034043c000d00951910368420500407503680d00a650b5561190300940c0112030a6100c01c806040c040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 608734343 1250 608733093 608733107
    0x30108030c160b0426030c1b092202012318040e03090d0f061b080f0c37020705010f0512010509061f0e01020106140303071106040321 59
    0x42c0644444a0079034140082c0e000d05100703074400e9070009400101c10144e40301549480340c004080940030340c2d4445604581e0386848036202c0c0b001c886806d200001d0b030150ba00d086407045025034581d030380f180382ca0b20942080a0070440009416410700035840c1500f94202c0b090760340003400d440004000c23600d846042c0c0d6585c0290b4511118180701e203046c84031b958207150b070000681e040400101c80f0140c5011043c02c000307882844200001d4038040c100301c40c0242140c10b1540320802c040c1d46a48407034541d60340040c0110607400945107401c0c840c0007007102c418040c000e86070000300c19000300b01d0728180800e40c5480c1d0480b40b400004c00400750300645000c028568004c50f1010720b0840c5410035900e000c1c9a600c0034440103105010b228440c0c448840030a840e502c49000c540c0070000d1800716100c007071180c000003a103007050f40c0529900640c00c0c402d010445401035a010140c800c4081c0c011400e050b440e075606181c2651101156402c00001d12000010503d5503560b8680c1c030b12065200d8a10703000282001b0103032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 608735593 1250 608734343 608734363
    0xd0b01050c060721060308030f040807080a021b040e10050702280b07080f1617040605091606021203040615090f05010f06020d1206050d05010e010b01020a0233030108030c 75
    0x40f03190020800116003c24203c80e80100d141c9c003a540d081c0d94606c1c00f80c0c0c0d940180b0101a0201c07201103400d044440e000140404060724084041c003c034080d400c100010784000c4401c000090304841c0c0c08030900d5a558015a03000012801a548081c0d000000d0036100c004480341c0c001c48501901c04c03041406040e60100d50080c01c1c1d03140084107031425100344c0109602c0a00542001e00d170710b80c00110254842d0141c410086140118190310303040c1802d1201c082c180a0b6580100c9014810300c10f14090b204019071011612107402400411889a0f460642c0d074000800a85c0e1603500c1d07505000140c2070b44101c010180210880c0000c2d000040407800d000c4a4050700f0000280c100d00d44148111900014190159501403901d81d20952212036580b01525150344540c1d0400c03c4441c1c1c840030044190498504005060000c0000d040f80b08012651040e030283c0c00b0b9044415035004000c070101201d00c910708407101d0369442c1404066400d00707d0b0750754001d0380702e260300d40c2011442600c10507041c031003c440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 608736843 1250 608735593 608735657
    0x70f0b06090601080c0d02071e0c06020f1009020a03050109080a0e30010e0601140f030a11060a030e030708070203160f06110f01020703050415030207080d0b01050c0607 74
    0x180b45000c03000038048100103403540340c0003800400e22030041d00b2140c0456502650054400080300802c4240440400310b100c400c659800701c0f6400891614400500648a00c1c1c9850013020007100c000302e848000c011602042c2d030000d2031494040003003602402130a01c000c0c071491040c0c0d500c080154000b81419801424140f040d040d459201880d0103030079140c0480c000b5405a80c40c5900b4440920b1030042c50580110745c200e001e00320001989000032900176245001c1552000e0b450820b4804140e1174480400006000203410b4054400b2030800300d0140c02c0c030342d500341070026030103035400002807441d002900e040320036120009004003142428081d51010030090070b00c5040301402c05000400d01403140c010030041100050240850200812054419102e082c008550394203403810300401c40d9000d802800200c4540c031640b8440244a44229102d458200f041c260038900c0d04140180501958280207041103c02c0c040030304084401d02030a4042c45240c5c8407101030800b04903840341f030003a0f4038a201035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 608738093 1250 608736843 608736859
    0x602062409042306040b1608010b0f0703140f07060605011d0906041812030c08460f0f020f04290c0d0e120a030e011103070f0b06 57
    0x106501d41c80c022a030880e41c00242c80380652032040035000030080206540c605440390a062005201070b041d80e160081c0d03007010b841c54160f8401c07401610701d0034082c814020b80a43c10807402442040718409442c4407071003840c204e15034966a071007601e0f55420548048070003080001301380007000114840c0307600034002030170f000400c0e46021010105406032440001d029085c40c43c0094200d9070b440c0c0c4242d40003083e22fa601e801100813400c02d20368100e41018224042441d01d6002107025024442c094403c4902c02e003120803148900101c4880590070007003c001aa081c8110301c1d44c8a5401d003150141c21a40b020700088100801d8540381c192500d000b40405890710400540e01d08445c0d080455040d10701880b03610380c0454000c0b000e400543d071182148040e101b0040f4002c6042c48011554210081c880d0362203c603000641410020f08240e8007940c00c806034400780002000900980110210040505049400749124102d02e802c60340050300c00c0f102c4500d075880d50010018100c0080c1e8005c501540c03154 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 608739343 1250 608738093 608738161
    0x21090f031e050304090608030315030c060703030e100c11010b1c171b07080d020d0c150b192c010608040f02041d0f060403020304050d03020c03030301060206 69
    0x30048089100949520640390200349042c088108200c40040035800c604011055950b0901901d940081d200c000c2d942c0c10350b03c40641d81d450001000d01c0159801840300349030100c6954186e0003458820000b04160184080e024540c2a49218643c41162503840302c00140c0390300500701d4216481d0300c50b0184076a499040c1100ea8030300c40710075000800e03400349030f1414814410004a100340039002d10305610145100200c0f1071500d0200740c40040b80c00a000b00c0c0e0150b00c4004d002d07a103e10040b034451000403000680500456904030001082c40c03406007000840d1030640000c0346028000100c0d401c25822041d00402050304c141c15010460002d910340000d81080008141840350b03010300c540e00c20050058081014403003c3c01000070358560003001040f26a0b00e0b804034114080d20070b01a001c0501270092104110b0101090326032150364940e01542ca05814a000c1003100760424100303504500c07541011096540b13041000758082e10440c0c0040040c0c3c541009501103143c003120711f03000c010681350030349 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 608740593 1250 608739343 608739353
    0xd0b0f0906091902040603020306010b0c0d0e13270308151c0b0627040311010c0207031403090a2d06170408070b070f0e030c0a0312030921090f03 64
    0x68419030340081ca001d25250740f900000d0040c09868201951501070f2400000f602c00307008000706207065402080d20041c001c070b2a01030740c4a81d90b1042050304007281e041d040342180320300e900610148001241010b5010090804500c0c1e014007000210080347d40c0400340265082c03219000885501b04540ca4031900303600010741c0b2001c02000d41c0042171a541070010034540c0c0e80d6244490b540e58240101811548039200510b403010001740e5080e0081a00150b1001c0001018021140d004900303070010060b0f40c1c44e5035501100000e55145000441c0000d0007080c50640e503058040005040d01c4c1c002d582d26001c4900c07242014407804041070704150111b001005043e80203650b00241e080324017180d4080760740f6400c01d400e1500c03c0c0500180035120380010460240c2e0488110389006482c0d540d074881802c43c4100381595200700b0400345070b000c8003941c1c082001030801c1c0801e00c0180c4143c580819000b80741d0382c8490301500d8407007901150641c0c10702108049903100190000a16010640402e418910784072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 608741843 1250 608740593 608740603
    0xe01051302011e090b0a050d0f18110a05030313080c060403030f2a081c2007081b060f0a0203040308010501030902030c06030702030403030305090a1e060b0d0b0f090609 74
    0x10f241c009035449101900c0300d000d800d40c00d00810000003c1540c030401108010700316403056814420652803d220201e58685500c54400c2100303060014466001968440740709801076150f415900651a20001c079068400f400035084a00380a012040c0050410304840d0030210100300440c0918810322041010036404140fa440c00701240c140300b2240003e0490310480141240034203000f04540b1a00f490400002200415496030300b0950b0407001c1801111031002c1e07032066800c5c0c0c062010030240d0038490b0721482c0020680c05100740049032400a402e55017040d12151a61011540e8002d031040145020000507a181d101d51140400c515500c0c00d542e02400c40101805a02e040690710003400b001c40d10700308625010800020310035a00ea280c0100001d5496125000848c006070400000c120202000100d0103030b00c2c4d0340b108101c1c0204046000e600322201e80c0d40401c0c2c403c661100103050072030f1605040342070300701c0c00b41c3d402000301c2c41d007990a10a0920050050103d950101040126503440812 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 608743093 1250 608741843 608741867
    0xb01081c0c0c15080109050a05010609060e190e04020306090307022115090f10020c030304022e020616020f070b0906040e0c041505040b160f06020309010e0105130201 73
    0x1003060010101e030514001d6070546803c0420701c0300c54100a003014a8000603200c0c100c41002e079040c02680d072100503000c2070328020f20410b0040b0380e04e00d9060180300c5c003c0c5602c6200380760181c008100c1d500e0849041e0702400e0594840d14828400c2c0060002398242401040e80c41454500218070301441d80d80440c1c004a00c0789240300340103845188180e203551080c007544446404005018000f070405845480d00d480600050303800510031007a087d1601ca0207402615401d1141801a50650b03070b454091190507560444a9a0b060440c203203040c5c407280a40b0090351079010140e000748294501440089003030070090040106560052110b504100000600b50041e41c03441080705845441a0380450000d004503044440088628000c1014081c00080603000320303000e826240c00691030030401503c60307200b540560f290303841040010a6160309810090900300748608d9021700846869121001207030001e545078903042c0d440d0006050b040c0424000d498005030b00c00710144100c1e4203a40064203581e6615 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 608744343 1250 608743093 608743097
    0x60801051b0301090f06090c020d090602071a13030f0f020102150c0a300905071205060f04030c1e0201120c0f030f020408070b040608071b0f06090501020f070b01081c 73
    0x1719111040e1071a00a04000c1c080d41d04240460625401d029480d03a20100440c000540c9038800040c59a200290381c1c3c0c1220000746c00d09041910100459130f6a0b070055179040381c00c01d180d2000000081c0745808011980e801420100703850b590b103100082c2040e03105000007030201054028050300c0c02c80c1034101c61050140c2e091548000700c0c041e01c030340200560520800c80300751000c1c4203001052003581252035164402d10a84d4040c6843d60880b00306442040f4010748a42d110700c0c00501c0741c1d0343c800002e5070881e010b03040c10360158005039254400490f800d03d510250015004c0c4a10465030800140500e0760300300d4805000284102e07100a1140400c02144001c0580710344050a04040c40e03030403a03025100c11400d40e489076880350021001548944140130000ba082c00c002010036104007040b00481007812041ca0412400b5201c803a06500045c0090300c3d95a6a5044800021001d20050899250a4003890303102c0010342001602c10070305a01030325098110810508032001d2841442c680503080f8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 608745593 1250 608744343 608744351
    0x115090909030e060f480f03030114030c0301060506030a18021206010305100b01140703050d0c09080d02031206010503130803040807060c031812030e060a060801051b030109 76
    0x5003012906000049074140d00328500013031107000d0f903c61900038014034104da24010300c5407408a403103070504484d186d0055448024054800401c0c510055581c2d000000101210494051950120b00b1075000b80c3c404c48145030b07408401081c90405110402d403a0034124020070040307180202052441c40b00915210b07607280d03641d501c018058003010b142111180c020741901840e8608003c410f54801c005c0c04242c82610480000d40041c501034052640c0700302d01030b500c6d41040903054080c241030342c002c0746d001c50a0100610928a200d240d9201302c410605050340c1d2020f00c1480c00c42070b20f080c01481c0e2590400c64208000142044881c011540d8022000b8030b030440c2e41e503940300110000c2c40d0301c62900403c20300d400414082441180030213081e003070780511020848100d08040540c1102c8643d41c000c05648035260001022a140c84184036000c1e80f681004229000e10240c45400e21200315001080c16548003c00d200101c03007407040d80d07880b1221300d68500604038546d07940304017400144107180400340c807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 608746843 1250 608745593 608745611
    0x509100315090f0c080c0616021e1009030b0702120f0a020304152d0210050c090a12050709061212030f05070c021e0609010503060d0c0b0c0601150909 66
    0x280d0202c1d269039001015507402126502d4100d80b03424991045822602c10710440402e50f10f0221f0849080c1d0140c0d04150400c102c0c150b09002c168096201300d40c40000e2100300c518500d845e04090241e04075181d540e45006a03055107429002210050550030466006c85040740300002c0c00c100f1900d2484d0a0b80d50b5a40750605210102d00d5485aa046818050701154403140360036008075103030305240c1104402d03094040030301c5802c18030240100040c0740140e008202c0072401c3e09a45e03110680084811000c03500d86a06a000b1030000c0030150b0006a42288403007a07002848401d01003900501310f0030006015542c80c00c991291410750141001c4c1c03030020074080c0d03c2c4903140603078040c08140500500030301c610f00d0001c0e806400603841c01410780c00303000000d20081400c0111b03514003e030a14001c11560610002c1e80045449403c0101440e400420200802d004501030903815401000808941559840400100c4e4203004c01a4804945155400110540160481c425909071103c00d0400100c2c010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 608748093 1250 608746843 608746883
    0x516112407021c0204020a080f0601030b332709090c101806030c170f01090908130305010504140114070302030a0b150d1505130e030409020a0201090c05091003 70
    0xa003c10f000350320a01c0002c01d6001a9044111a441070202c042da40b030b00c0355078100065050b903001181c41e5a00c10f40070410729001c010b11540e00419000007214200818074650845003050340042140c0200e0030220340040103002d9a48440d01d5801c4c5c1c250f5108040d0308140720b0240c2c2e20046042801d100356000004040d0700c5100d8060205503495800040300003d999a10250003001c4020b2a4000a100301c0c01080c1c030244500e5109002e405d040704503181e5a0f19007030005000309450801101e149404014450914002e00b10a40145010300000101070400313281c0003003405000c10a00d003040c0d04040540822282c440c041c1ca50041c540d04003d6541d6884009040040441d203021070f0340641c1d10940380600c5900072016101954555108108041e00c200802984040394841c3c654030014003003060000303412a40003501003243c0281140d0915413514070301c0301030340c00440040c001030303550382c4180041c04104404100140400c0c0e0b14500b45041140c1302550340102c0e0302000d0f0144c40140e00e4109065 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 608749343 1250 608748093 608748139
    0xe2b030e19020607150603120323090a020909030a180b030411040b032509200f0903060f2a030711070803070b0108102901051611240702 60
    0x21341d11494040800b21a14401741c0142068003090f501c220134070b402403e00500030b1003900b026101034243e03480c10111500c90782e441881c000f0203410040c02241500801a210520700c90b0160b84c0150240d5141d201849004011040080d8000864480080204a03500c030080440342c020340c100d030f4640610b0007038201040151403008076882e0140b040701c2a034900904103d00c80e01c411829003c0002d500e90350f42c405d0798150303101006d0709801412962201d1007150441d800402062001c01d8000341440c0d0904006401d00c00100c810104099a060800c41c040c03003001030030110405054205d4409090000c3e8a0311103000040900c401c1c0301c209011581040001c21140700100031460032280e61340d05901e0000c03c070110a1052100700c6c403554807079000808641c01741c8120024807107100d51011184100284810a80c4860141404410031031940c00013402560a6100c0380140c001420341c042c0360050007082c2090400c0c52f100c04410304401e04514001c0c508803244190100c0d0003003000900081d80c85100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 608750593 1250 608749343 608749357
    0x915020d060506072909070b09030a050d0522030309090e010e03160201020705120604081b01050a0b011710050607080409050f0103021207080604150e2b030e190206 72
    0x30202c0841c0040800c0b0b080e10803c4e5114003004540700c11185c454801030a0410207542ca0803e0741c12503034080c014860814040d180821004044a10329549501c545052401030361002c00002c0d40024002e605030b102030050b01146c1000090700c00075910390380700203241e10604c1c02041010358032a62803240d420400d4000c6a01c0c901000147c03540da44000c0c650800d800a030850480c0036001301f0302d00003110b2034400d15104603a41e0b980d005d0400b0380d41c1c030340d80d400e083d0f8081940101046e0380c844540850101c2445070b984174045803400015013018140c000351141c4009807199001400e5101004410755601c80070108442c01078400c0d0b520745819291006050080d5001000b52603c0c1ca001c20070400d100540c4541268025038000c00240d51440c4119200d2120740038000d000c4c0d004001183c00200d4914454410340d210640004104000303141c0282084403c14030128a04030200300003081c0c00c00c050000c0c000007014103080181000e10000303607849007100c00c8196040304030400c0d40e03025034440000321048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 608751843 1250 608750593 608750599
    0x3030f1e0c021206010807090b040b0a05010c080717031e160f091802041a03041e0f1407031b06020a110d02060705150a050c0304170f040603020903010c030915020d0605 74
    0x4c0380da142c01c6010303600c940920402e580746040040e83c010034201441407414512024120fa1003150034100192441c651402040f1441e00d010040c01001c034002d00c0c140c240c03155000c824540d40c6d05100703400c90b0301c5a40c40254921302d14120001d00c040344200c1110211400702a0401c950400140f02c03044d20044035036808889100e5090a054261140547c01081034030b0844070259641d1000c0080e00e543d90008480041500541c10b18001c50300740e26034003034080c8034850a00300108580c81d030341e040e01103030707039028500341c560700204003401003258115034050040d040c003c4400c134403403030001d00950760322584401130040c0030a00b0781100b8130b031144081304800035005030503103a0380c3d6058a0100c0c1e4070145c100c0340c05100c840b81008541046014056507000346402002c050450701c40f5160706503140351101d03404031015000c20007030000e19400f0380500700800580d100140c42d440d4060515003528404038034041014030b021aa9000a1009080c0b9002e500d105040148c455aa0085490003400b15070812a8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 608753093 1250 608751843 608751853
    0x30708010c020124050102030301060c051e0f010506011e0315080d02030d0c051e0d09060f0209090903070c0b031305070b0a0e0405270c04090c03030f1e0c0212 70
    0x7429015007148042c10390001c070103401e80f1030000040000c103495000d807500607003080004000052180d401d45100074010b800b542d00b01c0103c41484080e581e042c0381003622681002400c0c01802400b0320410358068401c0c00d03c007a03601424003154004e10002c203141d44c107040da03412550104644d00e00d2114050409242100c103456149d400196407a00413440d030490080c1015514100c540c880e20980d00c82404841442d1070141c2c000c6145d01031508400140708610741d0742c503c3d00d00840c0c45402020200480030f9001079075280504140b04241500500e0143c02c0e40c410070040002850060303624049a141101386526a10f8003c14844910207401000d81076100d044008210007000c403005101c801d06a403510003070440f1950500c000d8803c03c403030340c90800320b40040b10322150390000640e0358000c0452040d42c0d0301e80342201c00541200d001c035600b5a49000340942c00c3c801c141e0042a000d541003a02e081007020440344201c1c0014030f6110318045010000c040950f00c00319103412500342a694802ca054030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 608754343 1250 608753093 608753111
    0xd080a0e1b1017390706020f130b0c0d0509030a11030a080d150522020a03090f0b011d15040b0105042c0a020720060403080414031e0a0b0603070801 65
    0x30074552203e43d9a1a140740820b03600710b141900111641301000108500600700354503034982e60002c2d0881045c08901d4001000001458188455600b000e400c11540310360b00c0e4101141100d00d00181c221400c401d000040045034203a0b9000101494a168891054034118040e0030129040120425006140307507008521101c0390303115a0480c100c1c2c814900c040960403940d0340104088442030300310b84102b24544442510203240207070002c04a14038039003404501d030f413426030b28007010440c0450155154090f0f5070040c0412110100020403100c4944c0455265040940c01101114001c1d121907208541c2c03061f03100700e280d00482c02e54004000e2a0b07018585d543c07000d0a00c840c0c101301101c0e0b02d0102010700c03000600304510b600c20303102c84a4020036105e1105211005540c3c0d8008500e1105907c24410302001001500395801031016102ca08902103031010004203161030690000c0c030202c000701058082e209884400101c0340001034005040394401e8880382d02180c18843c1d2034019030415420100c00c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 608755593 1250 608754343 608754361
    0x2403050303061801030809040509070f0f030210080103150f060e0a0912020613060e03070618060c05030103080306090402220b13050720030c0d080a0e1b1017 69
    0x3440c81508142d0f003145402400207015202d1807400d010044c442d06041c1718281d1141001d5010981c400e01c40c608a0340c072a92100801c02d410311107980800070301c690b510310500c2142084205030800002c54108508954155a115507002848003036503030410340c5d15003010485d001940c00900c01003400a00748030847c10011000304c050445080c082e1030320480b901000d002203100161140c8112002c0050084c0c0b070200d03680b031f40080d100c0c00b1781003ca00d100c144810008159103104600541d002801011a241c42510740082910b00c600103400500806000401c013150b1503000f200e0344050f0484119a45656520000310403015401c402000166541c03030748404087c1c5c1c1c1d4041214940200c80d110724600780740c000001520400c07604030b00003540e1078540c95a4190b6940a04940f0445682601d0500701d92150452411000c40b41410004d00c06909206d07461910303104108030b9003c040c010744400c1551403520f6401111201059009041c03003c02c03006442e2007100f000c031110020f4480f04901d4202004030b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 608756843 1250 608755593 608755597
    0x1061d0402120c130c030e12130e190203060d0c03060209030106090902060904090201121406090c0a0903080901111504050c030303010f14130e0a110a050102030d24030503 75
    0x8124010300d1169041ca241070300000e01110740740c1c4000c0c018035450311300c988520050036036590410207254540388050841e12042c402ca40301e2001100d05684c80340140001c00c0000c00c0c4951040c1c2c00c0724036523000d000303010fa07050076500b42c4005080740240c2c0e039841d08008070701d004400c00c0d409003c0b041181c03004020049140c0042c260308030114000c0c0a65516403590108642c0c055500a52020041003000f80d541056000350810741c0c014101207001c0d4205480e158187e40180314514a280341c03500402c40d040c502070302d26940001010100d50300348006100c0c06009081c1600024000b190085440d030720682c4110822080f91828a064441c0011000340300c415900048d02c0c21030380c0d07006402c681700300d1b42000002e40703048a040c00100d0701d55914041c407100950420b40e051540241719019410030607401400388001d88800725008001501a500704541040384401ca042d20485111030200140d0b84d00006682080700c040e180052180c1104007144802900c1882094241c0c0411400100340302c0c004c80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 608758093 1250 608756843 608756851
    0x1a07020c0307090b09011701290312040503030a180b0711090f040b01170a061b0801081b04391704030504060323090c1f0e060c01061d 59
    0x104441c0b20070f444158400965404608040d00314858200400c102c4a41d145145003aa07401c0e800000da15503040d88011825041c803d1240110200382c9149006040c1000085500101d4408083c101420722000a803248903140107070041000c8046248408158038544000074004260450341d282c84900e404901504d0708842a40700c0e40c550000104210592100c040c455035201d42c484013076070300307110030407442c0e104052030440c0034491039040b0000500755205510242c00b4602ca841150b6640003c000c15000c070581240701180c10040c10b161401140c086404500d91007200d003c1480002138a00d6800d002c03104400f2004201e04580d15040000304040d1221411415590003200405110300d03500d900609030f40060006004002c01c1007003a1090f0701007100801d00060102045003c0e40111500142c1620b2140094000c0d008107c0784d4a4010a1828503154a0b510303811603800d900d0024202ca8007089590b8003415001810040768607003944044040c0220094800d41c54091200a40704544116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 608759343 1250 608758093 608758099
    0x8030408010c030e070b041502012003041e0b070c0203251502031201050d1104051008190c030b1e07120b030613031206090204080f0105011706010605071a07020c 71
    0x140084c00070140400c80c4000c1d242a01e0501e45421b1400308402e484d941d0040c00035085550b00c00281d04c05194181816000000000c3c81e9516814181010001c0315507040b4a0b00600140b01e80c00d10014001e41c00040c2d0040302c5003000c4031031400c0f03800402c1c20401000c1c5034045800003424083c513100702525000056400d51103152002e03a4030310030b06036a00c1c4902c440c00e00101226100401840c03501049180e000c0d880790103041e10340001da40c0450160390050352008546142c024081c460f8440070424800880c03141000d0380400b4010b03841d148081c0c6810b000190680b10071000144a2400b000104e032540386840b02d0700810361414480c0100141c15459245506600701007000080749000a609405101c2106d5260090b24050750140d0321100e102280d082600d4807600c002135400018406032004105c140090b0064000364007240303007100c0050300640031030f12500a1000d00071600082c1d050648000b405d115035525078500f440b0f402d00c0c0031100c081c01240064010001a42c0e030201d11100345070426 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 608760593 1250 608759343 608759351
    0x602040602010509072d03140c0405060d02060d020d15091b08070518040605131505040618050604090b180f03030702330403170603031206100908030408010c03 70
    0x1e13640c00c2c3d0f11102584503141c0186400b81e40107141c030035080014400c074014605c01100591380c0755980c2592031152a40d640c001c0d00000328006050801e40103855200d0400c0b070f80304034098916800503070240114860486c0207030b4003250a56400c0660782c00980c41800c00000c1504c1141d07140311040161061070300d000020445106001501030041d00564001d2105444003420321481159000140315403071072165000e6119080018a625248468600c10030091000f048245111050205228840e40803034021864050304100669010000030f035500c100c0000410b40d07889100c001030140410b00b20281c011040401441801d2400d035101e1006844da110a85015004040046441e0f0000300c40160150304103483d16030485201e00c0c01e0201d901c1c9100568101a06c0100100003105e40455044000c610b2503140c0b10240b0303041028a6a000b0302c210000c52030000c0b00c0030002e490341c001404003405034250440380d030140c0c1d0103041d2a0025040900c110381c2c4460f61a01603902134008003034414082450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 608761843 1250 608760593 608760601
    0xa08090a1205031e011805090120040603060b0a050d0e0a0b070e09090a020a0b070303090204020a0806010e030708120d02130e0403110a05070b0f0d050705030a0f090c061110060305010603021f0815010504050d06020406020105 98
    0x480fc20758000803655103034070b800d24480e00544405000c2038a0603103028040c1d4001c1c02c0026410100050250f001070f0f5802088044040621030503485c060120710150340485080f42c01a521240700509949000010030344411862506038058210040025805030012070301c80d50241d40b00d040b4510500c02660b032404072001d404c0c1071507100c107014082c0180c69000101451041d4003000024940c8100440c0011305c0c0442c45850151484619040883c012141105100505a101800c0c446a400b80740c0500300303480d03080d40da07550380e45480d1151045041011600342103000ca140107403280c2e040d018806114514060100801a03402210041d5100780703031003040c80000090340305085003654003e00c02c8050600705141605c02200528142c5804d1003901c101c04e9040a8030b024400045210b100049a01c905600c100031400801506d04001a0400001078100c10740c484000d0350406440e0320802d02e4080d8550048501d8402c0d60009600310488035030078010062280d00038021510164006c005d0f1340c403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 608763093 1250 608761843 608761859
    0x31620010c030c0806150f0f040306060f060801081507030e160f080706050d1a1816050f030601032004060c0b0f09030a08090a1205031e01180509012004060306 70
    0x101596000e41040101b03001c0100d0600140040403000703100380090b07040c1000341c401c40a55034400d4104031030607621a8000c114200c1c500c074214000e883c007070812034443e41c1040031096a4207090f000c2100b126040d04045480c0500030341c48552076540f120b0641d03102418a1603d414941385610544088080c00b0a0008020101140c0c00c025560542d03501803809281120320b00203403039003029141c41a100348203854100d07601d0900511886030b60300c0ba8075059281c200b03081e440c030086480141c3c06200040100701c090007100b408882d80b06034242000204d00c49540c0c1c8085a80003101e14500041c200010f001c039460b9048040701201c240300f0541500b0960761003000f945264800d03201d100c482e60061060119140c0641d2000781c0c49000402291140101502c1e469402801130280c4c0d00460300002c02c0c0005220200406410100003c1044a1551501101c15403e044040c94403101d503951b04d0105e50140001e4000441c81c060b5803001800f460050411907283d94040d02c10f400c040381c904080014240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 608764343 1250 608763093 608763107
    0x40f080f0705150f0306191211010806010e0d050109060c230406020a0b2206090203060f09030301060c0809040c05091905011e02190c08070b0f031620010c030c 70
    0xc03001051039130800841c442005110b0708003405d800d90001800c45c0d249641d12840b13540750014201e1075140b9200b00083d0425802c0d6044407030046040064590402040e039822085d840200ca0042c0d800e002140d5083c01c1076030060030300d030308001c003d281018080d06180354001304000703000e103d0031103440c68402c2100f500c80292042e8403682e40076800100c0f207a000300d40807288080e408003120000e0513080366400400c007408208401c04031184c0b03640d900c107a0150f0074108800b0354061840c101042150408011850b82d900051250324204200650320004001031340e400e541112201a009100c0a4810000a003a541002c4c4103240070b140c01c0c20008240400781c690050484106844211503032044e00140341741d18081224030300c00d51203500348030b2028001425040704c0060003141c7e4070341c0707480c148807600c0e00f04001580030360143c15040c008a028005450308aa40224650a4042e88612020015250007a600501da00034100c1c040c905045084c041d0440021160300366001c0008080d1103a003543e00d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 608765593 1250 608764343 608764369
    0x801170a17090d05100c031103190510122102120403060225200609060f090f061303050c09090a1104020d0908040503013806040f080f0705 61
    0x11492150116000d401201c00802072240c000d4241c0d0540c0485403030f07180c82c1031621060b52400c0c0c1d59484030100d503180c1c50701c40d40180528100c41c580ca1800c1c0401c1c02550443c01c1071090304055a2000402c1c00c10200185182c000d21b2401d213072161082c01810100940300ba01724082c8640029580401030252003c03840900e8000c40c042118140b1342542c80d048020f4000c1645111661a41a09428203040b0308a414003018410031510f01c0d10040354103200020010b07811400e01440c024001820b0654407070f010b0740e0b20050307044017164031515010001000c101810100030340203880001c0c020128400342c2c0500e429240501c1c200c80080140c0c001b8051707012011141b070a029045031740100700040d110115000e0103c0e00034805410600424900d204031100c0700800c441d80c4000060401450800b80606921640c9131804500e80140c00d507410010a10102d0800403003c000044501d100e945280558000e841c07181144e59070552140e900ba9590300c084400c1d0030480c800e5070000142450404944450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 608766843 1250 608765593 608765603
    0x10e060a02071e02010201091406040c05061804050a0204050432041e060b0301060f03110d020d080d020c011a33090420031905040f29070801170a 64
    0x381081100302d41802019034000b2170465480d11503000101e401400000c03240f100d410080c0c11642802e141c100541065644101c2c090281130041d2180030041d600264000d0000b503c2c041583d640318110080244185c0e0482031340700780340401c03500c0da050518000f01241a4a114062088811144007504500c4100e800406022035407100c503440c6200e20301884c4501b48a01c0000c90241c000c080020300317451064001d4204400b244204101380700c0050820b68502d0400c0d902c07402a000d4a401103420346040a03405001d180c0009103603251560281e044410040180000f003100c0144040701c030100e0302c148000d841c401c0109800c0001d0b180200101800c490050340807802580c0e000c40804940c54006100540e4000c0d0344059620141444a1040003c18810365482c1d80d41d00c0c003045412a561407060003032454510700810440050094500031503250b8000e0700611144100e1110210511501080c82039480100c9081c881216048030f9054180e641422a010a502071240915030b0b500c00c291002d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 608768093 1250 608766843 608766863
    0xb07022704110301230610030e03030604020702130f0221090c090603150a06090606110a02011206031a1603110409090c0510020609010b0a03030f1202041502010e060a0207 75
    0x3075108026000d62407016001042100081c050a04064003101500c1031700c0a41408100007443d0282c4078540e0229030341410040800d1951649549010003410f46020702da00107511429951070400040c14045107500c180038480d404450480690000384869181a620742035540d0462040c5034402d128021402c0288504201e4078100310030f420000c4c0c012501030103058202c108440c0c00c0d0310110312403049620f000c03401c1e514060b0868208c9420354400820000700d01c000b056220030225541d099244c09191040c0000f1410560000500703c591000f0b1031100300320003030081040c411054602c1140c00f52651840221042001e401b034904030f2040c42d044080400050005036501c0d07102059560190112070b40090710344010030b100300c001ca0103080250b03201d03004014084038240140013042900345d8840980900e0365402815040b000f140c0003082c013050081d4118001d030389a040c0ca00406040009110402461001038020040606084281d010303d00006120743d286008442e00fa99100603001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 608769343 1250 608768093 608768101
    0x60e01030f0e03120609060a150815041d0f070f0314010204050d0b160c021305070c122a08040501050a020c031501080f0f0615010e09010b070227 64
    0x140100201209441c0141c0d0360003855038405810005000840e412115030015800c11800b0000718410045c08280320300c494103402c0c0106203804440481d840d034941018129900c0307502a8140401001c040030340c200d071904030541c3e01c80d01c00e2030b503540b00043d150f0113907003022622170708458079104140244846612404c2c0e00b08002440d8601380e07600c0c00c80e200c00041c2095181c000040c0d90112a84058660200c10740c24400c021400c41e014203922540350030000340c0206564041011413010406000c00e4070394410000e0000740c092600942d1556016804a80000300054007420035801440b040402254000f034003d0b283d0040e4608480c5182c1119480e400c2602d09001140d10b54880c20b10380703086008000c0000740c0340c0c60070400700349140c210a4410005605100d8042c1c90001d8502c032404030b5500420110580b40c101203086604424611102117080283d42d00585060f460b120361143c1007056240006100f09005001c3c203811072080301d501e8101410704135030b40c62104e10309000d408500c040e04089 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 608770593 1250 608769343 608769347
    0x4030209160e12030d0f1d0105160804020f030f030d0b1903081c050108030301090b090709051009030516051f08070302030402010311070c060f020a030c110a03081b010b0604060e01 79
    0xf00382d455801c0803a845e03d507400550001b42c400c4004c2c0d9100542c3c441d14240055018924621707100c9281000812040ca400e184d2500c2c044c0c285001c4005102840d00820203545442c1c80c0c41d2148103003c1d0454058038072a01d5000d07a02e500005001c00350500c0c2c640040803518100800814069050318a145d61505648811615520403159031240000070890307151100c42d6130042030f000308040e40107103407a90715288032a82a11080092240305244440070405a540c024502c48142c85082d25076056602d04850151000400b540004d0a5841160000b40f583c442c0044a40140c440c04e883d211070072404201c401f010b0001210034070020480d80030010318414801c0d4007071503000c0d005160200d8030120800c008140d50340304280940342403030031a80901c50b140d00b0035984038800c00d00b0f20042882951030b0301e00901da007484c040020039410050001c00610380c0c4941c3c01c1c1c8081d5422503011980d80055004005000000c81190307a10340d400c00341841d04503d440d000b5201220201c1d00e034100405420307001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 608771843 1250 608770593 608770609
    0x71206050c091207030c0e06010503040605040201120f02041a120406020f130803090906010806150306041d07080f0d08060906010c0b012606150d03020a05060c04030209160e 76
    0x1003880c4007014400d0242d0b80d540e41d01100118114031024090480c11400d0180e00401640c229410030070341801804070990b4003404a179481900004002032503180c510040701e4069112001c1540c281c1810140424581d441e4002c000b26042e80611144600002158070868001d0849145148240c40c000902003442600107115104109810916041140340251211066a0400c0400b60310102e0a08468180072030320301d4004009080071881d900d2704000041103c030a10b200c160000e1004008039030700d82c4564104aa2401c0d2648070420540100a002030340c0300c0c158490241c00388030380d0380910123150340800c140c2c80e1498942d545c02029610071003403200f0381c20007030111410060741411030004145041111406440c400d01c5c04d05481141c603540120003040c031000a41f0300e400c08400c0c400d960302c0c0c440044500304016510f510031307828142030513414000343d0f00c03019040780151410810a20032107030050007528403c540d91110760702c981181e000740c03001404010703012901504480c09903141c0086 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 608773093 1250 608771843 608771851
    0xc03070b1c050105060a1d0a0608010602010b04090c062a060212010608040b0a050720030408071a030109090c0e01080114090c0102060106180f0b0714061915080109210207120605 78
    0xc114150041f600d022550440090348000c00240c8c8060042c40340b542d0a002e018a03a8a08681c10312166645c0c1d1281440180f80740301e140700b4000760180e0080f12076583c010740d0306003030044600380d07140c4207050805002a500c0b501340d408140ca1945c00200310103008c0d458245c000d94001c90120410350b40c11030600000e00f400f0788840140721000c03101449441d10066851000c1d8007180c055911180b42100e52490400c06400c50307100341100e120081c03c05010304003600d0460b10000e00c00f00382000d85c0c0c200450405019046611802044000480e9510054000d10402001d0440d045402d170307102a666511840c983d110540140c1000b001000450700c6010300559a48070b0786200010265640e488440c81e1400d5030000d8061200420b00806001c98100c04900c420309c0c1074090070b40d5150000d091009000c0420011400c2075a445000d6040c215181484002e0301000c03000300f004103114140054444409504082440300c2c451440c0012440452000c08550b40310284030842c0307002d552001d014210040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 608774343 1250 608773093 608773127
    0x9100e0109090f05012912030d0f020c030406051c0204150c11030f0604020f010306080304121a0f24010207050d060e0a0b07030515210c03070b1c050105060a 69
    0x4190b04041342c0288100680d84c1d000c4120021001d46800003407441150700f202991203441c2820141c1c401d182c001c8125000c0f14640c080024143d0410030755440240250707842160180720106000c44d1240d04100100920301c5030b10040d12140001c510386030164803c038014004031007100611004450b000f4840030350400d1041c00d02011600e41000400d00d01000d5640c2c000715030340444184825401e0241040c6c402410a280900c070340b500340808183c0e68800c5200d621941e090321f4a40350203002141e2110414118810340c2070710242080b154240c0980016034071800d00b180c4030308044460000b1040403005895060700502501881c06040080a441c0c440c1d0940700ea58407060540c21090b01800703c003103202d10400e030003003103414510001421035600500c00301c82c200d00440e210085540b5818840c07041c0e0b0000912104a03808000341c24181014140c40380d80501c5a000041022901c44019060f01242d1802c2c0d02100c42c5010202e0307050703032820711405405c44400c0000040c0755200301002d80340300300d0403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 608775593 1250 608774343 608774363
    0x906131101141c0b0303180d0311061008010b040603020a0612020714010c080703050f061c0b0f0601030c0305040c120c1205160603090515090106090f0b09100e010909 73
    0xa2032140202d54065810315601544488070300042401912500d00195811340c006c41c10444095402030900c1c00c42c0c6003c502c00d4140000c1c00c02014800d01c4900c07811240c1d02e027942c2040c10003243d05880f103186405044415401c24000c0d07540c13410a0300c1403000f203130703001008420004e14000050f0f80317100300050340c51680b9400f0000c0c0c00c003040300300c4600e642520740e040c0006000705803510020000b00c000360428007014103100a1250040602e03404907080b82c411035262401e01000b034605141109010381c000c00a060170010800c5600e155100988034110a803010311003034041c0c0c0d00c118204e9400311001010303101a28000e1040420107404442c0f4640300720100b1008070b49501c034003c9146032001c1d088407142d005002502902e031035410310100900345030609000e050015500c4070f40701c60886c50f0401340348031910002404240300b5080700b8000e1410f10000c02111481e010403030081c10314500d40e035002d0621900450600b1800014020031905a03115a084d50703428040b280d000307441c211409071451289 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 608776843 1250 608775593 608775617
    0xa03120c05090d05160b0c0a08092818060e130609050303160306090b101107091112010e06010f030903030212010e1b09100309020a12080d050906131101 67
    0x294101401d03c0d9010300001c00e402c50a80d001042010a01d030011420b100e4188a010011b19000503030041d0244e10000c003688a0303840c17a01080c5180c641c1d443d031150081d0003104501d20003000c8000c400c2541c111441c1c145d0800b01c60080407043d15098810344400a00b80400182c0f00450111450121f034411140171a494042d5183c50340313541c0080c0c0354104d400080c60700e140d103415010f110b800002c003001d40084c1310382183d00b00080c480c95018000d4405012420802e40c0080c58140604001352200d0f4408224407901da101032216a0050390202410000722000800c941483c80c0010b442601c050f0f41e140252140c0c40e00817009040085000c0f803e064090245940602c5c40c0405903002e014610180c08031441c00008284003180002c180d8501c04408101d140314513152061260151400760901003140d0000d84085484000180e00c41c800009115140301c0070000b840c00146030740c0e03283d82c0d4140000d8584110360780e240d5600380c0706242c0d02403600e00084009441c680400e008102d05051101000c11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 608778093 1250 608776843 608776849
    0xd0c0308061c0b0910110a121b05040302151e1b01141f030203060112050c1e0306071701090515032e0501030b0c130305010207051506030a03120c0509 66
    0x22440d00403907107460001c00b00f01c8402010482d00c25100003a000a01c003017006d81039010540d102c0c400c2070304100b02e88039928003408241c070b0b0000e10812605030091024400e014400510b82c1e04940402c0b845036102030030340b581030360448007507030f4070101481ea41e4147c3e1500808450030541c000c0c01c00d406c4115003a8844001900207100701044a2540c0c8101052450948122948100c1e05918100d13410b00d54034050002d40c40003d0380c0303419a10303004500e4404e031b0840d00748103207441d104840300c1d54408200c10421031910f03881ca01e1818031f07143c2603048a0650b1145503050b1382c0c881411200d4140c2c0e001c48401000621166003040d90403405400d0481905100400400d04101074240c0034016031510081c401c0322030000300c1c2e0041c1d00c009284c804011650460f965110741c0080a40300e107040c2c00d030100e8010300c28640070740000001d5038483c2c02103545803154501981c403080881c00403448004420000740040c2000300e002d941d8154581e6070310110304403000e10500144031200400e001c022050041d501162 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 608779343 1250 608778093 608778139
    0x9061d0708040f0b01090b09010e280b03101a120a060b060706051317120c0a02070510120f060305031207021606030617071a2d0a02060105030d0c030806 67
    0x4078591b4049000c801c84018062410300682c022082484008200882a0101304640700e03500100c03e0320001e14bc02000314040542017954640b43c0c90300840d012074003820b00980c0034182c1c01020404103507601008000308014591406501240c50300255903007c0041d407a83c1c8102141e000c000c001070704044150304c0d000c040703a10840c0c2c04c00030038403001d80a1003400f606688070400d00c00d9080400d40341220898220040d0480584031140f4001e0116138101c0b0a0300a100b407a010b00000b03019030242400d0018010030304041e0740703028800c1518152503c11400d43c28081c07a012b60350850010f5140c8007101a032000c00c110003d107004218040c03001201004901d0030705030401840c5655001c2041030508221425582e8040c00d80341d42a44061800c000711905502d00803a0365501644942e1a854040d0200000280201125070041c001c0f0380d10389040b04140e409400c0c400c40c41c1d4212003040c2c0e00d900070301d551901600c01703131004600a0b001d880006840341000b180e200d0000f41611409840082d1144401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 608780593 1250 608779343 608779349
    0x1a011e092301020609030c0d0c050f0613030e0604050f06090d0b0c0a031a1804060b0301090c0e0a11180f09040302010207030807141c021603080109061d0708040f0b01 73
    0x40e94403000300c1072140da4100035464008410b08081c2d1315000d811040e0a940707888441c1ca1405110b148500001030100030300600303103418035170310030380d0542d284c60b40f480c1810503d0301d9804c40c041685424000d07a0790410340b083e642510303809072442601d00344000401c0703003640042c40200da0221141c1000e100040321080c0d84c9004180704e1003e10f840300d0800d94041c058441495490f00b046015100320380c05036444c0803244000100710300a0340c0150300c07036080270320103050449d0815801d50300b86a401c2081004260113a41110044034503200385441c2c0315110000e40c0e003081c40308210078500340200d0360b000d40414030720802658010503403144250100013291110300304580036000750354046503200074560401c40c92075103c0458504010f07a42014903090105004840a89900c5100b4514820001c0320f550304492034803081d5040702c0d19410503841c00a0039080309018078a02142081e000049188512102c0d120141500c0d00034804c0399150301d421140d07110020001d840c4054605005004540340c29003160103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 608781843 1250 608780593 608780639
    0x1703070e0d150b01110f0a0c0602010b0919180b010e010e01030f0b070903020d0605070f091a0a0c1a07140a020a0210180602101a011e09 60
    0x124540000090915400200c0050060100c440340380c002400c030030310b000c81da00744008000818a50b41c000403640c040000c60240071600c210b211103c0341000024501e816980700c0c0e0042000ca40c2c0340d0004900340e80f00d000241e60003000c80d0300403038111680c40310082c0d4111000100000e840c115502e114464201211003560085c164000603c4000034442c4801d01410800080944951459580b00801d8035803510160800d40707900041780c1d590b4480d4404074000d40c0c00410000e141d0310380e030400344000d01c801e95402d8081182d00b020031101c5401601d0803c1200c40e800c000440030a1020100504c41c0c1c03240341120100500001e0314070003d64003154810340301d01e81e03844040d410314005101401042c10b054602d4a0600c051103000c0720350341d002600142c4550705450a03240041c103914282c41e42c02c805841151040038090000c10744580c0041d8103409880440c1043c40090f8007a124880c503d580744554900054020a400c0100b481150005805030900d02d001c0105c00d0307640112101c0d14604d0358080c0c4c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 608783093 1250 608781843 608781847
    0x1091d18031209150402030d05030c07020405070e090f100512070905180705190510020109061803080c0307050304030818071205010b0a14010e0d0501050106081b0a02060a0905010917 80
    0x30f00308101c902da0f01c10044101c90214142500081d5450300403407408010000e00000142098440d40c0907140410b5000d84181300c2410b0114001c0c1560b6101c200f854010005400000c0f845805910441d00030018080942001030038103050110404003001c0c581d00910a49800090229a80c0300b10784c82142c2c0c525410101c1c00c40c0110322810061950b000341d1103104201d155400c800480c2d41078004a4804681d80810a90840c40c02c0e03001d070031f20a0014201e00d2034020700a4002880d4402e04e0381c070318480c0d07403006001d542da00041c00d0305000035148100000d0303003840080c00090041c951030f500890081c154815542c5030060180c80c109458120301c00c0380007601c01a1042010901030b042c402c0740200c480d1910541081c0c480ca48100c007080c0c45904000001e40651003d80341c0002c8a64541e402c00028481c2d5030311107001914426007500c120400300343c8600403d503010701c048150380341681260301031f107815101ca0702c400014251602e03069600b5503903400c03660001421205280c059a060088080d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 608784343 1250 608783093 608783101
    0x15020a032c070b0a0e01031d0604150f061202012a0c03120203071106130302060301081c2d11030a080105090108011419020405030d0504090b01091d180312 68
    0x50b007003001591002a00d4542800414411038001511a44104080c6000150502944041800c0358618a5030040d00e00405040c002840200900c0040c485000401030181210904120003111494410790306e80f10149a00c050045d0b100300501d003441d00c2c80752050545803002468610310381030b902004584024030090100200500380c0320341d0710300c1042e0b40042c5007400d1441e164460300c50782200040d0f114220014009891141182d0000080e68014081c66100e40e1074049071a6101050701e04003a00c0381a14410406840c411f05400d10030340105000440e50a85200d86510791480170344a0006102c0c0403003010003007030f2080000c3d050f4030b21141c1d580380d0254503100500c030716148181c2281e41541d052801c90302000d00c1902c0f0f110380007421401300d6002811080f00540090080f070b044254035003d441ca01907042507011002d0301c16600c1d02d00c401c20088404c5001034450911078400e42010448000c4582a000607022160354030513002c500c4812271201807286035040d40c0c40000f9110640d0800e40500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 608785593 1250 608784343 608784431
    0x80c0f060708070305070507020d0602040902040308090f030c0a1a040308030a0218010e0307031e0c0807030b0f13060c18060f2601230d150f0915020a03 67
    0x102d030f00801c550508000c2e0b400c28030b01c014024441d16102174003c0e000003040d0010425240e0455005000206d000c54071961030b0f20b043c4e241075008100941c45010b00d4502c0c1c0c90240707804102201d50001c010420080303203180c01400c0901400503d003411420b0f400344000008980350600861241502010050303851000c81000100a4000e000190401c0b2181c17250746840e0b1000500d40c000c0c0c030341180c40701c01184001c6a081e90f45110351080100b126840380340000f02c0b02c0c000201d50055a03c146c03240e01321a03880d101c2000c403854003100c81007004410f010324807020540c19803185403080c11a20b0282400f1001c50380000a800d03903640443d0000d07200c0c0394001415a440640c600d48005511100a40488d030344507420110101070003800694101c1068001c4880f0710200e001e030030301c10003a00c280e01500241c00c18444501200f0549034040c1e0404032200640c40d12486100c0c1219885040388849c0c0ad03074462000000d40180c803c920070b040c3e5030800240a03020160007000c0e80841000e00440c00540d98201b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 608786843 1250 608785593 608785607
    0x204270c030c05180406080706030914010209150313021905030d030e0703020f1201050702011425030f02071a042a06050a1e0c05071a030103020904080c0f0607 70
    0x8040400d894480b000704520f61000031180a00b0340f0404180e0181d1141d00000e004003110b034050502e502c5542c100003015030300340d0020181240505c0c206500e01c0e00400e803042c240d100e201c1800340d20900c03841d10061500340e40c1010390381051400c81025900b802c2d560200c0e40607100b03401813418641d0304c000200102e107820402d070321500c0500d24091290041c44440d4581d41c5a460100a100e002d00000010558507000d00440030333203120348020300640c10041c401a0080c421100c44800b0304c8001c000140000030400105d0304102c2d80d0001641306c4d0320071001c04800828180b8655411140c0030040107000c0340f080c040707058402e054140350b400300d42407624005042c0050048501400721002d01c0440c07900c6846015107045030854100710340d844da81003104445a1000c132100300442c00f510300c01450416804448808100e2082c070072120482e07202d42403540d40150880b040c41655204000510041c14102c00160b0454130494119013003004c540c25003428000840e54448c500c0c0d102d502044102c0d507000103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 608788093 1250 608786843 608786861
    0x305030a081905091e011e0f022701020d0c05100e010605030a0318090e03030f0601121b080f100605070f080a080a14010e01050915040509070504060f0506070f06020427 74
    0x1008001602d2034030008091f10506c2c2000c45411540e4100d0310036800b20a8040701d91f90003081e9450100d442c031a54044400e20082c0d21028018400c8800d48a950390191900c0c500c00d0740c01038000d0609440100c1340074080e194900c0500b007155203450300019203071400c00c1400f801c1384c46030315030303050708081a0000b03104880140c2c850180e0504040080394480004811681c101d0980440400780b591298016140b10400036202c001803440c1007405103068031881c1902000003d20f5030740303640b1034441340c0200d0114242070340c01c22510400c583c0104220b90054000b003240510070750b407841850429403520001608242141e0003c0307008a020082c076002c2c0f621403580ca42c82c41c00030005d850f504180ea1009454014080c07640580d0290010030300342150250b0503001c0c214010320500a91406003900c0c1d0300c0b50018420f40d03008505084e404210000045c682c40b080e030324007408590134601c0301d882c0c9d81c8448007090001d8640c10741c00c20012444401c6840c80c80c40184140d40806100b02010a0490454101030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 608789343 1250 608788093 608788153
    0x110d0f050f150d050c091e06090609070c020a15051b03040f050f13060b0405130b030d080c3a0209090a2c0607090f0305030a08190509 59
    0x1908000a5807a42d041e22030042c401540c009480c90321034940140b8100741c0040755a801220b54040240d80c0c0700c0948000c11041910790440c4480d200c880500003070030800d964143d1700074000070000300031602c41c8003000e095600062001e88190f9641c44691208803e6070122030007d00c0021300f10354007070442560300c100f107682d4030020762800c0d162060b42100300940b4000c4501c2116a6441480345541e8402040c180c413442c0030040240e0396030b03034803440740661081c030480740a0801c0300b1046003030540380c0c41580c1e45890082d0107411405001501110503450081000641c444207016450821a00140e20080c0703410700c0c1c40902500c9041e4a04140308900b045121500c1e80c01041580140c0d01c4030303c0d07901c0d0840a5040c02060302038081030744d40341c03c601400c0c603c030804240030070103c0e0340000001c0751800307204c047d1202c00c100c80e1144c6485031000241c0c000074110b50310410801c800241f2490141e6841442c8880c1c0c00da100420108080568105590707412166214000290441680108451064000b9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 608790593 1250 608789343 608789371
    0xf060405120d0b040c1110140c1b07080105040b06150a0c05010b13150f060507030503060301200a0215130201111009030801030c0e060d080304030201110d0f05 70
    0x1691019034400c0e40c914100784800d004915409407020682204003c42d10040042c0144010300b80c006003c114903202040d060b00c21007801c0b51600c0d08910880429a1200b0040d165581d01c0c1440350800d64840d81500d600740301001d40888000e075042c080031001e40413520020030141007130b091200b04c00c48081d008a00c2605e00040094506116070b00300c40c006881c40c00e202001c4101410003900600c98004001c1d0407031140010b90458070440d0388462850070031800d00c1800c3c076440d1445041000264018000030031020098400860b0003078016680c4001e0090012800c040c4010042e0020400700c1c0700e00d641e003c0c004c24041e22030b07a0140f10000b4001000d1000c407440d4a01001c001d01200345248010381403042e80300d804002c0050038440c007200c8440144041c020b961407841d000380400b009200503078400102c84008140107415694590040500825192100071a600d40c1003440c0d2001e40700701c040d50340e601007014046844001808100c1c4140070b002840741e42c001e44407415130b1401002501d905d00c1d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 608791843 1250 608790593 608790601
    0x310080c0105040302011803052508070308030118020d090804051f0906110a0b070507050f0a020f0103020c010b130b0109060309020d06020c100204272310120b090f06 73
    0xc80b0056404076a024a046c0c04a8821081761030200c0344140c0002c0d0040c054101c0000301302080100fa042c025154503038148600350381d03600d003507258032381ea0000814505003040104034138030310044141c00524070060014509110881d02da02160404501150808404a0104134074909000f030031401d0000384031030041804100700010802301c0d03180514003c0c407544202c1d072460035000b00800307458664419405000750629020203081500170042c1104d075403040148892a1500104996108503406404000c04007031410056020350000c5400110565a6a0002c4850f945d0000c10f0305012441041c0002c04a9070600010010002c1d41c02903014503041035102c00050701e4000c18a0601d079000000161030b04041e603140c9040130380c0300703032824400b034000306011600506200000c081c07071115070400020039408140da60152085042c2607802004800c05041c00403001c0701c01344e40d2144090305519042501e46410b4040c200794107405503144002c0c07000b002900c120420a0030600c43d06200140701c9860 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 608793093 1250 608791843 608791847
    0xc1606050a1812030513200f030703030906031a1807030f0209030304140f0a15020106471809060a0819020103062c0c041503050405210310080c01 64
    0x72055900f40201640c80c0c1c006602c614548401c2c11642e5031040340c041d0120350900c0c400800701d44000302c452003011100803010301490001030080c222039164072601d10040c5082c8c41a40100110144840c0400f0040a04942640c43c0b94180780826040d80100126084c40500141202c4162003070f48070a43c410088a060399900006543c21510305d164108024000c0001040703042d0b0b017018060380c0106500d076000c106513901c50306000072042290f000b00b102641d2400c051491081c1b400a091092981510243c174144000749d2074101121148040d11484280c20350000455001038044910800c011092117074134900004075580066049800c5181c1e1410300124a40780c8554622442094801440c034101b1a4002c1c1c115000030012042036500b2105007903111002080c142d542c182d078035021040010241c0322280e0648081e5014004c0b200c03405220644181c0003003102030015a014481c404038444411403806c080103c0c0c1030541260368403824002502804580c0325081280213822100d60820700d66 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 608794343 1250 608793093 608793113
    0xa180f0c1404090b060405040203040c03031704211823040b0312031312030b180403020606040225030e0315010b07240e06310b0c1606050a18 62
    0x20394114000540b001d03510001445c18031440e0300c25604903001004001c280070502030078004590003070f00d91003800f544001603011110001c44005000408038840400d1440041501d04406045403c2007600a8140391400da440c1c401503000302140c8403518003d5090b141c40654454942c1000c2e5010320000003580c1c0041d40711003001010100000011001030600e040d0039550012140c2c100401d0084114140d80040240518050007802245003150060000003030091492056401d540640351644459080001079484005801d0040001030303003800320800c0211005d000d852003030701c4100c0c02c0e001300810305050080d1644174802c10150f010041044611076412a211298000b040b0408408500f0124000c0440d032100b00450600d1720341900c070485030004109000b10340c5081c01d07144500c956400c201c481401a04852204595455584002021a031119810210840d03c0d00e003010500c40d0000c102084892040d10030701d031a1024401c0e418182d01c10494049184c494103500300304c194613406540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 608795593 1250 608794343 608794349
    0x3050c0901080603120a0905090c070b071107081b1203040810020d0e0d1805040c05220302090708070806040e150a0209062a0d1d0a180f0c1404 63
    0x4410b0719400181c0c240e41c1031140000300440b071034690381c60f05d028a10050200744507024007406031044001103130340510b8090a4803200c5502c1803400c00e00380d507402c104982000740b0011019591048400200f00303044184400b038001d504000d91201e12a6081040150440c403500c00c0038400d4104010901c09400041001d5140c0719070148050b9440340f0505408000b851039003801040c40c056008450261544100c1100b102c0016403c001e903450f0b151001c120403521000491008203c3c1000100100320920390390300200443d9461015400e0394a4003c00c10f001800c80d6508001000c4030b0420000640000300280c00c480e0a841c20400c1a480322901ca50750302e032028111010381032140014841c05142c0d0115084000041d100c90b440780c62001080703001c401d4030074450405004220700e601210b480020302d030f80b0103078151f61644000c4180c080c2407000040d00d15501074102181420100b000ca4401e100b003140129070b2040090b000a4480e03042d401c03180d22002c006d017004021a98484d000365084203803815 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 608796843 1250 608795593 608795597
    0x151501020d0f1e122009210a050a03080a05010b072003070b0c19030503190912052823130305070302090a0e030d020304061503051c03050c0901 63
    0x4400034400c19240d910103c2e503640500311141510588041d40b01803c041000030000081c0180c00c407000054622941002444010315000d1180d09142e28065102c241c00b803104000e0701d96400b450a40071420111501010384865200c08048001c00d0760104010303501036a036000812042d410300724088185c3c1310f06000600510094504852804100e1250b40c071141da000f422281d01c20340e82c03904a09190000f1407a4402c501581d0990044424902c400f1644a6419034079146540e03220310440c4501d640a80072084602d51b954080300002d540301d10b002041c5070903038541c1911040300480e69401410400300c1c040107070144045117202e03290040303a400b681000c15040c2540d05040d030000d4851a006481e508050740380302c03e03400014800c0100d915030030341e03000380c410414613901c0e00c1e0141c2c29034102c102c964149038010080380304444040c0d0301441d0818801d880104541c0c0c20184050302c00d68040d08140d40c150401d0a08418451441001d10444030b8039080900c1107151041c00b00c602400340c0c014040c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 608798093 1250 608796843 608796857
    0x306041a1f180501050717090928050606040618030b31020d0206030612070b13082407140711010f020d09140316030b060f0a03021e0105090d0302151501020d 69
    0x83d8503c7d24030240e0b5031440014050442d649401c2080c04c0b0901c41c1000001e10350307640da0486800d240c4040c082c0904c5510050842d03444c240ca0710208031502641d00c00c070100051754146010002400700c6540130f0161f0545191900001203c510003000d10364500a03c007142d0540b141410010707225481041c80c0d41d50110350007a100c0e41d506000c10512040d42007040c3c0d66003d01c5202059a10041c4050301c80d10340103d600c82d0542d600c0e00101a90760740180503140311402c812a6520b81660401001c6502142d10b1804010309059035010002942160104445a84032508038940070350340036200801c000980d1008202e064400c00c400340412543c1c0c06526040c0600410824558400300100008041500c5114441c65a2810004501d400542d6807900c6941c40881c200c41c107242c0410b8a906482d001800e111002e00a0008552030400d01d907041414000c06010b0441e003551703990300e610207003400307500600030203002516041ca90f0743c0b000f451140481020010f84182da64001100700b0701c5515410550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 608799343 1250 608798093 608798123
    0x1404020132070b0f1905190203013f1103121605010b060f03010e06010903121d2e030f090311060f09030306041a1f1805010507 56
    0x3100008075125208080c40c1c01c1c41c4203039003103940180110782c01045a02c0154452800c201c104000580c0c00100200e4010042c1c0b4524465601550b000542d055410003051081c01941c3e050b60000d0b800078948103d004507007611801d04206407403018081d407001035545a01c030081d103440c0c12a0181d010b843e01c0040a04205983c90400107038000300c11135800641c8034402c159035034103280c44d101411103041d424445c02148c1400c14400b0340b4001d12241c600d5504680c2401607403404902c000700403904008041c400000481d4804d107044644540740e684140400084100650103820710360030341d40c0203614600c0030020480116611704510401c01e00c42864440d08248110041c0c102c124030f08109a1804c2d4005040503007000700501410800015940c090340d90160410310307a0821501c0003440e070401c2000a500b890030768059104034407181c030744210040c0f0a0021800b41ca024140c0340c3c0000204c0301100071056040f01c003004024070041015035a60341000c000170183d004e14603004040761503a44e02e070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 608800593 1250 608799343 608799377
    0x20610141201180c0b03011406090d020d0825150c051e0a0807080720100f05060f0319020603060406120f060506030a200103090c09050105010f0314040201 68
    0x31440848140700280580c0d001100c400110000c003107011104040310100000f9082e6000003600c0c104c5203400c02c48003075600302506120b0141d102d43d0031240d004802015450050366180742e104a1f182c00f0300038181d110700c3c40d0f503594001862410001da0301c41900c43c080e8800104001220113500a0f43d00d4081607480ca1440d00351003600a0104110081c482002603250400b021005030418a90503590081d05032107544d0161070b020b100750780d030000040035004540e0401c54803800100f80c2c21105c5040714001c0342020800000c0b00c4028a94030307030181d180c0052112700e00d801c20300000c0d203c1044000c1c4c1900d20900d200b04901d440c80f02c00c000e00403071020001403003643c1d45a0088006280c0402200383c0c003450340c902001e078401c044208890451505022408506001a50000309a40035180c06000740b0814020036949401c0300d0064105511801584009064404c404000300b6090b2004962541060005040a07204c030049004040c5000d0b424456004080c05403a0081d0b02800c12260188280f090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 608801843 1250 608800593 608800609
    0x8030d09031403041a01061b02041d1906060501080108150603071a0d050721020f0d1d06010515121f1e09020304050a12020f0d05070b0702061014 64
    0x10340d00a42d9000c4104000d02c503645800d402c08010701701c050743c3d03940c1e00c429007942c00481b4001c0d148540c425002254005040c1030f030025190001255002c2e0300c141903071807103c0c80e001481c4012030790440c0840d880400c000b01c5006010141c402424611081e41c14940c42d40da0314542c1c0f004900c1c16081c100003141e107549041c03052002412221146514400d100c1e102d8442590200f100e08040600c3c007800201110f201e640310f81e40c001003841a1140400e800308020b00690401503000040010412000d08052402e1140c5882c00c482e500c0401311500201d100f942c107181059014078054a280c444240c10f07118200200c03460001c3c482a040500d49840c00510000c0341c000b00c244103071481110700803604181d00806071260b10002001e656402e034945140100343d020984000300541c1c055117840e40023454001c42d000b420490392045405400141070014900882e851400011820000f460030511a024500315809a4180004d03c602e090051180c0304403d0b15109004514209074a05d61895441c010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 608803093 1250 608801843 608801867
    0x509041203140705070308070e06090d0302070e010807030b0f0f060114120c09031209062505010f091104020702030c0906040204030602042606070824060705061f08030d0903 76
    0xc2c0c14246850030038009002640488002c1c1e0102c1c410a0005024030300c11524070303011403006040030342000361003000d01c09881c0e411282101540156030f0b000c101c1c01e40c0d5040650081803420300070f001840c9181881e0000c6900980b80c00d500803540c40800a159500e040940e4100d4420310341540c0b04800e107400f001e81801040b4940d480d107141c031b4040c8122043c0c0480940900a8100d05072110440440300b840041d106070040240c03c01c109008000341141c242c4030400c030320705509810010302c900d81e0703440a0840301107203100400c103075440c002c250606c0f000c80005268600d00b42c07411443c012043e00020b0b07445e0312001c00307680301b01c2d80d9a0000d4420f881e103405441c001c5a201c64250f45032610750f16840404505510740c442c0c40c1c02018042c80d407600d40003c1c024001e111350344034002983c0780c8801703591940d8503070102491043c82e1100c10004a844032401495954062005401c45081100c28040120345100540103818030440040c400d0001c080700702e070f014403040500000c000c403e5141c243d402d01d1b4544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 608804343 1250 608803093 608803121
    0x30c0f140711060706140709030309090c030219084201031104060305060f03070b04060516080c030702010801091a01080910050108060f0714031f0b0d0b09100509041203 74
    0x1c44c581d0108802d0b6044060368010390607102d4015554440225582099440041c0000f5003a040400c0449082c1e0f210600001c082d01c0c0141c600200101801100c81c40d0004c01e500046c000350030040c1c1ca41c140c8400041102a04c00b4800f40400e114080f1350441664095030440c01c0340c0c0d204d15810f141c1c0603070701c21030a4102d1480c2740c5894580d100d401900802003181d032940030b00700740d224592440c49c010a40b28141c0720303404542401c0606024013100e803500300d540f1240c035040000646101003901c0300701500b00c003540340005560318000b41c400109208410380c4140b07001400c1807aa40110241c1001e0201c03640300030b281c00c424035592403400d50318001034941d0300540d4a2502002080c1c1d5440420410712400ea000300075005915150400c60b1007000d003050400c400c41040c4041200351207505644825160704c0100c42c01711944445900c401503024a299100300390317450403c034442d400d100308440d610004215540520901d01400301d0850300c00140000c0480360302040c0081514040e0f401480308003280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 608805593 1250 608804343 608804347
    0x170309070f0803070302010b060c032205040204091b1d01030c05090a0e04050f030909011a0d0c030b040f020702060304060e0f0d03020703080108340b0304050a0201030c0f14071106 79
    0x20b40c9403141c80ea400304c0c109030300550030410508034030b0420382d003180d2444070800c0056240814142c005011041180d031503410b0078540c2d4000003110340e1940090005400b03012070005045207e42000042590040183c1003841140200507025020948491458290a0074003240050b4040c804540310b21980d91810340c0100070b504049072043ca0980081e10440c858800c9549032148031081d1560303805039480855000ca10400140088005125058044400c2c1000321f420176618040c1101070310031144c0072800203035540c0d41200d541e140a006030310012044840461070100e03d600801c005d840b0040c400340000d03803210140c0020400c01c200011001442c00162480240042c0d40180030f54410107050b00060300031000480d0002011803a1280c42100444500b038540005040c0354420f4030f911600785060124160004151440d01d000351b2056110300007408019003148005421144d5401c0f0040c1080585130003094403d0300031056131031182408810607251482443c00003005038040c10120703085800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 608806843 1250 608805593 608805599
    0x130602040f060311070b16030f0911091b09091806090a15020a020a030f20030408120901083705090705060a0c0b0a0605030d020a0309060c170309070f 66
    0x1101e0000140d800715607090200800c0081210114080c50710701801e288044808590341491419402449510b203040205001903481141000c80301030000c00d036500f03080c5405070710203458a002199404084440707600300340240802a01e80c1409248421400f5401810200c0ca4440710403d0301c0c000f07680e002c030407500d1034071f080c0b100103407030f07003000c0d0011560016060f0301742c00002698000da50000701305074000c11007030301207840444954011503140e8050251400c83c1056608100304040200b400300c01c01980c1e55450304841600c1c00d844040081108181440030088aa90124034107811017540e00720740000c0401c104401d246500001e94000c22500030103440410986147c001c54801d80200055444c003a03514414017407240705a441707036000161201100000070b00c2c901e03101c40d0032001e40e00002902c15118004685440103200c555809a4042080c0800301a40510309101819051624609c405000c0d5256407000b00320344a40b4802c94400b1001506200d0100701010042c0b005900078a00c080d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 608808093 1250 608806843 608806859
    0xc1d0d0c03121101020703080a09030e03060c09010e0402070f0f080c030d0e16030b07030e010e060703090b1b0708030403020f070f15050f030103020607082b050609040210030513060204 81
    0x2c081d15001c004600d5034030503800c400310103109568131280c250302d400c606580c400513008010610144201c0c14401c0405680440c0c0c1c0b010001c46100b50301124070035540d031000d02c001400d405844082244a5801004140700003800c1c984130954035a400802e6415420562a2107003039405010701410180c403000c51040030207641ca03044507071061402030507114800301001081e01000752501003e8a85883e00011540851081d44040c0c440c1c94184000030341000d0340f0102c0782c144501903400c0f1002903291104035061000300f0324002c1e0002041c212010300c002e0920342504160150f03400203000900003000144c1410300074000030407001c510385c042d1100591100ca9641c80d049071030050490086034000640c0155000d00222125503141013079541c1141c0c0703945e08112607588040c2e412141d200090200a8584089006054000e140e4040c15250001c0d018003a5003158001003a181c407400261083c00050388412201280591807854003250a680380c8012180008094400038007441c40018001010700c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 608809343 1250 608808093 608808113
    0x106050f0a0b2503030b0a060807200a0507031a0c03010e130f02030a0b010f1a090423071106060405070c150b030307030503040c1406040905060307181505040c1d0d0c03 74
    0x20411241040d07d686c650100700c98198085036480c1c003141c00e00707030142c2000c4107894107100a01030000444078103a41d240e44850411140368011906081034004400700d8003001801c0c0c40e8003000801069007036602d032180290780c1020107800050001ca01d0016601846000c2c83c0c0d05810a402a040300d41c4811285030007242c40c1001d00c164420880c280c2d10110b480d069240005404101340044607044c6910003080000901c60f20403980d180d118405902074101101c2101107201da40191155602e5180540c4d000c0c0c1800307402484a40318030301d080c0030030140c103030090220300141d81c1204013400c0304004003520b0401480000109507140c070001c110003081561000003184114401c1404410565039040078149208a404201e54003590503c8144003403d100d41c0001e5002d08010221030700181da0703d07150b10142c02d000c009180160307186ca12030b60b02d429281682c04004c2c442928108560000f0070001412843c10b60400000301c0540e83c000081c0c2c1c0d89506c24454090340180d003034080c590340e07031600c11600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 608810593 1250 608809343 608809361
    0x906070c0e041109010501020d050c01021213060f0b150c0a050118140c01020606060a0318200a0e01090e010b06031509010b03060907050c0f0a12020106050f0a0b250303 74
    0x26584041d6001c203d0306051141078100d69042c1c0052a06110410b0b0a444503040410000c83c0b6660a203c2030510341007110031030340924803642c0c0d50015660300b814500150b41114800c40811410800001c8040d203c030030f100c04018150b920100c1d2104842c0c2c40c0c1c0c600b0a0b045600c00b503c0d80d8200800381a0580b11502c4039403085106806407131b801803140b032481d03880e04111501135016801c5040010054241140100401456032500103402c0c401416510f00e03100e50007005035031010000240700fa4048d0103002c40c6e80001c00407580f80084034035200043c90790980501601142c0d41d210000689440d409420030117196400a10880e1203140030048030502c540c1000c3c1448c810f00301c0d03130700008044010034100c0b4001c04010340201030341c2e5030710074055460b0380c0621000300c1ca41c42121003806140f40240190ba801c9d0b40b0030107480c10030310310903a002401d41e5400d4000030f200b00c060251031740840e6204031001c0212106003c030643c0f164111030009084e100315402c0501c10711040d42c41c2908040d4194004410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 608811843 1250 608810593 608810603
    0xe04030c051b0a1a0403030c0f0b1f080606090a110906030a050f060604060f030504030e090a1d030412060f1d0309090f070c06200d023c0906070c0e04 66
    0x802a502d000d000459134241d1001003540c40c1c00c00003400440d100302601e108180c050982c00d104030075240d07104805500215030342c000c201e5041044016158110103490010060300c4001c056038100240060b8840c0c00251103000000d0740d4020200703171070040c0c10598005090003000d5070b03224500301c00703003001030002180c0505444429000052040c5001410f61307060f66155541c082d01c18112110035001400301601c00e4060101079560000f4517581e10388014880c80c5000801b1078450b81ca1190060007040168441d90150001e000a12401004034288a10907070445000300d140c2824000d460000d15265070603113121301c0345905125803640000003e040c110001c0e0350b0385ca000e541c2c00b9603c6142c2e24059880900042c3e0204945000c685a43c00c80c011801a40280381c00200d8a9412981a80c0c0700200607207046802140c5041c04903030b101000104200400c031041c00c108450a1010741940814007881600c5001180850454550106980312940d210359610903203034035500c103c002c00a0890f002c4070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 608812949 1106 608811843 608811859
    0x30406052206020703030f0506010f030f0e0601030f0507051c0b04020f1306060810050102071e052106100312030e0a0515041202070f0e04030c051b 65
    0x1001500c82e060050f40c80107079240280507900d079000b40003003440c94503080001d166000031b450020f002c0c1e10f12303000480028040200d0300a2030341c2c0b0a00503c81c421000080100300075241c07110701c001e0060b0200c50f10250f0b20704c2005501200c001c0c60380040b0078100302910020f6042c0001e5030700203100404140407a0040c0c0040b07158200c1614409a180f510341d4410409150440100d41d08403811880d12002c241c10040007035030b246d07103078800c03541c1142c007010341841c45113102107258000d00001490382000c0e003142c503101c0000080101e000c114900542020134076480c003254048003120b503c48030b054540d0b0580790041e8020484a800c0c00d00901846200f940014018801d070046052070555601c0710b4201420004483c2d54040c0008065610903841445400c000d1013650040340d1200200014070390703891504a4501100070001847c521076440e0500c03c61291600c1c440c540702d41a50911 = true := by decide +kernel

theorem cover : BRFrame.Cov 608633093 608812949 := by
  have h0 := BRFrame.cov_init 608633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 608633093 ≤ n) (h2 : n < 608812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
