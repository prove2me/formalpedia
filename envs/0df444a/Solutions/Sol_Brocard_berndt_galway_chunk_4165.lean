-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:34.009643+00:00
-- url     : https://prove2.me/submissions/ee52b4c4-7ff9-48cd-a781-71d7ac68a885

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 748920863 ≤ n < 749100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 748922113 1250 748920863 748920901
    0x1710020c0622110f043803012c1603030e0f061c0903030b040f0204150509090408030709240206010f080c040908220311040915090501060e1e 62
    0x99645002805542d06060300c00880d030071300241000032a4040351081d01c40140d4148185414202c0340f00f00c0c1903000d580b0200c02c91403900e09030024020341410414044c000345003035140b10002030f0f030b401c0a0a0b002e0010005000741ca81440c0d10f811045850382401042c5d450180348160149a181c1d007014900d040401c1240c00d4800498200444280d99100303441c05001e1112051301015260a01000300c0d5455214003459031103681c1e401a43e85241100f080750700405802c11009001041c04030004a444154145e9441940010300507505e80d6490001d0765401070035044080d00702c5c200080c0d9105c000c0c40c503d41c103801b80559002c0320b0f076503a42c1d407007000c8034004180aa9100c9400c44401e4201506258221443c8544140c610500b055189032803084120500c00940a0605a0304410014401030002d41400c420050f18140510815a160745100e244401209a0b4040c0d8482080d41800030a5104c2c002800c81c840c18800d1074100074011010119030324211052917240c180c0072800d01040b00c4812018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 748923363 1250 748922113 748922123
    0x81e100f0e070e1003090507090b0f1f080405011401090e06060a150c060b060723010c0e2b03080106030c030e070b03041e0309090f090b011710020c0622 67
    0xa00010300c001d01c007544200c40844c00504d40c6424100001803014001000640700d080c0e00055140007c0e810090005007204049000302d503805494804501000a01002e02ca15803c22180c1902d4901e041801040090449044413024400124079012207420000e04003d60404441c41502d82800f040090341c0c0078400d43c410700440c030014031036081c018683d125545010f000000b84403503280d0041442d582c00440c0417161040d032200480c039100541c94403101c2011a10008011701149041c01a20f0400800302151044030100307002600b1239207114040c40004407030800300c40100b03100d14000d460740f0710030f005030008a0709080c2d103e21030701c1c42803080b0081e1803203034001030801c141760034100c0ca080d40c40500103460400214252402d04d010840074180c1c1e1030300c25540c55803d0384c40e220310300c0111100e001030250070034108805030021a11150406041d40c8501c01d0407100419040360300384c03404281c81c00c4824880e0012948058140010407041c2c8500ba1024804804146110400502210049000304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 748924613 1250 748923363 748923377
    0x31510020d0807031505091305010e0d0822020409050a02040c0e0d060f020c0d0c0b01060504080307020906030f0d020c09060103061d0402040f0612060608060c0703081e100f0e07 78
    0x2010fa44641c10000c0e102d04500803105e409a1145c021620303c3c1001c40e4200060b4064408040c1004000d00c80d4014005010000e00408130120303c0051070403074040c180c0c0480504e0034100408021310700000480130f6034001e02c1000581c01d075103000381e06d0348420f00060384600d10301640c048072940070303003c0401040002849082203943d50717564500188464010300000c81d034240442c0316000b208108101b00414161107403402074030203141050301c900c0b05030042020440244003c2056401c00000e640740958111064115070383c134140400c0ca0150515403248041c45003000d198100e0f900840c205103200c80544a1900642c0e600c001501610a54030071102c00a0480d5550428107013040c60b41e40d00b1038030081020405541d4a05008152011a000117014819641211080000070f1003508000c20084010344241d10303098006030307418041e4010103024854040d000503200d01d690422403610407070034602018581045900d44d010340b001c5001c0c40082d9400c070b01012881e0108840901d1041c90150380300300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 748925863 1250 748924613 748924621
    0x102060106050a031503020901080703050705030c0607030e03100f090b010e060901060c080c0601060503011e0542120c090a15031401140112060e0406050408070602031510020d08 78
    0xc00500944441540200c00110040010395507231009500a040b1440104681801c5060503820309076503a0215110740c3c0114110046600c0700420790f10040e805080c003a080d1112840440e06088550000285142c5408042502142142c0c440321420b40240e00c1460280e803128007103060840c041d502d0070b41c840803080c0104031a6205545404916119010b5130342401107004000745001400c0e00440007086021006115000446000e4510325501c418040c2000340b40401146405400701741805484038620b50000340003035414402881480004041b40c24034044403101c007001c2c0c1110603100c2d8039540070004580c0800f0a081980c5c40444020081e01900d4a0180b2014040314001d51020a068480340032100341e2182d00203540c02845510548000740300e0450004202c0040d018030703007031200d240000c240f20811014242c10b911a07030040f4002480e45507410601c82c14080c81d6030042c01d05c1d0001040106c4c85000c03100b181d682401c00c0c0e400941e481d261003030070398841070100c0740d540000314504c00107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 748927113 1250 748925863 748925867
    0x7020f010e010b300607200606010f140f220611030d0c120f060303090b07170703050712020a020a0e01050609040906150605120705030106021e33060102060106050a 72
    0x1002c604c07594081c260b94140c1000d11076609005045401c8030108400e800d2290b100c410001544844105c5840908224681400083c7c0304403080d140c3c0d10100701008141401800100c030807601e1000140d241c0c00e03110440d810304010f401d10414000840d5095007407000500a000d1480a80181d801c0d03c0914202149072061100400216844404100c560304029a00030000e100320010420012000318019056080181038580190b20241e2925802c00000b00812442d40d400201c400c4e040000a43c0c9a40c82e00303007142d941c0648007000c0c0c4031001c500c0d01d48182d9a000904801c005100b56081b10140d55954090684c41c0424440d45801c02c40c00c00041da890301d000d80c8500e00c1c0d244900c20000e0851927100c25046c5d00380003a0005ca022800000b108286031542c0c0d81415130140c06840e04510315070400900945408129010518500d9005555011408140074400c620354000c00355080d00100840014140e88800510010074012500420034551010132024140c0301e882d1038480c6021344440301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 748928363 1250 748927113 748927159
    0x3030219020f370b160f0803010e150102030a0504062f0d02060901090b040602130306020309070501120504110114120a06060e0a0b090f040b1512100302031203091507020f010e010b 79
    0x41202c503110101c0304500047e503080007a602070b00761482e500b4030a03d07108000c1c400c4090710261140c155401809244581540030048071706031031031071408510050f60b42d0203080e000a416011890001c01c040e9050100e000b00141d0302c000440340c0d50031200e80340c0712a040c00d0300321014100007030203040e40c0b2070018020500300e40041c502070180000c2d10040990701d484440c204e0300241d81a41f075503000724074100002c0d0b9124008003c240b01f03008040100d0b007441d549010f0050070042c1c03c14144850b110084c07000000c03d00030745010592080c01a0800d1a0448040300140000d00031034010440c2c00c0150300c074070300b032908040090703401511450340f500200300100102403040b01e07000e0b80c0c81501c1d0f02c607615440d11416080c51104120a0307a041c1c0b03c0480b11100030225000929003400090300f06010805030354002642903d40410001941d0343c0d8961011080c185420002016620b540c2c0c041441503e60303000540c8148006001c000f008020b01e504040c0c0d007640c990728401c0d540480070782c60b4030412045c8446 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 748929613 1250 748928363 748928407
    0x40903023403142109040b042708070b090606130c0207140406080f0607110a0507060318020d0b06100314040204020a05120403030b0a06030603030219020f370b 70
    0xc40d13540c2c2484078118507100880c03114103030840740d000c5940c1c222820701c0e0151040000e021207041c01803d5108141c00f014245c6101c510002c1ea43c01041c0e8814400c100c3c04a91070b460b00300151904a1801072002d9a07510015a100790040b103041c0300c20064105070b40b1940c40245140e5026000c07491800c81d041103045902101203900607a41c1d8130001d982501000114000c0302010b018000741e107827004001e400312454141c09080740d0881c01e0030500003400490700d1400d0701c859080015164203540540500c8070344491340290441c0240e2000c0d000d02114002d01c500c64003085915983e864034040084080d03800241000c800b15851001040040c6429005062060742c40e240c028140681c601041f2485c0901740d03019030120355204110780144c100384083c10041e00741401d0910040d49175580c000c0d035178500304448280407080000c0c4001113588000c7c400750369140c0182001401e185900d501074082140c3d040c0c001800380c0d80c4202e4a02e1b203051b14a9401190681c82c8080d0610200c038144080c4004402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 748930863 1250 748929613 748929653
    0x1060f080f07031a041a03121201030303021e03090a1101030e07062601180b010509060f0309010b04020d02090315100b030c0903060a0b010815131505040903023403 72
    0x9042c0c1a0541780c2d40725840303440b078181c0e03c603145820304541032504080b00a1103001080b00c0802a84001071485420703203045a505250041c0c0e5110300404459441e40c0300c00d21184030715000010301088c10000180790012600810314145102c3c07200d401541240c00c1074030f02e11a00c0e005550304025442c000d105005140d46070799041c040e6031119902109074202c098202503800b8584000000801c40c89201e000d034000003c1c00d03ca49070064000000c1d01600030b290081940e250000b001405d102d00030342081c402014007410a40d11890718035415400394002d03402d01c41c0039114144219058403840785000340140c0d50541c1d01c280240c241600c000c03045c3d000034003010b0364000410008072981c40c10042280300c0d40c00d60a002440d0501c007400100030407406002c0c40800c0203292403101c690341c1c42241203014114110780010700300080d0a90351003042e0482e0b018903440791802510f0000d154001c03d4089070648114044283d02c03049140020129010340038952001207074603c140005a800781d06420740034005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 748932113 1250 748930863 748930901
    0x1e0c0f0b010306140f01030c05040f021b0309131a100c120507060e0f0c01053604110304051002090a05060a0207140f1315120b01060f080f0703 63
    0x2a15680c8080c0001e034011640e0a90f0752803070b442d00031a00d10354550044008041020305501d140c94011b00756032a8011144119500d80e900390f91807041d50f044400990032402d10500d01d040302c5c07041c9501c91304240340040c01600f0041d45882119030038401c0b00c486030b544106408030000e48200f803291049455105406206001c5c4804000c0755000e440d4648598080d61229600c40f1545018002d42c1c10514101d04190701c01510b122002d4008903042180e80d8080c40c0c541e4880200b169801070400340e4120300c00d580c3c004040d0b040c0030b018480440c005074440a881c10b0003154241d005800e0f152000f1100170703003181c00c00c1a0151078008290000d11040200420800d10f20303407108009207045c1e0040c0d1080000d0791002e00e04108003d1800b0320b038203244408907010346091030541c02207a01c01d42d038404481201c2d981d800300301c0c0d881d00303401210b031018107407240840100c2c00043c50040d13240c10b42030041348007040d1a5400c10003414483c43d800d5210b0300d014400e885198a6041081d4041c182d4030100080040d01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 748933363 1250 748932113 748932143
    0x20105160f02120102071704031a070513090e0c010e060d02090627010f03482105130615030501111e07020d03080a15150f1e0c 56
    0x41040c3c0c1e55030311545000050345c0301c001d85040d00714070000c00da41d81440881480100301103105007100d854a2241c2c100c1c40c61080d50352940499040c810326000520100c40c0103c0030400349031a5203e0442401041c0072a10b800042c2001558520a401c4819a01050400c040c8591401a401600401401070225820032003481e202100c001c1c01e0300c0c0400080c0c12512902c080c290b0b8005081c0000c80e549007010001400b0b091000b03c0d0481d20a4040c005a00e600080703801d0851890032201d01945800081a084c003403010002400ca0f1400d8a00d120004010300048254655910826024141403551012512125030303a0f48050800319212450510704001d0002c0461001c0c0100a01d03000f1041e000d0f0347d40c0880b418864001981060403007000e030030900c01c4900584030745503810040d54242c20b22b0340c3c8a40d55611408042c201c1d052815605d41a0311400140c00042110341d903503000d0b400d0301d404000d5240176108a4012061100c5040010303407032051150324a005134203040c3e0081c01100342110140c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 748934613 1250 748933363 748933369
    0x1707024c0612060f180503090d0515010602070501201009060207020d1b0e040b060d02151201090c030b030d030e0c0603040b0a0e0f0c01200f0c01120207020105160f02 73
    0x68000400d0b29040e40b20000d8244c0f510300c0e44a696000c00000c40f8080f503041070340e2135441d528001d0303903070381d078058010001002c040c0241004400122800d503140040070b076031500c7d002074503541c0303921842d4040340c6400308040303549080255000c42c40ba502030041880030164007520010708040721003998810ba0800c030f200c0240c0c07105039100c00b00700d003d6420034600180c04030355480b6865860784070040c00004881030100040215030760f00c0d007210003100c41201c2e2051600008107200400c030b90b00305039090f0008000c20061681c4403524125142c201c0c08122501d5603c0e003e40c151018802c510380c0c95000700000f851058001e5100600e00b407401e81c00c451030707911724001041c0da640c4180c13401d44402e4082d80810005812600942699140202c0903219030f502015100c2d40e180b0303141e41074506114644030002c400a43c15402c0c03010007800d06085841001d50901700c43e49964020418500203000a2201001c0c4080c50085489881c0d06a40740340c40c0c01000045d50a111154440448680da068900034001d03070303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 748935863 1250 748934613 748934639
    0x90306020c0c030d030b010530010e07091a07240f0902040b040605150a0201020910121a0607110402070204060e160c0807080702011707024c06 63
    0x8207002004021a8007004101860229110061002c050410500b25203d0364021f050310140c400741e00f01d43d60181c218022005503211010281c00c0c080039000f00000d110741400350348501481c40d42d21100500c0381c5550b168500c100707801d8036541051000300002000501c900841c0100b002408100781d50451611201c030307041d00d01c000c1c80042186e40b1001d03010154600f500c5594160f1900725420000145400d010a0b040341c01421000816600840c0000301d107030003901140e078139040080554000010a0328081c007181e42040384200403e150440300c103041da00c0300161301c03841d09004140ba07042c00c5950b682c0c448091142e50150b90401d40034081640180c9407409550081e02c080340c9030031b6283c58840b030481d05080b401c07580042000180c02034075010079440012607c2664020803079554408041c00160b4203484400701501d402c01c804c03010065401c1d03011030329050f50700719070b03801080b1443d000c100041c07110344204007070b0910f0032810075030440300c65003074580130342d25550550101d4144c4d4bc401d01d204140f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 748937113 1250 748935863 748935877
    0x70302011d03040503012a1404270b0103050103030e060a02250806070f0509330414030318011b050303040809010801050d0506012904080109170c06060904020109030602 74
    0x42d0348049400d00440c0b4083c0600901d80071440182c40103540810103583c601d00540400c1002c0c0b00301c0e19030010010a03e0b504880103003511158240c0002410180550300d00203500310301110307500e000e118060f1581709004503412280c0540d40d60b84d140c07201e40f080180c00d601c074803c3e403429446107403a180b4140065920003486403209a03900800d06251410385070034501c0c020130103401c00c9085014401d500b03402c070b400d070350b9507501c1510900d4607440c0d40000a01c0c003120040d4240e80241200f40450410103142c00280140d030303000c268044074801684245540ca004c1c1c2c440f80001801046008241c65101d81ca940c81010348070304e1080e4074403042da12601c2c210790094406032180c041c0059442d1a558004c1003290051109039500c10480017541c0340c1580b510018080c1212851810a1007102648050185544980f07030b20300c03041c6d549079160211070080c03000071001c403210707040440080c1118060a068680d454032160181c4215520301041115160004000b02d0501c041070030301001144061006c1c005ea = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 748938363 1250 748937113 748937171
    0x30e1002160b4b0a02040b07110a0b041404050405011b0509090105060307020a170f0d06030b06060702030703030c0213050a0c140f0a180504021207080f04030c030507030201 76
    0x3e0780a4200154002410407000818006005011151040700d400d07021001c40002001c1001d16114032029002a11460740982c211080224860302400380c0300040403070304c41c4220307540d404240d5103520440a60089120b0b5503100100200d0000050800741c0000d41d002d44103200004050032580b1070482d9412060b0640700002e440450303440030b0750030048203c50152004480711411450000402036480c14107103402031250400d00c441c50540c002c85000e1f180162070996040d80c42c0d00b000c03050103004290a21050755084490400704005080c054100e07007441c0e0b00a400741130b403142076440036a00c800ea1148201c0e0091381c0c00184114080441c0f00d4240124130a1001140003143c551000742101e0207202c038900111820403008402141d560b044418038481c80c10b10201807203424018580f410301a03489203411a00000720751500c20318070036445120b0151a100c044c016110b4556002c0f0084003120300078003040303104e00d4120201340180041c3c015907120b03100204895155000c050900105e450340303011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 748939613 1250 748938363 748938391
    0xa170903180a2c100b03060609030a0b011701050c040f060815040f0b010e0315060d020121020415020f0718020c070e060102010c03021204080304170c030a0906030e1002160b 76
    0xb107441900740f080d541040015540040709814140c0110132880054456880782000003070014040d2000d107d034080c0641c000a00915540e910903500c01c00c80d241981000c60b035482e00000131103148010041d50103030340300c0c41010300c1c50078186001641d2800300a80500c2000400c07410040250340c55010b00c0b030710005480c20101c0c10002e054000b51070707104460354036407207904114018546802038880055100e01c040751402c150710f90500058a148844e102c441c95808030029420401400c540c006000303d5181c080002c80000d4031401c02ca80701c0259a44902e0141c000040400c40f0003050700d02240d03210040d40c0018503100005d0344440c5400c109900650b901d641d07050800103103603028440d44d0041507041c2020351404c508081141200340000308010f001c0100807000c10140300c41c4441c0d12400620840440d07030340d4441c00580a03900c4c0c11140c6000002100180c002c1003961003070240c0da041c000e0313650007051420040d845c15006900028210880c0d4024942c09038003103003c0180746800783c14000c0e6041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 748940863 1250 748939613 748939679
    0x112b08090901050108041104020d18050a020108010e071202130b0703021f022503021e010b190305060a0509030f070804030209061203040b090a09110a170903180a 71
    0x2020780016401181440091006c00012541c03524060000900840740180d5507048240f0b0312004000405035440d0300f002c44681c03102040340006510503114000d803111405070f031769030a01007144c400844071070b0300288402040900c407200d1a0007400582000010710500151140003800b903d80041038140d006a03c200248004403e03880200811500b0380203056180030304042c0740710500780b0107505c2040d02c0700b100143d0700309051080c40003106031f81220540c601040a60b200d0346000c1c1c0a13401016104000510b89032000d07401c3c190800d4201e039400303c0a06a20394400904000402008100050900040140e0300e60498940b0040c01543d00c10421070340ca50381180144500c2c0207009200740d00620117100d48100a802c0042520201d8003000c401c5c655460301c910210b0740b00c8010354070801c2642d0620025501050655002e40340e40c0006555240a1501110500f03610020a50320b440e0960810804a01c10344240c62016003201d8000e801510515907507400c890103a0904d03480d40b1407503691a0088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 748942113 1250 748940863 748940869
    0x11805160b0c0d14251a06010801140f03010f0608011104050607081b0a080702041b0801060e040204030c12050f0d02030f0c0a0f082203112b0809 64
    0x142030941c000508011441030500e543d03403800d00d000d01c180662400c0c503038000c01c540700881e403502c1003840e0502548558000d2080c050890f054003110344100781501c20b0858030700b40032000e1040c04142c3d00c0003c40d074608140c04032000400c1e0312040d000400340352804840e8900340642c0d0300e080e026403400a00103160820003400c6030725140c2d120800c48402c1004102c90380d035030026100038580009519030359007040c8601500148013001042824000c0c01002000e00014401408045001362014014a01d034500b03507500c440351400710400400c0d280f2006204162140092007062800a0001468262292111002d6109941c40440b02c0005e0804c031000f003000912a00d011221814000d11900602c0c0c0800b94a074007074400e44001c80100803e2110905e4810031401131080d0b0001445166180141045030095000490300380c203c884c60381c000c2485c40c051801c0002100c2d0007088160b91020340404210075070300606200c1c58502044500d07500361519503040d6a081c1031195801d107070b6850848040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 748943363 1250 748942113 748942153
    0x4140c03061c050703141c02010515040b13020a0e040e280b06010c020a03020d030c170909010b030604141003050d03020405091303090816180c020a0b0702011805 71
    0x1400b403107400c42e204000c00104001105015607600c090394901c030b900584044c500d02034140c52061410040141d142c40d6858066019502404e404500c401000e20038106000c00d4a41880c51541c0000410300398544040e960ba0180c110060b543c0b81080d8040002000507040c1c460001c0b0901c0342d908464442c91501c01201d170a080804400e122103003c220150315200b120160050003d0f050040d402040400c554035129010003959004004110b50000340c2401030020b8032140f0100c3d0501040385001c0900e0800d5401d07100040c00003030110413560300300518209180c1000c0d00c0b01d508a40c540465000100e54a000d09104404804c103107101a407070350820500d880560748003001410300c100824420342d25034240003a406060100c804524046600c2c0890700a000c0e54480f5080c0d01070303c040d50f1400c000550495003110341900d5240b100c01c002ca10301d8802c4a9084150300d015038482c030b070380100080120400c26401240c1e4000020340c44210303040c0524103c965081100c154010502c080410b04090b09 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 748944613 1250 748943363 748943389
    0x13060b070b15040513030c020a0b0f09010206090c0a03030c02060f0f031506031006110a171c05090a030c111327030f11010b100504080706050f031504140c0306 70
    0xf030207001e1410a0300c000180385032495806810058102c51880540d02e800c1441c01c010200d400f4095903582080a4503162500304402c01030050044002003003111200141402d44207500402d49492940b8658003a182203000b00350807038000d00d00b804000c0b109031b4160043c000800c02c5882c00740d40d03460305644030b02c22035600711011403041d07006005015119100009a038155000b50510fa0400041c22220a1404129038030003441c90b2072601080750710580ea5005405264100302d00c80d0340d040100802030040d07440854a081d01548018262004030b031107072071280c9905001340001013401840d400400e0f0103d806d881c46880240e2038101d0b0218000740c40a10350000070000248990542882c0d400a01c8204009881020041202d1140388411429804060040401020711801550743c5001030516003040c460104e050141034000280d0368041c4040302c8480807100c0f4080c0c9141c3e20460340322408a42c81c0145038010303031b903140c494800207010301225004900d4144010380b6481e1400c1080307174032480c0f54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 748945863 1250 748944613 748944619
    0xc0a230c0d14120601020309130c1b110d080d05010801061a0702010f081005031516021908070c08060a06050a0f0810020d0b09010e0406060b1813060b070b15 69
    0x1c001c00c0d4410040c0c2e41601c880380005400409180c850f4030040303285004d1888031550004502c145261000d01c50352100301104003a880d50806c8100002c00720a1901140c040948420200603004035545800307825030340e51610917482c040c100144100760100f2294241c01c50400c0340c0d90703403109002241d6140390600c40c40ba0313542012460f2944680c0024071685e640c1101c041032003001c070041002008034083c2000a03000240032900b58007031a0103001d2030341c0000c0d1050740c1641c2d41941d03140e0450780f000c50b00d5a41050400e20b81010100c00e9900c414070b41d84082d40644103214040c101050748a170074818107000d502500000714540c2d0400301004424182c40d031055180c2c1c800d1001c20001108080b03010080720180400058032076a0344801c0c1c04c09400303d00e00440d4090f940b8030000c0fa0301141c103440d4030b00490082008201068232507104141c0f0748260075030032880d401281c014458507e4081441c003108080e200c2c0103d081541c0f4450000b194002d454110b861289503020446150360404082e1041d003021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 748947113 1250 748945863 748945877
    0xd0b01030b0a050d1704080a0305071b05030714190611011104050312030402040f020307050a0f080403090527091509010603110d080717030a1d060c0a230c0d 69
    0x8800a101110780c41e000034001c002124450f01308501d17190640d8002c019101c19a03e503071409180050007070b40032001c03c980c88422024080d10b0b0011040700759040e250041c00070515a81007107500e00c2e0384044c20000d99070000421111528680c1c40021040040015844800310003120550142c02d540640e04040f95100080c0070420983d580060003140315584240300703d40e203889074008034000c0c015960440360420700000901540b194410001d10001070355644014212400701400c440c43c140982d409000690404028421840c01014030350104415007841254080c4d15103640240c0c1008481601190f00540e60000d0302c5007001900d994440a518000c2040d6401c6580b00c03040cad0240b220880d070280f019040444104500d44084415040c0c00004c04c1c81c507100b030f0800024403a8000c071210900c990800415601c0124142070300c0c41d10800c80b80180070b055844c141c8408039074101400c11010000d50042114011420701c0c854001c50840c4007507682e99244200140780b804001031103c100308149 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 748948363 1250 748947113 748947119
    0x50111041409181e0a1707150908070b070e0a0608010504270f02030f01060e01051807080415060308040b0a02010b090106020a021c06140f06030c01050d050c0f0d0b01030b0a 76
    0x2c102c00c2d0092004481340311407802444240d40c40e021940300e004050b5064640044800b484503030261142507c6801d0460580d420320b806081500c500c910001d01d00c0e1018000c0340000b98040f240d0a03809006860243c90300501000040d4002c04260b100f400400e4106005100504040c000d01d0022540c08120040c00400302c10810601e22580d0b00191545128071400f404550b028001c02507000c003c5c400034001240c07950b092426200c3c00307215452203861140602070012141e4038105114450640700d00b2081d907950b8640035804270348002002042655045c0100000c2e220340054005481c03940211521170542e50b101a003194040f82240d4400c40d5084010441145d0002d000c401315030b419030300720400b1141102070982540c80c4c03520003440d80c0d0410300d01c41c0d6440f410700d01b0766118509403125203180d52120000e00d9140c0c0c1f040c810107800240b08008402e4445580d27004290446480700643c6e03e02507441140450702e40082100d0354107180c460030b14094540c2c5c90300070809030850031122400900d203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748949613 1250 748948363 748948411
    0x2010b060a021f0228031b052a010e030d0c02010605030d03020d2705010c140405300f010e06010f23060d09032a030c050111041409 58
    0x20741c2c50500120710748032403810007401c10a40c06481300d2004041080008040f0b001400e42d040c00a02c20303400010346045855000b02d00c0726601f000a05042d51140b500d40b10540100118500744203c40130000f201c60303040c3c015845401d104035650210003002541c2ca40074104e581c00d05550b01c05010301d0440e0304000083c0300743d550101e1014828034407801d0050342c030598900024090310300e2040010211002e8903014440710b4410048604d62481040200f0800e00f2900b030a0341c0801003032118400c100d106200034040d40c1003a039085115071841101c0071100300b00c01c002040e108000c190383c8080a40041d160310390783e008240940c141141c4070070064002c2d9030520741c040c1c0c854480b904c11140310750841203540440460303807207641d220000050a0302e0755500d48641c814001e0803034400220002864022080c603c201002031442c00c010703c86040e1401070030107450456081003102415940755513162340a01c02d02440c00c1c01800240300c3d00c410003480495503810044015030082c450b96003a1842c41844211407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 748950863 1250 748949613 748949623
    0x80f0615091515040303030e0a17131a07020310200c12070309031a0c090402250c08070e0c090906031e07440c0402040306021e0f03041101121a0102010b060a02 70
    0xa11541c056440e00310180d002f0016401e240d06c00841d00c4580b46007401111441c5008240081c000c0d021549038140e40c0c032002003107800350100250110640065010801c42610091170200c401e04c00312100c54805401a6000754890202103001c500805810405c01401c402c0e1903c464213100c0400c181450114110051032003100601f500c81d540c0095201c1c02c0301c0c2d8070541160301074010a854400d01030030f440c0c8140710036601c0c090000288550312000401802c4080003620070a05000c03518107040341c00003070110403100948000d6160051100b04210b1f100d02917200291503000200901c0d916140410201c028155034205a409540c40513045105148600c07865034482a082e941c4000880105007107030409002111031a40540009000402e11000d1707000b0b401500110b500c0048102c01c2540001c074075100300310b0400311607a014000100826010008201c5070001818805080d1021015072007c5801d44161298529203010700303030040c1d59092180d10040002601e0745444c01024100182d030754 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 748952113 1250 748950863 748950893
    0x170f0304140f0a0f0e1008031b0c12070b18130603060507030603021f120906090c0602060906040b13020a1e0b040b09040e01020d0e0601080f0615091515040303030e0a 73
    0x500840c40200b00d01c041c544012000501c101c500741d9071507402c2701c1190a0385020004045600c4d1003502100b040e00d16011808078610002c200c01440b8903860b010710344030b0030740001d09000c1040b203a0051407070180e1140304504040d842652400100d01c0c0c11490f04c84211840035140c0c0c400c06107451000c0c4016100c01c480c101c4501c08105164101c0d40c03800c03000f02c40300703403600c43c1c40c16406040019001c00c102950b0040031429100d40d0000c8070481e151035049956001c00c40b1031413a00e0340441c001c98045464112105d420110f0103019007610019900411101086540300f00c25684aa004040c541c4500c000240098007840301c00302e207001d19042c0c400685008a85c001c40c0314696400d44610fa02d802541110030402a0000034003104800f80e417001d0f1191406d1040394074500900c200d0030058400422000d10942025007078502e1000c029040c4060114010320464016070700070030001d025a208000350710103000b00c0100c1580ca03401c5240050035502000141110350740036220329800640d90080c1039000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 748953363 1250 748952113 748952129
    0x90303060109120609050d030207210f0f020a08031e06031f0f0b090103080318060c0a0f1106010e0121020f0103111b030405010e01020a020901170f0304140f0a0f 71
    0x900f01a9052041c014207031503000401da44909542c1c00d0040307070140c01034081d6034010185c1201e9058050110510041c440d0080000621f043e160004840d00400204482c0c4e20a44101c94403001d40703642c0c0c0d00e41d5501c20744003804180001c0388405201c0e282d07503803c9940060294041c00054903e103500c02d10100000004046035600c4014443c480403d030342c800030840000070078482055a480c101088140c0c000e442d1980e0801c00184516084480018111f018040707512210740340009405003201c600080101c110208804540c030508805410801103001e805c038800e151140707515112000c00c1c1101d0414034060808140031100003d1307501c040041894000a08021840c0881c4c20403416207845510703044002d44807442254a14030034000080c2c01610000e0700c40c104090080c0e8016640e034074160000070340c00b072500c2c80141301d0b0390b4408000306003103410207080b2066020340000190442d000740e040580490801d051502e420310303100c4000101110700340d4895003842c2c18804d400c0382c030408a001c1c100c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 748954613 1250 748953363 748953389
    0x316031e020c0c031f0c0c0b06090a0f050f0a05090a020a0315090804060915080f13051c170609010b1603020a06020408030318010c1d0301060807150206090303060109 73
    0x40d078442800300f0542000e004044d9030380081c045400c0d404d9806584030344107181d490015900b05083c0111102e0035400e0300003110070010381d40c0c9010003a03480c20040c100f0310300c0f039280c000c550f41020701ea004850240e03040022603039507481e014a40e6022504020035092241c1c1c00a1445030242e100c0c03048800a80307030000f01d95140d554111120902030005580c00421008000400142c0c02c2d0b403011a90301610940c00e030391100701c54100c604807040706080e03400072510880307400803645020a04900001c62071145042c0c84284603440c10000242c10549498004207206591324a00b4002814a1a901500c2140e8020a5505109540c003003801405d066500d8103402e00055030601d070003000f001c01d1080c1d01c80425595035450300551500d030381050f1042045014000c00440101c9418001c00f03146070341956440360302c240c00c0000b40c0d1080700380f02240768142d569107001150070002403141c04040c2a1131452401083c1e84004000c2c036003407004065103510b0f042402848101ea070301c108400300b00c8503031032013a113 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 748955863 1250 748954613 748954627
    0x312070b0a0e0706170601030507051204020117011d01080d090e070507020d14060a1a0f0a15110d020f0c010c06140117070b2a071203050316031e02 65
    0x2070000c05146503007051902c07507002c0000b68564090409410075104c4a480034090b240e990041d800c0e1401980e4000104070709118500d84681d0b04001190b11071b005144c030301a440d2036952441c001503000c1c0c100c0034100c0465041d0910141c1c2103080745004002000c000c000382c242c540001400c9500a00400c4280c151280104201910813000d681d00140c004002212004d00c92030081519284502e40120500581d400512428200d1281c0703201e0300943c01043d90007030b180100300180c041c00321121a82c00852500081042140041e449040310000e4a52405140340d00c00384900d0450703d41750b5801194094245241080d602107460303031b801c00003800c0c0030301d5803035542c58a540a004121180e80c1d030800403900000b07220000800c1401c81c00c490340c00346c3d001180c0340d04101425118000250904d24408590034850400808040340e1041900b0180c81c5d5070b98898020305c0c4840503c42e004d500050012051000c94108001c5200700541c603401c0c1001014086241900b0481807050400c0345c556003c01c001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 748957113 1250 748955863 748955881
    0x6010e0c07020a0e160f020d08010b1327060b03010f0e1b0a09031223070602070203030c011e0203070f0e030c030708150703050709090c0201110d0b0f0312070b 70
    0x340013402c000fa1035410145008100202c0056110140c9000070740d0a0881d009154000320310411321040c0c0743d0b20120aa0300301420300c2c1059019481480480f52250400541b004c012541030003805076407402590800d6404000000b5a8400d40210712800d6040004001c1700f0503030b50100f0100d40c001e4103c1d0200d030381d400c030411200b4a41d040d40459860400210030b90f07410780c02000701c01a2031040040d1044c1c003e40c0042101c160f04c0c10000702c8084a003020680300340303c042101a03c0501e1141602524243c241c2c1d000c01d0460304071100c0c00030569111100404039408900d1180c0c41e07103000f490218214940048000c0c04a50704403402c1003800a00400002282c42c144130b2840361190280481c0c44444c0d9503240f184c1c0d40c1d86081e140814032503809011840d41e41c400d001e140d004480e107684d4681d00c64209055413004020b51210441590b43e200c40f2501d06c0d860380b2001d4807589185080003c1c807100d125080c04886107003101101d11039006008110b248106a50581e140d840d0810746d80c2d4500d5440c8840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 748958363 1250 748957113 748957129
    0x11103011d0a061706060a061d04150302040617010b0118140d06050106090501110307050618032223030d11010609060e061807090506030403033b06010e0c0702 70
    0xc0501040380c100044c00d4100c000040f110700807242968030184496940104940310b130f01b107584018442d0044036240c019441c00c3d07001f400d000000c2400c1003918a50722760002d002c84010f40d00600c0d4110303c0c81102c01c040c1d40213114180b181c21003801c001994540c044038030b024100325400740800c42110b030302201c600358071413070100e01401d940a4402c00c01c550f1240d901800450040c403640e800502d15483c2c0c00550710003c070175219050b500000401840d01c0d180100030090702c1100c2d580c0c0481c8001d0101d0604114007015011240300428000c3d0017517424019081e68008182c02c8800003942c02d111a151552000524200010558a44a01c540d070700c2075105405414290702040300705040c20700c0414a04580d9007060300603101100c66660b5040b900c048a551400b04592060201c0c0380304504024906204004580c011321078a4002005400880340791000d00003044004d03140c0310101c0c0140100000c2600020020f04031000030000740d850032042c052115002022403641110103d0300320119220020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 748959613 1250 748958363 748958369
    0x30a0510270e0a140102030105030c0613050607080706050a090b0702060907060e0d020604030c05091b03190605030115030b090c0310091b030b04120e2d060c0708011103011d0a06 78
    0x90b60700c220b4034130515254041e410a01070588030b40140e8581c1c106503d0040300701c480c2d900d03a076090000180d2804081008641207a8010703919114104005000102c5c80c0c03042e144541e007070004c00500c0303102d9410409008103004014909540c00308061181209000036400125513941c030340980304846c0100812515207030910000c1d0408030105021040003583c00b400401d81c1c2c030075190b20a0320b41d51000b00b00300412510311080400c4a040000c900c4416410b0003008404584040100d00e20f0381e42c50120303084501d400007414401c130580c20180200444880d01da90000c0040f0000c1014001d074400194a4a0090310340003070702c55907030040c6d0040040b6a004890000d003030b51300d8006078540d01e04151140c0402107608a4006404185a4a0540c018944a04030038805413504c0c0380210340f00d901780e10405000c80103a1001004044421443e030321039005003c0c0840303220140c00c14030b180c0980e00d070035180051198544018144014000e0a002541c2c404c034409a07803803042c0e40e50300e0f50b500a10081003960 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 748960863 1250 748959613 748959623
    0x3060909160303080603010f090b010b0310031208061807211506050a0212071221060803090f09011410050405130c080907140d030302040902030a0510270e0a 69
    0x1c07070001c28960400d42d018880c1006070700034080f222040442d907003120446031000f0049210500140462460b00c0007556009420030041e100154803030b00c0386018801d00880034000944500c1c20440c95080021001520015070b06050b182d038100381c030300a0515080008802040b003120026100340d039100b6001840003d250040c0d04440b06e23210b101c02455540056141800341c401ca00001c044d013102074007251035258120791a460000380f500000c0740d12981c5103d0070762584d0348810301202015150310440008042250066583e490403805010032014401c00491041c5c0c4000010044202284124002c04030226407084501a020303900b5942405240c00141e009102d07503290b8070080766980c0c00354491303000329105c00d500359840f81001d907583c1c24075014400805107030560100711070402c08456211203200341000740c281511042254101c0c0c0007141c00c213450303a03100d4040c41040804811448082d0800140e6144041140e588640c040101310000341e40c120390310491041544000d04c208007060f9480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 748962113 1250 748960863 748960903
    0x10e011d1302070c50121c1103040305032a06040b040b09030c120f09040f0609050c07030827030706050118061a030601020312011e0603020c0303060909 67
    0x343c40000c1041480031804400450017401d00d188100c2c01915a50700c00b49540101c004007034042280e02141d110f8200a00d0308038507111402e8002d01000e01420313000401d1284441100301009400500900c0f040caa242a550000c10060020800120403108603029200c40c00b803028401e4640c04100302d030700c458821402d01950381440100460201000d0080b400303807115449603290651800c0c1c40e4810103440100540c021840d5040480304c80001c1c1005000619001c1d0610000c0000b160503683c6a515218110b59030f91000d008000051081907040b05c8021440f0341000040c0e0350140000102501c030361030b95072000048002100070004260860a60380c02660344a00c0d00b1724000c80a40428000d4a02d11045900d03640d000b07100a00c1010f04452081064115a500b10100c0805070762010309a14118042049048003450b02c2c6100035009040d06640002e02158544070031a2001c01900710400b0940100302d40e00001c100001500d8120b0421201c4500c1c40e02d800000303034070700b03002c0701d021003502075003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 748963363 1250 748962113 748962119
    0x6070c0806090303091608150601110d080910060308161110021005180703080310120f031403070c02040b030c040f02040305012f030c04091505010e011d1302070c 71
    0x20100203940101240d0049a00c04540c6c0100280042202c0c021658998800000011280350b0720b001ca46c1c1100d07040c180314014202031a005401d00114007840c00105000c2c000380203008400308000c0070110b0321181304201c2c081c11980c8110340d52141c080b0102c010b0314940c0d018024002542d48030441681e000380307086e4603441c0d10f080180d01c2d100c00744601035500f1b00d00b500103442c180300e1480300000025100b0141141038290f030741d0900660070181040b4031007000ba50011550001441105c402140107501c5800004c0c211301e40200f500a60544042c52110188240100e4036001804090310340e6040b1004107091204902007440d101501b0b0901e60b0150a00f404109840015130050090300e0050000740036101a40c10760303030600a0f650288280021021000d0034100d10580f001c2d541010740c1c0302260780303020703601d41024007520040101d21000400c800c03804c03c815030300408403c8074000d0030300b800d8600660310f211104840844003230760303401203104090304442040c80b0340c1110611a400346a8142841d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 748964613 1250 748963363 748963381
    0x10110604030918050601080604240602030408100209011b02011107091a0303030c070204180b0c040f1215110906270d120c0213050f310206070c0806 65
    0x10b018411841111144804030305481c0c014081c203441041c040e199092607442c3d24040c000201780442e20a20501e40da00d80000000c4e416103450b80c0280001d03401581c88500708100e00c1d0601620144010000d80704010390034050b60412400b80c001c400042000c042181c06000584030361b828000c22280c03a0040103c0814a18600c0d804401c03042d000007820f5544607a0075003890b03138901c003e03200d0100a050a103c850010b20b01900845002280d0032103400440e14a5501e80c00454002e4600d0068a2000304040c000e401c14035240a0061000c0c0040300000c00040d1514a0807401c2070307032502c42107a158951a10050395a4089943c020809400c455450300e400300f40020002d00c880e6035000d40b50181000050514141902c00c040640101c0140041880790380705503403030a91741e03104a800c103180d0076000c220008580708062245141c070140c0701d014a0248201f182c00d03801c046420001c21003280082404a6440c407221841c2035050303520981c1d0b010b25041100e400c460a51006e00603100340d00800a140e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 748965863 1250 748964613 748964627
    0x12080c0d031d1f09020d0807080d18080a2706030204090e0607120515120604021207060c1b0506040815070c0206030f06010309120c03020c090708061011060403 70
    0xba44182d140740380004030440d0140c80d100c0070310300586101055405800082029405003080a100918040b2055901c1d0ba0340ea10580140c8010389000301e01055280b182d13180c1e80203502041404c141a41080d80003580c0707002c041d019901c200c80420660b90f540c00406164541c801c20350b6168081034030b2049603110030007006540540a801189810300041174900c0303800041441c0511001d84840445a0400300b00308020007005001d0200040c10b0300300d0401503258007074038200314245c0c0310240443d0700c3c00b80184901c12481d13440040d601e9000003002c000d203950003e58804000e0b4000000340030302d001c022025000410b26040240d002c000000c00043d84640010000401d1a01508001c070581d038884055540c2052040003940000701040001c80001c085100340b607000c4014107000401842c20388a4100000000c1880400b081403902080305041c2c040210305e0a01c9800c48074004a480c050000a0a071720014281c2e6015001c030002c1100d0250248900148072079150003141d07400e01d05070600500c50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 748967113 1250 748965863 748965881
    0xc0a1202011e02030912070504020d02040e1305030a030905070302031c09240e21010e01110918130f0c050f031908090a05030115060e061312080c0d03 66
    0x4948503075080340d10000394101503002c01e400380c1c0180d800e0214120512000c1c1401007013110309406580400b282d603a45a102901e55141c02c00d40c0180c4403800c141005101c1d0901074610641d40c00f55440b0b120000c0c0c0000b0413640d1281c0c0303038640031450202601d0943e18052035900005e50601915180c616640300c0c103030700f80ca00c40001e60f46d2035454503517403029500050030440002035010702050603082001d0140302c000003503003000386c0b42ca03141082e00140003070b0103140d0f1825465181d44440c521000784509008068043c008084814601520380c030010f8050391021415040d010801c1c00040d10981e2811071010840d0303088404032210f070302c44d89825101e80215000d0248580324206010b083c07418005409120400d004c034688543d40c140340c5410009402c0061455440507035000049a2078a003030089480c0417058031100c088050500d50040c0100301c003d1020350142d0020700510003090f0148003035030300310b45051210bc030f010702440c11b001d130141c41450100010b80c0b080c5810007030500c0d03240c3d11805003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 748968363 1250 748967113 748967117
    0x522150e0114070209070e1309021306061e051e040e100b0304030e041104060203121b031b0d051617161b0f2409020d03050a020c0a120201 61
    0x8000c140c880159414003140307a5240e244441030001d03600504100c0310103900030f07065044c0f0a05400c1040005080c0740c0b1510650243d46442c7c2c4e00180450604400e40d0309650a2004180212424114001d0840c001c1e4051200304c0c1c1c2120091a80304c9000308212a0f900c0840900c48207105c0c814204407400d0f034481d110b80d403135900b1407a0000da08a469020041c06944040c08083d05d9a1200e44003240c10b10340c00d100c1c09900c80d942320450100031714988010070007400f43e07070003540c1c0b91030081001c0e45080c2401495001510201000514441c1600c01103a40c4803003812031b1201036031242a52041503000740b8445c24209884c0409010241250445181c0c00791a155151214000c107840d85580580e02a100311602401035107040070b086008104500104645900781a240352298841031440d00c1d22507c10354503d145a003440a9580718a180b0b801c071450301203014004800150702042c0700300e40082c0e010f410001c02213440d4481500c03d12000480003c0100001001c907103800840e450300c0b49140e02240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 748969613 1250 748968363 748968377
    0x140f0307110730110616170703020a02061c05010e0103020915100c0512040f1a1213031707020c1008010521070308160c0909050c01052215 61
    0x1c08840703101c4244400010350714440c40c0880c82020050380c5203000301c0102c840441501482e130042d21014085d00c03600741c12240040e454030050030015841c1110f00e0300042c010b24208148404240c0014100c4c030343d9035042e14465900d194004114000e01001c1d040c0c61207842c20b0400008041c980c051043d4160780c001c0703c0304982c60315001e032000404104c10100c10717000091001d08075041d40c0500c951500c940e000e10161200c1c3d100304a551811a801900580c24050b050001032140305002c01005142d0707650400814174041d4055071a0300074030b40050000078250140701c9081d04261154135580114103462182d4203480c2004500a5100c04203180e21900615410f10000764491141c84554100c8078003808200305180101d28240040d03802080621951281c108000001544071005041c0c041820541507401caa181c50030b03142d50002d40e0300050885d41002429004218003042724000d000b0b0908100380c2c0d038982d0022640751104070030410403c60010f624002291007003000166140011551a24 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 748970863 1250 748969613 748969619
    0xf100b0319020f0a0306020c01021b03031009020a0c0503160302012409090201020114090604120306030809090a0b03030706140f090607030902010e0925030b10140f03071107 76
    0x10381d120341540145208440c0180c0010142c01d05041890525030090162500070382c50342c44001c240ea2140414540682d0300280007000c0ba500508900031140d143d0004e1071450400544400c0210700c1802050685a0f000440d25041c0780900746003034825074001c2c10341c1d442d201d940029107500c800803802580954280480300b100201c415500305106861201390301d4410341810007020082503050012410b540da1000d02c100c841c50445515441003400d40c00030201c41c0b409113011078150038019050000d05044c03460600c001381c01241a00c1c0000c0d01a520000b00340c1c0d491302a80040d00c98403c00d0358060000240403424000560408003a04032000ba1002290300c0300c143c0190b507241d003100c61005541084004c10042da1203034004e0000c9e10700516000d40383d480e010000a0341d90005942d008802c0204d000c6010380c0008200314102d00c0300305800d04000c1c6007034040c0802d60000c0950701e07207420030449600360548114998113039a1004a40310b40c0300c4c2c891038201d002a1200c0c0c02080b9603101489125000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 748972113 1250 748970863 748970869
    0x905060405150d2703020c031c1b14100b0a05060f030703060b040603060504150f150c0b090c1201110405041107050105090c0f03061005061b0f100b 65
    0x80d0112030340645440307014862a003100c52240c10990100d400b154948203009000580a42030b20f1412014520002810401e0329001c0e01e80241032407181c3c042d410030410034140c19460030040c404403a49040c41034040e01d050300b40303510b00062090300034070300144002050000302c400612041051a8035000b000365101c040704004240c41d11348a07031a44404100106010702d2000409141c01011506010500c0d9440700701b118003940040e040b0800082d501e1f0010001484c0c6130103441d80e8600c14403803d04c61103040c0a000d402c2c00413035000e04442e44980c00c881c403190920501100c020290402001e52050a10810064541009004c1d10303100c1e100c08030980307101030018400d51200c012500200c074640352800c800d200c081c280c0b0300d41302c01c40110300f40700741c1000c01e00c04e008103446548010301074202d02c14078004000c0700c00548101c041c020b82c0004200480341c01d5490911080e20b004550441d240c1c914a4501c2007548502e4025880034003450424824035407000030104800c1b19a01000c0c898a40b8403828 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 748973363 1250 748972113 748972117
    0x21010501020c01140703031e021c0c030b1f020312011401140418050c1207180b09060f09030a0c080a030207090e1e030d09080d0b030102030103050d0305130b0a020a090506 75
    0x3a86000d204c00b00a502c0010380a9404207107c80b406840c000d500050141581040760421100100f850340302c610760b112606000d01c074003001c8402c00d003010402000346d20b000c60030940e1210386000b2190a401c0300200154002c10a440c01d42140e580f02e90b12540c0c640c401030b50000c40040d0b030a4007290041540590508041c0c0c1074405403001e03404000b4003003031800f1341d0f18043c00340540081d0109100304480c21001d1a1146141e110b0502911542c68080c0c0c1d400a0100350445507206101c800414080c0c20308964030b40040b40d0301403100180356500d4840e0000043d042011828004018001000001030201d9000c01c8100c0114025000e407440140d4801c1c02c0e1060310184a0140b030a030700568125003281d107a86c1a0412503208510440e42001145110442155140300302503800c550007045443d520744c00303401410881c00c0290003c2d82903500d503503a01c80c1e03240c01000340e80b02896100c500180c00c00109214071902c1541000d80a03116003407940490000f9802841010300040d0051000b09140c208001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 748974613 1250 748973363 748973387
    0x50f09070f0305070e2706120a06020306132a0c0b220c062102070507031e0b0a09050f0109021c08090a090b0111070b0403060902010521010501020c01 66
    0x4958000c1d421000c0128020140108003009000c0441d003260305540314012842c0d42948040f40b5181c180781007044000300070400408561040209003514452001c002c5000d6000550210000da02c81d1107403c0010f54403000c3d2892110581d180c002c2148a480c00040c64070f5210520104214960080b8030080741c100f00751410241c00c0c04d05a402050141044030401e21105800d40554803605201d95100071000541da40034200058041a8003600030681442d80300c001400d01104521f010030030b43e00d035525007000c2d100103000c0c0b40c0241c114a403114001d102c005100343e40041c4000441c64480120001030000020640302c0348039041c508c4020f80014410320b4410781e00104039014020000c4411124030700d5580003101d00301000c3c48524903d80300c0c901d5450141094040218015840744001003803540700d03188190555001d00310400c07441a4030401c03242603a800c4800821000c2e0b0900051740c46114850100220580e400c45083c0070b00300140e21241070302d401368240da040302264001103031400a131003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 748975863 1250 748974613 748974617
    0xa1203090b01180b09071d011707080601021f06030b0a0e0c0907050d050c090316120305090607081804050a2714070608070306050108090a02240c07050f0907 69
    0x1030058920042030003202446030391001c64080111307004100a40e00682d00040854480e008040c420199554511503440003881c00c182030880510004504070409006242803196000104001d40d01c02c1c00104010703c0101140f1707281510508480004120600c029a1303142210804900906204c0c0141d4200d00c01200040403208008820050a0a4007a2855052040410081c50042060300a0600c2960302c1881607880e0140300d01030500f088000c007919603840b19601c000b40450141d01440303e100ea90540b404070784441038a00400c201d4840c048014001c0340c000310322509180c00e4140e0803040103d0588050295840f03118030881924112032610b044607009a03001c04040d81d0049801d040540548107a1040b0f80381031000700d0408409400620005419004003c002505400b07010020803003031a22070100d181c0004c0107070329010714410081c8a035844040446455000e6000d406441c4c0c06820440d0b0f5410907980740e107950390441d04c6440d008100e640050292883c001028601c105265 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 748977113 1250 748975863 748975883
    0xf0816020d0f09050d060e010e030702011b05101407090501020303150d020406050d08071b0f060309060e011104090b03070332011503060b10020d141b0a120309 70
    0x71a1058460200c6482d0726410000800c40028256590100114107603000f4100060307841901100507080d80c014140303c04039030b8000c000c16001070340d200714201445406401040c6604159180640c1801c105034036600110381009141500d0251280d2801c1c018002a1a00558a40d481005980382e00080300c0c440c8480c0c0009640400c1800c049080c8290f01d840204001030042e11540080e0710380c40004001c0d100c500c4003207a01c0c030070084103c1240800c0d0034071082000c2c0b01881d020040074040c50a0040780f040580b02c0040d0420008540c00940f05230102100a1018944444406810b500548a01200541010403141e180c0c28081084015070340c003c0711a401511007101460120700c8801d588140c1c610b01102513080e514021f00c51003031408041e0700c4502c180d9165013004d17015618001035030340c82400c11448264015800099546074001b00d0306145103030140c0000c61a0990280e8450031100c15013001c941c240d10072001c120001d01a00c107608941070311450b201c0881c00c43e5203541c8020b04202c0c407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 748978363 1250 748977113 748977133
    0xd030e361005061c020426011104052107060806100306050d2405100302103605091009050117070302040f02090d060605040b040e0a0b100e04030f081602 67
    0x4030000c0ca070ba4001c10305040d80884202d001542203074011f6000c8010742d02104904503942c400e1000b41d80c0580f100c440240000d01e0481d10360081ea109501ca464031810a200c5104011511410620607160314881070320041541c5031009850100111503152144403115001c042690292150384155038015184481601107940c80d026050012119500c00b40c80c075680003902903e2500410b0710400301446404a160700c0e510601c4400c12010318440188520901e40b40c2ca800a440d001c2500f4145154004c0140128440803205101460708400d802400d10410010b11407200b41d0076074100d40d0203003002c101d540e80c2c4003007040b200013030062a044d03240c10104c000c10162405801480c03003440c01c107100502d061501d00004200da08540d90440340d443c3c03074800c20480b41c5000d00c19138003401010384060004128180c0b005884485603140145040c00c058081000c010014102034054940441c03035103814101400c0142503c84070101c40070001d000c101c0095100d000712010200c10102c660010811050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 748979613 1250 748978363 748978369
    0x3051902061218100c020a0b0c09040204060c020a14060a0810090608010b030d0206010b09040f06090c0206040b060607020a0b0a031e150f0b090d030e361005 69
    0x24102003030764040014804240d40d40d6110b10110301610034801d100c504204501c60850814000c040c000c0541c503d810140070485402081c40c440e83c95009403054015039030601461914001d00c0c0140350031900c00b1601040f0650490000c25020740220752203080c007030380d8032411103416a01141c0c003504044107102d0040d40f42c1c000c4005980007160b00c08903030940380d225121502214000d0740840e030260344410502c00705050a1001083c01c0c400c5101400180d81054040e45140c4201c0d00060b00a0381d90760414203650704280c0c8100082d01c000b45090100018540c2c009503142c0702030720182c40d00301c2900046070440c41e18a080707800c00790380680030900c2149030846203000d81d0022070b0b41070203050715511620320015660181c100c040548403000500d40b985180e0b81c50440c40316030008042e0306e40c1d02c1018055903507824150703050948201e03880e2080f81e4039490100e40c43e41c48400d0715901f104605034904075925904041c615500c0300816800324800c0000c0510702c0d990800e44c0c2503101003980c1401440981 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 748980863 1250 748979613 748979653
    0xd0809010e010513021201062301050f03070e090a0911040207050a02030d18080a0f0b0613090803160503070e090c090a2615070309151b0201150305 65
    0x205900000300040300d541c4090940c0e10403100440d5000301d918890045180852a40803100201c46c0200a030a042040ca90415102d6960282d64095503076088482d07a880f80741154560a1802c01c110f031681003908003d81038001c0c2c201120302c2110300b240000d404c0c1459101c0e000361550400704c04a1505c100c01d0501c8001d602c0310a0596582c010455602c025132010030005019440030b9880c078175010003010f041844040a5007002c40d40b9040001100e01054048060180d8650800c02d00030b880c1c3c030360f100020100445100908501401c140441060000c1007010310320036101d528500181c0c40c540d00302102c0c0d07440100e5800700800c00711802040e2509080304455807080d240480ea51902c1c3c1403100191107008240d008511450848030304118004000052050341765014005041d11101803800815091008025404040d9a0511081400985060701f00703001d25042081200f1140f10040391540284103440c0005582480c99211072125007801c80011a81c000c00541003088c600140c0c88107070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 748982113 1250 748980863 748980871
    0xf031608131b030206180301050618010302091503070906030c05040504150e0f0109150e0616140d240e09030d091416030c06031112040213051501030e0c030d08 70
    0x5800250703404001601c81800402501c0d080b02c1600711030103c106c04150949000510250003811a81d040c0e5804000c000c000340d05495049a0410041d600d4040d075994421100d13a14550601ca4050000b480030719961000701580c0c041c0d0341c07460b003142c3c980e4144415614240e42c0248083c84800503041580000d13844400b085c0f201000303440007440e400301c0150075030b0025542a580c0b80900c80d0b000598140c0344c0b292008018854000e84401c1c0f0f0440d0b2440c8420184041c00000d04c90082080c840d4041e6007400c1b60200344099008100c60700140c0402802c03498412000e0aa00761040c5010554076010355200c1e2052116500641c58241002c58100140003403c508071a441e200d044020f84c1c00e44240143c1000d590840d01442a407465403c0001701c2841e80d40c040c81c00d040c60040c2c4040340884050441d01144038040a0380400d4891b480400c00a10510441c0c4050324a050b06012644015101c8a4039809090744d003481650a0400015260303003a4048169160f440201503003141806100001e0340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 748983363 1250 748982113 748982153
    0x402010c0512040603022a1507020f0d090e0916090b150309161508010509270601050102160f120f052b030209010801180609020f03160813 61
    0x161140c2800c002d8a80d81040c0c2141c804280c001ca140d401c220414112800450443c010707024003040600384581d216002410508800100500054140b038000c100c2815039000e01c2c1b04680005000c0700004000000307501500100580440111f50b94100000d180d04880c6c0c1c0d200c0b03c2304903003450702000c0d000500c2000a099007000e50000c1070301c07504944001840c4074a120002a11552a00010951b40388001c0d03007042001c50b100d1070b08001c442d83d200640c03078150b803401e03552500c407500e8254005a00c026460418a1000e51040d0b2658510b100820740710304880082c0c0031a40f0503e500c5150f48050700290160401000001000700a00f1807103603215100603000e840d0a030080307980c58641509048184409881d0072410745260f2a4110364007003840807444451408509008403140001d00581041c810035101c29a032400074820301c801035100e500146070f0014210368501c15240d02c03800c6a00101d03000c00d02d000c955440851128010310740588110701c0c0700c4c001c0c1840c1e001a51385c0c0c07482c0400700794081c0b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 748984613 1250 748983363 748983373
    0x80a12030c020f010510060e0105070c1a190906030b15070605061c030801030210110d03050c0919050315090d0f03020910020115081b091e07050a0320030402010c05 72
    0x4101c1c50a128403800ba01b001d00d4440d441609000380944641130210705030741008410801c100205001201d2a01a65480c099902151252164103a500d000d404140e11890208488480a940d00020504c0444145481c00e00c00080d0701d004001c500c2e40c080e405030b16036280411841000490b59400a07921486c020200500600180d01140760740c010801c0480101d40721400600a620f40382e404c0b0300c5010300c2ca25141032211501004140c542018620072001c1c56210008546100c00c4c5006441100340090007458211407540c2c4d24460f91010740c441c060081c0200000c90950550003190144a04a84802440e5500400a04031050b21400307010404060707007885010856030745c0600004511040c0d50000c1381c03420581c14081c0c0448041d41c0280e0856100c42800124401420441c040c1200100c43d54800c030b41e00d00f884003c00c4c681c140c2d11440300c5040d034010401c81c1c07900000a002c41c02400d55040220b005040b005804494590352400d00303807501400000c0066204180080000c0d100c1d9040d00c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 748985863 1250 748984613 748984633
    0x405010c060e07030b011e080a0c06080601090504112107081303090902070606090b12060712060306050c0426120703120f0501060e03030405060d09210f09080a12030c02 74
    0x100f0071080c00c3c5c101800200b80d03000342100080075400341f500941541d402500100700d1035520848802c600348262000d02081600141d07142e03000342d0060b0000c01006e8001d2242410031f03182c070001c075401064800300c80c818800c044400302d05d00728046841698540c07200d0401c2d80702e0301c3e10224002c1001300100c04100300502c2c0802d03103140e10700141010520544011a1180c00c0c040342905490300252250b0041d920b0000c40140d04000241840c0c0003015410a4605c081c01d1151450180055800280505003842d007480707161090180100200d0703030b5003000040c60140395102d804800380300b102800c1441c1d100d03080e00c0090894034401040359510a0414961400c1c1d20074840e016124080c0034012034580d0b580040204540010040c4e566807000c40265142505240001d6580c0c00380601100c4010b590701055410800000041ca21040c02c0c1c00740010304541003e0010206030300344c202c203400100390010002c1c441800003440169280e0000c0c00200c02c61801c4000c5000b010000e40440c21446080c001c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 748987113 1250 748985863 748985873
    0x15070f14120c0d080603060609070813021c0b130c03030818010c091712030c0306040b2d0a1508270c09011502030d0902061c0b030c060405010c060e0703 67
    0x10304480140380b02502e0400c000c80b42c098400280104003c1c041c1e0030040c10018566216070311071341e02a4076420820b07216200d061540c02020024400290040b0107001c805003401c001c54541c0240e9445a44401d44690381c2c034001a4018820f018014100300302d040b014400a4001c0c025550b01440d4031000d4000100700545c0c3e642541e40c825590000b04904080030300114038001100781250903a20000e00036501940c908604a00c40200035602d102004408564987e80e02d80010030000ea00030840d866544c0318004c64141003060112542d03000e0840860340c00349041c01200b1004481140d10910901241c5180568401d400140f0301c01c403030040402c0c000c40b0f4107a91401c0c6203c01000c4001411300c655034200780300041c9410b030003000b0115190807854075119800011510101c84e20072020400704568404950325015a09140d50031840b00c21034601901590390100d00082d9084040f2050a0031030020f0006522982c0500303030006401c84e8000f8085a0150802e45d50600104100e6030515581e44036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 748988363 1250 748987113 748987117
    0x90b0612160210051905131a0109200406031d0d09140303310b1206040f1a010c021305010b030402010f030c02070e090c0d1115070f1412 60
    0x30040401051428407000581d040024803004030f4840390400c401d0400300d640b01d155007403c10340d016080c0d8964001030344171000e40410030a90b56024030210483d02c554070264001400900a00710018500941403d0648854a550300c181c1440c0c460249003900b4050100c014104805040b850010b0064041404401c20031020889021654441c0b600c079040143c5268155640400f0b284254002d0004070030009000c031502101c222501e08280500152022104134251564040e542c001d0703001c1034a540c000c0401e030b6128803c04c000c8404100840c1c000300400300301c600140a600c0e03c94120441c521145d4050495611260300050040c014403450301005019681c09811800b0304c21000f1083c03108550300207450318054041030070280001000500001d641c0c10340c1c0c0c403d9400004030007000c90300c044001c1c8178115011801800e100c0e0f50b40da1505150b607458100b0901310b405520056041161050341d1030540e40c0e1030350b200040001c108403170780740c0e0924402440081401409004100c0c240c40c2c44002c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 748989613 1250 748988363 748988371
    0x30807020c0307090f0b0405040b06010c05190c0e0106050a0f05090f04020301140108010b0f030406090804080a050c0a0b040524040e0712050a02090f090702010e070b18040902030304090b0612 84
    0x8000c00e003119480c0000d1700f50340c1c041280d140682e08040a02001850513500c0e294014000c0c60001101026420620320300340c4892104410900500d940380240101044160b040d9241c0d50b601400690f0b8540040b40d0a20440718441c0c0014107400b5804581e9108400030082904002c00103900302040100040480e4800e030301030019906800900c0b0003558014140c0340c01803001105042c02c020312134031013110038800100b0040c0f41079038407131101c0c0401c00b1103400d030780240a80004444c003040309480c10b076548034545041030307114110602000901d0346860045800352100a00303e034200b8041720700d000642d80843c070001c0c4004d40c03082c40b000c03c040d0a00c945071031081c10300e035480342c0d04180c50605da5030032110060b2414814034010028807420303455030002076070788010982d4040c90030754541c1404c0340102413004401c12180140c0702c001908008820150843e480036815201c0301494140821080700d0000d540250150414817003040022600c1e440a082c400e4050500c074030300100c4890140000303100300e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 748990863 1250 748989613 748989629
    0x110402120f1e0a0b0d08030103060b0f0306060117040c08012a0c03050f07050a0606080d0e0406080601030b0c190504080f010b1e2403010303020d0c0f030807020c0307 73
    0x20800041d1040c007445402101c05080c00740c154000342c2c1006480e02000b0201082951500700d0541281c60301c8518070640c030340000d415500c0f03586a14001e0054000c0b9251603200d5040511400303480d190104805004020507184c8480d219801030000c8007500307009206803003102010314001142c0300c0038006d000800300d04170402010148003a2104018007664070fa500c0c2040710f0b003104840041e8002c8200c07000c56000d140e0080c2c40c2c0c034a42c600302e031801c0100300300244001d0404900040350040011a1140c41c4071036106c4140000300c0d1014081210721a1085d48100e5101d44010400b084030b025040390403608078100d081c6040400298451241091103201000607000181000155001e0043c00c00c45980c03000280115242c1d01c0006003a100000e458481e040f841010001c0259114868240c3c2007072120201404110ba090314105250401d10081d000b601448003500d8196201c0ea01c5000515440306020403c100c0c030761800ca8411000a001506510464440c1581c0340e4040041a00800b540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 748992113 1250 748990863 748990897
    0x30109031e2c0d3c08030109020c01090210020d0e180106030504080c1b010314161b020d150b01021513020406120506190b060706020c0312011d160c030c110402 70
    0x13200e44c415000c0219480026420401e80c0d102000406120489045880180d009615418000d0360103006010741440250300164141702220740710380104004190720314544564240751050800d1110028482c109003420458040043c44214017943c0015005402104d0341802e0030070765031a543c83c0c28104200200181d414855210f4030750f0707250090708400e25000c000c0f6411801c00c000e0010240b031410b40c00c01c0c240301403d80c55411443c0e842d2171090a4540091814810344900d04103255941482ca540040aa041241a0314154000035019211251000c043c510707690780d0312541c0b6000101007508a900c1038540c0d500003603640d07004603071810791809800035045034100400a40d180c5001ca48100c608a03040c54002c0e004c03075642005980000d81c026074056a01c0a07401d085604600c142c04900031044c503854004512010840300c061201401402c071113103a910744061452801c1d00300707030302000041c481243c44800240314a0700100058464400705418030350f410000780590308000039580500540d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 748993363 1250 748992113 748992173
    0x41d0d08010e060111060402090619090501050438030304050d05010e010f06141908120c0706050403150237020c060309060f15030109031e2c0d 63
    0x540000a9007010f000d00304041d00d03600d50344400da12204c00800c0a4861211a00020301d192140401c4400e21500c200c203880d03415456181e4140144000c0c00381d14000d52900e40112180c0c00b05c410410b243c0d2101c0c08100ba41411410340710041e444070f0310b8210350103000c18000000d03a52600c841102c5043e224000204046105040c41421140704131080048123007841d10412240e80381b01c038149203100e01a50b0b1460388000d038200c0385100d154107030300c80c1525101318204410450040ba01800f02840d0a6098401c000e59400044a590055020260100005c0354281c0c54500e81940144000408000c14140c07440a1301080d4410b10f49a800105403082d07003080321102a0360501000c81c02e03420450340d42e4190704025210329500c10000f410300d1030104000d40400e0740c0312500c00c8407400900004000f400178000c103260090280c011400d41004070010f114080c41c00d50702079000003d100300e049501c60700803151030300301c1400c0b44d030300400b182d421000e403602c9800814602c4a140c0f5210034880c035490b1000340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 748994613 1250 748993363 748993379
    0x1e07051207121b1215050d0b010302090106050306310c05030a0b0901031109070c080f1b06240105071a01081509030409050c0d0c080604050108070302060405041d0d0801 74
    0x404081071140396100c0e0058a01e996400081404010407820000220300c4034820b40383c00c003090b5682006ea40001d4001c41c0604200340f500c025416607100380c2c0c664440ea66a420103a581f40010b03100558012007421010a011110302e031205d108e512441e061040012a2024040499043c0d085a00000740000200104018540034604550409480e0015035615686600c2001040440041c0c8110b00d8080400d0b0310070312500400f480b00390415417035540c0c1e0400740c1c1d000ba500d500c00f202d811321554460b80c105007080300100320701c3d1040741e58080620081031605103038401ca180040d0300c40d0520109105c801d0104441003550b04500718001000702e213550605074954031b043c0952031070980f03034007424003009420301010046d68104e0344c0130040481d8940f6400d140e00e5541c054091120a440d2405440c020b00961050450340111350964003000940d8030b035401d05480380064003009c0d400842c104820400c60800d0380c0010b18074081e206c00c00040300011503a507400c0c040b00c0e06194000035503400040c00408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 748995863 1250 748994613 748994621
    0xb180d020708031e090901080d1209030c03140d020c0a0507051005180301090213021308160b0d02040f03150b091902070302010e0f150f1e0705120712 66
    0x20900040c003406190001c65079aa04c542c2003944181c941ea541c000b003d450b00d12054503201100140300740386a68503000910307603650000c101140019081c500b0029001c1c1c0920420031120f40550310060010007548003600c1b48131b91580040d64180c2c00b0405100304c4500d48c4040c4c40041d015001038506203026041c040e20f0582c003030b00114490030300c01035501401034004084640f000c0c0d0504040070301502ca90000f900408072080040e4110003168042c800c0e00b400c50303000f01a8214155010b80340c140d15140c0c80c640d901404444119080342406d03091040d05403a801800c1c10700500700026143c56102c101e00203074181d040c1d100301d43e6070603100b5461501c812a4062a2004c0d02c0680303005c6000d140280071960320b00c111121030203495038001912410b00d0f10070740209003030070001001c460111242c00000340d40ca1000550f188160789421000c5050131105160850240600c0c0c50440c00f00310a100380b05400c8440500a402440020080c1c6051001080da0701c92041d07135a070302d03056000103d500c9094155 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 748997113 1250 748995863 748995883
    0x803040609140f1003020705030304060b030f070e180f0a06050f07031506030c1b11011218240626010b031c0c08040807170601140d0303090b18 63
    0x104110352000110343c40f01e160b00e02c00c4003c00c480e010003040c00718005070001d1103040b8001e80640400002c001c140025134100d0501203100350100c40c0c142903090382c03580d21429640a01030001101c90003180b0504040e011111102c05800c0955644000500b00b551904003401e000326800d5899804201c214001d442c1020303030180d001c2c24180701004a0146d0b01826580074000c00080c1030f6034000d00c10049200d00368a800142d00c46010b51088115420400354007280311520500107036800c21007241448460140000d01440d880400403001400e80c0c0f903032a100a05443c900d5055118500f5000c4403001d800f90800400c2101c0d001804005002c40f0031814141d041d010649036810441038a219850008001c61182a2620407000a61021500315201d039034a103000f401140c0c0210300440c0c4c0c1d20021070940200d54218940c46680f5139050000c58495500744203441c4c0c8800c0c1690f481c0103070306141c000c40c00228400c0c500001c12040c0c90355107903c1d05000382c0d0500c07080e00d183c01081810f68800c0040d1440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 748998363 1250 748997113 748997129
    0x90e0f1504050d08040b010504050a0e0a03111603021c110d030302030603010506060403020108041103100903051c050c040b031b0a03050615040b160203072111040b0906010302160c0803040609 84
    0x284e1301e401d443d1103072045418840c00b805a9070b40e10015000c0001e0f0740c46100c0841d105019105030b04c0a50074010810f81c00e9000c004498000e203000300030800000310091045030b9003d04606110240e408032821200c03490001610f4007100304840d0003c696801845448840c441e880041e1281026000d00d82110402489513000f03050800c400c0c00580e8001150960050744817850075000200007000c01d0034044100030340b40c811820010000c081680080150480e0f0f85510802490318080050103019200e0a0324040082c5d07604010a00000b030403900103513446040e203080c0d00c9208001400341c4051f42e1008480100103a074170018444513141014000d00c1d0791588000039401e25040058000c0c0910960b21100904464074815208545083c0103040081c5414001c0d03c6540800c0380382114201c1c21356204449001c211981701d1000d242900c00e103000c801010746407134859a14400154002c0d030041c1c006000d0941045040c0b4000b406c0c6082c0f41c4003414284000c0d6803100c5c544003000d09090025000210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 748999613 1250 748998363 748998377
    0x20a1d0a03020609190312020d020105090d1b030216090912020c03300a02010e160609090f140703020a111b010e0111060a0c0905010e0901090e0f1504050d 68
    0x340c3c0d1188103550b01d81c003013241d2103050010082000c01c03030f0090603800103040344203030403840c09229000b14983d0103608a81d002841250780d890319254540010386e00405c0411240d00c210070b0541d403800d100c0d00e1018031030700444589208a00014008440c070340d01c141e04550b1250190070030014452000b016244546c001886002a0b07000001e44540100100e48404030910104039102c46036220a44400c120740d034aa1030341d8450008000f40030b8080000c03822281c1c8180e60a1003085410302600500b01c4680e9a1408001c07401c041902025044031078000717003100c0d2120343c910501485400058040c800c5500c00595402c070310035002d04011500d43d85c0041980003960f5800800ea464050180059000d04c0d00031032450746900140c402c4802d1030b01c0c0e11081c1c402ca404110703140040b640104622801074031a444155610001100c002000d081d400382c00100302c034010403101d221600b20300e55401084083d220f102038145181c6141007580c200a5551004410900080c00707400d01203100315038150300c0c00075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 749000863 1250 748999613 748999619
    0x1b062401030b0a0e0621030c0d0c080a030b01110d021f06030203060a050a021902210304110f040f020705010605090906041707050c0a030f02012a08180301020a1d0a 72
    0x2054004a80300b03101c4d0b42c14035240050000e03034400d048805512210004d1586039446201c00c0da543c0d41001c188800710b4440d4440812410b406a80c03040d40c803c1d40098501d160202203101100500f03204201141480903940307110307442031000e1084040d100c1c03007a401810007030201080c4081000341a074400207098a00b42c803d1002d0303240480c0581d4090708103c408511a1a00c0b220702c0000d101c0c40545810991240803040410703036011409040417020082c1401500e1200780552b030b0903210a0b900104410542c0c80c0211450a01c1c070084e2884000090002440302c2c0c2c0510b80d18207031b03030202b00c01310381c2c99644040030b000c2c40c60004200b580218054006056614103541e400d046203004401640782c01c080070a44404104040041424030b95010341003e070440d50300c0c64034116000088400700d010882090726a4075010f249500098081142c0314810400049a252240e0342d41c070001444081c1c158800c4803d0311610240000e062018aa40d0345054032039103400140c2094001c410120304c2101209020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 749002113 1250 749000863 749000869
    0x10302030c0d27050d09050117070804050c090705040e0c04082d07090b03010b030a02010801050f0420041a03040f11040f0e03030a140906010306021b062401030b 71
    0xd9118000c09038000140c42402150700c1c0602281040b0814201c0e00c0f85002c42c00700040481c041090003120b4648210440c1c5400c019a00c11845114501034585c40300700040700e00748503000c900d8200c0c1c05541610700b0f0b03103c080086079001008441c440d010030300c006030810001c541c12400c3c43d0300c80310b00c10005080c681011405522207900c1010689100d8106000c3e84400312007454101d200302c10541141d80c10350351124202c000d458903280c500d100b54a810202c15044c240480c040865a605a594204681c00d140401490040c8440b5543d007060781c9000b0b5410903c01c0d010740d020305051101440383c40da0729000140100b1043e034102403614503002e006020010306e5180301c0007109a801a05032950300c10140c0070500500d84036940750b00b4142030005440c0e8140d0088000c50144100841c240285484142c00b200105802e640d1080c4980c4030300010000700b04203a0140c9003918502e80d03a103030b0030848180301925140054540400d40c0310258018001840301c0c45003130307041000c21308052014840c45000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 749003363 1250 749002113 749002117
    0x102070f120b220f121e050f090612040b0907180f0209062a0d02060a022d0a0201060603050105030604122309090703060e0c07020301060e011211010302030c 69
    0x3008180306094000f00780710501400750b1540e80560075400b4081c100c454201100304035600982601c54407030000300355030214482c2100005046880d1483d9030350302d032109421202688528054481000306202c5590a50b4418008bc441c505141440d520141480c0c02d1140c00804064152070f00f6a005072420003081f0441010aa5921a1000d000030100041450800070744104a40f6076400303080042d0b00c0c4504542d8441005e640003d1b161025005c40b01c102e6401e40e503100c801d500a025034020780010384243d0240e001421210005a04840c440e2500341d2855082000d50540384840d81d03011032018605a030912807500100034900d018440c951600740881c4c0c54520141c000382c280d209000c209141da50081000b0f0742c0f021070032500112101c0b810082c45040703801c83c0c980c00348140e03900f0000c0f0b80290f209000d440c050705d03d480180503441e125444064115072010344100d8042d522400700040190f001c900050003001c1c20020341074400c1a078505006a00380300304406041c1803040c42440f0304e00300c082d81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 749004613 1250 749003363 749003399
    0xb0a0f030e0c040c030518011a09040f14030a18060c0b060103140a021803070b030117010605030a08030a140417071b060207060813080304021c02040c08060102070f 72
    0x400207200026860500e080495200589810904014182101c141e0540c0b2440c8a6402d0000c031481080e0004800340c261580014056680c500a0700102458501840d0300c030b03001481501e0b0800d8034641031f554103e0303e40030070003400e20b16000483c13a0f840440d00201c400710301d120b0329510410118103203800a0180149110b01078040d045440001c1e011707900079806001004a001d500b0021031400c4620391019600918a01641c0c0c0320703250350000f150400048540680344103034000d505503030030b00700019003106503004001450348d00c4010015441e1820b00001c0500c50040c01001c2da2407030815800d00039103000c030340e00e0b80140d0041c6080002040c2d0480c0c261800d0800118540e90b01d42d03d5003408140d881c0e0101e0350f6116103481800000741d4039000240b180c00c5405544600b01e50360768072307840143c90780856040540325080070000100146443c21010700300385820600d24452842a030027040171074000c12000c0002c04c450500384030740ca41c0c04000800c003c050406100707840908003281c0088001d003c1c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 749005863 1250 749004613 749004617
    0x160e04060218030105041101090801050f0a05062d1c2004060f0b0406140a050405060a111b040e0a1a041a0c12010b28031e0e01060b0a0f 60
    0x8102c40c1c400c0c1020390094a15040000d0083c881d0b8101428070801e0402e94000880c045001d14600140b00a0180a6544126038800c0020200d03030342d02246c00b0280000804055000c1c3c0390380050041030341520962007003c1e03505008407205003800001d10444071104c02c22180e112404005d450f0004008000f01440c120b25030b8109842641d012001c41d01030311946e00001c1543e0028507012900394481c81c0608100c418590701c010403600074017001611072080380e000000117001080103106c14101440100f8101c07072030b4039264002910041c416800c11b02d00108010312400c845645c0709244c80e0034002c182110307102c000600241c000700da85460395401005c4038010b441820000140c1480114603000041c1030048280c0360380d500d40481880220381c002605541c0760280c040c00810041e0800e403d0320480c4032500c10081c03024040d03440d0b4038a000d504480e2181015241c10041d04004040c0c458001103e44100c0f0224400c03a0f80d8003100e09640c0d250b046000b85060501c1111001940710344040c11101d054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 749007113 1250 749005863 749005867
    0x18060c050c100e0406060e0312040302010804080a05121303030e03131701021303050a03030c020118020409050c03160306050a05150d03121b11060c220302130203010503160e040602 79
    0xb4503020f9079100304428a40782e0051801e040080c0664000c95509071a0344202c05992080581c0c085145e0785001d240006030000340060009000211450002d098008941c10501d040034400311020b100103008440001c0000608510f41c810583c25005040004107640051818219425a206101ba20511940f0354000d156120201184000e5044514048003c01100e046540380d0502c1c0c1e07541c0707442120403400a440d000400300c100e41b06104115801c0151054440c10904503000c20010300303d2201c00f61038038060b9031561502d41c0e50400c80c5102d0f103c1540b8120704460318604145085510040c1b101d0703403586c20801001519038411541001e41c4000305d42001d00da00903400d049400800c50300621b0301651514280110b01d1844080860144200d6a00c00d2001840c1e0040305407a020242c8a6251b500414499281018040314025800d58070f003182c400180d03542c030f030006041502c8506c0000c800c650f000006101d281000c1c05842d454241b080d1104848610307004510740344d81d10081018203081c0d40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 749008363 1250 749007113 749007139
    0x10b0313060f060b1c050106050405010e0102030c070807060f1106060d0c0312120e010e0627060a05010e010f0b120714271503040f0c031218060c050c 66
    0x1561003494040202d4204004041c2c4440c00b1464035030003200b24480000364207601c0030603000701e4001d00341a80c585564250801c1c0c500300c01951004601c000c0b00d03040d80414020000190f804011a40c01007803550001c1c5422403902d000909040f00880d80c0c1d07030812030301300e2002c1c201034000291580c0213002524021400707a0213040039299440181c01c020030083d0501c1e542e448440e40b0590101c21910400f00030880d102e907400b031035800c031004000e6140c0305800c040c000841d51010045c40d000319a4048102c080300d101d81c1d24029041079011109007801c1642c0300c0040c49903000e040320060141002402d1071007598140300081009000711038040038a04503400c0012000c621501c0f84041e5000c011881d20303110441a9041c0000d200352014500c01d0205964894401d480c00c0f1034101000094070390014070315202da440e4908031804c0000242e0f81c41c1107000c40040002c403034840285e00c1d00340340e0707075242a0b20003848100c1004501581c04801004400d0031a04041003000c100102807502c01ca4001680180c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 749009613 1250 749008363 749008373
    0x91205030403080a2a050c011101020d0903020a150b030307080706290301050c0906040b09030f0307080703091505120907090f0905190b0c0f0f031617010b0313 70
    0x21942d000144049008118002d041e500714025091081d200c1e031070135004071800a141c0048555002020f8500e52090300a8504d9500894051800d2183c580000d840c1c4841c9124480544481c001c003100141c1c000c03090f00080c419000d10610030480e01c0b120a11541d404403001990b0b0340281c2c0c0d40500760940001e8001d04010096102030402030307110061030484107459040f102c8074a203180196000794200800145190350010488500c800e000b0525400e06050404202d21034200328502e540620030b03005040f00b0f140e01040500116445050065551211490014081d05551b4000314080b800700100d0710803a40c010080d01e164021140705001e00b07a5030b0b800d07111318001183c0c1c49803c0540c50502c10342d03480d041170740002c0720cc1030040c1e00304d40560342c6a0342c81140500040b8000b404168011300803070541d508100c02049050710702018681080291000002c1c031364416030301000c81e4990380c862460400e4016800450000e88201623045a40c94007510410030700c03004050b0501d5840841e04801000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 749010863 1250 749009613 749009617
    0x90d080c0c031e010e06010f15030b040501090b030706030608030d050403030b130203010911030408040e090a0606080304090c030903020606040b03070305030f04140a03050c010309030e03010c0c0b090d09120503 92
    0x40d002022114550048882100c40841c107641404082d420180700001711040064560b0480b540d4450030540b442c904054038065114274040c1c40f0030141c0750028981d940e6118042c03207019042001000520318000070801d4644105a4000803d05041035400c02c0344401c00301c160b0f024011517400109480c2d43d642382c114001d103240c20b6a598001c003460100c0080c0d54880c0e01860595040c840100070144540004105501040741c0040844500308014840150309a0141d90840c2002044410a80c1590784c1c403401e86015400c4041c66a10218041000400034000c8481681d580c0c02c041052107090b440003501e4910090900c0e00403601e0342082c0182e0b440c1005a07600454100741900d8072407103559001d10882c1e03c180b082a50160403500c0001035071810300500c04c22258450000d1024042070401540604a00d500030f809101f01e51481c1c0c1c0d980d403800c1c0240c1072105456501d40103000183d10707003103094150140c07507010144e00001c1c402200300d401c040341006440510101d032100701140d1a243d403030340c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 749012113 1250 749010863 749010883
    0x40515030604051005151c03030605130b0a091406120c1306080607080c0a080a06150804121b08030604090614090f120a050306010207050415030b0c090d080c 69
    0x1501c1594200401e100d004150075010700c0320102c083c03006488075159803600f050199003869100310101c0e045400c1c81c904030b80414909209080c0031842654550010701e2441c1000b460111030b9880c0c0020b401d15243c480c0c150f90191010800c00c0000e180d2800070740c07801d490000e10ba1400740f0440350420402500800505104401c014a010024500c1c0326815010f01407900c2024002e10406d0085032485001da50100d01c00e04183c03c83c6030500d020940212207a50015128059140c1d4418000ca040ca804d409622060b5540d0384409505d810203140510298104000c00030810000c84001c0014441440049107900e41040c411512500c1e2100058001d107004200101043e280410b0300d1102d08010310204c1c46201000b055a4007032105000064844140306049903403d02d007085010151801040950782050043c41150f4146883c1c101140469005c070300c08080521480c0b00c20000c00043c0c140059004510744901da003040030541c081414281800f0004001c0c00d400310741b400c40304200f00080341072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 749013363 1250 749012113 749012119
    0x50f04120908010f0e0f0f06040b0a0b0d08120708090c0d114623120c03011119030903050d020a0e0907050910261005010e030a030e040515 61
    0x81c5060000413000788101c40080c4004e0003030600c03101c10900301040c40802801a00301030406580d0759030f00c0e00d40030300c8000e004403112640ea510801c0c15440b0100b250142a1056200030b036103210212a40c503580c9801801502040005010000c07a810003088044003d4400c0d10b0041951542d440e2000d0003032441c03050190000340d03040d88820b01c541180071132400c8800d0403061011080c001c141880d1200c4039074050f620b803402c010008011060359114480b544041e800d950f0030320bc1000b400003d02003803551010345c0003984900f25501540c5403e00c03039038000328004061180352118070311840b61175031000d00c9168103145e0745000281c1814029022110b0014000b081190368800e0381c038010340088850552940161440d00c0001d1020780580215041c00b10010240400909103210485087e000c00b448528104500003410300c9108481c4a81406904009086507100d810400014643c143c4582c040f40720f54040f0800c03e0200350403500e4100342c41803c4e1404120350b99403401d00034400e0030031100260 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 749014613 1250 749013363 749013371
    0xc0f070602040f2309070908030a2d140c01060b0c0604110d020f0f0415260628201804020316210908030a0f050f0412090801 55
    0x20400c56070300600a588407042844401a168050583d4102c03040c031900120010001e140c0402d4600b80c2980e990012080c50091072094940d048142181c001c0843c0d140402c03000080819141072211000e1804480d9407200088000c050710020001240e000181c07481010002d8030400f030800a400c190094076070090700540d250700c21000650b40308001c03030381655003001ea005400d450b0b00d00f90700700781203941d002001ca030004e1407401c0400000d07481c00904103500a50b81d044074075028400204c014000c0189210010780d122804031080039125080c2c00304442a0005810080c05901c807404025004120740c0110b82d00e08140050580140490b0880001c2d801c1da500802e402c140c0424001c0003120a01046048000f00840a00050380010b650240b8107042c001c9a041d86103100b00c1c40c020841403002d984809080b0603d04290498102030820380703801300c00004104035041213004080c204161544100150710b05800c4c414200039014100500340e140c02c04514241900c10310700b035400f4040c4240208 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 749015863 1250 749014613 749014627
    0x417040314070f1409070309061503020f0f0d120c060f05090c04090c120813080a02120d020a032714130608070b1308010207030305041103060603150c0f 67
    0x380051200714600301442c460b0000100c0c00c11104800f2034100e512204901142d020208104140d005000340514201550313010b540001c903a140c000d04e040c02d84400b2030045d00314154018044038502c810041e900604001e80741d174007241c07070b80c00910188582103c1c07040e0b0400c10001084031201c1d1000405002541481c00c60b410a500950000e4007404900f011202c40d03096550038030065440200000c0d2103006101410401042504003003c00a48031741910340ca08600310500c004d4424a68000c030300300e640a15074903002c506043c15205a220050f500800c0020b1300c0c1600250b940205141c000d04100900c408044251402100020401040c003058403100d81c4030031646480c4001760b80302d60303ca01000100c02403007403014170a1b14140c0d00488041d045c124248409980780340d004c13600e4114600400c1c100054441030a1000d0185d80c3d11940d0041502c0c00c00d814000b9030340b2002c0a0b414800c0d0003140a000785135600050190960b4411083c042c1c0b5507941c1480241c1c54000c2544011003aa4001090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 749017113 1250 749015863 749015873
    0x402030c1e07171314030d030b030a060e010c020d090e160e0d21180e15101d1002190203010204080a0510201c1b053a020304170403 58
    0x605081081c00c04580704c501c0e41c0e407aa5008089050b55100d4040c2c100910140c100d521030b8109288585001d000ca8440e002a669403000711180100044c0d4540d41da0800308104950500000903a905140b4010301b119040401200d4140350142ca003200711103015600d42c90326401518035040200000f081d515140c641d600b000c042c04078500345401080d0305040e1500303114a01809075014074444601c01154028104059598030f10000b41c2042404025403807140c8960b6200d07001247e50900301d0307540c0817a03076056076031000039458549100c0748904a204d07840c089241c0d0003d00070144000903410401c2d01401d5001203030081c03060f0341241041e40030b910040c0b02409400144110659201e04041001249224501650b041d038104c2c0c84210540401940c0f07080255108040740c0341806000010328041c01d94042c0d612004140e0692011542c00708000070b0140540078008200b0740c00411400b20303004482e10701e4416804078001c3e01f425a0380031021400f8032100c6401102d59014511520780e440d5141c1c106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 749018363 1250 749017113 749017117
    0x30b0f0601091e060806030f010504050304080105071706040f0e030a0306061b0b07080a0f022701020a0302070b07210201020714070501020304121a01060e0f0402030c1e0717 76
    0x9207030209004200001e80204089029500e62448500d100c10041c2009411213030190090032540d41481a521403035008103080c03040c180918444c600440ea01c1c0c0c40d26402a09507080201f0750740501a5545401840030b8005103045c3d80004107da0000303240407120303541c00080c9981960f1001c1d41c44081508240305405502030401e40c1c6050721022403140e81246580c040b20f00012004144158850108414900842e802500100e001c4008211a100400018100c4c0c1240262003c40f61a00586100c0c40e05502c441884440302840604000000b07528080d60701c541c2c0b032103810114140041c81c94140300a00c02d080d8001c80035035110642200040500078003039008542c0903105c100da580000c0103440c000094803401c03100103030007a5041a00c1c10341300b8040c1020082090b181c4c1e0303242e401031a1a599030300c0d0060340030300320760388800c40104402828003d80c0c0210a003010302442c410404d01a0401c18501a40c0c502034020a0302040c03800b0480d00201d45000e0980018194650b20304007429410035940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 749019613 1250 749018363 749018371
    0x50619150b043809010516050705010906081612020c010608100b09070c020603070c020d260c0c1e13060e130b040f020415030b1005040e1b0a030b0f 65
    0x441000e01c40702c403229003c110440c4000b440701c0c1081c081c420004480740c003001e069140c10505005041c02c111f0242e03880030100b0648122100d80128005010560300004120003501440c0342c04d036409c4c5800c140d170f41c052a041d01652414007a02c402ca04425460640480d60400c03001030081c40150394624010b60f4884129803403404940c1001c00382c14040c24031089c103c0c4242c90175510220258001d400b0301c4103960003d088802000b0f5151a1300b40540c179002c1a02180500c5000a17542500d6600c84030f0782c010104444a2003d06400c01c81d01ca020f100001d004018107a0440d5103c00c8440801036902c03500500301c140035044070b400c0200d880810b2150b0302981c12110038860000c8595212140c41045c00340441009040141180102e00400c4202d0040e1040c244068000102e011b40c0c2c0d0014540080f032980202c6003033131030030104114480c180107094000c06054a09001d10541c40c0c120030386515001041c5511414103210f0143c056840c0c6490f1402180c0051078404075041c0040030701d0714850f08032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 749020863 1250 749019613 749019629
    0x100f0f2115080c01020d02280606080303060f030601050d030e1f081605031006180306050901090516080d14190504030204150501120e1e01200304050619150b04 70
    0xc85181c0b05135002017402c001c0120941d002d020a50f4200171070040c64100000e451100540d440e01c0c0c000024454800c0780c2c081c0c00742c0c800642c0c582c54054200290440901c03c0315000b50041c600400c180d844804c01105e559606092025a050105010403100091416490001c03c2000300b00c455541c0c11020351802030b500303003088540400c0015804d982910050302c000100f40300b0980d042125610070b030ba521003c003181d101d42c41c02d110f17520748400342940c07020340e04980681d544a4074002001420444c0d14283d2403082d080c980440c1ca460a13503511802c0942704001844800c1d0b24910803a05a0402c50745040450941c002c19250384500042c001e070400e0208034000d03440c140501041c018008030480445205a460208031089405148003501ea0300c035080302e0301d10a690304000c2c403040d0403405103900c1e813a6100005411050200c0b481d103080030a400d0056440d01001403002195000c501c4590004142041c08100b4200500050040c100803240e181a0888a1408030303a00712110000c1080311900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 749022113 1250 749020863 749020873
    0xf030f020703051c02030d0f1a0406230109090908120117060106211406031c05031f05100315050102010b01020a060504030509060304050c100f0f211508 67
    0x20000c0c0d9031841e060201404691202c030240c1c0b846028034144c92a032100c0c500c1500c0c14902c010f89903070242c410740658560219164080040116080c00f0000701300401202c080c0304071072901c9102200051444105484000340c0d0b500a00d1303e0340130b200d0403001019156000c205502280c1001e20154102d0803a00e1000700200b4000201c00c2600b0b601c1c07110708180c1d040035008a03480d114055074502c420316055003e404072a81e80c031445902c1e0b440340c685901c81c88190b0440d070340707000340405051040d5481d404001144003441620000c0d440b0742601c0e07000803c01c2480d800840880001505111582c0c8080e91141d8909004280e41c0d5058100505a040141d10102d10380c0d00d407001642aa105281c0d60b81c0140d00104843c0301049042c0c20071a000303402400c0c4507140201c0ba10204010382d03c1228207490a40c4210f2000d5818100603112030151101032030590700d00b501d410002405600b1100394081009086032020207083e515107051408102041c60030846083c1c104c0312445051060712419400c1d001d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 749023363 1250 749022113 749022137
    0x5060601050a0e0f13060b0705010f05070c0b0a111c0c020705010f0c0809030d05120912070605060f0301020a0f140406021e1f050609060a030803060123070f03 70
    0x590240c4118000a03200c3c004401c0080d42441480c0d40802e40d1103500c01a4000543c02d440d540c1c0c030480010300741ca000000c0d80c1e01c042e41130850954034401007000e0010303d0070082091050703000d05c06004156000d105800c00342c540240360000b070040c0d0b060301f0b88201000201508180c40e0791a040328646d6120000303200c13001c00da8406980346c4400f4810035022803d00c0f091041124852081651107520450065003400c0b154004203191580910412021030800144c41c2600341400c040d00d90300091703e800810f1440300c0c03460074080d2809800c0f00101015100c0020803140c3c0c2d101202601c011501a000310744502c6401c0c0d004162800c0e000540c004070322100c0175202e90702c0c0c03440100c6055034810f0300100350f040030101c080101d151381c200183d903e9009850940141c58810401151151002c000108050400304208040c8190242540303100e40040c20040000404540c00e1304d500c0309007420401c160070708080004404282c2251075442001c4001140810860039507034894081e8041d03683c003210b640c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 749024613 1250 749023363 749023367
    0x40c1d0f010503011e0e0903040602060c0412030e030309090a020910050702092e080a12030203040c1a1b010f0c0804110f0a08010203250e130c0e09100305060601 71
    0x3412030521400514104014004c41020010000e180c5144103000312003c1d58641d1026007061058a6020b0b0941001400700180e55042040541160441d0035403407a0a14020000c005009241402806e02c4440c080e000801d54091003510440303000030380a1200d502c2c2c44c2c6008070084d0b02c01032020303100c1c0450221421410b80b04100b40c4800d82d03405012035603c0d4031102d1040102d8040c01c001911020718103021001202c0c0305a0703240c002081c40000030b102000184c80c00708841030f540301e410720070540305008000100e42c410124404135001680030b1030285d1680c1950040030321624407a00c0501a0300541102e02ea801507101700130b071118101041288240b1180100d95001080d28007510340940e40700105403901c1c007681816a4002c0040a20103004c0e0764505242c03da030011035900027450080350340d00381008420f1807140840e680514100459a944400007000c20804900b0011895554404a02120b00408181d030028000903c113140c0c614040681c0381d80d15403d40401c40c1d0380e000d0040481c0c0194 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 749025863 1250 749024613 749024629
    0xe010618090510090c0b040605030a0c03090b07030e0304090608030913140a020a3c050c031222141204051503090a06240b0408030f03070e040c1d 64
    0x80d4008042c0000c0800340030403c0c0900b83c1407009542d608014040028aa8540b000401c02410f040d2a281d44915190a007041150060007003c0245402e05800c0c2d400518041003250340180c4504001550880340d00d069841c500030354000c041000c0c07400e000446e01100010142c2840d110445a0650f04e10000740344c241503070880e00300341c0c400648241c0841d81443d00c98000d000d400c0701c207140c040361500c1c04011856250300901b0700360400e8000341d12000c900c1c01d0b12180403003038804203003441031074401400c1c40a603072442003c0f042000030810740041000c1510740a01c042c80c02041201c910010031070340c00c1101c890400c40c000a10745200d4201e003100280d01e05000e0341c0c00c895008006019421301e20383c4c03500300c0d540020072800740c5000750300700030002500902c60050410703245028040959090f40d05c1d5120041c0079003281038000814003080000103000022910706000002a440c0c4a440c0c103541690340f400d2400c4000c2d8440e092898400d00d05a01c4414042c50b000c15051120518481e6010303c0512 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 749027113 1250 749025863 749025881
    0x6090c010507121e0804150c0e1215011d07020f0a02091909053a200a060b1c210c05030c0604030e10091a04090e010618 53
    0x120310240402c00101d041c501e03094142d01207900344211150305210041d079826581e0495040440c41417401e110910a0a1401c4441c5081d6000b0820101c8a42c40004e4202c803110036041b481840d0000c914035032503405010b111400444210818440c1d40c44120354008803d052140492052080c0c00007182c41d0302c001820340140581c24094900c14160b0f0b0280000034030f00034403941d903000220b2602030071000e541c0f00710309013140160042c2c4905e20415032091501740c10801c0007c000c0c0f040c081140880c4c180c0c800f08964801050030000f0181000e61802008024488400c0000340241c04500042c00b010303800411500c5c408484031541401c2507800c03900c942040001c09820059114000700c008440304000ba0404c2d07200d0f00b00813482004565a01e4955800210540d265800c1174050204154012010b4021040100c0c0c402d0b00e101c41103d40182103000c1071260421148024900ca00158405402c5401030310301004107000444600f111180640312034442c0b070042258158a81c11940c0300740c4644008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 749028363 1250 749027113 749027117
    0x13090605060906091302041a2d041e09170c0604030906050a05120703020f130302090609040203030a0c15230a05070225150f03060506070804030803040501060806100806090c01 77
    0x40881c1907000e000061500c04000141e4188220b2402380a40d1542c4190135070081ca94200404101318040007101103922000c0c05002e60b007445041c51804c0c24405015849209d040d0001541c422182805c014400c00300d580c1102060f000244e01c241c009001c00d03994800d5000b0313229800442c1d80ea420481d030512170b038480540011002d101c01e0360305000901d00c517a00b1407890b01d00941031107619580440c0550169140c0036401e070102000b0000c5040240d185540b11504840401c0c00d0f14141d008243c1720704c14000c40400300202d90b03050000700007004203a20303e043c104540400032002441401c1c0302e400e490807003445080741030f20300051881c407560041520079181e640c06406e104c240c06180c110302c94a00b0300c4000d099a8207400100315041c2940c03030100b0b03a04c21030f61382640ba006101c601408031801a00b01d14015941004400c010950010468080702c8c0e0041410380c0c2c0359642d081c01030040519070000c2e1031034041e4a042c816145102c0d0030b4141a0380e00d10003034800f0364941c420034a83c1c07004081e1000b40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 749029613 1250 749028363 749028391
    0x6050904080d15080709022d090105070c09050a090b090c01020304141f02010b0108090f150c07020d062403050d0804032102030a1a010c08091309060506090609 70
    0x1010001070f007201540000d5014400405034a80c0c02c0c450821460350095003040e5030118419803000b9040100c01c2c00840c400620100007a4030100001c02c92055280301414000001040b104001c010f1203a40020422010704000030700306440345a018011401080d50f49060010118003840b5000c41c0d08074401c0d0b41600258038041c5441e00c1100c15240605005034011020000e074008215450501100c0322125400021000e139620700140c014500504850b000341d1100c8244406064002100c0034943c0700d80d840c20781c45036103141084505103e041c00c000d41102090502101b0001d0030f0b080504c0008841112050b075140f541c02d0b14801c46110301c006001a845015144c910b035001d0790b107894005029162502803103968101c0108030300340900d199581550300104001c81440180310311880c2e9a1024010342c0341002c0140003c0443c540e000c40600000400101c1d10300e15910b000c00032019040c0203405001000c82414840018801204d603140640118000504079140c00505140b080544840d400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 749030863 1250 749029613 749029627
    0x105090d0e061c0f0f1b0206090d020318120d0207030c09110306040e240718060e090603100c0203070c0503060112060f2009041a010c03051305060a0804060605090408 73
    0x15001d00300315110501816640c0b04e405a00100e80d000740b4002c03c00b40c40c10620303c420b4a21b0020300c1e0441c02440c20002c0d801036030b410101e1650101c03c64044002c225002c000c1d1410880000c3c000d00e01e540c6000c0824400d9440040010f6000310380301040f00d000d544c683d8a415991038030601590300406107207410400400004442d49055404113000030100b404070340240c4c042d404400390070b0021800000f0344255a0007045000e0303a01c07020315215402410030500c1000d1420002401030301d692400548502c03091000220103803810003014010f490602011b1061800c5004003949135403240c8030984075100c0c0640045010b040000f4414100d841d418084407044405448413002010110340d0f2081c1c0586501d2040b2400320050014000e44800c20015035441e2500c10070403023103135a4a14034049184455038500426a04000210440da80508180b9914003901c1416080d50b01b685c0c00c010307030240740130940c19589540100f11a1040b40326070010450141c5072420030031382c114120b03030003043c8a400704410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 749032113 1250 749030863 749030917
    0x507020321040f020904200402090f0913020303030c09012706050f0f0307050a080a0603020906060a02070b030c1c1407050f1c050901060906030206041a0c0105090d0e06 74
    0x41c980c014054024250000c2043d0700041285a06442c00d8902148000c07a2405000b1010042c1c0d40c1110b080750114640890140810048603030b0300310a43c801c00c4858001210130368002900381d0a194000c0c280d03503403840c00310300007207194000e43c9216000a8050785084c0c101d40002d691421403515060344c0300459441d001c401c03521580300107840c442030103080c010350400c982004040d40c003514083c2c9400c0d440c0c003541c402c0105590702c0100030190762800c1c00e800f04003684580030000c2d0848410f0f61210340d42c0769040000e034038000513a8880c880440d40002005410111600580074401c201400303400c210000c19244d400f50303405282c0010b1144454170100303041900034001030030703660130f4404858200a01408010758000d000b0701d1200149855004129605400707106040251a0746001081820704640100b2014011402032054290480e40c002040d02000025a406a034900000344403c2c500148503070384804000344400f020400c01208405c00d49000410380b00720400d0841034416901e950b40e40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 749033363 1250 749032113 749032177
    0x607020d1202070803040837020f0105090a150809060106021b0d0f050105040b1006020303010e0702010603170a080709140f0402090a1403070f0503100213171005070203 74
    0x181c015441050300014200f102800a031008043d158050300d150801e000190580016103100c08549000051301643d4802e00c1c00440035181e03406480c0b60544001d0b40c001607800f8800d46000642c001c464510020356840d07602a5552500015074510317680ea1036000706c1d195102001e0168030056006405110a84040a024400280c9000304078400c11040d0391145010904c41c000281e4031a5100c1007004103102102c3c2d90260841020700f500740182c0d140243c025100e00040c01440c0e00c0320340082c0852003480c030075080000916008469040348040211105220b54000a03c03100400e41c07800005000c0b6024141a004907060403d28040c542075040802181e1412804516407260723080c480207206450f030b0814031001c0e06541c00c0c5001c140701e46208140c03520f10700e58031180d280d104082c0140865100490b06080103640c0100150715182060f620401c00070403a0840342240c2690945410b42c07990026042840604088040105441d600d004980301d200d00f4880d010500686004000d4409060340c1d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 749034613 1250 749033363 749033393
    0xc030106030509100509060601020c0a0803040e060d020303191d090408070203010e0d090819020f060c01021603050d0c03062403150303091a0a1b020609030d1d0607020d 74
    0x7055403c1084004c00c0e100c12200c040e900c0840ba83c2c031003020031450f540c04100307203200c4020494003c1e150364030b040c464070f03500d00c1540141041800d507035000c18aa07444203004804450350040a0306d44543d42442e06091914544c408840000e55480c280c03c0d401100d0f908005c1c40e540c0280000d60725645649551211342c4c01008101e81541d60748042c07003c2c01405004103140843c4030344d540c82131289401449460f1580354070300c0c1409805405030040041c0e0741c01d0a004200700c41941d94030340703c80312000c8040c024003901f030f2082145185001c9003810980e116000b42070180030000104000079107000114226120f9001e0107581d0f41c1d4141815800048010817030314002420700e000300b00205240d0300004140308581c02140845e030301c1c4200780000da80c0310682182854000400c1400e0400c00b00f401080d0030781510106901c02030b41c0c081413040d5200d1000300c4203640e41c080c0c119040551a61001022403850002c0301c0c9075040c24084c0c4854a103850821545443d4000f0094001400c940e207a5105030b0441e84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 749035863 1250 749034613 749034631
    0xa0e010803071415010611070812030f06010c120e0405010801092d02120a170f091c0501240501050a020330040501050a0c0503012103120f0f0b03060c0301060305 71
    0x210f0785801000c13080c80c2e003901074580741e5105064454815200c13880e1410070f821502003a00b0200750781030304a01c801b094a52100c101005242662a01401030f105150340600c0549800052140c0940071500501720b1061100c00b9035040000d6030342c1d080c0743c6080703510080d4001c040c1444000045044120720290302600880440c03204ec0402803503001940d030140451039062150429494101805540d0b1106084075114082d100d02e8031290b903200318a103200c1c2600321485041c0d4900d8403480901034046100c4429400750081180c10f1280c1d03140c503464480014003403003c002103100850705510400a03580174900030380040d81030500c5000c6451141d81c19040c003c1511582c6294210350300141c0c01910701440c051000041c107424a2034940041c0c0703044144c600140402040100000b048a840000704840340040d00891410185812030304900041c40c045040350800181d52040342a907070020b10394510a030b1701007102426010034145c84020841d01d01001c03c0d000d00041100c1d44c02a0071495200c9484 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 749037113 1250 749035863 749035873
    0x907030e010f0e060f0402010c0305070302100f05061005041508060d020a170c0a03170d0609020309030c060907030b0c03091c09080f0a0b070e1507050102090a0e0108030714 76
    0x1034900303800c440240a81c503030800d0b00c0d04848500002c05005a540101e10000b400181345042c0e00003800710210320400804024002030345005040c828021588198003801c07090000c0300c407043c0541d0140100340e43d1a4403501143d8941d61846000b801158100c4042000980c0700c144281410340c0c212400800341034101c80c00f07080e40d071b005981da801044003605185480c40390b948500c20720b0074074000c3d403116840e004080d0f41c1c1d814000304694503200c401d1035801c00c1d41e29503a40340d40003c1501800051340844102030002c414810717555008000381c241d411025040341c07141e0b0b450768295651104184130180024040c00c2c045455064004010b541c8a500c40003140d0104034000111683c1650142d10a00014806ea00170312400703a0601c2001040d030190f100031720301c450150310365510241c03001c2c0a86061000c80042809640c035010100325000c00c6000e842900d40d00c40341400740c081c6d4070800c03005201d90b4845001040c00600a46224103131b82d03085004500704546c0f5940c11078000580c0f14030701114416 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 749038363 1250 749037113 749037131
    0x50307033005161701170a080c1609020c0a170705060702030a1d0a0b07081e1b0d08071805090f09010509240c070602070c091a0f10090509040803011505090d02090703 73
    0x1600d000b0322800303071218020311310544a4ad15511141180382c001d00050b41c0100718264442000184102423580c100c04804005078440c000e4864603c14494001d266006040800540076004000342030310480b69100c0010320705c51038003010000540505159448030301003c0c2807112240c0710014242252240d442c007441c0007104124540d2004418202201030540042c408207807110400b9650a03c002c80d50081c11500c011400280465000400c03410400c4502c4c42141c40307440211000000800004d0b01c8200385040c00b80c6d0044101000b00c481c00700c03560030800428403151000441d01c0503203c0c001c5210840c030741c14210880d4100d8000e001c03001c44400c01e010460101e0340c81c2c401040700610500080d141d50345081006070641d480d00c00024035021800c40c6d598000d8583c0f144240d4401c1c0201c40120400c2d0080310196006045900115002014a030400003007060180085060303880c0391800c070303c030758852420442d164400c0c0841542c02c10510406400182404400160485600c4c02d002c184056 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 749039613 1250 749038363 749038373
    0xa080c010213270b060a080603031318050912030c07150216021003021c18080307091e05060f0c012403061107050307033005161701170a 60
    0x200342d0f0028030002c0c0c124860300c80c00b8900c0107006851503104a0040c0b000042080000b4000d01038090304405106c101000504e50382d50078011150450808003500351075a484200c854503201075410b00605441c50000480d58101001a6019402813001d01451544c2e03030310f200c1c8003020f40094400300c501c09031505180c4c240c030750301d80081c005c070000312900c1341c404500c140108001c00450703141320b40074148104407840b0718045540b00c0000c058036855012914070318100317a5406903500d02e40c02402c040c0c000301c01c0c0901c40343d2000700c0404640b94070890444002c4507040b04a055074a0303211301c42e4031040070002e072180c0d0300005000d0071a50b00c064000207185600714560b6a241c1507044030040014080450910802606220b40c1c507201520340201d905100c003ea0782c05590f80302d8280041e0078800c85076642c00d250038000d030041c5080000b4244d0480c158521580d00c5c1c000e02002d4400424091400c0602000180318020305a4400c80441c111703140c0ea481d00324241002c019441c0351a609002c3d80c0c40f140c0100d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 749040863 1250 749039613 749039647
    0xc120f0b0303041518030809013902030a0506010338061201090f080301082a09092a1503092e020705030d06050a150f0932040b030a080c0102 62
    0x1030107100c0a603178039142c2303a00040c05080c0300c182002406810b00d5a001065060008040304a0407450152400e08840d000007031400c0d003a0311009085102c3c0c4d000200401c802903100d0504402e038107450300c112500c81814888900c0d800141d076401098144006445441c0101e554900c038182c6800025032481d060711000c4201061441c02c0e20412000001003215200c208403010030680b030040c5140321141c2c0c421060400125511f1524410300d03003800498800c0a0a003c100b140035090500304082841146413002c1c2040180340d600d00c19041d4a005100807480401141d100301a060b01074940c44180c00d05501081c6440f01c6106804111003003401030041c10351004000c3c0502800096440d101c46a0185050300da640d04210b024920102d01041107044007900306c102960b080c00d1441881215050031190660f9035441501c1d12907044424640e50b603442c0282c40c41540081c140c003004500349074184410366908a0f4103d406621609150000c100150040c10030412071800261618a48a00d10140c00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 749042113 1250 749040863 749040869
    0x80f0c06060118050108010302041a0a170601050a03151d010908030f010605040e0103080a120f0902010306050603060a090902040b06041e0806041104050a0605040c120f0b0303041518 80
    0x203a4492001d22107503603000501800c1e8546104a1950742c42d040000003404094107210083c0075540720640e900041844180307420150601412030102d580e5940804101000c4100c80300d907aa020307000c0040b40314100f0340c10010a0700e802c14000e88200300071301c008500030841484000070b030400001c031103505240d081c0150202180103519041e203c3c02c04980b64918071b103042c0c0c821003d000c0100030400100382425600c03030450f500700c040700c1c0d244c0b07465003401d65140d602418007a01c103a14140702101000056409146203070b00030707030381040b08584550a00006c0c0c441951010780c400c41e054000c001c9452260407444150b03201400c045040300b03921010030000c0e0080c1d081000d03007000700410381c182c2602c4940200e000701481001424541815190381c4048203100b2100c50044e602c1c1e9000131a80600c03500000020440901f082182011005004040b00840c1402d038010509000c80c0008107492070050020401006014500c4c1c14a00812201d00307005003494041400741c00140008082058040c250003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 749043363 1250 749042113 749042137
    0x1b0e06060c010626150f0705031e0705040914070518030c061207020f01050705041214070e1f0e0105091b0301080123090d0f1205130203070b0307020c010c080f 70
    0x4a807044c0c28003078100110180ca41c02c1031040381003003110b032000e1003040d1031b0410300504160341e8030744038441e4a610001c0300d01c038844117102a030b005001c2641e82c00f0008004a0b9400c172030030000c4404440418122440650300302c000500c05020440300c0786180341031002c0d442d07801000c4030107140005000c078005070003001480030511109410803a0b1950188039050310000d404000700200d26158101404901807030080e20100b00324068030b01e0401411010200d1201c0083d001c54519664401200c903d60604440078201448941000d0f114820030342d04020130345929101c2440160300300014403013030860023080340c81d4000106030b5002514405500441c003818090300082482d034100c01085900c0f200442c2e00c8000b400c089020401102000309070b82c001e10100b481c1c0301840d444804c40c1100d0050181c0c003050002850441848800b000840e01c48030214806e5055600d401d81c0ca451281d8140000c482c030001580144d600d0400c070350300c01c07003c10b00c10522440200d82010b20010328180503801000442d65 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 749044613 1250 749043363 749043419
    0x3060a0212060108040c090c11030c01051602030a02070e090a0807120314010e060d02011101023408040b070309030f0b06091f030b09010605090f041b0e06060c0106 72
    0x10107107001a0070306602075000c0c00c20040b50b092641e40c0071100b540510030030260964031000000098400c1e2010341e00d40072100c0851f5100d030003204216000b0642911182c07400210a0907044d991030020080e0380c100c00643e000391000c02d01d02604000308006c0203001078040e0190180d41400581c400c0b010301110b500500c491080c032100340e003010301202c031540c0c42c811030854240010000780180c0d07480340c3e03800340003903500324280c2c810703440160303003043e10011798510307030350002c2004822032081e81820319003a90000244080010070728194024034282c0b81300030300319003420001800f204034030a000303100640c0319280c549030303044c0c0c0d81c0c407030030841a9951800c442043307103402441481e190201c01c6a130001e00c1c264403d01c9803510b070006000b0710504e51100800300c1c24290001182c1e500e0a520800c02490064108003413450700270366541303c11034200c80c1155100303c640e543e0504000c1c0702402a06403240d05003925425218401041455000204031040940d00c0302c0e800b0810b080001ca0f000f444c0490074056031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 749045863 1250 749044613 749044627
    0x1e0114040f3c09020d06092f0a12020a03121e030e060a0b100c020609150915031b07080c0106090c090e0f131a011d091606180503060a02 60
    0x54082032010002d030030b400d400c109522015039241c00c41d00341c400750b108900162018503803401100104661782c440c00003010800c5103600080319804004450042211610302161303d23400c000d1000030354000040c2d002540d1100078000100e000444c2040198241403074801400303e8030ba0310b5868510142010002034807034032003d0598000b08030303c94002131f0329001404400c400c040030800c0e20f00d0342c229810800030303d10001400c4d502c60b0b1084a01820303000d0314005921400791001c164941c4a0100706024429070030a07071003800f0104055030300450300b101c1c940340c0d83c2c4c0070003604042542040e0403e40d0a00c0c42000403c0c810300091003480018580c484011500c0208008003501500140e44054407001c160b00400c8020f40300d000c5a264080341c0c4070300400690140d81001d4143e01400075010003103040d0103002045e5000003400c1c0c0760141001ca2200c000079610040d206444526480407801d401d40c000c02d041c040240100c2c1043c0c000c580c110341c000390b078a950b4070001e880d101054440151b0b45900042d1a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 749047113 1250 749045863 749045951
    0x605090304170f0a080306190e1e0108060a020d020c0609011b0c030206060603040606030231060803090108041e0b041b06050708071a040b1e0114040f 66
    0x800038100745001070070081810182c1c43d42c840a260310010441e0b940000000c00c0ca60b16941400343c8a001004d244403240d80711400305246c00403c0c2c4446c05016055460b01089074150781c009070507a00700c48083c10313081c0c48070704482001c1d40068600e51440c94080c8021983c090702003120b144620815800031403815a5005000300d200b010094500c100300030781d03841c1d40100782c00064440d01304000790b030710a913241d40c1d500300007000340025000254400c10746903120207032070307020540c154503604840d29940d000868420040c0484545106100182d0818000701c0c1742580520800340d80580108540e06c12100c2c9049900c0003441800c00c1250b0080c121001c3c4000d0007189001e13044a1011000100030441c24144040c0941c055040000c0c0301c030030001510010400000b103425000200820040d030142890300c2c00308c0445408a0300e1010001089101110b51003c03a524039049800c800755038210b003044403007804060034025812182e00303038440303400c031291001c821850201c40c8003d224a4009074104844 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 749048363 1250 749047113 749047139
    0xb060d050c162012070509060307120305040603050903070f0f11040f02071a0601140d020c060c0309010e12030601030b0301020f04060c031209110108042a080d03140103020d050a0605090304 83
    0x340b43e00801d0426012809130000040c41402d685080707544907496910300c4000380c40c2481c3c0d90408203100c40002e070354004060700a00908142c4030300391024800703540d03140791499403406050800340114000700d40380340c042600d070850011050301402d0843c0008400c07401241c03d84100403210b0100700c4c0d00041800c01e02480f0f00d100f111443c948032600005081c40800205085d80c20f00030340300100000100a981d0b80c00ca50304840081488205403441880d1030760041800380c004490040f410350900c41c00c0b0180c0300020410742130503104900b80f1401c6849031b40044000b44942801c0941642d070803c4820710588104c0080c00c0201116030b00e0440000843c074004100d000400d192408a030308046440c00055902c0801c0b0041030420302c0c008169a4480c2896600c1200d00941074031610245200c000780042c402e44410241e5401030111000840c000c00304408031203112503120716003446100140014a000b40c9074580c1c0078003c00032211500042c1d11100301701c50040c2e40c1081c3d69403001030200314a05c18641 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 749049613 1250 749048363 749048423
    0x50406021b10050a02031303050607080a0207150b0a050d05031308060f06010e040207060e0a050d02070501020c0d030203070b0c04030209010b0f031927050609010b060d050c16 77
    0x41c03000900c92a03101240d4070800041864060000c0420703440800d40c400c00135103e03001c00020040311102e07a24245140c56400035079080c0001510100001c0565a00d40201d405031913100c8500c1c1122158000d04c84024078016054651000241d2400903032039541d0100f65550320b000d2806541e969200c1c0c5200c016009540d84514115000f10042040e032007481c1103241c0d480207083c284290040404000100207100c1d00c480201014079200260768554000102c20210383d1044007210000c0c2c1d5824010f076036400c080c1c0300d524010384c8402003509040c10b003e000b0b004a14842e0046a040414513a910404100111440441e0400100d01082503142c840306075030040603280700192800403150305045c81c9100040044d0380400464003690700c641c14076800300900da41414100d0303112a803105a80400d900c00c0c94400d507014401c0701d000c100d00c035070184600b05041d0b000404092400d0a051886000342400921401104000b03011000c045881d041c5855003e5100748840c048503c003101c1d90441c0d95000070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 749050863 1250 749049613 749049643
    0x20c10030501090e07150311190f0216230301060e1312090b0405061b250f06082805010f0e1e0606160204020f090a0803090d1e1205040602 61
    0x55003003000c07031001d150007501b09043d890f000c10480d400c500404807c0c4035043c0d10307002858110f040e041c070b010fa1083c00006003a0803030f801c0d601000c031654000c104140080c005c00032411030300c400e42c0048055080e400100e42401500200703c2c10b07030700e1200c141154021540045824190080384081107500e11103814802010705180c1655800d00c56003109900403401101d0107100c002a440345107103460b12030222101c0600c01100c648040900f0b02c826070280c2400d464050101502e0041010480c44c01d42c0000d6518981d00d001ca141d075100c0e580c103500c0240c13101c0001000d4007108803104900d402c0c01128041c003015442d00b03103034070710340120b11781003070300081c5210020078140f040f0142c1804000c900790303001041114507a4a8488060903015011b460b4000207620510002c3c1d030b40d8101441c0c1c0003030700000d0001c503030b0b03015840d40d10300d00240c40784181e08006071b00c00200e45003440082d034200d84c0c00200c01405550a4501d207102c1d510b20940e011441d006030049000881d08208003a810042e44041d070b0546 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 749052113 1250 749050863 749050873
    0x302090f0c0a08071808100e01050408092e08040b09011a040b03030408071706090a0f0602160213060f0503121804090f0804090c0302031303080601020c10030501090e 73
    0x8400c1c001040d0040540b118104041c030008555414440c00203415008010f41c40b00d850f85030746903400341d520840303111014401400c1100b43c010404042c42150301c20341e0000081071411515204010140100d1003448021100ba92910010b220060003414400b189c80d84a0342c00b2401d09040c070700c100d154001e28000700b5a052004001d80c105c808202c40601c010240d4011450360007013000030b4214000c9070000c40311403142d50400a50810b414152102001c41c0105459039521400480e64448001407800382008280c181d40c6800079031958001c00c01012007880c0c885980546500145c0350320230810b0341c0140303951240c0086c0946075881d507004004050850051801d202a5000329119000301c81d80000c0c8007032134040003400d58980360854061254490581514040c4030f00cbc05c00041c1c1c20030b0040c42c01151401c0d0102862038040d1080324040c8a441401659030b84907590110391444000701190304501030410b8012098560840c285c581004a071004109513040c507600c60105d981c51036510b0b103540d01c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 749053363 1250 749052113 749052121
    0x20a1b2004061a04031104021306080a020f030702060a1413031d060304120909020a09050d060b0319030e0306011d150d031e08090316150509070302090f 67
    0x4148010400c4408080020a011400150007003400e50701100340c54005409082c404031006005005481c480d03e13074940601034180c01d102c124002c450501502602002c403d02000340142d1900f0751002220001600d80071074090913046c65001624410050f0780f000b424820096520f0045409480d41920b0080040c6050f601c0c100309900030301c00140030b024104403440c03c0f4850110f82c1581245010741066520f08291500c41060340c00207140000062103404040f40740044e5008175900c55400f69901c241d035508110820600800902086070304075640c103070f082d41503101840128908045514500002038403409d024107103400c0b05001d148070340c01c500018003028140f605600840302940c030482102d69182000500304158803403129910042a114500c10144e110103084802c420400c10000e02c17a0350301c50140c4580c0e0702600c0507400d640050000c9009090215200d001041c02135803021115216080c503034003110402c3e213000c1c020307070000041071040d41031070030455402208044a10302035280c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 749054613 1250 749053363 749053373
    0x507030b0703180b06191e03031103040e010b1c09061a04180b0603070b071209290c010207080403050303060406050111151308030a0605031002070203060f0601110d0201020a1b 77
    0x784c000c20080c49180d28000d020341c1c2c010070905032005007a40c4c1100c8560010550b07803550b4901154881280018522482040c4003080481035800300c03a50000c603d5056400d240150390300b030300507650032007000c10200d0200700704440a016541d0014080c0100084000d464030520040701000460540200e040001095042804241c0e540290740c20800424150700c46000290900d02d8541c4020f030340d0600401c0841c1841840b2213030b6101709001da02c425507129601d45c00c2d000807218a02541000c1101400e0070408058140020f2004162100005103024002d40e22083c1c0e5030060f800944080c1c0c0003004001c8c0b542002d118000c00f40c082401c0051681e02d02d00403040d40d039007880070b546154425400120304401c025210030040030b5407040901d926407a10310306c0314005201502c0307521311a101d4040b00005403230051084900c01c0360050098003640c0c2ea20f0442d400e03210806007206040080c003c8969a00103014030000701d103541c49600240c0c0c1d424420200402c0c10010b22410400f0001c1d1071940c0e030020f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 749055863 1250 749054613 749054633
    0x309060f180605040804031712010f05130f0209060a031a030a0b0406020a0309060908030a05010b2a070f03030908010b0a0f051c02040509012004031e0c030507030b070318 75
    0x40d032040c2c011070340390b685107011a024040c980c001003010841468140c010420107001e48640c041130a00220302d03030703030310546603814034068818141c2148031800405141c8150340c2120f8414225100c01601d04803041c0e010814903441025a0400030b541d90519a41d540c4103554091040ea0b001c8001b4410107181d901c8803444180098402000342c0d03030005203406c26034080d400c03a00301e468100004004002050030000002c0d8000c48080e68900d00e008000f00e035039402c060540c0d9080c0c4442c800c08452040c0061128800680001440300620400c41c00003116000001804040c600ca036503030400b502d04c1c00d00f6040c02d40e0700413605a413041190713040a0007407141c07182c0b00c4021200112030317800204640940c90515001510f1020b5001410a401c0110034034054110300701822002800d0400c404004d2003e003407038003a60000500c8089450121a495240401140e1040b0302480c0884070342130341d03542d81c54580303916688100c8641d00000d003040a0360350184950103c1c4481600405c03044407040c0d48161000e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 749057113 1250 749055863 749055911
    0x81501020d12060503070b0c06070c05031c060b0d1d0c10050706140408180324060a0803030f180c0906150405040501180e281a070309060f 61
    0x7080792100c00b01da028154102c8001014040c094a0340c15441d88290440c0e0352282030900014450240880c0c5254442c03004461442c0e0800051410110780103411440c2c60701a0f00c160054130703101c1a0101d030b007181410040000e08051000001d04505504021620820203a07c0a041d1303044148081e940380c64000040803800d84500c0c0c211b603100042c0c44d001d0000c082940462071381c90001c2080004000c3da80d002096081e042142404403800b0131400c01d59550b074107041000b0200019407020344880044c03500c003508400000d02800c00291038014041c51038000b11000740f034001000051024034451b85800b180d0380c04409000c1d10720b0600c2940410807000c0c1c050003e5014400c111498401d030301c41c20081d5000742038020402c2c045035940f00003000982c02540501d01241f89454603032050084001850040c4480231031103001c1e05c01c1001d0440781c0e0449018000c1c4e4600c1c9041d400c0310615061f021030a8842c103800e0310001140314240c100030040f211017900d140d51304c6280028101c00c80d040c0d00800c0440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 749058363 1250 749057113 749057117
    0xc0306070903020607150c0c0b0a021303060213030506070518010806030307320c0f060903060705091c0308040506090d12021b03030f01090b0d081801110616081501020d 74
    0x61480f01b407400c006090000070400f6680340c42e010448685540c0154001402405051405184d88800e1101000c900c00d05421040d090b017141c60400008180d074018201950518400310035150762601c0c2c00f410020100c80450002d40d00007100815404010750f041c200010a1801c05c10906c0c2c9803010030713600d10500b200540044101300e1458103c2502c00740c0180d0340481c400039001c030680409100341d61198901c6800d8803a000000340c40449080c80020346a103031030014010142c50725503240507112544134042c61134001401a01203910001e211040f4042c040c8642d0f200102c500d4035092660619101404201054000240340c0f900c00b41d1103e034500f0600e03001080165610000060800c100c0a181c1254585000101c10040c0e64043c0070134050480361250400c4c031440c0011030400085218550380100300001c02d01008402e8000c00459008082041c1481c20305118a07041407464400c003220985050318807a05024484d99011070040e030031110105050100f4101d1130f0010751141e6402e824902 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 749059613 1250 749058363 749058367
    0x60e06010e0d0516080c0306060f1513030804060e030f1c050c060a0605030708030906040317090306040c060f02161a0d0c020304060306120b150d050f060402030c03060709030206 78
    0x1469890a412030b11841e031000407903c2e040e030112103254000308244500a80c50088841c02c2c042c83c02c0c0840e070503200d44d03c01001d80403c1c0079803400f08000000800400119400c4c1400205100210408000d001e036000b001c90301e0301c032423500e40c0c014928078441a0450198015448030510998006604441c2d07109a6894100e01904540201d0381809400203070386c044d02c50841407014091042e0f000200751101074003592082500c03003002aa5a01c1500e0025800202c10002080401c5e10400c40d00006000190440e19014410001030710700181594161100c0d101d41404100d5550821001c8203264201c3c005001d050f104003414003500c101a11a45175986da40030100c2900c0803005080300d140174a03980e0100240007078031500960781d8019001d4070003c02d25003100030030380b80880c0c000c81c040c103540600100841d40c0e0b180e9001500c0003a2210407a002290643c41100145091201d120000d450b04001d08452625004051a0201c44c40140d4069042401400822130b400200d90060303d40580e041a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 749060863 1250 749059613 749059637
    0x708040f140a05130e01050a020901090614030c18030f01050601020601060c02060304080714031303030f080f070c11030f0c04050c090d0b04051603110a0807060c06090f0b0709080d03060e0601 84
    0x203800340108617a504101c1d4601010421baa0103035a000e042c0c940d000380d036501d034415150780c81502c034103040c0458944412000e100141031803c0c41401000203004c4903000e41c01491030100400d01c0c1410b000c02e8250141d443c5c00c10004203507810080c0500400d034038070b000314409480d500818050301c800b50004c0d100040000d03003d001c2c04007080b0528202070307090088a9a0b05141d10052904400c1400201d000034045580d0b0030116201d10742e40341c081c1040741140707499622075407002c0c0c1d028010100c0c12154a50085007610711540e090020140c0f64001c0005494003030b000608020031030700001c0c0140c9000c0424450700341943c68144020844035031111281c3c2040d115420110314050030180004043c10713010001000f0080d04091094440200b9615046c1003501c03016283d0f120700c0b00d801542d0002c0c1ca01842e000c00704500e50015050280a022010f0064a9544030808100c0c403c83d40700c808954049020001d1035401c11000c03484040714601007244606100e030f12101c400014203000d041000e141884 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 749062113 1250 749060863 749060899
    0x6040b0708270a0f0b0106030b0402120604050603100204080c19150804080405130c11070303020d1419020303090f0706020a02131409010e0706210c140708040f140a05 73
    0x2103004607400008141143c561403074111700c0c0040900820340040e05240700414035041600941d40090b415003207585240d502d19041c0001000020143c950500c958008071f89000014401403018020842c0540180c00401050100c1061003a00c02c03041c030b0b1784184080041000744643d40c400c0d8104c5144c9030f4200c0d01c4e24100700e842d6025a801041d0300682890003801c0810855003c031401e01866103c5421514440c4d6196031251041d01c00500941c025507284901c55100d05c1e020041c009076050300c1800c01c400c0840651585d040007030300b83c1c0036034400424030102803004c21003c04840e0901d40101082070501c00000c0d20341c8c01448000780107511540709040420001e420084200b2000c0c1c01c104810318011401e18041c104c402a4401140100c1101181180c4a080001a0030300b28100e0680d42c0847e0030504002020700603c610200110901001d4115201d41c1c0200348413402110b2241d281c0e030600b228210052290b511442401400590719145e548514442c0c0003114401c640d0a040904110b1074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 749063363 1250 749062113 749062123
    0x304080a18090f0c1b02090612011d0c0d0c1a0403080304050a030806030c0607081b0d2c010c11040b0310060f060e01050f07020a0b03070206040b070827 67
    0x1800006203205a0080b580405035030028080b5440c9600a101c40c408a039401c0d00e550020003480136100204504440140c100580ba142d00980e0140580c0310502100501c682114440c903048075034221002002c40c41d19004000c8007000d807904542c0c0706c20783c0ca1583d65205182903d4490402e07a0b61504020102208140040d90025500660200c1c0d803407a03d4507055071900c605180c00c8000c1041507001c2100f505002580444021003d1300316441c2034038980381d5510a0b0040c2400c0e88050744400851381559205000c400040422502c460041d8100b0600313070301d0b508951200107107a101403a01400c10980c0c2c0300d40d9149000742c009c2d83c50390707c46000b5030100b80585041314a0350b4140c4074081042400000c19407110342140d110101134198151a00c070304403403060604004030f0004006000c040004150900106100c0c1c1c401403903001c81d41d0740c4120303241c06604112a18805600301da0100810302440c4490760f94007524500d0440340b01e02d00700507011448182461007030107184000740310114203102080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 749064613 1250 749063363 749063387
    0x12020f0c0c0111191b17010c0e010507020904170f1b1b06161e05070f0e0402090c0903010908190c020108010603090314030103110a08060402180601020a1a0a060602060c0304080a 78
    0x20304e4850503105e01048006c0c07140040041e045620b40640ca4002e503110b08072241e001c400503135806240810a030208800030b0b0010708150780100701c0c0e144501070300b941500288820315518140c00d80720803c0004070407800003400c0749902a43c12007841c1c10414200d060b6086050f12040f603d60f178aa070a10080102c0201302c40c6070040083c0741c0104510141d07071401d070803100308603c900c088079502500e030304030216140c0d42807060b550488409004a40140340940c0110340c012249824a0304103151100001e0940d80c0707070001540e9440d0005400c0d44121520b044070b05d070921712030410003440d03002c580c0002d010410500c6550b007016035501d866000c1511a180003103003a00200c1d146512540c503400c00100c900c1c0d607445030500c60518030a0000d003600010540f603200780e4004140e084240c000003070300f07400070b03600808107411400340410290004105010899100c800e184205080d07282901d2498111b99240d0010340c00d40d4801d500304502000d0620403241d01c96806000c5640710100b6110075201d10320080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 749065863 1250 749064613 749064653
    0x70608040c0f0b1e19021e07081b030f010c09210c03080a05090301090b060102060108060f060d02010e030d030b1309201f1205070504050607030f12020f0c0c011119 72
    0x5042170106580c00220380300948900201207004450007000303143d0b02c0c912840b650f9036680244c010b040056403036864140c0070741c2016050310125003601c8641400c59507402d11800205100d0401030100c0003100380d03448802102070ba2254134403006500e0b00ea954000520008149102c006050744040b4404c10560ba0b03000030190091000c614123241980d5030540442e1264014468040006401240007801c90b0040080310020a4140c66120900c4a85510000241c1c1440a44030000b21980c404000400000b070680c3e400050303001d040e80400100651080080564034105400385010505501c041540700d1070b050365a00f01c0c400380c10007150492100b08800700404100c404045a0b098001995078800034034000204059502d111003980da5010f00c1c0101e07034000341e0034000c03440000c2c001d0000c016280c1040c24011100200304421a06a03480400020ba0221021841d070056003c00c00100919003424207042c20a070001510040c1d503003024180b01c0c00361703a844401c110103104000b041501040760301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 749067113 1250 749065863 749065897
    0x9040603050109020f09131104020708030f07300b0310020a110c0306040b190e0102040f0f1a030c0a0c050d030b0f150d1d070608040c0f0b1e 62
    0x78107181d4020704040b20309902451000b401c02c0e130180340041d41540f1515092180320b400c07000d10b4070703410b102c0c1c9041c41213140c06c182e0030090305c0040f400e40c0f80a50310802c203104207840c003031400b860b0080c03201402c42500383c441840070102210440c0c2c403080241400601c00340c00204031440d20001381c51b100c4400392442c078451000480181c0158040d540342007100401c411640c680300345a09140c6d1365441207030080c1c200c04450000c1110a2400030101001c0140c050000c1002c40507142074900320f82c090743c0a80f40681c01201c040081307580010140d03005001c0350400000c0d104c1492070744403580c800180340b00284240051594820760085c503250740d6494012080768600384121a018004044c0311400d20310901480415509600e00800c03405104600d20300c070b003401c100e2100301c0c11b8040c3c000c101c2155049654840010071001301003090034010180380c0c9e5000d100d4100760601c80c0c081d519135044010400c1d94424288070804502007212900c0e10501040c00400105048049003405050b0040a1500310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 749068363 1250 749067113 749067119
    0x620070b03011508180619020c010501080c13140103030c020117011e23100c050f06100b07050304140a0e090703060c030e06161e020304060e100206040f08090406 71
    0x2c0401c0c443e01090591910034050701c0304448110608903881d40f00320940e0141001a10705401580c021180c43c14841015041481e80384a00e800d6a8090300806013130791200310280c81c40e1400d9454100140303c002c1c0200700800300c500c502c515210050001500f4030030300090400c21a4030404540729484522941201e0715611049440103402c82c0c0906010070f00703502400851f041099500060b10041c8544440c00003400590a0051001c410010344c014070900b842c00c040800d00c240800d9481450f600c019040e945014048150014055007200c0039442003884840c00203140041150242c8000c0d070310b080544003c45c000524480301a411040f2031400b0311003400046400014001c0a03648901030910140030003420850484014105003c902d511410206e41c80040c0e0100c812915400740c980f103018005d007a030182e448000c0d03481c0b5140050b84001010401d556118031401d40700c1000701c680e481546c90f1400002d41c0d03068058006421a0401103070901000b014004845040034041d0003405520b43e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 749069613 1250 749068363 749068379
    0x9030408060a050108071502030706051009022118101a1005120609130b04080405030a1a0f0103030c0809030721200a06080a021204061a03070620070b0301 68
    0xc000e12880000b4400c0c160b0200b070006121504245147e203540c011401c00c0000d4440d4000303000f01404489801b02c0070140815a1412400180010f808258080318214041001031308401d5000300100c1641040d8070200001100c00303c4c5a8510000300b51002ca100c07102006031003405002110900d0b403141c5a4545890030b02c3d0840080c00c110b806055020125980d00300a0060300321040ba140508005000c014200107008051b41540060040f145541082d4588010038507020101d0800d4444605014402214042040070301d41c0c0f0200c0000804402c1d4511781e00501a0441200005c1043c0070108561803140c4042000c20000c2c010800b8a0f820b41c00f8010300080d400142c4102503503124600900c0003014a641004c08442c1d220142c00f5078000d5150a0301255078540c080c0c91500129000c000840c185180d059955001c0c9010f04400034440010041209460002c1000d05020b60000e400810000b5000f003441c100c00c210106040408131040403000d42402c40d2604901c0c0080c1d0048000b0681c90 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 749070863 1250 749069613 749069621
    0xa0e19030201111f09060902090a060f060924020109150e070b0f0d05040f0b0c030708061807031112012904080304140114120726010b0309030408060a 66
    0x9000f81c0700c502082d070708800c0441c1c407900496804c1c04041c8444031000c411030311680c0300102503400f40c90009242c48440c2c0c0010003000d0203498078220552280c5051107003485031304401004021500344541d00914154910140003401e808410300e05820112a0702c8460007034000704800c0341e029201e00b0418401c40100c0c001400c100441e00b4061040d40c102007021070350f0004460500c030f40114806d040040104141d0040d01c8000c2c811500c055034052101700250f00c0103190b50003030404460690700c904e0800e0000788040d03002800385104441065200000220803070310190480014940801c040c1c260704040311030307072180c6141103c600344600000a83e0000801c01d18040442050701680481d000c0012480503002b00d0040010582003003208000c20350304040070181544060604001300c501c2c03410f4881690b0012148004001544020401035950042800024050b5100d110300368a59803010b501c140c10050041010180000010800700c000030402c0e1001404480100c90180c60640c000d18050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 749072113 1250 749070863 749070869
    0x201030915020a0c05070609060903300329060702042a03060302101404060e031006090c023d0902040c021f2702010e0a0807140d0203030406050a0e19 66
    0x6021b0404042491407140d0001d01c2290f0131607945a03c0c1c0d500310b440758141c0c800c418ce01c0a1000b164220f48144480640c090a40c0015094800140301e20341c0750b21305021111050244c54550142c001c550040b9500c04043c1c1d902150152800581003425800541042c3c41c000c02c01707400c40502070105080c481c0d0507000a07040c1c0c0d00c20745211000d16030103a0160344502400042c004ca2a00c14001400a0381c4505170040c4040c60081c21150b154103001119030846400e90050000244c0f51800550301c00d80410402c0c40861028403200300c40c8058403041003a100d64a401c244076034180310320940c1c000c5110f4102c002d403150000d20410107600132000196a130780c840c541a400031305038880c940d1502807151140b40000d2800810040022155018000207203440c5d41c401c90500481e400b00300010380b941d1a10801a1902c0d500900c01c050510303559100058045000d248100c0351004600c0040c1c801005490440d030040c00c0107038071100b61600030741c0c803000c496005a4000d10114035034020503541c0305c2c44800b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 749073363 1250 749072113 749072123
    0xf0b011416021c02120c010503181504030507030e0906060901030b0411030c0a110c0a050d0201050d06080303061c02100e010912030203030f220209130506010b0403020f09040f0201030915020a0c 85
    0x201c01700e00800141c44207540f243d05c0740882d03c240300058040303c0c0201005c44504071801544d454032450312000351002420341b401d9002903004581c01c01010342090204544d07900c200c03268840c070304d40b10000070183e01c00c0d01e40a41c101603c5682e020384940ba41c3c1c1041c040b071412400c1e400d07181d00e4042c0c100740464001c0031000c000142140f8206540d00b0740403800c0c141681c0c014003c600c40a01748401c4c00803181c0300d400128100481042603502c0c001903882880c003c1c05001c0065542c1c0c0c1406c5e020084440244580c1e07900c685d0f00a40c601005031350791b02c00e000072030640e070410000d0440900700696100c00c40b03501c0fa5a103030100340d00d000209a4080011480b03a00c10705290101c98071904005c20039100020340c61180c40c00100b05010140c0b604025042d0702898084d072411140b10981e42d0a414008283d00151440780e001c1030610442c070701400314030000ca2003910703440d030b00b4a000c0e215a04490152500039050507038441c0768006119021055200c80c1c203402c00259901d03c00030034010182c003216001528 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 749074613 1250 749073363 749073379
    0x181213091e11040b121009020307090501020705120318031f0204060906030216030e150a081b0703021c0201020912211c0203310302010f0b011416021c02 67
    0x10b1411125802c0d9001d507040260300604024003085a2415030b500684a402a40701c0000c0000368501280001c40c444c0040760f44002c0e245140100191030f003111070700501c0c481d10070b140e401c0d80300500020607149200c03900041c0544060f540c0c0046820070302c0c00d0100c03040f00b0001c0307400040f500b81c952300204211101c40c0e440b40e10382c0d96100000c4040740a451809003099200e0380041000c248540c8900d8030649004243c180140030704401c60000f0360003410100d0116480904000201000c0c40c3e215404070704036222145071107080c0d51f0080d21400c09425102000700b0149109551a2003581980d100210181c200c05010282031341c044e40e0340b6100040c0e028a80703400b0f10f2444030341d80e40e402620a9003501e100381c20001d400706801134002c2d400080081c0814404d00344450840c413074480980c00c1880803600c40320701500460a0007425141503010b2803544031b050603c01d24003030764401d82c00041a18020280c944460030000c032054048000d6074007a62013041748840062440c80780c08240300f168401c5408207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 749075863 1250 749074613 749074631
    0x1b0b04030f170c09190b181302091f021f0212100e0c070f080a0c0506100f12020d060c080907090501030809060306030f03040914181213091e 62
    0x1402d4800200ca5000f0030032004c2c020b100d840e0a2000c010245100200e80c81c03a0300544400581c1440c0d0000301820042040031100c00047d410143c58541b0f192503214020752a0001345004642c00c0001c0b1901044400700709848494114403d100d034508070000d02c0580710703c00000d1421540a07410003414014030540c0706000c03e01c00c1002c0071130326045848024110301d40350390f00c010000281d00911010b0390210001841940090306040040c00010040c0e01d54400c0441d02d4105146042c0c0010030002d0480380201b0f0a0140803007482c80384013122403810b001c0040300070310300c04607011030b0062500900a5040000042d4429040b110b03940c03080d8204411103c0c455036401c00602a10307401e02c0007400b401000c0003154040d051000007144c1c4160080e04580b01c109480145038615401540480345181e994100c0b182401014041c154000071581b40703061041c0d5000f00c0840d141c040600740c2c08041003001031712108900b040c03802c0760000d05c64450b0412440315112040321071001c50306003222005151090708 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 749077113 1250 749075863 749075897
    0x290714060a060f0806070f200a0c031e05070509041e06050708090d0905090717070f03110414120f011805060c04061b0c0306180506090304151b0b04030f 67
    0x80e0b10846c82a540c42080745101002561001ca10000c40040c0c0603154402c1901d56608100d000d864510079032881a0700ca02d581000b00b6050160008138100035075010300b890202e400012043d00b40c0307108440c1401035485a150400e40036070249602c020485400d035003142403180a40c040c512030400c030344031700440e07613510300e41305855030000a001e101140c0314000c01d124134182050740c030342e208599040000800d625882030700390904c0100e440d080080d81c4030340c0701c100003030b4180070303041c6464030124045040905089200e02542c0e0610312840c09511a41800c10b1031403230400c444c0031860080e10081142d13807510400307980f800c806a6000d0b1418410340000c50070b4814070104880489d1140c0d40e0354240d40505807820008500440700c160785030303d1a50408804159580701d050034003190740c83c3e886031103425490510b0905d4001003001c90325410078041001038a60700042450000c203540381c4106039403500a20401c000141c1c40024195551042c100410103070050080c0c0440c01c059190422420022944 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 749078363 1250 749077113 749077123
    0x100e2404140c07051203060612060d0602030c2503050409021e03070f021515060c030705011506110c01021209040e010c050a080a05010b16030e03060a060609290714060a060f08 77
    0x41590000c23820821100354041038102140c010a0007000007070310031125107070002070303801c151142c1c0355210001403810f83c8840001e4001c5448001c3c082c40301e80309190351310040c096000340d2085069254001a114201415100044500603242d000c826164108824014501051022024003512a020610f60181c8640c040b41c1d10510640b2900c903040d424520500283d0b03041079514240038413084c0080e100140c002c2c06101e004000154044102602c2c0c00401041c4030105100d02c1c4580e0803150407920a0b0368040b85860702c02c2c001801c0c1c41d0b40c03001000040f80050403403000c001d0a5501e480781030074140d83e02100400f06040c056a85140d5a1151201d42c411030b075083c494140c0034072080281e1000c803421034002c01d00700c0d8000c0c10640c0f003242090000c2030030001c003120202c012035070705c4000740700203078000170040301410768203143c4001ca002c0d0184480260000126550410401160f920100036880c1804400105440251000703810080d056001424040c001d003100d901e40d45d4408103040070f001030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 749079613 1250 749078363 749078371
    0x10c05070b13081c0b100c150b061e09150a0f08070c05160806010807060207091505060a0309050105070c03020a02010804140d0503100e2404140c07051203 68
    0x2495101e68503140d040e07065000c0d070220708032600c10043c480030302201001c2c1151000a082e15401017444075010041041c0188048041c2c0b090004020400c0c01040c0304190524100409400000704000340c00c2c00103106000c1c00074540350010340800d00100340710900000c1c080703201c02074400090a00e0605405407a44c0580c04d61080003541740200e902d045845444030079089192801c1446070854603466240c00d100300400026052002403c04001d46802042024010541400038041c06428a4402521101c035840751300c0780c6644444607103c1d0125028880001404020240d41d540c507202c09028024045003c3c09460030351816001410060040320a4011964580e01034406005103078019200c44402500645402003170b1280322000035020410078004013507075150280c0b0391401d91035402c4482400d0700a00341903148501400555204034038515040c084103910a4081c40001000c24002c0a144101d0f0303a8012015081c0900382100d040107040c5140a2011389038001250484000a440152 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 749080863 1250 749079613 749079623
    0xc17010219030b13050901094107150206040c050105030c04090905010b03100b0f03071215020c060c0403020102010b1e12010e0d020303101e0b25080903010c0507 71
    0x1240380c02654030aa003e4800e03582c004058403100b03161a01300c1401c03a501295140342c0c03030390341d007072010305100d9414501c0d41e407080030100711414505112200300c0c46000c00b4190081034501d4010030030342018180440d20103080c1d5980102c40d050380c030010007542c0741c80580b425104c1e401400c1020405501c03440450b0b210360041380d2224030f8103261000800080502e040152095565010000300e156000d100766411408011400310380d8554550400c5804040c006a00d8400d500010040041c1542d14068101041c4c00840408001d22038a5040c0064800c0c414802443d000d0001000041342414020b070081e03074000c1c0d0080041840b44c40502140c4620007900c616000080d0031001c000303242082c1e05c100703c842204008950300c0210f0070030038070380005a410a000741e0000300402820040c02e40301400203142031042c00c10001000c0f2032511050009000e00c41510700000740c048500d402200032040ba5881710800c1c0781c0f400f00c2d00d003010b41051b004842c603240b2079400d01c140c2c1d1440d50310840950f18216005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 749082113 1250 749080863 749080897
    0x1060c03020d080703090b1612090f0b04030c0501060e01090c0807090b1b01060b030414070e040303150806040609110a05010e1311040b030a06050907020a0b0417070c170102 76
    0x606030361003c0014812000c050300c42e40407900003101204000d020314103107400605c480b10350100180c42c01f6031110650440919140009010425030903035880495000300c40780d599038880382011201d618503910040e040350b08094001034200c078000c443d40d0480300480c008009041d212903086504010948884000603680c070005d00183c000d0f80010150541c000c04001c047c2c09610140b2400d40301c0c41c0c2c1c402d580c840c3d4044104000e1000c01708021210150500c0a8060542400d800700384160020340702030209641c50054454022039225a1009010b5980c106c4640b4602407400d81c2c003600d041d41d8100e41c0301b4481d800342244c5060025490040d5072050319080b00e08906203050040420060304840c8449840b0241a580580594000c0c00038006200e0303290f5591400d52001d00039902c265100f240648103240c200f080059021426805240e0f100e4940f90441c0c80f1030500c4400c0ca00700301c48081c00300200003108010130144c10120307002c03180340c40d44040d1110400d01c2a2800c070301501d24031300c04c4a180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 749083363 1250 749082113 749082133
    0x12090b0f0c0d0c081806010f0b03100e090a20060a08090106050a0f0602060907030201170a0f0c0908210403030503090102040b1204021801140f1201020a021501060c0302 74
    0x81034000d65400051000c4290034220680750710815102ea00c0024000300700c001d024002d10781501203882e00c190340039100402c03065240c0039014802c2081c51103809040d000210126200e000c90081420051412a10841950900ea0301441d02d030720611800b01d82481c60308030f43c1c1158210045c0c181160400080c202403e0188000d008e88443e04c00500804180d541d6407004900390f90768030355401c06004804110304225080c194060702e004d80c0644204100c4c3c1c440c0d101040180c0e48268103149002e14401b03200015144d90501c40c01408000c402204000e00b41500d02d1503144d4820507940071210310030112541c0b03010b60100c4100021122100d041c1c030355001c000074000310780154015600210707901e000514040c1d1740d004912503a0040ea480c80f11001144e4188401c0d85403820342c01c1a102482c04009025524001c0c011400c0506100707014020340c4041307507025003a69000521080203040e0402550f907a80411002522a0784c0c1c03503100e080303d90016001240b03003441441c000d2140359040d0014094052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 749084613 1250 749083363 749083381
    0x18040902011b0213050906040210140a030b010e0a141503010e070503040c080f0709050f07020c1e09100906060c0c05010c0c05031509010c023c0f0c0112090b 69
    0x3071150403d9821484003c0d2004198415200c4d0714855880f180141001e0708040c4108466200b20100c050108a10f051208900340019422103000d4003031404e000030080d5070113005a0303540260103801d951000078544c0020307030881040281c2102c0501100c44840005d20103000c40700e1400207004180000e1000400110ba0f0350051004540042c040d82c074008910381d4400201e882c2c0000e5000451203a00500e4040003d03406500680d50001c1124043e140740e4903081000a5442d41c1c1042500c1c41404012500180310528a1028203003120240444c007062a00100815080c0907e01c641507503a4034003080000c90500c9015101c454540c44544860900c4c81c03e40110356115082c5d8007580d10310101d0307000040565080000510080b003206001a55150009009003100c000110351810364002e4842c100c03036210030781d800345d80c8031801e001958480000581e26078010f48480500c20170611030703194101d01505000500c0c114030507099032340c040c0e0350200c0300c007040580d414a0b400a007885250340201300c40d41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 749085863 1250 749084613 749084657
    0x50d14030a0e03040b0a050d060609050f10121a032104031101051908091506060a030e01020d1e050a02090603040204020d11041203080c2505070801020d021804090201 73
    0x1c180382c21641007075111031011050383d000c1d2000e54040769000a443c01040170b03034010040205001e0400d00a17051500012401011505520074400ea0f040121080032034000c2c07410f18000a0b0600d0700b0030410055130281514072240090b228445e200e101c902514403035103000e9104c00d0070514038806040c1451a0f591400703246040c008181802018801e01510300e030b4420100748040126624090942031070109603050195402da004180700241040001d00d445100880342c80702128600041c100c01c03c7e1000500a00546108004145c10170382070300101c0400c20492810346900305400c0240b40c98442516049229000c01960090401c0c0001405841d0a81c05840007031001800820000c08181c0b50080c55841600a2a2580b4a20801301e041c142d124914680c8142075180d400d151a00150b03010540300440c402c06807d40314140e0800c410048244010001805054025512002e02812500181d0040d00f09243c4000c028414902c07145014060001d80540603102c01009800207070b0341035000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 749087113 1250 749085863 749085881
    0x5042d030f031106040b010302090f01030809130e070f03050f0f070608130204050a06211e050709090b01050f06090d03081308030c250c050118031a04050d14030a 71
    0x3000744001003e0900030103001d0540b140b8400c078040c10385581188100a00d1440c05440b1000d2001038031300500c00140c601c5d0032074400f12012200030011005417480103000d08130141c1030800303d0140c0e40001036480c1c032500543d000c1e40d00c2841640c00c4010201e60907640c411000700c3c1c20100e82d2104400704401c0740160f0040ba00030369145461001078000b90041401e40344240c4010301038503540d00c020040c00390031000c4103950380001850301401c04e07c1c0b034985861901d4074003061402000e142400d01c04122080010000600030640180700c0e201a9091014100748240b18039805110700a991040070300d0000100c80c00f840000b403500e4400d0540b514211038000004201c1032a981400d50a200441d0007007000e144540540311141d540c034800759030b0788600103a903480c50180c0c040c000d160000015034601c01c3c030400e55a082c6001c0a80c41e061604403e00208184c0c0050076500000c0c3c002d84c5441c0004800500c264050402c480302001c3c0440d00b281e0310300c8503403254607e204040c008540500840d0b00303d4240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 749088363 1250 749087113 749087117
    0x615041203090e07020d08070c03050319060302030d020d030605010c0803070e01050d0f0f0c030b180a11070516171002091305270a02010f0804031e05042d030f03 71
    0x341e6200d0030003c1602c0c8007900c01c400540d0068803103a0b03056034842e070f85035807208061600005040300b5070f4000d852400007520321442812100406000d0310b0345644120000c0da001411204003e11690340a512180004603085c002405c0a1001c50307254054074134016032581c0304440500d99551400111144d0b0403851a1504110b400c104030700c01d1030440d0040301c89403403184100048050180000c00201c0d018090040285811324440b0006aa6540424030b249500f2510081c050354130119114001c040c1e1b00250f0305040404074020302881400161000c00702d094540300d00c2020345410302100c0142c11802c0c2c416039a440b201c2404407c0c4503076005012015000380c2a45485121120300c8820303510111036008000c4441604c1b03100e8591100080c05e452082440640b01c00c0c00307c2d4000174000c8880e0840c4605000d28a0081020184105070201c9849096541c0035126001440010010b902a208030004400c1c0c000351840b86c5d01c42d000c0e031441050000004403101c185107540d5003000f9490340a064003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 749089613 1250 749088363 749088377
    0x50102061501031a092805060a0b070c1802040e09060c0301050d020a08010e06070207060f080a0b1908010e0f0625230403152f07020d06090201080615041203 69
    0x80340c4071603485c64022407040c2501400c21003400c140c0541e0f03060310303000c58a5050804c41031105030303103801e4071035000d880300d04041c00d0b5070b0310460400d2144c0c8503042e4411121214130441504407154513a0290050303130301f00b02500d071468503110f040690302e40b0190350a0481d000304100400052410120300002c031840074003da0f00c440d0759020b00b1405c495841141b08a0b81e00050200240280d061001d50042e03d030509001400003804c00c0c004095034002000c403481c071303640d94460706401d84e00e0319404520030600d440081842d40d1076040d100c3c06080706005803d6103200d400e410303010314600403d603c3c0c465802007416420310208040b481189041c16440e290a2000a01c20001456024180c2900a0700010341303141d1b41d10301d10b282000b600d110500d003403020a86000020030740ea0603079484030600f406031780c48141c0303100010074030300c400038840c0c1100258081d580094110030003989801400d0580d000362206041d0750ba03810280402c0d171400c0110b481c0600c400304014421022130420412040d4040d28042c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 749090863 1250 749089613 749089661
    0x1709071707030611040f06080613020d0c02060c04180f18060b0a0f0e060904030908150a1b0206040f1506061709030c0307080c0109060903051305010206150103 70
    0x4400303010010920040d400c241424400e101c56400358032071081030701c040e1515113440c21005c401c0740e443c5402603200f0064a440410225910405240c0641e0080780c000c550300e022240400c001091101d0340d40001d4010440011446002c440582d002c403495000514804c402d01d211100090042d070340d65046d043d030f450700c091400e5982c060b040407002d4803620300010001284420003200306034a03030265000e0661228203001480a004146412000c1502e0702c543c41e80b15858141d46114507074010400a2003041c050032100310711101c45902560104004020418405420221102108128001503032001d40800d0000381442c00c4011614000c50003007010300250114101580c0c0c940d0b01c4040021b42c2041c038840c2000319035810540050030000151f1a11504071031440d140e001c3c2403006801700902040d80d42c801d10003900041a99503100000300700d8486685000317000340c0c01c0b005018030400c69800000c901135000080e410b0040b482449848914406500114060a006201d900c4a8038201d1082 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 749092113 1250 749090863 749090879
    0x702040225030305010e0411010f020a120315050f03191419050115080601150c0506090102040f081f2403050c13050411060a140304030c0b0105010e01170907 69
    0x80c02806010301d01400000d003141401019500b040c5c00c5072003140307040c07000d100016030a240d821402030003c0c200202c04c2482400240d0030100d0185000d0407099a029255840741d6055108000b080c10711010b00c012a501e8006124642c0840c1086640582c4984205078068403215014240c50b8850310304071000ea10303814542801c06401c80c2020481c014a140340204000c0c080c01414141c4d00310140c1450b16a25003101c255480c8418440d0200031000c4010581c1a9403080008498207500302c01120513030b04007030076594000c2d401480382c0143c1d1543c41002290164010451140f0410919111711042e442c428002005142c07141ea0300c1d032440c0c45000c0050342101200c001a0041d0f000302e001e00700c403108000c20302c84042d9011181103c503038503000401c800030303010340101d820034002034600b90340b15021110241c56a0041481c1c0318080c0030007004100415500428803450a07100360b040340800d076600d10066a8890341d101103c0d0100d400d580142ca0301c1c503c001c00690740031400d00c04840c0200e075100e0765 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 749093363 1250 749092113 749092147
    0x50903030c100213120c031118090705241804020d052a07170309010b0307180c0314280c050310050f1026010e240d02010507020402 58
    0x18911242c0c2e008525403440100d4402d040740240214088440c50b80d9031035980d402a21190300000f0302413000c0046e040c8540e20340d0200b030300800364540025022824041d202c40d60358901886254070440040010f28004120340c42e40b00384018480132180d003071080d00a510400c00400d02d40e0030341c1140e400e002c0300000304040d005460140300f140e0100d040888810301c0b0103135003101824444c01055001c00c120800150b018196403483e048400e44075850340c0321610480c3c050003072031f40700c15030603ca113840105000007041c0c07410304442c4155104000803009403400743e050355100840390480c4a00000000c401030300d605903c00701031303240703081c1103202d1786950441c41e089171003001310b039030005170044100400f06150903100710241c01c0450781b003900c4610680002d0a00c1d0b4601052004024983d41c0040e0984d520042c40d82c102d462010402c10b0941e102c1080340c46205080761090001c004141683c40c802100c1d1704903820751135010b040d900641c191074005407000e5104840403608194200240300c1c1c0c0b0740c50621 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 749094613 1250 749093363 749093383
    0x61115010303050a110714060d0b0a080d270b07060e060a06081203060d03180909030c020f12060606130807030c081209130e030d050a0506041503020a06050903030c 72
    0x3c2c1c10351140d911420040100d030010039840019880480c1c28002e0700e044144e4054510f0084444507a240074041150014181c40605290801080f000100d200d200100300d074a5101c1c400d5030341441820140f0305c20205015150702503400c1c9026140180071500803c000dd220507806000003044010284c04014600502154290803180e90f0b50400d01103050103201c110840a1320300e0200d41507082400014138407182a20000b814040c3e04a24100d01040f0310b81060700030030490b58204600b00c103034200603000380000501240f085061313050f50740c0c0c503180030404402160b00000080205640b001e00784541c82d40014000408146d031a11300040b0900b0412225000d10720641c13510058a00e0905400e240103003501600d2401d150502c5154101d44480d0000c00000c2c2403000e010841d1004d03040750a003181b00d9076000d030481504210070440d1126842c1c10040c000e103820f03a01088024052400100101500d000080d17000f0038042040094a104001821000d04003d090742c0c90907d100000500d00000c40c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 749095863 1250 749094613 749094617
    0x1002042106020c0703210c050303060108130b0109050604050609160e010903050f100c02390405070309050d03140c09040b03160f210b0c13030609020319050304061115010303 76
    0x40286c0300c8119000944801e4085507041403000078000d035844136240c3c08020402e60411451a002800b61042c41c03a0450b80e03240c00c10702c6882d4031350311003040b00003403d012261103020b030341002c0209a1a040a050035403240c2c12000c5600d603116041e80c011501c009024140b1410011820404070100b2014071074940102543c00080400b41c0c000c0e0001d100352802d400303038402550041242201c1c103d994410201080c2402c400e214010644000c440722034a40108181750011315040c100b00f03d803505035101c041d529000e2806c498410040304011803d45a00d19a200443e11090010452080c00000504904c250042c400300f0600c0c035240112b4500305411101d4104840500c008020040400c10380001525070522840b2010a19440105a0003042d480040580390a1030000c0c00c0c00c2c1140c001e44005640001480c0600d0f543c03814200c01414403018241e12038003902c000c60044202d0030035129003640c0d100c3c0103581424030f401c000341c0c0c207032400b040000514000d80010591000c65101c825018520035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 749097113 1250 749095863 749095883
    0xb0c010203010e07050a02073f02031b010c020103020315090c030f130b13030e0a1403070f03030e130915140603070303140906070c0602010c021002042106020c0703 72
    0x180e445003c01921120521030200001100303290f000c5002c0f03007618400c0b4405003902d04072044100d41b10f0a80448031801d24540390110300300c0c000a02201d04200c0c000c03402c65020040044400401080b10142640070442107502c400055010750042d551101d560b82c28055202000320100c0c584441c100c0d030a84000100000f01725004580c1c101e96070b00242020044c41c180001a501da0304414405071200e00c002c1d41440c901c90402d441081c0240312001c000d00950b01e5591744a64240c1d410b500a10321600c24084c2110101e1135101d044c000000300c0f82c240d62020040e41c0840207001c0c100b0983d4108050060310385130b640e80403499030701318901e140c812580c5c0020040d06401105074824800742c941440b0f03801450342000425480b1a6101107804994044c50ba02ea44940006000e40300d6514010901040a0030024056406600039160000b0076000d0b140c0180c0b4003041c01d000c07485540604800454240c01d420030000014843c040c50600c00e1800515240103100e140d0726041580d402180e00140c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 749098363 1250 749097113 749097119
    0x911130312171905040609020d08030a0f050c09040e100216140312060402180d050d03060b070f0b040201031e0902010f050a08180a0c171c0206130c0b0c01020301 71
    0xc04414102d0380d280312900d988460030a182c0c8615003804500103040c00e291070380041000d11a19900c042011a1700800c0402ca0400515241140d0340044420000303052612400c00d90a1541e406428410321303000d0a050300e84400001084003e11180c40d00b41e25038851501355101c01c00c0948018029500740340c10216a8000314a0104441300703c2e1205426031741c00a1004800841d00000001e40110b01180c0141c0ca4443c55141c0c45032080382c030001d09070710036829030640050101c0422408038a503450b5030180000b984070b01c40b030707409449403203401440503002803401d001203002840740541041c414500413038510425039040916011840106000c90303510f182c40b40440d0b0304200c00d0034088850b0f003072442c00d10444005c0a049040000c0564100746d61000010218003020310580d01c18690000e503105c4a01c1c0c0f610a050701200802c44410030310311038480801469a0342c05200501e0f109141c2c002e24543c0e95a4001a00c2c4101c00c078421210918503000c04100780300190060310b005080c0000060301c3e589 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 749099613 1250 749098363 749098367
    0x81b0c1f1a1020011d010606080403050d09050c0d150b010311040b18030f0f060606030115030f060305030a030e19020d120e04021b060f0f010911130312 67
    0x900c14100c0d40c11200c4a5060441d07454035920100000c01e9420288000000142914036a0040c00c50583c0d9952030305090141445100010368510b4444070000c000e580c1d1680d000f6900700c45e0955000c0c1c0403410034002c40410310201c0c0c100e1070441344608140c5600c0d9200b200445e1400d01e207030004650326482e40c1d5400c2644400c51051201a14003440d00303200022040361050b0803486180038441c002c4600046000701001100d05000c032810001e01292620510410300c44e40b0754514444003042805684003166162500b2400d03139040c2c83e54400a10300135404800107030010000c0f42c0b10040a0740e101c00d800000f0070300500c040c192407440c0303440101c0d180c0032558901e403d2030360050034040492041ca280401688410b403102d03988540c00380c81e0001d003802012041e10950405058160300500005000c07000c03054810030404d100178408112580c03521048032912090030107c80e1001032400f01e1004200030001c1d500b000d40514090070f041450203038400d4802c80921215081500c19114000c200e40c541e40d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 749100719 1106 749099613 749099621
    0x80105060a110123101706151903050318010201060f0b0702010c0b040f230a060b060904050c131509030b07031116020906060a081b0c1f 60
    0x100b40d04e00c40380c55514201d81c0c090440350640300001314104466a05128111340201170401580c0b00d1a080392111340141d0140d40c0500e040d241c0a00c0c404480441601540c0180e020b1544c501c0c0d40b40c2d002d000d10303040da02140d046a15007107040184031241800207080e1400b0b880529030b40c4000b400100c510542804000d46904548018002080807465032084400d03c02c441d10701c410488034240400c032004400c03071010640c00501c131035400201254440400054001c1045060040c504081000c6401c00c690880b40340c2d0000882a14200d100b100b0340004045c0c41071444011025000c1c0189018002d120007001d0440c5c85001c03a403124020b801128051400210341900e4100780f1820504412003814107034050740d40c0c040840c201d82800c0d022200785003002e4485580a44580740800c42c3c42d491a040c10849100902c01e00300400b200344244041c15460002a014001003840720030119 = true := by decide +kernel

theorem cover : BRFrame.Cov 748920863 749100719 := by
  have h0 := BRFrame.cov_init 748920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 748920863 ≤ n) (h2 : n < 749100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
