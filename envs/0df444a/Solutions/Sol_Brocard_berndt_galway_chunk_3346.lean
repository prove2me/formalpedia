-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3346
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:23:35.525611+00:00
-- url     : https://prove2.me/submissions/2f449409-dc77-4fa5-af52-b017b2ad4892

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 601618705 ≤ n < 601798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 601619955 1250 601618705 601618723
    0xe01060501030b10120f0207260c1c031119020709050601020304050603340306080705130905070e1006021203040218090f0307080d0e0c030616022d 65
    0x4050400700c0000468951a404044011640c41c181445c034400c49060b2001e4540c0e044d03000f102e280b0004003142480507403003841402a200340390800b0131380e1103c00e03000d04c607010715050942030344c01180214078070140300d0543c0c5400d010141000314140d2401800e0b031107160010000b02c0440c0105201914450384e05114500c040e10040e10204240d00b48080000d69a0080e402120b000720710000c0446c8896800ca0848403140300218110400c4c0300c10800c4030a9806404441607000c0790404001052040010568400360f6030b004c0c254400440303101050741d016204030303a030030746060241c5000414480201802a0b214014984200040b14540f01d00280303080e40d0031000c0d02241c002401800010ba841101e1262040d4040340e0040598588010050034541d100d10b0351501c40c40700003145000c00108201824000d80301101c01c201491072500c000e81c9a03806540c20a5054200e10001851408078908610a01c0030a1044030b090301c1480402c1582204600c090f41807046801203091441c8108100100d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 601621205 1250 601619955 601619957
    0xa0531031e0c0909021302040605040f210f03050702210d11070501301b020d020c060c0703020d051e072702070b13030e0f0d0b060109030203100e01060501 68
    0x250324031a92291901c1080c0d03070040030032a44d11503a864043d590b614155401410b0b0f9140211f40e240d940c1d40001c0c0041d8440e21442c01d006000c000005514190420060701858422040c40c0d1410f426030fa0380f103c1002d00c1102213041c0401800303154003603180c034140c01e1042401d04034036160000b40c2504092030070072500c1d050b908200a002c1186106100442c48108940302801c09811111890100c0c000707404038514044032003581c02011302c0355102580c01a180e4004115440b0080713400800089854044101d24000940e00c010348440032800e03c81c1c014902d640000701a950b0440c0c40f03074001000885020340980341a8013079808250300a8002c1407002049848800074214a1310b807140d40400d00620103030a108940003600809406c0c461601214986980540300321410f140c02803031810110320310075040d0300140e00d00000c106141410f101c8103881c3c49000301a020300101680c3e821040d030f04024902810050380704000030040c1c8040000c040c032600102404542c41026840441c00c64150341c0c0254 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 601622455 1250 601621205 601621253
    0x31a07180302011b0302030c06090714040c0f080a0b040e060603060f01050d0f111c150b0105040308091507050a0b070c080d180206130614040305030a053103 69
    0x200603a0003084e085515030700b00660340301410650400364118011000c00d074000b401601c041005428000c186c48040d1940d500c444890003890034148022185622402802315030f01d1507112050314000e03044d0940c001980880403400150640c082800c2c0c8000e41c850204036481941031000754079003030011607800340803420984842d40c5010009200c007544203c016028918000044007031014601d0052901c0300007074000880c0e100703400f01c0c1c1c010206004100392102c04458846005480c40c0303000d5100180b0059486a08040c255211040309a00c62400c642c1d000600720090a034610800010b009860b001d000038106100761410401c01c10800101100100300000d00c00b040007c814400b40c4810f918108000607400c0c032050b6150708203810300ca1000c1d43c032a5010580706105103000786410107488186d500c2c0c006240304444207640500590000600c150004c1c03001c1084c00e88500d0290000724968550103824030f00400580d0f003030700343c038227035190b2000b238028414014003560341c0c085070031160030807244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 601623705 1250 601622455 601622459
    0x120a05090a090e031b03120c0306190b0d0e010f0f1415011b05011806050a06090203190903051b03090a050f032508010e030c21071506031a0718 63
    0x403586a1091011507418818005c1d0a2484400f080096602122518000c20482d061410800c50590400c071a1071b8400d410710903241c0c4215400100080458208440b150704200f00181308601504800e005c2e680550758816500c41e40801902407a2944c11a400340006c2103a48034140303002d2504001c24000d06014a58190240f0343da00c516031813104078000c1007844051940d03142460142059555100c140c000c0840d01c002408995440b02d802505804c0e42001203035512048030742a4002224001b155000d00340c00701445041d150003100109109240441c038010315100c25014004083e034000e0f21a60002c40c400846003002c109a401919040791a4103030803901d000041c1c7d98100f80f420030a14203240342405c002e400c4000302407501400060009000360912424a1503407600407080c044040e10428941a00d200d00d001906c1c00000c04050380e05180c1155a251034141031460b03206d001c01d4a03500d01000020a001705045241801e1401008055080000004103a001390050105100c0481d0400b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 601624955 1250 601623705 601623731
    0xf040c170d050702130207060e0c100e061b07030f0b0112081b0708010c0e0405060a0605030106050f091302071a090d0804060906020a0c03110d0e12120a05090a09 71
    0x2485011072071802c5551403a035440400e2568210070306581c1e5260010a0340000c02c10140c020780440d560ba1000c403540d298070807040061100d90203248001251070061521303014102680200320704c80066003012201c03440c02c81c206107043c03903541c010f44064818000c03060800c20181301003070043c0708581c0e40011141841c0c0b030b6060340d03200d950300701484030380c0341070101708000400d2141d48018041c0100800034201b690310b001e00795850001e142445141380400280c4603291510626064130210340d50541182e08280056510347d2000004074108402407001550641d0703101c050760545100c80d5000758403081d01d0b2404520f0040740f241443d001a41c190200844180001035403601d956185c46c200003240c6450400c41d000b002c40031400382c01207000123101002c590f00250f80c07160180c443c1d0b80700c615024000ca43e50303172240c140c1c00301840054899209160249080008403d074000080d0503a070518018402904980d800b0b005c0719000708402040b400b1080c5081e14446000344605c0400340601e00001c92 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 601626205 1250 601624955 601624963
    0x1180f0b280f0302160606091a0607110d050703080f0a020c092e03080304060b0102070b0c07050108090c12010b0a14030307080a05070c0305010f0e0c0901060e0411030f040c17 77
    0x540b04250340442d040040145000010400540100e4200029616003880c00701405070710003500111720300c08000c00300500380982202c4003980c000c4a12440000400100600340c8004031098440e44145840440400c0b10700c80207003082c44004014542d60f0480c00e201904160551004604c01d510550802452441a181c0c04c520f5800402195080c5200d285141224520303030380000e003206170042304100810401d07503c4152840300907021a00825078031200c1c01d4282c800c0c50300f44221600092410812940540b00d825000702d020f4054030f1914050001090801080d80303090b1410ba911084003081a0070b1452059001d00301500c11101c00d800407402090342c070711507000010300b0390100065404181d44160242e90656a0003561080c43d55503030b042050103403003044000101c03d4038002d060036100600250b4441c001d00c018040291031b80ca4a0350030b440c0078003156245908561900d480300346807075911008501c569001114100e542c1028140643c410a0b903400c07a501e0303441303841413072001814001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 601627455 1250 601626205 601626227
    0xe0d0c050907120207140c030d09090b0111030703030b040605010c08030c1b03040602070f090902030604140c2e0311040e06041806050406110406090501180f0b28 71
    0x29a03620300603196050304880b290f80400d0030b07070049407010032607904212040f0325080300701c100c200c21200300c0c680300c4041544aa10080703c003000700340800800c01c84076060ba001a807400105040040306030810380440d0341950700034a001c0f00001e03650380710054076107024412100608420302e00582e401c4520783d58205a40b00c0505000c035030b4140441c1c0d80011080345104000c060b034815040c1c03507d071559003402956500c42030103038100710031202601049000d0b081c071860343c58940040013001503072201d49136400141c150190038503542c040e00b1100401c40d01e48075007030f6142d0001400c0c0c001d165100d00300c040d0034039160b6074038140400d414441c4805103544000b090ba003d40b13640004030703141d80d200c01000078010b048481200e01c11000e40342c005010311405500040c0b190307010340d500341b14804e440940d0b030f03c0354820341c092200801d860031420301a0b940300d04400c1c0300000a410660b080d080d155890340d14440e00c141d01c044001c080000c0c0e481c00364856004080121040a07946160700e807070074000500f85640764 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 601628705 1250 601627455 601627459
    0x6160506010626100f0314060a0c170a0b0901080c041d0d0f050c010f06081c0503010b0a03090c0308030613020c0a03111c030b181006081b16030e0d0c05 67
    0x483c0880c00c014281002e07200100032240515001d41c1e40c0e0328044080d2005a0000c1c0c095008100010b50110340b64022420111026560001084640c40e01580000000b0b0940b00d48581e686903450f44d9515148603c501030001a0010203170345116508000070b540c0a901e820443c4859245491880200080c8071084401c1500f0081c291100201044405019041da0b08a056080c0f449c4010084210b0b0701c0201507070151401c1c1c0700400f8048a00e2010107806555403000601d0410040001da0f0442c005800005e01c3e034607000c94210055151058103803101c0d00152022403000041c00703090310303000322110001d41a0000075400e244110f8011070302c1c2c4481c5080601032000d1000000500d07a401e00c90030041110500b0841494065640010000d0411803031142c01071448149461007061490859441000314030603110719603082c050100c0c0d20035009003002d1142d5800a981e80040002d05001d4942c01003040c100d402c52080c2d60800612800c01500801d01075500c900307111010501043c5c2010a503401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 601629955 1250 601628705 601628777
    0x18040605091b0f1908160f0e0f03030408011a090f0121060f1506020f190303110315010905040b10030b010915021f05010e0403031109061605060106 65
    0x2000c2c5840302d1841100421203c007580040c408018480c3c8100f030b01d0040c551a961014242d079040410307a00c2d0302846c0307642e90210b901041e510035014800c00301d00001c818042c001c0c2803c500b031403010a00e19042500804c84d5039442d00420144018070700c00e00d9248040446091110742050b0394440745c440018080c48058ac00860549036005000d081c106011941c80341c400c01640c0c28071a000d070003c102c0356452081400d42c0c1a0000761840c070000d1055120b0442e40c001c0d100d6001ca40c42d6203110b108440301c04a050588407154203610b07080c0400554031540c0c01260b5071030000c10100005107882080c1c0c0140348a14600700500c202c5454900b581803a003802400c0002c2c030844038000603603007904150304c1800c4c0c00481018101d0015404216180641503500d03d00c01c00c01080807001003038078000d01501c1c00f107a07808000140420701c250018036500711110116031900c0b1b03001c0e01144807a80300c2c18080c011585840d210301c041000410465005140758985124140c604440c0c0f039038204814240500c40d802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 601631205 1250 601629955 601629991
    0xc0303050408072102060711030d2f0a080108120304020103090212030f090f040203040b1b040305010f0b01020d03050105060f0c0c04050a0b1c020102150c12040501021804060509 78
    0x150000c943d400ca400c0014690000c5140c0c4203e10030f026254107000043c01a040030803030050080d03013a8034034021044040c50030009601610001406038074081d915802c1e428030000d00364291070b021428105105400941d84040008001d06248010303400340074036074041c0c2c2e0800074405450341500d40041c1c1c246004a00d5810f1400000c40000503207030300c038000340030009100556840d4003000b0071408100391003d060700c08030141008100d00044802500c111403103000030701066004041010004100d0b2507490070551a9120300b170844030002c01c1c0320082d035070f030310b080360341c1c03503070100501c410400c41450305100940c14030003c52594001e003032032520003034800301d00901c120009109071080e080014204000703078986a01c091001e410841705250090641042a08080400342e060300a80c58040c0c009040040f00d002c0d005c054254010491a09030748203009040400c003082900c2401140074800150b207a43e40b008203600d91040e40e101c058451490001c0070016501d90082242e8000c445802d45030a0b09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 601632455 1250 601631205 601631213
    0x504180c0c0212210313060b0d0b0106091a0712110316050d26061c02120f010f0c0912030216030f0c0b040b090405040507050a03080414010206070c03030504 69
    0xa0030007031000794019003955000f55124800610503403801103500c0426148010034601c10041d101c15241001c60403040b003c01c101041c826082401120b10290181841c515542ca440100d220f082c3c01c0000050702010041115500b1074201d0700a5101d40320303c0510b0302a459035a486000c408880b01000c0c4001846416210807050050740d404c2218940d6140040d06585415a10740c4880034000000c6902c80082d0440f1407403003540344c0200d04078815900c5240c1c94810400148da001c3c0e500440010400c11011030068136020044511511007000a1514a01c900d46140c25184414003c1c0005460b00015a40669000c2210000c8484101b0850b02080c4142802c0382403645040c9980311204030103800004214864010140c00da01907000408441d881300011402c5100703138070449011020a0242c4840ca01e4241c4c04103421500c24800c41d41d40560f110041030348500c0542c41a1009000402c0400204058100c65110020700744058030551900080182c41c24000c840c01038101561440007400300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 601633705 1250 601632455 601632467
    0x51203120612011a12070b0a08130807080306040509030a020a0807080c070e10060207140f030c1c0c05120a0b0910020d0e0f0703210509150c0d0504180c 67
    0x84201d100090080403003a8151040041480d0541c5000b0180d144944003410b80c007060074000c0d40c03844a04986050640c1502700c46002c4050301d014088211000e56100003007400009029141c403400907a602c0b498150300704412583d00511952464104012010020390301084090407154071102840d01c0701240d05103074515000b005003000d400d10490034003040d0b12000c2080c00c0d10a00760b0b140c007404442d8540c1c40c00ca85400e09032060503071402d504512000285087c0da0003480d02c0c3e001170308880d001c083c0c0b04000341c2e5042047c0c10700007280e03410244107401c2c002500c2c40603000e0701050318800c009841040d81d280e40c55120a00140c04080e410010070200c243c180024000c00380307588400c2d0345959052070104000d154050340701a2a10404401c265a00400301e07610048075000b040c0500d192001d00c5044041840e1140c40d501000710801c01840283d42c2d140c0001120900640c840e038583c3c14000c0102d00d0082c01d58410801d210041c0030070800302102071441c8500d80710624010070103030002c2c8030507140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 601634955 1250 601633705 601633729
    0xb060d0c2132030711060f13030303021b0a0f03080709090e07050a060806030c220204031a0601090b180f0904120201060b04050604120c0b160506010512031206 70
    0x1c214440c8142e0001c14441e0502c0910442030280240309000c01240c0c0c81e624800e84000401d180149804c2d035050f842c0504c0070b0b00c601d14601107010301d0300340d00741c0f10a00c5440da56001200441d50101c1c0400440030741c0079101800803240302c010070000c04151600e501d100714460008040152070030020b595a4400d1074008000d00100c01c0600608d82d40f0b44036107441c0c034a180907031401080091000901c8900c507085150190070090040c06e80e42c443c200600c55400e41241c41283c200d80d0002164440110314070013800207500541e0b850030300501980214008800103040d0760f0411a0b00c4400348489510b481c02c840ca1024101407134030440c04110003003009900c06204495000d00543c0400080c001a903001c10f070074175001d038001c0181c141c0b1417503d54028081d074028550401c1c8140814481002002a408c00460290803225180703a641c03250004a0390020442e502d4510303c0d401c1900820904011047c05010215400e040c00c0b640c40f24400d50301c0c001c000c00c034040300e540e41000c08d1070307620b0300204421 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 601636205 1250 601634955 601634963
    0xa140603061807020a0b15182d01030c0e06090718090906050403020105010614041a0c01091b150c120e03010e01020c06010f0f0b0f090402160b060d0c21 67
    0x60b062a04000194032018183d07010b07205860440005403203064411213444502e0b00003402c84040b094410031814610030300400000781e170280c000341c1c181c180640240819401c10300b10b19440c02e070343c11803030080d4040d9000e83c0215122075a0b1001e1101c030b590349080c1154401200e01e0a0b07010058002680310300300318650711a0100d40d2910207000180800b80d08040c0c4a9030280d0001d03c00303641e9a103000c41c0c01890512180e02040c1f018042400400345242145103681c446684c02410111520f06803404c41c0e00c50a400c54550900701010700740820040f02c0003005200d92040d802e600038881c0030103009141d007034100410320308080200d50f4010303014441d4021640030240003000f0000700b400c0e0170350003980001c0312100350748500341c000a5135441c400f0102050755040c0d000084041d251004000c081d070844513040040c41810711415440351031310702c00780451406000322040082071a052180c07108170042d01c860700801c010345090011030790000c03000301203c0b0020414110015080e5985010303070300c00d40c0028 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 601637455 1250 601636205 601636249
    0xc0a0c24050a0b09040c2c01060206100b040b041505121005040e0c06070308070c0f0c14030f0a1103070306020f0301080708030a02100c050d15140a14060306 69
    0x40c000c4560001d4411101100100a080040010054519021500240410041c0c4814002040075400070004841900c040340202c2c1000c410701d41c00032009030031040050303100e20200f0041a6200c0403240080003070711401454542000100787d075601c105d005002c010644000f000442c14415000c440b204c117401003950070b00341416400048042d50310300c0341c03d01c81d60030003200780c01142000c6641808510020003440c548003d540d01900c2c8203400622020a000031444c1e600045410010301c1d60626115411440e20b01d03051501d10b0309070032000c050007030087d40104840c541c1001d0000d03c4001054010f4124824103a141000918100e483c1d08014199800072a840c0f80c1040c800d809181a644524140d40302203484401140d940c1c00346603e0440140d001199049213000710782c1c4000944245807502c10314050050070054182c4005540868102525980400a26510310b03840440400121074443e2070500e40700038070041031481806907100340c0f00040810003070360b15802d803600184501500c0b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 601638705 1250 601637455 601637513
    0x40f0b0901091d040c051e0f0a031a0a0f061805150604030503090a061809050907090903020607020721060213050d0f0515010302060301030809130e0d12050c0a0c 71
    0x3030310b03c40c1c0c03040d0381c1207031040340b00f01e03001c244c500c0d00102216002010003040940951420b0810a00c0b400c03240585402503000840440440d002031801c00c045d81d02420807440c5810500d000030300702c0e0745142d0003080f00c40c81d0920500401010404c001610307084150301140d140c40c0c00380203003440c260142182d42c1c4150002800030070414088060f0807500422540e000f10282e407010141c4800040201a841c21200b641003400712740c56a034855500180c200080350803150311001312104484c1140d50076070150b4010000c010311b2503410030036000074042112070340352030408442600e580041103000080c145500803880040b071041c054400d40c01410003d121444551840c10146035405211406480c240140700e45014074a00c0c0c1c204643c100ca9005d0142483d603840d58582d80c295400503c0007513031160400040301c1a8408500500f6604004080039100f05030303143c4d1028084000851090749180d09006c02c01842d210501c003034540998290900e6810444c00345072003841601c80750031080100000743c0e80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 601639955 1250 601638705 601638749
    0x1050108060f120d17060603161e210c0f05090102011128020604080d0c0201021e0306041d0d0809030415090e010512100c0507020303031317040f0b090109 68
    0x103001300c10a50390711190705200c1300502d40c0b0580002120103a420000420129012000251b1411148910f030714200034050b070004080c200700c81e540b81c503050016802003211100c10480052489002000040402c1032640340b29028010149a2030010203100c00800c040388541d00030740001040b4240340350031325640c6a03c22008070000190114200b103000b03c041e40218020300010f079003030095401960b8903050400c03407090b14000d007440c25048011175400340110603240684440c0c92505038004000346490f07107805003c0c40b044801a0b00408680d2442242010b2006408910007004c000d40740b4125203e55181e1040c02d20314480c0f070780241d52503002106031408030740d40714010340d0585401e003c0e40d000c43c6e680d40301044040142c50581000c0c2d50030030550603582441603489030305914200c1c05d0807400d00f43c0c0c1d50006411500226040c07500c08100201640810a00016050710204210034103401c0c64102000c04889540b0760040480030940000d04240f41d0707000c2d50f8503c0050a074000c200080d40c40c0800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 601641205 1250 601639955 601639963
    0x20c07030605091e1005010e0906010e070905031f05060a03080304060213120506090d090b1210052701050405250e090405010b0f010918090f020a080607090b04060801050108060f12 79
    0x1700200398514200c0082500d4020031a80c0e0301802c1004020540e41e42081c24408400340040c01c082d061054600c000660703610306005080810903d24054900c01364040012405d0b00c500400041c41054048020300005000e00c05480e00540c2101c00181c89a44804010014000e036400c40907040e0031030307004101040800201d09129070041425a8541480d070801580c01001b1402180c51088050002e01e06412500041951140d01800480a4075036a0404210001e4800721144506201140351b013080441e440c100c140100020303542008545821244c003952035581c078004180d011010703203156280d107204074103040ca1440d009045a0540c00c06261aa00030850400024003400c840c00f4401d01175030107114060708599080181c0241e591000201e88000c15544804880c0d0581d074802c40b4001d03803074040e6101e01414012000f0300803810b00040c054003040039503006c00b4401034104010300031554441d8810341110300a0800624540b1400c0c00640c0c0880c9200d151500f14010038000801e1140000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 601642455 1250 601641205 601641223
    0x140708040b1e0405061803071a0c0712120f020a02091314060609071404090c0905091308090103050c1204060b010e0f0f010e1302030a150504020c07030605091e 70
    0x1615a040c001c1d01c0c50452202c41c0118480d2682c080024401da4501d0a0300e4541c0003251000103060710032198480c3c0029a0f1104202c0c00078000d42c0001ca01102c80c95002c01000000d040c0301e102c0e03819100703460340d120743c1401d418040510801c402c6020444906000300401c40643d5401000003405160000c4400c035150f1819100b6104d030181500c0c074488100300450418060440904240f00a9482110941d402032240c02102c084000800001540320724034030034100c40203040c0c4c0c0d55a43c19440d0208200100320090080392001504003140c0000500c0c1030204d03040000282008140c030340e640703000010a0b004034002c20030310303400c00800c010800040b5846034041c04800d0300c499070301c051402d051007818050421074035000301d03180214040c3c0c1e60181c0b4031003059105c01082d0100c0d00f2640d8001206a800584180c50555110701c800c00a05054000074400707000c1c1590210b00704440700c5507035507540700340f48070207401d07560780d0301c0411070f5110244030446071809025110b0305015444002c0907034800d180303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 601643705 1250 601642455 601642477
    0xa021005060103230705040e090f06010605040b0d1503052e0b090103061107020a06030c1b03050d05060112090b0130140115082a0a06140708040b 64
    0x41030005030590301030710404107a0410b024034618410400c0a20f01030f0024041e01040503c441800000b55200c10302c921076100302825405015070801c1c00103158070344841038100e10b09111090006203e000224001e80c0d00c21101070380c4c0410b990252208002d902600c0f600040e040d40580f035141035150f11b048485e6500080520808e00303100321a9148101100e200580690f4040807100c010804901e81d600100324a01491000919100d060b5002801c4414542c1c01540802d0f11041420442600a451074000d5500821580c01002c025600107102d44290380d80c40c091340e9a50f401054039a4402e022200c10840c3d102001c1011140c1410800d812000c248640452806030104513030311141043d090b90200280c10051990045107a9100b8000200c40750380c0354a1503503074050030340c200b4050313400b80001003030481c0c040c09000400c800c0701c25856013180c0f48040c8a8011581c2c0034015210001d130802115101d14084280c02c203c0281c40a03980702c3c0b81e0001c1c14803907010801007100c0e50707980c0c020700c40c041c95 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 601644955 1250 601643705 601643711
    0x1021c0606050708030a0b0405010e090601060f0921080a031a12150705070b07031d060609060d080705010e0d110a0b0604050a0e15070f020106050f0d0510020a0210 72
    0x410a090203541090080070009901442944000b0380c2940156403c5a444071000c01c001c00800c0100c1c0c1180c400f68440c20032120480d09000701e500040c0b04460140c2218a8080c0b0f18000c1100003030003c84c480c0c07107540003116080c0140c0c50300803040002c040d465039200e80341a5542010010040c098460101114085000114140c80a01d0309442c078480002e0b8001c0a0a00003132030381444003145800400803414004200b000c4400104258110b5108015649000401c03100c0411040788030344500882c2d22556109d50144500c90380c40c41400b55101c2000c0380c0c101443e00c039516003181d0600603201c3c0105258202810074284010102c0c5401c00c1407100d940706030359119800100c903565641e12002408000802001c01c200c0d0803d1b4005c3d40e0720982c100c2d0045240c40070b4203c264505403080c011404c41028040038001c1c2c259004101006415040c4007c1c480c19050000068280320000f480610810100030f030582044018040402c003d40c0a50f4215120402100c001e501e4103c651001844989 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 601646205 1250 601644955 601644997
    0x40503030a060b070210301a0616140c0d061410060909090f1b090506030a030801051e090c031609080c011815031d0a0f060c030902120102 61
    0x43c00081d0742280d600100494070800d1642400d4a40450b19000a2200421000080034000229500120781e02440d070b00018001c03003625001800407496030046201c0c0c8010031a144030056048615012280c0056104405840800c3c06601c0d01003000d03a015044030b00280e412040c40a150311210a5924000d8000840d03500e040503030b144152036006100120340403c005010404903a8400c49030790f4070851700007000b500d00b03850307c00440c952186007071800d2900190074000c50019002d12500200250024880700400713503006403000b001401a80c2c00f94151904224038820342e00c0b107010400300d02610200060420300d06e64011030f03108640d41c8103890729a444043c42c15124841d1341c0d0407030b010306001d400a850814011200540d01d040d01808509003101c011841c9962000034140d0b46826440008417200130801e4010000101b10142c4110740020580700e02240704d46840241560303100100145c0303680c003440d043d0001d10f484080650410261070121151080c150b00800151042c00490784003c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 601647455 1250 601646205 601646219
    0x601140603070c12020a1403030a1a031b06091009090b0609100e0109080105010b070203010b09010501020307171204060f1d0d120204091a0901060206040c0b090105090306040503030a06 81
    0x110080d600d142c0003030030090300d190120340c01002404100d0305a2050741d110030b50741d031078010144107090815100ea03000001071001b242414800c3c2c06c249014680e110021096040003c0d840721aa0102010000c07007850810000b513544000311215003400402400400a21200007401149580a60030b082c42ca0b105070300c803161a0a00903100749d00401040d0913040e075803001c004ca549001103581d2906101d032000000c1801c55003801920301900044550075111701c824010182900d07807403070849000b102000014041c2c0d0764040120b58400703420030f1102e0a001c80988000405100e1050001a61510f420600c410082607402050b00c4d001d680e1402e1149001440314041005800750b0741d0101548115110525107000e0109101950007001c00141095031b11000101a0744c2000c1d001d5950115010b14041c240c40e2041001d4090140d038401080d0500e01030343c510794500000c0c060486000c002080f500502da10941c03c0710340201d00941501c0b190308041c41c004c3c1c2c1e03941040c1d500b01a034a080c01004030f00d01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 601648705 1250 601647455 601647457
    0x4030209070809030301061218030e0f0103020c10020a1103030a0519150311041401120c06050a0e0d0c12030e040c020c0f090a060b0a170c0c1c09090e06011406 70
    0x40f10104059071840c0d10f41003040e540758070411286801c50b600ca544000d039030050380000e8203846029807181400341840c9420001281603049202d4145841030190940f04d05000030f075641e00280c449001641e4200c4d4a000395030200485118411900c000010070441c040381d0340000e4080c00340701804200c01040c440c0d810701a558400c070149419010090104080b800c40d8800803003421000e131000030340c1d000c90185084034090981205170201f52090103c0704020003402590014070b00c500e000360034190448002058034410201c0e40303200300e174400c2e1104240010801c00000500340501c550040001c14900500fa4101904040784560702d401c0002e1009400494103100710071004000a24001c01102000170842c800740c1085c410b10303503a000104959445000070490800e007529828403d48040010b10310010005084191144090100c10b040e454000340e90624062a00c204124001400101310f440c0344656105c840c03030905004480e105418041303070702d9060301c0d181e007100311900100e40309000c69 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 601649955 1250 601648705 601648711
    0x3180b0906090907180308071e0f29161206120212030904022208010c080c2d0c010b03011104051c0b1006110706080c090a120602040302090708 63
    0x220800700418019803810210680d8080d41030b050132030214030f0b207450841718118646c0048035600d03400101d0b0804d115051100004615081005d500180200e9980c40400081424000c100980821070b03550b05409070f4108044080e21a02d009801d0300d0702e400911550204a64a00080f601c100e22103102c40c1140d018000036560710f0245038a0341102542440304c1e580003464110600d00080c80f02c108540d40c0c90005245085031560700c001d04401d103c41d00071100d50703e0740c0a400560b00d0030680d00139040d00014210740c0840304085d000c2d1117a003229040c84078610a0541d403540800b0b59080d40c98502684005040500251002004900404420316080750100000f20350414000d000803c840e14040021f4001e4112a240c0c1d000307014a07503601ca4000c81d006484600031a8001030007841010b6019010030402c81034000100703041441c00201408a213006846401061000981110345d0303160603441e400100800ea01d0110220000c0c1040c40080d005404120701c40d405450110380904d218080c0140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 601651205 1250 601649955 601649959
    0xc12150a290f010306150c030201140a060e09010209030a030c020f15030702240103061508010c05040306050c031605090f0a0305030a0809030c0d0305060a030b0a06090c0507080d1805070303180b09 86
    0x5a0252041b003900c0e0005400d004404541d20703605428480102959843d016520420380440c440e0f08144950107400c600911450f002d0b841442160041d941c002009000c1070b42501300341d01414a1400451080070758504441c0d08504404040400641c080008504ca51220341c2070310b040205e0081007412008100c416803070049005030061022032240d070b20000c088194015903614407962410300a094800019005000c204081810000c0c0403507401040d90002c42010035616602e4000307000c00740c003000d030f4172a0010450301060311000d940740c10750083e60703905004080c50f910559074601160b990b4004bd00c0340002507040d1f804144c041070f0000541e6501040c410141500101d2450110001d080c000c1c4020303032100018030b001021030f440007074003401000d940340040b0342182426848001c2c1c5010300031000410004200c081d010400400943d125440c582c040851410b412010701c4040c4081d0b424040c04901844a000040507002582501c541d81400c580b0840790f0b0b40d820f001121030090ba50f03401e0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 601652455 1250 601651205 601651229
    0xb04051810060f1e0816051306030503120613061806120203030409051b0c0f0d020304060e2e05030717040b04120c05010c110c12150a290f010306 64
    0x200c04016441d06070b8075207001a8607410402da603102182843c0c0f25003090541c0030800261b07130034802c604007401004182d80511a0a000451560303403081d0350380c4507284500044032022030100d10b0598481111540100315120144007241e00c802a86000074001c001400049141ca4000544504c0040d070009255800130040c0d03007424504500c0b00b020b00402092140c800f40e03041403505040200c5d102030000c815410004207003202c3c14150b8180f07081121400315041d58030911041008070340c051100c0d1960300303041da0710081250b002c4000c600008a8050203c002c203150b5910046130689c04030266105448558440d000c640911034003c4c0c555400351005008411040c00040200d5010b0704d004018640c5171034040b1015900380c07955421503104606901c001401405c0703800080d8010845a40029030889452800700d541c040c44d076580700d00502c00ca6144000700b8002509000041d48425196480c24248004074220b01000c011790b042803a0400b485100d000400e141294440d00c254002d07141260516 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 601653705 1250 601652455 601652459
    0x506152119060f090804051801051c0201140301060507230a080c241b0306060415050d1a1201090317150406090605010f0c110d02040b04051810060f 65
    0x1c0040d03400300302815240319032a48003019801c00944280b8900328084c03080907071220b080804000e555581003902103424000389006010380d55495441c4001c40d10310200321404103c00b480107031038a0f006410005400344020000140c2c513a0410003c094031403080703810040c4100c7c1b91a60740050010066507180031340c0f02c15110000a10014000c062480300c2000b15001c1c40c4502c1800c1d542c03421001d003800301450790345051019600c004054812000811480e40e03045113400000708525003d03600c6841020824144150b40d0f190040c1300315241044401c80c144407800030b003244400e6000d40c904070f4501402c0040c020315401e02061207582d21407030749540c601180401001c0e42c00c1c8000c00240001160a01c1307800501055a913512440700240900c0d040415650301c5c00b000941000304d01501101448030b504010000542c015420480c82c40007151400780c0092980041001000940303c26131b041850002800110b1900801c00d01480b0140002c9410030240080d890f42030340c2d402c2c8201c0041c40c0e201401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 601654955 1250 601653705 601653733
    0x304060c146603030c0f12040804030317060f0f1201020c0a0501140601020a030f02070b0c1506040b0307060509060d1b0f0305010b0a08090a05061521 66
    0x3109021044044891212020b540d100100c00b102424112800b0800e07020010700e20b800e401005488010341010700003004114020003912440003c102004200c000515610210b00d00400c0c1d842140b201c1d001401946410f18008a1590103408160045503220301402c600c4414441c01a1190f000502454500c031240360a11600c020340b0001140d20203c21580205036840910240100307003801d0b0000d040c40d1340e0900b880e40c211044841d02d24841080c41c03041280340d0b60009007a440003070307062034623401121030460701f00c1c1008507542040840c02c10000e249070011000007078074690261404220110340d1250b1040104076040c818009425800c0300f2420407010740140d001e400400c030043c085910f0010301405600807036544000203900148254039290300958064038109507500f15003010803155052005200c1240103907025881017000340000946094020311442d5089544402203c040d41081203401541c8003008480311700880c08510140ea0022501d642c499000201030058521050b007062 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 601656205 1250 601654955 601654987
    0x2010e0d0f030b030c13060f0b09061909120f030f03051005010c150e0120030903031302011205010305030a020d1404030b040f0507080102120c03090705060901230304060c14 76
    0xa403130f81c58000c0544e214002d407110068000204c50300c03440028098101005009404195084100c000c0c400340046400c940303546003112201c0101c400031146907510240c0441c0d40c0724031030304800851090440401e0401c00d100000c4090640b10381c5138403044040e104803c0b002c03035a040b58000e545000b14542000b05500422811501b14000e005403656071280b103580805840d00481300081d16955040d440400911200c03400441444503019145942400d01110f966400007411a440e07980511342c3c8482103a014800a04000c0021030f41440150794030b0805940345c1d0403a91541c00076000312106590070a210314006c4105018041d5080c5c107041c1951110280501c000303100302c91b000c0004170520041070082200c1c42c02041f445002596401c0300c03010705107100c03030040e10340303885944127009020700c4d0700300440c8601c1615000c4e122a515400c2c95030040760510401e821080c4034440c2c4281035484403404100452003203025071410310000c80012000c0702c40e00140300c95424600c1c000d0000401f0042004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 601657455 1250 601656205 601656221
    0x71505090618030f160201080c031b030a140a0603050705240d0e100b030717060609061f0305060306061008190b130b2b060e030c15040302010e0d0f03 66
    0x2004036400c104210004500e245c1c09030f0b136045800301000b0207110440d85e00c8507800d6445804959103904504280226003001c0d00840b1058910040101c0014040da2040d4001c0703002c41a1030a26003003034100740d0018401000203001c1940c0c0e81c0598080030805081112030f21004086180b103064806035040381111854004984400c4003a86829034460346460400006940702800070300080d1400d80c040425240020a0384501c14882101207204015580400e84507800308007a20b40c1c0400d03558040004122051100f80e03590002c0c83c09110b010802e40c035910280c0300b200150101e41c003685802c2d04000a20710628907210014255000098001d81d640700200d00080d14a4800310741010308000050894561500705134110b640c41d5009031151400044103465603446c0740756004942c01c1c3e1844542240b00343e0304044c003100d40b103100080a0200800441d4105000d54090707e22903003003c000060300f850147c400b60010340c28011040500c7d840443c0d00301c2c0102c1309844690135010b0485051b80902180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 601658705 1250 601657455 601657501
    0x7050f012d0b09040c14100512040303090803100504050f13120516120f090f1202060702040606050a0807090e04030e010309140f07081606050304051c050715050906 72
    0x20325a40c01242d00e0f51408240524841d4024941e410705040702c5100c5100d14918440c400c80c03030800c0c0700084a80080468410403002d0f10420714507613407810107074040d03c1449402440d080f0000200151850503000031000d4031812a400c1c44a612580d90203292188142c59503000100405920800a00140c500300e070b00c41f800d810803038107060600d40d542290701c448001c00e079903200d5a0354000806903401500c03d00ca0301c2c0e4a00b0000822401c00103003074519207190141c1c25040813620003040a540d00d900c1074070051540140280001912810020129045048480080303400c0703c0108981900402e030b24010303a000340290400a41d2540c030200e0301c4005426125052513681c0511101040d414072030300f281101180014261605413020403868101a03a110a16a82100070340d41400d0300c040b55031a00301e5030140761441d00c03521103040160030f03e010f4201c01046501c141801140d42500580a0003206018050028070f2640e800a030340c042d0b440844200ca841e401c00400100c814043c62180304100c111 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 601659955 1250 601658705 601658711
    0xe0103080d0e0f06100510081006030f0b04110403030201050106091202010806060f03150307060306030b0a090c0b070b0a1107023001141006020c0108220c060507050f012d 75
    0xa40d0030401c0c00c1c48410317107410a00b03504070103051000c0d013040454015a943c01c0d20b4031181c103142005401c0349040d0b0f607000c1c2c0002c1545807611602d0200640d04038007220040180100043d01d011030120304191f00c984422000744d42414000540e0501411110301201c0d56080c0100c0c2c1d075a000d6004440c0102d00500d400d500c001d043c051500d6a01600014504c2920ba061580c10703092a00310406240c08c1c140d901c44020035090500510025440740141c42d00507039200d90114458405251440120100740c00510400c0f50124a480c1070203000d405042c045d686008042103030b0b40b41251b491101d80314560f0040e400c100c01c801503032011642003104400d0b4013040015004848041d4507010300396200030403203214080f80c49043c0b2030384141214030b0100601c8030b80011700901524900103890101d0040000388a19002d095025615520071291102c103544003025400868640801403c96084114203a0301c502c81c0c0700003555148414491130310104e01001038040c15687d40d03c1c0c60768040d40c0b841d182074600c0c1c0c0c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 601661205 1250 601659955 601659973
    0x1c03050903040b0f0913180b09071d0a0b01020d0c080313021005040501021c091511060a02040305010e0a030909021e120402190b03040624030311070e0103080d0e 71
    0x3c0f02401502c00480031442c850f0b07544c0d880f00100010781c1c2e43c4044200c082d52810458403c0c5280d01c0f0864440c03150300012294107965000b00040c10890213074004042d12640700c003601e521503501100300340b199050321400c0001c800c200e001240c1d103546008202003c03420400000340403480174805940d220000d00140c0c0c400600a601140345000341460b12804950302050602ca1580c050100d110714820740f1543c800e1485141d40c0c01440c0460902c15001c8110140441068403482001800010030b03001c0c0031660b81d4280001c0c5a070081d80144801d6525502e010016416281b0100b00a5102a0166070f01e0704d0050420440c04000d6014184091540c000c1c0c130703000012890408007600a210010342c1c5204280740034014072813500c0c210044501181503800044c86110001d000707a0303030045d40281c0005a00d2800c15200d03a00d01000000101c03100ca8141e00010405510004103945040c010082c1c0340303010f90f104415003040700203001c02850803105104840000074982d019a0702c0c000d41001b00c5050344 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 601662455 1250 601661205 601661219
    0xd021b06162d030209031209030a020906280303090503030a020d08090a06050108030307090819031b0b2a180d02032107050c010905010806040f0e0d050d05091c0305090304 75
    0x20a007000401003134003c96010050303d428000c003e80c0003501c00d1160314010b005000a82c480c0014880240700300b000c100458820f84070803001c08415010044203e0141079080c60304c122001e624030040300000c456003008181402e000c400e0300c40300c0742e6580050108140d4061300340d607084401004005644620120f20003c1401c90044078000e01b520009541e990030001d200616809090300141c0c9180d00207007114000d4582c035124659429013510300040c4840344124401001140c2000c058507082c568010301c8911290314a4400d00002c00e80c031100760707880c50400195030f180a100080d8070103801c00040031942c0c7c24001e41c1001124402000e407600913171800e41c880354402c0c60742500440107401083c0c520130041c7c00c1103120302101013402c103000c07054a007600007800a10b00500da00d0045071a00307681d012559141c0c203d03100b80a801810f442d40505260380045c242e800540e014040b0302c8c24000410341c42940440c031301c103890a0300301040004403804c4c2400d402401e40500081041c0c4400c0000046034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 601663705 1250 601662455 601662527
    0x607060f2703201005100b0703020a08070f060608030a030b010306121103011b120c091211033d0903080c2b0207150510120204110d021b0616 62
    0x44c0702c4400045a0a003406108007000054111606001041240c440441e40006514034116030000d003ca60b162460318150540c006601c80003414107050100c0461020004006403441030100d81c0c0811030304800c80011019200d480c805e848a094018030f041d000b0545a10a030550390b10094000310ba4540b00083c03464121400c0d89a240c001410710038928a80c0f145e6004207425441c440c90451810340c280307031205800d44241c02d0020941d48045241c81c03520349050100507003c007080d18000744000b200031240f0725045030282c142c0c02740c8440700701000b291241e40d02c03070107440350b4041d52004541d0b56a400c59a24691160880044420110050030580780e0303086645844000254800350b29007416150121142900014480c22a4103110030020be11600c49000c00c11a0030203400307602052140c1c00840e00034040694600100c810008944007580d10782c0c0c0080203110740c0560700341a89005501003945a1200ba40d1810214100d07021000c0c0c0c59103d00c2d000c17200d0141c07400c00300600b4421f00881590dd = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 601664955 1250 601663705 601663723
    0x91a22020c060f06030607092304090210030c090803040e0f070c0b01030f06051501020a2402130e06060315100e061209010c09080c1e0607060f270320 66
    0x4445001070420050703045c1400001e40205031030401c3c900c00e60814140900700c424a8076038501101800e8014010b59036540c00515207103030013804000020000c83c0e0004d001e04200c01c55000400c44160001900c002d0010484080b00d85610a10003203880708500d40004247c007400c094100501c0181c0b62022804a101d024000c612410038100d05040034030704402134810003418a050703000e441c140861182d8021803102e0020f80e000e4041c6e1100f40203218000d00700003c0841d4000c0c0c171440400d0b40c0c1d0481041403540e10685409480406c3c3d02c1d030ba00010404144000c844813240076082640640c134904103034035140d07084480740c00e0070b0039070070000c0010403c1a0401000c98180c000c45500b442000741080c4a028009455443c0408240e820182a5551441608402406030100034411000c0c203200340c00c1c080c1090700091000c0e0f565001c506044000d015140740c0507038441e20b1301c02650180003000c11881ca1000324100768880e18000e070b840564025800070107060f40ae612000910800490511000c84 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 601666205 1250 601664955 601664971
    0x100218060d06050103380301061502010f0e030304081606090b040f110102010b0109060c050304050604080d08150108061e03010f09030e03060106050403080d02071506091a22020c06 79
    0x100d42d0b01d410001010344101d6241c0808098031281c0345800d003818141090360050840401030301c01500d44000c06d0050581e40e04c6440102c8200700b0300d200b02641034001001c1c40c96014001c0c040c40310b2546441c1d40701d11081e1802810840c003003180c9a50402c1051145900d50b003e0800025990782c940c41f150501c4030212421283c12113a0301b0003c0c104034000d151002002e00078170003001a0b207400300c006072001c0414050103040c01001c0d90120108079080048901422005e030410b9201d035581c0100c207070350b0307200c200b1000d020408010008004d0001c00784000e480380b00503541d50303800781c545c2020311495201d2640c4070a5940c504000c2080a600d00740122100145008070003c0c1e80341140c00c0040884040700c64652080d00031400421520351f0010545090360b41040c403956030f490124103614003d1241c14030040912440740804000718806904c10001c8800c510418407844502483c003904020821801a44c40003c00039072800ca9689446103003512030a003030b030052400112055040c030b0700c0f0b802c544004c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 601667455 1250 601666205 601666211
    0x17060604140d03270501080f01230f03012406050a020601120206071205220b0f091c0b041401020a090306110d06140315040c03020114040312030f11070302100218060d 73
    0x5c6592002d00c007544151107807003500044d41003290117400010610440c1030408490304801c00c10b607442204d00072001d44014002c01010f17004070701c00070041404072220509070400c07041c00502140550116086899030f54050a82e607070030440c424807a070803121010780c1c02600a00200002480d0008807030301d6400c0030b0b15441e84510003e00030b81d20f0a4807010810202618002081049413132a605451045d41070000e43d54481c00d0441c00704413480b101a01485002e6121006181441814440741c0e005601a5003a42130b04040d01036031030700340e200c0d00d1518000100110000c101050403503204000b0003600c400801e28117445500124203452003074100e01c194440400c0c914201c1c0c5020081080070751502d8039400e804d45040c0d11a600528450b00c0080d041c80070300f051519040d500074080710041c560040f8030203103051800078014018001030400001007448c0a0b10040d1000300c94040d1040180d1550080094166407141c0001030b41200a065010b18040a42828590b5a00000d00000c500c084400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 601668705 1250 601667455 601667459
    0x1b0b0a020f28291518010302300f0f0c010306050a031e0803041a01061103041a090303070f0501060603180303230717060604140d0327 59
    0xc203090080050001e60200750640b8041c42d00d4042e0050a80410b40203c08010081c00c0c403c03c00700790a0a084001c0d012207030a1040001c10078208000c0c2031500d9081d40e2018880149080203d00001e0038000a540325014500c660031420441007860421725000b444600c00c3c1910310150b80c40d000d112a030075106034102c0465801000420482c11503481c00900e4240302c40391170200481c14402035400080d01c80d01d03146c20004001442c40740d0035500103138031203041941c80ca86420f00615a031004d40480d00048a4480009044c2d0b204846500c0110030038805145094948103142d1418051140703190711422081c00b0800c440e0341c00740040c0c00c10902500c04107164440d5841c060307007100c007550130034001e0502d00005020100f1811a1300a0b00b554103040004000126075282042c100da045113040807102203104220503035030300c8005a15080c144c243d41c04882c0e11070324100325890185003d44c040d02c1c02d00c500a0030f068a0044800202c05010341060700e02c3d000d0b0110f090441c0c400303040e0304110a006403e01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 601669955 1250 601668705 601668733
    0x1050d0204090b07111c140a05070507091e090308131a011d0a060b1e0904050109020d06120206190c050a030203090a080c0315060a0906120209060307121b0b0a02 71
    0x60b42c0c1289481e0020b03081500c46ea0074014002030f0b8140c034040500a0042905003034203000c0c0b821078001540220488170a690354040f500301038042d1605040300101e001076403e60068a6016030103010743c3c5508c1e01205136503154100003107440000c0081d50001c0020142c1d00304d0b5440101480c0c040e00304070400e080712840d00107003840b0324800170742041803492405200f0440f50f8540e134113071218110503440b00140700751840620b80860040e00d40e0715034860f02c0c000000a40d49019401008160303e13440041c000c050740d07800c0e8141c1d241000e41d0041d4012200704590f800610b002001e800007080c460602c50700b80354050301c84d2441c000d000241200941e200154203620381c500400c9003030040c0340340401042400b03440340c0441e803117480c101080304070ba00110300401c002d40e8410303103184046c02c1810f104101542e5104100c008541d60114107134001c12005001c508181008a1a582520301301200c180992003159a91159450642a03180400002000200700d6805200040500088941c010015400320200c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 601671205 1250 601669955 601669963
    0xd020c070501110c012115050906040c090e0709180e0c0a03150c02070513060306050a050f0403140d091406010b0c1b282c01050d0204090b0711 63
    0x42c10301c50f145500c01c0c2c964200080b4858908000e1800076000903034078610000300004020038081c29400c00c11070b075844110000303d480840c0d6080b03c0e02c8800303888031401c1c0801c5811401484000500e12a000d110300807140741070a400c40d9641c40e0602040d651281084e40c242d0188d00040e40c1d180d150956181012010080a01c0100f803c8030b0140010b0b20b03558980440ca101400c001c050fa90301c44024043e03190090180500030900a07284d071200b030385403404510003003070750b400304544071490b2401244904840d440b4241c8140d44404206401d038440707031401c1d50b903c0441140b50782d20503010070100909903080d0042d225121710030a1103204541502880c035080a0050b00b040310041d800f803200100c088800681040a0380010401e4a154a16880804c2044503016080500c00440c1e208014210780842c0c3c40c901202c01d165249440034000942460720b4442c050818038440107400010b00c070500c0d20642030440103100400018602d0340703c1e41c0300c0d1407d050888106020516490310301c1d0360020244 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 601672455 1250 601671205 601671209
    0x403080708120703020412021e06040923073219031808030a0b060915220501090b280206010503010b0405100b13091e0e0a030207170c060d020c07 64
    0xc2001d5007071030300786000044d0079207010101a200301c41400c03400c9e50130040724a81546040c8003606440e5511f0b1100e4a610280038004200c1c103900c00d1000c0d05260103205402f4150280c1031607a20301520b20160403080c2c0c002600368031480c01407003c40802c400c1c00d0b1502070051408090510000301c1c2d40c0700c4410b01030100c810350f01014000503402120800000c600d00d00310380e480f09000900040b40031402011504030300504800c01d03004003140c907607040c0102c1800050810042c1100081c00100406804d022960145108103400709464040a01c101040d940c0600300012106140c2c000c0f010421030b00f11040d94120401c040981c002c5001406541828010400d9034101500c0510490400c0d0301c04c5900b40409204400715100080b0f500f05029a41c01000c0004100c0328174144032500c5042500c6221a50158a441d002c0d45041c000601e4001c010030b00c03160181e01900a4140e440c540f90b03281ea81c40c0c0c42d001c2185100d0080f0181c7c070009a9420020b004c1030994413400580303964402d4106481c0410355 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 601673705 1250 601672455 601672457
    0x20a14011401030605090109061e150609030b060607060c08010f1a0319090f03020f0d091d04080904060609260d120f050c0705010609061203110304030807081207 71
    0x806188681d07000180031141c1102e61200002030b4540d58924041d00402442100400440c20311180e12600382420f52040c013180d6109408114180341c2142c0540100f0140c0300b0400856243c00082020501c841c2c2640d92165001d09014544000c41d0b40d200102d40c0e001104001082250700180328224140f04888094420201c03090104030304070103602c1d07050100805110381010121320440c000350007074012122040d402408540e41d003000346030103500c58041240d410503600c00c405c0794104041c403500c405011038065840103000c0a0010200c407881400c01041a143c20a0410402c0d002c3d80b074a00ca218000c18184e03684103d882e0030007505a182da0742d2561032068030140c2040040c40c00e0800705184003540c484bc100042150b4003004018043c14203500e00c41c10140ca0034040101c03280304030f0010b0a020384580020010f450b00e8425120803141103000d11000130004544a0002074045d680340310301e812050040307034100303a0b80c2d50302c0022681c0b101c401210801400f045075030781c071890041e8042e041086 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 601674955 1250 601673705 601673711
    0x21030e070e0c0f03060324152d01110d1206090b010503010e0a15141002010504030e06092407170f0a08041104050103030810080109020604031b0e010303020a1401 71
    0x1240400c480301d80643c1d018005035042c0000824a80d6608004110b81104a540c41700f403404462051030030902c02c12110400b03000c07901e48540807185040340e901401e5003010240003c103000c660b46c800f1500c0c1902c0c1032139418000c05620151890300c080201c3c0510042d180c0c3e031501760b0f961901001090f10059440070307184a00300b42c91140b9070707a009410780c0c0c10b5138294580c8110315a54a152480688140b1040d0611071074404008102e41c43e1064010004c0c0e83c0a0300c015071400e1a5030403ca007244c20884019000030003400241d440c0745001e40042481d00c20003031004a0b629583e0210441307007111035104840b80500000c9440800c10081d2000706105008100c4901f40b424401180f61144203e800f2a02003100c01300c00034040206100d298600041d0181c070030811580c503071401800c41e090030f0311520b00100c1e0190307001404980500403420301c540e0141c09641042e10350f40d145941d034403001c01030764800f054484012401141b10200940254040d80c0244151400c0303040c02106403803000003120b0b490741 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 601676205 1250 601674955 601674961
    0x20c0102030306060a031e0e071406160204020c0a06020301090603051501060518040e1b0f040605130902011707020307060501060504230a2313020304020907050721030e070e 76
    0x1d0707904c0c1a0b07007540045040c0410a0344112a4001d440540b002d44c180c034080ca0900c030b44540c2e6500040d58001e50704c502c0440290303010400d040202d60300840500d0460002017260030740050a2603006810312904010480320a44040d1356800d059800980240c6846a030391038040050103804c0016083c3c1c13080000010342c15504003180140584190700d61120900c41c04c682040d10340e1200c0e80002c0d90500e603c020344111204020104516041c0d041e0424403842820f040a030540c90141700d04021144002c080d0304403c80c0800c01715014103a88041641402000c045207680c000400011610a40c07069024558511542c50040100e034010b8100c2e0080040602042c0501040c5010300c5449225024a00f0895280d4000040c1002443d030040518600322004800c1441008845580000030490790039504880808540c0b00328041140c02130341c031910000108460394012401440000c0c0100e20700303d246050318202c01c02544680040f400040e0351a600f111440300e05000030300140072a1201103000d81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 601677455 1250 601676205 601676209
    0x612080c01230403030507020a1a0601110c370303021c0503280e2d12030414010917030403080906091c050c120c0f070302130216051b01020c0102030306 67
    0x500c0140002c0071725648501080b0b055008010142d6281e51200240754044107000e4503020f90030054450501140741642004070841011031030455900004d0940d1080c0c0010440c1e40c0404507500c3c08024041965501168002c0d543c14400320246000b50024401c6510360800b414000203c510002d0420405000340300000c0800b6407800fa811510042d82c454145042c08084010b040181070138040b44517403902e80b00070788010300000070b0f614803030300c400c043e04024110034507118406640b6a1751816401c000007400900c039428400103100d504000000d0815880d540d912245131b8250b100c100f550004001c2104140d4005d00355607110700e0b03d01c094a901d0078001036460703955100c3c000700519000c1c01038015403c64898810703540120000c2c03007291610401654003038841c2c1c0c409603401c8154007505441007144880000d04000322640940314014440c20b00e10350303500940201001c90054945007000340c1c0404c60403c0402291141900081c1c010b0b00c0b01c4001916014644c0d00d0039040d500144100b00013a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 601678705 1250 601677455 601677521
    0x609090b09070e060903100501060e01080c0d050c0409020a020102090405090f070905070203090307030803010512210d0f0f14091b0907110a030801030314090f040b040612080c01 78
    0x80b64200b41a00d001e40000107031036800340600701c54041c8103032440c0c492989050b800440c102c40301500d9005c02c2c1c884078401181c03080c1044503007030030002c0100710b41485020b407580f001d5408031161140c1d83c2080e8a50601c43c06036880f0714003904c01030790081010552850103208250300030881200509106000040c0552101543e1046007801070343c500001e00043c2c000c1c012110290b0004041d501015200d00e450840c0b9002801200d01844c4100034010120301c000911f00b61641d001091084d03586400141d9070041e6004405d080b41490702c416422513005000c1c0074074980c8925845001c035512103a06090901c1c000000c1610f20160f01c0150b508100300c000c04ca09015088069421a2003941e40417401d0b90100b481c86015192441403107088030501d54401c0c5454140c80c0309a44000c0c441c180318813113540038000d0040e103540c040080b0300aa0103928069000001005001c4c00100c1c94036a40c900d9140681c0c540c4e1415100b00c0d50020b15040384040a2084065480d0b03017241c6a140b20031540c0d112000c2d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 601679955 1250 601678705 601678711
    0x7080301152604080408030c06152b0201200c010e1903030c050a050d050c010501050a0f050d0510020c07050108010f0e2706130b070f14091c0303060609090b09 70
    0x28000c2c02d60045020701c024082210007510042c02101d0365100a040301c0c1740e5a01046400742d94141601e031203814646003041800407601c0740341c0c2c00d88420f0010f5421008000c00c0c54030003281880105c9400c01a20108034844c07141d0a02c0c24006004140d0301c10001529903074460301e105100d405050100101c1d440b180300c43d00300390b0380c00d0720f40349005120704d140080c030700f10402c1d1003e802440b030004100701d0103038003030020021240c80000901c001d036655010301803011140d0248610303204d0368000c140100d0400c0d5484100d102d00a000b180d44440300780c030000040303070710a0313904100310780140606100c1c55800440b4940140340a0408003c418a000103180882c200608200c1214804028003070010050401d284030803041c00c07003554445d041c150855071410024020454a15000e00c00085806c1d020b800e1344000081d1544404505a140116064440d03100040705907202c00d000070b11260302d6841c45000c0c82da6505ca52070025100d07042000150041080ea8400100c0c5420309503010002e4075405800c80d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 601681205 1250 601679955 601680017
    0x50706030f0908030c0a1202040e070f02030d0507020606210a081c0c03020409060905040f020f0103110403140105130c2304090f0b130b0615040305030708030115 71
    0xa80290061244020b8001400d028003200ca0201c24000c0b00e20036903009044011503a1a104107502c918407a05050740034a00c50280c5c46020b5400003103882d402442034441c00d040c1481502d140a001d01d400d202100c00c01d80d40f5000503444031080142c03d01b0081c41010107040c25100040c550400110821740d00c011440e4020452100406c0ca032002a01e01c0042003a803101610080c8000c0f001050010004e4001e8801d41c050181000c80c0040e08200070701c41c960040ba0000c0304c480c0016241d8090000000d00250002d04041c2d4038a00c03090884080e00151028600c558840440700c101d0308080340c20b4400240400e80c140085600c82000144d00d042c80008a41c0e4400c203100f03000c028501e10381d20080d8010401e0327402c942000e408000b0018004421050316209040c43d0b4450384030880310b440d90700400c2d01d004049809507000b1500c40d00d4440100180d50340918400c1c2d00e040e86035601c6078250341041404503038080780440103011300044204502207950941c038245276405802d40807003400034209007200d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 601682455 1250 601681205 601681211
    0x6070203161704150804050d0c0209060108090705130911150a0c031b030323100b09061e040f0806190203060d061d061b030117160905010311090405070603 68
    0x20303440041c88140d070010100210404d181030f0b42100041c1003144106c404903102e0007a03442d45070896004401c07140d202c0341c01410140103035460314010340d10554040c0c4400007510403800c0028180c0c0d590340a108910300305407004540d01d0b400c0d00e001d24090500c03080d00d0344214046001d611b00c0c45107501c251140d012032450700301c1d4080c07071750305041d101100e8a00c0d96648640f40d49100400b8103405404c5036074080030700701100c418a25200505a881e40c400d40d0001183d042503a42001413592042c05044d0340d901c014039031860003255180d9010082d45690303510200050108003000b00042c909020340c004c00344140540b03a9454541909140c034915981c840d100d00381d020010410340d0300ea2014096070700d58021381c00c03c145e0311421a080010307101c134603000d061841140000365406010240051807440628400b604607402e0807581c40200303a01da4101c6c0d40611600b40000490030015116400405020384c00044950440c10124000d03100c00d06064013843e010740074400080d0700080e04804442d031900d000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 601683705 1250 601682455 601682483
    0x23030f07060e0d08071d0a181103070908070f03020112090501090212061803090a0623030c070b09010902090a0c050405060c0c030105100e01120602040806090c030607020316 76
    0x600020098a10303008858400c1003003126469401c05103050240710300c1c0e01e031011041ca008503c482101c6c1d04104d01c07908251302103c1045002101150340603414114000482c40003443d1040c2c00080c3c02c100d03600700c00a11440b030204081d001c01d000f280060031007101c1c0c035125141103400207030001c503081d014042c5650391051103105004007944015206580101080300e001002950960b0755081503232030000c602014540c1c2c5004a80000c2140d418240c058041c6440514084095600e80340100108031135041800a14050014481c029481040d1901545441d18401c3c1401c44920300000e003d0700540c0e14101c00740003d41e070b80d411101c0d440401c0131404500d0117052142202d15005d0380e80180e40211010508081004010600c00c90341c071411f50003041103030b840600c04240380c00107100c2c5024031034030742005020301d455030898081100d01610b000f5241642d40c10303169140c18070031110fa100a0b0441003400300d10385406d000c62a000481c0344001c50030804d0702d4a6000a040f400034008083e1001a015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 601684955 1250 601683705 601683713
    0x70209100801180201020d111005040c050901090c12090305091912050f190305040902030604090c03030c0629040b120d08010e0702160b16050105070c23030f07 70
    0x1040014254070320081c08400c00c0c01c2d407101081c000c0802c0880c0540508429041c14922031005060500100f400030040402400d10000081c4805001030701c52030614030010a8580703542400500801c40b0020004800c1914400107042120003000c44035110700381205440800d42c404280c61400404803030920074080c55600581e0034120942c01003502100280c108818080d000c13030b096100b102c840003a81c8500302c00d10362a01e15030011403002004140e045c0014010f1082c207074007540e488a070180c030000744810a80c5640221201c1544114002280c010811041001c68000c0c0d89544080480c00d04a80c2c07800c0c000700c42c0c42c00042ca40c1901039556103070001d50940e125400c80310801c1c8070b070007510300e00300001d5001000c0100034090b01e0a40a802c1d13011888803440010501c02101d81604c01d100f040d400c0c4042d0401980c40000e400d02658400428240452401e1080c0c81c01500d06444500c1212154074000440d03041c0000004048154032102c0c080d8010302104442c501d1520304185503070f414035454 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 601686205 1250 601684955 601684981
    0x10501260117100209010512100f0e1503010c09060c0201050d090b010f060203090303091e040f0c1103120f06060c03041508090c010c0308090a05150109150308070209 73
    0x900050300c00301000041c1000c1003064480300385034200141d400110090700e140782a1300c1503014180c002203040100d110080d050036002508104070141200042d17a480c0140d11419400c0c5c0c10410004c0b05540078050080000ba000d026403103001d4000b48001020700c00058002c14803441040700303111022541c00c1c01c580c860411510f02d844083d00800c5504441e0608001c415000d0064038458610300b40e02143d81400001a0741d45c1250050055103045102c1040c05840417201451444000768269002c005640300c0c010444140f4265000050b204c0040e20020041d030250612854581c0003000349540014280440561003040e020b94005503454200c00328446105010414506010100c1d000c03800c0040710480ca003803000990b5a02d400c0e41c40b9040c1243c1c403103541100060101c0c80c08100d0a001a0040d05c50a60000d1070340b0980d003945405441c2c05040c0400c01200c0c00604510000500a915a510a520082d074071400c810603401c2c2503945010b080d00c16000040d2007007a100f0300042002000700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 601687455 1250 601686205 601686257
    0x30c0e010804080d0e070b0909070203040f0306021812010c1d0a0b130308040e06030105010918170c030726070302030f3f090303060a3b04050d020114010501 69
    0x3021910000c0c0c2d40c1135280d030123801c48100306101d001c200011078501440003094805a03180c02d60f401d220310b46140d442038000c2d8000d44100340ca196803040c8039036095a0350381c4907860306051100080f401c00c2c40304130010013040841d03452451140980170b065a1700c0d1140000e02c0d040c0d40d0440e42c4030f550b41e00e072980b0340002019a07030700050940e07d00050210b5054400b074403207070188005400920103070341c0b10304440f01502d24684140781000c0e440303280200841c1c905000d040d00340300c0130640c0b00d140c0740c45140880c0c05c41c0c0c040041076928035200c0c0110f00400340e06900d000c8030316030f0010f03006040a046680003903c0e0310520548040d441c0000c03038002c501c0d82046409800d0701c0c1c1c3e256020080e406218003450034070a4034030b040090301011003000a241e1003012085a2045800400507080c860826058021460321800171200f0f0081000d069a81820000c6a0492420106915102c0e51a080c50f01d540361202c0c0448080459040c0501a94510b40602c3c074a41500c1007401c08a10103a000b804070200700400c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 601688705 1250 601687455 601687481
    0x3100614010e1906050418090816032106050f0f010522051f030e0706022806090602070516080a1103150c0301081608060a02071401051501030c0e010804080d 69
    0x160000101103410900600484a006900d01611086081c0c84004c84403040c230051700701c100c104071001000320802c41410b4403611074100010f010700801031030300403400201e10031480c1a81da00b00601035854071440d10010348504940c5030a1200720b51000900c180510300c160114180029a104070f01c1c2c40808840014220241046030b5484201c8050b140e800c3c000c00030000030030b03d032010000045a0100d50002902c0036074009052151a84400074980e2a4950341c400b017414480c0d44850026440f0701440088501076000940c43c1c0c0d10b2414000c0c01c0c45080300221300c0d80d8916000800c200040403072040100c6401c0401030060180e0440845c1c01e00c01c0080701142d0109810781003181e808154000f842c141c2c0c0c0ca150440e0441c007100c00c03c0f12010f2110340202882d82e401180040c41c050f0482e0002e01482e8822510755002d400603480351400c0da02c003a51041c20820b5240310b0f00d000c95074507102d00303203480200b86081d2520251020011b0005600904080c103040c000040c500d54104442d0400c0b2010840 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 601689955 1250 601688705 601688749
    0x20f0f0109030f081201140a060e0406050a0306020c0625080606070b1e010602010c050d090302010207050d030f0b1c030c05070f060503010305150f01140f040f05040203100614010e 79
    0x62800b500030754441a065803048800d1000421f4030807681039510201c00000d040740410324201202510304004aa0441d036019456507030101d0705445080c03640700150300c00e00d00961204030111240c0c0c14950020421508190308119a885800300c800000130352021500384518188c0f550004038506100d01e0501804841340e80c800e0110418180d0f010000c800c420a510240c20391721102c2c12400c2e9040c0100c7c140c0011814480041c408020b40c0c071043e0700510900006180030b80565601c4e043c080403441101c00310b40d139501a000349114a004214a20700c007228002404030812851107801c100a02014040103100800b078030402c20104441000381482c50400d500c56030342d07468010302541c000d0008451a0161000185072104050003d6019488000c1460702c540c1c00c0801e13510150355074003480c2d0303030212644070740600c0d90b191445801e000b4500d540021403c4d18060041c1807800440800ca09100c0c2d151080030001566100b07090100301c5400d10b082c5440b811800000b0f5201c0e242e188400c520055 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 601691205 1250 601689955 601689983
    0x1503090606140108090c010903020108090f0619050702010c050304062301080c130209011b08120106080a1b02061302060c011a120a02010e061b01060b0c1009020f0f010903 75
    0x4500303021852004240d95898240c1d036178140b07480d2103440700045203010030000702050005600402c030141e4171003280000c8071140103280c4085898036009031542d0300c90740c458801074102010305010303260b44900940020720610303400b400300420520000780042c040903a02c668032055140364500b00c012582c540042e005c11540c560301129203801078407520034401c01002c0800c482c014164001d441005005844500000340f04216403194425441d004560381c24040000c0e203c0303088060041400780c915990b540d403070307413500c00d26040403100c03076407400e00e450f2004030070b00804580d00141803507015030301d1140241d050b015480032440d01c0c01800344040341942081a24070f44140860080f91a812003201c001c0035801c01c88030299151001148040c2c00100005551031150800200810a17151440640d403020442501c00c1801c5440607089081c5e01e0703100103405801044108968001154114001c225014550740021400607403601c055001d0019404030021903806814100001c5030840c1000541070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 601692455 1250 601691205 601691219
    0x60f06010c17131a0d050c070602131503050f060f031603050114100305070b030621100608010b0105030402270403030b090f04030c0b0405071d040b0c0a091503090606 73
    0x14001085030344690f21150030008100c4c2d42d1070054120b00a0901a0302e26046040c02010040c04005180c4062108100154000620503200030803049443c40ca1a1440034140700000e05101001200e280406003494140441e4015015a40c1e4008408640040800c7d070703210003203030500c036080c410160090074115000040c08410b4120b801e0240500d56031842d55603c1709419940d00702c04e800081c120b648009414000d59140c100219003021000b031681d42400075145c02d01181c540072200c451002d03080721041440c205032a00601c0050b0200174028000c0c1d200580000740345000061000c3e1140b007101041d003224100c0c4120500e690748140e422000c040c9045d00700036000c4c00140c0c003098007030308080d400644204a0000c1d082d0103540c0c15030398685500c0c00c940f50852811310250003030b1840d004a5100150340010486c401070524881c070000c8080d441d141c00d040302d42c1c04c00108461140c1c8020000010300c0c56112002005956004a032550b40100750241100200100c1e00020401331030301c0340100d854 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 601693705 1250 601692455 601692457
    0x50d2a0201140604020408031215090405010207030e010e0d0209060d050f07061d0d0b100b030a0c1d090103081b010203070504140102280201141201080f0f060f06010c17 74
    0x198071202d440c007105884510500c0100e2080740300341104c3d90010f10070fa541c0310008100581d04a00021081c250f0015528002003c009095404844a030750000c0e5801c20150085c01c858403107002420a05503104c0f804010443da0751381400300234810f4141c0000203003551707241032681e50f00030303045402c0b80c244540c0c10713240d19030751101c40c013440c0b0126404041980c07062461006a86600c08040c0894480451316601c11042f040d0140c6903001000c0c5280e00807680030325032005184103d03070790040410406002c0c1005030035800440d4440014144907402070106032034205400381125401941580e41b01c8200b801d2000c07000c4610345040545d400082842102a0306c2409401030b02c9804142c7c2c42006003040044e640c1c0c03220788030030501c10600c0c001d0343d4a20080410701e00c03401343d00605050007080307580c51441c0c0380c4c2e074800c002d8242d052401d280144000070007000520118070301395000301204c40424100a696a10041c2042441107000b40000d40e41d0b44501502c211140d4013065405028015980c51581 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 601694955 1250 601693705 601693721
    0x150e030c01090f020312040b0a0e0102030d1103071202030f0103141006151d0a03080a210f0615020c04200c06010e070504140405090102120906070816050d2a0201 71
    0x11910504015200101b0410122011100605481c510b003207a248400c3c1c0700f20b08008489419404203016201d6400258040c0040c1001040051030f41d034500a4405068440803560785c031512071060007042000c01d14441c100741500c1e044480c01c54150b50010b02e591030f1070201035842105504100000070710600c61842205110082e031070341074200205500841c10041003d0003680e02211043c000c0000c42c03d1500200b40c40111803600d841204541194141c001c50fa810100e80780c240d60b020411f49100c0d09118000c0134185a80da6003070002180e05000395124802e205a6100d55968550f40b01c21030701d180000306011701d0010446455204260710941c8960003481101e590030b40b10400030341e245d48940704030b4058030007142c0c400891840baa001d01c0004c3c440141001900e41d401c001c1c00010b900c85580d940c4c840c2c07010030028840c6161118000340b55080140c14020203001602c1c10700d12030754104040d1004001e10280010303942014a805803180303c42444004860b602001d121000d039075042d040844 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 601696205 1250 601694955 601694959
    0x70f03050c010c111216060c26070602090303090a1e05030111040e0907090e07091802010c141509070806010f0303090e070c1a0121150e030c01090f02 66
    0x2818014010064983c0c81d00003800500c410b06019072804646131001c1803490f0741c0305a40484260782c410360b02c0c9180b040b225422803030106004090240401000726070200ba0203286129080c460307450310911200a002d01c10300203010360b80105120900d514108252210a64002d01d541da0060382e0712000c1e00e031401c900c0311074075100000d6140031070981014021510148250965640f502c0e00d071156075404104c1c041c090a04038041c08000180b0841030703003ea1080540720340058080f007498409010304841c50003544030038101801406a000d80c3e04004403442450f000143c00a4252941c0401d070304121010a0321020380e581c034070602254940c0080c00c00c007a11404412a02180d80f10384022010600b60310000300019081902405100c110118464001c0310a00701420500032a81d101460f045000c6143d02c4100c5001d0300401110416a2100702c0b071640b0740324140e045545a031520345000340865a160301454460040c8007409808000300d41503c09144001c0125044030b01d000107520700c0b9914164 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 601697455 1250 601696205 601696213
    0x303010308040314070b09010c020d02091e0a0b0a030f050319030204080c010201061a09030703080a0f0306090506011d0f09180c031212040311010507030b030118080405130e070f0305 80
    0x440d841200044242c00c0c2e0340000405802c0c00b0107e001103a0b20342d0011400c07a001580518a80016110146850b00a1222171aa00d41010079030203010040d000050402103060304000045401e503c038802c1d850103480e008002c0110404150816a142d0300c01c074403144400c0d602c40d401030b0301440d030b240e400f80042da035443c01520b0740040001c0049080c0c3d407082c0210b4040244148035100a09002d0006001860000d0103a0395425526110000079800104d403003004140850440045c09a2511450b0050b0900341420461800c1500c002090700b982600042039098103c0340900095442a030800b490704002000400c141c54146c2c081c00021401c0000b55500c2e1003200300440c031901c0d0100e07000c11941481902242007051031b01780220400005041a005e001c002038032114081000e000320780c480c6070b06440128030207200070180b508403001c140719114503450000014000a040e00122400c980003203408105980a4a041c1d46c01030801c0300f1207641030f11440e040015020300c960070840032640500f0680d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 601698705 1250 601697455 601697483
    0x15140c010e0c030c010815041d0606040c030e0c04090804050d2301092109120605041202071a0f04150f0e010305040c0b031509100e100803090d050a0503030103080403 73
    0x8113540ba44550715250106280d02d000606010000f400345d850030b5001440414910f405030745041ca8443d54031320002c904d0b0815010410a41001d0081c944942417500d801c008000c3c100301900d49807500301c4286881075407104154014400b4080640e80580710046c0542c030075540d07902d494004040c18411444020b8040c035268120140188140b14000d9000841000c5601458a001c500d0302104650b036403d101e041200850b44501d01c0000c01507442c07199600003001c2c2010708019150a0001c5c2d4100c044cd84002c0b000c4c0702c08589a407a90052000e07400c095601e800d234160f041c0f00321b030150b03420000c3c140c0c940c007000814a651101001074001c030303d511800040c40d4200c0045050b80c1007260302810b0104492001c000b00e82015004590110807880b00500340220a4001000c00601780e540000e000c954031014040b124283d651960041c0314000c0e0050003501d024041c41d101d009121a030b40c850f00341e108540003842020300c07000c0750b400da1087c284c0390740b90307186e1030009000e403c1400300351941144142e03c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 601699955 1250 601698705 601698709
    0x307050a1e1403030a1202160609021f1b0515040302060417090d2a0e011404021c05060105070609030215071107140a180504060b010207060915140c010e0c 68
    0x5285150b0058095442c058654030144d5211044403110a141a42040030200c00c0c8012085043d2041c07081c00c0110707969005d40108210003210107041341214440c00510b4006c660410307420000b1100200001c042110780381001820180100c00c0004035041c1c0000700410143d001c141c243c880d030b10035407001d0780c040100800c007800c90103000150f542200c00c406a03c408291141201e1018010300080c010140c1e6201115500010082e0300c014a000c000c100140880e0394000c1380010100310030790b411410600b0648138040902c0d01c0401d00701d45544d4030800b082c0581d200f041280c20035900001d09120b4000c0900c0c000b552080506106044504140042407200744920301d0030100c40340107001080030908040c41c01e034074111070480c4254000c100c0e8400007816503a0040000c2e41070040c00000901d0b01c2e1504002040d80c00818003541103400000c0300b44a0150007205940503609401102400035419101c03e451100e00300b05003282102000c40d014035100415080341804041c00c6003a5101c05c4a0941 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 601701205 1250 601699955 601699979
    0x303030903070317070e09340f0536060a05180d211209030804020f01050c060f041e050f150c0d02031308041805330307050a1e 56
    0x10785c240003c04088155009240940303420303800070a4108522002440d1850300d10040800300e050720a00304003054a41002600300d0040802c1950a0500034030b82100400c1012000307000d0740c48640c81481050161541c1c241141810310780c3c02020b8120b41d0349140041c0c01800310307040036403003220911007078807184141c0c20520508403c803544050a200e41101c00349040c03602c99440400401046074a00d00d048061a0901a050b011406915920004c1c10140140210800c400120a05111040000c82d8180301e00007011076100d949089102040d1300e69260a610340301480c2003440c1c800380c030244c1400500030040741d400040c0030040120350918400c030030401c022000859540c082c0903028061102044a1b903002994004403030465000001c005988041030764020350010350211121041100780781c4482d214240e00a02d440054958014460240459032610480c03460b00c901880141408161400c000b8100542801880d00140a46800d4030700c5440c1d40b50b200c01c0090002d01c48000481500e144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 601702455 1250 601701205 601701211
    0x3081305011b1e170c070e0601020d210504080c0c0d080a0f02070306090501050f07020703020904020f130f0e1b0306150a0305010204090204050a0b0a080a1a0303030903070317 77
    0x1200c552002c5981c2c40301c0c000d01005000c0c4011101c40c0500310b0002500361546031811150700150b254407000c044003000d2404076590404a038070300380017051140310b85e000507152148034034514060031888030349110080400701200e11076810300c0c1400300344400c01650310060000300c03c0c98411110540001010480d1507080a500503150607000c20062005510403848184003900314011603418554a6840d02c046030040801998103940d1482803041c10b01550580c16001901c82c801000f2842c107680000d40c1520001d40300a1107640ea40b0210030302d035203610f0710841403d00b0110302041803507a0003803440064625581c0d491198001c2006184030090034101074065284058002d150b40c0da2404050180d070040c0840791544141000c1000000450074002072028100f0300c000503032502d14040c20f100121000b50420485188148003551000b9070003501c0ca030f4080204c03600442c1c0010b560703408030301c46000c03011311a4160000200700000424000010130303c651107980c0d2410000a49405160107540075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 601703705 1250 601702455 601702487
    0x609050f0f0a0b130305100506090601050a020706032a080103060c1d040504020f0a03030207080c0d1e020402040b0f18090708010303080606161101031103070e010507050c0405010308130501 83
    0x1d00c0c000d01010610f0409015260440b48107120f11580300d40b5002d107009504041c8040158543c801c00c0070600701000100e82188081c00e10300c0c1412a0711002030b480e07001a00492003010398401e1603058080300580101e03120136071a240350413407144602004211440034041500e40500b40032840d0481e40c400d41402201d100b0615451102104080410002d00390141059038026003980082007a940e55144079401503110b50028860741e4506009103090512521401c0d104040b40c4040c0c20225016035038061404c00c075082c0203000c1c3c40180c80000e0082c0030f2500103803d03031384000c1160394000083c14000c004403a071081840c200e031404031040241e110800c69910b00090000d9004100103030141c0744d2241c00070401403180341040f042d40c04441807040c08034000d071800091005000780700d507010320a40c60885d0800090514601d04204060000d1031031500403170400c4400143c1c0024010144502158400000d00038400395940c2d041c0342c0c4c41c642002d41524518900d1480c005288c0d070213099070380514048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 601704955 1250 601703705 601703719
    0xa09030b132f12160807060306060806060909130b282721170601020c0a1a0c01020309011d07050d0807080903011d010c0e030709090804080303010609050f0f 69
    0x1002449940740d41036443d4480340c0b00b032500c120f4840104411480290041c00014014185800300040603583ca90340304100b4082003070180100c0f62101c40880344003000c2238580d0003907620f40e0129031032655180d89000e8400d2140d10113004002c0d00303411006280c60071039903041c01a00180b00a180c1281d81c43c03214220707480803101d81001050f1000505502d5540a501d1010b040021805404203000c0420340d0400090054a4504c03441648400c0705d940000e000e2000784a98103040000c1940203038035004482030b00c00e54a031444050680202200d03280005c01c0001c2d5220b041400015010f8094006c1d00c01340d011301101c015a544100054800c22110010001210248140c94400c100e910103541a90041c501304009445510240136281a0b0585c0041c40b03039502095400c024216500c6089440800c0b8040c1c030028482e603800135400c0161400003400003084030651038580c10621695002d07103e00e01011000207a41508250202c084600944410000d201184e040007501c5038900750495124034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 601706205 1250 601704955 601705043
    0x230405070503010e120403170d0212060103051e0705090d050a0f0c050d0b06010c0311060f0f01090c020a110d0b070e09010b1603120b03010603060f0605030f0604080a09030b13 77
    0x3100c444e03039008d1070401c070b205c030701d0f14503401000c905030b0b84210204d00440000c90b051000659052080b030354441746049050b89000e102030f4501a071400c015000c4006c010380450b641f0f019644101042c10300952100403600c004076203241914004402d00405d0f11812100d00000540f0f0030306420800859030700160030310565503a01d0044d140540540c0d030075801c002d10551004080c0004101c0b881c0a81c2403001c115406146c030030014011510140c03c2500c90504004980b03200365000102c0c61090781c1c4c03100030404c501000c8408900660356610004d000341c424981802070b12030300040c1c2e840c0c0542080d10f08501c0390b030704d42a0413480341c89a080641c10307402c40c5001880202e0b21448044903541e20303020011600804050020b8207442458005840e107a40c2e61420301d4403003000348940b00051000382c026100c2c490200d54041d45900b00240050b01c0320074000713010780d441440341903100301843d408843c100480c20498400c01002203000c0045402d20304c506203000b020903802d8540058103007110140c021600c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 601707455 1250 601706205 601706213
    0x1e02120708100b04170c03030901051c09060908040602190c05090406110301150e3c03010c0c030210050402091f0b0a050a230904230405070503010e120403 68
    0x540e00404403034035032081c0d86001c9200c0f200c0381e0081005080c034600103000507111803031041c10401e1446116119500c1084044500d1b44c114096894070220801a044a1041e500c01100603085200009014503d400e9041c000c1004041c040d0003030310f031b159003103894003d807441d0640c19100503c140900b420103101400c01241c901150504d5015100724008a01e513280d90704a0300654000380c1203401e504841c3c081e00c07015241d01c051104451803003100c04484614490300c0350307102407401d1900103200300c200c0d004043c000c0c401607070810034400340500200294101e006001b4044608000c3c220014011800340030b13152000c1e40540c601564000f001140d080e21000980030700c81100408038a00301218940018088000202420403402c0c99190705039940c840c80340041001c42411500d00400084100f04215410400290350040c4001e444c000b07100d0405907034055085101f4040b04826005e240208010413001046c071104651003500213106000c00d4020440e12030012103000c1c00d182005000402c045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 601708705 1250 601707455 601707467
    0xb0303310b1c0209210d080c030c070512040e0402090609071d010309020a030c1509060503270d0309120207060210050601110d02070303180503100c03110d1e021207 72
    0x80905400010b142100356004a1070504400317a0031035103480c070b01110718000e0170280000d0072140404d00c0d01448038a00040b00303001a0201500302180480045003e03020000204001c110702c82e4076000e00c0e511555a006c24000c01c40d41280c04078051800340c0d01184040c145950810300480c4a41c41300402d001da2450919800d10b081e00d11721741010340340c041e40c50240c0c07251b1100c0f101135030080c00800c0c0d1640c00c00030803028a980145069040004800c030030440130764800b0a40743c10400c041400105100540a41c1c00025900c852514250142e101c000c0c80482c3c240c1d014400043c0b289a10744c032004406101a41c0701c5005100780c8000da0000c00c40e4110500480c1c0c015980000d050425071640d00700e01c07080c00d144c00070540700903002da1700150b4180181500841d180410001c000188801c1ca824000440d440315000c03c1550305940d11851040700c21030203174000b01e40ea030300c081c1202900d944145120030702506501911040355003a40c040c41f100c3e00990300071201280030b1404000000c2c2c075456812251 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 601709955 1250 601708705 601708747
    0x204080d030c120c0503160503010303080c09060409060801020a1d0d020121050408121302132c01060302090a0614060c0c03030f0322020a0b0c010b0303310b 69
    0x70080c85856003106030b0702e28452845080c03901d41c0c85e2512450310f04518404101c1c10a24642484030900040000aa108881a901070070400c801900c4591050104256001e80d40216200904001010584107415400740165203a25a907400840c007401c3e0801c1d0f15000804400768100510030203800165018010130509040c02e00c42e281a403000d20706c612400c44400f5074040380c0314580014034000c00807045002c00c1e00030940c140d80d595003949540c000354dd02900b910002c29200e44070784503107035603400310710030f81c46409014412161807006403103146009180600040f0701c00d20304d0601084040c0c1487c0320b2402603800000b1100344864080c0104840d0350000100b00b00e00d441002203503400750320113002070301c100705151030102c1e16400c0031017411220900341d0440681103484d0018080159460307559070340071140c0e01038019555006030440c103405400c00000a6800d80300003c0d8040400404040d582000e8801100c1445004002680088052440d2040414a5500740241d04440b1400d003c4122 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 601711205 1250 601709955 601709957
    0x270201020a06020a0917010e0601060f0e0a0e0613021e07021c0602030a0e190204021812030c0118050a03030f141f0815010e0403020f1002031006030204080d030c 71
    0x10481141d079468006076804101100c0008150200c104401000c6480d140c2c1c00300c515034024030030303881105143d45c1d4410381440b80d2000c02c0254003c0075682070140360084e010030030280c1820402a16500364900d404403c1d80d005001e04420602c4c1100e0000d00d2007662f200f00070700090b10318005207120201c2c1e169044440c007030380c0c8512201078910120b030503000d5840401d48200b03070250b100d2a0000b0541c0c201c2d0320b03200c43c000f00e5820210ba0110310000800318007240c0c82d0704880058491600103021611000c4c034070811074000342545002c0562060010203440009400c0000740500100058800f0034148881030080455101031107000019000750040220980b80050005a105100411500c12b880c16a41d084400071580b0b218800b8114440b20540030341007c40c0101005000c44402201e02c41c41441100c85800649000c582014401c7c0310090007460601c0403500303d002049243c400075401a00c4403030f0500c100000008155019000740c404955040000d4000c107000140140d001d844130300f9800f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 601712455 1250 601711205 601711213
    0xf070e0c0304031e11070e09030717090a060c050d020a0201080703050703110304030c060b090114060304060212040c1509060f0e040b030d120f0905061b0f0720010327020102 76
    0xb0005460070214513608010503540c00308541885045ca40c2030425075004050006070441c00c001401c44000200c58006601142012b8440702c0daa140300c445029070116550303c000407410001d2803da10240402016000c0c806072510a0080c0d0703401c0c2d94401c05480003d01160401000500140c00390b170007240e00009a0402084015a81344481407a40c8102c4080700412210f156010511007640715031400b84200352035150f01d0b0350400e90042e001c030041984c610b10a000020014040141680540b0410b082015510f45541000c1c0342c070b040c1c1011140100c3c0b600f29210b80607040135902c580394160445510f900c6480d043c0491207000c4440c0d91544a1064100740c40d44c200406c180c40802008242d49925500c0d80c420001100a88003a500000c4802c0741d1941028401c102007200442c0c0c141d0802e409101c0303181d180032014202c1e074003405035560300000c403400400d41806000d1601021002e910241d888042d1105461005504551642d10084d1445036a038010012030102da1800401c0c40340140122 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 601713705 1250 601712455 601712477
    0x1302011206091d0618061f0807062001060b07060e010b09040b0106091a040b031b0c0604110d1110020a170d0605010f1d01090e180f070e0c030403 64
    0xc40c10f5038500c4000d512480c02c281070702143d03038400b840b50715008555a41d45090885011903407550b00c4101070320a01c2030981d010281e4000c0300501800c000284440350913a1051507880300d01400074141c200142e40310b010503000c280882c0c2018401e40040d00e403ca200203080c420b1945441d4010b080400c02d080d0590360320000030a040d91040c000900c580d1054280301c19a40c140070b401050a142d5920590550051103080a1500c409105450942d000c59000d01d49a03a180340200c1610303a520046071003001800100750b9404d800105c1e60714811409500c00700b0282ca031590a02c00c0c02004644050000161403030480d51521b000c1100c414810440d20480d2111013040d00d58015040d8104000071003040c1c001030a480b02d950b076004440041400f42480c0b02c00256240000c0c200040800c500c0707610308084003492038603a01482c807080140c101001060380342c0ca003540c850008262a280c04501610a0380c04001e03140c140021010143c9007180000800d43c2c0b143c0103410500c0d00064022020b2103079020b59 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 601714955 1250 601713705 601713719
    0x20723060705010f05040606330e0603090705030705090708041211030a0207051002030306011d1f0503040b010e0903040e062806080c040311100c05010c180e1302011206 74
    0x41142d88a059500040c4c14105481c1071f404a61aa40c44280c000412801c803501ca60080d40f051100f4201c070074070200f40d02c1e89190301158640a1020300550102020003406031800300040c40d0400e4038403c4e8112031080780c480c0c0800545000c1258a000018620800500000c9401034009518030090400f001c030220748031099411508104941c10050344100000c200d0781ca0460801560801c0d640051461400c285000902102c1d507000d05100c41c1d855051401500e07151202c0c8034200e080380b40e91504600600ba440104190b0050703d05450195200e0f0010070801500413103e406a8010300c000d43c58940342c80c1c03880682e007030001e100320341c014642d40b1002c180144000c441c41130358040d036111617a1281894005006d06001501002c0c039200e0520003400000c4019000c1e442c40c045c202c4107805d200c201c3d00421542c050340c20030002c2035542404664406550000d1070310845501c0b4244190748551550340000b100281100c00000224030100030324055400380d222050b9100507044003140307240d1a221 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 601716205 1250 601714955 601714961
    0x1a0912010902030628090206030c0a0e03070306020c0d02070602071802160c060f05030907051c02120606010e01110d030507090308040e0717270f07080d030c02072306070501 76
    0x40821151501d8180c0c0410703017503280b900c1042c078846a40d00700504100c0390049a01030000800544410707000003051031585008044005403c10020200c03079225890b86418400394102404500003485800c40603600c090010810b0800e5400560051042d54030f0304000066480c0287d00004240f6420050344d99240514042c011000e03019040e44034400c0c2c5441002420400042914030401000380280000301402191120884400300c51402c2d481e01c28010041701c1c140200710080d0301004205000e48108030228000b88616401d890301400348008000654005c80c0750020090150050001c01c45c20034001d43c0201d4009199203003e403212900c035a1699103540c4a90400000690031000b080555a440b8403814810050036410307081c01d0800c2c84588020055800081b80807018650a08079248010400581642c14540c22100c10940d140c000e0758a4044017001e04000908101320510341b240000303081030469022992403414590f003002540d882c20302035218164490300c200402404a43c0c240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 601717455 1250 601716205 601716211
    0xe0909100f0b062a0d0504120201031b0305072a060507050403020d0b01031b031223040e010302030c0103090b071b08030a051f080a03050c0106090c11071a09120109020306 75
    0x803c6006002c804140c00000403031326640080d43d074003032007203c640c0e55404002d490446000c450400048100d80c40141c4c0544641101c88507518130400c03200000c42e038142c10080c05070045440c2e44c01c020b249000c1c1c4950303580e180c0e10b13000c4144941d80c03a203000088036944082c0d40140d42c0d18100b030510761a40d000920b000d00e8090140c0e103c0402c0301c014030a0020305240001d204c891072042040300c41c503641c0c1d080c01c1c81c8081e5451101b4801c4041c042d04441c01e10300300d0f12820704040f100c503550312526101000380c280000c4c00260301a200d07009664100d94001d209a0701740c50b4001c40c42c064907903a62070f0201c07409011581d816401c610700755064800144c4240103980101c20044000c140e62038501c0f80100d440074031b00044200c1d090300481c1040824400300d003400c58282c0600c1c0890b50343c02049415405000d15510100e0340616020280d0200b9900c0381d40c0318180d0003490184ca06150395800c1d0f40d14191074103400b418031014100418412480d0078542100400100030010819070a00e800090a003a012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 601718705 1250 601717455 601717477
    0x3c0106020321070c02120106170312091b090c090405070f030507140307030b010302070c0311010f02010c0206012705010905150d0804090522060c0e0909100f0b06 71
    0x480d032240c8040340380d2921544400350000000451802c43c5004200d1011864040d00940c2e039014150891402904a0400740c00090842d0081c03200c6034004070745d2980624401c402040360140410040706020400c005040006441c6ca40a0480c01f0200291650068201fa0f00104104080d01d125100c0d400748bc4d202d050903803600d0808403003402001d01a9034001b0040c100b040b050500030102d40000c0d00075282c1200251900007030405021005034000c5c443c030b410141482124000010400c60400400408d109080c0d132076801810f01c0d0b20050b03090311805100c510258000f40014000e80c0d1900a43c20950381008030070552103011b051807641225000e800c2910a10340318803c1020300c005800b1a200642c100390f58030f44e6a2061622065814000d50098049140d100d2011a6a00740d50324040404181c402e00a0300318840d142ca09030009060348440d5502191000101005a00d0011480c500c50720700000507091000d500720392500204401910152281c5d07450b510032005482d1140030b0320400d072003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 601719955 1250 601718705 601718707
    0x809040b0339061c020d0e01020403050102030601090e0c030112060f020a030c0e06040e01050d0201090b040f0302130207020603180106080703080405030601080712080904021e070215033c01060203 86
    0x540014060049080c0414500483c01003110050700780780d0702c0c0440c24055461400680f18480d8101c00710241c110401c584809600118000c010301406600035402480c00f40c9429030345030356640320401070f21011910f0121071081800100486500813042038415440703030320002042000001c00d1000c0340c0012601c240041e40e903590460115801c000c80e00c01d461000c480303990605292218602d07100c101402114010f0120117182c10843e4000c003082c80181c80c80c2c071007a5455070b403103031300144850300c4900c03050b445490320688142c04000340b8400c4440b450f802421f0b10b840d656800070b50000303a1445c84507840c410b46da6401c2c0003c0540043c0182c2028601c16118103550394070700000c00d89880010b8015114a4014050070000d07640c0000308200e01580c0581c41e1a156200a80041d0083c01481c40769200a00544446030781841c0309001020740510844c0c540c03e120128069885940c042142e90702c3d1141101c5100f001c000c205020701d13400c00f6103013440982e403201e44225001c101010a901080240e80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 601721205 1250 601719955 601720033
    0x18090201120903022416021f110c060c0c1621110a060e01020105091902010c03021006090501210519211e030b0d080f0d1b1b0809040b03 60
    0xb8411b10030354101c0c01c0520050004020340d80309110602c0c004070480d80d0301c907961000003100510325019903214050140035581e15141c0399000c0205a80292400d03d403034014182148030b1a114000090160745038031038061000c100c81545040c02c40e4540f1800d0320503810b9198441b2145ea100100c10020b40320666400c6035200955001a0030340308080d02101c0541c11200c5480d841410302281903240c242c0918081c2e402e4640e50a00380d0601d484114952103243c241000032903c039409400240c101d07010008913803024251030f41d440c0704032540d13a040141507401c924900c42000310079101c0059164040d50347e0000218540b2038115003505c0540c1050003141070b83d01e4411850b040c0300003031692200356007400e0090700308600c00102119003400004000850105003996002c0c0d40000707507401c0144000c4104050142d00000100c0040f4403a00710f00002d1a180c043c40d6411400d658001c80b0303940c0306031500c1c1440c0c0b6460810004c3c1c440d41056940510406a00301e0801100382140700c0414a03241e210b8441e50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 601722455 1250 601721205 601721221
    0xd0e122517100207080705070608071403040515090325060b0a0b030a0504080c061f0602030405060418090209070305090607050f0703110c19180902011209030224 71
    0x280d5141d20219981c001e900078251803070008a0540b12040003510016a101c0c12071404490601600d040900f86105600001c182c80d50011540760003084191103c0e030b26100301040e403540701c1c80201d034020711a8200b03000110000c1d03260001d2a42000800059a003400d10005854922545110b0340b11140c16400e0100002e020441c03180c1d2221070350542d403007138030541410702c0141284006030034000090b5582000805010f0400160303220990f04500307448640c14040780d403101410820007600e00c450b41040c400070b0160700000c1150b0458001030001810304c0c3c50480c0c55242d101c15541d420b1a034a803581c00c0d510043c0e84410101d4405c0c507036a240001d090400d440b1203450880000c02c0c4c1c0b0103102c410015000e010b80c1600554400a80c14949800300103130741c9041d50308002080b00910342106c80611030281e015610023498054940c4040c1c07100007002440960f10940f00d11100203404100d581a00c520040e5442d00003142e4a4020f0044032417803e03640303d414040f0031003104109103845511003881102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 601723705 1250 601722455 601722523
    0x19050c030708270d0b04060605130e0114070c030503100e0f010f060305041709030703080a0e0906040b0a0b07030e0904060902031005060604090207031e170f01080d0e12 74
    0x404045499603441d86091004201545403908000d40741c0c07030380040006c0c10007250b60026405000080e01814840b0240d00b110006404d508a80c0c1c0b85a5017011a1942c4041141c2c0100b807041240d6964544000100d44041d6a582c0c000341c410265115480310214281c503100401c140110104442c15a0662410101251200194104104150401040c400424031410394207a0002c4180c1c1d0b400c2d503a0509c040000e18080c8076034070003064510301181080b01e154000d100e25078100c4041d00c000701650380e02d10070007048070ac419440e10360019404c80d09000e0407900c1c4018003440d52003410300c400354080203c0002d440c100708650455110762594000310842c20144940c91801e403154800307000b5410848001403c0c1d000c2c8d030003512030740c0e98013103415024584074000d01d03880c071103100042c4680303100c3c090002090b03500b500c420320003e001900b0203d078205524854071030488501101034032071000c0450080304d004040c00442c50340070380c50001d2a164601c060042c1e03110200b0300d860b004945003812101e074000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 601724955 1250 601723705 601723747
    0x40b070815040b040b030d050a170f1803070b10180c09050f0103020d0212060414010b0702010e120f01201602090619120b06100519050c030708 63
    0x3040003200620441d400200080c80e140041101c000c900ba80032100894010300f010b181e0907074188904250351010700d800078010241240e95a451030f0f4007040c0a00f0b6202d02084c182e0312000c2008103400003400c48069094030010401e020410741746441d0541d100c0200c3c14200703607804111001c5a007000c21054200c5c0741042d00014004106102e004501440509070148510540d07000d031154070751200c910780c4280c0c12035002d41d045440c02c544440c003030981c41030b02c0a070403166035010303c0c07801d010381e1a00035030404014100c07490781000c5403915100d6401129070003a2008250b41101d00d4101d011824403062001f0700c81c0090300400000c20300300d50410043d10b8400c00403400b8500c0c0e0100041c0800380d10031200c2101040e01a1031610143d214500420802c55000307201407181002c5902c0440c13a00c1c400c3d45003c0e1158000c480c588200d449046c2002202403030740000002044081003054407090101319030f06d100c6425414010f0800c05e480011900790f03400868111020480000c0300071801c03c0c03195007605 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 601726205 1250 601724955 601724957
    0x170723070617040b0601080901111c060504020405060f091801180c0e0607020103110c0607110d03110414040603060e0c03060903030c03073b09060f03060105010c031412040b07 77
    0xb04508044c0c4401c40c0803d0041c050038100146d0038005480501c007504184031110f0280030039a903809501071703034800007940ac0056404150a1140004d05071406000b40c1d03083e184000c021170300d0030041c3d0f6a00c516541c403071070f0b1054100140100e813401420b000344006001b40125140c440d001c05001c8044030031910030181c07100a21010400780d42d0340340c44040684d10780d07950a0800103103824001c095010513001e201e014008601c01c2e00300b002101c65001d842c40b03401c05541c8040b6910505034200c00d40a848410b842d005500320240000c00103510800100700c2d1108001d000041d41933181c2c4c4441c001c0d40c5004903090f07903681c03180703000c6110b90a0070001103500c001008007850450500c1c0540c12150300c001f410150400c5aa0b410200742d01035501c071a21101e40c1841e6986007280041848910340142e21404988500340e100002031480c107200d01012011040140602626800c010040d100c03040c4090703003542001190360075a80d80c10f201b0f4006000d956800c1402030382e103160501d0110501c140c000e000340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 601727455 1250 601726205 601726247
    0xa0f0510080705060c010e0a030f1206060503040213020d090c050316030b062b0b0709170d0516021c020405160219020f0603040b0a060506071707230706 67
    0x1500101061007416a502104c10035510048108280c0c050000000c01c00f000e802072000389400c0641140785031024502586400703601d00c1d40200c3e40e500b11aa5441100d020600810015005240100343c140b40300b10060801810040c05d64080c40445036810400c07209003404030014842480c08020340302801031041e0203402c0c1c050441e90358241043c0007820190180c43c40c12015901c82c03842c00300c0c4a856558901c81c0b41051103060510800d54603040d1004400300b050680c004c030307565044060f0401c1111000700100204400020215007d078840c1d500144098000c1e003407900140e83d005000c4540c4d1602d5001c0ba0981c0d20140100400c880e03000c1d1201200c1d8803440f09010006801040800403092480f00e15221404c20340080b4140b503084480e17669000800000708820418220000e42c0a13078028070003006056101c5062120500c10803001500c20b189000740d01500c0980341e801081010b00c00d000554403221400704010207031a0703642e0700c0b1985400885090010a51043e1a8248242c80c00c42d03070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 601728705 1250 601727455 601727459
    0x32406030b120c09041a040609110a060c0f060f020d0902030706020303190203130f03030c030506030321060a12050d0e090c18010c02030607020d0e0a0b0f03091002030a0f0510 77
    0x1e250b850743c2d262a902d004000e10000070b01403103448000e002c00010b040e00d40c41c00300e190a107407000c0206540b034003c96020a80483c14000e509040c0524001c0d00d1860b210384044c182c1503110180c0080d27032200103c8682d515407400038000b24080c00070b8a003141500001044007000b40c4101350800c03e4a400c000115413080c410004008003424003181c0da0106401c005940380c8903000c500f03042c2210040b000d04101c0400d0650b81c1010b03850340c02110038040c10359081250780c80365000c154880c13044a903d110101c0a4994106042e07583c09c0115402400041002d1506036a0b1107007811402c101100689154000e60003a04109803c400648042c0070125001ca600d0f242202c402c48081c00340c0100e00700907120601c00500140d0107034800010040d00101241e1142c03602c600c000703584207800310560700040e034030340180c0d521400c0074040b4000346c44251b007246040441e031001010365500014800e403240e210300c240d5030b0b0040400d48021800742c082008082044a01460010103441c030103031803010300c0b0400c504e003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 601729955 1250 601728705 601728739
    0x7080a14030f0301051e030d0c02180103021e1212032707120f0b180706030203160309030c0602121014030d0f14031503060c03090706080403032406030b 67
    0x1c490540b1000c86072002001c8140740c14001c000f40c001b460030f0301442442160041c10b07810000c4040b80c01c1c0300302e5400c0352030002500011800a4280300c025046030b8000c0e803030b606003038001048000000300074000b00090f505150000d880d10040003140c0802403800010710a05100707000c101e1266007040c08040c400050480c001a0395101944038400e41c107101c000b400d80c10840b10700c04d160b41054200c2e00f2482641130201013071036a00c00182230303000303c0e209190f030005d0050b00a001f5a032268080d00c541c00251200d5a10270350280415041c22004c006085030702c040001c00e10310140200007400c000d070005c14600344003418115500c641010303010806001c001d0441e41c3e07002901134401c04c81031901c186800c00c084010307a2680c0c8100008040314a000c82003045001c0c2244088901035802c80403110a900d44400041e0300340701c159106070741504030460501805000300c801e690854400d140004103503c500d90762581c0650382007062440c0b540c1c1c400080014607898010504410400c480483c0c00c4a41422 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 601731205 1250 601729955 601729957
    0x80108030405040f020d0c020708100b090a02030601091805011d0405100b120109050a020301050c2505120a030c080c0a09060c110607080d050109020a0c150e07080a14030f 75
    0x4222440f4648485114100010365010b80d2241025800b090203da4240ea4001e9107640e1140a41000c07031103140ca0543d2000b0b840d008006500c040540000d0740c50302e031110144080c5d40010001814048603a6000071003114078400c24000d4240d01500266075410502c1400c2c20114000317104c1c5510320040180400f0031004030345004141c01d60480000c8824111000c01c841180501520b40a5446d010749001400004644010050b200b14020050f66558850011150046644819034414070030f401c0d01980b03013a1b20380041d0301ca010380b0844e0b00c0441d035004603103030540c0203110f0400001c2e210035403098a48c0e0040159174000e41010281401e00304900c00c0242218014410641080107843c030180910508075907107403610303070b000d0002e5540e0b52841c180902a07504c4481d03205001032a10b0300000da51030f128401c0e250380c0041941c4441c4003204540f120000c825141c201020701c65030390312401103a003030100442001019410040c15002c903031402e052403548012078000d00181c00421081d50000340b010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 601732455 1250 601731205 601731209
    0x306050c0301151101090506010f08010b030303150907050706060906060f0806060a0c02130203090f060907181a04050f01060e0405062803080c010603020a21170d05040b09010c0801080304 82
    0x2207030143c4c5105800102502415001c840504280a250000309448840c0c500c00410340307805c240240040e00ca0802455a688400c403005244070300064860021450a220225001065890b0003420a0201d880304421940280c1c4004400f07640c9050400281d0380214000d410861035080c115443d01d080d0b00450854403035110584100310040c0d4000c0304658460342240320700c060b90f060440d00d034a0802c08203542d41e00e00384066101c5101c1d842c00110303910b4001880e1000d46d1040f04151110b0040052000041d011403188031181802c1041c601d070854841d481241d20403080343c000304541b94507001c4007030911b815410481c1d0149040c00104201e50300d80e400326254501148a01d04c6d4580d0149013185172001d66500010030300d100025803047c0c1d10b40150080b074140ca008030707561190707103a485841c2d2914112002a0985c51828004942c003c039a0340e8141443c15400f07400307410300e00011801c03985e08540045504441004941050040c000c0003403143c4c4120522900b40030030310794188a20345a89000324 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 601733705 1250 601732455 601732457
    0x11040b130b060f13030c0e0403021005101e03110d0209061c0f050d0801050a0e19110d02040f050d0f17190c02040507030b1e24040306050c030115 64
    0x72080080300341c41d81000c8540e8680d280c1400b9460f4007000815406005040c801610302d0b2600103000301d01e038030798656510300455068005040c60350710381c0c0c0400054040100140039824032403500113003490082150719903281019607a041074506502e8480520f90110461134065041840811b006841d480d1074240c00240841703111001c0224440801d90790000301600400d0401811100007c02000081d00b062000c2d03582c59000c2c050f0789400034010048890b108040c42e03201000c01040804080941304c048045903868089a1510109100722035030b486620741c1400a9800101004a0b18020148030081e01b4201c611250042e003d0301ca001003c03118200203004034403036840c402c048404800460340c5044d682101d200035008d404001030b200707040c442410f0380603c0c140030010f412548030b07201c2c40c00100c1000f400740d10301c00d101001c598142c8410f41920394111401d03204080780700c49035164042891100025143e0340e02c1c1149021001da0f00090305041c03450605000501c18940b41d102d020201c2c80721 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 601734955 1250 601733705 601733711
    0x30901050c040f5006090603010303180306061818030509010f172523130e15130c051c14010e090d090b3c0711040b13 52
    0xc2c0c4101402c8400c0003920310200361120001d5100f40300c080e9840255001041d182d21384a22020f0041c24400c070714036030398042c104000500000740685901c2d020803111920b00c0c4070b0b1a4496803643c0803508690011300302c207881c1061b220b07042c500900400c00084090500406080d4590384c0140150280c11880b505000b500781c00030340d5030b600c03c40301804d50f07003480c549054090800d40500134803401d01c41c068000d800212a8a007110b2401080b82ea0b03201c990380400c140c40711500d070074070b140140c004d0b04460000040c6503600080400f20107002a00400e0300404808480d10880104905c0103581c00d8070a103d00d080c000d450280d103402c101524140160003010074088901114040003d06000c4c0111029901d20030010440e01030246021b0311074510441201c1200c0c81d0007d0648280c503180c410340084000800542076407480000b00586692207034404400750200030f42d021800540010000040400c010031034805200b031340c0d00c3c0208044000d0310100061140132020502501d01d4400d040310642c4c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 601736205 1250 601734955 601734989
    0x32016090216061a0108070e09070503061203041d01081203070807110303040309061101061206020703020f1c090e0f06040b030f15010512063d060302030901050c040f 73
    0x40b400c1d03040c00c1c0c00c0b0340c44001080261480e411810303401541010590018050000081401d0301501e80110009402443d00d04103a5540000b2a4641e200038000e0341c02120840c002c101c50f05041020b00040d140c0301001740c104450700200c900700104e050780031240079031140341420700c5c1c10b450034126504a183d1b4500b100080c2e407401c1003503504800c040c441c00d901d13100020070042499401540743c010b41d0020b0761041074200700d440b01b56007078407154022095a1000b0044000001d58140e0080240030b11030700542d1000b03040c210010b410903e2448a00c003100aa0111684066074044848005002032066001603814a04002a02c0c032400a09072805107a440700103100940d0104000d240d028030034011522801503582e4a8441024284281409510041440413600a012800340e00ca2040110032041104908807082401c0c1d4800400410210906030180b844411424980000c5c00091b03e0142e5a800c28010190854100038400031152806100900030440d40c1e04450045541804812110103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 601737455 1250 601736205 601736227
    0x1150e0618011401030c1d0d020f0315070e030a030e06030a09051b1207030f0308101a19080c0d020d02091c0c09060605031303030b030a0320160902 65
    0xa034141c1c450001210294000100e92081e125034108a100a03a010712240b00c031b6603415220981c40020144034000a40d1180300135060000070352940b5400281000808904c03200882e080403070301007002c2820782c915010003004c0ae0704501d0481d986042a0f008186010003920020000f440750000d540c820600000440c0e90000c00d40c101c04049a000020368503400450306415200101002ca002d009110302c000c0d280e082400800c000044a40180e01407010003100e1742c040750300004c01404a40070f0801c2240200300c040c0b5044403801d503060300c04401ca50f940d0115200c035504021007003040041224030300800a460401300d0540c2d4130601c018801503141d40710029140082c1c02908030140d04088002c03810b2445035241c0c0d8200c03d0450091350b08660f00c42d103a00c86034054880f07600680b40071a0041010941864107141a990780318044e11380040c1904c64000040d050150a020a4000920082020b030b45000c5085140c40440030700001004001c2403030341c0c16600362a4900c41c08200560104001000b2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 601738705 1250 601737455 601737469
    0x190f080306060d150503070909080904020c33060906130216020405040503070201030510140112060308070b090c0f2119030203070b070f0c060f0b04060f05030f01150e06 74
    0x4810311580078041d1907a858181346030003d482c4200c0d4440e2080440001c0d04038414890504050742190307a0a11740001b41081c0b101952110849020f50f100e00e07c0c401b100081c0310301c14030740e4102c51030308a11034000c10f400c1d0125030290040c001c07d110ba81440d00380303d02c5a8030326100c1e44408202040168592a030340c01d5808991001c1d5101940142c00c04040204106000c401080000e1013600c08002c1078550f110a00041402d0b8000c038660250403048000d5550b0045400d41216020310101041e910b4982e641c0450340e4000010031500d4040c07050511007092010310580207404401e0303035015000d42640c40098284032140d002c00c980f91800c0f4110410351031041c49410846802004000303001d64103458002e641c0d0344110070960f03001c0b00c0701012030815440303032001281c032204554403d6001001034541d40300500194128680d151ba0302c8030584150b17190785c00381c0c800900b94442d030600c52a20304410300d40ae20301081d03800c04450349461040d0f940c02c0c90224140301501c041c1e8045041d60394400d004501d03c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 601739955 1250 601738705 601738717
    0x303090904150e2d0a0f020301020403140102180301110f0702040b060a020d030c0c0f021216060c020a05040903170a020f070b010510020c090c160807080c190f08030606 74
    0x11030503d24003200c20301001501d586141c4040c111400c0e200348043c07015041c60301c060050303800c1d80c0204136072401251010700001a224002400180fa00e5a00c0d0b403131805e00c0c00721741008815650042218008001807107542d01c00300c2e1094000303000e0a07600b0114084d540c882c6d01c0c80c00c0c2c4c940e000880d01c03505640380c0d0350105c80062030203406103580e002030f240007130b40d14840c003181c410009091242c0011001e10800d035412401d64050610030412100346c1c03c002032681e0705000c00c5010b102c2c400b4100c1600d145c038000e22009195a48409007283d0349030040c0300300d5841d2604018044c4e070810aa8200283d4081300c0703140302c1c0d504a1008400c03500c4000c0b4100191040e40242c40c00302001140d103d00380003017074507580c0c101c0d0740c12201c0201c2d42d030703d400c000c1e130b192040070300040e43c480e9403400000c40b0050603600514600c5017a103112400d6005966843d0301c15003050700700380c610840100e0f510b001c0d840e00700107148890000d0b14034040d546400da944c55104000b801c8000346501004804516103444940035261 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 601741205 1250 601739955 601739993
    0x10602071205011e1d070f030807030c0209010e0603101404080a05070501060608060a081b010f0e121e030414010c0f080d0b1309020109052e02011a040b0303090904 72
    0x2240044c42e90700c0130007038000040c07182c503017054031000030450040001d1140104d0f0a40d200c90480300c0c1c5542c1741d902254008090036400c4c0442c4d900c1400050fa80e042d100c40c00b03069040c0311841c50f401e00c903090600d0f003812002010081450201d0314903040d008404042ea1003070340300601030713680c8000b41c1c7d00b00c0f803170300074070000070415070900c580070900d1500320001d548a940c0a42c0d40b19030842c0d43e00c0d1555580c0200c184200c4050080305404203030365115480c000c1511055040c040011404400414000807603200d480c801900f203102000c2c00800c891905c01c40c0f02680d08015401d1608002401c8030034445c003080a4107110b0760441304410000c00401c01c1005580014a00f41c032840340c284940b01a090444174248a081c0b17171180c42d013200200c1e208880740e030740e0181d442145681c144824440c4850103040c801003000d410024046d0880c4090700290a8101250300108000c84800203048110030384e03031100d07403040c4d0814451195a0300e0010030340769803040480c0c851034942c90300c3c2481901a0400a03d00e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 601742455 1250 601741205 601741241
    0x30a020109061503020f0d0615090b01020c090c0a030902060417030c060f04170711090103230d1704020303120403020d0f0507080d05131203022203121103091e0306060901060207120501 81
    0x5489516507000700f90421081c0c081e5046003a02c10108810171a08450c101e481c2d0744180980c42c0b503030f4425405041942c0c806480c01c0d28064640b01007441410460951480c154000200d100c0c1c01d59090100e5904034a070b40010100c0c078100b5075601c0030a041e10003003000740c02c0800f00e01d00c400c1c0074140d1103200d6001710103011313049596180c0c10403501c4944180d000a603500d030612000c0221002c0065425409440d65441c0003c1e0900c585500c19940000742003668036110034040540401d011b110454080c0740300750024243d802c004000909401001390208040c84010310010001c140f0000c100d03060b03420382c6000010280c0d903d01c54545a440311000280441094014070541550036034003e10300030650410036503000110520b0304c00c042c2c040780030040513542c00d00690495540541c0c442c015071003150b030699042c10700c02000316080c880c0d050280c41031100d0340d00180c03846040c2800683d400035829a48920198103016000c0d540e83d00a10401048030001d00b00802404401c0d40b10300504080496a8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 601743705 1250 601742455 601742459
    0xa030206211015021c12060801020f04031505060d020108061c030f0e0402130b070309030807050c040617060711150a05150d171b030a020109061503020f0d0615 70
    0x3003214090140035000e001c000302c00c400c88086000240c0c00072804081317100407040c20b00e42d0740211602902c04c0011880982ca03280e0206401400b80080e00d00035103802d58154407949141000d48502010252911004d440c040501c90203488004034a6140c94081c00c00c0d5440345c4a560100c0c1c06030701c0d5101036000045a0803181c0042680c0602d5100490595544400304140c3d00707070400c0220702c00d1310310081000f9014503081140b401c4400251820f18020b060104810f95282c56145076548408c0044a1a410108690f0f017545054450700d4090010340110320f640c0c2412440b019603941010b0189000c0c481100c52009940900300804001064003500988050074900c40b060b011f44010740e800800c1002e2400515650304040360003140c0c1e25000034082903071081030300f80390040e07920103049690380c0040c540140448500400051520500785d6000141603222030070102c00b210101a081d00841c0c401030410400741e40c07030301d642c259030790000c95843c0444079a80c80c0c1003004006061104003080301203400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 601744955 1250 601743705 601743721
    0x1104120f020a1e0e0a060b210709030b180106090903020105041e05120306060702120a0203070603020f27031516020303011805060a0503070906060e0f0a03020621 71
    0x2208040034401d540b50384100c0c0c1c5901000f4030021041483c4050760446100401042020022407500125028070004a0725250002c146a0ba806000c441a2203c2000d0702c440c45108000f100c00e41c48521072034900d210504507a100705008901811003c0c42024503254070301e40705405c0d0301460041c01407070b80402651145260207400703131804031815074078100c1024121140c00050304088403390750080c0606000d16828507404080c0c0c0002d411240c01c50070038001c03440140c446410041d808282500241001501481010b140c00301301e4000c1820540103121600341c540d100c0007902d200c42118500d0344008401d01072060307a080781030b030100d1f0f0b41441a901d05645240314800c0c054044c4084072101f0380f400c4d43c0000c0981c1e03648000c0c480c3c8200c0780c9240c04200b080c0d408e42d13880305030041801030402c40015903800000f49882420307000483c60710381d245070030000e468010346200c050050540d4115800b070100000500c41c10007600c40603000d0600042e500c540e10703000c0d03a03a0010084c0420305000e010304140700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 601746205 1250 601744955 601744973
    0x7031403191a010806060a0e0319050f1b130902180405060f040b010e0c130906170114072f0703020906010201090b0118200306010e10050a03110412 65
    0x11010441c0303031600940c1c81c0030541145185800c0d01d010307181e407a80f030380310141404030580c000c01541c2c0400c000d02c00186820f41c0c00f8000c1040291032207019826207415420b00718104401c460758100c49600502040201540040a0200c8000d080b030f0700c3c3c50250301424070b82c40900b4400200a500c4500760b040d001c2e2000c8001001170059004004440460340e9080d003001d141c00050394003500b5080014010403402e209103c07910b0f4003410911609051011010101200032410340200701d260391144001d100e100154070303151101c0c6182d0402846108460f05000040c00c502900d42030030030805800e04000341c40e505846080002d1544003407205500545130f600c0d02c0d1041400101d1188404901140156105000d094041600115090150b909e000400c041d0881c440d400415100c1d154007400c2d1900000790121004005202c05080d0b0b40e150002c00101003140c03d412251140710060f80d8903001b581c0c07010958682282a080000742c11000401540240c01540d2141e20700d83c54200c01e490811010306 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 601747455 1250 601746205 601746241
    0x3190f14100e01140103112805040506030f09010e030d1506050c1e011512022e14040509010306091a09101e050103030f0f080c07020607031403 63
    0x68146040c07911203040c460309030034162180904000c0e90700014002484030810340d44400105050000b24008600b1070b0107103a8020130b20100803081e400d00881c07040c40c45080d102c0c20030036052a29500c1d046c1000d0005200d4000500542081c00d11400001d007510403d51110207058405000c0303c1e29070302c2001452000c0c040380391a00c96120041e010002c0c0881c0100305994032091944041e00e4000c10702c2e14420102c07280140030342e840f5900d4005d00125000415103204c050641c240d101c6c0c0510440c0d0052110075a0f92098400c941060b0b036402820300f8840c4020a8100c610526005046a400d0000c00c540c50007175401c8103a000342d80b20000401c0042603030012400714400d005564600f02d00300c00c084840ca0048820304116004846c0b13131034100302da0341c1c029042400006a800c00e02003000050008498090b0170884c04a0341150321181d0194212401e00d452030381a190103c4245411064180d0501540400a000f602d0120346001098000c2020700c001d0380607894502d0704c0c2d1926503090100b1100e04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 601748705 1250 601747455 601747481
    0x61802030a0608060f151e0d0f1502040f171903170c030105040e0706020c0105090109150201050402011701030201021b010c150c0f0207030803070804051c1d0f010e0603190f 76
    0x2403000c0443c0c2498004502400e0041c07e20303000001c0b1010030300c90840c110a1080300d0500030307042004002040c4100201c0c948100040c016216800c060003101c6038481b42d000110501e0341800340a0301d155002501c00311200c403900c01607001004600d000e0343c688074010082160405003908001d8060aa0805941250800c44003032019115014800d40c4511a50044c800160000300c0600c0080d402000100700350311062402d10880e40c1d442c1c90303a64001c10009040310050351558284421b66078400030701004041c400d483c5002951541d800070303581305a2403c82d41150043c2110a4030683c1c016200d802e0b40d10307000604410039010100d500c0f401000520300d2180401c03034070700c00340d480c00348006a5401030ba0707407000d801e6145813140344090b61480f41c01403040b03506100705540b1401e40c203090107603003a0038000ca0b00c56410191412080000442031448003078015001480508180d03030f4082e10402d0340020641d00300f0386c0c0b0380f50f015044504c0c0440640301c103821070038443c1c528441041d642c0030b000300c00c0391 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 601749955 1250 601748705 601748731
    0x60203040b070c0210111011031b040e04061d0f0a0b010b040e0c0f0c030c0304050405011508060d0203100603050a02100f09030314090d060207110103061802030a0608060f 75
    0x6a482c0075101030300009006500001005001c113465800303014540308210f40c00301120001c040c90030703694040da0784101880d000b207800030045c040f85c502039030407a82d860705131106030605150034180341080405000341301405d026100c4101102c0b40440c078194814480c0c203107042c4d815011401c000c083c1d88610054007166030704810000029a110484250b41c01d5902c2c200c40c512031910b90800715104c5401048005a8540d010008198505002c000505802d0956805183c455107408204021140c0590000c0714030b012918031a085079600400c119404001180c50101c07017441800801e10f8250001c6c03554030700c41c1c9050004014080c0005003072465030710803145850a5800d44808076100f82c0109903100c04101d00040070300c0000e0080441400d00000d0104584c14505050f0001d040c82c01000c8080d19103c1c0d000460b01c1c2800886620054041d000f8201070042c42e240c00c0e421b6040c00300010310403055513408000300c0e14800c03140e0000e030024524042181c1c49030030b001c039883c42c124406441036030780128 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 601751205 1250 601749955 601749961
    0x40306022118100902030f01060e0a0605190506160209190b0609010c120507061d1b060306060c03090307030302032715031806070f0210050408030411120a060203040b 73
    0x910700b428182c0281e010000b07403030700040008a0902425076814104c3e8540280001c000010300d0034402d240080220004180c420f0415207810012103600360403450042403810007100489040714540c00485109580712a80c8224401510f1241007140d80000e50100082c000c0c402d60b60b4841c41d1400d0400c0d071031041002005001400c01031b09101c1c03445018003041181c1480c0012443e41d4003001035030000d40c141a80351a40d0f40e03032140101d82010420358055a90300507250585032041290035004a403c4001c01707200b0125500144290000800c4c070b600c01c0350002a1607111030818015618076040250880c3d038025186e00c2e000c2e44035003100402c0b0050754050341603c81155110851440060405494003e51040c1d03080e48481ca54402850b2003001c4500b200c604159100c200442482644544e0742e4403048540114000d0901520b80c0340707549000d0a0006020108010404485d0056440304043c016088041d010a9801008000d298858069660b000c01840703510b40046100c2d500c42c500d0082c06507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 601752455 1250 601751205 601751221
    0x1c06020405210a08031f06023f0a09080109151401030c06080606040503061602010e0c010e0f04060e01030602070204110a020a0f170c160b0403260403060221 69
    0x42c1d24000000c1c0741d54006440030300071402c02002581c20000425080184600c0c0c5c080080e00d48205a00c9800142d0000788244c0b4400341901c001464a40326200000186d00d810074011840e4640f40ea80e01880c08002a220700c0e000e0280d01524020040e000090000c0d403100e0401e6060244000d081489043c10405070140601d0070100c07850582e071b4494462000340381004d004540a80000b04441d401140800011030a607904000c000c0c40f9030145032080f090350701e9034a0700900f0741340f0481c889101540704500102c5660303000380082c07c038880d080c0ca60b000152445070014000d00210b40c01111041e008200120501540d03070001c1c603030a4001d80f0240714809113481009a184502c03100b520040c0c000c0c1240500141800c1c43c203484850107068203c20000c54030687c000c540e40b00d44074020706940820b15903ca60105600c2c0305000700000c0407581c1c141482c42d20703801102011012200313034040d240105140017071201c0c0c09903005190040421500c801c0c504403002000303034008082200000900001070615 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 601753705 1250 601752455 601752499
    0x10b01020a1203050703020d1419060f0b03190216050f0a0b0109051306060927021c0501060f03030c0201080a060b0d180b07020c091308030f061c06020405 68
    0x4198003142c03018969110120440041001030302d80001c0503020010786903641c000d80104a07040340e01f841017020070f080104040042e403801d81c600ba100c442c1004010072002c000700c0d034420100d51000804c20381e03a0342e031102d1042028622010b21aa05403020406c000d041c0c400054006580e4483c41c21603080d50000104903981d5000c00400911910108005110342000d907002250007007960a461101c0c00603e65503030050310800d03080900c0c210754500160b84802e001844120310b03461580ca400d041d8141c0d5801040030b046000f11240390b1645401400c3c01000310944c03000000300800c1d1801c142940d03c80c5001800d0300812079041e80081d0f403102c0800c8000344540310340d6040b15100310001b864504001808009420482820115001d00c60590740c081104510564422007456028000c0311442200704007042c03201401072002d010481c0214800214200b00b201d4104141c82500d80340d03965040c000940e5294903502d82203004656412000030840607030050400d54804407051110b0080031584150340e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 601754955 1250 601753705 601753723
    0x201050906220b0415200d2708101d0f031e03151314190e0a030c060f060b2b02070f0b0c1b07060207090c1736010b0102 53
    0x41100c541501c00390030780901040c2841e141b2840d50710001d085d01c200301340d0501041542d1100410300c5000d0101030400001c1c2c01030b04026204c030203192850b0401c0300b9a90780780e030a2070b07a043c00203983c0d1801d810781140c400080300c03c41414074102d03201c8200300e0742850340381e41100c01e140030001d44800b61060301602c084141d9104640e00b5413041c50035184001081003d1845900c400c4205649010180054414011003403081c5856078640080c1101d00c2c507100100c1d485090111940c0e00007203640c80c0025802a800341c4d685405c2280404c2c2c60400c0c0e59440010140d44c3c8c0159450f41000500c540000a001c000d220120071666500c0403e45002c911141a4811a0740090a00c01841d04000000e02c10720405908044400c1c1c00300d0400001d07200c2040403856114100c910343d03000034030400116034100105805841803110501c0501c901c00405803403181e5220720608004407410014906421560b01c2e4441a6040003402507009007034415074442c6d0000d001032107201d5080411800309540006281031f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 601756205 1250 601754955 601754969
    0x30203060102150a15080106030213110703080a111902060108160e090c041805070506160b180d090519060906110a050a030f030513020603060d0201050906220b04 71
    0x101401c06070901040c03030383c0020810403d6554640790314036102030310311444010301031001c000a2007901354010005c5182d50900007403440b90618081c41c0c1e407102010140c0318503603458140400c568603071458440117010004050785501901180008403502540b0b0b22010b104007580070350b01c903a41c80703020050b00d0b00700403900c0614600503031204101143e4016801a484401e200076241c07000a2100060207503283c0382c0e0561405500b44504000b8010f0501408c03005020442d10b0a10340b0184a9540c6849004c5840c06003a070048a00011804e800c0d980301d103c0040045400d85a0911912101a00c16030303140c090103028401001d0103803080700032044a030b403e59420792507040c1c2c1e00c7d00e4000c2c22603c01000c0d940e170844a004454110002801c10007110030480d1084d140d118102540c0800203048a8004106074002440e001001c0e0142e220441142e030004807e03140380740c3d05d140d1400144d82e544203409540707402110001c0c00e5a10140411142c182e8402540104c0034103070355407400350b60036001310f0040503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 601757455 1250 601756205 601756213
    0x151c020a1806022812022d0d0f0c05010504081905090d022b080409110711060a02010209090a0f29040b0a12050c03010b010c030203070b0403090510050c060601030203060102 76
    0x10384034505014807542007004584d40e0f410540c1c1150b5480400121962107039015034820140c0030750b00d49030344d0716004412421840d0007c0f1141c44186059944950710903000c04d02081c81503210420340708601140d00b942c0c01072b009000f2802e1518010302160700c1104c1100006038880c0002d01054403407422110441c0c0010819102c050140e020803c420385400110b141040407d1000e100c1241f038910001d40282c00f56400036107a510344103548040d203081610310b10303501c0010060030000902034907151504100a4501944800700400103a00900c02c1c1e1140e1584050300000700008141150000c0b0148942010180305482100f01c682c51a0b03000c40480300b501800c4004a0307040c40c20154850701094100610ba0041d1690301c02000014101d00746003621980c0241c1240c4c101404c0c24007980400324001c1c178041c0700094481e00c0080d00c81c050030400811103005070000c50b05041c8245018005800000c19081d25a40420000b5010740d00419100310103004a10008825600034801d5900c10342d01a00a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 601758705 1250 601757455 601757473
    0x2070b040503120f04030b0106030906060504050106081b0c12090307050627041e02030a0e03040b0a03021308070803190c0b01050f1206150a08010515151c020a180602 73
    0x504540c121341030050130903c05100c004040395041008500801d810f4800007540400381c24020140c6080340c01c41c0740214141b5004000c039603803111442381c1c400c584100f01e6000c00b00000207072649100b103021612182c858040b10303a2620758548024007094004808a9400b2075a680910040c0c0c010000261220158030301200404004904201501c440090000a01400400754500c2c0c401807026070196031503011040140b402a207105400e21400c00b0f400941c01c11b031408035440e140b4490313036080004068003c5240b101c18111090038101929260040d1085561109076103540c0c0c0d0040303004c0c18244810fa6090b00103250203012a2815150804480c4043d6800d101c01c0c400080d20320300c0c849030890038000b641d61002209100240c05010b8110514072801c0b100c5040040700034803901f1865459140409001598050740c0305100440341c183c03928100007041420b481103a001301d40d00e0b4a50780b594070f030f204203024429034020880d0301d4180c1c541d41d00d41403810400381114080c3d8002c03200903a00110390 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 601759955 1250 601758705 601758733
    0x80f070b040b2b0204030515040506070c0203070b0d0903020d110a0803060d0f060501150809100e150408120a0902030a08180a030b070f020d0c02091801021902070b040503 75
    0x24400c0a02d24036000401e0a000f11154401c00700d15030100d0410b5074080b90910421038144200b040c103085030b070382141040c2010f48410ba143d00d00502600c06204040a5200454905000c098010504038602c5515014106400c101904404408400501a803050410190b005404408100c00042c008008045865458400551010304419402502d4002c0c284c00a80600c0c0c0d4208914030610010800354900300e00c000b40e6060751801c1205000d008010070034808800030381410950304250021507030001d2200080d050621071403090a40f04844400c1105000b10400202082154051140d4041c3e0707554428104a41c00d02d48025070540100c4050800b1580780e1001e850003400d2500114110740003280001d5495810354070485a034010403040101154204c5200340d2949030b640040d1100b070600880c02800c00345542030080c440c01103079000c02c0706082c0d40b040760106100c9131030007195101d06041d90080c54016100241c0b00511070350102241400a2609039402c403540500102444d0a903d61 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 601761205 1250 601759955 601759957
    0x10b030403080403050d0504050c04060504020f072010030501050f0607051c03020904021314040501030f0314090d030201140612071802122a03010308190309120207080f070b040b 78
    0x22040c4d040010500001412800c07603c20745015510034802003404072051818002950310a070300003071049105201c05020804990200e030112075200c200f011101e411104821100500102c90703541050440e411040d0b20781c0c150380005e058030001c480c070204c4010901c04100c01d5129950000305140c00c80025411242c46402d140d01c2444114140075003017008a10204007280c100d0f010340d0720724990140007006200f1420038201807010301500d00340219070443d00c880c421044d141c4401420005600c6c01e921007050340006481c643c0030b0061450348261820304009002c0c00021031500039542d0207001040b030a28280072508040c0c83c01034098030755680f6024100c04040311290403504941c2d006c0007501940d402d0380080d14404c100f00c4542c1c2c4207880780002c003040503000e124544610350360100b0041c808074492200f56034525100045e84001d1043c9640700b20064600803800508200403407116130714070b03074010900e0750a030780555040380c0c20031401201096550303115101d96060100100000c0c814416518 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 601762455 1250 601761205 601761211
    0xe070f1814010321090e090a0c080303040f120302070c0f180b010e040e030717040f060906021911030f011e02090a03032003041e080318011d03060a091a010b03040308 73
    0x41480c81c142c0e9030b01c001a05151b013080741c07a403510341c102040d95010480b4a142113006801e50000a5080d0b14080d629174110f180040c50207090300c02c0121104092074801d4049640c180e0b448080c5040c0c180c0d44500305140c43c4900c0c01002034442d0200b11035910030900f8454001a9401691450886072010040c4801001501018880781c0010403100000c912010050340b15514450140740e81c40e40792100c481001801a0444810451004000c01c4020350010b0745041505ea0f50a6002c40c045580c038000904003d004141a0180a21b03d4540322851041d80004035235688404030b0700c585890080820704a11800b44004d034400c202c00f03014000710740f0030164103c2c0100041107a0740d03200004070006103150010380c00085891259500282c1741500d845080005040020086041c054110a41c1490070744003130800d410840c4400c844002c0601d8604030303801560024003501d8003801c0c00d81c140005010b132958113a4580409030801e05154501040d00e80c12201807164040c150340b926a800c540707441020f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 601763705 1250 601762455 601762457
    0x3090d0b0a0204211a0c0d02090d150606140f032a03010806061009080c09090709150e13020102120304080409110319050603030a030e070f1814010321 66
    0xd02c0042607032030900d03006403114007006041e080d44c02c10502d412052006860b02040102c1d07800010f1100f159a890103950307850034801d00161f1034410a00c046025641d490a001e4018400791540030038a6107581e005500b9201e066480c1c002007144e84103889218032554109101c00c10040002803800f02c01242400f000140003821001c51010b010b001d07440540080e00550415040030040c0401468952400403020465041582e400c0f460310352107680316500c480c0b140d4007440c10b8074001102c038002400000c5c007504841008000a210303d001c45641c00da824044c98402c000300380080380c1001d010395124042c5d664140d0007440c0815240c140600725400c0600202d607002c02c140000300c4c010380180078951080030310b030740b4454803481d0091030007200300462103800a94500d094140b04250300c000c0103c51103c1000c4c280071a10300c1119034480d10f03008d010f501902c400300b110303c00440e0b00040624000c0358a0321030031040c001480503042c103d00032002844001d010751445160383c43e0222050700014041816 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 601764955 1250 601763705 601763707
    0x30309090411090c0a030b0913030c0f02040f02180a051f03060b04061d1e06071a010f081c09060815030a05010c020d08040c1205160609090b0303090d0b0a02 69
    0x528000310f00d5a140030355071003807100c20210350b0040f080d90510032404070361012100200c460824a28448040b06100c2014081080544600c0107110001e003107000d4040d40500200310b0340e200801c030b16000b50480440e15402c1c003500c4146840d1890100c01e10b07400d64400034101000c410321a1140d40321526080299400c0c0340c3c4030b83c000075105003a180500000c015540312044002001404241e1100b00007012a04c41c03001c400b500984164210f100c8241c24900303603100c6584001a05009040201902620030310003a610004144840b400454800b02c8042900302c0d020b10002d2103540c0354035030440020100160b000081002158801c140c000c3e0005410384816940320346941c082414001d10b41400c4e240c60307440e64061610568104490300c010340301490a285030703043c242d64070000c0031942d00c61100b90481c103041e20f0007448000d00c00d07481e8103001da910000308a5640c4101510080e003910420700e0716454405026064280031007140c0020000804010001c041540c82c282006800f0340304d2061154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 601766205 1250 601764955 601764983
    0x324060427020403050c0a0b030417030702010902040f15050d050c0f0a091a010e04060f05060f041205060403080a02031504090c0909080403020f04060605032d0a020a0e030c0303090904 81
    0x6042c40104043d500900240000b0384240f000c1c005141383d6030b032044540013005c000b007001041d9424200000740d11661002550381d101d088003280034001640d4061743c480d01c0c11548504241031640440c046d00300e118a80d1008560f61010081844c00e6a10090002d0700a43c0c003201e0580f0b0001c1400e54404002032040b0300c813907201d600007000ca500d6400030511255903000201c04a680280d80d401043e00104c90610004e42460b0040c3d610704035500c80ea50041c20049509031034100e8034025900075019441c0c8040440b13550f42405c81e0b80d06000d540030343c0401d41e805c0c04150362061a0003140c2c802c818042003030144041c3e13401400010042004103468100550901048802d0309019410328540a503c590f030301d640c190700403c44150707641c9240c10b2241d4501001000995003000039607600040c082801328241350105485a96240300810045503a4844c000304505401e580d805007280c1c11803607075584070101032041070554580c601140c669256000b030002c800c1c903203409212107030300500c50050402c1d000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 601767455 1250 601766205 601766279
    0x1170a080307020c0a1406040605030402061e030411090f041202070801111b070e0121080d0f0f110d0c021905030703110106064103240604 61
    0x5007080d20800010b811010852145141880100380540840c50507a030a07040c1900000304284500d1144c101444000300c0000d05554455044d12070071050b25039120015a00403004919035030040768111800c2d0040c412010341410800c5c5c1c1a4494106080c02d896a6200c544039968824240c902d02d9085207c7c0d69800305503c41c2c01e0003040441c620100103140c5800c3d01446c01000d500003481282030650200800f08000482d050140741160610311042d251050705045030340c0c1005d00c03240080c0c81d1000c0051342c40005001e903800714204142622003003000d05003080c1020285c41c2500c04540b032551007405942d030f444031650310041c2c806a050049400036400080520070760032180c081a00c094101282d2401819040036005e00c401100c08004c004035800d1240103004402d000c001003c001c0660b121032001a000000e1544114582002c0c5210348518000040101d038800c44110102131074100302c50342c11203000c000c0003c1c1c80d41e00504660509007401e080511038141071000d02c0c03944d001c442c01c4102d10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 601768705 1250 601767455 601767457
    0x3010221070905180604150e04050a1502031005090709030507171219030b0607050a06061a0a080604090204060f030606030606050901080c090603031b0f010c1701170a08 74
    0x4940a0021520528000d4000b4100a519900283c0104084031000c0d201c10b220508aa0b40003e0480340011220111000c2c0040702a0640102d402103c0080512040c00400241501e1b00c1d48141c030811601504010501c0681c0016100c1c5030408118420900043c9405040c15511150328942111100d9607034030b4441c03416040360301c80214640140724850700e0300420700074403892485480c0d243c0d04e0194014240000244034051140400d603450090340e856031b682904071500381c1e4100c401c8404404450900c2e80003050303284515107910624404c0311829100402c00c2c0d44400d21030b030701c4410301c541e41c01003444083c00c025481240d000f41d9a0801051005000001c50017560043e1000642d1604501e000400c5032002d0b04841d1003040c812004000b03940300015015444901642c52486a07100c0401091541c043c426101245481c2c103803010340c0c5c01d500010419600031b0084002e0100d1041c4000c1520600c5080060321300c8400e003400180000500c002c1030215029141040320640c6100b40c039205c9603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 601769955 1250 601768705 601768747
    0x90b0304023c0906040c0914030703061a040f110406050702150703080426161103010c0f020c0d024504061401050631030501090b012103030b030102 65
    0x40042c401c401000b0780c14001016035110704180c0d401c21240c4a0000c010f00068040d12401e0803003a80045284403544080c0301312001150f20a90a12000140d000d104c3c0310065058175007030059141000410795209503006503096038404030100f40c42c20b410040d0481c0c10390b11841c3c090341c0125085804903140030b500d000402866010340d50705103507401c1a02c0e141c891400600340c400300b00609081d238443c0d20301c108401c64410216100e000c9403d000c0d1450400715101d00b00391041d902d0b504c0c204030300f2880c5400c0b1503181c210000075820b54a01110910410a02d400b2120b8069000205010040a211441c0e1094591800101c40c40742c1d80400103c0a40c00044011041455215410b8284000c0010754000c40d2141003010205086940c14080890290700070080d207020501c0082021400c1c02070175810015029000701502204503841e03080c00341c0030f42800c081c22210342510030000a05403214204403903190852005c003049040716900c048000d07041007011654555800c11801244900502400d54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 601771205 1250 601769955 601770049
    0x4060f0311150702031506011e0207051206240109092a05030403020a0b06010c0b04120806060f0f091302031006030b04150515040f0e0115090b030402 66
    0x80080400c2090010b00c084249031100890703424006980142e9002c180c1078030368107010b188a0881e90701c1c800100ea000110702c40314694844824109080540d02045000580780c081c0c50501092001481d4565541c0c000c81e01c00084013451190f1100700c00a800c0040002181450705140785034503402c1c003008440e0801511958100c01640e0210b03c1c1501413041c6c9103001607824040d04614050310701039203940e854000100411031000020b44207a01942400c058141c00c03800d5944d091902c0e01d804a120300ba940529000300b050400010707181c0c5065011541d0001072144868203000580b8604482500819140c582c8442c14a02c1201c1254040c4065441205800701ea05912490050b024045800c5120200c3c007842c18120021542035601e5021030454000f5140203e00f8000411541040d016030303080501100aa410001030940303003000c4d054140c4400f141448441407001078140e800d8030a6124014081c0c50500010b800361400100044005060004220080c4180300100544160380b5104403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 601772455 1250 601771205 601771223
    0xc060d06031505150427080f0a03020d050a090c060f12020304050c011206120f060612120f0905181314070305121303080d11160317040309090b04060f03 67
    0xc0380c1d49a4658070452404c800b41c4041000000300c080120003840600c08000d001e203003006c0e02c0020002c0030401c840d0031003c1c6650941d1104a000301c020041d50000203911806402c00c804200f90071190b110320007074035a100101100300c80c90320384260b96403005001c44400b48001c0385111074000115000a62140b403041010b410b00c0300141001404110605000d6000c85207000d405100100d00014108842134000080c0d1640f02c2a40c80c0030030103000c094112074501c1c0e050040403820001002d050940d844419200c0240000490b04100c40d20750140c49080d922042c1000e502c00d0805403e0505508130030b9002c94851201d4086e100c84020201001c145450355114070b00400c03c0c00814000c00d2180c81c0c2241c0d01515000c0041d4038131250800a000240050300d000030a40708001055100740325030184040c0c0103031a413600c041c54031800429903000750b000c9061500101c4014507a01002440b496041d00d0f800c030702c10306100e040d000400180480c2c0340c000d0f40c3d44c4030101d010700905a0071001144640e86207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 601773705 1250 601772455 601772461
    0x6030809011805100c0c080114061f0509040228020f15150f210307150b03060115050903121308030f030714210103030e030f0c060d06031505 62
    0x14585100369000c0c04081c40404801d118560340e054010b20301da0200d240080c004007160030400303200790380c641c1f00300300c00c0d860030020040a0030888011446500102c81e01c0d1441480c7e030781d0b1100c811460840c1440050300820503200e161425501600146410b50b10102c0501180312144010303400f00c051110159100101401c40b080081101800701d20420760341c3d04071030403c24140c407004400c0c2c410340c5d032045840303051000c103545911a60300c2c1d2092900b00c5030303d4143c6401a07419101e50000c0c10030380d00c0940d6041e000700c445000b4000c04418000103001000c4507840c0c510b418071103c20700e82d0040d00b006820403150640b1b580400c05150241e201d0f0307291542d100d5100b0713403401e403001c01340c0e004050700d400511101d0601008001584c0d4081ca140c103107030002148840c04500d491280f00110811680350210740b5642c140e6860030320341641e119480d00ba524007400380030999648204c56052a580c0c1c4070144a052a085c0309000d40740f080c20600000c15401d4590380e13001c0c2c0700d18669926200305550741d010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 601774955 1250 601773705 601773707
    0x30e0106080d021507030b030607030204090b010507150b06090301020708040801060f03020a150905420a1d04060e0f0a0203010b03060603060a0e090d03050a06050a17030d0603080901 80
    0x3595004080d520001d180350154100042d485402d81c40010200d80b20300b03800181220b000380c01860031000000d0075100d240c980618054001c0d04903014144446180c01d0143c07005500580072602c1c60b0390080324a5000c8840f91058101070440351018581050003800400742544090001d0310700e591281024070344131404d003084039007120680c0c0c2c40201c4803005c000040002d42c65620508003901c901e41c8440c00780d4a40114140d880781e00c10f0b03125a82152841c1c841240c4841c00941001c0502900c82d00c504000a20110720300228503103005100981004225405049014500d60002c040035850900040c00d5100d00186c0ac852003503210452450803081040024109d140c1802d0b800840300a08606650404022032044d020042c0f516000310b8002011903c81d60360580000024183c04101444c1403410441c6030340c56071055542d95000c13a0030074010942202440c007401c4180e50010700790004107031900381c8802d100744187c2c0c0310583c01e000c00c0001141c00c0140d800344402449c041e8480d1550b030389141c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 601776205 1250 601774955 601774961
    0x6090b0c161220010c08031003080403200a06050f0c0a06051e01060203070302060703090f0b1f0b09060702012d050a0815032104080322060c030203030c030a0209060a030e01 76
    0x211219440100d0050b60f41542c0e04000000c5640380c1146040c0d44039540c103e15801030119075080642111408030700041001002c50640d000340c400e0821031240d01c040c19041c41103640241c02010082a4180801941f060308031029200080d00d2204a80c09640303d52104002ca031402da4028080700c62403032400301c944d04227020325030050a180c40254074010558800035269580940810201600d8007868401d000c0100b1350002c03034503004640c540c00741c1001c2848041e40c05109c0c1d0020b40880c08500d00059500000c4103a820155010b005186060150390045401102c20298800c08904002500c0c0980d600c0719400c84200003551595590790150310006401c0000c010020352000c070f8640c003401d0a90b107003c40c1c9110303d03c6250079800034200074119580c0d618011354200500501c004101601e4010311000c03202d1010703981e03500c101d010341c0c0c450804441034103650300c002d005070b403041010910102d40c0c50700440e401551074000601706080c0a0005d0103503402801703208006070b200c41754212200310a00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 601777455 1250 601776205 601776233
    0xd0605030d020304030b0606031003050613030207122001020307050304060509040f0204030f12260118051b0a090b1602090f06010c0209130c081f0606090b0c1612 71
    0x2000a6013402d1031607859040042d00101928020003003c004103102401c0f95a0507000785a01c182519240c1c5001080300ca6003455040c2c0960040c8516a0006400004e007090083c0341e5030814440032102c0d01003844030300302850b800c84080c110701c003c00c0500b0120340140301800c0a0442c076519907949030102c400b0403042d50014070003003105c2e45c8104810000a0b1900c0348000809511a0074240020314207401512180d00001c0040d00542c210100302c04501e010401007810303515901003840a8409404c403001c103c80f0129070301142d01d100c0c03031001c7e4031241640d0b014141c04141031511030411500e034a2507101d41d40103405103448134031104c0d08032021442c0c0b00140f03d03802038150b150f405a520300350000801603800d020000c5c0c000c43c40794011800116030215401041d07a0000004801c840e5982030296840c0112640d680c004034032250074504501c1c142c0984801c031401c42c0d5492070003600300700c3d40c0481070780716640d0080141320b821040d141d4410b44c1d000580040030084014409011541040d0743d15400f11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 601778705 1250 601777455 601777457
    0x16030c0503031c0c0e1e010909020a02031b19060b0f01110c06070f05010216290609180106080708070602160b070203240a0b03210c01020f0d0605030d 66
    0x80c00743e2100c030b154103080070380d41e030241c0200852018904007003600d01203000d08070701c1d80041c0207010344000400e03107801100360000281e0303c21007203030345d034071450000c07802007420a2005070402c0101d80e9010300d111507040850400c00c41174a54101103a0b011410100344408200c440903254080d01c405840c140c0c0036002114400c0c2445071309685148041c41d00c1da440205130314441c030400f2903580e05001d80e4840303d220740d0f64414007c541d80c0750480941c0c0b45984801e441103a1503101c80d000750081e1406498030b00746001c0e14000810058585204001d500c0c4d000138110041c009485090f403601e072000740542802021035402409c0400d0808941508282d441e41010095620806034428160200000e4004413040d0b040c10075111031003840043d04040045060158030002c03082d507600103000c0024424041e00c922042003103105010f1007410703140c40607009154112042c00c1101010444800010088440c001c40014503100c181d80a81e40309400c0400d0b1850266941c40041c40035040c1042030241a840d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 601779955 1250 601778705 601778707
    0x506060f09100b0a18030b090c010c050c0906012a020f01020f10090f140304091d0a0b0705041a040e0109110d020702010e04020409020c010c03020406021002160516030c050303 77
    0x3100884140208510035146143d0340064002c051900c01c0000c00700ca525420450304083d030742c03800c02c100181030581c0e000413140100205c0301c081d13600501c0c0c00072a241c6d018000e408008540d008000a40000401d0141441034181400c40c650342c02c5500c0c0d95545040d41d03401309070041036006000a251848440c1419035000c07850b00c90150304005411004071700d4074640490b0345541da1418800c030140f172100c0101000b005070800c0c0c002c2c200200c00b40050b508002c4c010001000d01055040c13030b1210002c600059900000c0c0d080001c10781e804a040d52090711070600d10b14296490484000e80e441400c04003468160200d4140414032000c440a401002c02a5080c05030800d13103290880288180251011000d40c002200000c590059940c2040000c0c01041151501d6541b85908060f611a00700030000d03528052181040350f010b407013900c058410660041086000c940101402544a0020061184c1c16180c50b000010410800100a0341071000e012041c94a589402a202940c3c1e4103da80729401c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 601781205 1250 601779955 601779961
    0x6080f12030c07060905030d02040b0a08130b060423090102070212011a0105030702011512061d030901030f111b0d0206010b07240905010e0706020c06041a0409090506060f09 76
    0x10031001a2034280340c104d040007696480625080f0300d0343c8a80f030003082449001040c0007520f07421807809000b01c05070702d45840c0c0c0e0f00da840080d1102c3c94410b840c1c0082074008042c0201d511030030181e100f100b02000704514001402c00c20001030307400700400c031046821607400107040b800b10b007040544a400000c2d80c0c0020302210000d0302040313207011040c41a85042200c00b100250849100350801c211418920038588007060316000c0640e17000e143c1c400705a4a250501c00300000707121900074800d0031b8400c00702c0034504000000340118080d00c3c0c1c0c0e5001c2c440441d280c81d902c00031501c05a001703004250b851546600f01c02c140b040000c0c10203440240c2c040c25500900c1c01040510b00310030458100702d502c40c1003034403c4d4079500c040741106061020401100c81c03070016284100241540b080400d02800d0b4100d62280d540d0313440403030750340d0111542c09400900a2108014151502c0303c1002d281014143d4541040c2c0c41340c03020390841f4094041518180e1128082c841c0750f00700445c03941a901c1c005e5a00e40d00ca8a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 601782455 1250 601781205 601781221
    0x5010315050d03140f0304030f08090d14030a02040b0d020909090a05030412020612091516200f0d12180206031f050d0308010e01060201090c1208090406080f1203 71
    0x15082c1c1c80103424021010714040c204d0710600211450307001d540113120780304c0c1001e0034010182c202646039080412004070204450342e00c0001c0740b07050100c8039070710480d0403030002240084942000e088182081d0302030101060082c0002d0142010011b0b0302c80060315503000d2020059440401380c01132000350007612029011407404402c642c01e4405c03640404003004010301c041407843c410030340c92a0610f004403003404103941001c200c2c2e0f41d4000e001c1c041d014441d25007071405034171409070000c44170204c2c1500d0302c4007403000140d242c44962076100d00281c03811030011082c030508102408040306e00180145400c1800c91f00c0903c200c01d007640d1602541902c0e01c0761980411024800a0141e0b8401c1940d4042d0006400ca42d036010405000003070701600c0b400b01c3c40c2c174000c2c165207400c1c040c0741d10031982c000001c12064070500c22075a5007600144c0140000d03152007000a18042c41e201c1c1a0f46c8000c0800501c102620760b0f000e640001c037515401405085052040d240c100584085030103405441001401490 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 601783705 1250 601782455 601782469
    0x1512100617041b05040203010905061207050319050f06090a0c060e06090603060406210b0a0b01080412020c0301061d060307050a090f1404030e12030c0a031b020310060501031505 78
    0x20f644004011030090151108000c28001584400d034090b00020010842031031036007109005110955680304155201d900c4030707440d40c01c64014541c0561140300d14000003850951190f81060044042c4c510380355507807400d03d06040d021201c100035a80480300000404c1844003070b500052000d4070f40001d00704480000900340e0700c07410030f4407842221301001007107803030703440343c0c031440060071050b50300400c1c44031002c0c46850710f040700340d03041c0d4000e4203584c00030780c0d0940c5901804865190507903400c055961503554152007034800f04003c40451190b202c0e906c5080c0c409200320380103484c4009018442100c106004805201c00401d580d003e900408403c0006855201d01d8009643d504280410700750f014644103030040c5098090b04862950040600003070503040f0b0040d4049407010b0320b60458540c0d4102d21aa603030310454030500800d0b807124964001085c40381401414071800c04c00401d44244181c1c00007441d005286001002141e0f58540801031580c1511035694000c0d48500031042d280d107880c1c005140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 601784955 1250 601783705 601783711
    0xf0f080609150d052109030d080c130605030a0635121b0c01021c0c170331030c020402090105161401050703050f06010e1512100617 58
    0x4200000c00b0520305001022001d201d104068801c0a50611034108103035240481280c1802d03940700c400c00c0c584601c084004491405001400074420744c03030308080403642c03001c0013800c01031446000c0c4150118001c2042100005203030303a50720b0684a042070407040007140e200768025400303d1800805c209174081c42d4141030b010641d103901c03040e031500100070416040055a0700e00c1032582000085881078106a111201404111300c0f0444406484000042e0394408000341d40c00ba1103030624640c00e80c450712690301450b04d20b01c140c00d5200c0c400072880300c0c404140c2080d14038101e11040d0480c001603d100b5000540901c400c400c034107044c42d070110340300580f84403040e0202902498001a00e40350ba0390192040701c90001d640329000980c1c80c82e5040c200e09403a0f000d03084207000d5003800003040780d9502c00e002d02c500651152070513014640b80c810055480485503803070503030442c0c03440c010595800070500180402000b2258039520b240b61500101c1c0c100456a0481000c8c44000c2042d034050021482186034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 601786205 1250 601784955 601784959
    0x31b030a03080403050c10090c09051b0d02041d06031b0a05060d060e0412021504020a0519080609030c0f1903110a081801120b091302060c0a120f0f0806 67
    0x1455161814202d551b4401e000040a6a210f2680710945112980d840040d41d20300030003448000d60f4542c2c1030300b0182e40d41942c49503250608030b4410748401c14040010000c0c070419140c0149029030f503130b9000e000744400d00d403000e00700c83c44001000b996050078000c44914508892084200c10070240000f19251401c0c00303458043e01002c10f444240e40695400700380503200c5c000e1041c9461619107403000b514000c0300a000b0050007410544945200e01c114998041c6134014040303103200e070919060100301a8145c0111400780715003480000c0d60302c401d100d40c1d401804031a01841d510140b20b1700942ca02101c4d009400c829600c4540039405001400840c100b14035410700e4000d03c001c4901c010180b41200d005005410101d00003840d010a40c0c00190ba140d03000c0f800c0c0c8844200381e01501c0a20708603450f800c0060b030000c01d90000a02d0408001c500e49501c14030050045013017524107680c103442d00e40c0c04201107a0b00d085489996040903001120941c20003a640740c810308039003a45c2c4005100c2c00026203505c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 601787455 1250 601786205 601786217
    0x15081b0102010902090c03090d0809030d02070303091718030a02130c091a0307080603030901140c071a070201030e0604260c01021909080705091f050612010302031b030a03 75
    0x10156071007908080c0e41030b03030005d007400c0706400c00b40024111a402902c055002c1e115413500d0a04850181e00020700ca8080b801c040c42c103000800941d5006580035005c100e0416035200210703400101005504d824101c900700c562a02c407a50348424003803884444518038071a5004020800050381c4000048c99840312000000c15a404404400e0b00c0018554100301d601103a8041502015440c00000e540309078010f956044498450909050300ca10892800c2c9001600300c186040c0f007100d0b40001010400c4002080301c0385580e4841040c00c080d0804a0300d121100c000040c240195a414010000c01c02d00040282c59942000e54072061910026405100d100030003905104900010405980241810500039540c0e103510013002400101315a0210b4081000d005001c00c1c14a400170300b0720150780380582070f910b407a00e8403a10038404d07003e031482e035074041d03242d040b0049100d458000c040c0503840351041102d141035040d441003600304809511407884401c5400c5d003410690b070700003403038644541c1c040c2000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 601788705 1250 601787455 601787503
    0x204050d1b1701090b070c0f031103040f080102040e0a0c1704020a15030212100602100b120115061d0a0b0a02010902060406090f17120a090905010b09041508 69
    0xc041c1421258040c484001102e00080b111003010b4211541281c8070700c500805c65a5410010b642501d00e0000c068184d0041126410001e030003101c809061100c1641100d050a03a1400750081e44542a080301a040e5004a010084201c242e14055001100d00c84244080410a10000c00103001408008860720030b201c003180c15500c40e030390381002401000740b002d140701150090180c042e6125201c0412a840110300140c0070500c40001e0509070348045d8050807040ca0322825007005410312244060340300c0c001c82c0550b94282c009101d01e401e60ba0078141c04440b03603481c00c6000707001d004402014a030300c040c102d1041c42c40c84d56803103840310580e042045020340318205d5000481c0101201d03200250820800103000c20840d4204070a01c080700c00260f510041240c86414080b50201002c1d0005510f0b800300c00c51016103e5000c003c2e240440c0b0301d01d0b041508aa44894a0094510a80c0720007011000040d5410381d500705806a5a0b411018101c440e02d0207250540c941d03a9510b0850840319101940000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 601789955 1250 601788705 601788743
    0x14010e0d0c03031e061e14060c0f06160f03061a030403051b1f02070c052206031a060301020c0a02092805060118030b45100204050d 58
    0xb0001c0700741200c031114440895035003d50b2000384640d00810300741c1c0061441d00c1445040070340c6c0b0102546c5c04000700b4900d40c04c030501444810b0308400c5100c0000c0c052000310022480c1f0400c169071040110800d615050303189482c000d0004c20b003d214200130141400c02c103021900e8583e41462050559441c01d903034a5a41e030804a80a000e41c61079400e40121402c003803004003500140911080c81101c000d80380044414030903004034820b0030002880b01d8918813040100380b030f040b240c0ca4030409440a01c15200010400014100c0c0c050f034004807940a241d4200040822103141c04a91200d0154021807605654000465491340b100720f0080c4600381000001e10305011100d1050390150760300d04220280c0b00c40f91100000340c08200da540340040c82c0d98110003d41855010200c0c100c9070495500d00729a102c80010140d01c0542e00c1030000c14422040741d5604030741c001c1000316501461410540700c10040310310001d0600320500ba21241c41030040c0b00034881942d030100088103255020664000e40302050103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 601791205 1250 601789955 601789961
    0x51002120706020c0109030f020607090302180403030612120318020d110a0906060801141807110a08120613022b0b060c030a030f02070b070f0c0b100314010e0d0c0303 73
    0x51103d149501b4680e0701c81c1055040000c20701c66402076001c1d903555548140080f14644094880a58000c43c0c2c1c90b06201a1020901226003040c001d1801003251522150b100c944410b51103401c9410500c0421048446640b500c551000b4003445c0c013800051222540006500d84003440b005020f501004200c03094580d41c192410009040b0350354244045540d400018240190034410a407070482d100800c034205103410000b07a44100b801981c00041a02d68520403108055810020b002c188201548080800c21010140413003403d12070680d025817820a061141c0040c0e0701000010180c01400580000e03e41400d81c0c002c002c1c1002003030105181462408070282c001c00c03001a41064001903560300d501c1000c00200340a040ca07850902c042560b2521800480c451610054150f000c0f00f404940c506201c0c80082c03c090050b85402c0304403400719250a00b2000007036070790288480d0a400b04208000355580100030003a002002040300000585000381c0314818698100108824070501e002014000d0b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 601792455 1250 601791205 601791217
    0x708061509070c140304030303050c07030c0305030405070909060603021804030905010e010c06060f05151c0f0b120303090d17060105030c0c060a02090a051009090b120303090105040c05100212070602 87
    0x400c04c0c0300904900641c00340c0360f030310a0000342c000a05080001d54842601c4003141c04086c2e243d41c0308060051203480803200341c1c101500c212102d000348400051101c0290180150300b0740541c80014036203265204001400c103003e50054000f4400c42c04001c0429042a0842c08651007800c0c403e4a0746a61230048070b41200e01c01c4010300040c0b400b0404501000c3c240c45120903103000380d40c517403908562400b407001180101e9210400d1031b9001d401d54041c0c0001030300080d1030103844007000b1800b03048180003c2ca0f110180380d00d81d9440c0c1d1001c0100a10040200414a5061130908240d000036034042c41c280703507280340100102e05008000020078020340383c090856855000e8a000e84000e410300c428428080d5000d200c04900c18001030001185a2401816222010140f52103e8803454034160f00b80001c4c10000307140640c0071841c80202c00486105000451160380d031031000251034602807800d0303806901c4a402007800b684030304c95540034280d00090840300083d44031a54035100c0040303181c00d101030302c616 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 601793705 1250 601792455 601792463
    0x9060903060a1b020307150b06091f1803020603041112030406030e060f010e2e0603140f04020d0305160215070c0608130f05120310080708061509070c 66
    0x14010408184142d9104030302520101500c245a1070f1074403812640c84c003603103401800303014002c11580322913407043c5d01c1000001005000070b030810304240c00090207101c0024004400c9010349005d14501603000c5032601840c005043d174188840d0441d00071031410700004200070081303604524024150341e100384a051003001188200d9903160b49510009000d0003107120b195105100e01d2000c1203040c940a8002d40c141c030014084204c1c540d5441c2000b152031680320b0b10099582500c4005d0262612440030307600050302560310b001c00d0b0103041c05804030150304014208075102620400b4000145d503000100c40c501c542500d002c680300c2e12241c80411105441380f100a500502c400c042e1100290040c003d05131141c000e4021a11059640405444000341255034489000100c456080001c11841c01407420034065801c9882c2085141204d00c0035510035030301c465001c08080003c105580f410092400a809200c0c0984840d0820402d841d6080c0d004180c0d00e4131600c00301e8001180d80303101b4822942447c0d08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 601794955 1250 601793705 601793713
    0x402160c0315050604141f1a090306090c010507081c020a080915040c0b0d150e011a090306011211030607080a150b090405100e0a0b04050603010b090a0209060903 71
    0x140b840c0220b44030000c14845040703503081c0703000600d44d072509108040c01e150660301c110105546400391038150f480405052081040310320004078441210b911502036403590f001c0b01f07035502c5011408042c03600d0700040c015070b0150311000510859907070100c2a078564641c00740e11141c8900e042404503009442c009404420a840464446455548400c000340a004400141c8404401840b01a104408200c0c1c0140400c01040d104100700350306840200030070381c401074001884000c02c4030002c00540e4654484100f10301100010b0000c110341c00702600c500c0845c4450f140c0f800358080c01282c0c46170b90510450011142c41070043c0700703001c9030b6080e480c00000d008043e02e0305454140c1020340007980076540341c44640e14161000c44001e80b00c0d0418015196480304050500c060202040040c200040c00451078400c0d00c2400a1401900d001d0503004d00c103a28400300c0c0e800238100501c0119240184a18801ea0500e002883c0320b454500c2900c1e00300c0140f00015945480150100d4501d2098403c06505842 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 601796205 1250 601794955 601794959
    0x11030c030c0a20030a110d020d0507140901181a03030d06060311040e010510050405030a052a0622120c090507033e0f070b0105030f07050402160c 64
    0x8002c205a46003a02c642100954140001c040200c1400720501454050b44001d0354900030a4400000d40020710008000e520300d418580d010914000117020100c4059002a40c1409036049804000c0f00c1c10b101031381c0300314140d032501103244800d00010740d20a071202c0d514490007061007501520f44500502c06000c03250788080b65080d060003007102c0d11401c800240780c1980003207400d44520480e02103a01000811034264200310400c0421001501010b050203410080082c0e262810702c101b102446c000d0010300388c08450440e008190b02c030b10188990440c200c008564415030b03241419904e9424240345404041160701040d601240c001c0c1c2c002004155004415400f00700d0a683c01c0010346400c00c90502581d01c60240542c1543d00e08910044142d03950741c03400d400f0440310aa8100b0b0642883c0b001c0e40181000b02d0640340035444401d80181700b00d000518002070000d5100c826005050503001016400c0d5010364180d1114018001c13640f02d141c0000740203c04071040411694015008084090415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 601797455 1250 601796205 601796227
    0x2030a02090114090703020f0a0e18070903050d090608070804032304050406080705090103080f0909040f0605061f2f010b2b120201020d05040303021b0f0d11030c03 72
    0x2e200f400030901c02e00031000020034040c130038000c0c0ca0b086458000382d2810421224000d441e0382c04445007950301301c5860906c2c1c03800280d0005206015050303a0b118040c0081c1541400c90030111143ca0000500542c42420081c40e50302140065000b0241d26084100352078900e030813609000310340010340c1c0303401d11407002074400c5044200a10450360211000c011156031380d00d4203500e0780064401c2c00c3d403101e8807000410100d03010100904030020451b0805142104540c001a02400203a80584451012600d10400c00c9480e109054102204460345c108001c003c1c070342802d0003e41008120704222038031421001200038a01000c44813501c02180145405014001c14001c010040700c1e14410032444c05103d8403032083c0c558503a900c25070721099406c041001c0d25080550503078030320f0400031990b08004040707401e811489010301840c469940980d40708081400b6802c040202c0c0648502030b00504a01c258421000502c0652900907003802054050b902141605500801208682d103020004402c4400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 601798561 1106 601797455 601797479
    0x70305060a0806040503070b01170d1d0312030f010b030702030703230706090606080f0a0605060f0604030c1e0b1b01020405040e03070c080303160c02030a020901 71
    0x350b07241542841d104085500340c80c5038002183e0101000b00054030b0300d00412652003c07000803c080100141c031100b481c94003c0501c00d00780a80d214800300030700003220350800101074a101c0c0d42c0d02c1d81040c039168412248400000054400031401103803000030f40340520f460394001d50500700c0350354094540000b001c040004900d520b108822045e1401030003022540e10134040402c00c2151454400d054031000d80005900f03070030114080d296100006904410030740c00c002c0200707103602c030000800d690b00c0407240c4251b0850000180401031000040740710048a807640045070900100c52a141c50018042c0a00d155840e0200000c81c0c03210b03c5024180c0704030209100044c9003031382d0307400060115070b0340341040b110f203810100b40f003c02c0c0007601503003000404510b805940f452422103041219003075410318110500451030425400c0d074504028445d0040da01a018004958542c481c14180c = true := by decide +kernel

theorem cover : BRFrame.Cov 601618705 601798561 := by
  have h0 := BRFrame.cov_init 601618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 601618705 ≤ n) (h2 : n < 601798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
