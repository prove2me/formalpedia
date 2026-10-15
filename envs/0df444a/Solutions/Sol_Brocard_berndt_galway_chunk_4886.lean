-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4886
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:03:29.887826+00:00
-- url     : https://prove2.me/submissions/35799f26-2727-496f-bb94-5f9a4dd3ba42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 878597122 ≤ n < 878776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 878598372 1250 878597122 878597141
    0x9030e040c05090d261c050a090206090d030207170a1202030304031b11130515010509010e1207030506090303191a01030f090b1302010e0306010303141b161503 70
    0x311343d407088a0300d07030901c6902d41004203801d2000f0140385031800c0d03002400a240483c21540309094946100e541002101c0000c2c00d002141d50400c1d1200c0003507034400c01a21614072045900446c4c503101c0b4a02a4602019a402540140c41c000d502d81e55400c800f144620714140501d07035a900d2060628422601c03807104480c001c0100e0a400380300200055903001e030000d4284903803042c603121144c201c00170b44d811204081404c0d1043d240c0c0200300e59030050700302d00e0510810a00b070075820300c8800d60007c3c050f0810110a140901525134003411491020081c02000f90341001c1a2106402c040030000d41300c0d401151484041c0c001002240c01082d41403207000040d4941c442c20a203003802c054011001303095080c107212a21a00e503961103011030700c800d00040c050070040400c0f000c84045440003400030006103040e103209410030001040840c2c1c010407c40e80e01005040310319610300c10401019110101101707450003500c144004810110394a00c4d1380301c150f84064654000022454a04405840700c40300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 878599622 1250 878598372 878598379
    0x301050a0c0810050114030411041104140d0825020d0303020405120303090601030b250f02010b060315010c021f0c020901081b0f0a03210801080f07030b0a0603020409030e040c0509 79
    0x1b44242c0111004201035a00f05200d0082403061000c00301c0080c1c1070300c40021540701e40d01e400042c201700c88001c050080190400581c2c15529200c800e8660300000c0c0103607135200e200303c0d10507410380d03001005094903400700d20741c020b044009051075810014001d4129028043c06070030651003c0200c01c00000a8900c51070403100185400c1c1e00b9542d8100083d130b130250000354003103025650b640c0440038001800401c0b803803595960f07400c03050440f4020b003510f0f500c0458130b004031003c00a01c4071803001a824a80e0a03007007030801800c502c00034400301d88100f126181e603120000311400c045200c1c0340c0c420314219103a0700860b408501d80c0d07210802e441d2504038036014100c020505d81114006030616140e0210781e041c0060000c503803255640c8440146a14200040c140d031045010401d100541100010b03000d840d40d00d004242a510950240396108980d00000c0c00c00d4481c000091016000c030b8110b540a1540500241300081c1140b4010700f8103284894818403450030b084800c3e100034410340c00e4070101c62000703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 878600872 1250 878599622 878599637
    0xb04020f09160507030e0303120403120207080405100212030a050907050909060a051b040f090608031306030207060b060c0c01110120073e0301090206070b0a0b0301050a0c08100501 79
    0x842c181c03110b6010340811024001801c000b4515a641031025203000e8513070b007910640a24240c90014410341d00f29500222280c814000c0310701048148080d2410b450041c0c41001101003650400e03450400600d0042503814800406c000d05440d0030f0b00014028020203045881084d140c50800c080614100d0b011200c99022400051081e07030700781c22071900901c81a1140c80d4982110100f403040350700c682c000804081580c0e1081000100d241b00d8540102a007102550030000010503420114945220b20410503801003440000d100899016075142d0f07100a202e9940c441864080507142c2c490231000c14085a4500c02061404906010320100380710101100504c0c0051150028180c1c2c200071300503a80310b00c0c0f140c0682441d0705003031b2844000c450b4004844039049103296403404a85003001d201e80c02a4102090140140c50740c00549400307079444030600da00740d601c0f46007903001003251508456041d801d040030b01c658800300d684030385a044440d43d01d4404541c5c0d07190401e84400710320b101e16400241803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 878602122 1250 878600872 878600911
    0xa03021c060b030f07080c0607050d140d14160306151d0303070605100902071a0a090b010f06111f05040f170405010f030b090601050903070b070b04020f09 68
    0x1110031080200e44035900002d00e031190200824a4841882c0c000081648403903002d100c840350412070244a10f9080355107510b403c40990312186c40c3d100500300c9005022120b84141c8a002115040d5240c0d0303071511008110805a8901004c0c03510340070380300b0340b01c1402088440000f8a209000c0c00701504c040c016026030600302c15000307c0e28518100445518a0700880a800290303030700307200400d2001c1c082e00700130409081440c42035050210950060300745520400c00100010481301040c001c8140c00da410003000d40c0c0d5414480050608100d00403c1c100c0740c00004142c0e92a0a00004203440c000d030385400349440404a01540ca00005c0e002c00d141c0b42c0d2070b046503020428160040d07a840b41c42401046d50000b050f58580409184241c0801000c500129041c00365503404090241c1f250482e2038248002c5074180c01055400c0000b901146c10000d0000da1002191400c01201000300354903010180d0f034106504180c1100d42c0151000c901c503292035803030103c80e454100300c582d00030a4140c03a400c854010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 878603372 1250 878602122 878602159
    0x5070f0312021c0b01030501121104180210170109060f030b04060b030d020106030201082d04020303190309020f04020304030503150301060f0e04060524060c100203130b060a0302 78
    0x20341c04039064040d020048031841d071100364048a0b120103550004244c42452000150641c0d02c141c00c40000150190100004140b480907400c42411041d540020b022840c00010241140d140307802a403c011181640d5801c40d61003003c6204001c4160240c3d140342c0d03240c27000542517401d5840f0344080400c209d242400030419110340306802921a410006000c08000046401d041c103021544000d0b035903030700c410400c0d0358000780c01c1544400a080408040c0300303078840ca40284c5407145900c001060f0504001021034500300704842c040c1c00c110706070160b0740c3d807829002005012012022070082c0d0100c3c9141100d400d060090702d0240307916881d00c6086a94411840000000050031280e15640752030000540194080300000a0080d1352140b2040e032600f804d2982c01c2d14000342c8180c90b2405080d01c3c0700e504100400300e1290002046075502c0c2e0b130754511a0200d2a21744040090302c54180b00000b40a2003200c6003003210b58285c420343d80d20405944000070444801c0c040c0c8001380d00480e000003802100716 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 878604622 1250 878603372 878603387
    0x216050d03030f0f060e1b070b0a0902040906020328060e13060b130501061107050a0b0906040509180f060606160515070e0307050913020d1703040f1205070f03 70
    0x152603500040d03814510f1540390250303026035001c1c21811500c1b41c140840c4096001180c508881c03d000b07070615022541e5aa8880c11600408610314169a0351220045607520703044145040c2d00803006545a040081282009000b10700300907a890b1100189400d200c42c3d12b000301e80484038180d03107085540c0d88040d6000100e0303486103400c6a01315680c40181070b041d40d4420280b1902c0540d2031002580c0c0d0304144024082c2d103050412800c0e1507003c10000c120b5951212803000a4a1207803100d282c480090b400070802030302594000580c050404000c10038092440080d0441803034030b84044640d00c003918100300b500d4480c10750340640c100038200a080c20a14240701c151801d00c0c454000c03610003000c50207412054030170a8515000107001d21480d010b4514041084801904044131204842c0c14075240d8809490141d420007030186c0e900c0c11030141030208441e40590381e01040c0401903601d16203440d00d00d020000300c0900b219001c0001c05489407491107503007a07072842d9911211031401041c0c02e03182a0f0303945 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 878605872 1250 878604622 878604641
    0x10020304090504030827100b040e06130203010b1207031101171f09150e1b0a02010e100606021005040813060c0c1a0f0a020c04020c0d0216050d0303 65
    0x1440208000a03500c85584034041c8104d0007a5100641c5041c01200e12402901141c85203200d0f0981a00038408004041007510141c0410240012031480c01c02c0410080c00155411403528081c60302001501030b01140c040741790f14400c40007044842046e80030031442007030103603504c9956404964140001942a02c00418801050501c1c0c09c00600060520300204004c0754003c0d601e240004103400c20400001c0300c04c01370440b0403c140185030004d0f0102d6210200c0384202d1858406241c04604036040031000142c004004e0f00560b6070f40c800c00080640a0044240d1104c0144a401d00c0390b42c803060308c2d104e04000c1d01c030140d0140400082020320a40a444041e0054510b00800c011001110310075078120802800b03d40c540c021701580c1428220340c802070310751154030b4007002c184a00c001254040100d900403800c1000440d210800944100e00c6d00280039a06070f00706100103101b041c1e503500028900c0ca094031a90868041004d960034045508100c2c1c890540c101d242845441c001034000c0d007100c0c2c0034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 878607122 1250 878605872 878605877
    0x3051c081b0c1504060c0e0102030c120304110604080d0e031c0507020f10120608030a0f0c080705011409161a160203060109050f07050301030804060806032e0606180510 74
    0x9100100f88201c4040d42a81c0c00c42e4501e40d907600e0071040540003a0030400454090000e1801c00340051200b81c1c450955000704401981c0c00800241001a03004e0120400782c5c0c041c000c1600d5580344c0c0e4025560712030780007680c00440d50311501c03220300e0f00e0001810351440c0710010720f0381000401204180c0355034000c0c000481e0301c00701c0880104078a445451800800a500c0e81c4d51310242c2102015080455915402c0f01d480c60b042040060110351f00034103c41c07041d0010f4640400c4441042c01e00c1d0402c1e0040e10302c000c256500344540e00c6002000c0001583c0560300d004181d8040203c002d0002201100c18407542c41c122203200c0241001c2e01c000409090700c4208032105811100d5a5400281444400d03044007100954078414030600789a0400c01ca9803040041c1000c508d95411034680c02014011841036108200105002032120f403400d00020164400e407025909840d20080940c005090003092288080c40c40c044001501910880c010700d164076040714904015410301082c0815080f03400c600109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 878608372 1250 878607122 878607133
    0x1015090c03091a0703141509090a0515040c0801021c020c030408071509060c150f0204090203090a030f090506030f0402040209030a050706080f010b1b0f0703051c081b0c 74
    0x45080c400003100f905103040403001d4146050403010342161200b120341001c0e0403920080154001606110549140d42241c9001c2640d88030388245240c46102d08000b00395002d4141a600110000544c4600592142a000e000192100754103802c034040c441085044e2024500480d42e00a001c0d8010542c104074036094070718064031000840c2c036002280c0d0140d80030305510358020842603032003442c1c030000e0000c900c7c004807801a2900c0361a0660311102101132296510030396048030a40d0b41d4100c1d0010000101c05645134a8075144846d2a45850a0300f035000c40c0d40500c19080c0248940340d0501a14001802c482c15074032410010240100021300813030f0459402c100103e07580e0303010007021000e0340c8514000d003c01410300c00c00a242050141425002580503001849114160b505032103000003920316001003001d11850480c035014041404203200d0059a1010080c0900810392411404204618418100d41000b049070103120803950318405565003a07186818085c400c00910040414504840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 878609622 1250 878608372 878608391
    0x6121014060405060f0a03140703140d080106030506030717030f0724050609060906041e060618080d110703060218281a0f1306021015090c03 62
    0x18125011041588050801402003100624260280740d03444801501d5041d00d076008900803802c42115404024025244080d08420a040400443c401180c010003034031045428113411944480780602d203080080d48c1d0740b0010400e5030085c05140c0c0900c8000e001048003519090217141da040c0c014580c50300300d00080114400b00c01869001e416001d0040340e00000303a94101c0c14040c182212000c24294140c1030070f04200c0c240c0c0e2881c0c01c8c0e0b58040d00640b0030b03200c1c1d95103a000040c01010000c480292010102c5150380030000b2580c04482603a81c0d03600d402c000d01d0003a00400f81441b42512510203194480800b284005100f651100109a082070480f40000e03160340c4c0328130581c0c02001c10805001c0722000c01259904e01a941c1111100440b00f05028441e000303524014100c40170300520300300c1d800c90b1610b405808802000c41d901058450300841d1903009040c61040459418400d0200501c40c1e655807500030703c034522916103158410919109845d2038180000301030510090b401c000d150740c444d04079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 878610872 1250 878609622 878609653
    0xd0c06061d06010f030509060c0f07020901030b07030608190f080d060b180f0d110d1b05040b1008160c02060d06080105130b0a110c07030c031a0c030612 67
    0x80750850036800c121900307494888001090010348150000401d4100b006000403058040391003034200e05000071107640c4441500a0440030f22800030000c0d000307545100008180032503409030f00d005000d0b0382e0b000c2c00078541d40c034017141c2e80309203461010240213000741c4014000b400210014148070700ca91074a0b402c106a0b03018a0045441c02e07800071040e107030005800e0800100c1e207072102c1c8400c08100c8050150341d45d010041144180401c50051040e040880d030b126450b034543c000040040da000d130100d200c00711200d400215550301440340030300a40c10100083c0207403074002494041a040c955480c02195550000b000b404915450903c0610121001e4640540c40300002070900c458008800300da2585044600340c03c592000340342100380801c0040c035030002401440d589402c58a200750110328182840009012403207a09500c0601d8410700100008000031640c210040320301a18a101c0c10b52285945a02d201e801141d034035000c8001000010f601d8980300144881e109045000c880c04c3c07805a484d0b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 878612122 1250 878610872 878610899
    0x90b0f0d0b18090a0c091109130204090c110106090c081306060b030129041a0d0b040219080c0a1b05100f15090612170f03040f02040b01030b030d0c0606 67
    0x580c0711907080084d203803080c8030081c8815801881c04800070003e1603442c2211400c4c0303004152080b44070b16080010240701c81160340507180a4004150b041106d11007050340948144048a11501c3d55400d011002030300000500c41e0207803403007480d100e1700590f039184000f200682e166544110b441940e101c8000c200c000c282070195010748000f00f2080120155003010940302d00c2181d14910184000304000d0004402400c030002c40301600d10242c070b44072248a0744070030143c58204406034200381f0210b84203a8401403809805070924a41d00c0d082038685526a29000c00c1c4500880c401c041215544007604000d40311412500d114000c1d41983c90b0540c0d921007080c1541d01c0314a200c075119071181b42c1c12514040f1020360314010081c00b40e04014075450109030b80c030890600b64000d010f015204a460800402c508111340e20342c280540c40316030f64a000e203040542001e6000082e4040c500d8681d0180c40e55000340b2a862a1601c02002041c204c401c4210460b10f54a02c42c1c011075000b500e4000015101d0100d640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 878613372 1250 878612122 878612131
    0xa0512180a1d10271a01090506070c0506070321060608060616061a010207050a03050703060209190b03040b1503070b09060c33040b060d02010c1203090201090b0f0d0b18 74
    0x2100911101e507610850140e0700d4011110000c5c810240300301c4160703038110760a181182c009585040d19072225081c2040015115444550050b41c00244a07040540c4044100304004100b40c0707042074505203c60781d400301c480394041c140204e902000426000e18020300504811605c0b411448030110071982c6120980d80c1c091070b100700300004400c082103a5030f01441140003070501034504640003461500c0301c0340d841403a0700c006022964001240c0000e910b83c1920032051140854240145c00d507504c184041c20b07401113509852005150000c07854150901900441c4800020003c2050ba820035000501c6644505880b99000a0030881802c5040d0706110480130f00f80d01c0a501c80514403250f803111610f0418850024940e50f401d4100400903845424181c1c00080035500e00314880e406100503149850700314400b4064a02c00c003000907402c2e82c160010b05281d4401ea0300c112810b035441241c01c1090042800039002c6036802c0c0001410b0711040d43c4407640200c0d000304001d03036060704101651152801580d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 878614622 1250 878613372 878613419
    0x1b020d03030b03010c05120c030703090209010314150903092b0c1403010c05043b070201060b2b090204110706150510080402030a0512180a1d10 63
    0x15942d442a140a1289121404c030030706045140c029446041c510b8214000c0040000100100124001520a9025102c1c0a40c042c050b004070f035869040011164204000e40705081c890b0301c2050502d000c030180c0c0f56020708121401076080881ea0707001c0144222400100707440e103500c541e0b0316100c0c1c800c0c4041c1c403407001801014107202d0f090030b01d1480d54440e10309036200f50080e810030300c2011251b0343c420b0498080f152603103202048074040d500d241801c2480c2e201a12600000200c00c0e12003c2c2ca11948540100d1458000300b2001d03945018120141c054051008816841d1400d016a80e00c0c2074841c41100f644040780000d5445295400101250305821100340305400109030301c810010203219007070aa030401320401a01c00c2c44d110005100c00c1c8024410003c02c00f0134000b06085440030401030b8030303596000d020303101015804561651690040c900c40f2414010388100801141400c43c98007058900d0544040c0f0041044000c0d510000c130040c0011294401c0d210300000d00c2c0d014a20007240d44407002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 878615872 1250 878614622 878614631
    0x1b0f031e01061709010606050708030c0c030a1d104503050706030614040b120f0616140405040221010602100e15060f2707031d0a02011b020d0303 64
    0x11144107021010007066029130f60700d440001d1150a40107002c0d112110b0340024060340d680e035001d50b811040d005090840c8401c0c4408500740300419000886038000c103a02b80038070084440000100455480008031044c04104c2d501c0401d27000c000903c50003903500d206081c0d00d440724800c41400c03001c0c250b0440d2011020240c04c45080c0304108082c043c000040c4000d1030148021800d0094101d0440d001c198080d1189545070100180c0f40c4544c0d40000f4801c40e6841600d000d041341003c86611905d08030b9520100d0f251030044014010f02800811040c0422941568101420001840000d601180083d0b2010310b003605ca00d1510295040050301902c3c2980c00703040d0700f9410904000c25120410250513054008c00390200903001e490380350a40c0a4011610340040d201c0c1400131034680c460400c402002c41c0040c102844081c00e0b100021401b910040e6020002202d0040001001000700d20003143c50390060024400591b2042035208155414031b42142000c0f4500c2d03000460300862294100c001c00d484 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 878617122 1250 878615872 878615897
    0x190509011d06010905160f050306011205160806010c0503030a090f02090709050301051e060f04110a35070806181305011508030906031003050102071a1b0f031e0106 72
    0x900500e90001306c0b554030240e00c028000b8014000d0000c0003840b80410a007c400159031303a00c154040340507140c10741c000704460308091991400c0380d00a4500c81c0c01259120300441c00d2544601c40d20003030b0a80080140d41140c5030403508101a1400c40c07015501000c0500441000d65102d402d080d008145079120a02d8044c03602042c5070940b07100030300d99802408280004d440302c0e03503080b0a0717651050040354403038441486280080c0041155602011000380c000c11007903d80c54000c102c8000040200320b03d01c10005114007250112091aa802c1daa51a1242c0200d99100e00644003d900154000c3c940011400d01018804241a003201d1007040c8a03803205091081c00350a10a41e00358802c000c80c4145041d060644481d030300d10607414024082e2100000240202861003800c5001c4c540c800000d5540708140c0c10001c030f42c40100b0980841c2810240d0200321191103c0b400324442c062845030203401c000e00300701c00c11107682000b01014803104018105400912100f2420b902801d15901c4002400301e5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 878618372 1250 878617122 878617139
    0x9090c0319060b01051908070315060306060206100b0a1b0510140f07050301140609131508011e0c0e090408130b09150c030d141e190509011d0601 64
    0x3c0190383c1d2030610034100841c4d503c5207139400c5640003410307680c1442d9440d5280c1080031002461088440481e03049681000f00c1e840da41500010115500e80e422910b1f262100c4076101080405841a00e00211082040e000d096014402900d0180d102040602c000302841e2074041c00c10300c5490036011402c1c1c0e0785452440002c100e03502d0343e030406007004241c0014640804003400d24071040c01000d040d01454880c4054a5441c00f04030303002e0f00409440c281c03400c5090300c0000090b0201400540726005444008603614130144103000c8204001100441154449540000200b01d41c2003e2030411100300c240c504643c4540c4141c900541c4907040440e5115468901242c1418064115000340c0c801007103440321039130340c0152002c00d503001c00900c02d0780c0d520700d500698074500c500d001ea0790202e03040c00c229248070f003129528a0f1007110030769040e0b113030040c1c10702c1403001c44002211841169190070030250710380591b80c0e005962001c111000050144070f4070001c464001e08462440310141d100c3c0c0014005040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 878619622 1250 878618372 878618381
    0x16080a0203071d03070503031b060c070b0610030b0d0c1401050405090f2a0c0111040305060f0604150905060f0307030510110d110c0c010f090509090c031906 69
    0x140000c600354140450000c0c03181e902000c500346800c3d94a00e0380a0b4980e418049a40200402004c60760ba44d14071101d42c0590712500d6150004a000d41800a00d280b24144111a0340b00e03403000a43d1290380d540f0081041510200e101d041c1059926221080c40e03807101e03845000140c1c01008020712903880c12a44c05060b00c1e00d15846c504122084c0700401c42a04d61401340c5402071541040300d840c66443c2c01609440607c1c40500100e1034800c080040014541d41e4024180010428000d00c041001e9002105aa104d6841700600300d03402040080c800304140303074103660080343c02000850f064429071140302071044241c20542583d640c0703106015880c980600300c5d2022200c00d401802c1403d02c1c503182c054550440304d06880070b2945580091003e20b0200080f0382d240c02d56480200941540c05146041a40001c84a41000d2145c14000b10807913016420010842a803555010040c0d410300040c02038240c0c01030900c0411388104035485000e50303000c2c495664160042d10380c1c15902e000c0c034140a02901c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 878620872 1250 878619622 878619631
    0x1906090b0a11071106160c0e090115060507020127050f0f0102280611040e15030d0e040204030f111f02060f090c1201020d0c090b1902070e1608 63
    0xc0d468084000e661100180c25609041d820031043c130103200303003040402c1070fa00c1040c9076207841c403a511000c00100607040c0d1100054554012542c0c0150303807100403c500702d034003085070036600703080800c0700300301440c49140180400351061401d0790002d41900c06509290703203000c00448a503070f0386d00000e10240c00e0800000d0400c2d00d04807030000c0711485800010f91109076856040f0300847e01d03118020f10785440010040c22144d8411020040d00b07840940081064025000b80d481080042c40480c858038545131260103004401005001031048c0000b09a850310042949150083d130280400404641900c1e0149550350041801140c17080300b960400c0f5074140c2840d80980c241390794a00c01070b03000d81e001070071300d42c0300440f402190b40b151100d210aa240605458049500210b600d08030001080f06402918440c501490140030004403030345c0c01c0d40d800030035009000c010320081c025058156905400382d14901c02c1030064030101900c42a120078142c208440721100e1240b4101d1000b100b5034803200b0b19510 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 878622122 1250 878620872 878620891
    0x21e0405011811070812060a080a0818190608100306050a021905030121021219060b010f020303061302040b031e010e04081e16030206100b030106201906090b 69
    0xc000c11039442040303c2c041e102c2e8050300010b91400041017915407998608c094054031040302c2e0486032510744860b40f0340c058088640c0003051004055590306260041000c2e0fa010002c08440450502a04403400c1600800d489901c0010340000000f181c02445203a00940ca0304c2c5e405030b500d1070450806803041182071898001c0007c104010024030202441001e41540b14114070521004103000080100007240205c41d09070240704021280e2090b4280d0005401d0320584d02840200429001940c403c10640d001c08050382080001a0403858081c8010625101840300141420740307601c03020080b42c000310b481070003061407a026008468440c3c0320341c1c1d00504165442510b140340c9583c0707070321090250601d4040e92582c0040340c00c03103004d100400d8032140009040c0d400ba074180c03171b410025034500007607442c0f8854003103144001c5201c22114040340d058030501d44920311209444c0050ba6002841126045d03100c1c022603020201d2182c080c03805c1d40344140101ca001c035074402d1504003404a4034001e040d86c1300317 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 878623372 1250 878622122 878622127
    0x925031b03081b0a02040501081e0705061b011b05031801060f050d060e011514030d050901051312080d1b14210103061d0c0607021e0405011811 63
    0x3801c80b1080b198882c0d001c00d1125100400440c1103813503c000068020f42c4642400c00100780801c00240f282c0d070341182c0f5103004c03020304070550209483d0342c02402040d801040800085403100c5085207441c6c14107910740000164034640300c000d14083c00407010340c0d00000302c3c00001d001c00010102ca8007403441c01040e00030803180b4507010304840e40c4010b6105290003840095600e10900c00550300c0349940110020007841000c0a150b18480c0c0c1d40c0042c0201071041314203101d00b00042c1800101004c43e444a0b0f283d043c5030594080054996070410507040d4034402c00004080303003070203440445480d003e2107508a25190640f0701c103840182c90000340c2c01503050100b40480200258003a80d5151070b032802c1030816507224270050380100490f6140cd8400150700d0940000001c1203180d0344000400d401c01080c03411071220070100c1c0c2d80c9031042020341550141041c08018058500403254540b072200026508121079590b90110742901c1c8241c2c019010130040e0b28002442c65000d001d52007a030700b64201803030f1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 878624622 1250 878623372 878623379
    0x30a0203030f0c0c0a0f050102120703020405011421190608010906060815040209100503070f090b010c200604030204090506060a08070513020c01021b03090118030b0406050925031b 79
    0x1962800403035170140080d4070413550791085c07040c00c2d411690a000c0064400240d494014400740c060750261180a000950741d01c2220203c0c984501902c0d10801c09074001440c1001c603011009807000301501307414580408641d00c2c0001c2c92103100700d40080000780c001207440c00c4c00f4102002110225400185c2540120802800c21804038400c9039110ba4111038405180c3c48441c0100c200303c42030b410407901407044810220b41c016922420200326000c040301442402501c0c001100d4140d0803d10003003440e81100310700303030a810881406265145001c0c14180c02d007a520b0300010142d9a0050301510940c00400c00c1c0512410491200c8000c1c0410f0802060b00ca03180c500441c030400e00401c0d0840d540c40d40030400c110050000e404903a0552442d07207504010346801c004491b140c4e8046046a400306108000c008042c0c0020b04140c2e044940041c40a04650344075110b000180000400009841c01212180b00d4000f09929181030f20a10f00f01c12441c40030f00314608550b407100c1d0444524503042000e04d041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 878625872 1250 878624622 878624647
    0x309070807030c42091703130603020f040603090609152405060706020d2a11070f0b0a0903140d030b030307020d030c031101020301060314061005040b07030908030a0203030f0c 77
    0x1e0318130b0407414162810f084124808695000d100c1d004000081e01e2051180392002d030000c09007100c800310981c8007154654034502a412442070003120381c2d601509002c00c00c049406035226003841d6010f590049001d0100395100000b60a48566080740f6a64401070100b04807070005461320001c101c01101180f284c100400900b20740036801b001800c0980000350329042414682142e140f564000721441441a0a549071800712002c005c000d0002882c8610300c0701c0c4c3c0100000d614022251310b04a060b0103981001d0107100294060603104050206181000000684c07551025102c00181000b0f04209503000f43c004003542c9110b03050500ca544107100c800c001d0b1307996040349034100d641070400c60381d105100c0c03030280c8842c0c00c0e00c003000300a54404000021400e405030449040105008c0b0301100c0c6580308020001950030501c030200008405010034010414034200030070009000e400d04001541d9240185891070f840240c0c0400181c00120900490010050380d01c2d400410281101c0d040002c5000c40c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 878627122 1250 878625872 878625959
    0x1803080318070803040602280b010b0a0e150d0f0920030715021612240b060c0a110d110405130519150e10020309070807030c 55
    0x1101041541060164081c80041181c800140b00010a0b071303403100da840704041d445207080c1e0100d044045c3c0d5060316044102500019042081c0d2080401d141642806650409500300100700000d0141c100003100b015078600700d45004046400c0700700ea40d2001508001400d449141c0b0541c400c03941402e900c08001081e40b1000042d41b04e400c89104024181000000d15240c120303449a2840034a421184144076804211554201c5520450a8095544003d4001e1441c281403014104030b40c500191822456144885c01c0c042070782400c00706d11031307500b40c00203030300780c0e01c0701e08443c1c0300341d00055080c020006104032584140000300d60341320001e6141d81b58441e01c1500010340c1441550b0706c600003203d201c004e01c15010510740181c1140c26111210840d2440b0f004080230a481b030b0360b50091108400206070040710890704a0b48054810b2131480c411200113500003a294107294014060b000c070340d000f402c005210081d4055048100c84500c0c00350286031503a1031a0031340007600086007802c002040304405 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 878628372 1250 878627122 878627131
    0x2010c090506071b06031407050c0a020d0212031c050603070f090902030a0c0e060102010e032106060909240d0209041514130b0c04030b04020918060c03010618030803 73
    0x500c9070740c402c6245880300741c1e0b103c5040c00b00450407a603400403410540c1a40251f0000a03d9145020715441e081810744032070048841020150744045e201b0401428600c03c02100d0b90310240c902d0304070040c1220f4007825a000840406444580100f12410003501401540d8110609401418405003001c4124440c1c5a02d400741e0f60420b6121450001151010401d40181540203d40c0248480d140c0c0300c401e0500405481c2e5600560130246c0203500b45002008031000590307442da614112400c04003403c4498540101040e5010909200a19072912540200c40c414070540c4107000e03204103244080311001444248182c0100b01c81891440140ca40b8600b1a402c503401c038003c03901d605800d00541c0003801100c003440092103882c200340400d100701494030750f520610940d450140b580c0d401e100906140154400542000c0070740000c1009070400200c01608007000344403801c0002e048409551030200166000015038400000410881f9030180c20000c400c3c0000c10500c00080c6140c8990789980405070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 878629622 1250 878628372 878628379
    0x3010b100507390303030f1a0d02030114070206040c1a25020d050303101205061308121e09010c021015080f010b1c0803070c0627021002010c0905 64
    0x8030310400703c1e401032540030018841ca580143c804460320404100c00840c0d884110082030170404411649407103805004404c1c00240000110191898200100503142c0d51050b038141d5a0345004034052440c1ca006184100203d8004001e2802c003403901030003100b02a488480345820031560b905031000c0d40c8088a8060000b0708489103c52902604000c8410342031000a40c0204c2184a0030100030001c03004e188101d589c004841100f40d078075002c00c28101e00d1444000c00d22703000b0780005a1b0710840704200685090041000c903050941d18a0405215407060707904140c002105510381e00d80b01280740f01e080c0d100d0b01c00c500a00c0140303541400690f807980000e98984143c1d4840c90400a82004240244002c00090f0b08070343c0800740c11041c0c3d60080411200182c0288085450a00100b582d00c04c2c10072026400150189580c0da581000c03030f10740e084150304840c805e480d81680340784604840c41c03c1c528083c6e100b11004d0400b41c24810455540160b26543c2c0075a414510074041d03442d0009032000c103d403800d0303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 878630872 1250 878629622 878629643
    0x1050f0123090111030a0201090b010602010608031207050f0d050411180727090b0405070e0315060a030c140f03010605241308061f0b04092004080c03010b100507 71
    0x42d070060b1401c00f000041540148004941004000c0d415048241c05601500b0005080c0e6280c680403400c1e9045400b0304c000c50340c02045001c0c8180c4100360f0302903000905140040c1001c5084104070040d510018081d00f8240c2c64a05010900203605040d00c54800119480d10f03640340014036402c24490000e00a1003032061541480d078a225800c0000c1c01c0545a20444400080d00d0740030380300003004c01c0c44181d805640b0b004006600640070314041c00e0001001030081030743c854050403038103400340010409038019004100010005e84540840d00161040c06010681d42d5070140038040506802d11070305201e81c2c1458010455034655100d898848d10680700d041000162544400070503210b0700340012440c01413650000340e00403010421b1802145c42900d016401c0180b840c580c2ca03c01e4943c015200b8034103003081700304a540d24650121305400a0591126120f610b491450b801540055000500e01c0e009442e1050780e40c503083c46014032a5104031410584d01c00d1040c401885c0c0c1c064080000c0404910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 878632122 1250 878630872 878630887
    0xe04050907050621010b0408031c0204051e180f01180b0a0f1d070504090b030c101d09010b071101020a12050405100203030f0a0f11030f01050f0123 65
    0x1d010580240c9070281c40e80c4d40d10004820f1103801c0808580c0d0480802c0c0c00e0a00221b106002c0000701c0b800c48400038011402c05006485905104a100c00d90f210f440d030b401c00002a00d80c45080200c504942d400a00396200400c1c0402d11500600c1d41400502d000502804c20a64005042640381502c94403401c0c10f404502c07031300e445030040c20500311842d40002c24010010300c08000350700b25400d4890310020642c411940d40b03072001201805030b030b5110101d04148070620000c0c400c2d900200000a0081c00c41e10b401c0d40350404248145400780d03040001a100c0035050702c036031014000c800400401500d0b8000b40303616000340c20383d15016000b002012044800c08224141e03100700646200107804c0302100d00c081d840080050856481032007254000c004204115424074004016070b0300c1482000351100040d51001d41c840c00410480d0020305803541d592803c5101c00c80048040c0d0321400c84410501015410701040052840308103000300e040144850f10390084c080031040074400a05c06481280c3c5030604c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 878633372 1250 878632122 878632141
    0x9050d152c0703060e0327010507023c010c020402070c0509180613120f1e0503011d010305210405060712110c010906082e03030809030a0e0405 63
    0x95200101600795484220100900011074040200e0344103100800502d501405036039224081c14550070401585104d0906d010070003c1000e52520005140041c9000f1603980080d441400e81d06d108500c0c8072a8625800708291107008a0002000c95040d11442e600132000003040d45c601414001d02464000c141802040805900d80010300801032107202e103841c1c4141c00010b80e61013066820040d210f030310045095445160595945030350841003603261460099420348006036070307111080400020948000c7d204858038202c10411025684040c0d07203515003040503904607800c042d0028030040e00001040051000100344420f440050003803141c00f13a0f010402d00450181390311807504001e0005002c0c080120b83c15601c6002c034050b0701d8aa0803008800c00595450310903900080c080354a003413080c032a4600458074558404400c1c000c503860401880851141100384c1215800a8019400113108064100c0d0005611202d000d0045d802d0591200c00180b552207400c5e46e0900450ba20b2011036071280 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 878634622 1250 878633372 878633411
    0xe0109020f1c2607031d0105040b04061b1b26070e0c071209030218091218030703050708120c0a1103010e0714120705030a080a0908060901090309050d15 67
    0x100400261303d849440c1006031400400704800040d15044031a80180c5600800c01d9800341c80500103030340d0410781442016104034070103a04054000310300d141c0c0b400000d081080340c0040c010740c550b42c03004404c0c0b401c0070b110720ac601e26008040d120034843e09540d1094400291103021a4070410902c002070700c460307083d5641072190a0000e0200c20408560076070041d00200c150040307030310980b2859601560a800c80c11b00d0103003610108e000d50404c2501c0400896840083e004043c1991141191840100d000900d01401c81d0700c00c03542500004010015400b0500c4041c0142481d02d241d20700e0030f222007103041c1d10380340c45100c01401c0605541c40c6100544095210b81e2002c0d0201c0215070390039450b1240d00f001910781668103842102d86040004070b00300d010801c0340844802400408551007190b030b072080c542d004581c141080003001d07200029843d0f410030025000381d0510000048111a5042c0200f080c0341c41c0e0800c0b4040c0920b40350310340004002401045403122000e1000511441a021800071a03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 878635872 1250 878634622 878634683
    0x150c04120b10060c0c3b04021c03020a26030a1a060405330712030f050c030612070b070c0f08061009020a020304090e0109020f1c 57
    0xa8080304100c81046a41031695000d00c51038031090700b0031661030b00110340440130303800e0060489899040411038401e540003107100d1100c807441c240c081c0340304242103400b480f454561181301080b40030040c0010360401203028070918407080242a82494030b80c80c041d64580440d400100350381e11402c0345208404108541011002803094019a6800e0090060700a00100703000c101c1c4003c2d07042007108207450700f001260704652000d0503c02c08118404a00c001c40440300ca02880d28034800d8141c08145401d40004100603845001c1890a1a440c004e00030704855944c2c0c06000e4a5107414243f203505054803050325031004044800c080035880200310603003810a90351184d03d20b09004944e850410a081c0f10010990750407442c001107007642c600e50b0302c1e0341c2c010940d03001201040e00e050a018134101600149900143c40c011039203400e03510754206040b1000740d1078915850b55a483c00e9000c5284c00b010b2100900000c940114503441c032031001007040085081c008081c90304480b42d1940c012031148090001c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 878637122 1250 878635872 878635889
    0x1116061e05061915030504060e0a0803040c090501120b100302041e052a0a02010b21150402031c03090b09062e14010507020d060204090e0f150c04 64
    0x148090602500c01808064501c684030342c0401c080d400100c4041503464040f01d03000b5010b100440c41a1606500811001d081032300c078280c403041300b5078031038000f0011210500e02c95907030907503285480c1c02c2c04c640c800642c0e082120014105001000b2441c242c03000c500300c240d00003002074910780305c81c0d80d0011035400940c40290014145040304400c070450007a6040d01c215980300c14029503a8840c10001050a9608102003c0b050010072200c60b60b50040a0320380b108250000140300c4e00c040e00022507041c50075807100314980600203c01039901c402d200c45a201d0b454030500001e54201a400261201011601c00f003c80c0407984032403810300d10136001b5421598000030744000c9070404101c0c090302d540045a1502081d404610035242c445000221983e500c84041c41405e02507042c5040035646000350243c00d81040002c3c064040035a4442a02c0d0350390030f2080c2001030b5624a0240c4c4c040c251100c8070381c00c0900da0081550150055408140c000822900361503659990351808028030103800303541c200e81070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 878638372 1250 878637122 878637161
    0x306010e220b0414060d0311100e010507030b0d1203050c040b040b070b07080f04061e0e100c030c1202070302120307020d090b09065404111606 63
    0x140701059902414141905030340500c503110f00071100f10001c0806980080e0007100b56503901020038410384821351022400f8082e160f02003903c0300440107a0f80340d00006207440e559001440855a01446200d0590304251055195400c0c180c40d82c0341d1b8251603081e8002410384640000b2858424902141d0181c03521000454980f0b485640c402d40541089004480c01865800442c50260003a044c0d544962003000402c8065999940c0b214042c1480780400507001d20032010040c411a07181c082c109800d80c5003001041445482131024040d075401c0b201880a241c6421045043c06074402014100f41d034280001681c0c582e0a45000ca2415616250790a4040700200031b1000c0d869010a420f1900c000554441c1280c50300e40d00b480441d480361040140c0e00000400c02001e054540d4420182c0c214800c1003440c6c0e21003034181119410741100d4803038428161841c01127031250120b140c10450404801d480401c01e000740501350800b580310360020a0140f202c4014184104409600404492100b007010600c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 878639622 1250 878638372 878638429
    0x141303030e03041409090102090303040605161e0b1807170a050d09030b01140f010c11100c14030c1509010f11030403020c040b01050d09080702040c09080709110306010e 74
    0x32400300040015174802c1d18198081011013105000303907a440381d0000d01135840e00d85004c409442903030103a21001101e5074070805900103d500621340e10740482d000048241440d006280c280d00c2e002d402041c6030300e10750f01481c0e89483c4450000c0c01006455240e00c0509442d01d01c02c024500c0d00302d070888014450f1050650072040141d000c003901003241e110703d42030287da0b40c1790506801da0812440009410140100c890422503101d01102000782c1d0003040c0140c0155211302c0804d0859400442d0360011a2000400304200071445982410307207800d85000c1e50820500da00409d0b1030383c141c00d0f400e403217200000d004030305021801c1d401241c11030f403081420400d1075440e04031129983c00c1150141d01501a1401c1b100c002d04041c020790b07a030b00d01c050f519103107892007518401d401800000c0c401d4900c04400e025003001600c0324410b14520640645503101d080b03140160440c50b000c0981c21500d030060030411440a01c05104c015690060800d0070400c00c20080b4a02041050300003004030f80010303440c4c08034070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 878640872 1250 878639622 878639639
    0x9071e0902031501090603020408030d0908090a06050306130501050609060a0909020304150e0307030c060c030e0610150906020604150b13050703050721050a02191110141303030e0304 80
    0x70543d64900383ca030100840e96540b0141c0417405207201d140040c1e0010809400f00002c02d47c031980c1694440c84007681007103d0f01000c40c5142c80d45801c035601142001042c03102c030b4584010300c4403401c580c10380d007807002e5030404002c54101d00410301d41c0760040e07502081c0440300700d00400000c00505210002191245402c1c2492900308075400c40310071a680c503082c4030410500e000b004840742540c05442d61074800d42e8640e280c90060100010650805960303100c0d942d00c400d401d0114602030b1800c2c4204104450500c45840c0c40301c02803040343c00c140036601208005080e008103105a006801c210000c007880c40d02c54148029007054440d15501c1004035031040c07404200ba9000a00a007000e80d002c00442c4d403960030545100700124800c002560240407007804460841c2c10083d48000c007054094145032001c0b500400b80719449140c02e0114460104401c8110030802140c1000d00c4000f200784000b404407880c000c0c1a40e00035002540000340b182d400018540660803e12455080504407030b500d81e56100740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 878642122 1250 878640872 878640901
    0xd0e0d09050112060806070e032d0c01020601030b0c07020418080c07150207030620070b04050606010804021804050a1403040503010b18130c0801091a09010509071e090203 75
    0x45a01045036000003031150f50040c40303400e060324600b200408050b01c90000a43c0c106994000f070592512a03d01c0c0060780e250f074021401c00e002c82020311a8a10100d44e4001404c01c41c4669442d81154441e03001040404d0040c0d5081d0340060502c3e80e50b035513401c1e00d0b00120300545060b846280072100403601c80000c02960300000e00f0b00d8081d18058459413074031b446542c0c0107000b021001f2001a070101e8400d1001c01c20035405000145041000384040034100c00c2d040c0720740e8005200503a5007542d01002c0206101041c0080340d40f12b5024640300c0b4040c0360503800280280225040e1250a00e0f9280c000340811208001803414035801007040d12031014003c001c6a40d950260240e41e029508040110949017450b000340c0e815140340300ea0300070503036841f41b85500038410606030940d2000100c040001c0c28090a110b581061401103282040c1c9800c0c040c1d90f00c104000c090b25003490b07030385408104504c202020401a041d50661045601801d200b4540d040040d00c95412000000c3d2002041c0205c0c2a0301030130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 878643372 1250 878642122 878642129
    0xb0301180302010f0e0c2b0303091403040f09020706380303030c0403081e040609090c0e0f060a270f170c01050d0e06100e0a060f03080d0e0d09 63
    0xd0002d070841e51504000d88080c40c00006007540141204c01d047c1c503040c5a03208020311008904400b14903007500e00808140c003110243c0209946501da501804080d03918000c106035918015403a00e4500030b15004500903d00c03070302c2e039900c0e408100c40c801c101d6681c002401c0e000e400c00d00c0e07042c0140c1115450010560401140440e44000f003c210300c1c070700700030060707034819100e9104c8030341460301e140c1b11a0001e41c04034a17a40d4440750319500c8190100c510001030006440e040d51608802424101e603481161807902c4408144031041a00500561b500d03104950501400ea03002c43c0c4079298404207664a561141c040340c43c00618060408510000513890821500040318116004d59904540744406441480c80b1000f60010701143c0341e19406440242840e40806c280003600301650040941000303026a403141903200100020031805882d0340341c054220f05400c9081082d02d2520f101d40e885100c15201c01002540b0101c0c441600040360303409031186460b01015501304030b40c404d030002d196880310300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 878644622 1250 878643372 878643377
    0x20a030f1b0f030503030408180307090e1902031011040902040b0c0111120714040308042723060d06091a0a140403050d0e010204060302040f0b07020d14010b03011803 73
    0x40e00000d00404282004040f01e40103006549191100e45503202c25500610b0003260989013030014055a4030308000b010018241408001491540001402e00b0603d01c2140030360b044140c84940d50150b074000c10708140002909000080030380e92845907123024016a48500da41c1c610104000a40a1200009103d00803039000200314054883c00c5003d40c5c1e00030300c03048600090b1403100140ca1140581840d901100310010041d0906c1c0d601d51701c0c100e00c0c0c0e215800203d400701c0480b450f40c2c4184404108041c82001c150030902074220303030b00441c0240074140c40000d0001d01c42000030525a451b0303103442200e10f41d0011800c0c0102402800c10024a24054000900108584000981e08000c074881c0d0341d80030545c802e0001598440b80c030122110341044560440c4e8031740e20410608210024402040140318035100903848920702744817040d9040096005102e0701d4000c110b203100603983d54007454140e030352240c7d031a55001c0350a0301440c018507c5601c115010342ca1f04608a643d2120000007600d620b100740e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 878645872 1250 878644622 878644673
    0xa060e0105030a0f02061b10020d15230d050a0506010302091026010f1a150c10021606020d060f12111e1503010504110406050d0207020a030f 62
    0x1041490360fa02d440c0b05000d030040d50071011080c01407401600600502e607900f06030450f51192500024100041d03848220402a40010b2154114045001750309020020981164000d803030241c00308801c0803079001240000701c00301c0c1c04a94560300e078208440700c240c0040c2228402680340c40c110341c2c1d4034402c0c0030591107103888600003088803043c0c40c69074003550002361150300110883c241041301c0b013000200040855403210402e07207441c1898401d00c550441419006035a4603009414804103035041040c281c0c050f10104241007000b400052304012841400800683d1941c03100c5810781b4401c1e03000002403882d400044e651003c481c00d50060429241385610b000340c850340e640c00e120780417625041c0050142d25034460103a61407070700c0070300c004a00044842388801c100100000524080150351181d040290100050206003081e104170341d2400354040e1644d10b01820104081c00a0042c22040c1c0003083c2c0001c0c40c42d045490789110b01c0000c540c400c401807040034a62030045d190f00d950808c13150400209 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 878647122 1250 878645872 878645879
    0x3106060905061602040f0603150b01030507020f03091017010609090b040605130c090b040603050103060b010c05070b0306011e080a0c09050d0605090304050307180e0c0f0103020c010e060a060e01 85
    0x14100325629400300a4242d2600c2c2c0f1030741d092101802d01d1510170f40c21107a6800c0000003040710701c0440301d031000f205000000e601001c180003504580c805805032046600c204401e4060410000031215408001c0360100c22100c8440012211000904140110f0801e2100006089600f0151072000d0307800f4044144903552111040c0b0044801d607110b5240d200c2840c4601c19003000c01035112121090542c9044290251108910212030780b080e030211001072b641d000100148010342c4035540100d0401d2038403c002c40c20680b1103580c1e445140c0280c1c03950340301c0000810003503806501900700760340010080c481401c0340f0398005004a0130444008034103500304002010170901c100004000c1c0c843c01403c42414080b0741c1c454500500000f0704a001c948405c020110b41c60382c0c200301000c008c1c203810410a143d000b00400f041d040c0d0b88807400d0140c031940085410211070b40d8218402008c50000e107030040c0c0360780c00300340c406014104903101c24445005407000d001c01003400303400400030303a403444081c900d0326642d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 878648372 1250 878647122 878647129
    0x1119060507021e1809150c040e070c0203010e030d060e042d02092e0b0f0906041809021903020f06070f0f0b06030f0c0d020f03120d0207020f03010203060f3106060905 73
    0xb107800401002c010802807027000c0850b440c1d150003c201e4a890b012182d0180d0100303085a24581450026500201c0c00103030002c501e014030307000b400e00003503442550b0070150390301160200c000800c42a4a20b000c2c00f11441e24618015042c0501c0e0001c0151006050200ea240044104690001240c0b41d6002e050180c51034901e00c2d001c03c8440c01c040491600f1007265103402240c00280d80268000002c020018401d10000d4014006202450f03000489a08900c100710001010074844641d01d11311003030400140e9694002407407005400d41c3c46c0c55a560b01032502003001c0401c41d200801c01c0c0c0c9030403900d90912203480c01d41441018103404540d04000b0f480130304c9643e80e462154055000c007007212006c005062801c0110004c10010b4115680400c0e50950780d4030a81200c038280c40507036408501c42042d443e103480c6294040900b0b500031032540c09e003800071900078a0034003255800b540118812500714011840c00e003041c283c2d607020049410750600f03a048003800c01841104001102a60013041928 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 878649622 1250 878648372 878648413
    0x15070b04060b032d0a0f14161a030703180b06040e03040f03230d030b150304030c0f0c150e040c030c36031119060507021e1809 56
    0x2040c401c4c407071400644081c40282c2c00d4441040106940070740c44460740080c14280d51034484902c81c5050640301d00e068000c8074030b4000c040141030340e03451601c4410411200310810f0303e00510306400441c1d6607036550000a8018046c8000c02e020003d02c0445035000f84a403900406000301c208560a000501084240d1903480c01940102c0030105c0703c1500c2080011a0b2001250f8181201001111040350a40140e810f05890440e40000300b52038a90760102884c109006080303204020344024194103054a0051204241c1003000b091812107000d10024001901c112500410110814144418034600d00409642c102c0510601071070400303801181c1c0794042c2c0200c10b00003815a54201385d8611207000140c040302a840030300b4820741359440c50303207041c40c00c2022040a14059462020100054024010040c0c80303a00d8580d10204843c4081c82419408000c0781d800c0342d012540c120f4a94a60001c000c4002c0700b94007040c3e4001100c2010b1511b41030703401079a501ca0184801130344c0038140300ea407101c900706 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 878650872 1250 878649622 878649643
    0x2706040501050a0605090f0a080721120806010c080a05070308011a091005190e030616050a1101021c050603100504031704060b030604080c0d180608040215070b04060b03 74
    0x82c510082800080d1003100500a01c0030001c1030a150b1038087c0000c41c0c000c8415400083c52900f054509005100a4440b03a004040030713038941d0040c46040e515116400b001e0b040d0314000304104070010640350f0303101ea0000c40b4032903006140347e03607200d01c10000070707010b54050502240400d4114000041050b0740c00c802d800316003600c015507890900450100304608c40c00810341d2044c01000c1c03100314032512110810700d4025140b0349503a0b242c000800d04151070110018400070001100444d5500a154002c0540d04080b0850400e00e00340d081d1041c0351400f900604145c13103d4216030032440c070840c1c00e694001d1805000c1c1035040c0c811229207401441c0a4900440300030b004220354002802c07001d0fa0558503968810300a010002d4015030020000f400c02c08c00f81c9040d1002c000100311740712100024010445030b40c0050500321070300c034001c1035018418000e500c108414405c0b43c50000d802d5440307400522946400e48440580d43d00d843c0e00d81845121000e5070151050761400952110a0030300284c400705a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 878652122 1250 878650872 878650879
    0x607050313120521030106030518062e0503070e060d050312010e0a0902031c020304030b09010203060a0f0b031f031208090f0a0c0905100e010b040f05010c020f100509030111071202060601121a270604050105 90
    0xfe0f1410558041c08054020f00a190403090b61030700c91000c01c4051000c2c00b000c040050412516501d09520721403800d1010f0b1001d40d0700303071500d48040300590700003408180308a1440034000c0d03c1144613034140c0c2507000315031019007058038a008101d14910f041d070045100d010200d60b042d1100e5114031001c1e404a44600807508020320410200d4085815140300d0b4821007210f071010b00960f2f44a5640c10400c00002c614030f0b02250700a03042c8600100c061000703a844040c440000d1900c1c28590310381802241191150840d99130391000410242c680e900c600901421251003596000c0d40d448440e0103040d40b1500c6000c0070030480d00740c003140c10b41c45417064110698000b0a20a1603244503010880321500040c6214140a400c000e088002c0d2801e00882416503104100300b6160005410301e282c1282c00342c41c1840464001c142080039036a0400d541d02c07842600260002890f803c400c4210700800b00c10b10142b90722901c205940a0340350242030341070000701c05c2240c2000c1c8a0302d9603024801594406c0c010240d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 878653372 1250 878652122 878652133
    0x703090c0e0c160f0638120d0807080907050108040311010f1a0420071407050a0f061704030e0607050313120521030106030518062e0503 60
    0x111450710511a9000300050051502d4403000c1400c2c14488001d00004070781124011801c507051045a200d04540d0791001c03e191086402c055805c50480c4003541c46010900b640001c080b540f5450b0100050240d00a480446000e00786e40d60001d40380c80c104075020310000300b201000600b9000d01140480407200103071100e54030798032213a405540002041c40d0804607596501e200401a00c0035004241c880e041c2c8a03e0305a400d8075000c188030664032402982101d05119074408890850024122014a0380042541d090124a41c45039414080c0d5648110b03800005840b020070f60114110524040341c038a0307203c4a403000d174948050b000010048030042c01050f4640c240480c141041c0008000151042040d01c2c600442031131241481c510f60b4001d102c92041c40c81c40030040100400c4150801494103900d521400300940e2005500e100c140103c0041644410100b0070000f0b0b00401014004036010aa034943c3c9825400b01050f080b07019000c0030030f450094040702075665810a04400d80703401501070304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 878654622 1250 878653372 878653379
    0xe07030c1706030307170a0905060309210f040902130503010e070915091505090c030f0105040902040f020a0c03030b120a080915070506060a05010302090603180c100c05060703090c 79
    0x201c0c2900c010b001c50b81500003081000c0002e4040070f2142813440c4540d1900342c548000d18801017250103241c010341d004110030800c0c0000c1c0700b0001860003d02000341d41098030b07815180c0150156000303110500e008240c012502043d4004a90042c110004581c4280c1c200340d50781e00d080500741d07004400720840c0e0b40c000c0e6034148201e881680140070343c00e203000a065205030352102c14400300d802d5000c0d1625402c02000c1c007400a803800203829500001082e04448c11418444078221243c14103102d1035208a607500e04000441d00c543e00550704000824204546441c101813001c0d1140038042c02c100d00082c50034518042501e03094654550b5000c1000050140c0c0c8000c3c3d84034441076020b000803644c4011034040d41300200d080c00d070007000d005100d0000781c405402c0c202c041c0040b081041c0c01c410b040c1030040c0140b40081d159030068070740c0860380e40f0003a003142c401c441c24103080c0002c01c1c4245800121101480a04a800c80300c07400c1103500c03550031100259036404085048802d02080208202d51012080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 878655872 1250 878654622 878654657
    0xa0b011e0926060106080f130501390f0c0b040507080d2703081204060f020d150e09030316050c0303101707080d0c140d02070e07030c 59
    0x109140c103500d052042019845500120307480c0340c41104512124004819a00340b9502440154014006410321104c0741c20300c0300102040c550300030b080c00caa104064142100344602500701303001070f07201c4d480b13661030200e8224040030081091000b600c50810907030908644240c4101041503116059170380d48003266a1350382d0344540454000d0415240d80c030500c400420b07101e800784884001c40c425030301c444869034485000307203881000501a04101d1079a000040010412040c2241c0700342c042400c0c000559500c03858440300400840c1081d5a03040e1000c6401000403441d17500a24100c240b001c103c0c0c0502c0e50711103000a035020704071901c10440d0030078008602607075500c1d030340c540c0d116107031303081484c10302e406840700d036286030030403104601c8a045580d402c0011203070481201d48821101c8002c4c0140e2803c002e1140d81d200d00c82c030300050400800c08810350a010031159182226a4403078180c4441e1050f08800a6588816015015501c1071030b4000c5032115000c0e01c03130a4240c450304d494040010f02c918011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 878657122 1250 878655872 878655917
    0xf01080601091206060504060b091009140405041b030804060201390c0501050403020604030e06120c0c0102090a030f111816110109030c1509110603060f1509090a0b01 73
    0x80b113082c0e895081c08181903680340181406404800c000c15211056502040b604110900ca01002d10404180034480d9110040c205000b4400945001c109030722075113010071031800317040d01c902c2c00c00c0c1c8015004410007503240001c0c070131548154002e1142e58400349010482d2060b01150011b0300c054580303824041503000031120300240042c10252551040c540300e682c07d6a004a900b2001038001c1c1081104054200400101c043c2d01a00d0b900d00304044aa8488445100030741824114034011032a128502000d4040300c0c62070102030f01451160390341f8a0030020007181d1082c01c5824118264a101041c2040541191001c1000300c0880c0c868070b41c0c802c0c4008420a9240100400c1400040143d0b5280309006a8041c0c521030350390480c0007205801c0c044a134064580c2500001802c0c0411000070030071105941b54035402c201d91540d900d848280c0043c0710105400101070f00810703081040078001d00d4803c080c05120a060b0f40700300c0d4940d038003495801226004058940410210f484011880702180b10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 878658372 1250 878657122 878657159
    0x1c17070f0f12261f050a12050d0503010305030904240f1701091e0201020106030b0c0307031b0905010e0607051e011a09070309020a0512030c15101a12010f03020f0108060109 76
    0x20040003c4d0785600104000f801c194201030251012074903044100481000742091042d01480d0442c195410f5a550b19282e10912450b1071186846004003040c0b42c008074466503e06180089000c900f655a034000c110304103c0d0b10480840c4070301e0f2014203004520601a0981031640902012001542c1e0300050b0424240304000340c0c1150740e10301b400301c0090441610203009202420600342c0b2464600701c000c0a40300842c40740042c0c0da1010590402886d008414281503907000d007000f014281451002c1000c074012044060036501c240c42803080340880a00081d174441c1402002440030503000b420021005a050450070f4001d1505400907a52501c00e034441c01400384018050200c45542c2e000085210102a150080d90b0b0130008540c3c4020f40104a946002c2c0e50750101c00d02c40c0d2800c0201000980240c1c4a809020144a460044000a0341088544c403400c4074654a1321940c4441960348a03c0c141d0000300d006880d440002c400315802504a03030700c07410b41691485140381c10980007500001c0040d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 878659622 1250 878658372 878658421
    0x906050c010609090c181a040e0a0501180210020d0507120516050606040c09080a02010503092b0f03020c0601060e030a1502091c17070f0f1226 63
    0x70008074598030306002d114400c5016100d10b1200342c2c10903418460b14003044646441d410b1a0091f0081741109015008503860804c54000907000441c118480c100414104c00a00b0340d40713450341c003044c01c4040c4000b80c41403a000380d0381158007004128040c0c1e41e0707005110038000400d500703000610006024020901810000d03103006400d24600c1c060030a0742c50b0a2101c00c03595508201e0401481d420241305210080510303292411410341340001b29616810001800b80c10040000001020b5640412462401c5088103901070a204081c800c13045050f9654240f560000b0310f44502403c082e807090081c0c541942210b000b501c510303482e2030825118110302007500c036014005c075203204001ca035102480e000c201c00b200c0c40244e6110110302c03c0044c41142c03402640b2040c4051891140420f11117060240508104003086650b1407203402e00c030a6460404c80002c00d085440c40340c80c020801000030504004e9915264aa0f9076440344081404041d00c822900602c030b07a0030b4000882c0054091110440d25440b803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 878660872 1250 878659622 878659631
    0x6090619091e03120e0c01090b07020105040f1205010b09040203030a031a030d0801140d0c031101050d050108100f0c0c030e21030307090911090f030c132702010906050c01 75
    0x51604084a20702c0400a502044002d107a04030344810600686030504038030000740c20308040079800680764000e64010a9510b0340b020a2400440e401803044802030305c1244542180b6a0399140782d5002118450780458281d400d014580c9080c0c02d0082a05001b15401005117040600c3c0c0c04040700144002038800c60036840c075400c3c120a07600d007404244144080d0707a645c90341e5981000f5082e5510001d040c02c0d01e02809102041c4804140301c042813400303403940011556442f010101c0100d030304d4010500c080080781e01d007000005560700000340c882094501008103200702c21807800001d0480b440c001e80040814003910747c2c0f0300001d104000040124078018059145c880b1059181000041600e914640943c40002484440c6400030810001040440020322403240154542c550a0040c400c02c00d00a0301e59601d040001e940c01d000c081c02d00000606241c08801c070030222000034042c10321405e80840315410f00030324069030320110b1291a50301a103a8940c42c518052041720154880000c40b6119541c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 878662122 1250 878660872 878660903
    0xf0c0e071409040f2c0d0918110406051207140a0309060e3c0d050d09021003020a180b040501141209030405040c03150306020912030d0e0609061909 65
    0x18801d010740014505c41001002980042440700c4194110450f42d40b036000800b000100c80d44600d580e000d980d0b02d4421407000c0c1b00303c4d20040d405003400040302c00100502107408150640c3c41806000304080700d004010003501c445070191109202c0305051941d440f4100042034603035010740c018609252083d54006003407030118040720300300b1000c415401020284016540c01c1c121030198540c0c0000b070301983e80e50007032002d007a030190380d4101ca0600c5810300c50301080700769407108c865011a10300e0f600988103800b42c5e07d47c00c0004000394001e40c185800318230303100481003401140b526080c05541ca5800510b02e4030341818019154083c40ea51203024020081064000a54000c400540030b122800011900e070f606102c200010307a110001c0d080c0426140c4510301c10040c4484aa41c42243c0e044071006076105105400b042052040e1540a11644000603440c0b540390015803100c844040c070402603d0440e1070b0351403540d890318400e035101c0394100b51840d5401042c0c400c40e886111001d110303580d180506201c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 878663372 1250 878662122 878662151
    0x19021c0509070602010e0d120b0f04150f090605030a0816050a030306060f1704141612020a0f060503040311010b09040b100e011d220f0c0e07140904 65
    0x30112440d840503001120100480f64090140481d15619200030341004e1030000002060303042c08a0030600ca4540f00c4400303480c252640381740c000308208094010302c805190401620b40041c090b00c02c21101c0c1740d41000004013210302c1c0c4101d00a580d801006410542054cc0315010030350841550380001f46440001070001460400400c0ca0326482918085000c615100340078001604004000c02441280201c21014248075111280e00070307031103681e8650380128003228914045040100c044420180c04011036818140d0309204a2107200b03c5400307800035169541102d58481c14410900421014404100001d002e00107680010203c80d00001c1c01080324000110301181c1500c0503541c464030202031206422030045140017904814000c01450351400d2540e80350500684000f100400031600480c0182803440081c01501d03d8400134000000001d0408030203d003180041101d5425048200050301054030b011544280c500b41c81c0c0c04020000390500400e59481185c00319030041da0340300703059050350 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 878664622 1250 878663372 878663381
    0x905070f0e01210509072606010e010e0c280e280b1605070e0105040f060b0a05070503090a080312010f0503060a24090b0a0905010e18071503021305040519021c 70
    0x20f90805403405038846245a0340d05205041cac0003101110424001844044000c401c0d0b65080700303900000994603100c0705203e44042083e45044090a81c01c040200e401e1984160b9150091004844d40c100303c00c182030500780890001210300d40544042141004210f941c0e401810000d04c072900c0105030945c443e52200e0400129400042e464010700300140075a04041c4941d0025089d00042080300c6030030074058151500500c05040c04002000030810304001080c82920b42c100b1010b0204411203840b100034035240c0d042000c4883c1e821281c0b100000b4a90440180a02200c4025010b0179450b1200041c21000d00906d07410300d4010a98224101a0180d482c00380f2401004031030710000d4081a80000c10010064980c4000005800d010051264440390300780035400a07442244500072403ca80c2c0c001341031003204c0d880080740c00300c1e04800500c0207070541c00401488000b400702040e595100c40800088074001d46d10081d424070f1141c281e040c90280e5038020100c010440b4900c401d00380306a401d000554 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 878665872 1250 878664622 878664659
    0xb060d050f030c0105180d080402100504170615090114090a230103150902090c22030503030a0b0a260715050408060703140f040305040905070f0e0121050907 69
    0x1360340d40c20400000c0f42280700542e0600030004058810718003a00c500078100d09014101a10078810044946a024082c0048500400c1501d18181c10b0091290319a0b45071101199205102403080d40540490720780407400d20b05940700301c00740880c580e21700814000b00580040c2280074565039100d46a01c03149003411114030304900c10741f50503003940c15031600c82c407611000b41100140c0b40c2440d02e103d0060b913405032000e80c4911f00340c8032161500402d442d9000814049c000c1c00a4070101203a0102c14040040000c1d0f20500c080c520910401030000d00340303c0e41c44503d114003540802550b00800226405800310002c5003d108100d174100d603250307140c1101c40d54820300c4a034041180014104418003081c04002e501400300c1c102000340da440081101c1c01044000c00400c0300c5404100042c007058012401d81e00600030000007001203180440c0041c0003403d281d211040400d00d100034590707040d840740c040c06003204000d10018001151480c41240a0b042c0a0400907881c050001c01044900c035803218810700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 878667122 1250 878665872 878665897
    0xd0f0b04060e06010e12070e0c070c080a140a1e020f090c0403050106211205070b04240923120a0203041508060d030e040b040510050117040b060d050f03 67
    0x2103042250024240030b514802c0680200e215020506c25004085002d100702d9003102030404040d51001313070044180c85010002014940151004a00004009800022540b003a601040074548005080d03a8811880400400185003181040001412240c0c208405407000d03201d150090340342d0b0000703080d40208440b600031510020408006004090040c00300a20000c09110041c0e100640050400c00d18228060040c15401c07001c0040c0c03620500c212a020b44d04001e401c1e2480c14540341c404842c07180e059416140400220050307002e03460f24814034a245501c60b4102c0700e003005c0002e007160250706003180d404060040d0390304804107001d000c0c010107403844154045c6545506048542c24141d4030a2504410081400200705d11900d40003c00c19105415007090f000001c0e00c01c0c00100600a114407035074100d424030301801802d03100920600c00762042601d58040090074002d02500300b400480e0301900c58040d0801050301070a102039010200d5025005580440c0c0205180610716070111020684 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 878668372 1250 878667122 878667149
    0x303150f09043c03080c0c03030a09020103060b030906040b0603030c0303130309062604151803030e01090c050f0a0806040c030507060c1211010f0608010b090c07080d0f0b0406 77
    0x625140d07400410f869030358a501080c05140100040070941c221001c024103000388900458602c1201006a469407032002e01103a682e86410072440c4050510588105d0109082041c086550003991051303d1081c0441c20080a0580d03c5407525080081c000d81460b80500003042481403c40051000398880d104411040f0034040c21841d001744640c11943c0004104184d800000d68440c040d10550800840341c420014550b44071800c11000a111107811107080302c3c034024810090401c41440b008410b402500c0800800011381e00017826641c41e10300080c25503e41800030f008074605405501080f060107000e107880c854503140040d10308142903405484000c000e410820402c101042050041c2c0100c4c5000740c4604015501d9503041e10781001c49005220380104c110416032025400594001402030007407201b543c0d80d002c124020001e090105004035422800249003a0309031003194a41c03a0300170540c0b89080e4144200d8402000d208c603a400b10107440e02d0b00b210280e035035801000c0207868480040403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 878669622 1250 878668372 878668403
    0x402010302160318141e040605040e0d03151a1c0203040c0306060b07020603060d030c021005120921160c0f09051b0a0f0e1002151005030303150f0904 66
    0x524228040d40b05441708811810380c8a21602d03000c030b5250700d90038162680c02c0146a52000103015120b00c5c0c00035074101c0e103003403214840d049000662120244460710708001c2070340410001c074801102405100305501401203451588900b5000919078001410060300d18003500d1440e80c000c0e40d0040e601a2004030718a40c060ec2444454810030000340880c0240302c0c5401416404038000b03000c0180400d00c00c4d401500c0080c24540203403014040c0f264010124413000700c4404003c5c1c0709420129541014500440028201d810009101c44078840007402d41c0e086e803440564220350350303402803601c440c40c02c8407205440005911050008003030b0000e540d051003064145280b4004030b403002001d030f643c1e1501400041068000c003074115169550f25180025940390220400c0d1032418011078281e4010040d6400700100c25404520106891403451801c000743e01c403603650300c0c60303060395000340e642c1a002003000c202104071034480340d000480c02170b20b8000716403408000102808001c45003900d007801244c4600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 878670872 1250 878669622 878669657
    0x619061103073e0d08070f0c06050a02070611030331051522021302070219031103070f0603020307091d0402100c08160203030f040603060321120504020103021603 71
    0x908101c910154120b2982e00d0000040d401c55080c14045c10600002603140d013445a01440880265040f0b81289061ba0f07449900030516400500341100600807003002240e80b605c911180d1015150320380007141903446400d00c1045d00058141442c44080844500302001c0d2440384034012010302400103041c000040b81c4558444503001440c1050304058040880414a0301c000071400c19030301a0360601c008214464a44020f00c070360f1102a501c407902c120135031071400c81e400703041c010380e071083d02c50b8a11104072005140d0780d251075010700350702051203190038000ca901c2035028552020031440c0c1a000943d80f20040e50f46c04620241c0c0d00305c218050800c00c419820301400d000c242020f03a10b005020f45526884086840c000c0c040002000e0343c0e840580c10541d41c0070400d23107108800606005684540c2c905d00600144402e2108030380d420314412011003000c0c80245103098600e50b68071010003c1140055100003060000d000f2418140c2c28080c03d409a03820011005a003482a02d41d80603c40c4441c4a6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 878672122 1250 878670872 878670953
    0x604080f03030702070f0602030d0f180b1009090206300702011505031f0e0a0b100e070509060a030e07090516120b0a05090a0f0f0f05061906110307 65
    0xc407103111b0040e41004826800011581d050141e2000000c1c80303001309280038054541602211f402d41d0f08030b00301000380448003110a00603581d1400c00008a660b03031100c0c10070348041810107503001c8028080d18242d48040c030064280f00d9520026565408620000b402d807841c0d00340c808100607035581c401c03641001c00c0d90340c0600c05000124014603a4803448041044c103c00718400080c40152903080d00b1001c42c004101042189500c00401038162415401c42e152460951203003d135402d00003c0844c0302d06003d0341c1240e0f007a25000d00003500e8900615001e4002c0c100001310004244100e50001889444134440c150042050707003020306051a0b040001002d07110341e80c0b0701041d89490005054555a1641d581204031a8283c07040441951040c5180004142d031142c000c003803d00700315503000d8001c01079200c185144641071003004a521180300740950f803580007000992060781c44d5814481c003406951110301008588003102c0c80e04003266034096104031340d0116030200c4049041d03068001e01580341c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 878673372 1250 878672122 878672129
    0x8030a0b0306180706030903050f032e0f0311030f0a1401060b0c071419030c0510050c060c0f1b0f07050306070f0c030306050607050709380604080f0303070207 70
    0x106060f441101c40c4107030352118010321a65050603941c072905802c140c054000e840e0726000340700d18540c0b02d2030a5695408240015000c1d01407807140001d03000c00c11414070122406407850f0315607035240217042d070b40c0d00150100c00c080c6240d414480d28111a80001d000c001c2022145c0c450b80000101944181d8010300b074030500d030458942c240c0c0c00d0000e0760704c200700003640e00121202c4018003512900442c01161340046544d400d014032070010000801070140b0042c40608940e41500c0c40d05a40490000468541c01106100806500b203e804101141d1101c000391100e614038030801458000c00d41e8560000c40ba100300040a550000305080301034840c01e029081c01444254080e113146c1c5403e03940101440110020301d002c2c4203600b100e90701807600ca41d00210260102034000395a80c9031034100a5500d280310311a005960b42880c0101101010000000c4e503509511850b07514110340301c2818500d48030710a0f10054100009201c00240c44808001c58075200e501300028540da41410080203003015207a80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 878674622 1250 878673372 878673391
    0x3070914010c031d010c15060303120216020f010e04090f0c08121b100c0818120d200f12150108070810030605011401021501060203032208030a0b0306 66
    0x511503010035040000310384030310201d044e03480300003d88100513a03184205843c003900040c500401104039480700c1d170001054a00a4481501e91706c84005034606a00c5626941224101100d89600060806680300000c41c81c05060440f4810355160114044070060001501d0f010106104074003807024000702c41c1c0103800088007604081c6410310f820001480380c2d1481d00b00107000241c03e0102c500741030114083c3d40c540b15106000c566980c030401000700c2000d0380d642c4022001a005581c082303400145144000c04440c2c3c0c0f0b135051404904540d00180786d000d40000c00001d0782055002014200b400401429444248860b280c40000450400c40c4c00006c0403c00800305040041040360780100784150701c100d542c0b401d01d095070389440d246814071045502c0140000e043c50008256182005040c030781e001401e03400c03100c80900e0301d900a80c14550a119410160b0030400100f440c82d40ba80c0e85135045100b17004003130346022402c2d41d940701495104a8001020b030369940d13280c40c620b14092140c10303001703480074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 878675872 1250 878674622 878674637
    0xa02130b010e10030b03010c0c1110210b04090501090512160204020c0c030105070e1305010b030711030c0f010603030923040f06081e06010803040b0f0715020307091401 74
    0xe00042c2034841011441445200c05420003000d161094200b5500d0050140003480420442d0030b010703004840c16901164101c00800b0b85c0001401c4c40845003c040d1415a290141c0d0001c6540c1102c184410311028441903807540b030100300c1078949000ba088124818800040c000005091043c02c1c60740c4601c542040712001c20885080e090310582c4145030580449005a40300c0d0072900710340c50044840f1100f60154203100c20440f1441d044016880be400040c0c84180103d0842d5040200301c038802d018070501e9003c240080303101d01d07120300c414100c00d45a6030112454403041094043c41c0000303002c04002981c1d102d00701801050f500010b01c000800380c041501580c45518140302c022200b6000805014070740d034198281c000300990f04000c000307250420a58039241e918900c44054040c085429240c20320030340000050f550000070480301281e208251087c24036464aa00307115036407000f0f5003030780c404c503400c1c0003a00c1c075554900c01940500d2880d10b48130382c11842d10030041c1100c40a06805418042203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 878677122 1250 878675872 878675891
    0xf1302030d0f1116294e0c090102071401050705030f0405150901170402130204031a0c070c12080d061e0e07050d1d030412031b0201050a0c050f0f0a0213 67
    0x1001580d441b455012000070008400d1000300f8400076402d1001d40f070805880804c600b16122158428034004c1d103c060200c41c03960380081d503c12500c0b54170741c4070380141e21101e810442180c00e8070310000b071460145003035490003a86460701303403071078000f40c030450018007001604000e14a0200c94031418400b265031007600b401c1c400e0001904035001010540340307506d1800000380465441d01c01a00e00c040b2144009c5403219124100a101074240d00441d0f04000c0b401c0021442d003155840503682120340c0500e1495115041007001c1c00810900350044401c10380034040b48030f4516450143c80042c3c1081680e80722005000c00d0548400031441c2d00c5240c1e1551fa000c01c1c032040542c0310342164403006480e17001080000003000d8201c0301a802903039024482c0000306021412000301070303610509500942d1048805004108801211654900c009000c0b80d4100b0404141c01c7c0103501c80e0703180c1c90040f42603450403a00010702604101d01c0c10b1810f1050340000090204514050003000341560002d0800c1244122 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 878678372 1250 878677122 878677199
    0x5090111340305070b1503031b070b04082e020d0905100c050405100207120503070c08060c120726160201060e01090905240f1302030d0f1116 62
    0x203190300944982c1140002451404131408646c44490001e0216940d8080d014034035043d4a4441c1c003440b134540504200081e410072200b040c0c40564000401400b41c22030081c03051103100001400c9506030303420324203046000801e54400340243c04452440814494883e00d4141c1c10200d4410108241078a4519507181c2240d00c80300780c40035150300396204110300b40c1405069140c007000754004105007001400c81070030402c0100c0a0501c4903c00c1d180074034256200c001c0c4a0300c616049440d4000a00244204140384161440ca2170f0400d140d403c101a581d20310183c00e9101c0b4071201c54488205140714180203100d1a03008544540600c40d200030081c103414140040c1a450061080450705501c1d440382e02c0174004244928041c0161076002d0252002130b400c10311964000c104c42c0d10803404481400200350384401110311a40950044c00f80202849500c42034594820417203000082007441030031136421050400024514a1418809415a611300403005041c2603404130205ca60070a40714880740c2540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 878679622 1250 878678372 878678377
    0xe06070b1b090d08090a08071802070212011b1b0308060906180a0603110d020d030311041a0705010e0c06040b0f131502010b03061905090111340305 65
    0x46070304180030240d604003121071a4a000d00d0742801d0b40103100c0034100301000001c00040c01007500580f21952015500c0910355143d40f0640703d80045521900305c505101101c5500600c40580300a00511801d15111449401c40c1c110310100c00251035206014140642c00100302a880350041c003c0d40f40c041011754000740100005040d0500030401790010988550750170b03c1c50460380040c0100c5109a144c1204000c01412452000303484020300fa2080c0200ba09142d000b00808039000fa044000200d000d607402c4000303011034010f85070703030310428003010030400d12500610304078805071613840d44c6403082c0b401e081e03013160030380d1010f80038960045070850b00c19194030064604440150b1803141c0c494001140c66819485800d43c041810407040c5004070f64500118140004030025500800c8200503030402c0c180d0398041556902c400021006450a8040c42c5400241e4003103a100c0010031001200b00c001200c542052201707020100210140304100581c40d41a404803402e80c400001400105031409051072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 878680872 1250 878679622 878679631
    0x1104081209030a080a1d040c1e110304081f0603021f171017160b0a03060b04060806120106031104091e05010c0e04060f1502101a010e06070b 62
    0x20600401d031144a580d003440007402e60360300b00c0d0302c845d40c8054030302000741502c40380c48181d1a03004c032003803480c002410903114820170760010f1348680300c1c045c004031040e44025400d2905a410081407000b46440303207000384040d10051200394010a4020f500510720b030700c000001201c1400980c42e1a00810240e604d0b03500c007034094441e6000c0ca0b40001c80c40c04080b14140e02c0b0b5214111014a48018481c001420f50445022602c14003080c6818945206203151115409007182c1900900c000c0148881d9080c8001005c3c01100c90a0009165950311142040c540203540440b01003a070a200f0000c1034140090850290b10a071002000441c5c11035036911001c071080d85419014950f80c030f14000c204040c00202e442036041e0b1082c2c2d04010710349880d10300c0c0680708040c48000014001a0f20290508040c0107402c00d9803c00040340100d107041281c00f001d205c0004003460b007180f08010416951803000c3c480d442281c441c0303c100b10209282c02c0c00140c03d00d2070f04020301d80a200c04001c44008640c2c07480c2c6540d080f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 878682122 1250 878680872 878680903
    0x50f0f030a0813121809093504031a070507110105090a09140412081b0706140a0e0f150109050a1b050405030d0503070e0f031e0a051203062103070804090c03110408 72
    0x7800204202c11622502d50050030510005000c400d0107046142c3d0401800c0da1111102f00d03945d6440100c40901501400410301044003a05000381e600600145c1030b10907014010b4511155a07a05940c2a01d4035801c3c2c1000f04840b450610050009aa800304000941d50520f200141405516071581020800c00000c290707001140c04010410281c002c0541800e84141140700e82c00c1041c1344900400340c1da181c1c0501842000300e4030806110101714114a091442001d030196880d0a4419001c0c1600510301c801103a075980a820f11100340c02c2c10001403454075501d40c2e0b159410b0000b407520303140d40424410280f15042c4100000654000404000c4040c191440c200d4181824007007885c0080254200c2a001c000310b41e10851a94006000aa014090012103e0300944400103412070300c4203440c0b403134003e0f00081011500c00402180120700100d1a8112482c2448984644049400a80003494420f49401103203000a5040c001c03900041c0000903201c1c989450003000d82c1c3da41000000100c003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 878683372 1250 878682122 878682173
    0x50a0e07050304060f050106020c0f030f03070f0206090301090f0c0911030c0a110d05070506010f0b070b13170301080c010e060a1d0a0909050f0f030a081312180909 72
    0x4210131504108000440081e051003c0d50312480040d44854106c180c0d580601c0c800c86a07440a440c000030442015084440076502d0030805494000128007100001da801c52820444603001c1d480902c6241245802100300340e41c0d0800034904140d041460340d220180c02030412646c50b20302c803c0c100450341c000c40304114441c1d940c03000d44003e4440d92001c10610342e2a0041296000143c0e07080030082004500c1201652010380c0c0340c0c5003000a24802d070080c0c0e2242c500500510b400195000302c1030f50490407040d0303200b059080598400007003010181201d01000310100c01008425010071000800f15824240158904011b40100700c01d40242c2c0c03009400c0014a031350950300007200350a1580200740150007020078548889041018114140e400ca03a244502190f02e2607024001c9001000594020b02842c9001c0011100300c42c4820b002d8140704812040d2840380c000180c0c800c071007100d60182916400b0060344100d0003102d942036654020782c0d010b800c10240c0c4000400040c03000000c5120704c1301442 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 878684622 1250 878683372 878683381
    0x501030b1f121b06110f01140103080c0f01020703020a0c091a130e1e0601060801030f0b06061210060306062f1f140c0414040507120606080907050a0e070503 69
    0x140c410000707210b401280007500e400407801c1c0b41d014913985e112110543c2280c040111000410f42211114800c4000c03a8001600500005508034010850800c10108581c81c80d1900c04007242241d121320001c8002d68404048401004800728251000300805007081190400c0e4000e40f40400500364401382c402c848440c00c40c4004203042c1d00190340403000750100c842c4002008c1c010140e59041d141d60706000d11448000164292080000328141c0e58480300c80c510441c0d02c4d91701c0c00c40c046c102909556100c142441804c0200c461014594400d462404122511500d0200090100e0300c481d008841000011121000b500520500c810514038a41c00e0b400302d6505030140050500d00c0d071552a0000303074043c400c0c546030803d1a80009060f0780510000b60740c691510104010103201e180300783c0c000094800c552300700398680341d03001310380c05602d608000f0b20109d20b658014003142d0342750b0800030100c1d01c000140326078a901041114040c0c0742c180c031800041400c200042501c414001c0c042d03010802d0000006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 878685872 1250 878684622 878684633
    0x606050d15270e0303070f0309050102190c021201020f09010e0a08031303060c050301121e1410050108010209012010060b030105010806010903030e10170a0501030b1f12 74
    0x8010300404400262a0a10701c0700c4031110004498900180c0e81407030000081e543c008070842c0c1c05102140c480080c0300c1c8511805034041c08680798251000d550174482412500c0400c076501408542554032040f0b044003604c1003001d464080f0080c458246c0c411b000350501b944440044076400b62090814068112030714000415110090f0044d411a00012400216201c0410014000c0d40d1092006000000030301c6401c40d003034082441071b44c0380b441d00c1284a4001c0b83d5000300d54541c414041c8246003c031240b940720440300151144984d4500d5010080384948400107215580c090207040b4029031070f14000382e00090074102c42640460781440100506030460f10100800600401c01c41c405000d41d0b69a108401e2a9030403d100780c5020860322800660503600c070321040801d40c0d0385500c402510101041c14801400c003106822018403003010800c1800380304002c00b140c4104015003002c07400798194901213038440c00103042c0d4299007046000180e0283d4041d800c4006503181c081c05140c18030040e0500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 878687122 1250 878685872 878685911
    0x140910140d05070e2502065b091e020a030e250806010302090609060112050f0711060402012c0418061805030702010e0402090607050708060601050f0d020a05070219180606050d 77
    0x4404103140c03010044000c418502910a140e11001c502422650741c0320907010a446c0c48032b903041128400103034248242ca0443c2e000d000c1c041a1407030300151080c00001041c2c50070b2403406400c2c1901003c0e181c0c001484540745400005009450054251782d49540d0114442c4180036100c0c900c1060314000043c440d074462060b641e0f01c00e030250030601c030500304450b101c00d0860050b5608070009030300303880d42ea451000015032a4042d60b0f041c0d40d5888005e0282c043c80d101200c100188524410560f001c2807207542c1c5500410494008140765500b9501031031809800300d54010400300050718072081d002c400b1410201c144c90b080742d020f0800a09502e0703258000340007449607054595200c0c90110b8205d040c400c0c00200c02c2e00303683d1071908403541a00c801c0d0054030346000d80c0400e640c0b101d03002c2111040400c5650040c101040c2242401824080b281e0300040c0d030030640c0d0a150aa9421300c1e003080001382185c00080c5200045888108212401c102c0000e1692084c0c04e1403411031070300c604d68903d8660b070300c801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 878688372 1250 878687122 878687221
    0x2130c0212250b0105091302030a022b031709070609290301120c06021b0103090c03170d0c030603121b020901140910140d05070e250206 60
    0x9800708480307010f103000ca030011028060300b4021040000052070140415484145a40c0c0042c000c1c01444615420454420002c1c1c0c2205007501480c4860318040d440d500168510b6403294503014400340306510b800c102d0040082600d070082e407101004228150f00407400d00213481d60310400403a4051070700e03401d908800e610615001415000000020002c0c00342a0300307030460b44a48004c00400343e40d103104a980ea52240486103082c0d48149880303c19601a0f840342c00c405118854001150343e803611898000e40c10034040e0803244400040010b0041168826000300580c641010000b0505603101c1441e01b0003039400d241d041c00344444001c0e0308d240ba1108801030060340100700020543e10340803218850780d81d140d0580d00440808021403902030f1100e60702016a29140e50031520301510380100000c1012040003550140544c903804120080e489080c0d922955403075001d0680c0d8001c503605105145403125105c42103400000c28060040c4204203c51181294489050f130790603000300d50b41c08409030801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 878689622 1250 878688372 878688427
    0x40b1303030b100c03030b010e0913050a0813080645070605042102060f071b060e09180601060302030a0b0303071101080c040303050708030c0d0903020a02130c0212 72
    0x3d21859180e50151a002e0400d02c01d60b800d010009032080159074415456403003550114403240050411080c01101c1040d50b4022011500307003110740d03100d0303403459400b100200300f04801e000070522088100308906504101c1c45d030f0480c20026421101c29a0400307112099058050003886046002908003520032a1060600180c5000030764684001d82140e11520230691410b42c41214020082401c1080031122900600304901e80644040e9603039587e8807030502280d0700708a0b2616084140700c101c501c035000c0c045903101da4a00d40780c1c0f0420040b0740c1200a18508440c03d110b04000c15807900400c1e0181120140c0c280540c032515101c00c01c1c2c01070400c82203074941600c0003103a0300c014001160404007040c00281ca40304e11303a440e881703500318103807103a40800b801140e03040100c1000250401c00840e800805203c0309424207a84144400645a0388034060700180d015400d01c105618007040c40c0780c5c40020400e0200500d03598048041e403039404641240b5500400424201059840d034000c0911008100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 878690872 1250 878689622 878689639
    0x40b130b07031e0b0a14042309010f0e0d03151a04090b0a1a0708070609060f050c181207150c03030e16050d0c080102160303050f040b1303030b 63
    0x3280c1c000e0042c4050541c84107158480510650441c00710312918081e020040c055800791030410072032100300700407071030910340150390380d04c0e107104400020700c214022103082042d05001d41000701505003980d440030442540303a0300d03200502d403a01000044401d181403050030003059a1030281507501c181c400700d034020392003c2907040280070030104c000000e0095a040240803c52901400184030241c2100c0c006d24076511040154131407400815400341c0b4a4a100da10030900c0c02c083c80d518581036031400340e03080f9002503c600503120340c86201e009a5a00c14900002682000322580f07030300c0f01c00501210b1540c0521a800010b8005280c203104510103030440100300080000c2191000b018030030200310503800a45003810000421070003241c445c0403420842c0341d600d00281894204030b5004407100d011510101d07030400000707441c002800584409400042d0040c4003120509010301a6080100224001380a100421002030089100e1030b400c2440380400700321000d00d03468217500a0907100501da92100c180f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 878692122 1250 878690872 878690881
    0x9060915040f0c0206010e0c04030b10120602030403020124060c0218180d0203040e01090c03020c070b04170105091009050a0506010f03060c05030603060a0b06070f2d0803040b130b 79
    0x46410400f040340065088513640daa80d000381c1039151000380d601c1d450400040004001003441c03413100d0740d004051411419406540e9403000b101c107604040701150b04035004000c02090640a12400400312822440c07402140140d2042c0500d44100380240800e100b041644502075480300c00000159003102c07101c10354507040a41e5001c040512000c0700301c0e114461b065540155900c04401c0e5000c40300e0001365001030340d08003440340d0040d0000c0c40c90340302059404c1c8075511080c80d0410004000f0005075800701d0f940d07814050114481010300443e810142c0c1000c00b84150040b00250740e1444102103c00091808110f103040760610000d0b41002d0007038803441001160144400c00103404503071044504210400b07428400f030700c01d40800c448099064110800103072403080c0540154091800c010907a51030980aa55104503030201c052040ea101d4030920002c45800890140542ca004620801048048a00e07601c40103903120007480102100324040105042c102481040005036a000c0510344072883c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 878693372 1250 878692122 878692151
    0x60905041b170318150703110c0102031c0911030312060315070f0e0301291804021e030c04020301080102090316061202071a09100501140906091504 65
    0x54418030002004984000290b80301140705400a0380480b00043c600700091030b03c150080300c10502c0c52a4200c201003c50903c101c3c1d01000500019100751183e81240140301201ca29161342e0950850542d8410407044400340c5110200344000d1081400100e84e1203030310320300107480000701030006070544004134483c003154070455886403047d80d040d021074075600781407a80e040d01c1c04070070380e480c8011942c4c03141c401c142644101d10070034501c6009800404d03000007100c0d9003d0b200d0fa4004400c0074610200e001d542013440e0542a0a1004140f40c58215041c24a600001e5030304a18500000204007172a001300601d0700c06120000c04414010001c544a40c0e68055141c080c0d40814801c0d8464042c0d480c0e80c4850a4900440c00c00b42c3d070050f52203414220b402c10904000b907001c18002d031980c2c08240a20081d081d83e424041780b00380050b0300541148a261040700c01640d0301038110b01c60041561002243d00e172540b6031050390152017100d81f14241d443c2c948844040806100740349400c10700340b42c030701e041600703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 878694622 1250 878693372 878693393
    0x102210108061b090603060103110301060c0b180309091807062604121214090d02060c120604020d02130f140f2139040c0c12020106090504 61
    0x40341e00703040e0342250703031920b0b0b107042140e92038141c01c1c000c400148030700742d407505003100656403064040c100020345040d088920980d03600241c1c000b1700081c0d00c2c01c01050411151407000c40d0080d403000f81180031110040300f9142c0701c0c058580064000c83c0d170200081d0070000000c05119001c80300c9426192002e844031002407840d480c070820003d00c0c200b0310f0010043c2a1202d01c070300e44940e400c20211006800c900314200c6800160340303112501c464441c60244003030b00c1c0b01100b00b40540c2d014070080030045203491020b414404020304061a1708420310600031070042d031143d0140d00440c100d07001030780d0b4115604110001e000f80514170038208200c0d0004280c95000c28944000d55482480c039001c1201b0340360801902c101da00f6101d94000000e00400d46445c8507000d280401c2441c107500b9600b4241581c014603603002400740310a64254030b00c11030082045032414540d00586410f99050002c01510341c07000d1701c100003912004000c42444a0301000c201c0c401e502800c040e1003025000e01c1103080c80c0c202240107a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 878695872 1250 878694622 878694629
    0xc1205040614060f15030604021308062212050a0507060e0c0102100e1b03031c0209011b08030609280b0f040507081305070b0307030e0c01050405130b0301022101 71
    0x384290b002140c0e0700c0c9007421202c0e90788513004080a006807070741080c4040d04e03000645066000f540a0028110ba031041104140107082e403140144000d180c03220050311040d02d480726510307080c0000d040010100e410100c0c3d0354038200c03250a2242e56071000a600301c466109aa0020f400d0514008030040c02c404042001403c10409034201c81441000715504805ca6071b0603244404540c0c0301c00010000e100400302d00e41010303007000f02500e00300740d0341c19060003c1c80038075820200c810f40e001880440e0781da0080020342c01e0080619002004c80d9080ea1680c42510025004d144211060000521800c92181c02d081c402c03444400f008071600000784d128000b9010044140307110341d04114036101241000d20600744140056a43d00f40591940354035120003c00103113007a1094003500d00c010814a002200a6000d54026034000a0348141c808803d4117107907d41042c181000004c02c03040025964102d0956a0b000d014003000448518440000340240718a04070500c160070b84000c400f5030070441d126414101e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 878697122 1250 878695872 878695901
    0xb0a1707020d201b0406030203010c080a060f120f0f12092606071b02060313050f0a02010e0402130e01060801030c0e0408040e0601030f09050d030e030313060c12050406 74
    0x1501c000c055160f16942d8a0541800b980100003658100000c0640c0052a420107000014542d80b60340220342580d4203080c1d4031000c1920b0400b4011007401c288110001004011508500d1a040c807040308130400c50400040d101e940000c0503c024454030341c41089509901c06c3c5045032520019a024250b00c10314410b10000104650940702c011117600e01099084d500c0c00064200b9a65602c4240d03211014080c107182c290300c1401080c0010f8840d10011030007007188100f00c0440800c1440e00c00c0c5007010030800480c140d00b1180c0f2500060b43c004015400b15503080302c015072590050400e03594000d01560200d0264490300e0300000d4a6038100c501c0354103890103005210311040e100c50419503206000c1d40e0040110310100010002c69070404103c42e003001c1e0524001ca58021031075002420741d0300386402038915802500c000c1802c16058400c00421000b0705010b14210b00e8901c04e079241075012100007920058403201c40040302032203010042c020042c81142008a4200f0f8201000207009502e0790008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 878698372 1250 878697122 878697137
    0x20d0c020f1002121b0c0d02010204051e012001090b0412170108060a0f020408060a060f121502030a020c1b030c060910110c030f0a120c0b010b0a1707020d 68
    0x10001868000c40b802000815607620090325401c4040000904004496120740c80900501d0700394181484800c0c00e00d0426800034be00c0700c0c05c0400700074428401d03075800350f10401d800c0504c90315a41c005051240c40805014010380521521182d140540441c0754002d10400810040004100410021002007040783e80c502004142d0341d00b022000010070b02410791568013180c001001d10141e82c11588a9203501d540150400d542c940c0000c0c07a111064403241d0b00350707855440510100d080901420002c006010010b65003441c0d030b4954480885c0010091903c041d0008001049030000d07030111000d08114104542d6020464240c1c075a8141c5c0d0400814841c0c06110040350191401c40191106050000e01da50b68a140703141084d500e02c400816142000d000f440c202d40c01c5540c042c0580880220400702400211050b49055082d0704159603401c020301455490030070108400b04038650545800345600ca03070303c03400d0740015541101d81400341c81e0440550b80800c200d142e400700710400d0014941c1c50300c03503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 878699622 1250 878698372 878698393
    0x1002100b0604061b0501180506090616050403110609151201050103020403030e040b0102160f03061104030f020d0611030a1a03010911040c140c0105061003092004020d0c020f 76
    0x541442030744030f4000010700b1541c805070305000c0c440110325414492400003480d400503600141000c3c0e410541a5100c0d000a8200700e58020188011544403c0c00caa04001a0601410280c441e004501000d482546604600c0c0a9502c17403030211601a0740003002651071300101c111903081c41d80072424071042003100e040006041d5009000356019240d060300e4001001110f8418040240b00000030350303046209801c02e0b2030300f03e40c4400680001d07010818001e1b0410781981811410380b5128040c0000141040004001140c83c041380c0050240e411116a1a10b0049040c00300107071136417041d8081414400818130134051030960252141401c03800040280c150b45c00b081500b25600604e010300710100070b10300c010f00c9103002d5004c83c10341085410035081c0e0036060092000326422800d001b0246a54520030f00c251443d00c02014165004103107028801c1ca1419610300f14806000d446961010003048510002980c8940540798480c0300000c0c1000a6005088020354801d90590098964042c0c40c074420b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 878700872 1250 878699622 878699629
    0xf100209190602100216060c0305091612031808060703020a080f0f04060e071a0405040b09091216020316030201081b0714121210050406032f1002100b 66
    0x740880300150043c1800c0d5000c54501c4001e580304044242d51042142c40ba0300020300a841000750b1044a540c001820345481400d40d4075007606a1140080001d444e4000c11540301d00d134811411390349c1c0c14500389912002001e213820900c80c01c2d030000707800c0d8001c1c60100000c07207034943e0141c4040041903452000540340c1c1c44511120070300968410800500c240005070208a0035040817815060440440e2a100d594100032099403142114182c40100300040c1000340b40340c2400b4120842d50112800c0195040614610b580d0703000fa00207017540c403030020585001c103411000c4200030b81600035060b1180314020103450700210340c4600040703010507850f2003c204800e04840c0c0c071849503000351058a00c0c01d842511a205410017084102d183c0788602c00940d4a41480352020b41140c1103010610b041c80c0c142a50400711014603600068000c1d803620f041040400c50f6541501e0000b2000d01c80703c0c8180c440c2043e6012801807410400e1740280280c1050b4000381ea0009010010048002c070800c4200041d8042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 878702122 1250 878700872 878700919
    0xb0903030415180201140c07032009060105030403110c0d0501050f2d0a060f15020715270302030102130f09020403050c1c1b15090602120901020f100209 67
    0x14401000220f0005000650003100070146d034885400030300741454004000c82e071404942c0e400c1202c4d50a075101c46084005900300c1600344185080710783c0146485c0c210002004d0b80402400034003000209580074039001024080040354001c003800c0c0c3c00100150781010703400381c0010b80706242c01d12444c1c00000c01604480000d503000360080c0c9440c00310300212440303115000b90017600820321a0b0b074a9600188414078485510010300034110f030202002a0f001002c0d0404001ea4843c020070150440300002460780301c03048031a105810291000c11154600c800c10318249540c2009401d5840017404010010b610300340ea008940641d10102c1d206601c910140081e400743d0f00c4010542e6010246007500f0b4a001d071400c10340950580c01c10b54000b1910b840d091031101c03200c003d034610380e13000300fa00f0b002d440304107409800004540c1c1018503c3d0740c44c0c070400030b507585016070b0006181880402d401165a209004150301d00459504895290f036080c181c0400a50014118602c1805102c42000100780c20880 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 878703372 1250 878702122 878702141
    0x13240905220605040c020705010212090f0d080705010f1d12030708070c05071805340c020306090c01170c090d1703090c0a081501030219030b0903030415 67
    0x10019000d005400d601000741d18080885014075191000401c190b2501e200342e100764141c40d4004c0020388e04e010300190800410030010301d01c0308c108010b040041e4841080b4142554400c1d915540444980d00381443c1601802c00028840d500f80340101031502c83d960040d09110030701c81c4655400e18610000c0d035030340340512403940e0a00306051000641036030088030660f91040c21810701e01d03400705e00c07642c44034185000d80c0c04c13490460780c1c3c81c0c02c0e81114000700d100d031960091094200101c800f070f1209421503030980854003800c200e4102042150364a2040044820b215400b9003141c600703041c081a42e0fa19080a40c00440c00a2501d1121348507510b01201050b00603410a0056890110304209018450318a414107507804004a41041c24075050100154440c0c440040500150300c1650100114400c3c02c0d4044d42c06a88007207013280c0b2542c140b40d5194110707139045400c10011801c0801c10703a0645400d03403003d800800b080c02003082c04000403004521440c4a100081111052002c2c40400c503400641c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 878704622 1250 878703372 878703379
    0x3c0706020408061806310c050616030e060a0c060b06041a0d0e0d0c0b1b0c06060a0b0c070603050a0b0306090a060b040c08010605071a090f07051509010c0813240905 72
    0x20484408903030b501d090a41080c4c0140c14400155448001050312035014195016a22842d4ad0110307040c90390090104120880c11507000380f41c415413890050203e040c078000502041c0e61100b610429540b540110b800420b2074120b03410018003040721050a542001041215142c2803c0c102000c4d20008121100780d111a074907441595066030b19000c0c88803200400c0c10707410381e9401c01c048003594860f9000d80107400e08040140110700e8040140284818694880071200c103080c0003d607814600414500705640e0a40380000d2656074195200d8090801010724503054061031090180c968008240542e01c135001d1001408103c181c01c007030108079904a1040c10004040303070f005200c1c603072255004003001030290b20120282d5000f51030710341c1400000c2d18840c40c29030001c070701c0040c060024040c1c4001004121544c2e02840c007015207058040c400c400415041010a00341c000c10400d014068611400031082202800c40d2260440025054040c41c254807406950f0481d0b41d02d00d1141c0400405e030341002d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 878705872 1250 878704622 878704681
    0x509070501140307020f0111071209051018090908072901050402090f03010c030b1305090607050304021201020c37021318083c0706020408061806 64
    0x180885242c542001d03180c4c80442c0503ca480ba0b520f20002d0107260483c0d0f0156901c65941c160320714056018007a00d0141c0c00512021010070007056444100d4070120301100d003031024a444610301c54007401613260b08000d040034a010345172400d02c9503590141011502c105400200b061544407032031540d00c12280d04a0032442540c005104506080e000b503e01c03150050044500001c0050001e400c0d511131003400f0340069961003614001d442c18004a82014004480406c61030400700b00c40d50302c07030074020900b03014414000046421520341060200c1901c1803400210745951041c0304441d182c04150290f090350040c0350030b12518102101700d101c419804100a140c070900856030a22001c420521070313024038681ea4490b003a180e41e0780e20400001a80c400c1480980c1c51505550421511405440c510440700c4507444603004007803110507008807031115044450321503c244c0b920101a00c900e411020a5005000612491030359a240c1d03802414050001c3c1c0300746964014081c02c2c090007050300901003c500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 878707122 1250 878705872 878705897
    0xa02010c020f1e091b0409091b03030f3b2106040615030f080309071a0c0705102f070b03090622020112060e010801090302010509070501 60
    0x2214036400036803001d0816022585000c0c00140d8040c2455002504010b6407000c0c40c00c54074002d0740d22540458a080d29000804900d80341c42c142c1d0050b0700034507000d640c0c0d502003802131004404080d90031f00c10039210202072549034540240304040b00c0c2c401c407000c1256691340490141c68034002c81100900340e20518203602d0540b01a110016121054540003d004920300e1140f80402003000c1d25000090014119420039182250071a1002c400091501c2e201000600c00101e03902040c410b51600020340382c0c0ca0341c84040d03025081c00040c0d4481c0d5070240312582c0103c001c402200144c00c00205003400e658035907035500248172030b0090301980c0708005003007483c03c00c40032402e03804841d40d10620340c1e242445081c00344105902d0200703e41c114102d1098040200070b40c014040081390750101c581c0c5440b240d0b0341e01610008404d5039075074900034140701c002e2004000700c9000c1d0344031000030b02552004036181d51703403503011b10300038405840d090b40113500340000150001000115a0708540c01039640403558035a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 878708372 1250 878707122 878707127
    0x3071b0f080352090906150207050904080304030521040c150906120903020c04050a090b090d1e05091503090106060513060f050408011514121203090f0319020607110a0201 75
    0x3c00510084c0070300e035940420f07906403038810040a400c2800d8444031303200480c20003a141030350720740c42548101141c1c020040002c1031041941e4101e030b07050802c6501c405a04480b08240440704030000502d90b000420441440074085040303013111441c00c41045400412501100d05c5070483c010785d0003040101c10040c905030b4540e4040000c560080c8151140448034600080513a441500c0551089840e050400300307003c440352009402001920060010000c0c059000c0c1c5044800100925912b080c80e668501d05c42c002c2c6d00b21008194001c1074a10603401388886d071000398005590040e1550300e032510200d040d9015104440e0303506031811408854518142003292003036460740030a02008410710000511500034041c1030340054480c0c0c0c400821030304118021038942042c2070464416448410202c60300c40e004148040d000041c0d0005a50302d50f24428120f20781141c11401b96481d01c0005290542c803030703901c0341800711901103600380d4400c2e85448100b26a402d86800c802c41c1160400910100150f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 878709622 1250 878708372 878708521
    0x110330130507061407080c030901020f030a080106030b01030e0d090e0a06120807080f0f07020f040b01320f09040510152307080a09090203071b0f0803 66
    0x90062100c98645a180d5480c600c607030704031f04417154844e070011070000499a018425801c0482c4103a004606100f240b020080862030b0600c1074034103065442c442a003c0d83d00c00e401494601d801c0004450000c14003880040441005120701280741806130042022146c0c81d0042508684109a81021022064075213080f00d5110000843c1c40700d4003004023003c1002c24002501c84001c040d000c0d070b611010140107220010060000365486149840e4501c5403aa810044001502c0d03020310500d400510020000041d082c030705244084060b01c0800c0e200310030801c19008105400c4140c80c1880346441b021010854103549004240080e02d0b00952940c86038420f40e1081c0309410810110004a550501c0002003940710758001d46600c03c0002d40c030241c2d140c200465500a10700b090381103185142141000f04251751446040030b01d0b0091444046c00e01c01e15043d018219a080590159030303041c444100e40d411040101200d900c680744042900798080c10010300c41120f400300703262900540040c546030001c103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 878710872 1250 878709622 878709647
    0xe0a18020c0307021c03020609150c0d0b060f090406050d1112100606050d051e070e120709020c0708071a09030a0c0303110c03071511033013050706 65
    0x1031006200b0301c4050ba0741c44920070301e28800552045e20003010f03410001e0030719000816030300a0f0380c0403c84030101600031004880c0c0c81150400c009031100c29800000018203801071450303a1181010800c0709082c24050007c1014820444042124942d80c00c284100c000111340301920b01000a20031030418246940c0400c40700c0303115010341e00540c00003901e140031a00c3c683c116000183d00820920100e880301e00c00d6075040030703400c440c069a50320f0700c141210003840000c026408001004039025540c0e15000d01e42c036150342c507010540712111b40326400b0400030b4000349001d6500c5d104004d000103090074080380c0c544c2a120449502070311003030040787c2204942e001c80100754061040045903c003084802401c180070358400e40d10780074410702c1d44422500c0c0c44007140c0c190740b1a4000c0c0204000c026203110b11445c91200342c3c103003240c00480c3e82000c00e007113000305025103285095803022003220b00c0007440303545154a40c040d01c145403621a6940494414109a0b0061403580080000d21180e03000c2c070519a0300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 878712122 1250 878710872 878710897
    0x60717071703010302130e060c1c052e03030212070c0302030a20040c0c060f06050a1d0a020406081504110a09050907140a14090d050d0e0a1802 63
    0x2061029a01c100040e05000280c125821020005104500c3c10340c841d000c0d00314042c00b0900041c000c810318a51203140242030740c11a030800080505050a442c4400801d40da10444100311916208800b02d2824181040340119583c101c1c02450320140c0c11031008064a806900074519004005942c24680e40300032019607940384220000401079800f0007020340d42520500c600d0100d036180917072030031052040b592042c1c846d6041038074420510743d001580c000e265070010004240c85000c3d41c9090001e04403500280c2d00500c4a0401090310129030720645a4140a46400c880c01c1d654240c42c00101e02481c080c1d28009602e030f8021030301079210301c0700072960101e000b003000950b4480b80a045c0d403a5400728900344e02046480104000520301140365551041d4035060031003071220114000f042d6407242035404020301039100b0603408072040302c0d8281c82c0300001c003500082106520342403582d524240500403d002603c604858035150030410407072000c80f20061000003038584c3c080d01c481e020790892050f5040b07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 878713372 1250 878712122 878712127
    0x21918020903150a0c1715010c0c030c0b0a0f030209132d0e190f030f0c02030a0c0e070c2f130501050a14010e010e0f0d05031305010c02060717 63
    0x1408865098a14010950500000f50170421040007808554941400302c03040300900040044d011008100502c41c8003091800c01020300302d030300c1c0c8007051010a410140841d18254400325606004100411035100203480309540c0c3c580d210710440592007591089a0403902e035460500c4043c401d46c20003900805001581c0c1d010115071728900c8078042c04101003145c0b03143c80300000c01c10304100340800040c0c00c0346100b802c1d25000042c0c5030071241d071121140080421030002d0040d9210740c840c0c0360130010260b005050f0386c000006818a2150745440c0d026801c3c0b445a07403808a00040d00444404406a900c90031407107a5055085140079400c0c40715215011600b43c00034031040650714594015100c01c00c0c0140019954105800c0c80501c05041d0031001901d50038480008080e038019a183c0d03002c00c0d0900e4900000301c1d10501182001c49080c1840350002507902210382006404000350500c901d8100d0060202589c52004440c1150301103000b0390000001c00036080071030f11401100d002c5454000c4000d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 878714622 1250 878713372 878713393
    0xe01020a1209060e090c0a0530160216060f050c01090614060901030c0302060918040b04050d0203120f060f030706030f050105060702062703070e0103021918020903 72
    0x1910071140d480d6003001810b0044140b110540111410b103500105035941102d03031500c2c41442025108007804d21003840b8021881507900258910b00c80c0c000184640706441941c202c1d6100e010000058070013840e0380d41012490340c03410744000b5010101d682c0f40502c0c074000c10300d0a1002d6510b24007141844040042c00c10124442d04400d0061020b241d10503407002408407940b002c210302c0e171003000d00014465000c2d0401000481c08600048090b01e0301202c0540da41c00401c0c0005039815510801000e07100942010441444540316200b4800c500450550707454084411080f0784a10621104251442c09400803820145441910540c800f101401070f84111301c20400181c640f14a40d030010000a4172241071180d180060300611b801040c045c1c941030b050521542c0052034038010003c2d241642010032101d036040c0c1a038000030200240010742940c440d50f4403910060b81c4d1744030900099000d8515045042c00035a00c0c08010402c607100c0b003403442080d01088240102942c0311361409941403140d06a0030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 878715872 1250 878714622 878714633
    0x1208150a08060a1b1409060910120b01020102031e041109160908011802010309170c07030c1d040f03110d03140a1a01120e0f0c12060114010e01020a 65
    0x1640034055290092086140a480020503903d81d225880b08942d00241409000f07504910840c110170684890103440c0d0400c807020500c01c1c09030200d000c3d44012215007000c0402d0700144070080000600009025103404400161700384d1005071a0216805201c96440150040e01e084403038104d881501c0d2404405040030004400303c00c00c1d54645001c2611000d60705465802036404c400034201c03c0e00a210030300054000c1403403080100c001034103040d103030a8104104140700c4100404010038031074194540040d465520358a6026010441740780081480114488040200e036500104000d10b181c1030642da40d03521454800c0e21001304506001c4406a0b2040c680c3c8188100901410030f0340d4000303058402c800c2940c4100402030290f40c0240c0c81c04480f842040f07024000b11825510a0034890702c03540c40001c00c40014005904da10885003c0d500640800410214404403030460840780220505207400304940c6610080c801c8805580c04900080130039402003c0541c94400140140d4507004c070075807940d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 878717122 1250 878715872 878715889
    0x403060606021c0f0801030f051609020a110601030b181504030824030d081902040b2101180903030f050a14160503130606051201140112120815 63
    0x40070240c1c001c1854100d00b918244007429000c25140742101440411400c003401850040c04090310342d04d1800d035800d0503c2420091041a601200345030301d1650342d101a4007000750440800c03500010030981801a8022000403524180d13504441c50295a031542c02d042c1581707080c02002c00400e4001c1030409060710384501130f400d00c00e501039140e02001d45000708450302c0e40340641c0c5009242da10380d041c500302c0540300041c600700213004504061070b060b2501c0c90344a9034160f6900c1e00821903400041c0c0880c240d001c50000c0e10909510061010030f4068240f02034061160901680c4180b1010090000b03000300702d6003210032401d0003403e00041000c00c0400110660f0300445030000c0140d203501614209000000c016580031090600360102d207100300200074842d11000c0e0440218051b000b0041c2c0030720815900020040c0002090650b1882001101c00c0c0079006107a501500000890000a40fa0421010b01e1030680ea00461541d50403202800903a0301e100060100002d4520007400e075000758960810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 878718372 1250 878717122 878717129
    0x19030f0b040b07050c03161410060e0a020301080d030209010302091c1703160c05190b0f09070b04030b0a0b0a0906051504060c030507030c150209010216030b180304030606 75
    0x980e8540d854242011000c0d000050020750410808210719814018003005460f6103500407070500030880c48a06108040c80314001d0340701c005000710740f40e0209034586580110129240d0340004d00f89560b5902e00c41c4120f0009101d20003c1e03411032086441201e209a00412031007105040c014100342d202030214a40c0031094a440790945040d207034070740500c2480514461400c021954480c61890607003903030008114600200401e01c078040c1069410403400f841080c1c2c0f0302c9002072440710b845c04a070400c008150000c1e980b20100c12405004219080c20215011056940c2e0384030040c905444d554480755544001000083c099030794841c1c004007036442c070352400d00400000c000411024141000c0141c901e45070795081a000c01c0c204401c100464100d0058003134290107040807500e803c55828151002070001100410148614009040341101c0358064000e19000380e00700e5841d04118950341d440043d0078040a07100303194501c001052420700d0f079800c954030028101540d003403540d6070751240c068800540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 878719622 1250 878718372 878718383
    0x31201061214010303210e01091109070503011a0f090a0b0901030b0f2412010e180d1403310204150e0714041e0f15050919030f 56
    0x30840440d03640d0259000100c48100702d0303840e6501d16074000d1308900140412680354a00c2d0305690401340c449070b01450031404460024002c0516500d0154040c08200907183d00c02c000102c04681c5031442242900d040e11080e90342230f00071081a018041407038004c0581d20750b0540d0100424a981c1d2120111000100302c1501099283d10400e4000340640e95016082c900409849030080d40c65515082d48003125414107510907003031714896608080354801c0101c4010410320074800054590b0700c0049030f170b109600645036030080d0045003c404d5141c4503031b010a030b40004c034001d03151200c55010000071500030000d2510032a102e0810640c813032002032100708050b084124402c010342542060700900342e0814501a040740b4090030034024403a400c6024102c0c0c4100319030130914841000c1c0c69011100038020140b85d600f10010003018604440181e40107001454141300d01c00030791054008001c25a02196494490031714440074240911480d142c414078001e0145410000302080741c010b40d5000287c01030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 878720872 1250 878719622 878719637
    0x723040b120f0f0705032a06161a07050a020d11160306023001062102030108030c280215120c0a021b060d0b13020309010e0c150406050c03120106 64
    0x40480a04000da958440c3d40a1f40120340c2800c03112898503840c0d0030598a0090200c1e851510302c0c0403030094003030b80001a500610200116051207254000402c21410b220140c4885540c0c8600446c0c0a0140045440150b8440d40c00366503643d0003120301d1120f0440710402c440070300e06100342845c03240c1c19945c0700791070590b0700080c0c0b120711901d240e00c40180f0580d041015008140003100c00e6580010510550742005800880d2079100740021480720b5440c0e028500564a170350f1100c010ba5125031220700c9501c0c0c0c0344100701030b5181c4050804082c410400d2044c2d51306202c29800d409008010403501c1c403d8140d89020898941409001400c05024512043c2d096440c0c51391141d002c0e1824502c0018054600c100030b900350460b41c0d9403011103600400705600031900d0349099003c21001c440c01500540c1c641e0000c810407500d40c80560003820388500076800c07240043c8192007802070f41c424807070800142910030081030001034043d074002c02030091450f08591400002c1100a61800b000380c01c850005001e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 878722122 1250 878720872 878720893
    0xb03010203180f0604030f0807050d15260304170118060606110f030d0b0303090a0305060a060902030f01031b0914010f0e0601020706260f01080723040b120f 69
    0x400c800c10309100c003d40107000504050700d016255401038400003040040e84000110120b10030307070036100d444202d0b44c41801482d603e2100c0c500e01d01820300902e980e4448040c5a02d40401103085040c0342100c0000145161605000501000124035100c0c03102d55900d82b0760100314140008504124107000701130005071541011310041402004c01d0705074134150f01800194120388401f100301d0f599154480320004078003080030042400c43c081d4404190f44106500070000130f00c240426094884c40590f0010404603031221801012400183c800a001804103030041c40021641001c0f80902d070600f8038040d401e250303034503030620a0300d0200c107101507240d100000400201c5a8403c0c0e5801500c0c0c3c816072200e1500e09280000d650354000c0c4a9601040041c0600d40041e2000c0403601d80300e00042e11604a4620b02050100309800003841290b100f44140180001c440c8090181d100c0500449009075120740b6040c4100006040c0741c602c01c0354404941c910307140e1054010000000c860341300e800680b0007a02c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 878723372 1250 878722122 878722171
    0xe040b061503131a04050d080c0708090f220c030c0c0b04120504150302180108060a060305091618050703061208031005120a0c050105070b010312030b03010203 70
    0x40030302103501034200795840d040c0c5414080162a07120050b40c4042c0c51114483c1400c03441d0229140c91560600c02d104180070030f20038041401005140251184282d54507805814501c074401c1010141c001041809440300910b08000c1132000440c006140301c02c803002241a01803982c07511f480c042c065513640d50b20119615014000c40c80f6508407414409520001519030824140d80103000400030030380d04211500b0913020340184d42c05080c00027004a9984440d4202400a40c001d000b00c842051084541305100c0d03114003541449500042c100c1904903203448001d501030300b1b010385032078514010286110080542e9160110040c2140c000803004140c9000403903048030400b40c40001058202074080c040c01d0f880b00c00c3c0d9003400e0b1388503820703d0340d0b07540d0700030202d0880b0a83c3d00000d82c0021085c0710044030000001c0d03041c1409008403c540c4006549400650f0184140603005082030103940040011070403800d802d284865540c00c01080455504001a007260b00c21a0740780c5403520b00d0307220250300c0c44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 878724622 1250 878723372 878723393
    0x10b06160606050901031a090a05030d061a0304080913061a18032808070b1e07050a020c0f1c060e0c040603020f0418050a060c08090c0f0402030606040e010e04 70
    0xd09640d290b0302941147c441d10b00306117070b81c0c2d0499240e555410200f03582c0801007040d01c09080d048002e4a45500b0940c0024010b443d091207280c1c1c58101d500042d0308050806000ca0b806560300003101450228140180075900d2250350600109558580c800a80f110760424003010700c0c0c00e00382d0107a03640c82a0003031080b0315210000142d402a80200700c50000c045050146000c50001511381c18031408540c90014100d115450005040300034020501065200b1400c0c0d1210001011404107001c0d612a8400c5545000d4a0b2031f00006138081c00307088000342814070350380c1003030b04014003080b1f80a0004c0d101c110010304c2042049070301c643c1d80d070f0443c42000810300000c6410003041303030240699440c5d0380014216100e0640e1052081d6500c1e00c040c000c92016015030111241d000055404c0380c1c28a051090041140a1003603000c90321503030008a0944d800f090103070110310020600e14070301c0d0541301844025080105080d4106008010202d803154102c442c0500034100c030368140e03109250510340408000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 878725872 1250 878724622 878724629
    0x61603020c0703021e15030f06030312060f01090b1c0f200306041d0c031b0d030807110316051b0109090b04060b0a1701050a0602120c010b06160606 65
    0x610502003600080c8002c100396044a40441d403c119034082d241e8100791190245050940c4403620160641000c00d030b45d006180704402040d150001d50740c82605041c0c480c819604c59002d0080c01038005078241c90440c3c00000c19074010715050074069110702c0829020303409800510b82c0c0c10310040401e40c0013810f9018804190460010070700848070801800f403451030380e02e01101000301c000710024680f0384995008800031200110900100002d8044045d118400120b000d80280074103440449855990f1001c018422006401d94051170314544046400c0e003c0500003400700003060029003c0b200080025081840340603103030190a8104c7e2174180d10303003003080403100e0300c40505005404490380c01051107000c9a41603a000706d0608426000100181159046000041d401050010003240c5c04005203003c9078070400060703c9031b62101c3c100078403400e091140c840103921039003038040c1ca904000d002e0300000d16000004541c9112501c0000c40030b421894140c0d110f109088242410b0154500031134006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 878727122 1250 878725872 878725877
    0x6010201060609090b04020904020a0c110d030801050405100e0910140105060405011805090c09091b0f070c0302061603020d050c030a0c0809040e1606140921060103050616 75
    0x450325218001d000c84445118004d642540e0300d40c90407168640f60101c481d040c2004000f195101c401d0180170749544c640e20020b4070b21080b000c6014105003806801e0369850361305525a40c40e02c0e0320b0030301048003810005040540b40d0f03820350b6000580280244802d070049c0c180070058205008081d008a00312510011561201040500100000c0e25a68101c40c269002840c0c0084840d2100380ba00240308019880b041c0c00946040410441e105428050314034407500716101c0700c0640f00c00302150428105418021196402044280400c42c00c0700000c001c41d5118440701c525195894000958507081130000d10b07002c02e1075420920802d84c3c140700103a8840c5140c1089414030030180803465030303405046022030902c0b8820303004000f0700414105a403580c000c020302c1408000b4140c80d00c1929103a554064100030300404001003541030080c4101e02d90320300340d01d090301d042000020070006030076100e00ca08461100103004180d800002440500e000e180503000404690404607100880c0304418103220f0304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 878728372 1250 878727122 878727131
    0x609060e0a03020f060705160e04060e1b0f181302180112081c1518060317090a031202010203040b0c0918060a090207030306050a0b040e0711010906091a06010201 71
    0x140c0d135000344034144800c10b403900d5031560501c2c58000d181c101025200007d401000b0000200e82c03014040f12403095118504c2171121201c02d81d034490740c41c1d001c6001c6500384000d010000c049402e144081c0c0300300c80300c001c0c0a1102e158204075000c0c4a074000b550088101e007102c801c4a001d5081c51007d400480f6040d100c00542580351420040d080352646100802c05800011885680040a021844141d4040c1800c11100c00c0815080d0320703000840c40b074a40080c031550264000c0d084030307201d48021a5041400401120250460301340658415820103074040180300001c0b000ca030446c0328420300541d064000503034074102070815007c1303000c0080410803101d000b0894000c0c00d1720354a0303c81c0342e071400000303540c466034071920005142c88c251500421191480030454000b1b0540c1604500111102520044200d030f803034100b03d042078400c1e80100940040a0004621558820414014400d40300d00001a82000c103503140d00031303565001016580c40100000c04203000c9009400242c1040f001d000800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 878729622 1250 878728372 878728379
    0x30c26180a02060a0804081e03040c0f06020304030311010e060705041d070f0809010e0f03070314040503070506070318090605010e040506011e050403020d0c060212090a0902031f0609060e0a 83
    0x208980325071130030041080043c42c00308007000400801d0b10300309602c5002501d01c1154071060b180d0503400468090b02c40480901000549024501038081a1501680035519042c116203094400b6045882c09803895940c600510500803000d02083d40200c03095903031a80d589140c20041a0a00c00c583c078a45513004281050010380c80d080040d050110440d8100103c088ea94504201d006000c0140c0c030103264040d0101c40450700070b0200042214900c2611203040e10901e010703100016000d00d018482d01988042c1d4180807a1904e8005810007502c0391805644011102c40b018460154a511448626484600030b10566800c032903c101c410700191801c100d5440d003400001d00500803404802c4404005240101e0b25034072603001c40d0040e42e0054407144240c0d0180c84c000020403000c0c454140140075944504804404001c00c46407420720062440d190315050071101d0740254409414a40c0103002c8507038a10303142124544803002003080b81c8840e5034083c074003507026001542d404141072003a46e0004060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 878730872 1250 878729622 878729629
    0xa080d020304202101021605010506121c050309030409060923040b040204111b0304060306060908070e0a06030f050a06110f25080706052205060601030c26180a02 71
    0x1502d00244d881c0300c4081c203880700c19181c1c02441a00801035010700c0340d82c1800140401500210b00030001136600740d42c0150803082442e201c112680c2c000c01c2002204518500961081c40a10b8104001406070b82c589a9213803c000112100c9e580b08046403038658420321400d521011a0032072a11a0605c0802a841e0954488408601c01400280704e296915408072041c01000140e4814540c402c040b00e54024258180d182c0d00e400c14812900064200140070a00500c00c041c01c400f00d40306e21005050032402c10040d07800802d4000d0840d41c00641c0c81070000003041c401c0320024415402007000e401502014100003003629002485460180c1c01088200c0300b203a002d0301114481c00010310055149402c49040380755888440c440940007036408140390040c014a07a01003409020807082e0151310404100c80c4d840c903005007100180054105c2400103519501035004400340e040540307000f1000700e0030651609107100f15050405c00036540c0c80201300d2403110301c0c0d514843c1c4c2d454120080950b4081607000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 878732122 1250 878730872 878730889
    0x8100518030a120e01090b010305010e190f031b060203100b040f09020d0906060b0a08090c0105030402040506030f10020414030f030f0f0d051303020d08010303080114030a080d02030420 81
    0x20003c040001690740e40207030f40400940756803074000740300c040b8090074002000c40007030000303131b03429460095400070000d00062080307103030050f2840e15900d03032801c0e803100b07a41002410402d038140301a4070a9a00b82540c5c1c400c2c2c8a800e1842001c005849003041c140d482c0f00e0112a410021000c0000c01c400e001c003000d0252804116070b0001000740c2e4a40503c1040341c00703808100c10080881e41024400301d0b00401e504050328002e0403507661811142d40c0d42c5029680c500701044c000d03020503010808a80035080035000a81d01540140450308000c048800051a00d0320a4641d82740c0a5030110f006d01010455440d01c1c00060307011801000c6a040b6914159246d210752f01c02c20f0b010080014661f03544000a0702071311795800c40600208402d18189080300650305052038202c1c0140190b42e200d81c00700b800398030714a040c0d913015034605690740e00b0021100100c802c0b4807440f40d41441125688000114064014081c05144040142e1a81840c1c42c00200145444000344000c00300c00003030034220b031585942c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 878733372 1250 878732122 878732137
    0x5150106020729030405030c12040302090c03041e0c0911090901150207030501020c1b010c0b01050108060409060f06050f01090e16050f07030306050a140319020a0f0810051803 77
    0xd009101d0100e00d9031600160f222042030700064203001c010402406000300c054405032808005540900c456120b080241e4030540c0030081d407100d5100c5c0414104503404000c2c680c0a03215090301c01e8600485001c080d07150000e510121101c04135074070280b1881415000d03e010703550141e80710031f00303014580c1c00207070f8064014090001619444484204c0691080207010019600007008640c4c0d401a4190386e921901400743c800b000d4114154100440e505c03400786880d607160013501c04400d99007450011142c081c00580820b40c410f0b1140503078000306110384a59980c500e6920000500ca61074441400f010011903c41c01d818840717030701020811256103a40c600e81c485c40034582c178030030000350f003809540c24090004c1e038000c18403020035110f0800d074241c0d102d081582c508071603a01c41c0f51350b00c858500ca002521100c01c4c1d0541c0100c54000d9114074903080d480b4880e07200401c10082c00c0c2e295418034803122150b40c01003020358002440c1807807455039407041d507800c550200c1ca065000b40d030110b100c0703581e882a6031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 878734622 1250 878733372 878733389
    0x270302030c0105120a05090703080f030403031d0c040e010204180603021f051e070606080f1209030a020103021e0a0906030f05041e0203071502030a020106050f09040206180409030309051501060207 86
    0x1b0000744078440510400000c3d65100004648402413902000025001190708901082c6070280d000a8082e0b5a8881000c0305d200030014000104600180006403aa1988170484d564007400041604410340040b10240c010a80001500d02c1c074600400010141044510700100e507260b00d00700360700798454200d502c5c901a501d0803d05103c945042900c041c812143c000e02103a00d040400f1445003004035059160741681811200311031081480380403d8804c034400658182e0200f01c0c80341c010b5010fa005800103134803e4030861034514000018140c25440f8200410000d40ca0450500202d9003600c600340d003040c3c0e099010071040c5010340e00e00c50112040c580c0f66407081142c800c03031002c5550400c000c40140006201061070840601c6010b55281c200104081c00f550800b0004070309824a070342d913803c181e0b900906076481c85d19650244034480d0b224101c00d41c2c220a034048140714075140c0d80907284100d0710940e0001041c8801d41081d900f0100b801c4500070a00c41030b50010003e00d64009030174829160400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 878735872 1250 878734622 878734631
    0xe01050a1e05031605010e01171b13030b070206150607030305090f1015060c0b01060509060d05010803070213050709030b06030c030a120f020f0a060c270302030c0105120a 75
    0x208508601407540e92025506224035900b20f00a840003080c00030464100b030322200c6c49000d081005482149074007401c01c0d2011400b4001a40c090009541d107680712107041079207454189481005011044ea40e0803e0b0381c01e2043e0f0041c4651030303604104246c2c3c015150060400c00400c0760001071523520540bc009002c06032102c010075820001800120f20829900c011114203821000000002e05040d800c0300060710790100c2c0000d219030103440c000080c240d00506001460f0300380791080c2d0350381d00502282c980020303051208150384171031840303414007810000c0000d607121149841001526420344400541c00e50401c41400301d956044611102500d510240280203a40c554010034900122003980d141d061040d4011001445009100d5200f00c20b850380e6564612250504141d0340c40c0240d903041e60181c3d101014050100f0f0141e48140d00341030a40c03804003001812000d1002521881d007030102451640d6600400442c501042440802d00e030a0074514149286050901c1000d140140443c0300c20751603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 878737122 1250 878735872 878735909
    0x809030403020427050705010e0d15051503071716080c040b040b0d0f0b070203131403070e0a0f0f15090e030f0a05030f0105011404060c1403031801060e01050a 70
    0x2480c1d001110318420990f00ca200c1045040c176583d0303070900e803040d0b41c00301e0404a65a9071a0508010741c50a05400c50341c81100e090350a900d02c402040300400b180c940100c8a4071095895400740b00460050108050f030242c2a01d0a010340d0b42052214000380301c03c2c41c0e620504001d0510040740720043c144c4121000164000504081b402400140c212142c4c442041280003040100001d0200181c0e8020f0000b94042e554654040e40d881c840c48005e0b0540c0504210708100c0381002d412074408408001d015141c02c00d681e01c00084c603940d001c1d103241c3c003c00d440303410700c846400031841820040c010700b4105000418071105c00c3c2d91000b030035000c0d4141003038940b4860620007404204444140c40c1d0407030031555500d080c610091250b08180c0300c1b8214103002da000001c0c0b541c0306641c11780610501d000300501c0d06240410564214450203021540000c03107550341148948180080c522480f481c0e91030f40c1414041e210300c0303400c680003134001070600c881d940c00620654541e0041d28080d2688403042141e100803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 878738372 1250 878737122 878737151
    0xc010c2316080f010f02180909010f05010f050339030a0b010608041407081f0914300901030b06070f030302041a18191802030708060108090304030204 66
    0x4020306005401d031a8240005040b500001c1c10071000d6050714020070000a8031644442a40b15a00c845040c80d07009030840141e500d048914182c001010350000142d4182171003940003a29426481019601c00c1c40e4020022800d0034495440001107941e400140d840c1c0e40080032601240080341b02d69001030016aa22041e00c0030804240c40c02d40110002c40130f907030b4481c13004050076411a82260780c0c0304140424109040c0003e0f20740c00383c400d030341d001c0c0c20080304d0f01a07045e00b850341000308044000d44580d543c90100300c0c00c41091061900740c4020300780c3e58070480c0420001c2040001045c00103964507030040c4d1440c040c48148c50082c81c1c2442d010441d00302f4140095014022200302502940040701350800f0540c05900500444003076840900310000e640c90031250500500341034020444000392146210302d410600380c0300981c103117a825185687c94030a080c13012841034800f0720840d50f00005014125800000e40e030350180342480d0034012860f003c141952640036504c0001d001d141c94441d14180c0c0700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 878739622 1250 878738372 878738383
    0x601150e030106080d020124060f0504050d0c0e07020d0e09181002040519030201050703211802090907030c0e07050f0315040f11070f06020403080a110c010c23 70
    0x59004000b800720135159003116864900c0e00d01030802661800400700515400d10032008000d20425207852580c52034481c069035a40c51110b261020404100004202d5aa8607229909910f004100340e0364480c3c20041054407034000070f42040c065500010415000700e601821500e00510286c1e4140229111b02c483c03200b0080d0407041c1080c0d03900446040710316075003940e03010307008462080303403501d0381503920030340e4004c03509031900021f4005001000a01d02003030054004400000b01c5003041e003844143ca003c0b000071a0b01030b03080304006001d0040c8080641c0303400b127102c54110718048051f16020f8a140c2d102c80d42c141a510940902d110111b002900c4540980107403500811a12200303035480c900740042486555101014900c21b0b854015180201182841007188009100041a1801c00680c413140b01149400d48200c030090307020400800005e00307080c050199010181c480e400d80c16890348019081481101400341003201503000000803844500a6065040e6002c9032100c3c0500c0d0300084a0504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 878740872 1250 878739622 878739647
    0x303180d05070303270609090c140315150a020303160e0a0e0405100509030a050f0408030d06150c020102030304020607060b3001021801030b031015060306090e060115 73
    0x6000700e10b400414503070840049207072040a481d0010b8000b20381112030440d45841c0c000c080015200f4a4240700d105001c0d03108282801550034045c000400f8910100074030342c01190b41151039a05000d41d0301741c90910342000124000c440c9040e5081481d4040000c0d903d020052003500b15000305a11604e14a02401510008410103414405242c0e00c031050b15001c0101501c0c211030340c0c41110700c00d0f90310040e03520805009030850005145001b8071504200c465810016201494440030480010040000c00c000c011101a18101082c9503280c0381c5000d03506044109008140200600400c0050380c1c00b0003140d46c02a1b0403204213464001341e003001c50040101220850308001d07043c108060b00700400c4000b03441c00000110090244120207041402c0c0d003e45468460500503000c803810340c2d580241c00c03241c00e00c00c0c050105e407000b80341d000e02c1009030344148500100303144d18280c0038810300ea498043c0c03402418441c01c0034859a2810103180e940d441051003120762900358032481c2d0f00154030031a2400c208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 878742122 1250 878740872 878740883
    0x6040317091c03020303190c0e0f011101050907030501110301080303070305040c03120309060506010c020105040e091c050c07050907080402041a030a1118160509040f140906150303180d 81
    0xb400e64070f03010351799510547e05801800070a84603070f000c100e414090021400c140303590f200c044d40542c00502c00d24001c00c8030b03400d0602464144114044100744500344c4202e20703d00003000c0f05461030a01500312043c0d520008509807040005002c20840003045a81240091900007620781c2d403400d1507150500303da0402054031440141510300700c2c0e815084092664011041005070361149801541c0c0c142c003040b030003404140103000800050b2110030405520001e00c0e030556200d2101c4803240c2013608464054a00803035030114a0a6001104000700d00c05814142e60740c0c6094142801d0141032401c0080000b44500e841c0d41c84040034480c080d50380941c2c04005012550013030300b240780140f0a41c0c4031020380c0e0f00602c84200c1c6034200c3c0303088500701c500846100a00e5105407a08a00407186548000c3e07080750401d03110140c014140348a441001d180c00100b036002046070400346040c0d0300784100500140300004810601218070359012003101c204410010036a80c400c0381c00404108030000501000d0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 878743372 1250 878742122 878742169
    0x4120f1e030207080c0a0b0609060a0302090a02090a030309030b0702010b220908030a060e0f040b0c070507080613030e040504050c040207060b04053402061302190b13050604031709 79
    0x1046030f0000e030346111b680c4115900001d96880c842844071520b02115802d42c17214140b04204054200900c00c1d0340c0100d9120005440c24511501213880070714250b1040300003804228041090000c1c5108198004105100a12030b041f480d4000456450311103604201400e000006040014241d40c080c01c070040d4868400340d00c0e46040002c440c002e00d45842904030318a00c0e0760002d402c00c0c400c1d01c0304610455001c041101c0c192075804580c0100c0c0c00c0120101c0d040c0c4100300c0007069404003002140d00c00c0080540d0104008224078005210b5111201040d020301c1c24a024440050404a50654000d0041c0c07401601c40c842030402ca40a010291862038200e454101400346840c641d04000e1064810a0900e00c4510300d03c6d01d1100b010f2515410800c0160444000704540131012040e207c6201c1c0001d0861400704420001c080114a02c0e9000d17410f0b10100042403400f081c002d010707000003004c0c11a0000d082500d941c0303d4000d00c8603110b07602c41c0c0542c0c0000f4114507950340d40040020142c800c170480003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 878744622 1250 878743372 878743387
    0x702150d0905060709050a0605040506040b0304020d05100b1c0f06110d1a0109120804120f0519050607020d0815010212040b131a192604120f1e03020708 67
    0x2401da5005010345400303087d10f8a07000c19002d0040b401c1301c04550015000c9031a00340790002600480d000070b013003242d120254a03846000302d0740412407840540382e01c00e8001852a08403080150442c0c44d82d076030044105141926201182544140e202450f80201c000320360382403808405005413003202a1140708a02d0810b680d04144000c1010b00780300c4000307883d207455054807041d8185481022100090048000300802c1c0015441050100072061040700c1451140ea0156101810000f40214501f10002000000000d0040c1001001d802203001c0c0090500401b44540003002d08c00000c1c100c90008000c4107113004613034130800c1014045111050001c0d11540c54061485103070b0b102c020303410110b00e011704002c1500b5894103900c05500c00c1c86200b50f45803424a8102d0203580401180c02d000f8000030f142140242500580300c104062251109500e05262502d010101c142405a004080080d00d207003000600c0c0e0000440005558408100c1c0e621034401a4100d0207131091000c0100100c02c0440d030784 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 878745872 1250 878744622 878744627
    0xf0303120b0f1c2a061805150706110f070b10030c0303120b030c0604060318140f28031b060903080f130201091203030b190e0a020702150d09050607 65
    0x6111003071241440030209442d030000c2002c09030004a1115950304584c400304060f50141054642001004000301e440980d5000010101c1092180212448100040100402071248a0a5400300044c6022420a81402a0348195000e00c91005004c41070400100700342c181c1140001004642c40708030308070426201d28000b000c1d04540c0590b10711039420540f61380c3c0c031441c02140c00c0c1c05050010b05010b040c6440c100003180540003080740c0a155205c1d0108240200304003005205034660070324000c1c020f030b02c07129100c00d01d00b001c0492403404000d100480c000a95802100100704140c0601d0304c1c0440d0100302103004840c0300d41800040029240c040c02c0d008164002c20882d100d8400c00c101d84d00d0940c1c0e04224207140300c0d04420024001901c0b80d50610000034488040c1003604d009141c00503071040404007241200d130003801144198600c907001082410031b56a861648919104d00650400846601041c000311901c03940d000c040701d004c5100040c3c3d003410703444072a107160044102c2d43c02d1300301803401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 878747122 1250 878745872 878745919
    0x90406120b0a0506030a120e100302040f060e090109021323041103100905270c0901050d0807030e13151509030816110303030a060f0f0303120b0f 64
    0xc9941ca00268006841a80c052007601c0c0300300c4002d800342ca0403180b04d981340c0d60314031220000740d070900880c0f91b054421a2180600a40c444425440060f0f503603045c207074000b0380f41809501032010400c000c0060106610342e602451f0441d9a54440580c45441c1000d0710602d020990300083c510903820025040ca8403a1003900303100703130702c400c0d5000c11000c08406900d50b82e85c401158495000320128008010710005580004c0e4050700b03850304082c600c000751261705024072a0080351007140d40140c1c105204d910b8465459401008229090302c102e0030315548600d15802010400340a0003440c03030a1841544a403500c102e4420700c2002c0822045002241d076000000403402420241c10f810003844d1b0802c0c3c010080101525080f08840d810b26903800162500b0b12941e2204035405071074241c52403401e46040001d18042d04a403440407034014240307401203460803000e038044110401e048004001090302f008d0104083c402c1100d010410a00d8074001c41c4a0200c4c89042f01c0c3c21960701ca9010340c80b590340c40c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 878748372 1250 878747122 878747159
    0x60121060c02151f21030f030e03040603140108370209010806190e191403040312030c02030a050a0c03031d030a11030921070b0310061101060602071a090406 69
    0x4643e80e40d02d458071080c01e42148148138803980103180c45c07640c0c00864051307004805a0019031802054000030540007d0654010ba8460004261194000800c41842c0d82d0075501514440c0014a145034020404280501140140c0041c1142e55841c03403844070404075001e048180c01a040c461a035a41c2e6128684d2400c0031036040b652200114040240d0021502408016141d6007000702000c41301c0810722201c10104250885100440e190620308880082c0007400085025030001076044420680140a0741c1041c4032140442d0010009807007003e80002c1a2000c9100c1c9107411010301910746400c0d002001c020300d013000701c04c00300e80308149d0210340000208120a42030b0340f0004805405d15103a60f50b030152f46282c941c003c082041c88000b1031b07000c4282405030a502800c80d990741c3e80d1340c548400e10341e005035040c498442071403070113110f025005440c0300824070041000300025860514002e459000c14050200421340c0384014187c540802002e0703d00e4058014400c101140d959980814609036050303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 878749622 1250 878748372 878748421
    0xe0c040602010b030a020a090c020319050a0207140109060e270a24051c0b1e07050a0206060f030724031107050604080f0705150603060121060c0215 65
    0x162044a50a000c035134031701003d03405022105014203141054004d010616028011848180072016803d54241e42c200b1681900d40c55040e42c846900a0003414290250000c01880200d0030034001140d90125500f41281c206290613654090610000b440d081800041500c1c3e001c01440a5004c414240416500500345000c013040400e062840c4c1038041c08500e41d070300b541e0600d81d05040000d401c00f20402c84107007205440041680080c1e6a5020703803c441a0381600d0800041d8500e10700d00320808002c941c2016040c10b0441c00c08450716002591484014035490080b90394058204d81901c1c00c2010340042c00c40030203d28129107101d4030f82c05018840c2824100007904088aa5015440302c8044030805034204010717000d603640310340741d06405074007109800500080400125007c2481407124041007041c0d65000001800c2000070540340c2401030b0080400e6150044441c07079810106d18600f14074951041303021036107900c01601642804244144205070300e42401c10000b100d218002114aa0034111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 878750872 1250 878749622 878749631
    0xf010803030f271c09121401150905040c09023105040e0105090105060a05151309060308090f01030c021e250819080403021201060305030a03090605180d0c06060e0c04060201 76
    0x44c40445200c100d40c800ca040000003440303010301084c20701c4460b544c0f01940000201d030f80c504000602d0110754450f4880000150385006200c100005c0300f050000902102805600f86544200c0100404041c07103203d001070365403004480c40100c04428210020704000b0070401c80c005c006c1e103140b80600812250041c0d01d51810b00004e80c185004003803001504c038040c0c001e00b0200329912500c00c4513070024409d441204041080003845003602d0180300055485030b260070f91145c1c11036050081c402544180306052509001c0c0d201d0f101e07580001c18401000ca6500f04480d00100c1c1525107007030403803041d600c004814002128114100750785404c1e004440c440011a1051207070074001d400900701501c00101005d4040100304007625155403141a400c2802000058840c0c0d039540b4645950f020007081404203448909038000d10005109880c0e202c0000c06c0042c2c04c80c062000c206403641c2200c8000820b0002405407074040c081030747d10840180111100d40c0841e42800306603010035400a01c9000015801c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 878752122 1250 878750872 878750923
    0xf020a08060306070f1b060f090204050f090607050d02070606080f0f03040b03010e090f25050a052b050115180c020c1513030c030b0f010803030f27 65
    0x380f541e20681250740c030388210a10003d01180e085000d44a450440e0f0801c0f04040c002c10b5942c4145c1194060340e5074009040040d0b44140015110010303c60142460346e002048021040450440d03400421441d01c10750355a622483c2d08000c1c024440041c084900e0b01c10f002c01e01310000510500c45d100400100d42000800005450f031700d100d00d00030175005844c01d100410101e0140f400fa035820040c1c100030303a10030010840d9124900460301c08145250760345003c59013460200f044402d00905030544000c0c281700d0420000c98001044042e00d021000c448040599840b00b00402188420344d000c030084c40540d01c000c2000d03045040a0040c18019401400216602a21807080c0c0d50003000036005422201d605808100702190001e2401076a0360080000340d80c03440c051442c0902841c440c800c401491401c504084511240060126000c2050f0b50014440c1003000400d50b130f400b40401300c2440d03082c0e46400c0c0c504c0c560381c4600c02d2402c0440c04050305951603a004500c109510100c000c58040c002c91 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 878753372 1250 878752122 878752129
    0x101a030a0e0f1015080a120e0d0302150601030e0f030702031203010311091902040602030c01060e10120f0c0605030414010501060c03051e0415022e0f0f0f020a0806 72
    0x850540142554000d04a0501c60700003034100802c0c0304105004c03040c1403a6100d441c60b0134503c03800340480300c2c0d5020070124114950407501000c00c00f00d00b514500c042d0450795801960328603049554803c1c001c0c0b040005038090307100e50007085070903a0820a8402151000178101c4d07494201d400304174400c0c0140d101c19007454000c002a02c6c126504829118481500e40342400098139003d03000c4c101c104003d02c1a007004001c3c600041000b090242c3c02142c3e510380d0080c0c92403c4070b00540005c2c103108440d100344040c0f040c8902c011001d80e07060354001803109007180380c906121940b10900807c0c3d110a243e000a110b40c002d00a140f00d5801f8034420f0303509082420b04582207c0c424014140410481c103100e1010a20071800b808140080035180c03410403c154042c40e0864215a21800d01c503410984250101039040c040f0401d106002000304114000010a04058070102d6030801c1c4900d594003d40808410345400c004e903c01780b0ba50341040050b0310750815001a41c000c0204c4004607040401080d203504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 878754622 1250 878753372 878753383
    0xb01090b06090906010813060510030b0f0f180a0b07030617012c01060317030103120e100e030a0b190e03161202070f090621030e09101a030a0e 63
    0xb81c02010b034125640c90780b005548501020744004180041c0040041c0003c805101d424024444407a10070940780c614a0b00c41c0001100811125200c1945001c1c003420102c0382e44c002d42c000341e52001203020440345000c0c0c145030500c26640a4200b45114082c0091160103501c0141036590621442006c840c039000b40d030f42138800c01c0341d40300f080013411808040070032203244d83c030940c0031400f100108110769070792100761103000800840103540390000010010060a0b41c0b040803801c2c201d0800d1646c4445000010b250345250b0f120032018407901c1c03d000c41080c3c0d01482028205030b403142e0303100042c0c10450f21400502c10306458242500b898903414150182001003500d0040010001101c01824183d40798580c2c551030701900030640c42501d0740440c40d0718543c3c9490000e008400000503004e480e0030f4411452a0720044130388a1b01000c4050311000c01d0303000441d0030281c03800380c488040c90b807150622117051a10740e81c4042182c03041c0b40a0708068001010084d40190700308a001d1090300801e501154075103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878755872 1250 878754622 878754637
    0x1020a020601052709071403071a07020406080d031b0e1e0402040e040503031603050105030303040b151c0c0e06091501031b05090a1403071a0702030a0b01090b06 71
    0x5038440001080186490001440c00034a444c28800002c50446010344000200366504134241d040752009201c2014590100d5a030402c00710010608186004031281c030b007401780d0135a502c801000140c40030035074681d900524000d041010889000c0544008003c0003080c00540707400164031a00446143c007841007422010720301000304100908191661050081e14102080c10340264080c80001200b180f042e05036840ba40c09140a10350300d240403580303095200801ca88040034545808010310041c1c40010580f54419031100460100761280410032611400e4055a641d00803030b100a0160000885c6030803d012603c00c41144611a0310307030001e003208400031111160840000700010740b0200894503410b50100043c100000c0c2c818181c0342e50440c02c000c00780300801107000000d202d00305041c0011250000c0c1f021a0b16100240c202100007078460080303204201401a00321101c00d0101204811240c03580d50080c00ca5200c034000d0b140040d0648024400c0d40850f0745003644c402614281007003100d460 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 878757122 1250 878755872 878755877
    0x7030e090a231b0f0301090e01110409020318010c0e210606150d060b03041401090b07050711030a03090806090607020a020d03021005010b0405030c0102030c1b190303030b0901060201020a 82
    0x4580a10b4002e14101000800c2603410450800d51100d0000401004141c04d0121010309656981002800b80941d0750201614010344c0c58104c040c01d15004070b1064609854002a02583d40c0c1c03100d4400c0b4000d0000303006121995481c00c051200c6040d0072082c0f40c500054248c13038419641d0200745501d01078030319100e10000075802c60f40c00501246001040c120300440d148400908200d0b22540701000ca401603041041095800020f010a00141100c0010904680c80003072001415607500e1f102c541d84050100028440b0105016040050b5541c042d6000036001e4120b0b40340012505005002065601c81d6450600841001c584010808201c1620800c0c540e0010801c0d40802d509001c50103000b200e003542140220b1204420000c0e40340200e600824503c5070035511203041400301800c0400c0949281d045d9030003080504c000c01070200d480300c2410701003094204031446040c0854034825055400d0703a81000c140c2c01c040200340d01036001d41c41406003034a1a0301d01e030f030721144103a00700d02ca5803850002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 878758372 1250 878757122 878757161
    0x6100206040506071b1b050a12030f120b040509030d0507020601141003110d06030b060315150d020d120305100b18060f0705071505091003180807030e090a 68
    0x4881c5c0074800c00460100002000d02900c140b684482c13410303503ca44251004050019810082880c00100b00f4002e07090301080e03002e5901d0b1035039000c0c0106c2088861142481101c0c2c400150402069000d00c0c440c0c40050003d0260b844c04110341910782d0701c1100d01c114214544004a02c46030300c00078030b06060300e0503100c0030215031108004005822036038440c80d20415840c3c000101107018910b0107090207005640c0049040341c00c3d80740c010300005000700258040e81c0304015a044001c69541c03401d8101c0740d4042d4035100d61400401052103040442000b9402c10134049120080004032405848400fa00760750030001611540816019003e2911440062982c184034181e6094004000740c00c942c40300800c694541001d40301000007075007080c80709a40540240c01b040203012071090313640b003016100d4a080d625007190103000a00108400740c6a004142e0740e40001c581f151840c0204100082d0840801c98640c025498020010706001c0f0046000707070349c0603000c01c00c024024011190501030300700e0041d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 878759622 1250 878758372 878758381
    0xc04150309020301060911030405060c1812030c06010b123607031506030b0631090807060c1d0f120703020d0813060c0f06050606070501050c0306100206040506 70
    0xc001d450445020390b419507035048001b46103002c0b8480d035500c1400301c841281d01c924050900e0750805000820300100b031a03041040880e0703881704540a941c4a07000303c0d50480a002e44c2e401203443c500070381307454517020f21075000042005100000580840660140041810794440c0084d06e1071816a00c45802e1203118a540400d0303281c20002c1480707800546408071884990f0340d447c1d117000040e528031515422503440b001801402051014075501110a40b0b01ca00109035045080601d004143c010b6007501c0d11600d01e551101c009504180441d07900044025154030722410040014100b00600001003081c0d000d0142d014205601b90501002000340f0840308010001709002d0184080b1001e002d050003080340110042e61003802005036240600d200c3c5896034103a040a11015001e90411001c5c0006a01008009101e108020780e142c0d601c10404102d83e12141c0100302d6030300903280020059428035003041410385000020b90b2245030202c2ea8455541c03115507044c0c0c0c8641d800d85003d0020303088840002c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 878760872 1250 878759622 878759627
    0x18120f0801140301180b06030d030b030a02090405070e071e03150311120a0c0f080a150b131b0e06091305071809050415050c0a0315080a0507030b0c0415 67
    0x2c1440b050203400401d030344c0e041541c1220245510a4110780d500b124109011440c00c042003a401c0014503420200716005107100025515100c0444c001c0c41400c00304001010800f0038898140100b11a64401c00f00741041400681004425000746410101000103101d0042c800d00404641100510304405a681180c89994140400700c5140c5c2c6c2089a030600141084402c020502d0194041e20780440a141412090a110041a84101c20382e40c401404a070100314a0b040c884003403d0072450000d14000301d2404540c0c3d210903a00703584100f0b4504a860400c450041c1107099201c00160798890301c5555100401040b030040d055056044880c01c0038103440f80c40268041c5400c62a2401c00314294800d1240c403010400c3c0a820556a04c2e481c0c1d4244000c02030140e0240d0016072614800b4019460100f0803c50b0900038a0040302c10076403500c802c814402515a07a590140100000340c0700e500780075050290f0365124070310040f83c450b054a40080d0712100f42d0400d40c0c0583c0d005400500c6e00c000d07400003c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 878762122 1250 878760872 878760899
    0x50a02042102041104060503060a0501050a050f0315360106051b01020d060b070b01080a0213150b040803180612040f06060b0a0c020310050114150d18120f0801 70
    0xb03e8101d40d40301c002411300300208014200420302591a6581c0303240c1a0140034802440f40c0c862418480c091250709481e42e044425941d0198007803650070744030f5564160147c0c0c0f00c02c001c070b1030302c2e046814040c500001040d8908541c00e01b0481d202082400401c00c1582c2c000b4071400d00c2804e000030800d108002c042d013039040407031018007a05800941008180a0f20320201c0d00135500146101d0320000e800360070810b60004050040514402034030700c004140d00882e01100680d03210801c005d81d0f900084041e01c945070300c0240a050780a02c1540c40d01d0711382c07007a01d640b40c0c00100e5580740b4030110685001c40746030050031580b00c2a064119031445498940c0c856140103c0d1400c1200c0087e15164045107000d001c80181221303c00c1030b40e4000d80e004041c018981000b0101c00c65125482c205030041c007a01c40d83c0111458903240645a1080e01c880102c1c126100340035880c0c03400b41d000c1c00c0c160803084441401c07110131003040c018038650000a40700c00d804c0c1c1e50641d080000e0300105920400410050001101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 878763372 1250 878762122 878762189
    0x1390c080a18080601081f0c080402090405030d0504050c01110316060c14070503070c14090708130b0f0906130b0c03070c02040e070609090c0e0d030e22050a0204 71
    0x400140803a101e040403402c0c074030242c1000c0d4070741d401f2006002e040e50b802c01e081c0034090003030403040110f0902440e009080010060019010340b200d04003142c2041001c0003243c6036031a0b06603003044181051719085031202c0c00d0100c0076000480003418495014008011148000340381c02d1000c40c40502c41d5614005055145150340038440bd0a0510000010030b000503c0356511070409156190102d00d0200c80c851490f0300058240f030380c0303854000150b89a4100d06600305030a820b04200c25503070042118502100e00174010441030914092080300c40c8072a40030343c052004141a0340b00795645280303c0940c80c500c2030001d801410004049010b90700f4060040d50081e00b545000500042c860300400c0a0f1171610041d80e400b5401304000300300c070a5008400c2000b03000f082c84203200c4020f81442c001d050990190903180700e098056400301c10540120360b103900e10039000d0400d26003c507501c3c554800c00c1070482d0f0480c901d03909000004500d4100e91084409944514002d00346803160044100e001010290 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 878764622 1250 878763372 878763407
    0x190e060904110a0b071203020c030a11030f0c010b1c050604031805100503060111030c031e0d0509030714060402010f0e040905030301080c030c060f03010b070501390c080a 75
    0x40e01c0300c0603103a60064402405941c4e42c941d5940040d8508240b288440340049410144103000d4592000804421184100300ca85001c07503045401c0208107046101d407200346103d018000400a220500640208005040031181041000001c2c0381c02032103c00c0c0b01c24028001d410100000340004e02900c094810300c001c15007c03501c42d0b1744a84c0451051603019000e2004128040100003842d80d000d140c90490b0350483c805542480e00300d000d895900c0c0112450414403ca049600700602407014041d21081c0107610b201340181e003421031105489074031000065510300002a29194540310004525006680c180c3d40e02c0c014418054044480d980308072a2035a0181d150301c4400302081d010400b55001c0c00741c2c48094561404000300301441e00964820781c81c0119070501020080c0c49000c400c1d0386c115081d0b440311690700c040601c2c1c001d0052050411060301000003032000d85c00d5541d00d210001400b01d1305810492140040381040e1000c0551032001000c4400810900082521a83d10000b0b02c644c3e41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 878765872 1250 878764622 878764643
    0xf01180b10090504061a0f150a0c0510020c07060c0c0608090c03060711070501170604150b1c060b0306090406020d0905060f0a050c1303060c0c02100e190e060904 71
    0x14036407003083d100d05940c1030391500e4941c00800044001c071000c107840104104c80c0c010031421114045186441c8245540b0150300c0701103095030b00740303005241038107045a006083c1c2d6191a0349000401c029000010041e03007034403905c400803440c00d0081d8820030303a0507040620400010b00e000001c540030b400003048594940110310103031205031810032201e40252400d80b40c0d03c42e60b060800f5050b00d0510168040360400561142c02c4200f4203d41c41c4040c0c2103901980c01142610320500340f0a150b1100d40c4c4450140500003c4030803007c1054001c02480d080d030700c04144040d40d6078070b0b602d0010f03000035141240d001c176980020a001945650040056a01c8244041154040c0b40c0751107040000440d2803c80c0e612811007080b220540700e00c2401d611158015034070742000b4488603460920241c1e4000200882d54404181c204140106101100507a00a04107820104c00340001411110003010044c01000710007650600346103826079010640380e180d101103840e6550b26080001d50880540305a480c15180c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 878767122 1250 878765872 878765879
    0x1e03040809040f140a110301090c05070506090d262e0305030903161203050a030f0e0307031e020a08160605040812060a03030c0305071401020a09080f01180b10 70
    0x2503000c1d043d200c0003840d00029407005062075201000c00001e00400d41c0501c0d00c181010034000440c20359040d030740000c8001030042e040b070741c0503217041c8210803016080307200381000c014620034005152260040c603680c8128141240d1001045004641030404040812703900c001052442101c40c41d681c604fca480900749031a00c8654500d008000ca500140c600707410000f030950203410300300720b0382e00340410f0200d201c0b40b15454500030707124144010340006c040000c009607040340d8500c03030f4000390404600c5d49410001040600f40d007035900d5010309000c40100704d03028050000031141010300c1c40d24880329005008c40111959915490b0345c070070a615645541010140745c08a5514451507110b113201d03082056032141160b10044018000601003407145030603002c1400003e074003802d0340c400554542415a02d86030245802c034100c02c40711500d40100d40c400325a1141e00c0303512043d200201d51000050301c0142c40011040c50a0303030407140800085a0b0700c5552071002610740d50005900c400855101c0d00041d0301c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 878768372 1250 878767122 878767129
    0x170601021c03020702010201110903060612031c0b0f1906030207020117072a03140a02030904090b071101110912070e01120b06030a0b0c09030a0206030c0c0c061e03040809 75
    0x1c40701200001030ba01040781011540c0900c82c14002c00780ca103440e10309107520b0030300003030b41c560006101c0c0e400b8100c04004001c040004105541c0b50244084005115150050171100109001e41e0220f04c2807810440c40601810200969540e05050740c00c44818217003809429000f941c082041281081482c0110207450b1088040c10340c040d519655444c07400d6501660160b07224a122007001ca8a002c80304d020400282d0408485244d4500707040c1820780712014503000364114000c0d4070300960828184031044c4200075480c0003042c417803d001e4440b01600510912318a00300c8a6418400340010800c200303104e0365142001d60f102c8070003905401c0301d08080e103c0100e081e201c80b0a80c480f040350a4400000800c1069004286500c2001540106034a51094403002001d00c0c01400740803c00100240b6040240c4083c0000648140c018003001c0c1c1d00c0c1483e042d054041d50192b2114030040c0900202c1c0900c4e40350030021500b244a403014103003911b0711006c03810380e101d501c0a001204d03006410001e0250725203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 878769622 1250 878768372 878768413
    0x20f010906020a03200a1b1208270c190b0c0c01030b040e0c19120b060a05150f180406032301021c02090d0204110705010e03070317060102 61
    0xe2103a0000b6842da11030840140603101c015070000c01c481002410701c081210071100390355400c201ca21300b042205015408180750080704800c0035000440a0000d05582c5401402d000c4c001c98a4600285c040c403208002c8052040c843c0000c03600c2a004104002103518042c042a0425a007070840c00001a58404c07180030594001201103180c1c1d0022060500950707050b1003209090501038030244806000030a80c2521f07241c882800c24442c00302411000c200600c0600341101910011048185491072420a400382e40022122a80300d1175000602082e982000d0b000c90a0140e018040a400c00e04507207442401c94011090094100000c488440c500382d0300c50040200641c052004030103a090007031501e12082d0302e510a079400360381c01005074640c03c800b00c110f012070802890900688418222000a05080401402a41c0720382007070014400702c0205030007401c03424420b40080203051140001e03d0b4580c01100805004141403d10400120700328810440d406901441a62060300d0801102003102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 878770872 1250 878769622 878769641
    0x10b0a06020a170a17090708070b0702040f020c0307080a021015060809121803010209190e07020714061b07030605190506330309060f07080402130c020f01 68
    0x42e44055010800e01c601e0103640700000c5184101d01c3c1c5410f01460001d04202c00500311600e8a149070070004516960070f02c454009814900140d072250b0350303940807600060300318160a91003036107003810180401c040c078821254204034010145040224540300ea0040360802c01c03903001907003c3e0542ca00c10010251040181600c00302c1e126109260a10304010405a03000304400100d601c40c400358460000c0310703011f07120400d400203904031000d2614004a806070080000c02604005510202d41c1c0050803800950144d81440080d4940d41e41c620200726030310000d07841182c283d8900003183c8031280c00d10400a1070024102590746819029914080f880c4c0f071542e84c0140c2e1001da54400b0310803c000c0d030340049a044180d0400501c0141485e80c0041d42c03107030050301c0340c109000d4000202c0012000b80c81d208124030840007000750b2280b070061a5191100300840d0700140781d000000001d640d00d405640710300d0003690003801c00c050740e002d501000001020403021000640c441c0b040569400c003001d01468101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 878772122 1250 878770872 878770877
    0x51c05070e030a0506041104020424022404021302040e161e140c160311101b1203020409090305040e070908030d050a1107030e0108060a080c09040203010b0a06 70
    0x191411400003071032900d45582140c403981101e01864041800040e0040d0440c0d000450881c0310200640001c000348100da22411200e80040032802c52020010307000f83e0200c280e070702030710112001c1200d9038100f1424650003102c1000705202080250504990307070402c030700d04040014030703154a03a0380c00d0450f10011502149020003418450f00c45c00d1340701d5011418903a003640c2c00085081414005400d884038044c144598032070100b18402150030811841001c45c11b05815101e5007a2241041c4c0c0f840f5956501050044450481c444a510300ca40c1d080c0c50300d8412050645580f80240e42c0d540d0520340b8030f0106608064091201003034840c424494200c1c0e0714840c1c1c840300da40e00d1920701c8078801c080740106044203003c4110b40400018030044100c602416100c800020941d507490401001000c40388a11848010041082c1e02059000001c06200503001d80b507100d81030f5501002c0180384815030103000401c1c0c001400301125401e00800040d0420f10060000c54988090b00224542c0c50069205100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 878773372 1250 878772122 878772131
    0x31b040b0403082a0705300d020616140703020f1905010501091a060703140a050c15060a09090312050c030f010b031608061306080115050a1a0901051c 66
    0x190b0144e007211682000128007140c005050904803056115407140c403c803805044042c541003c0c184004942c980c0c2400200c0441862080c0861601d80d00c4c100c840407000984070b40c00c08100c4400d220500c4003010f80445c0e0303c130764100400c01c581c00c0c0b00c0c0d0051902201944144041481024410b120f240d058000c170100150a100d61402c2c4103003504d0301030780200143d034500304d10f42e1400400c0b44180d4a4409090724a02c0d5181d40070f140480d41903a0301380a0200c50000805d4542800d40d00c4001800c0044030b001c1101e65941e000200ca1011100540d100ba9120f440c86108000c1c40d006504913080c21350082c10000c0da551140440b01c015260105e030000c1031a50004204803503003c01a03211400750801800035421440c2a4207451000408405c4840500c8070400001d9906c2d66000411101644101e006108242e99004114040c003540d03920051603107121301c000f09080c03c24401746021030701c500707a0076240c01c21790a040c540380b0384c065001e013030400108204254801c0310001802c24150000d940014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 878774622 1250 878773372 878773387
    0xa0513080d031a0d0b04150f090201080a18060e031b0a0209070512280c0305010302120d09090216023a0f020112021c060e09070b031b040b040308 64
    0x141120070710799000348221102c2950000f0368030b4100307500072090351000c0d0851081d10750b070405049041c0041d610034011400c004221113190f0725a041401d400d0300c03e80f074040890b00e50b0702c001c02c151200111164203810304400b1070008208540c1260f0029410034041c4c1f40f03003141c403583d100284442440408502d0303021040c0e038011801d20042295000c0f15919040d414071200b10050000c400f0003400808110b802015210112001c1d481b401c201c460b140b507000c0000b400ca040001e03024000901c0140d1103145140c803011450300000c10500b881918642c0c90300400d03424244102c009401c440e400381c0d0b070701848510344001604c50f08000d00d8050700003005150b8602d8413605c21001405001740b28031a5841000c00480040c44001d0044e11050382401e02c075802141d01c5040c0d4000f4042c034a00d0354117507070b802600c04081c1c1a840d80003406452806d260012243c2d62901d80507510035440c0b141c400425030400c00210181d0245041145264001644c42c1c501503440c0310440703182d00150801c0d01c4091001442e00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 878775872 1250 878774622 878774627
    0x2060f060a0f14090c1c020903010609020d0921120e0f060f090c0d120809010b04051f170312040c12150b0f01050a2a06021c02070c0b0a0513080d 64
    0x65034444601c8084924005c10400c50082400140c001b040109030003152101017550290032034005402c40030f44c115221420129480c01908031203009954a20001480307240304401c0d980300c5440d88940f038803200c913900e0142451a0060400070706800080c09007509000c201c0d4410310981b070040a0407003020350b080c184481c0c15801e283c99402540c3c0b05150395440000043d82c0c840c0d50242c000c1c0389040c101042d91300c0d22a05030141000c55281980646800304000a4070a003405201101f825814002c0480d602d4a458000c982c00106a20401d0b50081c004860005074108620b80c1c81f52148402c40c1d00683d0325000d00c0c0780c19407414000c0311300d030803041340c3c4250740c3c02345205441d00c00c40102c401c414121351140010340303288601282601040f400600b80001384c60620403102d041c13070003031a0341c2000c9045414030800035088035804540c44a5015418140c82c07000740245c1d07440076001800c04120034a40203c003032031039100f0802401840403d00281d0028211012200002c2c02d13000c014150391900034100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 878776978 1106 878775872 878775889
    0x1181401062304031a0417280c020108012d12061508120a200f0f0708030405130608031303020f1002060f060a0f14 51
    0x5400390702007600381c01c0300440403040070080c140354010702c6640324500c0007070025240245104030340b6000c03404064015100d81c82c000b06818510f465030040f03811000c1c0e00c03040c0b4071205d041c000b0f69020181904000101c14505880c0c0b600403036002828440b0b0600904d442000004000310700d14900f00440480540d404c00380c40781c01e0359240c10b0404140c5128200300c1e0700303d0402c45101d0007695079214240541d440c44024101e040040000e000c5950400e810790800c02540740c20600b040f842c041e200d4000c400400c000b9103521031041d442c40345080c804c50602401c2e43c0c007804081040c00c0b008400c1d9002d641040f1031310500c45482507040c4019107a5604403000c070f80400509045211039140b401c0782140c3c800e695144100010004011600305046c50740005604864006180610624002d60344940000c00945904c5c1c5c8802c50f50000a42d250450000c001c0d054040c07041501d071078240c = true := by decide +kernel

theorem cover : BRFrame.Cov 878597122 878776978 := by
  have h0 := BRFrame.cov_init 878597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 878597122 ≤ n) (h2 : n < 878776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
