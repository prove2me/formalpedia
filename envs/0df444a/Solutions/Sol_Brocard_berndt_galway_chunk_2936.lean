-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2936
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:05.264976+00:00
-- url     : https://prove2.me/submissions/99872c6b-7ff9-414a-90f7-a4d62c60c225

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 527877697 ≤ n < 528057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 527878947 1250 527877697 527877719
    0x1505040f140912030c0903030d1a130915051f0807050f010c15050a0f1503020f090118020f041706040605011a0403021323100f060c0318 60
    0x10300d2400e000009164001154441c04036140142a480382d64011030440310010303808030407258041201c0d16015200c11a800009003180708400b0020300080c20507111a0703500400b08172450304007000f02c640342c51601010b80da40c0241c40c030040b00900f0040e003030f40d81000d6010050f0451a4083d01801c81100c0305410b00c0500f00d88000f094000001c5640928401e0046041903441e1816220007403d103050445015601c0100d2044810000030307409441d00082008018640c100c0355078440800c2043c0120080440d020104550f03d20099106a5600c074081f03010f800d0918940741a5845a07030421024540c000d035600c00b030341c0404480b4941040030007000861444182c13030080e045d1103203005401c1034140f07420602c2c25681c042e04000044042904048004c5c500c041c112411079505688081619410039400001801c080c060851980c0c9504074507048103000b00c40992045805091880c403c039280e034801c4184c0000d074043d581c0032451040f000b1010078024180c0f088010126410100d0842d00e40300140a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 527880197 1250 527878947 527878961
    0x2060c010606020618100b0f030a030302190314071b02120d02010e030910120e011b0f0f050403031d030709020d1a0306070c06020c010911190b0904150504 68
    0x5265911202407100aa06021517600f0901c1518030210000d4042403540e101d480c4501008046540c2da1416881a19004800350150900034107891a003591801c0181c003942c00036050000b0307034200d103c2200c4820700911441440c1c40360070616102681e5050b10548000140036050024821106526001030307907002d00e410a10b891140140070000c10300c810107800c0d0382c0100c0c500e500039041801501610748500d0151120198940781132844080303d103809800400744010480d09650805170000800c00d10030184459104540e500c90310000c0345504111000c031a420300c0718001400411040021a2195641045419000405503508012140007a01e0030240b58031071450150040303102c51018031140300307003691143c0704991030003814944400241c45d150010004e0040c082c3c0010500281718055040c0c442e403038a264000c02040d82181401e07100040c0d0791841620412007100d00d0991422140100c200326442d590400741844401810440a413036484102984440e08090003d0b80d83d980340107501c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 527881447 1250 527880197 527880217
    0x304170304080d260c0a050a141237090809040905060a0b0a050604050d0503040801050c04051005120c0a1403150f01110604111f0921020d060f06030206 67
    0x40d450425680a03071581c4441030101c45648107070404100c405c146000403204018142d20b840356036a0040d070b20640e050186c610406074001070200303400700e4080603849902d00842581c610400a50983c02d01310020001140107501ea00702800c0d180b6507154001c3d044100243e1203602040c0c145054500402c3c110be818030710603583c40d8041000c0c05142040c501ca44200d4110a03240c003210315007001d021442e10700c240e10034a40945042c070000000c1c458203000b030750003074103852009100c00c2c00c11000d094200c1e00a40180f500c6241204404545140100c040b03038604101c0004981580e92415180c01c000d030040c1c2407100070b001c11400b0800302e42a0740740055200e221500d044005400d469401d00000b0303010000c0703007030600020388030440500100142003075000b0b52141d000c0d0781002d40800403441900d0800046202409841c000500b041d230844885020380b454002c2c0514034400540e80c0d80440c1443e194081d401540e415251000724080c2d0308030b00b640410400010616540d680c1c04190b4680c4980700322 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 527882697 1250 527881447 527881457
    0x50105070e090105030102042d081204031106030403020d0c0213060b030a1a012001020909090d110705060703080a0e160815042001090905100503070b07050304170304080d 75
    0x1d2540c914218850741d0140c0820340086040c281003420b44102050710203100c0011032503003058940075400400313890000c2c1080b002621143c20740c0c4010350b029a0440d0000716810f040410050000341409400c1e00e1045405900826483d03484d84030556411003e810305a07000071400b40305010f500854010f441c01131115880c69503407860b124011404580c0c2991000b40c048021004440d107c1e82d00144030300441030a801d240818a801015680c02885141d441e00e400c901001d04202481502240244040815444161011001881da00d4442c1c2080c007509901403004d11160001c80d03c14031185501101c01d58000620702144146030345480c0c03550f24034a448205a90043c40000000d028400d6506260102d2104c54102550740002015803864074251030540a003203000240e1245000e100100000607003003000b41051611007020746400d0003003074040d1044403000210402e20758100d900c081c0d0400091070400d401d0401020026500c401054a540302c240404521600240b0008c241c1200036191 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 527883947 1250 527882697 527882717
    0x21c060e031909051206071d041a0405130b07030209040605030105040f022404121a0103030e0301110c151f0909140c1806240c071212030b060705010507 67
    0x10080c01c10465402c091700503490140e040114200000c0d2075608031a03d8241980b0841c0400c602045906500c1d45541d40f10341400d01403903180c03070308500c94455240140d809100b6640e0b909201481e0b04203901e40184280825000a4003507031095000e450300c1c039001000496455622340001e8256042520250399507500301c4842404c6141c00d211403a20f604c0103508007285d900422001051a0090b40714443c12202d01110500400001e0940d420081c580741013040700325612410014a05a101000140a0762030321400c84640414502680d000303c494130f008014007580705c940300904010187c80440800907003902c03440c00300105010704018080104000402e00000d0625007440322903080440c0494220341010b64403034441c4040e00c030361304440c0380c0b42d00000e0b140c28000c035140300c0448208032088084080a840b040040c0c0c0c006208241e800c400312603066417a548100041000940020079403403640010201150003500b1460b10260001c049c4c070704102c156151107094070811284840000c5002c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 527885197 1250 527883947 527883997
    0xf010e07090f0e07091d0130020f0d020303030f0a0c0306140d1104020c0129130c020a060207110a0b0313080f041208040608070804021c060e03 63
    0x2001640c80055854518400762401c004502c00c451a07018850705015003d00155601d8040e0a81e80c0052125200981c80340155a0590507210020b02401041e20031100d000800d04d8001c5820303911070000920b00030500041a0f00b0050700400840b011a0011002c2c4500000369400340051441507042c0014040360380382240802080765061b02104d400d142c40c1c50002d2200240415416a00000c103403100d14404855003000c003010600f041c0080d46c46800010010001001074001d0034401c2280c0c40c051074014130060b22014030312000c806043e042103580c00004007205141c0c11580500c100e0340151030a1503505c2d10b03060b090ba444654143c0f05541030350039002950510700c0980000f00066a074603070941c145000250301103c04101d02410400c00400d40014482910b401c0303c0041c40603841407402c040b0f8521f001040c0c0e4101e8456400841c0582e800541c109005134903c602c15640240440b002c07941c4020b80810700d025900c016102d2540c0c0b101046508101000100810a481051280c980d12810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 527886447 1250 527885197 527885219
    0x40b06070507060305280903020f0105011206050109050f04020d08090a12141209040b19060305090d110d030905011e050a0b0d3201020f090f030a03120203060d06050f01 74
    0x98200c003041c6200c40a443c80000d0f002c280b190b004070b021b05020840800a08049180065105004150f546401c00014a800704000e4405c40720f032260388103100320303aa5000c56008a92048844030200d02101000030010702d088001c01004920510b030f4681014100000b00711500459000b01503c0c1941c0c0340600f00740500c01781e13082c0704241100300510320166440015039190052410f414002c94480002c603295035900c0f00900d1801ca044000d10782803030741c0d40134010003921091703810b90a14007918509000d55407203035aa01c05e17801d030241c4c010f00c4d00e07100c001411801010314501c180c0342d9551314121031403144c1810080c01c804801e900c601107030900b42482d0010480c1d02d45642c0b00e2003042c0d000c18180006440104505540c4460701c062183c074140b0b81e03004030f984010018001c4a03940f0010701443d013200040c02900d5011001d0300c0c540c3c810a441c200789030340c5103040100a40411100c207840c1c80d940c2541d070019680b00710007918085004149613201402d03150240c5202104046204c01030000112132 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 527887697 1250 527886447 527886451
    0xc050306040c0501230c100b0907050702010819230705071e0c1a0c1b06030a113c0306180406140f07080601020d1409040b06070507060305 61
    0x220090001070805640b90300320103020b4803030b16061042808034000790300c60130b02203404243d0510041d2a992094402070315120b000200c3c920801700c0c03803c807022641b0306100e001a8802c98482c5c80e800e140941640054034420740007800988901c2c808046076505071100d0281c41207000c2c00ba142844850300e030700c042c40e4104a00800d030004102091201d10040b613280500943c4221002c01051400c140c02e00b410039240308650899190045a0240700541010f842c000f46040c102c0407042e01c07403520140700c4883d03031220029003443c1c0c0303c2024800b0a5004034254040c041d800110f0910514061001c105601c0500101602610341016040048240041e21400840403003020320750519503e010b0002030b034070522004132090148280800075082201c181e0100c51400740041030b41c10344c2e14201c0034500d02060f084450a000541480100341306500004104038942203544400c00e03000141c1010300a0742e004404820341c0103455009c4400c1b503469030002015502c2c043e2018244a604004e805020741c0c1c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 527888947 1250 527887697 527887699
    0x41719140715090603110405030d080103110105040b0306040b0d021201020409050a02160b070c0605041103010b0306070905100509120c010f02070302090c0f0c0d080a0c080f04140709050f01030c05 86
    0x2401034403149040d84090035200f51340b0f46040008520015405081181c0540d40041c0d801d40726a8410180c05a008514036040b64400d0001c50340f44c0c202d100c01100c0d5402240714810040c0030900105c2e005140540006d018003a010341300340b11244080c1c00040043c04982d036008440d0358000f8080c08510b0241c0125036001030300f042e040d4a00f255a40214070f80c18005032000c1d00c4107203010302003410148100ca0404034907030801424059820b29040040c0103005000149220350700e041308400c41800e01003031052040c0c080e5169101190b1a2100380400e00303845440c000200308080125440c166610720500130b901107070702c2c0241003503a64130f00098a41055501200e040d90310010003040160380b60804160701201d8412100e440b0140a441e901c00b81c0100030f000a210300031010107100550b03108503500e1185400007400c0c00011803400d000c1c1c81072242610204284042c480004001c00c00044400700f00241a404035840b0b5581c6503078010071180b0a40303900141035039201c01001405a598400c40142074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 527890197 1250 527888947 527888969
    0x13020901230d02070c0e0c09040e0a0f060b2407050115031218030f030201090605010f030c121a04050a020312030c1c110d0603170a02030417191407 65
    0x14150715200c4190045202041030141c00082d42c03020000c04401400081c1b4071801702c1240b50500c0769908500c1e0b0010a100e0b40031781c2c40e045094224003c005540444d00d80c00c5050411050b600740ca0b4000138060381d540d07c0d6040480c0c000b5091402010305402a52002c81000564440c06c3c41c0c5409400d42c1c1941c00c80c4080030074400800d2000ca0301c2c0302961803501c2c1440c00d0150401010020f4003400d8240c0d9400a040050401010b20a16070103411500c8000c1c414402049142c2c0c0302c2d0b00303000141c000750101510000401c00b0610034030a408813422141d6018050504c08241c10f090888d8449030f048501b2501500309040b04000c504040102107200180d0030062811441d0200206615004142030b040e80041c0d0008503004241a5622044e040200d18401a660300c40046904016114034481107038a00c1404090310700e116414002ea0b410b42e0110342c041c500c1c1610340713500c9018014002c0c800c401140a0307020550884041c03111290f00c924810018440321482d854007890030509150b0008003102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 527891447 1250 527890197 527890247
    0x906170601230c1204261002030a060e0405033a02090d08190801081b0f010e090c091e060a0503040c090204060e120706090620060106090f0815060409080913020901 72
    0x40d1b4041104c41100306200c40c01a146ea948000c52800b81919600200600b0f200710300384824448080000d11220103000700301009940340c0b00745c142020181010b0755440324002d24107202d40300d8290f001043c103040020b1a1060f405002d44130140310b80c0c013180c0800c00c401d001002b0500c0907030300542c8403401042104054407524440c404410039400c11044054403d0100c03044089160b03000c2c000189420001424121092400b4103c078034043e03020160340c4d881000f074003080501a049100d4804011788000c1c0556060001c40c1d641502c0582002d0022504801580c3d80441c80c22964409480109003d99501c69105001c0061080d5450818181c050f2034104600a01200e50004c00a2003241d1203460402d2034040000364030700505000b2070a14546010362400040c00036400300041d816154000e41e014001641d0b850502d40d1000502c68207041052179100248247c82c15030320015070240551461840c007156000001c40d180101c202c8042403590100308180c255034071810b000084c60212401d050300e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 527892697 1250 527891447 527891519
    0xe0304170c0604030b09010f09030302032202030304090b060d0c08100501170f06010201020c0f01051f060f1b02061207080604090c09090201110a030906170601230c1204 74
    0x15200f075020281c0107510490104109440941c0a26000c0c02003200401c4008014540140a940103641300b4000c3d41c80c4402c40c0362002c00c400e03070700142542c3c0180103501d0145081d0284000c0d00101c01200d40c00310090040896207042c03070180312a601015602c03805107240160355a11240307215045103040082004009000d07007a2000a030b6042220050342e4101d542c6c5940040f0b0191003180b00d141c1c01401000e5640045420540205001d003001e500c1f4600810b1007005c00c8040d10641c1c0c820b81000460416690ba0f006014020a00c00785100190492034081d407a000324815a000c2041c0003003081c810307400c000b4003980c005485900024200d50900680000751951a13020a8a000b0382501c143d550f00404210384c000e001082020584500380c400c0070706c99080141512100340714000124250101c80c00010018000661060105841d5818181e154854421068031945290700c60f28404000000080d03100b08001051780001202442da65420140c00200c001401d5500340d02c0581c108000c8111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 527893947 1250 527892697 527892709
    0x60312030e031e130f080d0327030e120d0306051c03050d090507061d040603021503060103060305070f0602120403081608070c06050309060907080618030d0e0304170c 73
    0x801e0464032441500c0103910400f030381e424851160601091030f034210000079201080200750341150071040c103440480d640b807c42a400c2d12081841c5107100e000c0300d41059001706906030000c02050003807800340e200340501801b28034040700380030011045521204000c00141d0b03043c080c58010700341c25a0602c0c04640708460648210860700c0005003401401b2401544241440e40109051a00117040300c070121390350240648124601701604c0c0640301001100500390409003c2d0b402183c1c0e0190100d5100d0761340c0c03844080340b504054405410551a504000003060081090700081c20501c01c1400c0d00d0740c03034140040d291415814030030107200c2c0e060000304003007865001501d004420349121a00f4501440c0341100b603521414000908103000e448000c01c0ea9030341300c3c0c00385105064040894a00d61100f503031440d41c0f1603482c0b285450580c4454006000010010000e10788082c0207011281041030340010901540d49a01c650107082d400440c0070080c28040c181260b40d041410406800d10102174008102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 527895197 1250 527893947 527893957
    0x30f0706050418020906131e150503061309063e0a0c120f11060f040611090405041203050f10330914060408030304060903020a15060312030e03 63
    0x600c0e40800d0341c0b034140020f541d40403100c5119005041c140e41d01804a514581c0910718091100e1143c1c40440b2001c0368104503e03c2d030b0941c2c2184e181c403070300600b9044044480303038001800b850b00030049441422240e0740900499040a200c0d40700811424007018000541440c1c03010700398501004071040a003194161000310343d0f91144414426550080d00c4410f580400b1a400d0092420a00c440c0c445a52a0301c4500417107118403d944072031700d070307030707200b51078640d250000d1f03814404541802c80820000740351b6520440307096542d03060303550a10004000050480f40d080314141c6030760b12140541d004040e403501c155940640404000e0690b4100741581840b601420300403e0180c3c4000c814140007e40407101c3c14000d02c00800c0d074441840d102407402080d4455603c910224020000015011450500c3c1524190b8280b0300045003166200d884441c0036050303100c829411350280e0809180440d1b220381208001e4000c000003c9039007441e501c0d117071540c81c0720281440109460409608803285c00401110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 527896447 1250 527895197 527895209
    0x905130b011e0e04150e04050715050a0203181306060206150d05060408030901060906140411190503100f15110a082b1806110f03040f0c03020306100302030f07060504 73
    0xf00305e22101d80d00901504160040c21590142e082000200b050000381041950270301d004103011041519401e545600460345141c0150300280502c0c03001d450f28030245600c85e030009141903d2100380c11401070440f90346403c00c00050708420100040441115000c1600780b40548003003000e400d040c0c46854440801400040c0110400000b0070359080e02500464042e00007143c042285659800c51840d01c3d48455100f00d0050b401d000e15411003005a4003503e0100c00c0b10030004101c41102c520448550744000c05482c01880d4031400410800383c3c144040c00605048102c41c00c1521075881c0152400f110742c1036070a0035a01000800001503103620998044c10041070000469100d018840082c118402841075009481d142c4200500b0721200b0400408a0058070200302c0d9907400690250203204100040740f030601c040001c036000a800d6100d4408850007240c0f4500400c0d2258002070422100303450b0b244528290710300034420340c6000e21151910802034001000d40710314240d8050641e0046204170 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 527897697 1250 527896447 527896451
    0x20f0909120a05091f0e2b020d0507030f0b0f090d0305060f100801170f060c090d0605010b030a110304020d021c050307051606050a02070302040506010905130b011e0e04 74
    0x41c042c42c080d900b540c096000007465450080940200350301d808035500d01038030015550505120003401c07c944403140b099108540498444083c0e042845244910b20080740c0200d125801d550120b80f05104240185114020180144600382000e01e8001400f0785a1a4000d02d028148440d42800241c002101c4040c1d00740440c2983d104000505150007402c003894026000b0910b042a06d41d00c584004e042e101d244414124440740d01007550368604c02412420415484400071501d0780310340b20302030401504001e04150350681c169540320160307a42a40806e035100790200601204e808980203508500b80172014050452a00d41c000071030424503040c6c064055034031030b405120060180c0d428004055002030840c0d64842c840e1801941d500040e82510310004810039010a4a9104108075000700c40980c1c01002e4007407c2da02004018000640781a040c010311200004064586008844c0c00c1c1e40b29440004452400000141a14041000c1188c5e02d034a402d05002070641c100509406980c4190b0780 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 527898947 1250 527897697 527897707
    0x10f021228021237020a02031b0109050904080415050910030e030702012708031b070501020307060c051306030f0506041e0e0316080a23030c16080f07020f090912 71
    0x1d000344d0804d030211440c840110411a6101d032640000d8504000d40c42a03085501c0d000046030090202e031341074405d00f400620940d4080105141810403079070064040c400e000d280130f6641c44c483c0318085112084030042100403d0a05003841c28400309941e8609600301800045050941551a4030403d00020306200c98038840b00a05420035855001c400704086541c5013181d1a03200d125903a80001c12034403102c45810800c4448200041048411110103030000c40c1000c00580e903000113000403000c41c6041041c04e00108030384441c403a58120061000740c0300003803107400d41c252000a44d00e00a004500450405112443d0341707615040c0e607007450380711940000700e1014031041d00e0308512945100b0f24034510501445410702c28681e0060460052585505c5022402d80803195031040e54129800990f1205000103410a80c0300e0b0000c2041a1003001e014007880c8196660700403580107180208909000803551804505040c0c040f8000103008489080191912004095440c4c500703e024143d03210010030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 527900197 1250 527898947 527898997
    0x8040506070f0606080705040b0d24090b04080a0807020c0a210b040b01181803050a030b0306090f010b150a180b0c06070914030606010f0212280212 65
    0x504540003d51240302800440d5403080742d9983e42c2458080c0c144214504151500b00d40703003280d81c1ea40d407140d01003c0040141c0400a148160012100c11070071003580301c0420030001605030b104030340715610500c070854a54515000c01000500010109419940216504851582d6008298044840c0e14040444201d0188c0e00c070021460640402010101a0001e000401080c000c80e18180c0c1c0684000d01e5404104960a000355020301b82015174010811a00c8004a482180104034500e0035050119002c0b1007080801d14140b0102c65454282d001540144003402c028095101b05d0141220102c108101542039284207208105ca410280140c107007a03584001c40940300c0c400100054000c003500c6d8502e00420302d85031101103da0f032000032500c0d80c0209400c80003140c0d10781c410101800501180c0c1e070703038030065601e45050020102035100700051010b40742c02c540f0045c4048441001e461010141c540610340c0c02504000381d02080d500140001c0303446c81c06d401c00740d50f041c07140380d0030f1202c00c00300041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 527901447 1250 527900197 527900213
    0xf0c1205061602033a0501080f012703051e030901091509021f0e0306191103250519090305070807061d010309080a1d190608091207050f15040804050607 67
    0x1600e40a045c41c03d05000141180001c1a08458a03049000038800c8007000d0242c0d10080602d48071002036100030200c2c50001c2480380e005480c02c50590201c2003d070314000e00d80fa000d1038208540d011005d81d196180c0004001d1582c030104800000316405001e42181a400150564266040440c10844110161030410320441400c880c54001405882c21400d010345030b0254580c90026089240e420003240340720645901302100c0c0f0413803000507403031078503820442212040c002c80c903201810010144a402d06820841aa100c1e0a00f41070711290f0806146280090810280c0d61000307034541c00810041018540200c4c0c0429401016540c030046016803100503401840c5000c0098180200454003651046c0c000510030440c0350008507028001c014241082000c0d1030f240312074625041c004c2c5007041183d010315106900440c0440548031000740c0c81302d801030650840030301a2042d600c0742c100e2816a010500c910200c2880410b0508001d290a490b810098411441011300070364002501c503003440401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 527902697 1250 527901447 527901547
    0xa03021c120216060807050304060b0a050405180709020a1e2703060b09010302060a0c0501110d151403060402100e030f03030924040f0c120506160203 66
    0x1541e81c61055460000d540d8003142246041c011810303000410820700506150f4031131106d558401c0d1450751607a5450002c1e040c210381c46600a403190754089410398681c018070f40709085901e0003003038003601c21208500c0d001e600d602410411784104018886a07a0042040c040348031120b9601504448844080300d2100310b00c103c90020f00302405500c425404881d070081c013148c0c09100b00788a41d03540c0c4410415605006c0c4002948180c0c204030030b401d080d001e0340986050b54003590001600e01c41c50324007003082c0c2d44601ca0b07507012141d451030501d0500905209100c003504254504d14086039414010913502c080240000c4d125041c805d5141403518490401244032480c0902505d1400c5040307101c41d940c98100740c41100c0355000307a200341c09682c001c940700d4280d00c84500c0c1c01c3d840c01f911a0b4540c62420300609805035420f050111004c50011103010700d0000c240d2060000b028145040004c882071101120103c40c2150020455521a05452210f5030b5405d0031801d4083d405066600189801800d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 527903947 1250 527902697 527902703
    0xf03070b0711010e0405190c0207050d05010b0118030b04061a060a0807030b01051e0d021b070305100e2d0f160b040602060f040503131503060b090a03021c 68
    0x100140786010003a030a1680180300394203880c1e0b448440c40e03460400050b91401c0320218407440101c04e604c40b2179820346d0014002a08640141c5031540d403150045441d40440d40750a4519a44401d10807003036503441881c40c3c241b0703aa4500d11940c20340c25540d50800ba0040504041c00031511110b03011702544c9036017050044081e00800490703848485880c05007003108112070110100346055164602c3c1d500030021a0051403180c15030803940a0700d01071090440d007003181e0f48d80c016a03080c803500600040140103400b00d41034050085c4030f00c4c2d15514026140c20f1884c031641d07103481e040284c0c0000000c40003840907201d140c8001280c04203400c41d110201040c55007040042e2034441c0001f460040340001c108505207a00f548040e0000507103a04070700405203d14401c0750011b9210800051030210801100d507001031044050302c0c03074814031071000001c98165401c250b80e21039181380c0c0c041880350544280d00090062081941c20b01909000041010390700e1701c80603019091203949a440b41c1c0c44086e00d0ba0b4002d038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 527905197 1250 527903947 527903969
    0xb0f060a08090c030c0d08031e2a0a050f0a0201090c09090302011103102310030b0f041506050703090f080325172a010213050603010f050f0307 63
    0x5049500280050000c2c0d40803051406440c941c0c0c905410045000b803211000601180d1814096a07114007540e88024400c101c5880300110005a8400c4131100318042d8058480c1198600c019892141d807149821080300c120140800c450903800b90008113442c044050501e01d56128003900ca400e0f40034014213103000b029101c1481002c1303580c02c100d070b212181150082d80200300fa811182c5021101c0e1000395481410604036041c104041400100c195402d2480400c02300d201c100c86401044008205015820100751a040c4144040c00c00c581820202d0701c04a4040c0a82d1611700081c030400e45c4580140b0040101c00240d1206150103203d50100a111818055603400c0d0741c0c140d0303180c9a030030600b161401c004040d490780440000c9085144641c94101c018003c2000c00e602680c1c6041e40038581c20800300f0117a284030002c40c44240010803020150000141c4da550b0103a2240c0321048981c0c010b680b045109000611109801000c8542500d400383c41d0f9119007000100000d00e03180c903907800040200c0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 527906447 1250 527905197 527905207
    0x10b030f010e010c030b0f0f011b050114060303070224040f170d08090709020a0e2707140904050c040e0109020a0e100827160f0806010503030a030b0f06 67
    0x800c05510450158100c100200140c0c80c4446085042e01e4080d86200d078440486000c03417004c0d00e01107031102d06d8000141407040342d8443c810301301c800e20308620780c040d80c199645146861114908000c840d40c006012005180307408143e5002030500311401021403180f81c41400500d071900c0c0d50908540150810052084400e640e914146110401e58038a14030a8001c05040700b507518000e0301120300070301018010b046160f0611425038001c2d0048030410040008403580050381d900c688001c4c0040205001140d01c00091680e0b0ba400300d840c025000b5420450024400c0e4000400f20090760140c0004840200d800d40b9112450001401188c104a400b55a040e00004a0101550041c0944041512055800e03602d2804100b610782c803038615071000c00d50324000140d4055090403c2075041c4204c0c10550b080c0704000c0d0007103141400c002c025a04441c00d6450500180c44600e8215000780040d0000b0543d070b6040001080d00c90150718400070906844042000e0750350340e03000240305042005040e094440d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 527907697 1250 527906447 527906473
    0x70e03030f1b011806020a0201021308010b18070215130c080f12070b1504060f080307020910240314161101050103020109060c1505010905060316030201020a14010b03 73
    0xc1e8409214403090480c1e40c42402c100c0c00303041c080d004d07803a610140382d0a46a121615030001a600406800045541c20450350b00311409032a000000361100c84000124038036000288100b03052101ca841c0b400d04102010000030940c001940d0f0304821048002c05030030349424081200056014400401170300941c040818007070400a82c0301034104180c4110f404484480f40e00b0041c0c0d2152000c0a4066000400017426101c0c50750000800a00d0107000010190750b182c0d004501201d5a40011005d900300003080c40039803409900040e04900070301c1c0e100c101a8508030700d694050810b401000a11800c100c8000c0516010390b01081c550011342c0d02d40c041c01d140002902c06454901750780c0d03c0204180001e611826501441380a050ba641078503980c0c075a0f410a0b100fa00e418003103440c100c5015058090100c510b450900495000f0f140485c404501410074504050401c2010b50030410501064982000940e81c00500042165003181c02c40c4018920a8440e80c0034152b9140103581601ca00c00301d040c80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 527908947 1250 527907697 527907727
    0x1110c03070c17030711010c05010e060105010905060405060d0902181302270a021e1602010e0d0507091805150106081012060e0c1c061a0d0b070e0303 66
    0x1102d108100390350348982c0b42c6922281480b140402826694024840f01d4009169040e404800c40c5050405100d0444103655050a46184400044668022100401a55802100d00b40240204541c1a8205820031012400314018040c0500e034a03030300c5450050641d1203041000748540c101040307020b607901e090b9546200b01402e01c0000c038011001c1c08102d00c0d0140c895262034850810301c1500150540b40d543c510341c003070340003c900021710020404c903841942050f04024280741120040b2040011404d0001408400441032402d00441d12580c01c000003410124481c803d94203840300000d00c564041c03103540742c9880c4015004000f0f20503030303040030303144411080b50354100d8865503601d240642c2c0b1455034880820180c40340301c1840c01d2007010203001440c540c20560001d280d00085504d0340e00312000203144080800e901d0320100c01007440c260240103441c0244660007a181e8448070b40d211505021aa06180f9207001a018240c1c207404075103990300c00c480d01d1541d840b0050807641c489080302c0e92124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 527910197 1250 527908947 527908957
    0x121c1d010605100c080a08070915021005150d0f0303110c0109050105160c11042007110103271104020a17010510050f030a020d0203041109100b090409030201110c03 72
    0x1c45000f0591a61a60901c01c02950082d281d01c0105241402a5510f050340d045d44042e116000b4000e46450118203907200c030003100101200c83d4010150380d941400407004588014002503071880b45d090300c0c0444c03601c0384042300d21026400710208a200c40607090840003881c41a1103504c1141000915000141054104421860003070340200455250000054071020344940704801007240440d405020800010301041103400107400858080c2c2061a80b0105a8810005a0541030b01194020038042e2592941160b0310084c2020420300503801c0405880383e400c000612600001d9110300300401101c1c07102da00384040c02810543d105c1d05000000b0b8403800004240e00035041c502c80c00001c0620f842240b01442c0141768480d68075080c8141c01100e0203030706c02840090b4464003040104500c0400e07100561081d4001e0709074100c01c0c100b1500700450048040c100c00700405205000b0300111541c03000311648008100c500260030360135864164090681648401d00104002c12040380c00403020000b45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 527911447 1250 527910197 527910199
    0x10b0316080114220305130306050f09030f25050a150f060b310803030402010f03020a0f110a06050a02070209010522230901061403121c1d010605 64
    0x400396407041d940c000500c3c80c0c100d42034842c0d40d18007041c0e52403070500e282241a03168020710700f90f0700d40343c1e803120b800c010b00000d5030044915582d11810803d14001241d441c90b008400400614a000400200c0e14114002c48042e8498580c800264100c405101044413581030392041c00c1d078062100d0350408240c0e42c2200c044240f461400d0084810821226120309000c4d80c18000c20300d400c1041c4d441a0140452840031114000007003454569604100b07400d44078010400e4400a42e581e00d01031000411000c82084084145801804085404d5401ca556440ea205c1d41d49401745440348526100351074554174038400b07800d0514107000d00c172101c0681d0b0018030300640240c0e00e0f0f100999a4500f40041d01002074800145030500010390710030014503401000403142012a00c80014920f403403401c00c110000d5540d80072683d5107040411007011420114100400e00f100500619a0003241201982c810100a81a01f200c10725a1900e0701c800390740201001c60040036a01680941c3d0401d03180280f8980c0501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 527912697 1250 527911447 527911451
    0x50106050109050f0303040b131806080c06030717070504150210060f03170309031c0c080718032901030c0608090610031101090504020a0c0b010b0a0917010b03160801 73
    0x81010309082c0f14181385400050300640c40d003458082a40125046100c400e1025a01400002580b46004403105c00c0c070030b0b02100014640d49420f5039a4074011403040414000d0ba824810071031415000b10062900103490301c4019981d030358008040b0b400740f0840d08028501c0040c5001c41c1e01040d0700240c17541000751060382c05c12503640c40d83c00c1d2442c400218071004010f4a42d8620a40011094801860300f00c3d030490112130a0000e103070f0380c0c070005907015a14103400c25950402000c6a41e170280700f00340c2080303060a2111076102548105840c80b000b034000070340025001d910100440314800c00c010405004503800401c1c80d40c403840c00b42c1c2d02d4829482080c00044450b804550b21a42c0840c00c5801140760745003840001e4a5503580000300401c600301c1c5414400941c60001c1d50f42c0f1140001e01c4a0740c15583e0b080001000743c90311224100040c1c102d540d4014007403041c1c10314a50000c3c0c91030181c40c8416595083c041c030060105014103d00c0400540601071880c01e0004e040b0f5402c0b880080d20307524802 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 527913947 1250 527912697 527912699
    0x1e0314061813050304030204050109091a04030e010c020f040c0e1503091b0301090209010303120c0e130225060903031805070603022508130e16030506060c0109050106050109 76
    0x800c0444085021140c0310788246a011490900502101c0701d0118452000d403410b150b038039000942240e00c02d030b000040c02915a10030400b007040d074101e01e202000c5103210b000154201510002c0c00c3c58000900da9060200085080d03041d581e6884900d8240d050090080c05030040d10440180800e0307001e0b0209005140d81e1400c1c101006542041e80d2184c44460010881d003140c1c511180200501c968110340c06559800742500542c40f8040c105010758002e4139180186420720010308104c59208045608111006100794050740d80c1500340038403900c02c9080542c0301d540c44d140e03850b0b20300c08800107241105242da0301582007001c1c80c0c00880400f130085c0c80c200016610144205004441c10600800c40d030800541031210074021b9000d031401446690000249045485000304040d4071010203a03410ba1000c11485011004140880090900003070016080c0c1001e0801c07402003941c0101100a05031603200190207616078105403240100074000030700c00e202c01802c0050082c0924080c070b03030000c0c2c00300070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 527915197 1250 527913947 527913949
    0x301020d06031208090a11060c03130f1401120f1d0a020f0f18040503130b07050613030504091a040c030b0312030702030a110307020d0b160e090f071e031406 69
    0xc618810781c0c80340b010300010501b07a50b03205a40380681f800150b2144050080114201c02040905210300c42c1920301e00c074050802010303001c486190380c005944c48400c50b0402109903031050003140194120480402c80100403200300300a086001103140c02e01e034041004070201c4034002450a25031740282c50001780307140000207104c410301044036116040f400c02d0305940c030703541070440d903036a4041c0c05501501d051015551100c48503c000340d10404107402c02040102c140202402070719080b031000811440760360500da902420718099131107041e4415030364640c0c40c0400d4039054914801500002c2c8104200c60304085d019000748100400796010b0702c25000c0c900e06025510007201e00841c0d481e001103040c0219001c0441e40e0b094840c03c642c0c0c1c00d00061203100e005865505002c012280314203420955840c04140b03448088603501c45032820095403049500310b0751201c110300c1e6041780940341d65010940c6c1c0e0100c00c0d6982c200c0f4541541400c5410100c0700f03250341c1c0c5a400380034841d02004c4010115203500c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 527916447 1250 527915197 527915207
    0x3b071d0a030206090609030106080f030d14100b0c0f0102040905160f210e030f071a041e020f1e030106050405061f17010602010c110313140a050301020d060312 70
    0xc000290043e0007081075050703d141c1003025010301e12005002149403a104e00d9504d0405c5600c100100d100c2d44041401c010281c0e050080000c40f40c448900d0260b207141060182c111031041d48030f04440031200040402c0721703280a000c01140311200f130000303565a544d03d81c03c28004107011980604180500c1120b400a188604d8440d61030080a0340c50703091591035455074842051075804500c0390244e60741d4002070a1001400076081c20f05489103107585407131080c02c181010350448001900050120000c00c00095004c2e050040807041c1c56024200d000a6480413480583c0840328aa9000302a042d041503c810b0158a00556a00a84c02030000c4c551307820510054900c10b45035680d0065010815a00e001d01500c40d0071150a9245444e0f40861045c2d81c0c0103114107c00c0c0c0042d40140d44917002c020350389400ca0300404000303902400443c502003642d0460390880c841401085208948090180701b40da03078000c2e01c00081c01000300215516001108104001d20300c6200071140340f0030400d110507129002d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 527917697 1250 527916447 527916449
    0x1905070e130b0d0201030b060424020c100207031b0503031c060b0405010e060307170a0501080d050301050603150f06040e0a14090a120512012705013b071d0a 69
    0x600f540f90701100c02d03030040d006001443d2025070010f1040c0800580c4280c40550f00120b5080d40104802401d1042c8009082078500c4215500881818941401d16a800078205003202d400485595910301000044d041e01446540829818440030038140c809039000400c0c0c010071200c0300c804000b029954213821140e40154407a050204054a55214242c2009001958418a2403900c4c01050107200c40030820910143c03680c40301c15a03104014402070343e0070403041001180c00e040c041d04662401e40082c1240c8401082c102d00050003010000d03480d11588290803005200801e1540c4231915030b62013101c1c016040340d014441c982482c03006409a074150803240d004240c814040c0000e102d05071900032a940801204204112041220703005d91a01d00503100e01800d101d0009030040000c1441d00380000e00c030500004542803528004011010700409a10000385d40c0043c00c1d00c0c041200088000140c06a01203107165901b0302003001400c41d40b0031942a0260003003282d5000c04101081030042c00b40305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 527918947 1250 527917697 527917699
    0x12050618120409020c011b180602030f0f0c0c03030318070e09070e2806050102241302131410080f06040209040809030d050a020c01020f06040b1905070e130b 69
    0x2003000300f40005a0a034009103020b03000c0400105a5801108085030f158007580707c020001045001c031855510290944140105000d100a50401d803811001d100c1c24400c0d802d110300d0036100044c04980d0a8002d009060f40008010b040d285c5034030f0b01040c07080a020715607412040d1270140f03141c003180c103081d6002c460340584202802421460700b040b642d005209801707000980e002c051071b24055101c000e03160280c01411044407011072103030301d01000a031801945129154000003016203042e1081046a56140d128081c0e503070201c10a6414000301d101050704680001d400da00b0a0041d1038440403818086000b442c0021401848075580c0c00c1054680501008244403508002d0106d405450305070429138116000e07240c4c940c6800c580000007032905580c08450000704002040f00c06d009901845000b101c10b000b80094100e1440000c0010b4550000800082c260750401002c6000d401520310003a6081050030410440c0e81003000c4007814092540d2103140c4240100c0d4050208410640152400104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 527920197 1250 527918947 527918983
    0x110f0109080705090711030a05040e0f070e04110405150301151806031a1906030501170a0f030212030a06050906010525060b0d08120a06050a03060c03020412050618 72
    0x414001080080d80c0003500c05401c2201108086d030001d0401e02c000d110607451134507000d60301c80c40c0090b281a051401030140c11030345402010082c1940d00300e8050510000300711000641240044118040c0380a1030708030035001005c4401281d12036510100a5059445244da03500a0b01d05900040f503000c0c0c2842c1042c491040000da040204901030b801c40b80c030100228500640c120481c40200b02d118040104176003007110170740c104106103a018841c29000d032054a0840182d5074919512030b41c0c6803c800f82c0200b85200c43e1142c402494404c0c0b00f25109003030243c100559078209a4034507009400f590040b0340c810000d03c03000c01d60355806081200d06031000440c04540c2c2496002011007103603a1084203440549d11400c00e00d8850b80e48001501d0214804d003401506c5034001051503032040d000420008245103080018402990313000d640340d044961208000c5101340c481e0000b01c1c0603014541c0b000a40d190000c6254041010100f0824450100304550101816a804207590f407074080c510f01c603004a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 527921447 1250 527920197 527920199
    0x5060c03010617060a170a0b0114031510030803040c0e07020a0c1202121e060c070b0105130603060516020d0207050906121e0d27210c03110f01090807 66
    0xe0840c3d50b0003984042c00400350f48500d640d0b090494603010000004100582126140d402003100c0d9030515409462008154031508008102090359000e040800390f45100c521000628800c42001c0c1406c041d546c050041e9442e41440d00d41445001941d020305980e03c4650800501c0310b620002e10444010f4001c803109460f2454800c80100d00c5c0300b043d00990704028014192034003a00100050b20450001c1741500c5810b69403901d01741c1c14101c014260340d0344074000708103200110b58081c0e401810b6510481c2d501e6078510208891600500184d88020002c0e0309000810005c00d4410592800740c3c00c90303401f0350f280d40105903001c90b128101405450352040c1e00c98081856410a070740c00000681c00c0305e0490300c054003c64010422030b90404d1a1401d04e900010040035001c0d803000c500100c1c5131000002582e640303800c2407140403d00b03441c00303480c01a07a100c42d10312100c440011442c8058070303000040e015200c0e4032420520710502078074a01d00d00070303804411601b103554441c1e0709880480f084c402c0035050345 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 527922697 1250 527921447 527921477
    0x1b111501030b06060912070510080c0403031808011a0405010902031014010323070912030206060d0609080d06030606051c0b060a080d090e07140318160f0305060c030106 74
    0x402c00740c000343e0413610900c8488030b2900c41c0c0c56210883c8a07860000e0403000e11b00810886010701501d080020480200113001c0c0011680054900b6170b039150a008007142505004402000910b42c8441c500c0c0d0300382201c851080791f1210440191580a44003405140c0e00e6031207101c168801aa003900d2a03a20407a0100040c4107201500104000305143c0800c007452107101800446000603909000b01940d0810b204890b0381000d41d480c000c00c00c805080c0c1190205860294461200070304190041219844200c20000158404040c190388411400e848200c00f0066000070140c0740011180c5500d05031022806103050468502d5840340aa00c1c40c180201558403000400c10182078560020f034092000300d10910140310400f900092590703208184e524040403882038100c060804010b0068410340501f6200d1080201c0382d2000f241521184040042d500884c0780c0a021034903003e518484040c04686d10800100365004c9074003540031a02140c464025954140c8028800c000100c0d010001803480c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 527923947 1250 527922697 527922713
    0x6010e0f04060f090f0b03010902130e07050a0308090103050a02090f0d0206040f0e15040209010903241508150601020a0f11030604080306100903080a0513091b11150103 74
    0x10050150002c161240d0302e0b00211080c802a410148039183c0350030402d00c640c509485582424001100280b111608507008640c1d04004001c2066459480d4441d0800c90380f0b04211482c01400301034110140280d5a0030407014640180045034000303030900021400c640582c1c006c0c0c60800800030b0200e20a81c4200341049a10210764104907082001840002201c0885000500080075110403070640b519286a85003050564140c2143c07003a44180034107119a40d002e4511025280c0c00700e03c0d900034803510300b401c50390202c1480d0041e0801d030801c1014021031507a48425804c40b10081c04460040c14403440b90b02c00300f0001c40e5031030300580c0124144000308007021503455000f03000f21070100b4007407038400c0880e09011088805590802c800028480300b81480301a4441c1b521321351800f81821410369035000d00a1040d10100009c2103800300741e50b2540401149241c8c0104142c400400040041c3c02585500000c8041c0a8010540445500014850100302d0780c82d007450460b220800e582c2580d0b00c01e51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 527925197 1250 527923947 527923969
    0xa030305040b0f0c0d3603140c0a03050306030a062a140a050307050d09060903110d020c01030c0917331605070b040308100803071a090a05030403060e0601060806010e 73
    0x1401c440b43c2c0350581811000c14000c41b468501c035070000c074180803e900b030180404590341c4150010107810810351450714004910640303038a42c189800c550700d880f4071000903d000340100d0003600c254a4403c44140380c6c8064200500c8040501310600048100d905003a650445195180500024200700c07030005107100314025070b8440b625003090780c1072000a01c0f0000884201910454110381e1782d240340ca0500da0408650701e041ca03a04802802c141400810003074a42103c050810b042c075031240e501f6101d00d8000e2030f0080181410001d01c142d6280300c0f03416160380d03d642e1003902d41005049160305010f179024041d400d10403030401e01c81440c41e48940f08100c9507080d0700d51002080020a01c101800184842405409a0300980e034650346403c12202d001c10200d1300e54002c0349254010800540000c00c03403806803080410140c41d800b02c517900d40960070708208240d0030040182c000054007000b00895584481c509801c200110b5045030b0300d885090740c019000b40c4000740491a101810f40c070703500d00941c00d18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 527926447 1250 527925197 527925221
    0x50f03030c030708041a0a021f1e050a05060f01092903070323090706030504020a150c0b10050f040e011b030f0e0d0912050f0a030305040b0f0c0d 64
    0x180c540600e0154142c15034101d84400ca804000029003080090300e5114152a160310008840749482a94500655141100c9070040b001e119040b104802e40070385548100b0120041c88c4002c04828400c03d01000100747c11a0b42004a40c0303004046842da09010b411060a4081a1038032200c00d0b041c10390300400400010030400206400d0404111142c4594000e5030042c4c071240c40100e19002c49021903049035000644000d07900d20700100b007005c46a00019905d040300d5072800c0028094686001090301e807441c40e08880c280c88010b001080e0195409200455554000c0464400b140c0301c01c4c0d00120182658810654001600460845a490300317522850441d1410300000070340011b141c003d01c00401c00c0d1500070740030070758504000406d000d06025088001c5602005444040501c0768040c000c0c02c41805011121087c100002040101c1088500054074000041754054010740c0b43c02006428122021220000440040307225440700f04d25590088814105140c140300c1011104401041e45010700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 527927697 1250 527926447 527926453
    0x9060f170f011d0f0a0309090b0f0301050f0403090b0f1213020d0c0501030c17150a08010203040809100509091801150e040c0b031012062414010315050f03 68
    0x218200301800d1040c030100d911200030340200c1d446604050f5003408501e03000c2444c25000044c200d0000b070f5100219400742c0c0d801760300004280200802248800c013420200c99059882c150502c540c2074001d884061045100750f0396180e401e5104c181c0c0f40d105000300116245210780500019086142c03009540b54802102c5688810015081e000582071544400040d00c8801d9514402e01855a05018500b8500e2803410010b040c0b450a543c014000380008200e400c51140709001e86805941d09004407005060303c40085d9243e04140c00d0415440d07009012080c4640c003c0700d01c8840c0c030741c0608140c80044074000d113000c200e80da44a034400f18250b0804840620ba545c1c1d42011400b082511301103101512074000d02c1701051516203000d00c1c3d480c0700740d04203200307c0c4018002c01141c202c3c81c20300e0400ba03a5100601c02041034461504801916502003610405030294081c42ca04500d4080160f0450f03041c500c101e62940b0350070006504640c0d000090621040249000f80804e007402c92621500210103412 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 527928947 1250 527927697 527927713
    0x609120702010c060e10090b180a02060c0313090615030b060702121207060e0c01140f0f1905191404050f030a1403040e0f0106090312110d0f030609060f17 68
    0x1005040c2621541c00a03038299991030520207102303034003022940c0007500c4060380450710507510100303a844074030301c230b000b0b1245a00045014942c04148195155018074010a00b19a40c880310010054010b41c0900c00341285220180f501c0c0c3d911a02549a0200015110501c2d18240d81c00f4040b2446040c003d822841c400d40302519007803a8940c00400000b4060007001503400000c2c48102c0c201240d11074000e041005031000803ca02c072190084030481e1660804c500d41e201010003030a50240501914105103401c00c40001c60070a030040010155007140c55031001c41c0d4080c00c001070f0341c0001d00c0c4180c00d000200a02c41480f040c102a09540f180110040844402c484190348085041d0110b902c00480c07030f000842d00304800140d4040075900582445800584d940c10300100034001e403402c0c032002e032001140b1440054640d018040d400e440c1c0ea01c007825540d2a0201c80340141441c40d8041d004800603140074400140c42c009845000251010f800a14010728070386401e4100c1020050807186d140c0c025402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 527930197 1250 527928947 527928971
    0x42c1203070c0f081c110405030606062512180e0703090c03020603070314070807080c091c06021b01180f0c0e0a0902040c05162402030f090609120702010c06 69
    0x101a2103c40c0480d4401d80360740403400108010b0306d15100700403403120030500060116035808101607500500c290f80d0540c9039030354081020004400800300c020610190030700e0f40184070000700095400d5072941c48000b64242c01821140704840c4a1003079200c04d07201040405c0003d0b100b40c00c075654075030091508501c0c5039101c0e000134516600603070780400400d9440703401174203503001200b4059005516050044036803074a01c4001e0071050009040d20341094000480607880d80d1204c0580348440f03100001c1c0313403881c045403030000000c1d8080b80340c07586403c54403802c0070206201401030f0b409460f84170b1107050001c1c3e081e42d07030001d118640582c1141c0e08510100302182c0450107035500c6200300845900440e4a1b2020700500085442c41345903041001420082152888800160524103c1e40940c24842c5001010a401690b01c4030912021081d0700004c18414a10380c0c404a06001c1e0403902d003580d01c13540b40c51440300c0d1795218071444c85d02e000c002844401c002d98018a4881c107070034001e02000c901e51070104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 527931447 1250 527930197 527930213
    0x1104230726090105010f0e070801060e0a03081605060a0b1807030b090a0c030b01030225060b030d02030c01060608011505090a050a03050105040c0603060f140609042c1203070c0f 78
    0x40b100119030395200010030030b0042050001004081d00320540840307043c6403030000c00300101406030205102190000459545400d031f101c000660300b2124242d281c110742c2c540c034215603a00800694007071140030b000c2419008a48036201c0314032001400711110b0015841710919544000f4100c3c03042c142d85034a4000710b611410302c1d0302d100b01d41080d800500b50317030241c4000d02100d00c0c0042150405206000c0012944a9803c0c20400795148001050840392146000300150182c440419018012070f69034600341a0004050000c00001c03034000c2c0701898a820040714100750902c10008140623050000c409507000b10020005510041d0000010b10707141c802141c1030340d40343d030b004171943d13075662007048244401c085800024028503d014802d0030304c1c20b481480300348402d000710841c200300d101010520385d481d84101c42850002901c2440318001c44e000445040315004101d003010500005117406090000c5a4060040380445400341180c90f424800c945d0042e8103917040b10706002c040000d9001c100d000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 527932697 1250 527931447 527931451
    0x7030b1504050f0103050f0303060d060902040e030a030209040f05160f0207080601030804091a012001060f0803040f0b070b1522020a230304030f050f03041104230726 73
    0x203000140c255141d0311b0000d00e0141ea103113121150340c0051003482202d580b510001d40d03109030031081c081400c1e178031400010020719601c203000c003075484002440c1c000a41c0517000341000e10002c0f80e0400c0194809051390b019070390704a0780403200750b824452019000d0f00509034030400710154411100c81c5a129400c0524100080e0000c5d500c06002007410400e03900c16000d409000700e126600713041c0b01c1c0340c8040041d002405840d01007442428603102ca0840c0482540200c000700400c04001003000e545441e20707a1640d0240c041c0d4420f50b0140000418003252100803a03001503442902440300e075480614076299071103110511a889101030b840c9a161040c0e5400f20280301d010401c0042e91490f101d58058011070f000340700d01314080312400001410002d040107599025400d0309101041d4003203101e084565200b00c14a000a490b0003000f40010300802d0301101c94103d000b81c408126840c00d1030782e03074064000d40b281c421404100c0100040d100038440e07581c000260a0803414002c0f0314160b24040c80000b401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 527933947 1250 527932697 527932711
    0x30216080c0a080a08040b07030b090403030507030b031e0f120306040218040e012a0203181f02010509120721030e0703030e150310060302090f04050a0203101707030b150405 76
    0x2080c01d0001f0700201140041d000a114203080204c9124200460000c0400802c0a002e1507907030130015907480e01980000011900080543c0c00040c070079240c1030300101445100c034146104081d00b0f06140740c800600c440e042d1220141d00c0d41195144c07030070040030398030000180e490b9180300d5041c01d107075449070b000f4500416107076400131520482d0b42d03d072110501408161030700345100c008851604e10380c020080754a107174264512064440c01d10004141400584511018600c241e10106031070715606501050141c21480f0a903403242d81c90784482200c42c002d170600500b42241d00042c841011880c15269240905603041c00326082c0104001903003440701980c0305a010459a03a0f032081c50b031600c075000844a102d2409039a0a40c206040705051205a50040000b40b60340000e1510442e071344c07800144c113615001401480149403c4042d42c002e50002d40c0d541b42d06441600011801d6544d03104078003200045400200084e42c5103498a440501016101c092071042400d15400365440380c0c05100d204610b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 527935197 1250 527933947 527933957
    0x40308040b071d04050411031f0c0309020a05330a1101020307090509130b150f010f082703030705120a02190e060d0510090606030216080c0a080a 64
    0x150508114080e5403004190004001250035801038183d1424400c5810040640b0b0001e01c5945070b180c00802c12200c0c40031145d15115000d1189030000d03901d0248116000c0c9904188402e0340e02130815020340f180004000d600240141040c0814200000d10743c44c481d2800b40d400020300807800788003041050022540a48040004140780400d0704008050110906031000318514642480010012509405034500ca010480c011440d001e444101e0340300e50941001407018142012480e40421209484a160040081e054100e0466016406481c003041e181e80b50514075a5689004807100e51071810540014801180000903006041025520540301d640780c0c01d59074194104442d00703c03007000f002d0300e05042c01040140381c44e44034600e010300040320505002d440d4014500000f89280140b00d000c0f10302503e132000f08142c6035058800301e01203030500c55040180c162628402c80c180d03c0b6419407144800c4000704a50300107504070b4010410303070081030140c4070103440740d58450400f81e201d8464880028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 527936447 1250 527935197 527935201
    0x3020111010b041b0216050a05040e0a0b0705071707021f110f010203070e0a080d0e0d0209070c17070b0f060f0a03030509041508060a110c07062d020304121505040308 73
    0x85d8042280c0403041e61000707404a01285000006098417a0034019a0300650b11100c820303016504c108402240142e004e4072002c46494a018000c0c030540281100380e8040c4111503d000100000d1400c40d070301280c02030040d20252005464030100100500385003020450070180c207514a0700240643d100c158920b400240c1d032818400c078001c1c142c0100c000414030504440f803040195110000d0217076028002c0e801c06495407103802d000909502e1020320f0103500003c0300c10410070010380c4945040c440174850306801e1014102c84000b4210f80c0601140140000341a8002c2141c040000740c6140d44400c1c0244004002c540d90400b040c03120328103038000c902046000c141509d051500b4060041c1341c101c00750000002502d4491582e41d1244040c2400b401035a94581284680ea0320345e00301d859074152041141d0341150f903540c0080603030101000314040082503210304120380c82d080004000d0002c1c1303907000310704007810105501644114a01c6c02c940005402050140240b81070154901c071b14040c3d12600094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 527937697 1250 527936447 527936501
    0x6150d09120201180f020604033503070203120421080906060324060112051006020606180708101d07020c09070f030e010207050304120210031503020111010b04 70
    0x14210000780d18080da4140031012000b000d00b5216245040e40004900c00c0c051030900104645104541029000c0e0b110f002c41020218170980c0c20a142c03a81c2c2c1b0707040c1c800c00044c103011114075000664000005030030400000492006118141d41c0240c0265070000300448100c1c0c06402c014a0340c840100030510f02e004003c44003800348580c903403055080d000341c4829414101014050840f10066010094455011900a900c00c414100310681454420025800e062030f1a51054515118070b000621640001803c2403d003c9009485030002034404900d80c0c4a03514203a684150080c83c4c0303446031159210001d00700000c0d2014220580e9183d680e011070b03042410000707040460200ea52805a9030f000c050259003980190700344000242c034500000c07c1072400356003902a1150482c0508588404240840c0f40038910444071103517071088a044c8030b602d203020001d40a454200d031102c40c403200d40007810805940550801c8040040c050000584015203000003022941c0c2c41c00c400340800c000e00c42c41051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 527938947 1250 527937697 527937713
    0x50109120b0a0518070303110c010309080f07150606030c081617181c03060f08060610050702091f17060a0c020109021011010b060304110906150d09 65
    0x6851900d120044030085074503918a040000b502d030709421960351001800c1c4411a0003412044003051040c2c40702d4550300d050007050301c241c11403004440d005031180d586c020341c081d228101020381e002440c1d03801c1501a036542c11071504801829241c0110b03c2c10b040c0490243d0b881031001070695910005504580518010542c00b002040220440707003c07020005d003d5007011600342030010400c100070080d07aa03d4580958000b100d090980d880c4140000c1c90210340c0141c0c452035180005a80822800b91343c1d00700280c038034416104050700d640080c008603040b0b08080c0c0d0f08801c07500250030001c1c6406410788c0440e401180883e550761000300d4942550035150200c4120301c0003011030f030294450749030000094540f5070341c01030003503c4440c0e42c0300d00d0108024001e4100726029600208210310381080000b01400501751000b800c80c0039480d10651108074034002e01035a0040d5048004240a21a204280402c2a00291607503034030143c00504c010040c4044c400510344015201000302c3c240a240c50311102c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 527940197 1250 527938947 527938949
    0x14070c0801110c0c10180303021005060a0303120b010302070b0a0905010e010606201e0a1a01030803341d100503041b0f1d09010c080c0901020f03070b01050109 70
    0x10b5512010040b0382c00c416000100c401c02050112050014440c0200040d03500040c03951054910b881121000000c1c1900800e1100100d201c400c003d000391380d070750020031103403844a01000f004141585142c00c1c08403460780c0001c01401e010304005140001c291134170380601804030307019885d85440301240408c10200380501000440c13884000d018403410084d0151682c0c00615054080c02c0510301103404140702005491407042c80c40018202c203044034400d440d22101c104c0c0c0c055511202a46055031642c842d1025181202d80003040d060940e101d0380410720b1200340c030303890721141103510030f40641c40c825601d403142107840b0b040d40320501001c2c0320715a50300c4440c2e844100d29102c2c01c0582900020150007000f100d0344140d00208200d4a10b0001d0401c45626010382c02229070182c1e0311502245540d5140c405118a00d081486102d1a0ba1614155400e842c40803106100181903a00421640d501b60700150200c070405005031051b04118501c060300c2c0d9002654144d0343c0c5808034004106550700490854 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 527941447 1250 527940197 527940221
    0x1507121d0d17180c0402070605010e0702030a050406030f1407020601170a0803070e010c050a0c090524040b0609030604080405180702030f07020424260a080a14070c0801 74
    0x8040450140c12074090481c00411101c0c04407243d140780c002070341c414440b2014148008100315220722190801c480186024003d2138503500500005c98070060000040d40c0360104203580e00380c42c2508000c401c90140c1a9098800344c2141c4942240001a04514106100e4109680105031540c98041c0c0c460300c0190421041165800c9103040401190290088030713486049410005856100c520040f81d00d007082c1c0d00c0290a500a02480f601040a00d24010080307403500300b010700190300c41c00c600c00200410100d41c044030080450707a003101810683c00c0f4a561850082140c1c0c100f00701c00c1c0c04203003402d808482c101c0b2441c100040501a900c1c119081c685a10712100411446203011003001e0766910801038044880ca401040d000115501c035081000c606440c01c6461031070754240307400c1e00c6502096004185601d2424050802060360020901c69101c00710740c0100481c283e5a143c0f480d45501c20400c1e0000c02000b40c941000c1c8801e0b0030002c200d550f1007000001041e0780380c508101c0c02c43d14450b042d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 527942697 1250 527941447 527941457
    0x807150e0c0f18071b030e030606040501140112290a0f0609030b0405010b0d030806100f0c081b060108030a0314060a030b07120c0309030315081507121d0d 68
    0x40c5901d80c0b1560b10082c0b0f210310020200300640c41e00358068545000400343c104907007940724042800c03d58400f20503c50080c00b070b0220385103916500704120954100f401610725940065910207074962143c08001c0c2150041440000c0713100c0d082212001aa00c40380e07150109400400007120b20742800800000100040d01d440701603981407000c020aa0640b6110203816400804003203410300c070081d440350000400042c280459009245001f80520704100e520300c0c4540c050a0742d01e01254020368401d4200500c03580c449000007800d03604c15031b06402c900082c0e4000ba05000e040c1030000402c0055038003030208100155225070001000070709a034401e000880f100e80c2150103202440e181c03180340c00140d030380c020955889035480f0002114101160380001c0f400c94200946042c0d9160182d005002003406994184040120400c40c101c42114030700c41c00e4925400110b150303020320000208207820240d2850080950347c50502d4060507200165040c60040301d0003940403110240c104402070f032018560501d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 527943947 1250 527942697 527942719
    0x50c0f1b0f01060e011d01150201110327060601140f1e0309070f080c060702010e040504030819090b0c090a030503070308010611011506030e03070b0c0307030e280807150e0c 76
    0x805031b05018424148903c02280c8003043c514000c2d08548440c90b00c1c80400c81e2649442d0746090b07483c004102e000a800c04203100b1281100030003040c4180305181c180c480c0100b5003c406544c60381e6078401288400b0400050062074a0034030f1450280c030002c0c00790346040303030ac908082c1c40342c1e0305101c0140c2c022205101e0340d000422480d00045240c0035964008c036031990701d84000b07000503174011002c1900650b01034a454108410950806011030103614a0a0f41440c29041c4a40c91030840384a170710050f0544090b10006040480904000e001082c8050030007030b005941e982e2620310356004250300300c02094000d001031020b19400055441000d542e00020b009042d0b41404240100e0000d020b6941050b03103c07924150b8811041088030240c65002c00303030450a1428411241c41e03908260748210001c5d040503802580d4000000305000c04207030050a0444603801c0e40a00040a01d100c0011100c0c4682440000003040412801d034820466015010032004880b46a0b03d040944000741240b00742c3c452a9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 527945197 1250 527943947 527943989
    0x14031c090e1305030c0f010c090305100203090c090903030717010e06010c03030e070f170601050a170a020d03030b030d0503160503090307080708120a050c0f1b0f01060e01 75
    0x48110200d030198904409180c403184000100b5410102014149100c00254078140680008500000e81d114600810205040010459400200788806000c3d81e0154080c400e8005160307009503001004642114408604040403031040070341120740c0d038515040401000f2405030419140f00f140b0f4809100f21207258140200b5040749480541218104580e440b401410103029a00c1072404201c100111003410369a21031500c01c0308521b000b940b0b43c40001c100380480294000865a0590348000c19042d441828550340301c0d05018004141b12143c880c1141150150b10b0721843c0d03080041c002d03078010845400640c141403411040c800e06c10b040182c108100005180070044022407180280303070140ea2915100c0403503155014002020740301540008a54042180f4a00100744000510381c00405545c1c4450f1454100ca000f194800c203180300410000e0744920140004080070b844102003921032444c0c64134a80d00c1d11302c40710503c54003030790b5030700086c00302d8260060342c20f00401300c2c01c0c001012000000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 527946447 1250 527945197 527945207
    0x8060f010504030609060f0e100f0c0f21060311190803190c0c0f0e0709080a020402030703021e041805040f0b0402010c0f0312060902210606040b0414031c 68
    0x103c4042d0059544402e444200a41900400c1401400c2e603010b00004071042d5140d51a00d1003c14140c007040c1c0350204c07040381034015000b0080c80c0e031490f80310000f41d4000c61105032003250944181250798503200180d5201402203204ea04051800f4a1000000175050000c0c41012200d1801051900341101d204004000000084504001540e08008845000a0f6050340c40000c034000040c42d0401c04000454208840204081190958550241140c032000300c1624502964040e4003066046402d200015091540085030880000e260062038501e205000194844102c1d5450806050009007080202c0a0070307100308840c26050010046401c0590b0741d45444062200700400070b200d240c0c0080c1c15a801400d0500c00150005480c40740c0c10460310300104011000ea126020070382c5400000300740000300c0e100f62111820b0040b41171802088032540103511840003040340b580444200004680d000303480b005030000309101c00000c0c80d00c0800c0820141800941d510104080c0c141e9100500074540c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 527947697 1250 527946447 527946449
    0x40f0e060c0906040314010b0a0512060a090314030411090c180405280c1b030f110f1b0a0b1314210a030801060302130e090a06050405030a08060f010504 67
    0x703614455a401081020800a0145600180c80f0060342d20300c051031150190442868151b04403038248d1501d450b4000c000720900122181c200310b51040300041c003410100d0380140310340790003420051402c15544601c105a07510888045400e00e01d0100140e17601d0504010751500050304080032418030703080c20f80700018a001162036070302c1252560003040c0d0301450b43e00c1d040702002c003491900c000400d83c200707001c029289240782c075800a006443d6150110300310307126848600384e055441c01703900030003c1e02c1215007441d413000e00070950095840e0300e100c0c42000c010485c20120701010450340407845000b08503201c01c0c19400625030150030009018112400e402e04010b407081c10741940461411100402e07604510303076160458140c00e4481030110302c1030014075060402d1013680e8103801607888000c21001c0e1b0042c14143c803a14685000140407000080c04120740c000342c48001c07200f401140303031030701429140700796416a029040000e04030700159028603c0c0b5440102612160080c03180400028510311031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 527948947 1250 527947697 527947711
    0x1b1805060f090d0209040f1118060108042d03122003090c060f04051c02060315370602030a080a0903030b04090c06030e15010e04080c1b040f0e06 64
    0xc00650b41e0180d40e192000c00c95030b00c3e0041d1464800d45024584034140350118442520200e071008810155490403024a18811040c11031601c225217a9000564189030054000c80b0700111405030754010070005840030005140d04400c1d07454041a03414081e006804540147c4081c9041c0548003000c210f1001034041165089075440e6a42e070340d000402e6007840728045229501c040c2c00503900e4416403100001d80700307650003117411810041d15444869660081218002c2d0003140074000a0b030b0010450a80c0c2e000704c14060000301100c01d111000c1420101c0c414024440040c2c440500c179144000b8401c103001070300241c0000c0d440d020305a07601074240d800040c02c81d4010f944443c111400c061207a0800750006102405c103000c80040391038034900c5000b45000b14000a841d02081c00c0740c00302c0000c0e1070354181c0711a60b00981d40764281419420481e000030301c29100c02101f080034001d0403000300400c0b85005021114065019840000c00007550400d2603003240071b6041c0249181610b10102d00b450700410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 527950197 1250 527948947 527948977
    0x1b01180302120312010b04060806090601080117010216120e0102120d0209041e091b270207020604031a0c041d1504151a0703020307241b180506 63
    0x2c0c1c0d04103064918030506141c0a0035001c6000001148a40d45014005441498031078102030b650707500070301c800c4041c1180c15030700080d89980100700b0b41524641d04885407040900143c581006446944000050400201c40d07012089001901d05a03008020110702e22091029080d20502c02c1803021940c042c40c09510791065002411180e0303940c551f40014800c0c9070900040441901c00d85180c00103191010041d039070340c6120309200d00128008140d4100740c5401000c0102d446030456004100d8030f8001e4401408543d003080701c2d102503941d2501400066200e90388560080052945040d160032019011082c100e10030700091040852070802210040728010760024640d4484800d610489000005d842d005494002c0c910050001b090720348050702c05110701c44600c20401030b201d200e90302c80c10070041c00680040c09001c0000b0a9600300e00c95240888883c0f01c2d03000e80140201003140c031480900f5611180940400702d142d03030890115426440042c00903d241c3d4030b0600411894444e11071105803440d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 527951447 1250 527950197 527950219
    0x19021e011b060915051e0a090b0414070b07030503040b150405010b1803030901170411030d030e06090601150c0312050c03010305193309051b01180302 66
    0x3034420040d41c1c501d1051140150319848072030500c40010440308409581141413100790501603082c03806054054001a1050140c1c82a064101020400e028080c0300405440e881e014001c01e20301040306001e14003c217101041d0301080350405240540303030fa100f1179134500b042c40104c1c0465000002d40341d015412039810300c000d40e81c400d180016290140b026030f074094540000420005d200d030018085401d403410320813449030441c004069803401354040460004407a102d10190030020b600c6041d400c2846401501007004401c0d000038185681c0401c60400240e8a1500c042d0900080109a40040100b000b50401c0c0d4142800d6940c05c07040780c046801030146000aa00c1050b1180c10300c920350504903001000300d4101200103460a501c00e00c0309459074400c6600074201031000d0250b4601c0c59901201c00810340400c0d141070301c280c0c610400480b461981d0114480c6030007244ac01011312641c490005098420766401003c510b680f03a4907103803410080c2d10312040c2400030a0a05800589030100e41d4400b080c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 527952697 1250 527951447 527951449
    0x301150309021302090111120304230a0605071d030c060c0a05010510050a230409060b190915050904020f0607021504030302060705120a150b13050319021e 68
    0x1504201c040250040902c40703201020520a030b0261444960980ea103451a01185111940c0c6501103055421142c004002040006018003d05010344a044140d00e41400c100840d1600f004162441035403501d440700300300800a941314028124621717903025120322080c500c1300401d58400541c00700714010003001a0107141c015040107020302107079002e070083c001440c09021880210406c1e204890040d2498100860724440030307840f441d0140c05200981c0000840036040101030080c000c820344459279140002e4119032541100b0501c00c0d2208a07481526516040c1a2021116005505181c0040307004050050756501200310f0380041d0119a50348140e49402c000031481d01c078400d0000c0d031064899008048844403c0e0203001268080c0d001e81c2c0066072181710aa8062099058601f40b0b003031000b0000b5002c0c4815408110340554905a5000481e2240d41d0100340794020301803000d020301d1000d0708004a140410491300c030782d81c1c003003060200344020b03078041400300d09103440c2c40b03c8000c02104c80b0051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 527953947 1250 527952697 527952701
    0xf0303051506070809030c0105070b1b1e03061306182705070303020d03090c15030603080a02031c06291c09060f0c02030913020f04061707020a0803011503 68
    0x10010010160b0f691032030185001800c580c480d070b8540b40640030302852000598090383c1654002a007001c0c085070103540d442c481e103400d200c61400c452081c440c00e00c0300e54400203240401c4004982c1d4121038690f2800d00c0800c0000340c0f5010000302d00060b0030700e10b0600020480f00b180d80b1131400b8920020601000c1d41d03441000302901440000c00c0c9072006640c08040c0f01002803800102c2e4069000d07a81a2900041c08400340ca010342c00c0030313210102a860820207410080c030b1540e00303481c1c0c42c0f600081b0103440e961144050342c083c0380c940c0010b031300c040340c42001142d9200c0c42c85c2c0b00c414020420424103140c02d541c10300784114802000084802c071407501180c240d6110885503140c1c00d141110b0718500c0554408002410101c02c02e4035064500740700315079490340311700c0740c2c000703005094004608012066003042120281d001d2285801c41e003e00c80c1d640c0c0712504401030b0000d00ba80342c0315044d107010302d48009a00204018096811540310090007400f00340114216410f40b403642382e0700c04e41e03422841020340c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 527955197 1250 527953947 527953981
    0x170415110c1903170c16080c011a010e010314010e0603030412031206080c091b04050406170d210b0429040b01020705011b02030f030706050a0501050406030f030305 72
    0x503405402c0003001a0301c40000150040740c40380d1100800450141002c0f074003980304488007129904100185c0c6000d8201002c5c0300102d031f20503d810762800d2950307900c40e4203480b61040490000d00c03908840b6285581c029407d503036024400c3c6030030801e244a02e1400304e5039407010322541d5901c40c0c0182c04a003090720107100f160702a103641c0001701c070f03142d4903840c0040004070040c0d05030800c03a19051010540c480702041d10110280300800c01141900c5110b0300c074009255480c00340d0b0306040300b000000746c03540303490040300010300705000c40703c0c04010b40784074050818010207844020050ba42400070301c1810030301041d4000f0170034030760700044040c200c0c40401c0040c40346100180d4075035003850f0342e081d0311043c0d504586032950303043d50180101d1040d40016682d80c80c16004050103e4401c42240306a8665032078078241c002d0005080301d04600242c040141140d00c408001e0703812544500800c100c150035806290300408080d502008218615102c0d40240c400d0300100804058032800421aa108a994001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 527956447 1250 527955197 527955217
    0x2270a0b011115040c031205040f09020a081f1a1903020a0c0f0f202809020d020403020d0b040308090601050612150a09090c050a06050316020f160617041511 69
    0x1c070b560094607c0c00303080d5400c05d124020541020a001248215450090303500701c03039054031230440710f03150303100c181c0c10b8551101000c41c0249030784a400291000101c690f040400080005140e645c07800d99650304190110080d100141401001000b0341c10f43d0041e24141d00700c0d00300c03040801364501c0d0710b040c1c0701845008c01c0c081c1074290320082c1c540451494000280000c01c0403100c1d50281600b003020804d40554050540e003100201141c01c100c1c0c11015002041c1d4100c8418005191640f02d074000756017894040c40c01d44401d1078400070041050340040280d500061004001c042c558500400a0558420034880018042210340403510408122426881d0802d00030034203080399840b1140c800c002c1207002000c1d50140c1c01c400300000c0e41d091000c0404140da8503070759240c0c0707140d0746c008a0003a07128211a51004522504880cc2440c200600c290304942003c0046000130034070300f450082c075840b4090b40c2210000c9101040c03000007885421840c4c24913056110114100000d686200d003140903802d128 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 527957697 1250 527956447 527956463
    0xb0f04080c03120915070f030c03020717040e0c040e061507050727020c10021c0c0905130e0a0312090804090501030b01060f0504060c02270a0b011115040c03 69
    0x3416402c84071281080c8507030302050440d164450705171501007000005840f001c01048180c0b868280040c4640c10030742c0306820b175003009480c0501c250740d480c08206c80f402c2c040f40803210128040c030414503400c0c035083d0003007542010681131a08241a4240160026200311711134440c0e807031401c10000003201510101500441503a00c0542c2d520b0480341e0140f040c8009101260800700400c182d0021407080c2d58240c00e500d03008040601c80e03090120000d52003c00503002c01881d031529602c000c0c07000d00401e0100c146a585500505140100f44800038010048406100d8204005440a0400041c14480709601481c0070142042c060a000005181d0303000c000d49840390010f170105803c00b968224904980c803903c60099141e998850440c0ca403000b4450f200d00041c2c0402c010011207100e00814408140000c0929040c0038181c4046542042d101d0001c1c0100481403042101070b1120b1301c80c2802d00e0100303003441e10469000030080b603118200300302c68142d16800342d40814207205180c5e6008002c0d42d80701d80c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 527958947 1250 527957697 527957707
    0x32404050f0108160e06130617011a0d02090402010e041506021b030114010b0d020f0415020c0402160b0c0d021201031101020304150f02010b1314060a030b0f04080c03 73
    0x45210401e80902501c0300364864042d00c04c41d03034490341d5031500c11034600401034503040d00c8040030800040005403131040003c0c0c8032030340850703403800c0408010f10020140e00005050803180c400100e03603903101c00865200e050100d480c6000f5848110f9050b03402036091800c08460001c0d040003500406225400d920098907020700424503a40018404201e142c0d00482c000b003c2c5004400c2600b6100045000c18640481800410803210004041e04c40600708a0000d070030150080c9881711690095440480344105411503c5800f98050205410300304044e54150b281525910005081c4140c1801c010f026151400000f01803000100544480310515103085d544c8140c8429640051402800195070880d00b03641c0d00100ca60000080320704a84610005071070550004005441c81c0c0c100e42101c0341513548031a2400066a6250b800c3c09102c06185000660740b040d146d0300d00c134080c40040260b0f000340c03003196007030010405c0e002c2820744c010036440001145944c1d6180400281c000e1001036505d500c804a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 527960197 1250 527958947 527958961
    0x30606060e09010f14060a111506011d0307150c0602030a1b0801211b0605180f031011120f01050907030b010806090705090307031505130803240405 65
    0x203000030074032800700e50300d825698940801500f81180c2c0c2c4a40355090162600f00d0f5110b0a0090151461850030b0400b0395041c030100c180d00e82407442000c000d14003500b4200c2000342d6076802444241e0712008103180301094203412004a640d032110350040c80203070381e190070f40c940b1494416a424524264400d801799102c1c20200d090301e024100304815162845001b80a83c071942d8400c1c09418102d0b0761b0514840135415400c0701610016508050942d035586c1c1000c2045002d0b03159031600340041a0031b95849690341a81c0002210000c0040841485049000c800811a6400090110a0241503840000c0212450303459119501c580d01c10003150b01c41407800c004440140e580300c10b049541c16202900c45980300030013101210070030210a404104400045450b5080042c07204c2d6111000f82440e03071429259800007031805416a00441e1900c0300b00b8080c500b180c10500a80d500302500809818462502c1c0e518030b00e55000c01080f00e054448800c400030180c14228080303051041001c2c03c100180d040c080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 527961447 1250 527960197 527960207
    0x9020c06070e090f1b120f040c080a0309090c0905031b010f0c08070b0c04120501020c1203090a08030c04030c35100b040f0c210c0e0d03020703060606 66
    0x240c4020220310080c0008202c0d09003020000e11407048490001c03201e94803580342d207103480201400300342c1d4030f08244003045084031100f030840d0060b640b01c4100b003240e142c03a01c3c101903141c00b50380048025403c40b00c480800250880008410760307800b5403003c03c8100018800316076140050344074640c140724006034506041e8491644005420080c0c2e140d0b090b0500d02c8205507a04603076018020802d50f8100301c10400b00c0c00c041c00c101d810107020f9188510b402c0d51102a00c02c05884480103540603503001420b03408085c0c00304100b80f88844d00950b80760441c5400c824260315070908100140c13102800000003120400008201c070003442e80311308124001612000359040100503070100e00c07580d9504c11980201c0080ea02c05503c0800c0b0070030700604400d003060075000080c188240c5050380081d00c40210851f8032201d8020282c0600c0b9540e00c100c05501c010040f0122105e80c84030481003d0710307040d0100041079120a443c03240725010f441e01c1035611481c0c80d0803860b1140d60303800684251302c1d00b01c0c081000ea40c42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 527962697 1250 527961447 527961451
    0x509030f0616032a050904060e0a0e160b03060118211a061f0c140a0201080705030921120f060a080309030d0c02011710030b13051b03030409020c06 65
    0x41d907400c2150803005007080195600d0700a0034501380000c80400c00800b8070400040c41611b070003400201d0600d43c0c61481c95140d600540b1341d407042c0380d16160041c580d00c100f00b00c1c920b0510f0f00c100c03012428501d0415583c1c420f1101a0849040150003444410411a06014480105444504000fa00745420100014024514411601003081c3c00001d0700c00c03a034a000c0c2c40d0040340014501c6000640d0786522030140c20204a1100600140041c3c1c400414106414500395070100c001130f042540152000611503200209002c080c40803c2c0184055100001480042203c50074038800c2d001a1302140400d041c06030300161381c0e1102d4600200801100b0041200e4003840c42942d400a10903140d41400e601c038001c8216664140d40404800c1c90030910a41c0240d89460060408540c0c00c0701d40305840c0c20000085030003050100100fa000c008011002c40700e00e90290f04141170f04440e42181d03a8540c0c80b080100e07601120741060b2854022659030900442c0c000300940b00c400c41d581c03841c41e40201d45a03001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 527963947 1250 527962697 527962741
    0x32a0307080f1509011e0c0212030a0b0901050603010b0301090504080405040e250b0711150c010c08011d060915100306030c09050108030d050709091103040c0902190509030f06 77
    0x420011418000c01400381b05210000d844107400c074100700900c480000d20040e0703001c00441c03281406121100c10454010350081044100100701c04940740d040c0688060180c0c0040c3c001c0c18100010043c2007060310550b8196400603001103819116800e08417402c4c003980d000103502620b011314151008030001611070040e45205403054003403507041c2ca400c1c0500503d120b03010742c000040250f0030004403c1681d10160745001003050030344000c20704102c1801c0e0850020b00b0f03036581d0350347c0341c041695400c083c549004245040c1407000c40469119030400000010b02400c0c09100720030045140c00a400d5000180c1c0c01f0040d1070710740c510900c100000c3c0a84030ba44010b40300014004c001141c1c0700168041d080c165000704000710728051700101c6d01d60040600030170240400200c100c3c0400c42d51081d0080052202540c1c41c0c103500c034201410b1940d00c450890340a420850b20411080f04114103140c09040c0b08645418295211071101c8080780c14010700d41d003c00d55a000b001304004510412104081200c49 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 527965197 1250 527963947 527963983
    0x50a020a1a06191214010608030a09080f03130608040302151906080c010522030c0b0301062d0302070f02100c05060c04210f0c060504060e032a0307080f 67
    0xc80400040c80f88801c5000f104000d001500f04070300403031013459000030722810403800010400d035500081805c540080f04101c0000340316241c100118001049103c08210403900034500c1e02940c01901035003500e9510411040c4044400068241802402a030340041c0c14035544109600d02410b1904c02d030300c3d40801c0820200d26000c4041003198001416042c400010307181d0030319091000310b5103008a0540203400700c501c00d041c0300c0800007410785241100105183c40c036468595050200c090010400c0718815240c00035070715140d40aa044034000004081000d0400581e590214180824102900034003c0e4201140107110300001d54020060303d441c40c00381003550b85540750300203601041e01c1513100d940e1400c0c40d01080210300c03803002152150300301c0c40f9107202a03c20381c1550755614402c2c5e0300d0b804103011a0000c2401c100b080c1d003102d0f14951003c4100d020b4045202e0842c0710002d402558084141d201c0d00410003004070342c5081141c0c1c1c010b00f4508088071900607031545220b0b42d070740c240d108107044c80e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 527966447 1250 527965197 527965219
    0x10c020d090f120b0c040305030c0a0201030501080a0b0115050c2a011706040507031e0c02060702120d020f0403050708010f1407120e012301080d02060c0406050a020a1a06 75
    0x60b003101a410180d07280c4002800102805803118803607040c000c3d0404c10401010440000060002c200500700900400d0242042c100b4500016040310016800034110742c00c81880f10001032882c00c02e85056030107100002e6a058088081212f80340503000281c4214440c00700a5445500002040c198400d4402d41b100c070103411500c011a64120001e015159460f503001c007241c0b161400d82c10040d40703c101d610700051030918001d02640c080c1402c1112031790050340c440103204025410310021b544032005000400e140c5c003c0e00c01c05a072074400c01c0d98194226070b021441452800c82c0d081203d0045400000725940c43d61101c003d14024011081e6545580b0310b001885962900e240c3c62091084416861b00c1405000c1014400040c00c4000920700b540c0d581c5560701103900300081d1160f03413401584503010120b903040101540c60705072500d50a00542d0700903004c004622503403004440076030b1100d00d040d603191680020160701d81140c0120007040c3c4103900040422200c40096460304ca9030040310303815009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 527967697 1250 527966447 527966459
    0x9051b04030f0b36061b04270603080903060105032802130203090601180c0f03090201110102040923010305061f0905010e04150908091c0b010b131410030e0f010c020d09 74
    0x41d03d40100805c0d2000f00130300007044050230644410b4441e03900301c00c3d1780c45c1007008824410f08444140d003003241d0030b400100386072400d800c040245501401d0141d00078102c0c402483d00fa103103001c0ca02d00fa0203524052a410a0382191980140c20000d00f42140c0290745904066200b5601d420742400b8188071030309851920185008140904048564641c9404200503000741c0300710040c3c4044035040e418004003c5186203c000309100520091840210000e4102035004903c0c103042c50808150400c4000d210050010030b5004c6103154001900c44001420a58010b0b06524509425880303030080c140340c0000000c1090340c910b0030a110398800d0030000348002c41e0324940780071504105c1003c0c02c007540600a041d01d03810580201007111042107505200c05c4d003185d48001310420709070020610080041602c0c0e00c5881c82a0403040030300909040543c0310541d0b040801c070300e0a40c50100e03104040e11048071b072450040074408413003500c0100d00203004581e00c614019550f240b0151130a00040d00840001800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 527968947 1250 527967697 527967721
    0x30030c02090c090105180103090c030303020a0e0904050309010503041406010f0312180501050c150901020405041404030e0105031801150302010212040f050d0c0f09051b04030f0b3606 80
    0x2120368140c45d01424500da80301400c420004041c071450500d5501c6013941c0100d5401c00104000b14847d98003d40d880c3c2e01c400c0c0080102d941c1c1d0310a140248045824040025404025208106020700e0015100e50329428468010860402182400e001d0b0a0000c10410354144103003003541d000c1c3c5806082006c80040403140040c0c00401e000c016020844180301541c41807000b4040441d89004a41344004002580c0914031001d4662040342ea50002c1e04002c2410030b4020b07000400140303c840c218170300d07054a0181901c84442c0c141410440d00100140c0100b907c03040e58045101500000c00400f481c0704080c0d074411425000690242c0310b080301c0081d17030700302200454050300c03d0b60460b1104580380106121022084078405c03103451000c0100400c1502c030b40280300c001000c00b00c2000c07855041049010702c20300e43d110489080c04408200070300104000100007880c0a034482148080741d03545524119500c1060000312030090343c5030f0355403443c21404071016100441020181c8041da03c40300d001c590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 527970197 1250 527968947 527968957
    0x90c0e010e010503061e0a06120c050906030412050f0f030403030506033408120403110d030c1e080c011d07140108090304050301020301090f0f05070930030c02090c 72
    0x40028020030005030076080c1101b4003401840380900c2120081c1c440e40000da0340d0203003034100200060300a030030024414018080c0b84008606400d28518000828010500501c4020000f42c60306070345404420223680b094080390096900301d10b17200d48801c04030040300c90550082d141075001a080001045041c5400b00b403031503994541460004a0107202c40c2002440084e01e03c1d41184a02908800104030300c0510030700052200ca88600d954442c210314086503540d07821058240074034a0544140b00194000c00020151504144501180001c08002c485110301650004000c45004510000402c1054000341031140c4c8103050440700c1c1341800701840c0d840c2d0300340c400c1c00e41d154102111110554050401903400c200c0d01415245440c0d200c0000c603007a41c4c000c0e4003400c5040c0ea80c11502051030500e02c41c504090840038018004c03402c0180000b071103100c441c0202c4494243c64002e001045c03109429031100d04040280441c25201a400d002d0709000181320b05a001c0d034101000074001100d00021a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 527971447 1250 527970197 527970199
    0x110f040b0307060c021c050619020a141c0606082d07050c0a050105010308130603020909011401030204050409060e010e03041211011b0f0309050406080c060f0f04090c0e010e 76
    0x542c00d1808100321883c410142040c0d82000500e503102e00c40c52500031585001c1c0340940024886030034850030700e21401d416000d05010180c0306001c20710050f50f20074810b02c1010469249152680349490b4603170420015100e14020881c034103400042c0880d0400c0c6070b68416400800300640c1030342ea10034801d51f284046104800301c0c200040000f01007a000b80058041031701c80700100d5000288a94980c6e007140d2007038000703850581001c181e80ba016545d44c41013a0181c90145019804c00700c950740461100310041c003420103000710b5a85180b801c1e900c2541598000c00000308140007103001030508500a0003162510350b05542000002d020b82100003048a044030a40b02d40300c15607041540750b000c0c0c7c251440210030704104107100135003494001e00c1030150b1786501800760a03101a00038500500000c01c41d0b48100d0040e4101641000141800701e0b03100c00c4441c0c203a68050f540d12132960311a0651003546c031170504900c00030a02280e0b1802c02d91203800c583c003c58403603d45203200d040042d070344110341001c52 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 527972697 1250 527971447 527971453
    0xf08070807090c0903050a030206190e0607200316020310150b070c09091103060f010602070e0405010f060303022406090a09030210110d0b060307090b03090f0a110f040b03 75
    0x10007800600d540b00c03c2d400d48640c03074010300854a03941c8090400756503c00135030050317014505203c1000d0f9140701141840c0c030b1514041180480c0020600c0d283e0000409a205128103201d2240244181d444440000341000c01640d41c2c0306103446039000d03d40740340700040c2d010348104c0541c0340d00c070314482c40340480d0140000210724050b468030320840003550094074201c50001e2107140004001609001c1e8201040c4140702c0c0d60040801e840a051078180000c1c17090740c244116400402045402265141c2910300c07d09080620b50344a041c5580900b0105803058641490030a00105265000c224850103150b0f00d03084001005011314a01c15401080c0c81807540091001e004c10b0302448554800080c1d180700340103607004600039100c010111349a9910012000304000b501030003000c03242c13081e9200c20804441040c103500b818074009024080d10300807003145800c000f0100756800410014440d690040c6022180b04078511304e040380314201d40000050040505400042140c501030181c1480d070480038001b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 527973947 1250 527972697 527972699
    0x4020a050f0a0c0803072006010f171608031306020c030309010302070201032003060f061204020d0c0b0c100612020f100302160f030e010c080702041112040c0f08070807 74
    0x346901c69806121070206101428180d200042d03440310146102d0402600c80c040403400010004015000039007100889811030350041c071080c0754240443c001c1d00c1200006100c40603480c0722051510482038818a1441a06040000c80d410000000c1400c0e440c070b20302c08007125681c0da000766a034102158845600d6041480441d007154840e50141c1442401450045105512040c1500c007000c02400c1e0303041c1c42e400000800c00d4034104400190008081520070b0703480d240002c02d0403000c004001e80024440d074090b010030000d20540070100000741c000c400140c0d40d150f01c0b002074103507204c400588068001e400e14200144850310744134901500c80d0080c3c044000002c2c0c1204120181c0030744862007003070650a000c0c0101c0180c41030000e111343d0b482085940019202400e001d0840c1311210403150402800c610800002068801501d40150b0706640104481c0002c2c0b000c1c1d1114019000d0388500001c103101003000340700c1030791800400c440342851032a44482d211981c00f0380700d142c0c0c6e014850060303120402c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 527975197 1250 527973947 527973967
    0x20c030325020d061b021612260f030402010201061202090a0507030608100e0601080105011208090d0b0a02071719050c0319090801240501080402040902131a04020a05 73
    0x1080c0341e203200a0003000c840c41c995581c8400c82d5500540300003c195001c3c480500c10350104160300319640402c0012801e18900590703900c1c0f0081d18400240380d65044400519000d4003910b540e1010300102d01c1041d215242c03001d0b0700341240c2003224168010b41c02c0c01000142c1461680c0b1a1140c4c640280500c1195511107410001401e40540304104169a81600141c0808148200c1c001c4012140303000c101c80d03101c03080c078610744681a0030442071640341030700400004a0244100c20f08a40c0002d00d6a100c0d401440014000c0d5001500a072003a0030107010030070740caa40fa40c01001d0705446030102109a8008101440d1700303000e06040e030018070701d0820480342254003070000382000d030a800085031b141019102d807082c580c882c0840c048010804890007070004100c00e0040000c290840041d040c000c14640e045040c80c803c042c0f0031a41406a4940400d041d52956001400011b402a241043e5290421a07544c0204501440501d65007a00c2042c12032a140600884030710444541d2698200b02444da = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 527976447 1250 527975197 527975257
    0xb030a0b0102210705070b040b0a1b050a0b011d04020f040911181006030902011209050309210f060f07030e0313090b120102130303030c0504050d06020703020c0303 72
    0x1010706601c64071180c0c1c0110048106151011010307031054075210b5040e403400625203019908001241281071200b44084401881a6425080e2500d0161081400107520703000ca240c0c040400307000d034025550b000b07060014004034681214800e0840c9a002032b0035091b080300d800b5055030000c0d44001601d405110a2419030081d00407103000d50b101c80b4600400600055107080041c0940280e0b0642c2810400c0d02c00c007004015000340703203a0505110b03111860340001d10998140c087c040302103598080400a003d820015500200c1014002a12011102c00c0484140ca0344440800d500d1213401180a070310340c000f09805000710500f21607405143c07940c28040c4c001c0c0c000400030031034610041c403040611304007071703150440200214100095201c0b10001440700b0000c543c900704102e6801000b28500110303140441c001129054a00002c0b000c801d40800c5507980b007150311886c0e1112038546094248850742d0300801865100390202c410700d0300200e00b803648a02400c8014400c0031090341880b22002002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 527977697 1250 527976447 527976461
    0x5071209020d030521090c031515061318060f050607170f0c0303070e0f090915070201021b010605211209030312180c01020313060c08041505030a060e010b030a 70
    0xc5201740c1ca4600382e6004402c0f600300e03440000d580c1309440d210240d0505001e03140f0500d0300c200d51115107140071206403004004c11008280103030000540640c4101c034030000c00b00038202400c460b0902d50f51009620300645402d010708080d40c0c0b001000002d0924000c0112408558001912004130039522008204c54014082250641d2020420a00c80902c00c1c40298030624442d00c99980d401c440781c0a100007009400066801800b041090050031031001038001a84203842c40389000d41d54452100324064090701a00d04c0070000b0800903070005c400190000001d8034819160426400140500c00114011074903d81e049908401150b445080a035002003407001e501404880c68015200c520720140320f01107c0030700e502c3c4111010302205141c20700001d24840024801141000a01440482904042d102c0d107000e1081c144c517000d08000c4604150b40060040da40401810409850b001c2e0580e072040301c6819245261100102c4c40361812505181a00c4402c0382e104c0c11a40da20990340010241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 527978947 1250 527977697 527977717
    0x6280302190909150606020111120402030a022110020403081b0106030f0b01060f0309020102070501110a08070602300109050a021c06090b04180b1807060305071209020d0305 76
    0x9001c9010800d59154001e0704070951165141031815005038044200301d03200364000300d0459041c00601c00c00c1e2007024044e18540000c21200c043c0c6c6448500c000b03450f12051400082d000f240003036100692003520408210142c000c1d2090301c620003100030b0060100e11540c08018203c10091000c025402000c0c1c1200d10200c01c50740c0001a00750b00d03620f89902d19600751b1000c464100c40f500040c002c3c3c40e444200c52a0b042c0107130400740150500f55001070344075036150003144c0c10055240b00d855a03080040144845507600818a0380c2d64801504000010703601403940b64401051070070020760594440301c0014800c611006103000d041e400d024a1001410300504003a1045400340031490400c00d1860405a0095015800241144c6040382e00c80c180c468240c000340c0b0036460442d0020700a1b4402d07d00a001603800045407250b555119000c110214281c0c481c0442d5119044011074141d805900c101e028100075155a412a060100794004ad64030300f800082d000f50003050302c01c0000c0c0c00348000d4090341103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 527980197 1250 527978947 527978989
    0x20106120b041415101805150402090105160503120916031203020903150604061a2d120907050a180e010209060c010609051806041502090406030b06280302 68
    0x1400c1d0844d0480103500741c0f03034001d40490a070010000f0808125840140000800e814042e6140c491300d1380301016000c260107070040c1e400040e2102980e201d01e007180e11382c443d00260000c48401a0a00e44d580350800b0128061078130000001c034010540003c0e1035081380a04912011506003507603a403469031103020702103405040e028403940545640a00a10f0784134214407000f400f513450484100030641c0c10301d0307101c064049118100c0040070b031220710848511014403011a2020034006c10717211002c9039028691903d56401081d2240c20060b101410b0340100c024008135031406881c0c0c0c0402003600050320a0185903a021492540c0b1030400781c01081203059041d0005040c00841d4001c00c82c140e100d03820002d080d9650305c0c02030203005845d01c80d00c2e40003e1a61b1900c0000807240c16055614900644003400c5444e501000641d9040141c0450b0140e80014100380002d554030700d8010109403050b10442d2198402e005100201ea20703000c1a100444680c42104256501d0740e0203001d202d0048200b40707030380c0c06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 527981447 1250 527980197 527980213
    0x40b0415060b0f0a090e09070e0405070b070f05010608010203070504090b12030a020d1803080a05070f0206040b03010e091c14040b040b070210050a0e130902040c020d020106120b0414 80
    0x82e01e4001410061001c1c254482c0e5414401500074510112078112a018104100902600c0080050b081081e40c290a0000707a558955081007842d00180340c1c0401c481010008418023006030880745401c90034460402400380d207807503c2456082c0c0c001111a240015418001046190040d130007818200714080c4c02d605204030401d0085085501c00351202000d03a2080458a5460350722445410181540506172880b03181190307074a803010300ca194992810410b011031f00300c042c0b055a80c41c01003c41c1d401400c0d0380d580c5507240d00030100c41c0c20911580c0c11801c41d00c1e0004000010104480c41c80751400d24010881c03c14030b040c00d50741141651202c04101100303000200b4645007e0300108080c1c103c1003e96521031005104204440c0e1710f6003400c0c02041401c0c0b01d08040241c00c0710b50000d4010b0101c5000400d090f00d20b0500c0e0080c040d0440103940541450203e010680d00424801d00d140e026900038894a91600040b051301442003074004c1281d446040050003040c010000805a00740d50300681d07840d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 527982697 1250 527981447 527981459
    0xa0b06090c1605030903150c03010e06011b03021c03020304050a03110a050609070e2409040819080a05160806091e0702030903060106080114010c0302070f0f08070608040b041506 78
    0x9400c2c5644200c60f10350001540802916003004811060305101c0f107468050b152415001945000611511002c07040000104010340c0c000d244416003411030f118801140110350078000d5030b80f56011081c84018000130001d9001c1c0b0710900813284a26002001080024400c0d03400715001c50951400d00414002d180c07003040011030620469014031600c10081c210306c1d00713013071407a05158400b400700b108115040781501c150040182c412803640104aa800c100350f59a81010100c0e840356816102e042c2c0d220010300d05040c6d07005800c46024132102d450800c0310760350f80c032184814130039007003c85000704411100003046490001c10003503201c07986e0301c421000020b8401d1520300400003540c40c4000f50b000400e8140060904010040c014415840c100074194909001e40201c22400c00300c43d8100821400c0e10b009041c0200003070b0000705941810886116a01ca400d500400341d2405040c03024001c1c4d550018402e8803827480b2501540c1c001d10f122000344c03243d5462039420010b8003501c24030991550030018003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 527983947 1250 527982697 527982727
    0xc071b1413020f2701020c030d080408040e040b3702070f02091314030a081324150902070201020d050304060b0307060309140a0804090e070902040906060f020a0b06090c 74
    0x220340200c40c1607000c1d6001d4000c8882c0504101241394110b611090740032040380d40004c2c03a42c07002903050402e000552591b0520000c40e1007160801e00c605d000d0a13043c0001c20155980c03103841100c17406000041d10000314407508500802030305c2400d40d410042c40d030701210000c6a006081c41c0d8821079507981c008405601140e240c81c021101e8280e040107034801002849500100d04101013501e4028515008030001d01400b0a01c0203400c0540d054080e4051030200a1158407080003801e80c0048a041820a0300c04c0380c000d8019a14948410110100c2c0003c10386881d000352204a03505030003030400210b12420448031608000c0050300d09a03122050760040c0d490a01070710000d40100d40c2c0104100c17240d030416000c4200d5120036002103034000920f020112751b185c070594050701c1501c00082200c03002c917107581b880d06042c0d07048003400c1440010001005905540610100c404031303141c000b860180740300181d846101c444400b40c0400b207014002205481c01c401d500d41d001c5491902c06041122803240010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 527985197 1250 527983947 527983957
    0x1c120f0c020a150204080307080309030c06160215010e13170f03070305062202030a020702090c040302010f08150d17031e06060f07080c01060e0c071b1413020f 70
    0xd41c2280c9040014044402c0c5140c2403005102804c0d0300c1c040c80c0140207a074a10615001030f10012000c00400c6550000380210b611100842c030444003103061080f8041c598011101e15240941700398441150080d149400c40c504840660024404c030790303141c8074076078183c1003918000c541e10b404035002e0200041a034000352032901e0251521070f85038906090042d00700ca00240c14540301d41da03607480c012905607007003040c0f2222402049015880740c07500403005019002d1864001d502240341ca041141c0805e01e00043c1c41168000da8525412408484e011341d2018001c0e0740082d205107003c800401c0c50f08100e03051109191240c490a806125000d0129030681c2003621445c1881c80881d211189424011803146e820400445032a072500340111f141d007d541c846c4400080000c400810746514241e000e42c06000142103c8001207114600b07160505680c1e40a08800c0b10f050484026003500300e0300b040c48401c25658030740701115030402e005c400c1180d000003460f01e0b80f61180d02000f03e13100d0320446038060301d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 527986447 1250 527985197 527985221
    0x2060c0703111c02220b03010603030507020301181a1306021206120601150818070b0307030e01090b061e130603140c06070b0703020706140103020f031c120f 69
    0x8180c02040007044030000514003ca400350114805030380c0540d4958000002c40c415554a001244145060401c043d004017034001d82d26502e041c2000083c180c000000701511442140200890403402e101c0f00c08100203403501401e010482240c1503005041809100d8104484141075044141160384100907a4084007610400415980034003c403400c100d001180c11440d0500605480d6050603002e01c5000180c0d980c2c081000169404154230042241c104942c001450081e0346c001030300c51103408481c2d4020f4860000007071400c903903420307054410300c034134002103034004010328040e10384c0000c0245841d00d0700c00300b9070850155404070b40f441e41c1d00c555220b031250b20320801103032140c079604000035030340680f15001455402401400c0203558500d0211042c0c1176010403013142585641a085000f4014070000900c1207140540050680240c0031015040364030883d049501e410552083c1070301c960800010b80700f501c1442501103046070044251400d1141d000e100001c0400b1507240303000607140d240c11a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 527987697 1250 527986447 527986463
    0x170c030d180212070821040b130e010902040503031b010e0a050706022a1c080d060504050108030c0a0308090c0d060603051911060a03090b2401022802060c0703 70
    0xa001c605008000400c4001c0f042e0180c40510b181c501c000e602d554040c0e03416110511510ba82003c8483c180041d60007803c014140719864075109014001d940200c0e001e10345070340440030000034450b041802107070152030014018604102c084d000c1c7c00e1010208501266095403240e1b0450322412003000345056850080300100440c925040d006420048001000b0b003021030484031400e18003440580050f0f101c4000d903003001e000322140503846032007182070b40c5c01000e07510005485d0800c0300064100c00241c034401ca900b0042a641c580016580f440740c02e0304c92940d0313001514160042401005899803180e0864250342c0e000012000007015502c42110803030340255100b60510038484200314000080c1a03c4074040d4900c900c60700c3e103070301c0d8032614801741c0d100351400104010260b22a400403046103034010340c0da40d52420b001e0311542c0380d180c070032800d000c0c020846031b201040782d07100140b2410740908603a0726004500306910048440219060103a03000b803800c200da50009201000032000540c058990 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 527988947 1250 527987697 527987741
    0x17010b010e0a0503060c031806092401120f0c0b2a0d08010e0a18080c0607030c050f030604060e16020c01080103150c03110c030a02060c0403170c030d 66
    0x904101c21000269000e8000b000c0180400c1c4c6002070001d401c44920102e09072295100178169a40e981403c5004c142802003000b0701410010000300949518020006040b14541c3d03001908040c2c4000d00c2a40080f0f6900280c8501003a140056603856130b01400030f2190380c1d5101d4541105903804100001d09000d4420350f41d12340859a181144095032100c40030342030b1102500d100415500041c0202c6014074085400702e90f0701c0406a2216002068031007004507000c45608240d05540c110540118140c0141c800003012075100303219417094042d084d00c80c40c3c1011700c0102c1d008900e8000404c4580c10966804003c03802e6810494140e1042911401c003080d50442198024200032948bc801d5062002c24001403000bd401014041c080d62020300c00000c200c810040100e000c0d00440203041c981c560005224913400501100411000401d0380884446448480001300c21788142d100191100c1d003e0150355650341e8982c8000c0c004240490222402c3c4410007602508483c070440c038042500c4401c0c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 527990197 1250 527988947 527988949
    0x611090103060b0301060203070201200a0b0f07080601140a0c02030a24060b0306040e011506020d09050904080d0504050304211203021908060303040e24030d02070303050d0617010b 79
    0x750b03000b83c20150841030865240020103907480c090400000c3c140300e0b02403c02e00040c3e41031841183d401201c482100c15028030783c1420311039440c00703403070139030300503c00c10000b600c49806404040e000701d40680d21407981c80014034003001680c0101114804101030410740c00c000d640c0c10086408001d000303071401c01c0c1c42c40b5503d092016910740309500c0c604050802204200302c0c6400004d42c0c0c0c0c409000c1c0c0d00494441c0300034095500404c11500020308842c6a000007181203580054070180d1522282c40b41e1180c1c0fa01e40b800c0119442c03049400501c000c4040181200c00f043e00e401040d0824841c10850f420582c80c2c00310b4444400402000c00c00825441d0088000d005007541007048240103810114541f4810840c01101f001e00c00704480d00f4440144041501030718100101e500401c0300e44c0c100328081c00c05084000d60000100f101d00c1403403d402d10034407114035000c01d8408900711542c000348196031640c3d500340d8058014240d41c054031651094005080744034041e0b20048042c99400005030580504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 527991447 1250 527990197 527990201
    0x1412101706330607050c040501060e09061302190f0f1d10020304080f031e0c03030106120f3e120402030a020a0609080c03010203190213030611090103 66
    0x48050000c0c0c1d11080c18841010400c0900205045040b00e101d01d407108010040c008107200400c903240c001c44000341c08014480045941c0300b0300345048a0a001c6a41e0b200300460f01c00145814407580811074001140781450030003034403042c8800d800009070070003512070030004100d50b0440d03400b40030a0b052030b400040c49610803200800d50665091094840800c42c0d000c0c611041d60040d0140252586203c2405890080090314002c010035011100c03004001d52403c4c0c0c03650002c1200300c0c003140050003e10700c0d1507090f40a64107140b2030007000f03500310b84c40e22504442e8098462206011642c1c1c0c0e117070700804c03d80e160043d140450782d0020172542c59240c02c0950007126030141030131090001010065a09084036100300d408058079400545841c0c0c039103000103800c01620000096103c000b280e80069540d8020380703800105c5010500380c03100b85203204185802c0c0e21044401c000108402180e490342d400c1c135540608901580303400c141594a460380d42e040d00b141c00100a2503202c80021420400035a814 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 527992697 1250 527991447 527991479
    0x40c020a0c0b130302100201090503040f081006050603071808060408030108060f01032402040b2a010c0207030f11040e01050a0c05070203100b060d150302120c0a06141210 75
    0x620b0400d8039101d00841c00410312801c6002c02803107141a021081c002600c00d400240000383c200c015240c5d00d503642c0802c501c0381000c07480340840c07601600e40864042c0700c25110b1a4201c400c007810291540e41d41079400c03034503440d01800c84a03020681240c00308040070b082051510540c0b040c901e050340c9505000b4007070302e0300c4001404d0410004660303006000141541e00d440d50000840440c00078164560080c0101a00464000b42582880441e04003812040038120a10151004512401180c4024807da0076601c03080241070145e8004c1d5000c000103a1a07103440d20110313000310062000900d0060000702502c0002070507030310340e0391113406200c0f911030306115454120405003006840e101c034683c0842d448508110990f10040d41c3d441c45101d4030340340e60007110210900d004041002011018000740a1001400141e0040042952098209200242440001038002e00c14950a1324204048900c2e24907000b004c1030700e940c01e001c4aa000502c0c3c104031401640d50400102c202c40c00c00d806034546a0038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 527993947 1250 527992697 527992709
    0x6040b0c0c0d4103150d06090614100e0c041701090c050d02150c03070c0605030a050105060f03060f150a030905060603060c0f0a05131d092406040605040c020a0c 71
    0x808099059422424150074403507055000c0c000e449a450904038000560300c10b0010360401c4061b11030a0422400e40e11181025200c1c0504001f20000480c140e0000c200468240601510b0464180140b941150119034800d007131642c140d1a00d038503200e00400f416001c0c0801e0315240e465103403274400c10180d00d0003400030f0030b025200310700a610b40ea00002c1c80348103541d443c9001310000007074000044005100b01c1d5006a003000c1032618050303403444e00400a9104840c0164401d20f05000070519103042c00485002410032441c06d8219191541048480351843d070303000c0d5001a4440a181c07002022002405980205440000b60030800381406401e00b40b008010512a40044042128442184055850340c600d008141601c03070600820907200c51040c41c8032004076080c22000000c036210350003000c42c0f403543c072608100301e20348071852801c0c0d8440610f10140c00341c0390f0741b070040c0044070405100c10b940100010703c040344555440010404442c1c0c0541481c0c0141c1004c9184000c1c001c03080110310013004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 527995197 1250 527993947 527994017
    0x8041203120f0e030906160f030809161505130915050a05060c060115020f10020a020d0e0f01030f020d0507030c0810080a080f13060f0906090806040b0c0c0d 69
    0x2c03c0311082c13500c80c8250f000d0070303114000c04540c1c0055010814112400d0f43d0380070040c840d91a40e00d06019000c004101c07075021071442401034180c45c02045901c1401120103800c0c0c84c2c0886c501e400c1c1c0c2a05c1a8000e0f180200309404800300008007010342d806010740c02c01c80101d013841c00318104003c0c00895241c07030704468000c0c5410804d043c0203030400070713031181102c28a8150140f0784000d404207e060031030806030710a091060258144003900c40303070f00614004c90031fa000c4900002d00d02c02d0548448440d00040b980c0040c0c04480c61109502a0300030307101c80011101e0040c0f0b45404604024100d40d41560800c0000390307644941d41809402819150700920100c03200859141f520920039aa0945207400426440c40462904403650004054801c07060100701201660b603243c06004240000311f445103000541c103801c00040307a40c0641c0641d4240c5010b80003030940c5a4880d00c42c55040c01300602500c40001081000c02d0300494140880d140850709585c580402c8200720070344d28598100c04004094082d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 527996447 1250 527995197 527995211
    0x3011e1103011206200c060a0515150a11070b19091a0d090f0615050a06080f060d0203070905010f1a0304110a05040e0a060f05061c08041203120f 64
    0x180f42050f5188255110f9130214011046003498000b81c05807681124000c0c1c1e003c650061101ca012510701d100d0a410740c003c114035a103c18444644100d002841c64001c0b2900502c48000c9201400604003080700f81400f04400071440f810350310b880415804a01c00f007801041070022030524000c011801d00300b5160070710034141007643e070030300350014004004840940001d0320003100020b030704114106608070014440803806030400704050208148004c100005121001c04e40e40b4004e0041c0c410b0747c1c410390b102045a900d0700900071504101a0540e03500c2a1400101d80050742d0401414001e03000784080490f1551404071040e1403001140c00c034208000000511941800701001501d070b0041d0031180158000140b08080f4140120380d41149400a04103803440340381500000340308902c1481000104000c00f0581008800c03104191040f95002c00202100c801c04402900307407401d540c0c02a0001840c1a90f6170f11070301c141c85007200044002c955200300382c2100e01d00901c1802640a40c025090081d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 527997697 1250 527996447 527996459
    0x90503070e0402040b0909011a10021e100504080c1204150f140307030603140304030c05090c0f0d09031d0603130501061206141609030311030903011e110301 69
    0x103400381d02403070380e8010300d070000181556160340107107440c0c1c10040d110390140d00300300302200d004e41440700003041e001c200c01d440c0804a080104d00200d170200340f03501401510340690390f00c07008542e1003002080c65101d0003490010b041001e01c20795002c0d0344034802555807101072418050900000343c0002c03c815170300703000c104040d250421210450b0089480c05207860000400c05070347e070541ca0104002070315400704c01c10400b190503030b01002c00c3d24010103031050a0200d10190340e6481c07045000040012040c0e20080001d42444080b89030019095a1281d041441d40344000425030400522100041d07100c07884041410740003042c0080d0042481c0c407d036111840040402c48621002d070030380d0b10003081d000c000000d120007035000c0000b40c2001c3c840d80190050b5810408051b00c00b00c2400380c0807200c480c0202d080c00c01d1811040d003040d0580e850b260762844c91610f0607030b120002046181a01c3c04208105403a0303580a204080200d803021800c00c03401d06660718480201d50180c6004032403090100010701c0702d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 527998947 1250 527997697 527997703
    0xb0307080703031e050c01110418020903030409020313050a030c1202010212060909010605031006030311060f0103080708071202070305010e0111030a0c05071a1501170402010807110a060219090503 86
    0x4031244d12002d000030907011108407400d102c1c00c0b44183d415440e28aa02604840c46802001202d0401c0e0451502448000d01c0208a120b030790a038031342c103600030032080141c4801c98000e150b1109505040442401c0740742c03540c03802d000d0084811070010b10071f030303a94600b00060503004c4189008140700840c1041110036a4440118010301880d2099692000080d40d003c0709410003405488060241c444604110383d2420290850340412008140d031003607807080719100000c0c16440369402d03141180461f440c0d41c03910702d42c991007200e050340d90200412001c40840c490010b00865408190b0040c4080b614508200342103031408052410307140d040561500c2401c2d102410340e5002000800c00040d4004030080503145840f940400802d2000003400c40c3c81c2c0003c5400c5814032924801e250100744900c43d1004483c4001d0080501e00138207035003000304000d544101c9420b54402d909007400300082403490350382e0b032420001c0b86048550a40025803446618140018100002c009082100c0301a06000010303032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 528000197 1250 527998947 527998967
    0x20309090903041e0e070e010c0b0a020706091529090603011b0503090705011b110a09020f07020414060603010519120303060617100506090d02060c010b030708070303 73
    0x4800c040040c08541001810300446000300b000488002c041c0a010b294140070350401d2003400501e0305080e0000b107000d40a2801104072000580d1800000011a40c80340d0302030300054410000591b0911840000603214030030441d025024100c0d80300d03c0280ca12445095074681203c3c0d8191902c240300d03141d185501e020200c41c850b0b400b15550402130350f03041c000c28014400c2c85168032104403110801201160004000d5009201c0c05058661654a540040d107040200c40b1100c203e0300d01ca298210040b60303190515a450303582c020003540009641d00c2104051f038200d106003410102d070002d60002103290500c224050310720744d0604509217107050b000003801030005100d100e010321400416101030303814040b82407008c0c111030b0410700e40c0d48080c1d0030010010156401000f0105180b10b030070885c449420b16040344101d60b90364815000c0c3c2d0900051040a030040c000654002d0241071852005030f560001400d40800c205000180d1800ca500405140001607403004005400075001800420340c0448000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 528001447 1250 528000197 528000199
    0x1703030f18010902030d0c1e0b071d19080f010c020601170a0c030b010f140f0103020f07120e10030b0d060b03010b0d06141612270308072a020f0a1a130b0307020309 72
    0x42c1070070100d1010140715814240d040d40e00c0cd0152100f8920000c5003584e5809070b03040e440483d04030310039003013007107080b5441c0152a0015a000e9070040202c500358052080100504200f80c1d540903401b595002d0300b00c0c4103034104a82a124420050101001030341001c4018000e89660350481c11a8a011482e80d4104196290400d9000a1510203e40341c1d4400c0ba100f07246d2000102c50403a0050381d000704504600159140f10302c10703500c640c081440c446d0003688a51b400042403102c40d184140d6452009003400060640c065403a160f8950031a0740d59032640244038050303040813403002c000c002c4291903484014104508d200c0d15050703101080b64400c0b01032203c1404d10300c002851044200034450848030200d100b00c21038590740c0da0b00c02015840f41c1c1d030a01860694561640c501500000c80c03031701c561250616a070355240c402c04a8058501082a640c003108040c1c04000202c0e1507908010404d0742040b0b512802c03002c0007550414540001c540c0200810000049900f142482034000391a440382d11110303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 528002697 1250 528001447 528001457
    0xe1c02031e090a051c11010329040f0c0507110301060f06030203040828230d050c0d02032701050c0d092a1703030f18010902030d0c1e0b07 61
    0x516901d80b981c0000c40050075006221071003d171100f140b030b102910142c2070112851041a0607032000c650007802007074100b03440c144078056008a01031405c0007408440d041150b00035200d01c840030b0040342c2c61040042c100c1d41d503900e2540d5016182810607520007001406800707a85880820040302c51806004000e880d043d24000d0799030703251400c040303d0900680e12081c4650301646178817017142d10301040550740aa036507107840c02c1244c001d040c41d85002182030a0050b4070841000030480f01015580701070350022501c14201d0601101d10f0840d0100d070421607403402501c100301303c80140c0a40034454049007101410081c007440c035207038811094a004403500005541d4940b0704090030030890b103400c044105201160550101c44c80320700309000241070310941d00c8400c0c100000c4850ba01010044902c17804009141c10f0b00e0780c0311070000914141300800c8940d219580d506034400183d42c01d0228007102e111650b142c031078600560600207690341602c0c0744103102c12600310103800010100d00c6510341c080d0840c240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 528003947 1250 528002697 528002707
    0x152d0d030201020f0a20011509180f03082a0f070227100909080714210a08090a0215090607021c060501150210050c09040e1c02031e 58
    0x3099001e4000c0d11541e110150b00801d03585252507010b0703249555062001a0080c4508600d10410300f05c428440741d1800c0208511424010480310741c000b01000c2a106400b2000e40c0a01e840303d01c8000c840d203c00301d002070041d40030303c15142540390340c000d8100c0b1a100030b024004200c00403017805104044003d82070820100d00f030070644d52908940c0d00c18840c0014a003103400c3d0a4481201f40e004121030100f0700d1003400c40c0c08901c0e681c12303208540c01c2e260300c00d010618012440d150040c201ca4842e00440c50352003000c0d1011141d40050840440d28040c51040756200c28041c1406015180d0040c503494a640c440800900075a950b10903600160718000b0007503070b540c030030700d0041416880750900107908401c004c1440001e2003105003042d000c1d50300810003080280d80341c480000c105031884545100580c010603041200c01c3c07d9902154100c00001001d900d040080008a0140c8105551600700360f0040940c94034100b00d943d01e0614918418409146403052080c800022420070b030300c000d890b16030f0102d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 528005197 1250 528003947 528003953
    0xc150603060c0903120203130519150f02061806161b03120c0c0b012102281707180e030705061b03040209012903152d0d 53
    0x121a901841c0c1008003030003035903000d05024015034440e2200301d44940c480c10b61140a28804400e07900042e440c91228050f26151404210740c694603140148100219082c0014031800c04101c200c2203100161900070f041509080b001e414004001d1030306504103943d103008241c21401141c05503200d5904e0b0084071090741000b00c215a0b440108a01d6030a4039041e8401130185034001078018802e030b00040c014440c81c081d04400729400031007081c2c028000240314006000d0301e03803140110803504107810500041403071550000b0b40409814410703000001c0f0302c044010709541003040e00101600304284407103885440034a08550b501254071078064905400f01c181c3c810400c123074214540c10f0151004903031f264a0141009515000140c2e450f840005c000300009042152400589100e260010035429440e07203000b000c90134111000b141d03542e1580303008113204d02140001001d540134085605441c03e49a040a01b400100c0e9540f9016492002603400049107481c807212070008102070070f4500e400c0040c800d10b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 528006447 1250 528005197 528005201
    0x12060b0906010e010f03060e011e0803040b0912010905010f02210402010813020f0306040503041e030c1a1b07060f020c030d110307150f0b1c0204150302041806050709060c15 76
    0x10b001001c40c0304148c80000b46d81d070a19206c01400150300000e030007103980d0300d05685507a8030552007100704103142484103040a00c0c2111911114080250022800340c1040c1d80c0c0c54210b5142809000032a6404142442c0d07001d22044e10b00b000915000c8030038454103182e00041c0c45e810000703042020a4030000784071021920744140117080780e100941100d40c0c038206460190303203e0300240100202d80c03180140140280360403000d01800c994020254200483c201440381120503124001250319400030040103003400d8242c040d003c546001103014002c050f0130004002c0030140d000700d80104652200449610725a4046440e10750b1080b00c0c02c00f00d1081c0041c1d94214107600130003038040c101103240c0400c50300001080d040701c103110341449410410400003004000b50f244a003108401c0031510f00b40707145d00500f4a036001c138070302c803184140c1018140e60b658005001d66801c1c01c443c4041018812402c0108949030180c0c1c1d801c0f002d6400c100c0800740c1070000c01810030701035440282c88074210704106a040c01090b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 528007697 1250 528006447 528006449
    0x30306010909020d0f020318010b0d080a0c0309180605030609010908030105040209121504030305180a060f20120a14040b060103021309150503070b0a050d0b03010612060b0906010e010f0306 83
    0x1c00710647d100d1810f030180c0030003400003c0c803507001942005010203d61400031500d6a4541d40b007003c55003000e011801c11102c841c2d40131012828091a200d0210701d81c07130443c80b0030740441c01d001c2c008143c031410301091508000c0c000e400400c1c241e040c02c0003900040c907503009490540f1030990b40141c444500d40009640c203000285c1d1001c031405642140410705490100c030385d1081c2e010f920b0600a50b118a0040e0540c0c181102d450038007600900180000541640c120000c4035480381c002107100d8013181c3c0c110b59228200710a1120303580340090003400c98100111b60315485001c501e41041684500030080d0b500d250010130041030000110002403240e030296066455501012510034540c6480707002d030a0003480740caa85452683e4149100003000d183c001144015140d0843c04030341003828100d42601c041e08240150340219496000300900780d2000d11440b801030500d004010200000d80c00c00a0803200c9907624180112605410456142d030403052042c2c40400038030b4010f000180c80f050840c018182 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 528008947 1250 528007697 528007721
    0xc060e0703020a1701050f16032a030c0315030f0b090307080409090201110d050d090201020a0b04111513060c02010309060c0509030f1612020a1e060908030306010909020d 75
    0x35107010446007215910b01c044502d0840003045030752102410002100b00c1210390100025480108c01c0615210742c10103034104031003600204c81e0214840314401088000440000061766840060b244184e140c002c08041c410040010783c1010706540360812030b0103002070054000304801010030030a100410445540caa04105007544a03a101c2c0c584070040c2585180584c00103200d00301008c0c40f100003150b4410f100016403911031400701508094000741100710030990560090886960205070301e08450f5202d00e114281007040e1220100401001c1071101503100402d480a00400021180c104039140568041d800c2400c000e070090710048014141a940040240c2e041c402d09040440d0060090424254210181e99400c820803501e203648002003a111000c1050390b005c20000c0b10a0360790131900c3c039800070340302203141c58442c2811401700c0458440401d034484400400c100361680446408090305140020f50300e5420401c00007002c89019004851f5221b900182400c01e2949a40c400c0c801041c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 528010197 1250 528008947 528008959
    0x5040c080d030609060e071e050d0504150c020304080624030a0b07030c05090a0b030601180e0601020d080c03310b0a0605030604081206040213141504060c060e070302 73
    0x4401c90300401820842c4924155182455404500c0440044199110b07035501d0740c50000a0310700c002c0780e461040c02c4500301c00910608008041d481801800388a1007540155442c1d0840e10700e040c0240c0172140811001811900103000a000850002c92a181c100c05001030441c010012a440464101c4612094561511612602c07a0800c065541054450307249606c04014941074044240c9280c81103070b80440c0e0050440c2010b1024007040d2001d5904098185400d8082d502d0011a00d40c13030040a42210640c40960b400700111036a04001150601104d40703081e0350242000746001c541404050300042212040701480c4210100d01a444004603107400741400e06600c09007032482e4290300980b1b91220310341c1410000700b180d041c0026414010f5034000341e500c3c5400c003211003c1c2c40d6210301038404bd500079020000070034494040d481e440090004402c00000a525100c00c002840c00303c0790048400c00e80c107000401070305801114140415400c03a101091120f0740c44185400d1000c1d540009511035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 528011447 1250 528010197 528010213
    0x17030403021501032f03070504020d0f060e150316092406030b03010f11030403051b0109080a0206060307081e03120109020304031202090d03050f0d0f0b010e040b0607030305040c08 79
    0x4070140748a01341750a00e0200401d200d210114400400e01c048941c1d083c1c0581c0491010080307818581d004000540382034000244959a045100064554550042c0c810b824080107002c1490759620b003008180408800070600001c846c0c442200034460381c0b08240f9030a0361f52249520b64801c410100b40300e00e4440801012258031031801a00406c0e420f400c480c040d610345210300440f00c005105458080d0b503000802c41c116034959408a40715030148441500c402031002000384458002d02802129a10905000e521035202440081c540300c1e0081c081d6100768401402000a04408140c5403030500c0151680130400d001c00000510310f104200740a5490302c80d03d400000c0c4070360290b000e180a144203590300401c05d802da1000800703070700481d02055402040c0810b0348000034000c1d8005c0191801e43d00c440341c1003901a00424086601441c2c1c030507031240c0c46409580da10342c0c0c094a244810b06046500304210001d58010034481c2c09140d900030149a90b40000c02c0500c80000d03002e00041880104651001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 528012697 1250 528011447 528011453
    0x620010f05101403060103020d061509020c071a09130b0f030a05010b03120f0a1209062d06060210020a111b0301050106030b030a15060503120301030b010e041703040302150103 77
    0x44040c411200e0b0407441d03c4110010b460003180d054100c03a0018621030300b080443e00e5a071f000300185224000440c5c0000000520541d41d0300142c1803410800019001151609040c4400c58408030007a007447e040421051419075507001004984910300e40c0009240070010001c00c1c8ca050100d80ca41c0c2e41407040111040800405402840580b01e040d800c0d030b007070203914501a5140c0c2c02455884040e03284280042e4030600c0c03150000491110720403030302144104460311140b0440781002d075030b0405d91002e0700b02c002c107003807401901c44490142180200186e5242c000001e45a000842c103000513690002410402c5502c244a20320441c2140f4041e6020325030b619940510000d40240020f000c1d500f0000006081806889040c2d100c141c050060304c240c06055a0b001c405005c050810a041681c680022070251410490544c0034499451041e56950541c02d0002d00300758164801e11403110b14100304400540203120b100ca42e00782200780c07140c03030b51a01e26041c0e0500804020100c01c00c55844000014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 528013947 1250 528012697 528012721
    0x5130e19081801110a031d0d0303020904050714090105090a09020f03090d081303050c0114150301060905010f0e0c0d020f0702040b0d030509120304050901080a1505010620010f05 78
    0x41c2891042c00503000702100c01c01901c2c803c0325a441094650012400710021a02600d08001041000707c0c040300c5003544103002603105060010b0603030000b03a01180c07071071441c1030911a0701e03000380550600c031483ca261026500540c0c810340010134100040410052096200d240c1d108000c0e02d03510505548a840c5004250225081221309200c140b0450f90310a016178011440c0300c1c001c0c00c0081204034031183d1503d0a07616907029080703040040d0340c0c604180c01b8080006000740d000da0242c00804030540e81c10030030542920300342d4101d00e800903d00300c010889a051300b0104c00460f40615644861540d503500c13a4031441c0164110f44441e0b90000401c03024fc044100018459103100312010031281802e40b0501c2848451440002e010a404001c0720b407562034110b40002e514524181124034140e120400f00d45480002c4e4031500b115440000200704000031020b01011980c44108108070541c5061001401c039001d0308800c444450441402040c0002c080d003003005e154414410504c190708000d40d00d114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 528015197 1250 528013947 528013957
    0x30303051618030605070512040c15020312070819050c03042901091113080a0501050c0a08060d02010509091e070e01050706020310050a0801060609050a05130e1908 72
    0x24000d0300e0805a0340780ca41c0629000080400c1e0007005614090035aa640300003400081c15000074400140201c00b0030b0384241003401e10491180c10402081e514049a0400003021050300c0000d40d08140200c6417400800303000142d00412500c1d00c0c0d002c82c0c881e00e490780d07006104054220019418a001c2008d4046220011070089110349200044507031030b088242d20f00807000f100242070300719520040001100315000400c10007030160308140742141c1c2508002d02c0d40e400782d1101006d600a0500031080c40802e12419600184001d011460081d040000a08141009000324031405c1d9004c1050b0540e440303041503e51440f1702410904c401d080c10a00301040b140107031b40000f82010740000007905148650345a219103841a168182030005070b5030f441f0083c0d0001046595195a107103030001302c6580f5203100b44000d00a40c4000900a424820300428a5460b90000c90041c1a501c004001c151101108004503c07404103000a414603840300306414490b940302ea140300d45042040d41814428000300400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 528016447 1250 528015197 528015211
    0x6090e0307020112111b0d14270103060503030d05010e06060307212705120a02030409090f051f0e0615060711060301060504060206090c091b04081009031d130e030904020403030305 79
    0x900c0f40103819008d02514880d18803081801c050003480300e090740d030742681c0403500c041d01418085405038540c80800c2c9590082c00400e20501d032110010000031030300074001c03a088036081e51031034614584048054502c5030302400c0800d4986449100c1100001c05030300c0610464640a40043c0101c060f03000e0b80b101c1d11005d02c0070350b102d02803031945000584080084501d08040391300038508007403400780303e0001001b5880055804001c40303590600041e60034040f8000086d40c804a00400030841301180049aa0f9442c1c0307036219034040b4080c4a06015406c0c200049414126a050340d101c8261034000a1580c002081940080300480085901038000300904141d4402e070303007203a03030a64440004568421900000540100c1b440380812886d190000c180d604030107900c85441d00c2d2507903e41110346083c0900d4404810a59103d603807108042d0320448161501070b514039041100482a03001408021045400c00d0035141d0716094100a5141071041e65403144000740110b44807075407400e0160150070212101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 528017697 1250 528016447 528016457
    0x3b04020f1f0516050106060504210f080a0201180c08010c05030c0307050702030f0d08100905070f050901020a020d1401050c042417090106090e0307020112111b0d 71
    0xd030321281003074655400008480c000d0807000300c409107400d8609501000b40340e0642c5000584580c0461000d014000c01400d65503501c540c2d41e0b141c1209080c0108402d406a024403c8442e896000704284920070b040b51900306030415512605400242c0c01008480c014100b41110b90403158240100700d1400411141510000e102c81401c3d88000c843d44e101c100d80c001044681400424402449240503250300b0303102808a032800f105080e489440d118408494600081c042d0701000180941842103100a000386034052001c1e0a10703c8018002c0307048191800200240840d08000980c804c000a58400341c016021180703080060911711200600415502420340c00d0401140820300d07a1000c40d01110000000b084001101050b041d0f03003402c45c10303460010014040896480e0002c038002c401e0051448100002e070a51034000c2810941d004a03102c0720040e0014802040980d0304001d01c5482420030140c00280e101500002c210580560038201c1240045406015070071100010b5849411030030b5110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 528018947 1250 528017697 528017719
    0x904030206220201170c07151a0a0311120c0d03020c180f190f02180306010902130504020306120a0c061106070903030305250306060305060f0a3b0402 66
    0xb014080e002824000b80014444410303245012079442e07820360060098020f1074034003609900c034002860100224400c81c6941c41004151074a6a40c2e1201000007050381c01a04943c41e68950040308040e25841c2401340703804520101c0340c003009008100401000810304240441541402581c519880290302c0c002c80c1c0d018028035140c0518550148240c6031041182d4113541c451203501c00c02000140d04d141c501e5160b50002045040e41d0001d4940d541d031101c1c410040c001003508142c035103001a4400340c0aa4810840b100003100c0d6604c034482034800568000da0381c0d4071091301140b0040145e0110050300d00a000c100700400041e4603008040752107603543c034034011203540c48094a0f08400c0d2090004152558010000a402508072941c00090041c41d624084d610b2000d0100000c0da1401000000341c0d00d0380c0901c101900341c410250842c030b040d210540c4111850700440c0140f9000c0c0148000e0344080c400c6045240031900b512000070400560006d0022005411812030740c2d01910100d12501c16180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 528020197 1250 528018947 528018991
    0x60f130f030b01120f05240a062102030703020310150902090306060f180c040f09050c041e090218011b050d030c020712080c010c0f1202030606090904030206 69
    0x851581607a401c51090030140c0d01c0d00d2001400124049003c4451101c0e000002001c50420b10091180362051060740310078900803030034034144120080404a9007481c1880c1401010329403001302c02040000402c0c5001903009000003850101e040c0e0009515100b00f445d00c12030b520b000c2e0000380d80078248000042d046034030341805005a000e24a0400c0d0554424400a062481c008a80030605600a880014021062000d28002c0f50040f42d1540f48050002002c01c500c40011402034010018124100124100041c104940d13104902c905013081071110004200358030f05142c81d01c000d2002010465940072000303035003a0074582d1160090302050210308030346407a031403000c80c1d26115a4014050015048000415802070941e01a8141184600c44002c121078110010072400c01c3e0150340d03100c0d211800003e00300d003520030380101d00c8100b221b1210356081240e0000b10303001c069045c5040c096140d030758800100301d203400b50380390060340b02d501c94017071100303060300811074a0069940110281001301d01c81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 528021447 1250 528020197 528020219
    0x2706030b0d03210212090a020a0602070803030c1e03090c031006030f02040507050409360203100b0d0819021216020621040320071a03060f060f13 64
    0xc0c00c0900403e4a400390303609404240114411804082000103041501405120810300b00407206101590302c00303210b42040d850f014103808010480703807005110751820036056075242d01010703142038031003c0d021444c03105034000150008021022000d000b030301c80c9002e5a0166880000d0f602c0a8040e0007015014800015240214803c0c0c90700852000400480c3d40d00344001420001e002500f040001c1c880800d00c0202c41c054440d205440506400340040303651303101e00c0c11525140214a003000c3d10482000141ca000c509800000070820000409002440101d1100d03c1c20f080b0040c00c41100207a40c00c91603030b0381d04506100070141d5080760400b403c42d84040065200341c225100711003941d00712000c0140790030001041180c800920b0080f190361048001001d50300306070307002c4011802c2c214400060071094801156007401002c001e103074241c51300c5500b2414056a540100101000000003983c5480e5640b4070b40e140c04000c0c2042d6a550203200d00310300c40da042484140d01c03014019600042e806024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 528022697 1250 528021447 528021469
    0x8040324060614041202042d05090c0d030804030e10030212060901060207230415050114070c030b06011707180b0424090b07050303040b06041a060a2706030b 69
    0x4000401e14103410500030542d209085c0748202c2e07019803140308100c00350004110300656850383c4800c400380da101110240b002d4031130040407000f01c0da10844d01b03d4001c0c2e032100854a1815098102668651280d040c2180c0180c9500742d000d42000445d04900d40451703060380102030360a9581e842004c80c0d05e5520800081c144d0038400c84c00141e0161000340403403068030602105000c00c00420311040300c0028040b400343c90000c61565034136485c0c0700003040a540c10031503000780214090902444c110007a6103503c18290540805030900101d4400106240d0241020140c2841801c2d40f030300b4680340040c4c0003024000c4912881902200c04613000894a003040c00b80ca05881711000d000702e80710001804003860b410101c03041010040c40000c0098a003003c10001d00d85640a500a50b9a03440c00d0b04000c034180401610b407500603803400f00a03149510f0700f0182a041030be01220525920055004100e804050490070101c00710420003600d1041880360b5002c0381202c1043c3c13000c0c0300f400e1409003002400186 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 528023947 1250 528022697 528022727
    0xd0e01020d17190e0102090f0108040b0a0504060605090f100503070501020a080903070308210c040e150415080f0f0609070909170a0507150510060507080403240606 72
    0x10700b4810508004280da4465010881d00b001440020104103994207131800600c10030340c00d96001840010701d04203400461001d103021b080a40850915640d406c2402c080240502802c5a403140460100700c000c0e080301009180041041626050503490140040380594004103089000100003c042c140850f0b032404640b4141c0240c9003240c80d60700e80c5003150748a001111342c10b000d0080044000341050001d0002107110f4401e28200d070a207500f00c0303181148090316640509609020801c481d43c0d00d628065406010610081103100402c404580500803000a1b140141c80006d80843c0302840010001c0c20508002d045a00800b41d1010282c1c0318841550305161a401981040c4119800c54008880003880b8440d00c48101756402180700b02a040103280800043d80000c680007442181910481c1011001400b0085810900c0c2240042e1341c0f540300d04002d000e804508003051081690980c1c0042d5041179044141202000071400894004499850740500d414008241c0500c13403d002c00c84020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 528025197 1250 528023947 528023957
    0xa050d0b190623031c02030304051b1011070f080a03021c020303061002030d0c0815010906050a0c080909090c10090608040f0f05100c120207050a020108180307050d0e01020d 76
    0x511110f810481d1004100580e07018416540d032010781002c082aa004452003950107142c403070800e8641581803080c07500031050b4107081481444500c3d130340d50034100580d120703d00f043d15084c082c041d001b0b0b0800c10f00b548041c0b07081a96990000b41c84001242c40d0410b00e210b6820389a07540041d203003010f02207071018101801a8000e00005a0a080501c0200c0c0c1c1714095004880c00c01a50007840d4003980c41440c1020005030080050081c40c06901c0e00c081c20703041d0242000d10360f55050110081c80c40c01408134400400c801c17003080c001408032100865594090251180c4898600030000300c2d681c0001c80303a814001c141d62000081c261b0301c1110894140c544640e12039482e529151120400c090b40c002e41039403407044540410000410400c54220702d10a80100450384a10100c00906864690b40c81d80304083e0041102c0000a480802d08800081c2d0900742820980c958100c0c0c854a8018881c814a070340c4030008511052101c00200d0a00d444190755a802040d40c806004a0f01c91041451901c0803407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 528026447 1250 528025197 528025229
    0x1804020f0906090604030501020a0201020a0809190308060d021f090e0c040501200102030a0903110f03041503060f0305010504110d0f030e0f04060e0a050a06230a050d0b1906 76
    0x12074508010403c941004246900f011b44a0300ca0790b0890b0700200401c000350b940011100b04031a001018107900a13231210250002c2c000001e240101111b0501c0000c00300044000015642ea50b00c00c1d11607001600a0400040d010b83c6141e100b14501c03004103820086003401500107a60300b040468140706c2c203515451b00742018038200041d1382601c8012040c0310442418105030180b600b09101551003045004000300304c60105080103484107031079240008058002003043d9440305000000c640c21261480a1240b4040d01220202c0c01400c040d040001c04000000d40001808415046107004a01a48042205050080410021502c10080100b52000190741500481c3c000c0c0105111120042e050008500e00300001401b02c80d071503000101c1c501168024031100754458414654042e4500c0c0b002c11884e0f00348070b0403070021101012064696070080d104164151940f50000000b404040c0003090900007600d41a200c055045501c040c00160700a03060303031030710158020134045800b115000c010351 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 528027697 1250 528026447 528026449
    0x91a030d1101090f08030709080d09030f080d1b091d0c0a1206080a060e030a0219030903050303192d090203011d061009140106210905031804020f09 65
    0x1400c41d84000c4500ca540c2d801400e00071a001c602e40b210214420b8926a81d285400503010b0003940c0c6540000c0d02a500c50906441b0b0107400020b8041500d4228101d60164900c40c41e0410451140200c1c0d600304504024001100000c0c0c031403203e07070046040e21043c152031b0329010220340400300039a03585440f09065000c20f52004041d00200884c4080346080080103100307881d0b5005490081c2e10291203507002d440c0792001e21180344a1842c00d4403818004c0c610700384826800a68501209510702d12414403100c602e001c0501904060b00110b1781700301965120300d000e03207840700314120030820010b445080120000c8034000c64021401c51136403400d012403000c90140c88076802445201c504030381543d80d4000c0b00d0002c0c40b94044006101840a00130415807514480f4446005040d038010340100d8280b511030281482c0f26460a415034846103030040446615038464006451004a180080351400403a0418000e010008024007081b13034048201002900c02400b0072031068212072002094280152701e06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 528028947 1250 528027697 528027707
    0x8071a04061b05070e0601030c05070c090203070c0b07031a032e06090501180e03180418060e1c0906080c070c0f14150304020913210306091a030d 64
    0x2100c41c0c100414486040350380d074803840d042d02900051820b0003805d04103d840c0d80d01d80515480ca0074039181050a0215171340c7c072825103240d20300038665842d8000c40051600392203401d2a0300d0030340e00074050072818100307801c0c06030040503002c401d0546070b040a400e1003013a0900141c140302051802d5110046070040c030b01c00f82c40000e02150546082c80d02e401d0001452180c42c050940a09045015184143c81c0c960400040b900001204507440c3c2045c000000508240e5404484585003a1400328542e06c2c0c210144a4a0240f018014845868444110b0010b10300094070103c1c41800d0784c00c070500307006022065401562074850100001c0034040080c211804550145c141c152082541d00c042545900c0d8180c41440070350003002e1180002c400d1041c452424002031f90b110141400d13014034505003500410740048004000900c4200790903004e0b020000580c1e040140025445c0c1944480480498000c018210034402e02c3c042d6400c0074011240503801088500c50b210004000302070b0203400103025030f1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 528030197 1250 528028947 528028967
    0x1b0e0717061804020f030d0216050f0a090b01050708190f0e030d260117070e100501050306030a02030d03020d0605040516080405010204091b0315030c051c0f030908071a0406 76
    0x60400101a00d070b0742d4580702005400000031f11500908119215440c0c4003841c01d075958400362081c400002d00c044580c41707001090060354845200810f500340904016201da00c58044000c20198000071120550000034a6820a8a0f282d070f90701000740c01c034000102e51400c1000106545500000c0781c01c1c00132405115040c0101541038580c40034100030311305003105107000740e21911200008250081e001d600c24031111014000d40b03c1c52111904014030ba100760a10135001c1c55060200000200c1c00c29540dc1011046040e802000c03a506807000c4800100a500403c54502c54182003400103e0740303181c98083c0038400c070114180302d41990b030300b02c204072403070b22002d0300603121950f0800c00884c900c081400303000c0d2942240d205198800340caa00c4014100c50519031a030002c4182e9074010300000300e400e4120030450300119900e01180c1c030400c0c0703c094043c401e224000c1001c07034001d61420070143c1108a5404071900007054403803141da1410140d0542000c00080080d4100822050140c01c2c003409a41c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 528031447 1250 528030197 528030199
    0x120601030b0a06111606080601021204060905061b071517090a080318060f06100503090d03110c1509010b030f030306010305070c0f1b05030102070c030f1b0e071706180402 75
    0x401d20700c030100d030b4a4003d5007170390800000101904c0400280c1d5804010003000212828002c4d841c141c54680c00601005e01e902a00748100030010b106249081d450440513808400303003042c0c1301419941c0a083c009230030f030b240815000c12081e03020701e02041d030006010791286410b42d01608240c10320303543d60601d5a00003070141c61240001c0003600d20444041000034441c0062440f2100541000b404100000a100301a001085010403c11092150100b50420050031606000ca800030360300042000500800b41c02da840d0344601d18840c080c000c00314403401c0c02030a01c1002004030100d140d003410b031141254251220690700410104445511a030b024551086031407500e42d910250035614001d43d01c2c1c900000795003242d080c0140c4000b81004803a00d1000b840c00b24001c500e8201d040d44c484001e240203120240a040200300141e0911003100d0251180c80b05090350050b1240d2110389139042030380286c4903040003d8031001e1032100300307038100d071014080c0c1d4005021b003030304803014010444003010041081b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 528032697 1250 528031447 528031453
    0x5060103140403030f0522020f010306080f01050105040e01060b0301062607020105060f09070f050f130303020a0c05040218040b0d062c160b1e04030305120601030b0a0611 75
    0x30314100300d10007580502d11a60340800c014103201112019200d01900c003c100000c2810302e450761108402ca2545400e9040e10501413000c030050050b0024140e95000e580c4500400300c00072603080301907202506844044504005000522107418221040350040503000358081005000c03042c011820105481003042203801044040d14101c001c0e0b20f030039030b43d40001d40c3d1504203200030f62805501c6240390000035980350401d884c015800416904080c0d40b61030a00c88006503061564540000b124040d889074038441010710368914000b555600040401e42d1091320340700d4003148610b41070003101c954100c084002210301d0400390401004140003a00c03250310042c10156100050018010720741406000c5040100c1c515246005500081100700d046000e5008032401c404040750703160b400f406841149450701d494010541402016212180d0356514490001c20b0010030568004024601c0140c0d031251104c0c0c5481d00b84c01541a80c26520032145e1080520760180050b510030b00c2c040c02c02018207012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 528033947 1250 528032697 528032711
    0xf0418151109220c091d04020a06110f060f010e0901021305010509130c050c0c0307080331080706090501082a04090501090603020301060b07030e090705190806100f09050405060103 79
    0x3d840122210010000041410b40101304030300030382002c0c01c8080fa10b495501089606e40f40c0c0c00214140c0c050702580f07091265515680442a20030031054180c8124501251102c1c24001c1280c2401c560910482890001010014801510600944500d921003d4042c80701c00d05280064805030082c0d500b60307402503031400d0224655a002d000e00c0c0410307040c50310348c103507103010410a032410401d1106815000382c1c03001508203d800341c0042183c80d624600407602041e10804100000f0003c014000303603003e00168031010a0070780e80406d8841c12103855441d9650400c0e80c7c1d00064620320760450300b49401c42d503100e490400c0d54184450082c154403580100030300d042c2d16003c80d60121a4280c114128081d650a01441107003824031a580190a04010082c14880d49603001004201c0705c14100e8000c204110129040a000344103841c400400380b41d203041d00300c24a1a00406918046500314480d0282c4201c2d408454000c250400802005682d42c1401174180f10900c4041c05001d45401e04050361550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 528035197 1250 528033947 528034009
    0x503180909150c072a14040b130203040f051b130c0f0f11120d0b2409010c0b0901020a180612021303120815040203060d0b060f0418151109 61
    0x10140784030403820076100b07001e03806c000f10305544040340030040e40180d10f8401c0100050784c03038040e00304142580c0384015030340c3d0350b49140c174516a04992000800034480d003591b01103081c03c0100107904c1000c080c0c800605442003184860240c03812040490f0200708060144640076100b200100051702440c00c100500400c1d81810615000b07040558119035500403900b51100740301d0303004082c074034001242c010140303900000044110464013241082e0b2414001104005a40907540d05c425043e000441040103240c401403042c003039440200c01e44005095a00c101c9000c0700030b030600c00281c1d07082d9944c903818110202840002580900d24011499440000000006030071050646d013000c103075506c1d08028144002260150364050741050300c074a005004000c0c82c4d44894400f40c54a9402110108460301c4410200b00015180c8541c0350b04030f410304140c54107081007400c0d603c9100f441003480701035060b21040c4c10f204644140da1252044007013084150f071646000401d5809440340e140d844404102945 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 528036447 1250 528035197 528035243
    0x14070c0501080a150b040609170c060c10090c03110409030f11010908041517091b1c0606080d0503060306040204050603160320010309030210020f04030503180909150c07 74
    0x390040f545d80b50001014002e8562100c0b5050040200c90382e0141520030300406140c65001a0780c0031402a01e0104210300c00c01d0701007100f2590806085c1e000c1203121600d09120401c1c140c5801309462144008240c0070060070310348100c0032002d4041d40c0e040c005200e115400c0b07801943c0502c00308095900d80141034003040d8a41c0040008012261541180a09070340010b0244d0140d1a81d29480060031001c01108450105d100d00e00c60004151a441481001002480ca40c9101d00c1589403801c03034052200801101e035000c2002e6441d900100ca40900079000304441c41d1104a0307059405401501c0420010f00341504640d400142c01415a4201032000820044968480e401551299403030104a52004000320384c5010700310007841c0511000c0810746029640c1d914401541c0c0400c0d9000800307260140c001c6055801039903014050f04c1d03841c0b540c0d803071034910107407102c00803441401054041808568001071030b085200300f1810400495684250142c0a504a954262110b81181c007413081d0403081c003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 528037697 1250 528036447 528036449
    0x201450305060a02030a05130b04061d1c0801050a120209070c080d0c031503050d0806031e1b060903100218060c24090c0d051501030b0714070c0501080a15 68
    0x3c40700580302c0c0b84c603054083c1500e2003c0d003140c0d94078a0901f811400300303003414041a8444c0d004003002c98668081c803441c480c000d1905c1301c000800d018204607001c40800f01c1e00c2c44001a800c03a41e0711896642c8076020407000d1342041c4036400b0507601040e00c07200181805110103078010303014140014850a55100c404080e440001c0c3c0080842d0ba03403181084441e003502c1444002d401c12100442c03801c1c01c66039815900e1240f02c41e00380c1400074041c00284590b600f0000000002101c6070a58a504a540c040707a660741602c2074140164403102e240c451081c04c1040903101d0441009000344600b0f003030f02e0386940085d409140d6205d843c0010f030725403000985800000b0260100b110008250403103049007441c0300c48080241c1480b1800c3c01c2801d00ca44000002a00e04140000b221051806c0c0d405207411840e103001041051002628840000240251403030480c0c8188820346411007500c10343d40f00c85c0354900c9000d200a05008a01800340802c0d441000620b80c08411080c0009540300301e5180c2d00070000c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 528038947 1250 528037697 528037711
    0xc03030106090f0e07080a05060a03050f1515010906050a05040e0c0d0c1814030a050a030e1c02031203150a0b090414250210020f030103020145030506 66
    0x140c840c2041041d4441d1910320080813a160071210b0350034001c400602030300015104911458540000c00c1c420313502c0c44182c90003503503c00201c6a8013001123400503200d2100c40840002c10122100049110407400d4107103400100503510003510300e01700101510389401c090007031020171006110115050b4070032a002401074030246e01381c603180c94090310314005a415220100c420800043c80c4488110012107145041d990444014a501d10108020914143c90b001010702948a0903101401b4507030408815124000c080e030b11070049102020220b2400c0c01d80035402501036101c0896041089244c1020315001038041c240c0740d2a42c0d0060000600c1d114164018100c82c1c07a00056840d01c503d468451056420400c0145558030b02e050445003140b030080c4000300202c5420040d68140c5c0314402d1103100180c40c0540c81c1107407030322082145612281c000f400200d02217281d04040c420808080144002c5051300548100030104548490f00300e440800407140807103410ba008084000358003400701d1340c46445 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 528040197 1250 528038947 528038957
    0x2061b010203250c0f0212100203040c051c210e18070801050406121106071e0203070f030b07110c040c02060f0606071203150f06050d0c030e03041a0c03030106 70
    0x3d491412041d90804080f203a03414803002021040000784a60304111203290102c800088032090010404d041a0400f07416500c10b81c030005c00c020810800c4d0039048269002522528480c10380caa59080d000741c0c0c202c10141110700300091460241c501c980c52007003200c0292604004030010030300400d4407032040320364011f80c00d00310004000011390f100741d4413030050034229000e01a240ca0403203003000e2411500e0380a803440b1500f240c49001922141c08558025900584581c4106440264203482c0009000128441c0c0614000014080c0f03180d44100d007520741080c40e0f824243c4507440c098407110860000c8101c64015440f0000c05644c0f03c1c4540c0032442480d40240405140c031441c01d240300c0340e00a00385c0c2d01c1031806001c40d00c046040080243c10f00741d600d040000703040301090000c207040e0411b81e1202c404003806141c00b082e915030060151022070464201406840c400d00019029501d0040900d4a80ea01c01c0c402003080076256020f180800b0014103140c0d02c1e00510381c00007410b55100b604103d010072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 528041447 1250 528040197 528040231
    0x1920120a0c030605010e0105030903070b04052b0905010e010c0204060f090e1b15040302030d03061404200904060e09030c0715020a0f020303091003051e0f0402061b010203 75
    0x42100d01074028604020302e0200f00c1e01e810076001800484614020303d04025010000484440c010000c41ea0110340101c250403c900c0e051500e566605203002032180c016a10412503001a0f84c81c0313071550071100403a1941200705051100445005000e60304550410203040b0b02d00c00580c84030b20501c4094801032402803c601d080207415426104100c480d80050b9020551007040801c0b45411298150b00403203d0060040058401000c1c50040741c0001e90b15004860551040640681c00301c42203407100c0c3d69400c605240b69080204440000304d031068281300421401500d682500300400c0d0ac518028030005082d6280d000002c1386072422101c110443e07000054000b0307480c5e01004440f00508104412448850120708000d40350380c00c020000380400b06d440000000c543c0d01303209482c010b00000d42280c000b0100e80400030080e10f0103688801410a0315056041c1d42500708804a200380d0755155400b41c5a01c0d03a07400d0103881c1d0f00400261401c1031f1740d01001c11090500780001c600520300c40314804440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 528042697 1250 528041447 528041461
    0xb09030a0e0102070f0e060a0812190e090109050c12010909020f0625110409050c040e01111803010b1c0314040e130c0f0612060608192012 61
    0x104110075241594404981044000800c0d80210190b4100c00da4086058541c0c0000c40d03042c8500d03400410b890b00990349006840403840d000b420040e101c0b60140d0031343e45045001a1444081c3c014100e4004907040c1c01408a81c0c0320381c001c160001983e07004145001c1d25149106001038080c0c01044e81261194251800d515007034142c00080c1d041110040e1428805c0301100c030344d002001070007904c82100007409405000901d050258405c00c040c100380201441d500d0031507101c0b4504030180c0c0c0701d00c2c41c00d40030190818051080c3d030f910242501d442c6183c0350001490b0180e403622108000d40c15903c1d2015001581c641c16806401c400c6220300580d04280c0502d006010f00180320040517400070140000c00170721848240701078100c0900c4a003800d80103445c5c201003000e0000d607000311040c406204030000d005035020800241000d02a003003040415115101184c8840c4143e03010000ea2000309001d1002904907440000700642d0030306105205141110f80c0041c40e00b041e0341e00c03240e8000c82001c00042e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 528043947 1250 528042697 528042707
    0xc080f0c06160f0503011a09060703030f0c09050d020103020304020604080715080609070f111501081b040b010c140118030c03110f3711011b02090109090f0b09030a 72
    0x1c0c1030603030500360603492060f54028403502051050300d01002840e5000842814010102d408044000d482e8554540403403d025010700180030050410f540b030301d40101d00c024480d44142c000d032000107250340c981c0c42c425001140a500702a000b40c0c1d00c80410000020068800c01414006182482c00060310300c2d40c1c0200035201900082c441400398180380700b017110480e4405404070080c441401e12204100001807140d24004844ca0701d5100d03480740301d0000c2064500003032044202c442c54800001591401001d21040c0d8100c603c8090120301d18103000400a148526803032801151000000740c007500044091000740c1001e1425070200341154449014150b2000845008421140003072010441c800002e40da40c003030300c8a41c141c1c00038189003482d414003680030b0b11030112030032410084003408813410100e202085468000e8080351604099011980d80d825044d50001e8004100001681c070384515a8060905600101c80c81001d0540b00c40c006401854894041d00ca844010f50b180c0c404c4e8100900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 528045197 1250 528043947 528043981
    0x50a060507050c060304060905010e070f0801020f09220f0c030b0904031d03010e0715111b2403070305010306060f0b070609050705060c03070b10060f0c080f0c06 71
    0xc001081041d2004034400281042d10000f0985880b40d8a540381e040140081805600007000c0d5420500000044400000c601050300c07400d8550744d022036a0785400c07600708c1c401d0712800c0c050500700b403202805614101c0c82592048156a603042c10704030701c03810100d00f11260580d09008240da9031620310b021551600c92074015041c00d640b08880d50030140c90140c441d0680d0500d1202c020403a50742e558003602c01303400c6031002040480443c0e4080d920760100040b43c50f1380c1c030340c500c4c00074503813210312800e0030b2000500b480c1070951700203080c1541e40c43e00f0510402a11610052180400388148008501c4102000318890411380d1b4000409504518040094500b5a03000c1c812039014181d0074005016000103c4000039840200018426414030f4080d0800c00b0952003164010008607099000360310100040010500c43d00d80c100841e5180011824440d96600510000602510380c0b490000c2c001d030403079941d582c00307040520b00b0000303800d010a0700c0e640000005800c503080941072106079040d14501c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528046447 1250 528045197 528045209
    0xd0201051909020616171b1c0914031204060e0f010e1c060f14041b060905010302071106031e010b0f070b130515090d08060915011e0306050a 62
    0xc4080d102c1d40d0002000c5001d51a4510030002014441c641003110820301021806022040c458a60301c83c0e01c080c00c030601007100b03500c020340102011050700c607060001b049040002a15298002d60901810203000600b03418030f01e40501c55844660035045070307080030300020621540c40072112440d507000e025007055042810b905006881c05107220390f95840070486c102c6024140031038801c2d0703c0b60801c0000703406031428a984107403034001c042c21074850340c0117090b10481c0900030100f070024000952540a0947e0b00c128800a03e105001340081d6100741c0003009054002c480040c800340072540040c1e441d501c152040c0213041c8040000200c0758003c4050300340103200d9030303028504044202d0f240d02e030342d481048401003152201c0b400140ea013460201956628640100844103c07581b254007010b0030510075985c61050340302d80240307064028801c1140710712900c405410b41d40107465014000490507580d00f00613043c4040d8075400c2e03040455810080100c1102544e020803024905014408006250342001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 528047697 1250 528046447 528046451
    0x40b070f1b170607090b0c160e011a091003020306010c02090c0901091703070f0503041d0604050114101b02190e010b03011a030a06030f0b0a0e0307050c150c0d02010519 74
    0x42c250000942c404861601d400d641c1e1f15010b00c030f0200c1c00c5c2100303080ca00c01041c1d19501c0110300136081d01a41416a45000703680c0d0940070700c1902d101940d004006650781c7c84110110081c503610302c682c01554106206040244020030290b0000e06801e4049071b110301c0840001c24032401c5036074001c4501c0020f04805407207100314101d01140c152688600c440c060148011310b00e00204104040040343c000f0a0311006129241c81c020101039074030075041d5040c0f032089060800100d0902c2c1001800003840b02d0040001c2d00d1411041d200351400c80c10307031601004840c0200c10342000b68031786031880451034400b242152242c90401030012003240e4180c000c1000360406100502074084c0c01840d000b440f50b0708280003038880e5a0512100b0181209030801004203049031204410000c030b80400d503000700c0304243c00f800703000c88490016aa0380501d80c0060902e6008100b2141e0324100340c04d250080c2c211985519203801d042d001aa40303440a02c9003004010313995413082024503d00700580c4000c1c20210901 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 528048947 1250 528047697 528047701
    0x10309020a05190305070909290609040501021608130e010303081807120f0218270111121e0402060712020a05010c0c0611030c040b070f1b1706 63
    0x300d20981114015180036143c1c0c02000d0a100142095940085500000b1540c1094031982040040c0c25008400c44e490105041030341070401e85c54200b23000029200c811244c07079545210401c85842c80c054030507101c0755800c0100751034000380314070602a120702880c08103950740702c94044031048005a41c000050504010010320010f0f610100322500a140903a00c1e41440b07030340c4c009141c01c080042e40a400103040310140c2c803040203c9000d001d06000e00031680d015490045126558810341d088030074122281008210001800c0005c0c0117204405034900000741008403e903540c1c3c0c40354400c158510340102c41c60b0400a10310508844a401e403584401d1201040c10070f03038003054a80c02441d4005041c03450500d030031107d451082001107405a00a4028041030032400700c01713440b4145503042070b83c03071509065021191011441c01c503401401500e6900b40f0302882c1003268002d680149e2800c4440040c9039003441d0110380ca980b558010203d07100200c1c589540f425038040d40e03991550402101a40200003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 528050197 1250 528048947 528048949
    0x9011202071e0c0816080d020105092a0a0b0403140106030209180109050a12020c120a06150308031f0603180b1e04050f0d110303150112020a08090c01030902 69
    0x2000148900409401100038a058074008030480155000180c00307218985c131854000e0b0610410f002240c1c200f07420342da007544250030201c1c01c0e25001c40c2c0d1013109030701c0407840c00703140010501c05007403031030758000d01e00890180340c0006803240906900509038802c0209050040c0803a01c803c0c199442c506400800c681440e44d80030070818500244008041d2944402e01040342500f0b401485100d5400360998410140510f802d05141e900200b202c40180b1448a214110342481281c0c07144400d1000010510001155140310241407081d00d403908070002c80750000001036450000e14003804421504620390381c0301d03154009481d26103900440c00c150510304114583c260030482e451180d13800034090300c090b42e0740403d05800503001e901806003008000d41040706024020400d4005070200e04261030f509522200200d4041e9080000403501e0f4000308041000301e100340803d0b264a080605003101c101003c64040340403a00700d161440c000c10000c604008200209001501c5403001c2403c3c1041140005d030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 528051447 1250 528050197 528050213
    0xf03050601030620190801080706140c010e07030c0303030506040506010c110411070f050d020309010210020d0b040614191401030504080702030703030c030810061202031003020a0b0901120207 84
    0x220016004560703419500007031301c405181158045044000c0381e640c031482c0304107900303880800602c0b00000030f40c80c400104002101103200303402c07607400d07945555505005080541782907011035401d408540d80d81c550300e05044818059100294000c41204088614504010f020780c1d000510b2184580c0c030703050070080341c1d80c0c110f4038001c20141c2004100c001041c0c5200400d0082c03c03a80c540c020011004a006410030001400c60fa107524070400645100521420080c0d070344c0d00500d410280540c01401a0031300442496000d0b00c00690350402c08100b010002d0041070072500b0541060510040303000d1825201d0404d091914080e0304000e890f400107919080c20a11550002180030341050344500c00303e018071404900f0b460000f5001401c5d640031540e28a030103412528100ac0031000702c0da03680c002a00c0c044214a11900702c4201c0c3c0c4903000240c04401c0c1100080d40010049460011003003800320250303d445010001808a684480b1380e920003100015020320b0300300d2543d0224a00410848002034014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 528052697 1250 528051447 528051449
    0x250b190615050724090c0f05011b06090f0f031e1b17030c1207030209090601030e0322050f06090303040b0f0403050d050d0b0103090302060f0711061009060f03050601 73
    0x16180150300c5858034074118950440404030401141d401360b20400c0c41107032544c040d403510f0344036112140e4a903a9030050118251114412107011a0300026010203491501d031031440c070103201d05400a440f030421390b030f030303007001c0407003078412b0b100081c4446218017059008a804104003d0350104180b040c1c07941ea0005040e00e42e01503146003802400d40100040042c01c0780c5981141034025005500ca240814680e1196048140800303881506d18011401d098002d100f150303103a43c409444e0b0490381c3c0d07406005402a2020900b614030300e03c410800c0c000340c0c1d00c032007940b80682040c6c5413114a14a1801081040c0c0400082c0c08a11980c003c2001d0b4480e5500002200c1c100d40c00310b82c00c0c03611004889010485c5004991028049002d14000131000541c40402080c5c414240101000b47c146410011001c40c0d256600007805039000c803010811400c0c00e101c14940c0041e5070714041a450001c1141c00c0d0500c5010381e4074840544166406102290581c001d01e00907103006100300441d00c1c0303035031100b564580c81 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 528053947 1250 528052697 528052739
    0xc081b030a020d061e0f1b050313080708041502010b03010e0312040b06031c0e01091a0a032409090203101104060c02040b1c02040b04021e250b1906 65
    0x82d614a050351402d40c41c2c1341115072417407440c0c10072040074400c2d000c0c0080c11206002103003856041442c0c685803406241034900908032000c026100e80b030180d44511155029540544490a0034000001c007800306801484a18505070b0011441c201a20181400e4800f807905914541d001404405419000d403c00c03603621030b8000d200381e0082d0b00c9071b001203805d007500d43c107812040a02e5001e81108454100100c540d050f442a42e80e1202c0ca55580000303c0354400e5840c00c101d8420041140350b081c60310a4010070b0900c0740c203e800a580381010405002006001c1d44807136200750310741d002c2900754a818042c03480412241d10f410301c04543c1c5910044520b20840c013600c030500814216803000d5449503070011000d1000603000101ea4650112164229008104200d110303e08040014010b410b0a00a0303510030700d00103103414007080c681aa01d103000d41102440c5c00c000440c050700382c40303d41460746e0301c103029501078140e1030258103000c030a00c00004041c4c4a8141c03000c0c2000d000f0800c15903c4c074444040005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 528055197 1250 528053947 528053951
    0x2107170901020316061b0503010f05090c04030b0403090b03010801090302060a050f040b071103031008190b160516030c050f010501140f1908010219090302090a0504050a0c081b030a020d06 82
    0x134510f4103400821403e10000401c6011481d12010b440c1c2100045068605078840c1a00702c681da80204103d454048400b5006001d040c482040011300c1e030340030b040e0018401c2c00c1205280b51070f2034040001e500240d02a1003a81e460303440b424189030701032050039000484810140842d1605101d400c2c2801000b420003080c1c4848080000d0090744101400c003a02490788095980e00e080c44041c820842140b402200017a009128641680710b810041c0800481da0194041041e0b90364610651003d81030080b40d00148042049014201d50b04070043d100f2140c483e881d1502c230886203090451900180c0c0742070f01c80c40e0b89410014410060780301581d0201100460380c40d4113102d070703030380101c0d500d001c0200070780c6c2c00403400403c0030030540819000351001c500c1c05201c41c465100c001c541210000074920000e50841054808280343d1460b6030082588103000d002111000310150707580301d074031059607400389aa0350031101d050301c0161100c0d060715400040c1140200703000c440c2900081d003030404281004001503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 528056447 1250 528055197 528055237
    0x60219090b092205040b07090b0309060c09120f060703060b0715090f050a0507210b061002010b0303121504090b06040e1011030109061e0603020c21071709010203 71
    0xe0000e90242e094004404020f004e9814986003d84109006460810200351850000b0a49012140540b4803c0a901e40145181d480d001050300a581c461a50f19030004e0503402100c0c000003080180310407142e81e9500501c01c0d0303d0110740080480c4d07450381049032150300c00c000980219540189240045081080005101c200ca01d0200230754100044010486d00991101505010022a0b4a02181c000d900c0115181c428079031518601324140b2801010381907940007041107070800741d03c20360208016000001d41500c11100007460358210300720f042c0350501c0c0d804c10002800c00040a200d2032400640b01400000110360b43c60041c0300000700024081e1f55140220510030b0001c00c107008a290800c40c0800481c1c402031502c54065000b40242e14140342481343c00960b00449562202c010404e2402c0142c003a420f0000c128040d62164840307911900c40c0c840c20880c00d40c240700c91001191014069541d84040c07900c0e01c8210f600100021104900060000c110716176004001c0341c8a450f40d182c03241d03060b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 528057553 1106 528056447 528056479
    0xc150c02131a04021918031a07030e0d0503060402071a090114060910051504090513150b01091403120a1709010507091a090904060219090b09 62
    0x43c00b9041103510305d1921844019178aa940042c02c01600d541ea0740f501c442582e4842880401c40c0c40032010b0001c0a509489405d00520501002c4d00c50813110f050094003600004018038041ca40005101d007c0101110200552000300003e250190901100141c001e01518041105e02c506040110f004c9240c40c00c034091080510041070884903061409100e0b00d88820500c8c2840d0000c00c1c0400f0440c010503001d414840c0018070411015160a030600188000141d542c90b40f92514200880300c090340e003d48094151011898620002c1740a44d000c6803409203840411a4001d00100ba14810310354000383d0031517030740102c071501c50090702ca41300c9841c02c8540940c0c040000c990952010000c4c0311501010008108404650a050511000c0854180d500c2120211011036000804c211823805018040b204d210151400380900780c00c09444020078860628114800c0982c00c20034600 = true := by decide +kernel

theorem cover : BRFrame.Cov 527877697 528057553 := by
  have h0 := BRFrame.cov_init 527877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 527877697 ≤ n) (h2 : n < 528057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
