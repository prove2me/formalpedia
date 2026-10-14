-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1484
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:12:05.231365+00:00
-- url     : https://prove2.me/submissions/b3637223-2cbd-425f-af3f-1d64c9b0356b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 266726618 ≤ n < 266906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 266727868 1250 266726618 266726627
    0x1207121101020304081e10090b0601120b03030d0203040b1015031e0618060503010203010b0d090c17070905060d03090e0a0908040f0f0506030c07020d03050f0721080106 74
    0x1051584440c0c04000260030000507811400340f034205280b188204140040c0c001c012219140140c03000c181a95202500c0600340d009413500d200e406800020b00b1404140154403a06c084900e11041141c001448188100002e085034044011005201d8012040c8014007602480d0701d50008500144204501d00e082144804480d200b0024000c0c142d89134610b0441201102d40c560720107807031900410166445076107405070201c6180c00406100e140031030108142c00c2c14400c4905950500c2c4c0d4150801e81ca4802600c09000c0104080310400b154103400180300003d00741c030b424040400300107040050b0a202c40d020860f10014070030780c4500b41c040f5082c1c0c046a08005641f0030b860a40009030308a84d50291000c000d8103030100c00901c030580c00603002581920007440d0505441404030300841d200d43c0c40d01004418042510050804d0300c00b007140c500180b91504240000902c64142141458440c0903c1d0599400043d07060303892000742c241c0d100032450310f400180725903140c50500110b554113025000300f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 266729118 1250 266727868 266727899
    0x110c070e2208030a06050406030c03150b06090f01020c03010f0519092120010f110c151906090204030311010c170c070804180b0111030315010302040b03151207 70
    0xb000c0350800004121903001c0c3d50040300140001800501130380740c0c0d03454240b9500480388020307540130110b03102d114203411031405540700c0042c005003000d050540200030041a00340e101040d6042d4401d51040d104c282d1801c2c026550360241a0b030000031180ba105441e0302c804a40c0302c2c1e0190060785400380e004005103a00400a81d8040004140707040341603c5082030b030f11510026845d01101407003440c0d014071b801d015040842c08445412003801032a004126a804c3d5020721a440502500000d100381c00003e0003403120b561000c0610300138080340c4007200d07490b8101c0701140c103c0801c4540004041c0f00f8140c00108042159410000070010505c04003402000740907807100c2c850b444100080840d40781d146082c181c0d40c3c49030704000615503466071461714007a81640c042041c59050b0429100401a60249125042c190103440285d8a1640c0d6142c5021450586140482c140740e407d000101d982c0161802071441030040c6040d0591404d114400c004424680f85ea080001e0351081005120203c0c1c03a55010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 266730368 1250 266729118 266729123
    0xc1203020708030c07360902030106080a170d021308010209031203070c02040c0e03010e010b0a06020f0a24110a0216080c121009030c11060a0e100201110c070e22 71
    0x6461b101a14a01c0103e98500002001d0580c1c1d0300c2680750b05921015800258154802c40003004110740c4c41d068513486208410018101c00b05d086a007180300000c0c040140004c1c500102c0c010f05e411401610030707aa98083c1c1e00580c1079a035011803855480e04040201111980c1810740f07403425442c100c1fa009165110325440240161744480100803100c0c010280c8400f0071070010020700c01089150a202e009180c0e0100b00380c07041c415040002800d81c008519090100c00c3c880c0905180821500c805200a008a4540702080484400f0302d410000c5072088a40c2d03036080c0c8410f45d07551040d10200038a403816a511860a007420001c0410520400003200341c28000305a03040205031410151281c00c041d003c0b4000341245043c440c400080603400703a26404558842c41c10303e007540b02c0340700901c6124050000d00c03101081c03030020200701a2501c00701142c00b64001d4070004c9080100380088010710703005034200458640c071540003030001c0700d01c485640f98003100c0c5814407501501c020b04000310488284601 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 266731618 1250 266730368 266730389
    0xd020d090e181629040312050a180f032105250204090b0405070902030c070f05030d060b09010e1207120309082b0806010e01080c070c1203020708030c07 67
    0x802d400001803210249842002c00c0001815a991100384c03148015400b45000c00c815040c003005038059040161070a03a0b402071800054013a10700d0054a050f030005d0010424040111440e00800f030122010f0005482520813100c805441c500d00907255428801e5001c80c1d00f00024004524142d101c41513584940c420000c1c0920000d81c070302c00c2046565503140103500301d41040030103000d0102011505024600c0b0303d00310380000742d0b140302d28812070000762136100001c1810840c0030085440c000c6ca002d03140b4015030642e490100c041000303104892896012408040e070105602501d5a040403d43d40b00e00c1c42030369010b019680d140c5c541502c1e6100c40c01518a001e10101c030603020315100d1107104001d40103840413100c1c8041650300c21000d0340082100d1511848100b86c0105a11f0301c22000c1900600060311008002a000001950b03130b403500501c2c442c810701051040300081802851010024440c8260280b030041082c10000d041512540091070a0340c8200303d151aa031a00044442c02c82c1c42c035080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 266732868 1250 266731618 266731651
    0x1090c12050a020c0604050705010807141603030b10080f0c0c03190c02030f0f0607090509040b0a0b130e0706050408070e1e0406050613060f1a090307080d020d090e 72
    0x503400000d001d4203000011030b20a0001b0082002400182030090b170300240c03900512659800c6003110b6481044645c0790b201103040c407d404003071880d40000c2040900c0790502150820000003c580003009079840507001408007800c7c8503080710041140d9800c0400c3c0c490441c540301c184000c20b581d0f846510b035078141c141032819200b241e59208484812013a9801000e507070503a003072220305660b00d81c4074004588041c0180c9020034480341c0a102c1c114110b9201070030307440a5a8854448000842000304103148841c0c81c0e1400e82801d903a1004548002d810092000891084000c407051402c0940d03000754050003010402032001c807800242c6001140d02c2202e00d030703076141d0f10035841c040f40d00da0103010f0000c030f044c00805000c00c00c0815041640f196200352100f80a000020050030141ca00c144542d2000d101042c0c01480400b1112500c1d4030b21500e04014036160040560110f0b140c092283d120540b1500284e07401e000542d4180051424a50382d80740000c00d9605005407d05510350240c44d152501100306c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 266734118 1250 266732868 266732881
    0xc03090d0501110a05131e050f0a0b031306060b0c0a0b04110402071202010b03120405130207050d051b070617040201020f01050106080718030f061104180b010801090c1205 75
    0x10000d0f0300c4821081082900c0d05843c030001352072034025916454000d0020b42010842e039040241020982001d4903004001a00d01000d12010b000e14010b800e40001450201144071400c0380015805800d4500d040b20502c1c4440c04c051044400c140c200900e00c1008111209a02c007001400d09601078202d08505110303112890500746110b009024150440d00200303601e001e00c441c1c07803c0500011869002803214036030744010162a06100f111200805406001c00d2099081001d07641e601d801108500511703105098681c2460b02695403482d500140d00050544020492100c58092180500b0010003586042a2018001604000310300c100003651600080075607200b000175142480e0024001c11955855000090140348100c4009c0c01081c541c498981ea50400003d080702180d8014050180010b555503d03070003c0c010a55102d00306841c00d10003c201d41030b1049200e114644108000181112140000341801c8016842440142e2400e04010031154200e00715440e640c5a004000421341d5814 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 266735368 1250 266734118 266734121
    0x70e06040e0709050403020607030606021507030f09080c0604020103150f06050901120203180d090f05040b120d0e0406090504051905190804030b0a050c0f0705120d1a060c03090d0501 80
    0xe0380f110b900c01c1e0401003448149900810128080d4880d96410b00c01c41c1e41380e603000c0e41d5500b400d0b01c200300a40c0c0d02900003820b5501c6640b000e100c6004404002c610010700380c682e070156400003040000c03590840300520045603014840c0e800d00c20b040c038442c0e64803546450b09045000c00140714000034004005032610450f841240aa9080760191004541b2810110280c02c001813110760740360850320a00e880325940f5806036600c1c2c000c0f41c2c0e0007944910000d0034a0300344800b402c0805101500300b4072014034042c4a9105100c2c02c044125541d0b9406050602070003040b0075111250300c0a24500d25000034400032030008569681144103582c01c10010588528125260040906d84a00c102400c40d020b80d00700071005004004890280b50804103a8a030300040300c0481c0d01c1580c0d070b101c426104100d406040400c1d40054000300f0300400c1901c040c0b80800032070a0142e403000d140148055902c0c441e90040c212006210b80b1081c0301541d00501300020544080d41d03d210384500382e48034216059581080000c01d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 266736618 1250 266735368 266735383
    0x3030c0c0b0309060604050702160303111c08090706090e06061303060c0c060f020a08040312060312050d0c0e220b04020a020a1a0405060402060f0d2a02070e06040e 72
    0xc1000082d0380e881e06048650b16404240c2d102c40c8142e00344004148103c0c800038002400481001d040010140395036010344400b55403102030b140c2c50044a044844003001e0790030300d4060311540d407503070041d500d06220742c1402c00f07811f6000b84060050400040c0034168600302080c0c1e1180060b540759070b96203801e421035406440142c0c40103210505250010003410340c0801c0c462480c510448007840314106400d405400d90042d180e5850010b0f01c001c0001d400301e8403411106041405080000411980765254180b40300312090348407010600c00110000c0c1c00c0d4052041094980340c501c1c01c00507244c04007000a02c20381a07081600c10078001d00b040002117040c031317a02600282500500c00c565031201c1e1103000e51128507083d42030340c0c2d09040340c24599203815a00c1181d4403d551101c00350959507a66800c02c0b009421120700d800f04c0c504141b1400300284034600c9402e019101031408070b400d10103522014404028054020021908a00b104010f01c0038010402c7d50400700845020509030394010390b15181070f96 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 266737868 1250 266736618 266736629
    0xe01081912050c250b07150c0c0804090c0806030a0515060301060503011a040b030607080103020103021c0513020a091413020303070c06052101060203030402010305180f060a15060903030c0c 83
    0x95480240311400c156800003800c0d400e40c40c1e00d8402d945c1e075151a503000d00408101400c2055000107c0e81d0149041d844800c59a810741481410080c45072103407141c0d43c00c9500080d1505581f40402407113150400c2c06175038403800071002030030108095503a0f641c4502e000c030b001600c00c400002c0840e03159034080d0020005054017034000c100079020603451580004031940018000c80c81d100c0700d61801c0c00d021500074450080c0380c441030820b910355401100250b001e00060044c4206a81480285101070701401d8021600b098248110260740d004205d0340d4002a031049071020700e0140c194541600b41d11900364040c070942c2040c1001005030020074114400e01030000c142409841e0003099054000300940895030815000220780742c01300c50343c4c00500d43c3c00e004200c056841840003600541c1709410259200112400103110102002c03447c07881c01002c40c1c0707070709442e400002c108500c1540d02d1003030401c0d0390075541c0158007036840d0803000b030540c1841c1e003c0135042140c2c180107101032203c0c100b1316000805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 266739118 1250 266737868 266737873
    0x309080109031d1f140409021801110d020a02060706020f19090602060402010824130f0506030705010804030f11060a090308060d1509021c0303060e01081912050c 71
    0x3105494001c02001c2c00f2841081c866815a803550414100724440140800e40c2c1454007415010101e400d8450407a18019460705400c00c21000c120540c1c1d81c005000240000039030881c5050050b40050b0000c141d50b070180e03405034000481c60344141d40c0060054903050301a5080c0c1c3d61421981030100107031040013407202c0135078000101c1004442c11003903a0700d003c00c1c071a503800322400c0e280d02c8121707101c2c1f0041e80e01034001842803021a821081148801c1d441c998101600c02c0a601c00c2d0000c62010600035000c800302030380d11a1020043c00349409025030248086000c6c2c4003a60502c400a046448060006420480a00c1000004174040c84d0f0000041490000311030082c41c001c40c041c0003070045480c040740080e80c03000104e40b2900309594051a0154010400051500040c007120010901602d0982e40700c0325412100004014070181d214207140a9500400c4e0542014840300b440b0806900400d0b181e44580781e80449411801c035000404c2d64807110840500c07030051804c6a050050070140c81d003a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 266740368 1250 266739118 266739131
    0x303070b10030210020609030d2f130f0305070e0c12092a010f051804020d0501090b060307080a02030711060a0e0d0228030318060f0605101b03090801 66
    0x1024100c1c444003180e108840b0340321000c142e03042c200d0b10782d6815549011164001e00041040312115045144007001020104402ca09600c0142d6842c41ea2140300101c0140001405141e505228050b180504100320442d242e05142d1786c1c8259440c003680c424074082d40d4008c000f05440040200c115041032840c03078203400a0f81058038040303441c0c0364a064070151103c419507440f50b00b21043c801301156620305843c0c0203001d00e030f4a4000c0c0c2d441d5101843c070107500011402031002030b540d0340c03018114034918100d000640f076041c0035a000894032a9410380b441900140b0810400f05d41c040189075000340440c5000d03031a40c4888600780c4d0201140c201c49410342c0030344001c0100c1d401c1598840d03450a03410f80c0864501d00314070b682c1661070711001103801c00506054200c8a0245c25901c4406081502c24500000c1e0350a500d8984100b4011200e01207601030788410103418200c010f4020480a0030f82216142004021074402900c8007024415032403541e00c2c1040c11200703250048024600402c9074100a00c0382 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 266741618 1250 266740368 266740381
    0x30f0c0302030313142704080417010905010606140a030b0d0606030605060906010e030a020d17030c12060f0d110f120a410304080304090614010c050606010507020303070b 75
    0xc030f0340d50243d0941220b00e9030b60340c0d41700d2403c3d07295400010b100841500d030f40464245c0310802c11304010419035131070300f04000010725281013400c072a040c81c03d500000101c9007006d00e04a400d6402d194003000c01c00c044c00c04181e0340340314110b0403100c0c180c02c141000103840503c0300104039018038406003c3c180524201000003800826000356104103803c80d4081000e59a080040d900b6a8450f80100d4050f440f002302c031b07001420081e007100741c42801107540e0004524071400315901c5501c02c6039141c140c0791010441001c500e03d05119642c2241003129520307030760100240800c4a264030040c1c0501180c2040f440703100da40e12060101c0e12501000b81026405035a11111650740d01c408c500c0840d101c18811440381c07078613142a0910f1180d4a008151068842c8074282c122900d000712107034141d050700007004009000c82c001c00040000740b44035080403500c84d24005500342224000c82003141401001044800020f00102d0300b00c2e8031208c00d09245803a5601800401c1c034500411000070300401660b414800f5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 266742868 1250 266741618 266741647
    0xa050604031d0307060203190509030d020c0102070e06091b1e03011d0c070f17030f04060e1f0e030d021b06070c03090522051503011104050901030f0c03020303 70
    0x900c01c603101d6800c0d07244100b00d042c503690762000e2142d680103801c14000b214550380e4040000d01c0300c500504c1c1150400d4050000641440080f0b40e00e640964008080c140c11540c050008000a01100005c8400c07841e02901242c131901004200c0d8959240c00c0451301b2010190906541090792000c01010301c507080e410520159038428012000031720b44000804a40d940d07048400c0d88107005541582d403c100040d1386102400c0301d000000c403041c1d200e00d20300c190001d0030600503600c00d524980c08401182010305100d03086802d4080c6c1c4c480030390400c03600d00721080490741d0100c111401c600c100044441e000c081c458103501400e141d90000600025420381d0202842d02d0461440000509030dd080d5155000117a4805607020401004101c24280c00c200c83d24104074000d4042c4003c42c01400210f5043c0e4444003107d208980b08240010040c2e07000815040134403d61202003c003054144c541401c000006480c01014400100701c000100c400f10b00300f290340c00c2c02000079640503048a4417000c020200b0031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 266744118 1250 266742868 266742887
    0x10c06020c010e010f150b0c0a0210121d1f0216050705040b0a05010804080c010204120302010207030e0306010501091a040504020c070801140f0106030e0c0306100503060f0c12090a05060403 83
    0x850f0750f00b0080300070300e505014828a054456071103050380000303242194804058001800700c5146001380c80003e4054ac545080c441196010750341c1d00c5050078001d5000340d04a4800300040106c03e00c1c000c2115425050004400b20b101c142b084071807040d605405e603d81d02905c1044000040b0340500b900f05420071200089100698800712000d0002c00c1905041c09242450340c40fa150000f14a6804034000c13499082c0180b41465500001514264461701c40282086e0b22000803001030b0341c0061508241980035111080075141100985429450000002c18401c120700540c111403124945e011401042c01c01264000c2101030801e544400c09045056110041c62040c52160350905130404100e03103403881501d20424203201450000c2c1d0a0603011001460354991283c0540304004000c1107599003000407a1140c010040a018290706210034541040000303050000c02c2001e00d4140070311041c0f4039090301c01c091300c201e118207159a90401c43c0c528110042030060a03034002c030020701c0b06040d400700110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 266745368 1250 266744118 266744141
    0xe12010e0f0c03060a0b2b0203030a050912070e0a1a1201061502010b1e060909010306020307110f0a060903180b030106031a0a05040513081201380702010c06020c01 72
    0x30361303680da5501508015201554156940025011000c082c3c0c00f11a045000c0070b1054504d1406101e00640d012078619408061400046080403403040564a000c030b02d86501030100c0c2001e050f4607031800c840f001d50007a000c0c04410700340b510344407404104121848030f9064a440104240340d0b030403854800b507009080601800141160a25030700140500500500d06440400b603c0401384410342c0d0501a00c5009400b40b082d8070400400110030990340740c108550107507005030320060b9039003444070b000340c00c0503c541500c01e0700c2e40000e02031084480c00819030391005a00705001150045081c90100c03040580c0c960300040c44100c0200218112a5601c0a181a118240c5041060400c0904100f510b4110300240301e90000c03400e980cc0c86203003442d03000315401002d00b4180000326246560b810071617412400712000c06401200040000c0d00f4030310504e001c0004505603001070340c81c0b0501940b00f4040b0f0f00a074030800d40030000c1c0f0802103900c41d41c503131180c25401c24021910361741c82e08240c82c042c3c026034451 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 266746618 1250 266745368 266745373
    0x130c0b09010f020a0b0105010807030b0607121101090314090f030307200a03020907030f020405030a05030c0d0c08070605071209050a0309081606030b0a08030c07090e030a0e12010e0f0c03 82
    0x40c40c02d400028610411500080041c01680c038001c011100c031079006040b0f6042540340c2801280980714940079104040c032400b80307200200c8107060002c0080c8404010300f002d076810b188403a804240c00c401c0900c900011019000d50361401c560111700d080e0945c90010741c05100008043c400c0c4041c44048031144400302480b4100740d0041c80403c04188101c3c04003039406035040300030401c0c1c2406640560003640030b5500c054206555180044d0420041d081c05484941001230460a440810f0080c2139485a42e42811010003500b5101c0500d64060a04003d041e580e03200f022641030b502445420000e1010401c05102401d03944c07801ca91503451a46084010568488002c03c450a01049000031680023b4030080e204d460b03d401240588800303c0444d400100481022804046c14001043d00b01e100310000c01002d442c2ca0072030310403100c0c42e07001d140075074000f40100100310707500c00000711141c20116101a200052006042d00502902a4091551050062600b900340010500d256094421800e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 266747868 1250 266746618 266746637
    0x411031306050604060b0f1806041d0604021e070305040e161e1d060706020703030209011e021b040e011b170402090105011b0507080309040b010c02090f130c0b0901 72
    0x500042c0c818070300031b901d8181018000207190404050180c21250f20040310502c1c0301040c1800f141082d4025045485484030007020f0004840702449100c0e080311044c1d40440c9002680f60500c89078005a200c0800b03119070010308030003403500c601c042c1e5014100c1b4001c02d00c05403e0020380e07040c2da520000d20010100340100c1c80e100300203102140c0e4445104540d25196000d00a8950134050f0012208500740c0c0b2000600c080c40c017041940c805410050f01c00d0310016940c04050380050554040604140c4284c0681d445400f00b00750701241d42c04014100d815414404454140001d01901020341820150341c44c0c91038010103061599100302e9040c10f5034071200074051034243d228010440c100c4010b90004810801003185500c0740101b013202c10007040c024207641025a442c28203144595014001c25800880e81d661113280c1403099899610007400e2000c022001d076808103644d00002440900c404400c0380014442d440d2001000c610558000650036103a500c0700040110381c1c200b00c0e000390000c1d440d0031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 266749118 1250 266747868 266747881
    0x6110c0708160504090f021201020403050307050705040b09090307060c14070312050105060408060f040503070b040302010b09010b030f060103050702100f0501030b06090606070807030302090904030e03010e1b010e041103130605 99
    0x40317003180c001d41101c5800c0c040e92498007800100c0000c0c0c5030f0518607641c2044000f000c1074062000d800d031144507401a00c40189090300f04403d4075840c00e2344511a041c200c09205010b031000044682c4564017110100d540791180c441070b540c0301200180303415003041c0041d510303003007503803040e014001c01c400c0150030000380e40ca032006c1c44154001c900801100341d001c440411045100035505681c020b1081d41201c0c0b518810355245011144c0646044000d030b0344070881c003513031841d1034074046001d0818036802c07600354584448029080e200103171299040c1552003000c5003440380309220100025403048000c0c041c5944074552036005103404d102c1680e1a0705c80303101243d031074a440c161003805000020000c03420b114064503484104c1d440f0039030840916900b0404038020b52250f90f951480b840c0641c5425044482e14410b1500b0b4a444d102d0b410340035003086070740700c0c907012170b0f034482c50183c60081c41c0006e00403c4030001700d0020005044801c1792a5000300410540000007136040c80c40f0f620641c0c05100382e4882c00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 266750368 1250 266749118 266749121
    0x301091410060516230f01181e0201090e090f07140a0b1602031b041b0f0c06140907180c080a05040206090405010b030619030f06110c0708160504 64
    0x42c090500081d02c100845604038915044400025005641901c21008401401c40310f403070301007600726404d07001680d0200ca00b64003880f840200e00d44400d4001480403941c0d441d04506406220813500951507000d0354000e5920071030010000d40071002d102d4035281064541641d4400090701407180350710445001003120081030000d0440000060b281842040c20840100003981140072111310141d0951449409070358104101d00e4140c00c8048200c41c100101c4042c40299681d0781002410000ea0010100c05039a01c180100d030000e00e28034005941d245240b414178040c000c0c09540c0c81203440301005001c08202d01082480c1211800e60070300c0e40d035001154520381030343c000c0c403411404242c0b2240066030000b081d8105e1941b091000746401e107807034010800141102c3c1c003a000310491a0f804000c02a00781017480258410f103c0c41006181c00c1440d550b60785a6071021550300504880d1a00714044290000ca029070303010a10b001c06a03010a910303502029613802c0e06608444003181e8002c00003500e030809 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 266751618 1250 266750368 266750401
    0x5040b0a0e071503020c2103150f090f071103040906060e0108220c090906050f0a090f020d0602040e0c070606141e010203040801060f0e060108220507030803010914 72
    0x100d50420459004008058000750000712200445000d140f503140300b28000f0038480007c0741e460007140b0781c480c00d0462404800071400c0c20398a0184110b2003031134203150340c0d007441c087d40001e031412402c155170713200081200d503018244564401d620012402140184803070f04000c4c1640ea060380c40c01800065080119454001600c3ca1205400404c0e0388024200411854101e0113008010b40090385070740f260190304403440b610064507c5542c48050051000380d6020484d04a4a212800d00000c3d00644815100314104100288159840e040b0f0000b04401c580681d401003440791460101071030320901201d0790360304c0300900700e6a09103402d402164204c8016001015268041e10742c0000404007444030204e088486000c0d41540f1084c0000101303075809018038805000c92205082d90030b840e203403080709000000782c801410701c10b2007070270001036107900505c503070916106040342050f403071081c102141412601e4001a29007200080041081c0540e6048001c0031a007481150350195195521451117210 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 266752868 1250 266751618 266751629
    0x706020d0e120706180b010816060f0909180b070801060206090307110d02010c0501112a190f0209041202060a151205010609090f05060a0204050609060a030e0105040b0a0e07 76
    0x3028000d0f01e0102c0c441d030b808001c03c0c81c0b4096040c0c8407141e950b250110340c0c0d4000da2140600d640b1008009240b000020800c5004141500345034041200582d400741c07166126019040101d6a1a031200c4c000702c0ca0040715100007900100c2c5002c0500749220003c04401003400f80e0f10261080c9070110340c1e000400022660515044289111068130070300400118000226080c0d040000803200c15011440a10074240e2a40c04060940da5032080080d00007074281c0001e0704400040800c90b40c6640305000464000c1d14076020301c408942c098070900d05580c0c509802003000e500080100d0030041005a82030340142c542c2d001d0b4088850b16501c0c160b8050560304002c0030780f103001c855100104000b550071031140380120312070310002c80c4054885140c0000c540040009840044000161405119042c0b2807103410a24816040d8034040c140320101d60144510305205004803c00038451091034866841800191500d8009103d9801c003400e003511451415684200d05603d064258044000000740190880d10f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 266754118 1250 266752868 266752903
    0x903020610120314090907021609150905060607210908010e0705060c210a0807050a080112060e0613110607021f170108060f1023150706020d0e 63
    0x100b15503000c982c164074110700c0c035101101c10301024580d543c1e02000b0611510541d401881c03501683d081c0320243c0003840d400350900d6807411a10040601e4003a603080c0680716886408105500e81c070300490710500c18807001500d0200d240300c42d40b4054040d600ca65804e21215503a07000803a450380b0300c00d800c135000c0580c4107007503501c10f80c8100f0990501d100a050420107540540b0044880c4c00a500c43c00d00d0300c541044070510001030380d6000e164110580c01d81018651a020342000c5c0704410103014600180030b06203240c0ca0b1640290300700b0210b50082c949110702c0c00c0a952071030600800200490350711038800c58100c41000c000300380314181042a210603e03001448428140846800502c212440c560702c003013008000d90b541700d1095410302116000b05074a8004004903d859443d141c0461000f0b4000018801c40c048200001d1005507480700d01107a0082c680050640818005050032609191032080c1960202c0d48030140030266001c5c100044001c00302f03001e004480c050894803800d2002d6400e5486 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 266755368 1250 266754118 266754149
    0x608070b0a32040e010503160e130203012703140a0507140111070302060406060e070c12020c120d0e0303130e040501060b07060501090b030706021b0d0606090903020610 74
    0x9000360b058210600000c0d4404804001140384a80b0740c951154000c92000498000100001d080400c04a100c2642d80c00301c00d8541030070504100714102c8054201100e01104512020941d9401c4d4090791f4600f1034004400c4a4040e4aa40030003c4081484160040b07140c0311000c0328014000070071103151801581e00d081c80c01d2016960300341a501c0d001e0140d03480c2c2d981c0c0e841d95030a101042004200440c0650000e00091406142501c00e89142e500000da01040c46024400d115070803160b1030800341c1c2e014482e2000a50350303840403442c001c0c0c01e0343c2c0d2543c000e203e03580d071803819880840c400c00d80e80c0d44d41d03944800c03a00c10b04081c147d803449024100319113041e014a080126034400c6c1c49080d00301e4402c0c000803038a15581d84481125070403420050300c1040d96040104102c400034030a0012010065000e40542440c02d440a51034036903505c1c000301b5400743d00e8880c003426992600c0c4d68140b194007807010800e0a803140c803602c004002c080011005841500302144e0019483c80001080350246005400300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 266756618 1250 266755368 266755397
    0x30203090103020c12030a320412020a0512041e0e0a0b01020a06021c06051e010e010e0913060b22020f091c0201020d11100b010c05030d0608070b0a 65
    0x9601040c42e113a00c40c000c1c0048200180414001140128031102c004a4019000c5009203507945003091291496035140041d000c0c5200c601e03600302d03402034001080303080030301038035006034201070080d800108035004941803210300a00000c0035005480b8840114084c1769941c5480140c5c60045015014400440800207600107401e9001610740c0441071054414440791b903540c840507600440e500c03100c0c016221803c000c60440760721810001301412122010540421000c2c0980922440034850401100c1d040d0400c85901070625500d0718003000c1c120b90300d90f01c0d15804805600d07254060840c2d04ea400c100c018a400d15104001880304d0102d0f040340c42d500700702c0983d184020751124840001902060169442607034a2a448801c1a40c0582c60340d44141d036180300080c18140021071a03404d000051076071200d035060004039086031030005c5600040181e9140300685110b2a08000140588000035601e03403054015040141102c1e490011510010b460710b5021040f03000d18a54a0b00298034034040c0c4e4807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 266757868 1250 266756618 266756621
    0xa0c03020f0d050303070306080d0f0f08090304080712020406150207120c0f2405031b0c0c06030405030c06072303100504060603090525051201021909170a030203090103 74
    0x907076000091545086602d565915400e6400445000010a81d1818100100b1354148141048900f843c50300000484800d0300103005240441c0da00e00c00c000240c0002070b8504001c208072000341c00c02c1001c9034401a5540c0b030b20700743c1022803c0c0890049081450005009503c80f02e0000c0b90440c94001e4a001030601030703035116544441034152601c0350f00142c00540c0c000d0030344612000c1d00b86400c0a100442d10382201000f020803c1100c0780810404004103c0d00901031100d2810071004c1a000c590b9551712004081e02e00004000c41d26406030b000024001044000001040d00340b0880c800e88149a4600e80142c03000e0199040d140b41c0620b00c03907400709241340090300031507000c0e10418107802d10703d07200c00124040f80c1554210f0804240d03181d6288060220030403182c400c5d05a20702c643c54141c0c580b20110301480f4906c2c404d050240b410300d98840c010300000e4055666069a17500b00c12103046200c04010400030841c8114003d000101e19800310420010852207409505074001390b180c1000c4000460 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 266759118 1250 266757868 266757889
    0x6170d0809010b1f2007050f040608070f051905010e0d03020f100e0118020d0222020d060303030c020d021c05090d0515064e010504030305090a0c0302 66
    0x14440d540e20240000181d40301090201c00620401c0c3e05030301d0f1a10031102070100c000700c244986101503000395017020300307500060306401d0320380640b0f5000100fa070480c049005030140ea00441e00c0e03401240d001080960a490070034085840485421640c540c1c9843c003e14048a40c1c06024000f640b40012588641800340c1d0740c0910707030310074411501800000b2442a04001041242d0f00500b6147c02604da00d10b0030234000c82c0c01c0100c50b002d1701d150000d200da000516500705450024090084410200903000e6450446000700d114440155981c6941c00810030040c12070740404c40c0800d26004560746800d01c005101c1d01c1e810b1f1a078005040d54961072400c42e102400f4040e48600304541000b840d4042d071240c01d000f05069104000070030690f806500309103048040201620b005101340c105058131001d00c854000405000c00161003901c0401a0700102c0320b00c0c1d008180710500807041707204003055505622441c8218000d503030400154a17118065a150404d20002912681c1800e1003071026250500019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 266760368 1250 266759118 266759131
    0x6090312050708040510020a060e0c03030904090c05060408280308060d052e0c081e0601030204030602070506070f260603010b04050709140a06050415020f070f0906170d08 75
    0x50030140d17a08001800352030718040c40c00068214030820400c20069014002594600d4070240052204400c08139540740203a121491103152104000414405030080010190074040c00260b40c644d00c48041130380c3c60300c0444001a5030000d0010035005640c00702180c200315541940c803040745854582c1000840b580b8441c09807024001c55800180890060442100383c0080c00102c582d0640010a03d80440724044050030a010340130041000a000019140034019050010300d078480e120400100d000f03001d0750300002c040074800103440046c041c0010b00c40c0c0c41030b2a2942d60350a00b00254800310345062803201201813055100703250741c0429a83c5001158440c07000b0b000028540526000070b81540c000b079a02340302007071581e00280710100c240c3d61401040501940c01a0426107005070050040c8103a200f100840082d01240200d07051082c40b440820380e001c2c0088400840d103034184011846036600ca0b04c29014a0b060002892094045001aa2a4086002c0c0681078600ca60642d45010b004120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 266761618 1250 266760368 266760383
    0xe0c040f03021e0a0f050a08010b03060c0a0915110607020c1e010c02190305070608160c141f06090e06060d0f0803010b1e120628140a060903120507 65
    0x12100f03e44031071900c2c100078900c807074511158070318000500c480191a50010102d59040001c9840107480025003160083c1040c442156074490102044600d803250342c2251603442c03656540b00c17410652000d03000e0200c14034981981c00b41d4035041000e0b0f035a500544203468001400106803200004090004a15001c0c10705018001c8002980007540d1209050145d05225210210038401d1000800041c0003a1043cad0900030428140001c1c015040103010f4001d10800c44241c107044104040140c80d101c40384200411070710400c0340d1100d40d481c500c1000c0c8128898606d40b00c0006041907240c040c2d92117600380340025041c01d4407a041071008078001010143c5118030021603c4e00043d4115004500a0200002c0e0396101c1e640110b070b00d1449400701640103807412051050002050840c138500e81c11813000c60b49494401030490314030703001c00b1011440701501c22545000081014440d00365400461045441302c1040381c90b5142503e07800800d02010700001200c282d1040b0550140c00140b1090340100003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 266762868 1250 266761618 266761669
    0x80106210c03060b0412050106080a0b040f141605040b06210c0f04120b18100905120c010e0709020406050d02090f130b18130308150d0305040e0c040f0302 68
    0xb09071354168002e07400010a00f003880d240d1024860700f0311500c00903001d513030b018000c661480c1d25075403900740c001f41002e4a80d0000d8a030301000c0000843c400741032284004d0903541c0308a852201201688264401c4a0290307050500a1340036141c10000ca070111110301500d00025642c0e45400e1403811002004900c0c1c0d0700d8100324011713074007032948060300040484004208111140b0f14188401d25009031980b00803a42ca240716061001c0701003604a003031005240000740034a0300d41096842c0c642c1c154002042c45400007500d07112148107400c07007859900c000701150074540e5206050422482507200d00f80001320140181c95441510381c004010345c4100409000d50340c51407100103060449140c00101105945902039907103810303c803624413038203080d1442c40c1c40740c0c1c504218007403180d00c00300500408201c11603000444410503030031040211000600f0044564a0070720717014140c2d60003030284c2016041103800180395604200c2c00c0360180d42d504090f404905155509002401b480740d0841249400c0921 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 266764118 1250 266762868 266762879
    0x1802030619030c03050c0103110405060d060b1c05060916180509160305060103090c050103090819090602061f03030c03050705150709060305060d03050306031005090d080106210c0306 80
    0x40c14001c2c1d4050566011001e1562604a01e040c0622085a06140c200075110003000c131204192000c0345d20076514103a50703c041b00c0700703c001404550800125070314003043c080b40b0040440d070400300340e443c101e10406c140d8550f00c1c1001040c03d02154490003141070603450702520352040002e070000201c21300422291684030b90004505441c100c40b80c04640c0402c070340503060154140900d60700701070203013400c00c60950b00381c030703101028482c50284506054540c4000810484c00c4003c1b1484080c010a03e407400c20141e02d0004e2000780d05205940042c40b8070000305a0141070f25403032082c00403030b92600908007880d5550071740e1000c00c890750941c1403003018804032012803c1482181608042d903c1142c00c24507290402902c0310495410800825140c07000304003c940716034000803695505401d100b6200c1c1d4696001a10f040d1640d10042115818002440f000910000d000040303021691135030383c5183e88070f00d422604031002e221040e0a860001100ca200b40f040c59104d01c207280114600450f8013900da6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 266765368 1250 266764118 266764159
    0x251403030d09050109021c030c1b170606091807030605061302070f031b0507090515030f03030f1503030702010c0309050d0b01050301050c1e090406030b130209070918020306 76
    0x1c40e0251804d9440d10a08011490421652600c0302d0309031010300781e51141500c0007056030000c3c04000b04035114521504d40c2004008001c0b900408849500394a42403250b00c00c40c5e20f41405513400342c080c007410001700e81d0050322000d545c0481c0440c080181040c0d89983c80c0c05001c2e15004c1c0c619070b005441e1106442600e059400140040d60154480d0003160701c01d4540200a0000d142e2007405080007a0402c1c0002000461040221818020046003c3d01e483d00002101c0c0c0d0040b542c42e42c03501c039045a09200407000b102440c4a104101d84508956880c11019100e15107820941d5605130410001c0a00560040e10050803090103031914200c250780741c1d800720726814280c801c151003041004c0700401042c6401d02a2a41c06843d0a8086050090021103405c00800341d82c2e40c85031244000c41c240b10651500d43c020b01c001c1d504512502d00600340a20075000450040302c099009282090000d48480c5c007a161000407584a0000b00d0b07500546241340400940024001c9680881c418000c01081c2204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 266766618 1250 266765368 266765381
    0xc090b0408010209030d030b0109030f0c0f0314060a1b051309050c0d0b191514040e01050f1909270506070908010c050f0c010b0d050f251403030d 64
    0x81e00010780c0c1e0300c0d4160030949021814007249003050704009425005980c002c08000c21070b0303405160903490210300d00e080d84039400f60340c020240c00d0780c0c940000020701c400c00c201845615041c0c010340301291039032040781081d154280c84003030f40d8070311030880c040145115500415072030007a44006038046486900d8071003070304d4042d902c960b40b4080128024170300d58000e1142e080309038412035107040380c010400c9000944140c0c0380b08070b000d045600c504240909005654045040e031001c001959115162031a40107a00001c0c06001d00038841e04a48080d10b040c030307007110400140c11203a90b40c010362a205000015113044440b500c3e0301580030680040d81d05490030040350052045c000707055240350181005080f007589510103000b42c0c0c100444803e40c9030b0403808481d4201344035a40e0710350f05c201c1c85104a0150422440094002c44041c034580207009021030040e1005000c1003c1d5500129501c1c184440006049a20b040d0319000b05001c1103103846012000c802c00c28043d050742c0c100b40c0030844402c102c07641d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 266767868 1250 266766618 266766629
    0x2150a15030b09010b04021611060c030a08041106030403140a0e040501080709050f0f06010e04020403050f0a0c06031104050d03090b031905060904080703121b0c0507060201050603030d0c090b04 85
    0x600c9041c400203040c04e000d82c00070644183c030114280790720031000c038581c0040e41e04083c162715014100d01c040c0761a03100403601140c90340412a07a0310305040000400340201220103581400620f005044a8079083c001c803800390303030182c0c0c0d02c0e030300b2400c1e07032301801c50315404080761805201e032045125099441c0d81c040d15008050031005446464a0204c0800645400500f082102e180704401c12940c00c0c409a0002c2d0440300c20710700308012192403008a40280700d00e80001e0841c0c030407110754001c90ba2000620041039446014064903155072500190140d4100b855281c00081d802d000a00c402d00b05107401e085040d010746082c20f410b03580c40004025580c400e540b01d0308202c0880c80c070701243d41550302485030081410345a92003189056103c003207990003200d0004041000030ec05269040406402c01d0641003150303140700b1051400311b040078090000c05602203803180a020400030315103006209183c46031001034043d600d001c034a071000400070149a26164248624141c2c081103c2d03000c5800b038806440f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 266769118 1250 266767868 266767883
    0x9040c08090c01050406050d0b0d020d0807200307030f0512030709060306060c0201050318161d010f0f0302060f0d18150603080d0209010e040f0221010602150a1503 72
    0x1801150741e820010398685081c1400000c0204001d82544141111b0540c41e8a210001d0b01c0c04440002074048040030801950040e5110300110a000030400200103503885044840c4410443c210b1100170101081da950b50700d50049002000811658030342243c10900c40c8003516100c1c1042c01114038036800940d0020009107180100b40700407a050b04c2018040c2c0310034200040c1d02040e5500090052100604114465500942c031442d501c60400c00c50840e02000b10044c02c919440e224005000420b04482d42c200322140c80001800402d00300d0301c141951484007105c1501c0d400d507003e008c0664072100c50035401e9401080303040182002c5110382c51034000366000340025220ba5050103400ca20034240100c010500d451010000030b03103804220359102c10310301c40160302d0b00312220040c3d40600c8c02031007c0c3d400c60701f40504028406e1a5900508629107065220f0791010038050344202130040c01d015400143e0701c00443d451f442044041e4040e409200140046079104050f03501d00e035400e01d55031040342d101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 266770368 1250 266769118 266769121
    0x1d040203040b011503020c030f0c0a0c03030f0e040204260f06131703070804170421050f0a03020d0c0c12200d030e04020c03090a0803030603060f040b04120509040c08 73
    0x203c13548240c28a0300e000d1746015400c1603084500607499114008901803040000610355400b2601441303080303080c541101622406c590b481c140036005ca1049c140400c005404140c45030902d280500c00c4c2d8068451030342103400c0c108a181e9103c08003012159080c00300707105500283c000309400300001c5104401051000022400304d00e803050914092804081e001c003014803c105e5200d80c40494070350300a4200d20310304000406400d00d0340d101e1049400900b40c5c0c103e00c0c18401c2c0d08207106000c40c00310358030602c100d405d000c48608095440724001040100107030045801c1c0041940b10f030a1026035640505015514540c0e0b07522010b5018510460880740b507411000200142103114a01d03064040064400d189622850395000301152201c1d00c03400c3c45107030b011a001100170010000d9a080020184c27a400c1200e0722000001d513680c10071540c1d40d100380304500018140a004d140484d018a501950301400e40d101c135652010047c1c1c05111681c03c0080034060000169554082c6a032021419100ca5209 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 266771618 1250 266770368 266770379
    0x121b050c100804050c090414010c32030411150406032301050a05040914061906090902010e060915030c072a0b0f040f0906150315061d040203040b01 65
    0x201103103081a100740301d0000c00f0040852008030350400d415004481c0c040c05503584c1c0c41c110303015010f00c50900301d0703640c80c20103020325403a0000400c104030040498400801402104050250350781d40c0b5821a184006102103400a011441040c441c00c02c02054403a09250500c0c140744950402d900900000c0e8a80350b4810301c0100c406070f0040304a1000d040c103200303076041c04081000c440e5248201c90007255101c5289091100c8024030340d4409801f001580d0041c106880000f60500781d90b081c80c0b00721803500b90300144881c00c42c403805400e075506844a07021140f00342c04110540d0841401c0036000034006000028010a81e0000d5200301100f940a90b00c0300740340d00740071031024803000c0301c41c09101136101b03c0807070021550000011181c400410b90b554075445041e180690059034040030784240300c4800800c1406031904500f06031103180d00302e01090750542600303d081d00e03880030f0302030801c1250300310a002e190310801041e00c4004000e40b05801e514007240105e41240c2c02110140c03049403080c00144038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 266772868 1250 266771618 266771629
    0x30b04050f250e1f11010621030e090103061a0307030203030f03090a080c03030f060102010c0c0201180b13170f03191e0e0f10020703121b050c 63
    0x10022003481c420309181ca04040900044402881c0228140300707201d84040100388a240c44011020014105090084451400d2110b45600d102c0c0240441d0108003c848241014441c2c40304031800303000b604140a5103540d9003090204440d1060f810058100e0034080340d40c64000c0080c1c001d51003460000b48441d2003134004003100e590115581d210f03411030181000540e40c0002910a800040d074806940c0342c468685440c030b05800210024070b000b602080700e0030021408000340d8400d5010851440443d502c42c2c004900703c8000e00c5c0808041000c041e402000340d44181a03c0c989403168582e10304419888100c0c0c401c0a4120503401980c1c3d00d01c6007014030004200001c0310700241c0502e001000ea0080b0811a652280603450880410b44400514866000d20405075401c0c04500554106810910984024444243c0c0e0100302c1c05032406000c0c030740f601e040c1540b8000e00c1c260140d001d0035000c1d066640700c10a00100444001c200036440b0f80324044103103450b0901f61200d125800400300c10b1103040c1800b2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 266774118 1250 266772868 266772871
    0x906020c0a05010203071b0503060408090307061106040308041106040b09030106090203070c0b07020102090d050c030606151209013e0f040303031d03030702010b0a0f060f0804050109060507030b0405 87
    0x14001c0c0340000e020080740e600041a01d404075441081e82c05182d4912240781911a02c940c0401e51520841c1c040c842480003a50051040304800ea05907010180c4510003941c25985918021265502140000e008070b403168070402d42140c4030b14004066030403c0c4002642980181d04510140302000800103094542481120014079120105505614200c078014001c00d600140c007811a01c0424000742071640300394112001040000c0c48600c40c01c01604040c0e0b07850510403c0503019200c5c01300030400514000c02100051440c05200300e00e41440640c1c80f009142c8082e080d010107648070000d1114ac40e251018074002e0328001c2c00141e26062101608102e51854280580001d5800704800c2c14968050801c5505494240c1000f0940003805540e050001d082150024076901001c410300011603819004404071450444100715210345441d103001002000c2c1c412840401c0300c00d8a00494217029046c1c0c0c0f94414080c0000080783d5030701d0b803104400d42d10100c0c2c8050000e80d81e43d140361060720f824030403107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 266775368 1250 266774118 266774143
    0x70905010f0e040f03140a0905030f0f0c0d02041b11060705041802070f200a14091f09090804181a1c0c09020307030c020f300a090602 59
    0x50144601d803242ea919125000380001e0000310400951340b040c540076100c07a0120703459881c00b90740c0d03500010710000e010100501403940309004003103061105c641c00107201b8004002c0718024080724101d00081010549004170102d8000f070f11002401c60804640c0c890103070a401c280c580c1d00700c0c0564215043c0c10840020040401e20070300344802d1010750018450510010449400140d90f20758904010302e424404940c001d01811031040529040000610040300e4424141d0f807031a16a0b496480318007104a1801c92031350000100400105400c409080a191941510b500341c90700c286c07585440420340314807040c15246600006070812002e4010311b0b04c002803001c40d00d4100122103440f030b420b0f900c18402030500340c480d990804801d440c40c90b510701c0b6014015402282400b000c0c2e619412280070390400c840d0800828030300104802c6440c004140707072a88400740d401410380450b221008002d00c14040c1c01420101e45003400c0c004810034541c4c010204542b0984440042d2440c2ca40024503246000342030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 266776618 1250 266775368 266775389
    0x5060306010e06010540140f0402030a06052115070f11072616030b0712020d1406030d020f0706030f0f021603110606090403051b01060807090501 64
    0x41000c6602d144402d03400c4182464140c0c3e544512240c903450300c100013a0310a41c0881a001c445901c1207510614900715003010b0521904903544000d8103401e10242090300c0c0c0c10981c03480c10210185003e070700455000280240005800b0345a00104035900f04000da4404004105017642d008100f04211040500e040710840ca0035520701007030000c241800c140344050030301011034546003440400b4031101d030103031800d81420f214030001d0940380c041c00340c0030b0012080e03103001d4080011001c6880040e040142c0390040e105544980700d486e01122401061071200d22110b60900452207243c116001743e0080f07501d800c003800070504040d41058201040e07c8402402c2d0752000700081c8907042d011400b102210414140000d0400140d10082c002d0720105042500701807001841c9040348500c2c5c010340003103502903520746050015081e003076540c44109590480d4060481c400050001e0f116030000c020b141c900700c080004111808940c542540c1e4950411907058001174414001104203100c0c0c2801041d91880 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 266777868 1250 266776618 266776621
    0x20c0f15040b06031f1815020417030c190c03061802010206060d1e020a12061407020d1403060d0b01090c020c180f0c0c19060c02031812120304050a0605060306 70
    0x1500c205000c90680c0f001c02c192035130f14011b044040c0310b4280f00c1141d008100b501000c03d2801110000b0347c01030040c00c01c150090b80c80c4a0003441c0020076540d1644169001b41440c00900b500d8035180030105004680c1101c107084d01100203050b03800f0311060840380c903440309400280d5200290030003c0c0100564040c0882e14002c070081010390304260700c440400706800d82c01503100d0011500300c0d541ca8001d006090000c080210412920780d210401180038911303081d9070f5880d440000c0780c644e480425440001642d01e102903c0e0350b0030030402185c00810080c0340c5e0701640300c2c81e40c82c00c8910074240d002808080e0344003c1c0c05031094040c485903203055130845003074032400503010300c00000c048003034881c0900651110008100f0190f901c203d038010481082203a8100951407910070328104d00d00f408641c401e0030a4078002d65240004181c40d403c200e00124031110544040901800c5a0502c824278014071404e0030706420754134072400540c0183e0048001d070241c00600e0410702e043e40d20190006001340d00500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 266779118 1250 266777868 266777893
    0x50f03011515020a0206180a0506030c04090f0e0114070201110c2a120f0d0903110915060703031d030a0503130503270301061710020c0f15040b0603 65
    0xd03101e0003551000140034429514982c8101e02c3c081d2040d07002500004000f03450354000c58a12411000c200088031021191034444d03003405100d010580350451035420510080c080c616107a00500b035140d4985c1c0c1c000032046441c0c0c52722425282141886104044030034184686c00d0760a006401c180f45000251a01d4122144180c17550b80d0a4020b03003881403c44010b4064081022100c443e0800d000104054182d408825916440c1c8000d15070b20034042c400d80c1e1084490501880d0080203d0f504034400441d00f40c40d0000340000c09000038040500841c000d00900c0541da00c0b840030700809402540c0001d54004040c4030780c3c111041402c3c0c0c0758500d0b0701c10310100c1041c030360101c102c03644007038550740c0b0030841003061401d18a14011200c0000440000002456008045001c2d00c0c0740640220000d01c44d082c2d94020600103000d142500e00e1132504100306c07414803217200360000c0500c03007050000c0700c0a00304400780740344c100b84128480101c0388007800140b20910480161458000c14100d0141c0342191259 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 266780368 1250 266779118 266779151
    0x110f03041104020f0406030504150203090313061d10020a15060f050a0b030619180209040513030f0e19060f0f09120204090f1202010203091603110118080106030c050f0301 75
    0xa1140384101f60322440000c040203094146844c00c102072130000d5482e8103181c0702e49500c94215514400e02200031040c002a07062107440015250311000000c5010500d80c24244540c0c0b107a4011140d00f03501c00d510404001928108483d15074850031b4900154940c10103401a42c550996400a4850800010f0501a101600007201d812001c2103600a1411040745040701c4295415801059000a8518184041040b940050403010340850781001156122a08000c0ca0700722030602a0000e49110b0300810528050480100c0300c2d4001000d04404510441500300f020348a60411000078900c0148200c0c1182c00030452000c4010394101420306500304401500c1c0036480313417400f03032055481d405001c041c002414003c4401540024103c0c0c2e00315504280a4085d500c02e507051515482810314200901c04001312000959920000c0103070344403440c00044030184218200c10406a14214000900340003d200703400c015813151518107802d602d006c08008100380410002e034083e904240c4140707404810b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 266781618 1250 266780368 266780377
    0x30d2a020622031704060906031a040b031608010e07080a1208061c060b010806061c090606080a030c05070e07020303181c030506120a12030c03110f03041104020f 71
    0x14651040c829458401e40b0b51507010056201500d50020308400581ca00d1000c0000c10544516440c2d0440d103c0da10704045084610040096500d40424961580c4500d803079001134100901c000c0445030340d641d01402da200c807003207030798044051a9901d080c542d180580500546001703100300b10181820311081c1d16503a812242c00240d0400b00070458000418560714685d8050071450b286580aa22140d5454410002d00364207081c83e010480d004001429854854101c8043c03076500000e52070710f040031b030b58114040c18020340111440c513101c04d07021070700403c100061080d9900990b144071404c04542402e038248031664000b4107400c2d040380704100140d600042140d400442c1c07444011004072017414964140004c4001c00c4842c0e0056884070011700390305820490060b0b0341180c429000105065a841d9200300c0100c009100a14140f441c0031040d01a0740910b6010700181004a04d8850140d4a580c941d400800c60900520303020003404107101104155111744a401e6800318940b400b8800d2400c4940074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 266782868 1250 266781618 266781637
    0xe010906030b0315010e06030610050d080306040605030d050d0c090501080601081806010f170606030628020307050c15061c1109010306060512061005040f0209030d2a0206 75
    0x4441d10010a02e86042007003030714130481d14001c20307940c1d6110b0410042180c41500c04901c01e12078900401c00d480300c002c60f54022148010480700d088600c0341da542000703800003050310b640180c5d680c00014181c2c905100851849005a40d202c0c0d4a501c00b00901003100e5000c034402080024000381880180d0704004000e40003402401c0c441100e030303070318000c0c0c800034080740448801a02807000001049412411a102500d03c1c2c8002c4058241500c4105507407641c084801c960b255100340045100300403004111140200c3c0301c060030440000340c0178660b0580c2d0081d0752540c001503000840c44008941444440c48422941310121054240800002c5911021042400303c40781c100302e08908110243c15132108084018024084642c0d40381405001031000c0d205843c040c0144a03100c05c0c2101d00030074107511403d84041c003030042034106414040100b0400400700b280503401c04c03060400fa5010000540c203400740d60303101d0f03081c40040600014016070388111a0104e05404a421005984d04000d41d200782c403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 266784118 1250 266782868 266782871
    0x170a0609051f0518010e070b0a050415051806070c050907030f06080f0f07180903030905100603061d19051f0911010e0f0108040c1d010807060e01090603 67
    0x31060510302d00701400c8003400c0d54107088100e042e03161100346420642c468001c0e400380b02038441013409107a0907199030b046005040c0d0040b0030180140d24031480070301154032031858100d05081c1c841040304425164120760001040c001b24129080e40b0850200b030421000541d209810005917035210650780e1014064a40301d80343c1000059251803195101e030258040400061100e1659050455181d00c0840303082082c41c01042c0130700044d5180001c42d00b0880e140b150310410115202c1030800b000b80014030084081640318034030800441c1081100d00400c10480d000011007034070f035181800451340c01505005188038184400079071260302007050515002c0d280c00400c108061450028101214140700b6150000b4105c070382003807282158000400d0030700c50110001d0b91008840155460b180c0d4131507141e03000c00c1055100c030712540300d000700c682c1042c8541c021301d502c0e54540395204c0e640604407451480c0a030201c00100008041001900014000c90400c20600d00100000800741c0c04131b40a50010706 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 266785368 1250 266784118 266784131
    0x406051e0a050a1b3c0e03010b0418030e03150f180f0a021504030b0c070c0509010b16060e0303071205130206030c0703090b070606030302010e0c2d0a1707170a06 71
    0x6050846451145000c01c5c00400699040c1e9840a0059102090900c1c065841c208403802541090b10030154680000c051045408550340c1c1c0445504540032569a010f00820150342045150a59002d0140381d10034822111490201615228541d400a041ea80781d07000e41000c004c50440070440140c81c54054403900e0782840320b44c0c2000c803140300d59400200030b02c40013810001004031040142098500c21868071050903943c0c8100080c2040c20f000d03019a91000300002d28600f49003002c0020410301c80c07607020035020034184010307056406c110b44880c003140d000104940750304000c0c804e20b94000440c514031480550076801042321404018610400040e000448006040c090900c3e4801041030740c02045d990410b83c501000901000d1004030055070801c01c1412940d070020540c410b0614020700300000003441c0c144014a1801900680c502c03007102d0403c1800c1d5900d03240343d144080c007040c0c0c401691100020605501d04881ca5114a42c03405031510a4003089802184a00d03071a034200c040440c05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 266786618 1250 266785368 266785427
    0x110d1418031c05130b070201171f150906031b0509010908121e031302060a1b05012705070612060e1603050a11030406051e0a050a1b 58
    0x2000002e00b2020a02d000300345486259590203802003c0045442c001c0041039907940052040ca0b029607030000b40443c031440458010090000d05241d4458480c0c2d0f0080c400064010b6404841c40c0103412510518041c45415081e440c0c00001c0d2034001d1110b03190401110300c01e000c20108240c5800c1d40201048000510340c03406a20a000c0180130b46251400d881241d0028070505885c2e5001444d42000340540e26012040500440180d038480c00b400c840c021150b00c100e5003045110b0f8040c001d51018030525003082c0d00e181c0d0181031151005445000000351442401084055980745500c090245c406d07102e1a81c0005400854020f040b81c51600b0400d10300f490108a500103841c854110189884244e010070800d40c07030b2400700a044c04507548003041180c980c040c0703060039161001c17046450000c040004c1400507209a204940c48108150400e100a005000b40ea03090a01601c84814403a07c03041030160b070200d14803400c00c3d0400c0d0001400e035190414800070700010124104da00304001030803141c111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 266787868 1250 266786618 266786623
    0x70e041202011d24130b09010f091112010c0912060612081e1e0702060903030a0c031416060b031c0306080c060304050604020d051c110d141803 63
    0x40c40220031001c1d24020321000c440f5511300c10001c070304501d482c406001e55044256021000d0195420420b10b030041d20560319400b04500c0d0151213208203650340c102140c0c00d200d06100f00580707144207040e000d10302c66114041206420351821100fa03035900d040c03c1221083d4124040350121a2640c2c140c1c41909142d0810000074005680880500d4450803a03180420503050020150203448210030790f00780c80e021400003424040d1a41d08400c95042c1d15030700d0b80b1815420060300d9003910007400f00703180c6403043c80840c0c01c1d5080340710503101040c4110014010960884489447da000000501d810b15a04401420000848000c0504541c0c1e03aa425001c40c1c3d02c0030301818012401e0314001c20031114100400800400d5180324008250080545c1c0b12a2490310343c084034040c603003040040c075041d103c42d0204101c5003054141154284a451959040c401c440c008030080d6030130b143c0300c07650070710860019582084a0b20001c0000c1040020700360300c0702c241d0041a1142500c2c40b120300f1040c0d0440c0c901191 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 266789118 1250 266787868 266787881
    0x100801050d030c0b0403050703120506011407141615030b100c0501200307030f090c051c140d0305071701150c0b090304060216030f030804030504050904060c020609070e04120201 78
    0x41c041e850113010001415000b00041c040b96110b5078074030504a400c1c4a45100b2148184e0344140002d44243c1e04102840c2c0c050301820719140160313101800c0301e088682c458900040102030342154496141e04122240000c500f140e002c00031030500f440280c0b10000041c1c1041e884424500030b00c01c00c1d509640600c0400d5000030b034946120300000e4644090100c02151b16001292000f0010341441107208440c02140aa016201d40c0205808074142c200800c00c101d9044011540c000d821609410b1030100e100350b07442e000c5000802c00074007140e05c40c005004042e1800204240c0a10030a62211450f13002020411411100440c500c94101c0c1c00503001180d56014802d8068144401603091104001010000b08101c0d0754603000c580c82141085d40303130402211a4031003d010301141c688004003213402800059031062103454854903103901c501c0003403121801078038141e681076940c00004114a40400c401c94103e107907000208503444c83d0020078005894001c03c003c28800e00324036001ca0180c000d40088 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 266790368 1250 266789118 266789123
    0x406021203150d06141518091906020403020f04060b071104020c0a3906050d020f0406050c1e0307030e1206041a100b0313020a0801050c07030806100801050d030c 71
    0x10070122264206030014001c51100c0c90007041174840800e044400c3c40442c4002098060310451100c0090080051800b00042c0405038500854105102008902e040350920743e11032440162131350b0942c010b00c42202261010240110726011091003120315820035105420b81c0302040840410602000c40c000e406215074a154a22400049404201803000710f42e032402c2c00724044000280c4102800d100245001100e00d508a083c0101070269074403480081c805041e1101000d45088a0141034800da80e019901c0100024404030b1f034070100c41014002d2108a200c046030050700d03a041013020548070712400c40300a080c01090056664140c40d148015a44031083c1400c0c1d0b40c0a1509040082940d6001f18105401106001c00186204040c0c1080c900351060918400e0840c0ea880503403000f000300e03070101640d2211194000090b841403d008480c0302c1d07512440c00907120304172442c000e4503060010f030400d40705d04103115824021940c414190f07811104104c038513201c40209402c0c1a00c8040c07414101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 266791618 1250 266790368 266790379
    0x3090a090b0a030b10180b0603041e020a0e07031a0f011d1801060207081b0103051519060f0c02030a0b04030c0b0103030206070e1c0b0702160e07090b040602120315 72
    0x400c1040e17442070381c81e075007150200c201c20a500043d0b00f04030700480e980e102c03660340e001c0000e0001c80c02040300259900d009451044a002d401c82d000d40001d218400254000c141c2444403074100140d80354140200c031800c0003035108814108882c4800101c1e10400d0a00c0c01f4100700d005004440e008a100c40d951650060141420440d83c900070381c0440341510074015000035204220000603800c00000b4800c0078249034801d4001d00c1e40c0300c68011000740030050321030400120b1a4035599620358403610070b51020f001e90614000804d20b011805451143c0200b286c1c02880f08408030b200158074040ba406038019804450100e055855241c2070b545c2100d03140c0701801c6250407038004410550009000b90050078103844058124240c90100302c200506034011841456071b5909400002e0101c000342600003005005840da99000b940c0380301d2072144941c1c030001c2c541945006204440381c000350000c01500300011102c0c542801c04074040c1da69582030380d4030a0303284070020000383e0101c1c1d4809094070b0081c00510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 266792868 1250 266791618 266791621
    0x20606013011090f090408030f1b031005040b060408060a0c03090519060f29120115140102010c0203031b070213051509160c050a050607091703090a090b0a030b 70
    0x4007020140c02c040f20b010302800101d0302c54065440c00c1d020103881141c2c4500c11a2541c1e482c81450350b8a010007a105600c47c50303944041295074407440b4040d5106070b52401b20411403910b00300c208401d6504840005002d100104014400071102068981e4040c1e5031a8010844008111f01103009040c0c8800140c8940104514803240c401c0e00c020020030103000d00014840c445c0d20250b00340441e4200d103810600a448030003180901c1200d14400b00c9201c100904000f140034800e44501c0c259040301c100c40312035140d42201484030740300c14140d41d0b0242030284001c002208100e08060341e80e01c8050700c104801003500d000300030700e40051000c13604070395405442d4031030280300e03a50f6480c0545820380701b05515003400950600241840c00c07525124101a156001c078140d0303800004d90308114a50390644050043d4076410001c140b041190b107018a41c903545d505000ea180124602ca007035018015203080350010807500c07010381e0300c148a80065070001c200004264041e01c0000e020003850354001801d0702540320 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 266794118 1250 266792868 266792891
    0x3160c050a020607031808012723010b03100b010c030c0c0b07151a130c03021209031b0a120516060c030506100804080f030603070b04080c0a060206060130 68
    0x941803c401403242d55006403068847c0315060076182d0364a120054030144002d000010207481c4215201c1c40d018050348a2100300300d0303415807400c0610389488502c030380d1120700030051400d042291401c00d007100f00c8200504690040002e0001003c414083d04128002240b5020b000141010200402c81d15449513550066890160f00c1044100c4244080b189040e41d01d44040540c00d40c8030040010092240301a464645600d00050040d0100b007420035900b40210101d1483c0c003002d05004020308001184c44070041c01004c0e0780b9a80c20b003418611030b04140d01781c000040046182c10100c074130a04200d0740300c1e40c54014488003211780358405800103080503070240010b81c15134030190050700f017501d43c1189000b07412070640350010140d0300205141c40030054030100c0040d00000e190480401025240002e0307881801030f01c2d82d041900003068980004420301c01c0e6141419a0340020900c6e0300140c5810310701580080d055058000041c104038440070180010300c0850741c2210404980301030304020000c0d285 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 266795368 1250 266794118 266794127
    0x105070f08010509100b0c07030501090503130b13090c0e1306051c030815010201111206011704020d020f040b10121a090103080c03090a030f050705040203160c050a02060703 76
    0x40402000301d08188000308035810150341d4584101c8641d50342c044090300d0116043c07459400488900aa802517410200007d1800e0113440581c90245c4001d64079041001d0700400800c0480d48801c14040d410807007000900c200581c81c50071190540c00008003d92061001e403000540030a0140d8099204c8040e81c0071039940368401d03401d0391020f85005580d41d445a04035441c43c41030b00c00240c0030031074001c001511a6940e003030b600071400341840007003019400071100c41c5c45900080302e0b0750000b110b00b000f00b100790b503070040030003841d442d551911100905142d0040f8406400300d0401901580030300100040c56141c40d001419400c2010f8210821f143c0000ba009188131b02400c0100b90036402c149554030380025651011b5580300b40200030480f180d01e0f607541d45d540795008050002c000d0000340b02c180300300d42d914000e4800940c01032442e0f66000007640303045420711085d0b4001e4bc2c8910320500900090110001c0c400c0003a901c607003880e501141c1d903806d00506e0306e0740b0032100a41c0002c00062402c20144d20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 266796618 1250 266795368 266795387
    0x506040207290705090d0b130209040812070203040513051305120a0e03010e06061201140c04060e0306070e0f060d09081b0a05032a0609011b03110904110408010507 72
    0x50a001031030b1a1030f151000c0f1954842c20110542c05480c904000011032040302256401c411480200d0841c1d1603d940807401040b0220b038140d80c2c20f90003081a0010203001081981d02c4030403440950b04d01070424000514204110400024907581c800001c1c00103a1034021000c10250000201c0300b0040c004005041181d018620b81400035038482e0ba0002d01d420705000b191680071418000d0f00b00765481200b803008000a18942060341d641f1020540d42c00e2000c0440c82d4002d02255421350303511030134030700301510505840b40c0c614006c5d48490108a07081d6441140c0402c121011503030b001904921000040b6140122a08440d001e45045c03450020050f440000f00650f560440a941e2690450034440d910741059400140044d0001c020800402c81c690450030100300340710325084100c0504900d15880c103801180c6070b02240e950703403445940980010315048462521881c050050724401a07180c445801001021030180347c031804825120b1107070100790350240c8030303841c0208a40e2820440041040e0030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 266797868 1250 266796618 266796683
    0x100b010e15040504050c0706020c060106090e10050118030203010e060a1805030306010513090c0f080901020412060e0f06040c0302090601090509070e1504290a020703060506040207 79
    0x142400e103005038181a0640e10030441445a00c0b400d1616050501010f06070060411204860800140000034581e101030310304405064002c00c680d41c10164080c101d05215009200305640640c20403508160f5000d5040035501c1c00c1c41d06414101c082c2c0034984041d496030300001c1d495400c02e07000420b40e40c8000ba41c28400c84d6000380610410b01131220401400003010005011a0402c00c005415540158028650000d400100403030465a4160f0a401c40e00e00748032400008400116862140b40d00c280d2642d00681000021031400703140030382c100314000210740002c01641e02c400c03003200c1011050014500035140319003a504030385803500c0c1c2040c8010550004910862001012400f5940304448840954502403c034a00a403903100c020307211110000120b40d800041060000344010380f5402510042c200003030740480300003000084016000f041c00001d01244014400310001540c00034a0700110b035045070f00000d06484a10206019108180018000c4008092024140912441500f040e02c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 266799118 1250 266797868 266797877
    0x20c151806090a030f030c060f02120609090a0f08071e03031a060711040908041508090d0c02010c03110613060b030106030206041a09030a030207030b0f04030c1112100b01 75
    0x3680c082040194010100e0280e00600c0003076003400040c424603841c022860290414040c209065500c240580d1a08801b001c140c903000701d411440340d412280c00383c2c0c004c3d1088460459a203481140e030350b641c0042c84400344c40300d8000d02445061082c0c542c2111121a00106055482008101241c5c4044400902240013a00d004018038560f0035500c10030b4403000380100064030740480d07500d8151201d1600c00c00c06611075590180d0f1000103003844014402090381107114040900d2001000d040c0d4440142201c1054022204034060507520a50128050f6424200318146c100c4500301224201c00d0002c404210384140c1007800340c41280d400800c05824407415043c03040403810810b00d426110b6a100081d0409014042071007180420f440c00e01810402000083c2020700f06000689001400501500942c101000030300c284084401c00c15840680d20344216014180b0f558000d1110201110161101050703140d0a149a5201c0c40401e1000c3c604204640001c40150311640c01420000801400315 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 266800368 1250 266799118 266799157
    0x806070305011401050706020910020606010909090b040f1a090a0b0108010c141b0a06051b04030327081f0b01030e0a060209010c0f06060f051c12020c15 67
    0x840c82805024140e610380400e04001016000040d240c64001c880120349840d028040b050786900d400700e2502003a190303a8014606800c0140024080c48402e800c801c010031b0074a602040801e980c200c4003034015500c521507600b0032203503040805401c4080c003004150f9040e08401c4c0030983c00c0c0061070030202c41c05203001c1e200603607036211818202c401c01800840070621101000140039080006001340c145a40c2d10301244004c10240c9500b062026201252070302c3c0d844080c40060181c0c03030310b04040c2500c90525145400c0c00c5881c0a1300e00022100c8000c1c600c650003029850720200700f038041d0010041d42c81104c604a455541c1803030400c40b10b203c0c0406580c03510348506020361080c0520951404120090501e83d0b19a460b50b02c01703544504000340c180204072a6030000120188003031000d42c5d000386400038880b420082d001118040e154049841401c00ca2444d060800d190300c001c50126501c8200c0b038855030007081d0164209000310b114954020700407496521403400e02001003030401d00071640001071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 266801618 1250 266800368 266800381
    0x50415030204052b02010e03030c1006081009080f0d0b040c050c210a030908130b0703141c05091002030c070c24140d020f0a0e090415021e070605010806 67
    0x1e03181c403500003070044c0b08001c0800c80594007502d11041074101c080c007540c1c0b0340512461914544081c4210405100741c0c1d50000304262a82403180c03120000304154180000c008984400c0c0c4540205040c0011036000014008075802440d40210301d207c074007070010320180001603009842c9800a801d800018011030001400007190640012010b819000d210b03820100c055030100e00500104000700c801450401c403498216002e0041d25008008800f034069503040d5502d0300604801800c0c0401260460034000c079030b280a08030f1a21245891030b008002aa60380b0301c942c41d4030349107202080f83c041c0c0784000148500446c0410060050900428584070072644d00c011044008203905284000b00d000c1e82d52401c0030078850803e03d0280852403100e503007020801e45800049910510502c02d81d9040045c110300c186403c000c1c29108940205d800845502c0c0c191100c0a480d255815480b0003d0750000301110480340b0745610180945044501644a00c0c841c50010300900080c05002c00c24440c00e40054075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 266802868 1250 266801618 266801659
    0x120f1306050c032208030a0905010207051501171902041a0d0308060307140d081308100c08010501030e070b03061903050a03021203070c030c15020a090509090c0a0b070305041503020405 81
    0x413016030185907140b85039100720000004000311001103c0c607540821405010890401031030300e503054400c00080131540340c90134805403940900484d0805400c00f170010a0b0b021400940311100a0b015200030600100700e8030402040e055074100310b640305003506460303414076512071440c52044070240c040760030160b1140b04803003801b0100d00c01550b22124103e01e170f20014420f40301406514007104510800103031540111800d140c859146038900c1c41e03840e2002c480442c0e01c4004240142400c0c241000000c034880c0d003481d220700b050702a075009510004041541512605c5603120149400e0300140d121640740c0c40e215484044520003680144141071165000c10306e00c0c0101d03409410691a076040c501000c0c8c4e019682c0c03858540781520903565400100c501840c150000f0b240341c1d10f582ea40e09010504040411503c0c0801400305d20032a4814a2035400544954001500350780d240e0381c00e580c41d91070301d2508543e944140e81205016904500803002402d03051f8003d84280c1e10304136032649118070705001410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 266804118 1250 266802868 266802931
    0x9050406210c0312020105060306060a0803030402090405070b0703020f070b0310030b1302060c0a031107080304140406030f08070c0509060f040c020a0501060609050f0303120f1306050c03 82
    0x100e04092009500d8195500042500000c61041d9410180b0596a0b00c0700b41d8046102d6440a002d81d458004004a03443c2c1400820ba1004040711580d66580c148122161740e8000140000d015250200101e03080c0182004108000d1000001441e41e4044500e0002d480300068a84610389201c0c0040101c0d0715000d40069078171800a0100f4200341c86c0c41c50f21614103100003d0409405d100e42106c1180140e00c9140082104a1103100200801c0c04681f60083c02101c070b21080720320f10380084100344607540007c82180e003122001004031076071606400000e0020308003680700070510114a03488504011030180a040381a002d00008136400380c0e540c0c14402065001c48807030394050401d203044007891600f03501010041c10240304481e070701c81c1956502f608582c15504000b010a011030410000c0d071030060040000b8000c26000b03141462840000700e400c440c400f4000003580d0101c000050400007180010014058100409100a007421403081c0080e41c0240c0340104040e685205040b0840306500c11392 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 266805368 1250 266804118 266804129
    0x42a050405010b181306050409080309150f2706010806090f030301060e120c0406080f0d0203181c060908090411090d080d061e09050601020f070b1c0e010c09050406 72
    0x18a1320760b000080010014050700c0d8000c1c440e55690f0b0204503511544105803d6512072000340da07803420180720051800e401b04444a01070081081002003240705030b181d2542010200d1400c29802c54505000d100840c2c1d120039030605c905c9101c000080490300010320a00814643c01516904a41d2210640e107a210074001e038004950b031005440c040d0705100390100b0940100b1030aa0300078180300350018080d40c1c016071121380f5543c803020f4806d504000c140401c90907a92940010b5280174120410801450314548406205c0c00d1004524449089150102c1d5020303688030718100170309543c0e440c11005a8101d084210f0040786400303180e020b061356035401c584e0a044024880b44010510359268809688420912010143c4450000a40424007c845030710384070b40c103e1002d6401d0800603444100d0300c00400c0c440c11984400350305504d0309000b060203010386480103003a6940e00c5956608501c140781500000f80002c1c07415416400400041d4003100340c002090390348004d1103688004000546a071030065 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 266806618 1250 266805368 266805397
    0xb10030302030708030c16051e07180b03150703050403020c060307020a0b0601120c050c060c040e191508010c17071407021207030b010303030608030304031403042a050405010b 77
    0xb003001083c03203980907551180007081d080703182007806501141c500440c0d144c00c503230591011007407010b1590110310300030810580350000c00c602c81c0780c010b0b500c01d408140000459107a54030b200c449210348061086071400c0b0a018958461410300b510b0042c000d040846055006004080c01207026161203000c80c1d0103a01c180d4010003807502c1719110003c030307401d001e0111410704c800c030b01651444612a0245206e0385041d901c80c9a00c1346000030500d03003001300040804206e018104010301c410000b91f4271040d04602e600100e000c1c0d451041544100622011500032601c1e400b5120005080c9415007041030303101d08550f107240003000e420301c01840c441c00c191810000328005508582d03680094002401c0400d00091566802012500c4d44078101900c036002918043c060500500500d03401d030044a00a1124100851552820383c45c000c1507010304640c56411341200201040900107030480d1040618160700c100304842200c90007210004105120f04c5010705e0601c00000350084141c0c01f44c03031071005074621 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 266807868 1250 266806618 266806627
    0x40908120403171e220b0a0911030106050102030a080a060504021201030213050609070e010c1a100b090109060e010329010f02030c0604080a0c170403060f1509110403140a0b1003030203 81
    0x2078500303180c9001e174440c1c180e001c07080ca000049a000b041c07132405003401c600000384e0341d6480d040004c01030075500300e540c0c0207a04199081100da40e0020480d20816104d1410103c680c40fa0f8403a0000380c4500d5101581c010300110380e000c041c0740e0643d007032030482c1d108071009443c9100808486068400c212600c590062030b00001542c02c50261003400001001454048904141e0f569420304000f4086c80b904003d21610007000012100340001e44007500e0100303413080c240b02d90003000070701811080c040c101c1040f082100c400c500d139009810050208850300140340d44d14150048000c403070991421424005035003a4154104940040115144c021140015210559a03900d4048481c2d01c4011070004111405c0b8441c808124940c01080c20241e000741e100b50b4403440d5040c0780080c0c421340c01d10f840d2401e02d040c044072200804402c1c4d200031509070403c04907103010481d43d030300e10030300a030b9202a12a1100c00c0c81400304100100c0c07540c031614499103800c80765232110490740007406818000100942e00810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 266809118 1250 266807868 266807881
    0x10c0c03020915030307060207050c011803060f0b10020a0b0601210917030a2018120f030a02010f110c060411030304030c080303180c010e040908120403171e 69
    0x209071540003c8030484001c1c01640c1d180442e2450303106510176035a0310750116040c42006000c0c07081260004091808503100c1c0b03c07414201e0101d481521008007150b0b40c4009102508400da0001028680001c101240455200380080e4441f507502c00129009483e00001030181c1d80999a0b4803801e40c0504027205c0c840c08400070401c000d054200c0d00790f48500d000051544000d170f58000641c410741e141900410011955a082e480204550394031091402090001413000a004084181241c40445086000c2d05000c0031241c200785168a00100c103010004880c03c4042d01500708a0721540314400c100400381c10b6084000981c0102c8896455582041c40450007141c2d184500d07059243c401800d0700e15181d900ea80c1e0840794034059000c6d0905400c0801000203411105004101000030103024150b007029550009140c4d0b0751042200f442141d0710302059007449245001c0e0780404a011101074941c0c200380c1000350004003054040d1046000701ca001414501c0c0009840e072380214008000403940e03d500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 266810368 1250 266809118 266809129
    0xd0203041d0a140c0c0609010b0108130c030501020423040209060307300e010b0d03020606010c080d020a020f0d0207080c09040203030702040504150b0f06030106141303061406010c0c0302 82
    0xa0081c60b002ca0702c50b001c4202c20306426003401d0007259007940c80b580e10784002072038605211005141c0c100a91401d20344000a0340c0255207164420603030160081003080c0383c40c0ca03c03803003c081d030406400c41d80302040201c1c58503548030900c4255218191550401450b540420040e0b00c43c811815410680c2800880c5500f4000d0f2000c1540c0d03080303a440d8440f01105c04101c08283c1c0c180042d0b081a0b1500d580c0d00600c004000c0c800d000b0407207000da5085000200588001e075172240082c110a04001c00c8001c10401d100c1c410094230510207002d20203543e258200c00000359201d40640e618440c50141ca06031904007400020300600301c0b40e44401421107109140d04000c0742400c0100b050341c150000f041030320010303503a505c2241e10491094000e05928484402ea480440d020341061900400341000c03d203001d6074422096904640c4180b41c403100b9407151200e105450b001b800070880c00903244460100c200242078000d03d00e84030001e070002d40959150801115400c5080902a1034400309990520143c00d02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 266811618 1250 266810368 266810371
    0xc0d051b0303160b04060f1506050307110106081b0109061202033d0f060e060a09081b0108160518041b170130020409150203090d0203041d 61
    0x241500c2c00d100400700c0303402020f600c071601181d606602204010400c4421f00c01c80f010f42c2461070041050b84031702c0388800c50502c400d000b107206101e008000078010f20b00c90171103441410b00f9400288080c1d0707921003145a881c01e400c2c1d500c55402c107401903072420315485046914110360035a40d8809440b08146501c40095102130500701d02e851130318107100000c00c0141c04401c030032500980100e0b1b02030081c001603c80d2034026001042403c413848030401580794050405589420101c83d41951090500d8080e1070040701507201c84843d01600324110410b00d500c6403003001e010800c0c0c0302e00304e4076501c2000310b01c41c02c000980114003060307060040c80395a8084051b02c46140102400028804013240d010305070102c903400b0240700140b0160440884030036865015801400030207200034040045d81407030295100500c9a001006201c45080070a40da81d0743c01110403140c00c02580d8116104140c140400b03507000b180d10903031a100c0c00c04039100b0107100004960403140041200c08001541147c8580564030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266812868 1250 266811618 266811673
    0x9031204051c0e06090108190603030c0317060d0b0a0e0303150103062103210f0504110d02060f0f04090e0309100203040f030b0402240c0c0d05 63
    0x10500240210061415045016500a000814500c2100c03004005801c2c0c5140840301040b908a40043caa601d600c0300740d8801e1002400e111029640b405d01c14450b806001d882c4444080c24608000300b49500680501500c42c0a82c1c0c413000798000095420045000945803540c2200b00c60103400c001c90482022140c1083e50400045010584241110302e50b4009a5040f0407030006030400865543c2c0520905d40106250f01c2182c0883c103882c0c801400e0805201e1018040c06141d101c0705454401c0a6a410010702c12190300b08445020081040001c02040320110385400d00380b01040c1310703483c1c17485c80b002e0b840d94000c140614128440d40481c1e8160003a410b580e1001790701380000f1424250ba4082e5000c450300d003a00847c6c03181030100030014080c169100074025500104020311181038003451b80000e4a07048240300819460f1440410182ea44201401081c00203044080900081240041c0301403200841120340429a007000c1144021303450400500e581d02034050000180000c2800040b00c09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 266814118 1250 266812868 266812873
    0x111207020d1202010b0307170709021b0303040b04150515010302090604030609080a0807110303070c0309090f09120e031c0201060305100504051501140409020a0b0408030910110604060509 82
    0x507180c0d0301e003000500c00205110250b51100d00020b41c0781070030800040106180c00e07280010802104885c0d4507042c7c14081c1800310b0303400007480705040c00c83c10107030840303982c2440440303175071345044e04001c401c0d928140d030100c034810341d50944445211098003482c0d00a098905405c000c0000440041d03001398007658605030000001d00000020480d50302c140801540a02d5070701d551081c032105c0040103804010110f00910400c08031501d1926000002c0d264080c0c00740c00c001c52003a10034201924011450341c0300c0c0303610754204010741c4629881b030382001c191148520030100f0741741d180e01e5058642400103980e464260380184040302c3c004d05007102c1a2869402c40c000010a0394480d140c160404c40064032004d01c2c25202c0c0705020802004000c0c1000070300030440403451950400303404c1c1c5e50a012002c140d03842103446403172100c150b6036028030070001846030b4041c299545540381070742a140d8011001c4688181e8210b581d08000600480103107158002800107400306640301d030356401c01040c01034245103091 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 266815368 1250 266814118 266814139
    0x7051c091a041502030a02070308030a090b0a020a0905010306051003020318060c1c0902010c0821010f14040203060105030f0403020a0f0308092b1b0206161211120702 73
    0x10030400c20040201c03024001e0542c0e01ca081c10007980b06101140d04580031075000b0010040d0703c130350204030001640d51042d8866030f41e03200c8501880140251040c0903014052042c14041c00a149138003d0007840721680b00c0029041e510001901202d40070721a0030340201140d5100c0e8410307131180e401942c1c096543c1c2510155048449103140c50320600316a845e07030007200011403a0603480c001c500c901450a2440d07003800894010346c0001c0040500c0e00d4000d003414804100070a40304040b009483c010064249074880382d42e501d0044403041400307032141955501002e42d440c0070070300705402101d120b4101078661510b1512003020f9903c0f000e000501c00e0301140141140000010200700c43e440600d0b010341e80d110044e083c2840032a0800080050690b0a001e400c00c440284d07652481d601d860031b4406007450780c000030032048a880c10740035500000b17500520000340711811b080683d0034143c03001e008010344030f00c044071004207607204c409200c10422640d11010b42900728203000001001154405070146410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 266816618 1250 266815368 266815379
    0x1060c05030d0e03121612051314100e162616050406050f0d11030718020a0311071a06060d050a06080105060607260423011407051c09 59
    0x481d040c0c03d040000c03c1e000040c01900b0a0410540980c214650504080701003c601d400680b09000000388618a6230700c0300c00040601580d0300b143c4841c00d4000d174885400181d0207200315110030005d9410106a0b00e002c6071640807910004108410019140710300c00d9260401c085108126103024010307031070340c0c802d80014504080034410f0510190048000021881c1800d08002c02d594540e0000c81c000c4502d9205441c0d665a15001e41185d5a0800e00701038043c2280c1011a00b032030002d400a00c240385804101055404483d03008060000c03040d5010010031604400c080030610400d1800383c24245c4021a1a0036614500c05c0703503804c902c00503c1c45107004004a40c10301030b550225068180c10790341c0d81c0c041100c000d082c007405511442c102d82241c40c107a1a81e840c07228140d60301c011600b048800c10720171554490120101d401900440e40b1030319030035501505c0c0c41c51844900c0d12050015603002802d42d66a4500e0055400080d0b01c0805005030342000402c045020901844103c01c0010000b40080d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 266817868 1250 266816618 266816621
    0x92c0c0a17160909030306050d0b0420030109051c0306050102070e071b12030b0307062f1f060b040e041113021b0c0906030c0904081c060501081e01060c05030d 70
    0xc00c0900004204d50a09080c0981100c030309902c014051610300c2410070005038011550340c0d226900003241c1d090307807030111081e503001c20110418640541c030300681c0c44140007002411f01001c0c42c078400810b0800805000c00c0302a10a60300c00c907409640440014040d0303d2100e000c0c0e9a00207031700d180039104001d494905030501c0141c8101602c080d078201040501d403550501030401c4060040d002400c0d8a0b00e0a070b802400c0e0410704180d030078070902502c50301d4a481c07407245501110302507030700c12684c03407079001e00c1841a10941c0400c0003600c1c5140144c00611010500305540840b003590390b14001603550340e15180c0843d0700c41e2801540c82110a0b10003016001c292004c0c000700000d41542841c801010100c13203144c000e00710f48840c4104101c00800100d42d178001810205014282d41007289501e035440d0032400390145884080c1c04443c032294041c0c9000e150b80c00b60b030032070300700742e0b00d484080e142d00f03070000003464050b007608400345450001404101e0084010303d141c680304a08603468069034900500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 266819118 1250 266817868 266817913
    0x1709030703080a021006060f0c0f060f061809110603090a0b04121404031709010203130902091008040b010302040b18010e0105030601050105161b092c0c0a17 69
    0x3203140d0004079201c40340c1c0b5410005c21a03981c2c03072044104041030804601400d6055084607030b8041100541e400e070100304040303200d1031070b01760310140522031001c1441c80380d03011b01803900991041c90090404008002d40034090103a00d0380d04400f03008171062003d020300a80341d100030000302040c400c00001d1000614041101c52183d40144003c00390440e0740780d001840000086000f4412102c180400e20200c2d018881800d1113410113090709070398500150040c3d045004d526180c1915180003000003501c40e080790001c0901000440f400c031400c8600100913a04000f00366000751181e44010014030040c102a0700424014100400d4500c0d003a0707044030485c000c5030090700444071040b19140100b109041c10054140034180c2424142d003800b0300e8a1071f07050800486c4001400c0c078410710324032202e2500c842c0c0c0702c480030b0060800280704005188070603405030040c0ca26164007064041c560041388107804200c042021800900c4c00c00f17100d10f804892080c046ca51201d903060b9002c0d0401c0b01285519491101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 266820368 1250 266819118 266819123
    0xc04030f12030e010614120c120c030607030c0c0f0501060506131a070503070305090d02060f090a0509011412010e01021b0c10210f02040b070606050a0509041709030703 74
    0x1c84401202800a0640c0e0414a0b00d01040c0e04006060104103440c04156001c11300945680402840480140b49440354201d4110780004240994060002d80403c281c400c0260a604030b48154441100403012105140c29410010702e85444900020315609402c11030107014030008122a51034200048890b8004c1c004c481e148080c032203041008001c00010384100c0002c1005803810a1501c1e11156140d1154100003010014001660f4070a0360b1400c0e0a00302154028080f2030b00e405a40e40c1c1c052290f884a4001c0344200380d885030000d0b5074a072144000c0e05880e01ca5401c80803480314503091202c5680300c84502c0c08155265500040c6001007440517103132410304818220302450580002500704520822801d001d42e50004013850b101b60041030744904801b00c403002d0b155801c5d0008541004290300e01d81e64080500010700025441e2400003e4900e40c0d020f064100070300717a50350082141e003244038403540760042d42c80c100060120300004135203004508148001450080305800103828101150002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 266821618 1250 266820368 266820383
    0xe25030b0a0605090909010203040b0610021f2405030318010507020d05010209131104051018080309030d03091119080304030602210906061309150218060415080c04030f 74
    0x1c150302880c001740e40681108080000310724504241e101e8459101000b011039014401c00c60b8000030451007081021100d2140c21a200c1c03a800c11800c5590261072594801110307804541e4400d15a00318020658044910080c01103140c100010b48005a2424140441d4140982440301c2e80141e22041c0c0002c0d03095101c2c2c1d00050f5110300c800100f2055840508800c10784178544072030160004c41500448086d40c504940c110010a84581d045401e5210000f0404240240e03090010322040c5c000b020703003400c0000f1815900300e1103c1c0c2800720111881c1610240501d11080c407112460306091120300c050340b803003d81144410341c07030f01c11403481d60f441540201d4800d5400200040d1980c0d401b08041d8984140300b8450362142409220300342c0c3e03440c001d80500d1040d140c1100801944134140c0c0451155030b80082d00405610b20108104000c1d044541003100c18169100c450500d440d1403030844043d11040005402ea4030035403001118003290040801d20307854020040403010030114403440c20030300c0c400c000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 266822868 1250 266821618 266821627
    0x180b030a060e01050f0f150a1706040209071b08031f06050a030b040209130e011e1d010e0d030c050f070f1110020d030902030304090501030b040501060e25030b0a0605 73
    0x100b03a400c480c00144a80856140001030100100c0411982038000e0525030a00d014050304000145c030a10a65112a81842d00b0704003402d6040303004121144114002c86403401d107952030040030f41e11220b02411809060010358841000540c410002d5a04188074081c01111104003440340950314039650445804918041580282036a0501524030010800e450135030403c02003102060b500c0c2015001e0105103601c554580507c55007d5100025403c98041400c0100030302c1303c280c0c0000d01608000f1030b8807003012a601e18500a05006009611054200826500aa2241c120028075642c0d40c0398040080030490800140c46840c06400d0a50160400d4542c1544529006040c0760314078401f42d02441440c0080405117401017426121881e0b00e09000c00c04000c1c0748000303811803285400c000400d92811002006001509a0180c0700d2131040d8000c00449d0b4442401c091451012651a81f050441042005000c240c02403500c00e1003805003008100c0c0388055001070b0050f00070b5040000000d20115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 266824118 1250 266822868 266822891
    0x209090304030c090b0f04050402150f0403031101020f04060810050d060b030c1914012006010e0f09070501210501170c010503040c050904051f0207060c0206060109180b030a06 77
    0x1032500001d2130441420024000340d40040303421359114803480e6200b240c0d5500050199201c106403018450000b51880790b6502e820001000c0e1a00b1900082c1c0c00585050140c904881c814801c690030350304002082c90070589003110488081400400700e40403202c07449000180754071148241d44100380f14050100d00144d4404c240361900410b506d1480c400c240c41082178000d40044ca00b0202a03d5010022a0300721080d070005880304099411051074140d5010000c844c003502c041015416503100c0744088505886085404600c400c040e40c25003100e41140ea001c0040d076026039165480c0c030b80b00c2c2c00038841c21403480800c04112217090340000700b41014000d81c407413003c000b4401e4220071402400c00c1800c608154540c004580300a00031107019131401008601804070801008101d03826000740c0b500074102110401019400080003140d000e07080001c0070007014004141d0f41d11070401079640e00b06052514800f490703042c107101098651107540318150b0082d52000c2c440c0c602e80601505002c40d0780d40004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 266825368 1250 266824118 266824133
    0xd0507170703172704090507080c0a0b03010e0f070c0503030a1a1005180f06040308040626070305191109090903090d060e1f090b070519030e0a020909030403 69
    0xa03000c05441020049148102c2a5405138603100c0c0003021311001d4142c040700420006c00c154440944144a22600003c1140c1c0000d09001804402d82d0002540d40d9200d15030890782c0020301491084158000005054510005103640e00200031b1401e007444040c5610b60758115401030303454016284e200e00020950000b030a0b4041c80b5168191511803032000c5220340144640074581051945408102002d062a41da00c0c00741d001e52100104442d07a540d65900c1c00b2509648140b01e10400b185210070360a10740d103010500c910a880d0000c4241e6103580c0d034240d0440003841c1c0104011454210050500c2418040d0301c140305140c400b0300034441d40d5080301001c05c00d01050080004549a0041202200e0354031049042122203a010401058803841c6008090418401c0d6a0414801c13001d8170076281149000c0d08981241400f0b000190700c1034032012012955407042012582800d20b001140d40d410390b1007684100512115403054580f080c03416030010340ea0400c1a03841c035002e580041000e00922510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 266826618 1250 266825368 266825393
    0x9020403050f0f0c030c04051b0a051803070f05100309061104051206011a280306170a0302070b090402090901090c020d11070501121404140d08040804050d0507170703 73
    0x3d00203040c10500c07000003c1c0d80e41517121016000c0d0340c0b2400400c11001601422005071790f001c44540380c642a40304801056a0401d075080285640b24202b0700030141000b00300c1c4001e4a465000d400b058070300303003024031021004110702c44040541d01d078102d40106249100c0c035840d41040c618082d87d128036203170421510b00c00d41d200341c0107103801200041001d503011502c10202d426058000644501440ca41ea116100300d04040708a240144050200c150340e0584c8060300f65008254400c8980194444541e5910600d56006000d42e000813818040100c070700000e4100b540e40100050f29103058000800c20a94003030f4045420107445180c2e10002c42e4060000810707444235454030030b01d01070310303010310a5903080d5a110380e41c107210000401380c000d8142c54001055400d070004800445017482d04d82015030201d2189403035803030300074132805881c4ca604c110700382d42c065a00180418109400c20042180039100544112120f2085a00004040d1103251a160030b0001150103841064514245084007484 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 266827868 1250 266826618 266826643
    0x90b13050c0406140708040815090105040c0e130602070c17120301060e010302070203190311070803030a0216020d03080108070b0307120b0a0528090c090308070c09020403050f 77
    0x1004204035651100c1d03002d64040303c0c4a8582003410350b01c2152281614400c0c804081d1030000001000f10340c0e4400002c1c144840f1041204600d12a40e0305044d044c00ca95060318010002a807600c010091840140d03195604402a2500d0201100940d51050b00326400041c04880c0c1c3d0000200c20040180000550307650100b06d88058091000d446040b08014881401000c05002c9141c030560310591090303040ea0006540a8122100f200303d040c4d80740f4400d02c403010200d0006016045030380005001050840403622203000841c2036480d42c01c001c1e8060740100325004040c1c0d6a1041050250351854403c80b1540d02a0315403080b1b950418042d2818000b950f08210b0300004208140501e00d9070114800c040c10842c13000000c0c901f40403000050800307140303501c0590b101d112201a0407171403150b2540601120980c4000b0100596140c118505035010a0381c68004100700040c01c1006c208034000808549101d4401d055480780c94140c100c08a8000b90410340d4568020800f028415008010201e1443c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 266829118 1250 266827868 266827871
    0x5040815100501030b090a18080c1c092105100c2114040321050a02091f1e050418060503010c1409190801110903070609120303020c16090b13 62
    0x4803000080fa510786d00240c52602d0320b42e95815028019007684406544865102a03850b6489000c0d00c1c0c0d0341d41e90341c0c603a180e030000968030340d0114403611f02603408041180c50350348401c450002d81601c0c0d040325003241c440c26190780c003d014003c112400e81703104090030083c00b070710380d101038082c8001c104074003a8000712845070f080e203852055415000c2e1418002c1d4096494a0488243c02c403132800160f0030082c2e28402c0410508010920224020940252001c100e0681c0c40e68a0b440800e04880c0160400b8101c1d6004611403074800c01c0b40800ca00000d003c410407030f080c01d80c03a29a03122001ca9906e00c4120342d081120b44d07240028041c9203000e0049200d0b4250078588071015142c24108500c1c98822441c3c400e2080d10090000c80c1c03403080008401c401002444000c004400d88405003000583c848030560303109002d150000b050050003220400f007a140038500d0704e40b01d0300d02503400360001c1d405900021800e02c103e020656101c7d00b001c841d000903010040d0003003800d005842c117000203801900751114215 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 266830368 1250 266829118 266829131
    0x20a0314310303020909040b1e060d060903051b1e0c011e0908010914010b060a050304020402032212020f030915070206040e090307210815010504081510050103 70
    0x80c041056180c22284511807803010030703030079440c0c2a070080c420464004c2d000004401044140800d14000c03512603d1172415008010382c40082804038000100c48040d80440c5240200300400c1c410b41c0550419882424031a01c0c04484508500c90b20005111810150b48041c941d020384980e02c842a0f5440f0507141d00504c0710714000000604400d42d0340300c207000c42006002c940482d05200b420703028000c1214a000300082e0200d410860710031039124141c46141e40c01c003100500142030100c1168071a00843e500c9a003141c403140d00304006540050000000c0182004080302c00c401d00139440604184201603106e035240e0ba005021381040b040d00f4242c0e006400900210905031034682c5500c0e8440074030b101690b5601e0b80e610000303066002b10b8100d041010800e904011610074000000c1092030300852740204148200081401d60100c10410200054041c8001c26a4246200103030720400c401410054202070300d8013085c0d450429207682c003064030501801440343c00080d04440102400080c0b80c2445803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 266831618 1250 266830368 266830411
    0x323071203090f020f190801091103030408070902070f02060f030f01140f041512051e1b04020325090e1b310e06041d06011512020a0314 60
    0x4000b10f214080e0080c90030480c070014036522041c0f1540071221205580c00c050f500e940b07081d4024150903000325038038800b01404a009203000020355040f20800401010304908115417a4081c0d00109800c43d9082034040c4c044005a0354070014110355442400c0c116264a0315070007820100707070107a210b00551400010042d1094903030025071070400c0000c1e5804076008148a18603c2c40c41040d5100b00f468410f0344402e0401c00c240450304d800300188400203130b011380c000240425202ca0b65105415404000f00007a203c2c0c80c03c1c13070340255500ca85d1046041e000001003a040c2134614080030840c0000440c600c00501c51040611052604811002049521030a0324a100d0b00325101d0441040410351203441881c00e2052078103502e40d04903200c910444850fa46d00d80e0440651141952418030450401140070300300302d80c006110706440c800c0390040526034600081404010400e10b02801000001042040400303041e00085c03040d55503981c2c001611a0405020680401d00075000c0d9144280f2403191922 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 266832868 1250 266831618 266831633
    0x6051c140a1112040c06020d09050f0f0f101e08010308090913050343020f0a0e010b0a090806042d020909011b03020a080c07032307120309 61
    0x244030100880004618858524840c503d009900440b08409900803c220420400f8903d200c05c40744035800702c2d0281540040151031180c20340c014503030402000c0081071a5480d0a48100c01036400250020810201c0400407961102803446440c0124200e00c0020098a41120246080107050310308003042c3e5045554084143c454088080e1040445101080710741c4091900410065801000c995440b00b5042c680c50305800100c82c00e91143c0140600d506900d00780c5a006c240c078140c250000904c1002c1c0350300b0001511700c0d808000d41c00210a000c0440c3d00160003c91030b020340303000088242c4510082030002c2c2142c0042c0c00a80b02e9801c03010a01002400d03881c1c802185440881181a82045841e185626aa40400e0113503000039590140706a0f4901035111100f08500c8030090b01417005441020f6069101d40c07585180003503141c90004024003c1e00333014010b0700d84a441d00c8410a1a01c2e00d1841c90405045200000d84000090300020000c81e10b0a04a9801070b41c2828003070509030f51030b0b804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 266834118 1250 266832868 266832871
    0x302010f0e0105030c07050c09040b07080f04030c02130605040c030b1e180c0f030a140c031303080a0e01060b0a0206130b0a0b010210050a0e1002130b18040606051c14 73
    0x45d2000e404100941081000c0c03141c804240f85c0078001007900d1805042020a5a1050300d000300410103003408102100d0313407500400d22880e0142c40e0003901d04815401e0001081b804100302e545a5a10b890201c5c16075079038010803580c250741c4c0d5408a0040d40c1041045020103500500080d50720b9640c0c0e01e00b01c55220340c5240f82c1402c41c01c08074410035550b200a0194141300d146070402d4144c4001081141c0c00ca8203500140580b1010f40c80d1520564401c0b0344201c45201c02d07034820100d50300c240c2448000a22410440358003619144011441c1c3c00e02104c1c450070365440c0d030018984450701040b44101c440e41048556440384014824000300c2455072986002c0d420b02407c5080a80c5d1111090600b40e402081515518081035900f080185801301100b0014400d02407040c11500a00c031030500c0680b420300940d0038414407000c0003000d00d0b00c2c1043c980016801002101084000440c003801d09681c2e61003010001d000f40d4442c141c0d2050031542d02840e103040201d20103505480c09140c1c0c92280480c4031900d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 266835368 1250 266834118 266834131
    0xf0e0f1606091214070b040e07020a050303060f0103090206040f060f020705060720090f01080c060c0304090b0a0b030c0d0e0109240207080c100b011707050d020408060a060302010f0e010503 83
    0x5006150140c1440c0104000540b04d2011621644000213081c107040002802290030614105080d9110b91354200e8a4150240001c1d0050380f0500100d1014038101e46020012001410006080c00c611360120385140c10583c00710600d864000313002c020050300b050500350750300c0c0c0e58400381803100e09000002d5983d000390240502402c20101c5001c0710403902d42083e04412200030075100040c03510300c108108102c0c00740501c4082c1e000d15540c9a08500748081610780c4210f10074048d60078903080c00340e810020b00c0c4d041406c56118000280000e009850040111b028550b9806510780c2c4030a000e1881099440d0983e0000140e0314001401004c205030205425031580780c4100e69918800b03108110010340540c80d0b01414902002410104030480000c107034845840c0c1d0a41440b00c0584140192400421000215020310151001071f0701e01e0f00c144003d000c0d6031100a401820203844402d19860502c0c2190441d401503078420043c015980c010858040081c103a20313080404401c00070000b8024000505103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 266836618 1250 266835368 266835389
    0x15030e28060b04020d060302011b0c05040e0109150209190e0a05090115080307050c2202071b060809060c13050915040509060a0510030f080d0f0e0f160609 68
    0xc58041020a8000325940b020041041d07403242031120301503000f0000717480101d0100b08a200020748652040c142c018485801c00300342e043d45840e00301030201a01703a904541405546e01c03c1032000084100c10258000d9521407401621003942c04103214040400702846000240350354420080d0041006a8660001c2115404130f002c0c0c48076094103016058941d82c403046c0b0040c92001040303d010000c00340100501840880d8242c0f000001031001081520b00c4251050604c91840501400260000d03c1c90b148182c0400112a02d0082091282e0000e9008134000500c04420301110210070001c5503040700c40d6004807407074a000441111500c059a06c6440c0c0541810070000e040030f00000d40b40040c41c000580240000c0ca031007070704540c441404840b0009074a1410000c103030411008610b0030192548480030510002c02910b9400d42904640740340d1107000c1c0c42d15010390302c510710f0b03000d10000482d039140181a4103120350300309401d040044003c010a40399880b802c02c4041d902081110448041801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 266837868 1250 266836618 266836693
    0x30909110f0a0e010e060c0a0b0105040504020319080403021e0103050a05070e010c11030601030b061e01020709020f19020325260706020c0604020a080a0302120306061315030e 77
    0x181c030031200e031001440c0c2c45030022032040c180c0c400208d95188005d10443c2c10a00aa8940f0208022146c00f0307100171b500342d44042918a01040c03520303076048030f89028940082c2170507035135800541110f50131403100c1c0c48682c619030b488081e560903014064228030745039030520042c540140018510188015040d04010408881d202400000d60100031945000347c00c2d03030030540e12400c103202100340544206014654040190b4041c2c0f40d0320b0002c0043c460164090700c5298034003115940603403c80a8140710503003040040d0140054888200b05030b10907a5005151101c1c407001d1040030406c00c154a030f204d00141f5056003400142c403002e50a0110704401702c61000c00101ca50502c0c00d0b400382c3c0b03100411103440022a0500104005015845107100720f03216044507850b000d80310340b90801c4c80320040141c1c0c04105d0304912414018045d580c0032070f000d88500e0030600c00a0540701c1c4810503600201c00c01d9026040d00b8091689030203100c0c200000400146048200c5000400000d03d408040403a50050500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 266839118 1250 266837868 266837897
    0x60603070e0f0f090f04020a0b04060203030c0d0608151515030402150c071d0c0f090f01030b03071d130308010e0405010b0d030807080709051003020c0703060603030909110f0a 77
    0x200024075090103082100d280c941885c1413061403000b0307902688500c240103000207030400c02008030ad007a00c165034061411a02c60810390506038022000b00700c3d10035112031010802ca5810400c14407500480224101c1e43c0c28221078091403141840f5082e4000d003a402107502000450404a0fa04281c0c191014001c1c0140e41c200082640242c0c81144628021501c001944c80c0f4150a0b2882c1074148003085203a50306c41287c0482c0f14865212a000e094805100454031468580441c88002c00306060124048104034002402c014640d080180c038100f001c0400074860341107580460b440401088140c8440c8526140540100014428034514010042c00a020080290403142d0300602c00382501110501ca03160103009418100c0d60440003421510000c1c130018070881031002222805000001c001c2180d080c110003039071041289000b1445400c17070000026841c0c1c45400700543c0603070340314a00341c0e04143c00c2a00b81c41003080080310303484040c00800400d0a400044954a04031820300b80d1201c0c4200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 266840368 1250 266839118 266839129
    0x3200322060504050603101703041a1801110703061b02100c020307081e0d050f0a1506110a080d060807060305010311040506040b09070e12120702010c2117060603070e0f 74
    0x1034104c0c2c224078801202e841d223100400800703082a103008025101076a068809a00e4030381c00b070700c0c1d9036200c2559400c0212560354050006002c00740ca051003541c44803500c0781c03941010380d0fa45403810002c81e0b0340016040c100f240e0612201c00078451710002400115140c0b10000e589019a90001e0042c14000816542e4011100c0c811103d4010384180c6589030440e0501e00002028101d03540303030b201d130b81041c001079805407648210740113643c4081c8420160307410318000302c5801e50510b8040c0560300c42c28203071030b011400301c001514822446001c003151107402d201080e400c000841e4000418541000010300003c0c1c22550001c201c4101030781c000519503a4140002c0242c402600800e4100c0709190078041c240350b001034640800f00d000e075500b03090004108101581c1d080501c02010310300800f40b2485005610802030040706034041c0808040e030441c074200104110081000710f4000c0340290721103d01a25824003e10740c4a802240c209080d80b501caa4013511500c124030020344030300c14400c00c40000755101d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 266841618 1250 266840368 266840401
    0x3040f08090112060609150513061412160f050a0806010c02010c021c02090603120403200a0b0a021506010f030b061303030306050301050a02091c03200322060504050603 74
    0x5918044c400035645120160a0100314000d81c1d490749544901803000c14016412603032000314024075880e603a4904401141c101d5001e000c0070601341b0302000f800030030440e03c441302800340f030103008046081c240c4a6170291080312101e0b42e4105101082c0025040a5004004554030500030300700440d0415007407004982c404070040c402580600c1c414101050460024101d0040a100b1740340706d091a1203d0301019030320210140c01019400c000c1106000081c0c0d030358034941006590305014914440c100b07001400200050700030f04406a40460802070081d410842160703100400340184c6411304104000a04440c1808590002e03d9100d215809050b10b448048403008002105d9502405072039141c0203010341080c0c480c2602c00e40c01c3c1404108901e00c1c038422100da0540c020b0812003402c0100301036440c02041582c081d400e215041d030b45800c441d0a0350b0018540010b81501665a07005500031000351000b0050600c0c0c2c0c0061109010b202d0160010122425500b00320f61550301c903600c2000c8070341c880c8030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 266842868 1250 266841618 266841647
    0xc080420040c0302030703060506040b04050d060609020c0f0c010309020a0b07170f0c0f07050d14030f0f0d0c090b03010603021309020d0606020f0d050d0903020c040507020706031103040f080901 85
    0x40c145200c2c08255144d4051402100213950030b08c1220341e40c00030011180034500624543c00c034100720810aa1a0a01c4c029125510400d4040360483d41c40102500b20b0300040c50f1006141c001c9490210940c005000301d03e401c4100742010030403021942c020a00128184c05000d00000c400034502092240d4a10070261a03801842d10305c2d0384c1c00030241d00d00e059801500d42c0b18005d2040010300e01c5c4070400030940c9029141c0c0506500c114240c40e4840c0300d045c00c840c0d520307138800d80004c00104400c8403040d0010076a51441c07000031545ca54085c0f0f9550100c803550000c020402420800c02e224030b01484048904481a0346405030b2615072010b503c20403442d0a610180791140300040581c0c00d40501d81121b07040312080c0d000e8030404150b0401880d1074503480641c1000050303041241070309155a43d480010454084e1045030041c14806c80841e04554040c0c5280003d0b07408032000f0010f50390325029140d601d12803c1c0e105030842c200340e030b210302248901103c01411050082540d90710390348200c412204042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 266844118 1250 266842868 266842871
    0x9090b01090506031c02071712090603060d0b040305090f0405090a03180509010807050405010f0f0302041d1911010e010c1217040f060515010f030e0304050a0f090f0c08042004 77
    0x29171355002075075070081880f8490102246010707501c440c40000c9040716405c0c19805d6614a040d80120802c07406a10041426074031814500010b8082005845100c0c81148240c403825524a0000100031054055038546403007141007008010440c2d0000c01c00500a81c0e05040114458034107002c0c290110b9500d07080f00c2e41088035600000350101000403410219401950200b0150340c071036000441400b25805995080344010200b00014101036101010085441c0030007006002c00c0e203116401c00c640000396284615440ca28070061080e4101860700c4a40c003401e010f05440c00110020f0a84a903c035030141c001014401100f88541c01541a0500e00406c02110181442c00f8904640a200c1e1540d042e500e15103010b0024500c9103065440c00401041610b88045a5a0605044000d0504010616810b00003403100107441e844050540014048202d00e207014207040c03a0307043d070407140044c00507004c00e03007040d103d000c1c403035000903440f5005508003212150750790301040d00d054484482c60426411a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 266845368 1250 266844118 266844163
    0x3030705010204140a03120806010216090b0109140d080706020f0301080a1101140d0e100f140604020901051605010e0a0309090c09030b0a0c030e070b030103030909090b0109050603 79
    0x300650052051341c0581c810ba040c03030362400c01404143c0d581804001c0041c1c2038100c441720020301445002d58003000510480300015104601c0c11340ca000d9030b9000c4201c1540b507424401c90b660b0030030100000351403000400c0804001200006800c6004028064009030001400809210f02074040301c002e48642d424079070380c07569101e05180ea2412545800e0340d0031150102034841942c4600908048118465900750801030100c2c4244010208a00b4443c0c041c415000c0b035140c800001d00031880c0078a90a01c0009040140c0c60040d01c10f5100102607500c2148104203000190f07800c40180c540c5030b0b0880c00d43e00d07070f05200791404c03500600040f1701d610010300c50620344074101540085800c00b84c072144802400052078422007a1044451408010300304000719000903240d0000ea4001010000c0c1482e0118658012460041c1806119008483e00540000050051582014404005040810040046040984800c524000180140c648680c0c03190086076041e03508022840314001c0c0c400c0e17900c103034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 266846618 1250 266845368 266845373
    0x30311030c1201080c1f020f0d050a181a1606020d05011d0f160e06040803211b0a0905041b08070302070302030409110c1c030501120f0f0c05030307 65
    0x460300308504100400c4401e00010404c0c86000c40d00415540d805402507100c00301c0407140c0c0c06c05106d054981811480b40300c4088058042c01c200c080c607008860340343c0720342d01c40c144100200013440c084070048440c1500e00d420001401000c8020325420241340c04140c035060b01224203403402f01280000340807180040740303140d4004001c0d80920304a40790a000c2da2880304a8980144189400701e0706500c00d0700c0014006420414085d40000d110300d00c506e403031400c142001d0002001c0c0d801c50340245141c0d81c40400c0e010b600100700c000072480210307400b0017243c50349004c40c0c0900e407103005100310382c581d0500860700d400c16038040d40005001c0c00b002001402000c2400402c01a03805500d003250000803001008214850700903c00c9803000764041c0d006d90b00d0142040c03d07403805130990311b2541c29840303810801e29403c5501841600f02d540c00000869050800e0b4603401025640d0681089051010b1208403400041c000d2444400b4258401c0c1c0c04070051005042070315603c0320780e511094260100003054000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 266847868 1250 266846618 266846641
    0x1002150702010c0201200304020904140304090b03070609080717070e010909021305010609140f040203070207080c010905060414010917010207030207090b030d3e152203031103 77
    0x5994a164001c00810186608010b6040c11440d1b841c1003420003000801d000d41040d254250340140505c200c0309045410381d0140c3e140d07611070392100031000c2e80c901070100585003e1003910014640e83c130340904140c1c20081e0a54607a8000c0c400d64152059080308644141818800c220044c01d2510031101250781d070388083c2028004400089214401e0050b00d1180194140701d8141a5801035a82e000740c1418001c0d80e04008141c02c01050f40484800d880070b10964660000b9803245110781e01030f00c40c4502d007004162130859a6583c0030305002308210284020384500094030112400840c1041c5000d42200060358000a00c0c0c112800e002c8610120403413100054008041d900e00c264200d8030340780d43c1d8415102c2110280540a0340c144c021403140303410588143c0000340c20b00101c1c2070b0202d1403a00a42440810741c42c0300d00006c4001082100c2e00206201400f41c844d0425800d0240543c500e86007001c0121001062410000b03a0381400808013854441e5000b51585410048410f5890a06654010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 266849118 1250 266847868 266847881
    0x10f0f050d080319060333141807081009051911010305040f050d0216060e06040e09030f030103050106032001020c01140909010306050901060602070f0315020d0c080f100e06100215070201 82
    0x4d01c44d007054025040c41c410248a90012840c207072a041c0842d8a481c488248449d0041d02441c0842c814018049007001042c010171141c0c841c80070380007400111602e03040c1d00703240b096440d03500000e0080c40b502c00414006040469008802d00e8000341c0c964440c42c0c030214455030b950f4041c0c000d03c15050350010382500007034200510200d181484405a607120f0003101c0e01c410030340425030411814802004000d43c5d1200356908042100140ca0070002d424000920030780007640161400d84d1102e10030018481d003450f04212040c002004400c0c0340c5c86c1c801c0042d68400390f640742d0074100000250400c607030b83e00c1c030825103600c4440105400103030359590409101800044d65601815482c082e800200706000140080c01c40c0e1102603000003442c9191900c20309803000001041c1101e17000c002c186024481880f4905007105151038081e2141070150509841c000300400e00c44144030312420510020000217909580181c00b292400c01c6002521412810202d00503140340700d00781110280112540c040d003094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 266850368 1250 266849118 266849183
    0x15020c0a03171005010c02060f040e0a0b0108100e0f040c0504090501050f01122402040b07120f03021305040906020d06030b0f0c070308060603040f0b010f0f050d0803190603 76
    0xc40558440b80910300d02424148201800306e081e4002c20001410803801410582c00684045401d02da82c1d040d001010319022a0700c4d1042540d100e011443e13641c1c102001303640000030201c0c4018400e0911544040821025089582500301c01c00090104400401c00b40041c21015005010038842c905c0c1680c00b0b82015248070b904c03190854008140d40d480b81d01030101c0160450343d24100c00700189940c01d0b090f088120041c0d400790302007001290765507038200201500c0d4820b9442c0503010404480050000600c5c0302c0c110704240c01001034010245c948614070081d80d804a80020741c1c45020700d0311400900c1031000054650741020000428460840020b610908101c40d00202e00d540e00c07482d6841500c07628200802181e55080452480d0030800003031035009210b0400840d4040080c3c4071020304140c01d81c442c0240d041141c01c18888280000c001e200200b000341d8030007200312880c0d80c88000c240802005030300d940c1c04640c181c98100c585a0424801940c03c0142e0041c050b01d020105550303130b03481c803425 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 266851618 1250 266850368 266850407
    0x3051c1d0606100e0907110d260705040501030b010e19030b0106020f030403060506010c05060f06120111030a15030f0b0708071d0907050c0f0304060e100c15020c0a03 73
    0x800d1420200c955041d440180d5540036950442d0f04108208041c000d0401b10810200d50341c4149120804c001142c0a4082c540741c601d07035140000880109020803c2807840032104400920003280e400400351000d450090a0228000aa00004980343c0b072100e09280c2d800140b00c00c0c0c0c00a40302e450841c05058030301034910742c0e80c04d80c0c90381010790352903c0d001c0303151025070f01c204020400705000c3e502007130300841d051600350550720140d154146046001d031a10051a0b0881c02172043c3c4c1d2604582c505951142000207009641c1d542c400441c46000043c4007900c00390300c0d11001304c0040c440d00080f00155078420000750218040e8100241100422103a01c00030a540b8008102218000c2281c0c6a290b140c0c40e0444809150100a004811102400520038004144a03902510b030007030101ca06849607110046840346d00e0f040009149207485da00544c010040003030000c2c0c1e025031044000320140d0b0030203501c540784550345811400910640303074140d034640100c01ca00d0081541c410310ba004104c541514 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 266852868 1250 266851618 266851621
    0x301120201090828061103071806020c010206040605180a06020403021005030402090a0f11181011071203020705060a0201050601091a07020904050a121101050a0606050703051c1d06 79
    0x40d4994511040b0425202a030814601c113541108a5002030b82c3c042c4100404070b1009900d075204c80d66a04161114004100c1902c8442c07624180f991048000300450310003080e64500160000c2c0d19524090000303000030381c030784001070400c45900725607a20303e0300c802045511441082c1018002504503010880c1b040313040401000780e140c450801e407030103240c0080c909211a2290f55001d0000c00c04200c0922501c0d032520800b2900c1010103003e040003481075007000d0001e00d0807404120703545400c05107600c10700a0142c070305180130000007600001d0b84c125208140244440b41003c2e4589001c507489503500480019010200c0c56064000c1e03030285c20280c17140c00c50b0381d44900c1e01400040c49422400240003040c05503c01524040d4070103a00300d030181c0203440468043e5102c20300c1103400d00f0391800104110b140c00e215070a10034841d46500032079110b0100b0083c0e0902000070001d100d80180030f000c100d004101e40700c0c00024802a54120741100d9801c12004000c0c105c11400c032618009420a24000d250 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 266854118 1250 266852868 266852879
    0xa1107081b2802010c14100b0d231f06210b130f150506030d020115030b280605041a03030d1d060103110915100503070509030102030112020109 63
    0x3540c8642c241c80221400415102c0e0000c120851451880907410001d041c00c1c480c000c214104402946d03c00c02e0005072602c11a000c1204065a1066100c0c600512240e88601d002c52440807052110030340d040c10b00e409101c81103c11031b2801c02e070b188070079820403510081d401c0d4810180d84001d04407521380c050a04030303040d882c01b0460041445c00c0007500d03181445c4006800d0400c64a26003034003504c1000b070581010541d40301e8000c905c00340180c034641c0581e20001c0c000c00d458100001001c44000388004c1c080c0d240b050400421840c403903c001040c0c01504004901d0204a180611241080780c01540415244986070302000d00342d6485045d005524002000404040d201d1041d0f50b07509001d00154908a4070503800001445150301c11148003200710402c1da6140000c1c4034490003076005401040d401948001007294841018180503c4080307840c0d4030300e410707440b0001042c002036800d04041d80c41741da600741c0640e05442a0f11003254903520020000c100080780044840700c0e503000782d0300c0b0280a9220f0b03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 266855368 1250 266854118 266854123
    0x6030a0c030b060a090908030703050129070201140d05010f230d05010603170a080606042d0801090b090105070509061806090a14040b03071208030a1107081b 69
    0x1580140a41140300c0007070000c1920b6240143d00200040d00c040d149558404081c4221840a01d044410381c03000011700004a91500905015002100448999601a90001c850740507201780b4291a0034005c104982568002c4081c1d500d0600001e440aa60b8003004900c2c2001709801d000b400e5503541c103840040341141d6000161901068002a8a0031400710441040103190941d007040700d0941d00d07983d020000907a001c0d860f240300c0c0003074010141c4074503607000d020300100300c01020103024040030f1200304605070078082d407045c07140d51128942443c0c040010300c1070009003540d0420b0b921903003404210410842d10001cad6a2003520040d000300f0040e01d070001c0c1182c0c1e44c03181c01d0325150b1102d000c0c084002400d0003210a04440180181482c0c40d0110480203d407200b8540c2e4403104c44a04502000011420540107001c6207090480c0549a001c1c180260414841a0380c100a0b00b075030344c0031000655204165000c1d422426074100e6041d22041540b505210780e030f00289000d401001001d600c0340d04a42c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 266856618 1250 266855368 266855383
    0x30f041403010f1112060f12030d0c180302060d06050a120501110c1c11011401030201030b09160c11040203092401081903021515032107170c060708040b0603 69
    0x1c19603841d1400640109011401c2c3d001b034004c40d40844500301c1c4c0411540c415051241309441030001c0c41d201d984c80702e1034008032502041c1810601c000c2c213907101030070b2680780d25903010f4a50407280780b9292101140010024015600000d820402550000c100d000e071081c0d6020720309100703900034091310f41c42d501140228064040140d000b0350194064820140c8100c181c140d1800c2c80d8900078000d0386103251900e094610300070001d000c81c00c84000501c1903581c1401010034002041e5086e13113250401c0272000150805200000d4108008200c0034000c00840711000d420b010710090080d03449003006003950391a451000c0c8201c01c0503204100307140948209540d118100d903a440080c18861a00d0116110f01462610f4218214091100511001c041000d8074a004425500d054400554950141b42c0f52020780024401c41140c1c842a408003000301008880d101ca40c011541c3e5405951315600507583d01031400c20040a00803070b02007068003548401c2e014490340c02061000e03620785580d418540c441c0784 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 266857868 1250 266856618 266856641
    0x40614030c0f0f0103021b0304060c0209090a050606010e0a0b0708090a0f0609050607080705060f010503010c0216050f0d0f0b0f0f060d021e030a06020301031101020d05040e09030f041403010f 84
    0xa22074110f04290300a5000d0b0015036042c400b01c8001c3c040c1c0c400500d080d46c0c0503410080203e407491090740c0640c1840c4c078405602c511711000400c2001500e0311110750f20b1200034002c038104007104507401e000751540c00382c01000f42440c0c03000035114802031030b00c0b01454128810141c040d0200703650000d400828848001d040300c0d2141c94604a207801d1500b40200ca6018080c1514000e0301000182c00142c4100078640c415550041c804e126541170408041c03e60302071005913011581b084103c0d0109440e416080030031074070110783d0200c0040c00913000c52400a0340e81d1024003400d0460500d0400d0140700f502d281e1040c00e00f03d18410341d690711408000f00e240000c0c1d40003034004032003900484c0141003003030403004003441c0601c400b401074520400091600b0032142d4122103860b0080010010414040c8840880000c240003070005640da054005005e401140302d8400541c0c03085000c503030318140c103004681c0c811086611196603a5120840c0411000301070340348038000d40c82c26088446242c840e10403081d4016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 266859118 1250 266857868 266857879
    0x31d0d020105030a02070f1208040302010e010501060927050702030c01180c060302033d0504060308160809031e0c09040b130309120b010608070c1a15040614030c0f 72
    0x1c4940032480c0c0250026602100c02105085590003c60208c403400c11b151401a5100c00307039403815182c024251200c050091140340e041c48010301109400542007015248031603505080742801c1004101d07044540ac01c1e10b8a898178000c24012402d5000c40142825031000c402880f258002d007000300b07034013203400300301a00218440c2001e000061080c0c0046420512031072101601d040c404203445080348040c1c0301c4140d60f00c100f90b01c1290680d80400340f08002d110495040042500d540c440003c00c2c4121050320031403114100c2244108810350098811907038001d800c0710114040a4402c0303506040030170401280e44100c800311011840c182a005120360340c481c2c0c03403006580322020840d5640c400c1804c00c4080c00b0f180b00020880007106004242a6401040d5800d02540b400001915802c0090105820042e9040114011822070500d0a444020451801081c0e5036214551102c034044550025403040c200798001500c020709a030071440035403048080e02c41a0318038004004082c4007007013901e030300070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 266860368 1250 266859118 266859121
    0x30f181b032619020c040e010501120f140f0d2a021e090f01030c0b0307050306011b15050f01080708070311012d02010f020901022104050d031d0d02010503 68
    0x200d800c40001003001041c01105042942c22010390340c0780c915660103d40107034010042200a4038260240904804101c8000c00c03065040084034008035504100c050300072500903142000304a0007061001141040106880c0385800c4221100d03101c80b4030140c00d030001003031810000d1280c021110750b5105101e0b001c0c2c010700030300016400e0142c8000c0c2044400002c0ca03040030103003070a40b5405c02662041c1d1a50100d560b15604528100a201085402c90b8a010f0720510070010140d07005000c072034009400342803100d14000c000035000003480c0030820061007c100b6032030008851001d508010700034291a44284281da8807490101e6136500f6034440d03030300350358001c20013040810b40100b11001900c50600d001010104d0355035401c0402c3d6000312b1408000003805280c07802140c0c0c2841004020a00031806501e82402100000d542d041c0380140c295442c1591007040001a80c00405c480007040c0c090100904202c0d1810007402d90a518040107a03a1b03006a801c00740d851031300c912049031032641611468150b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 266861618 1250 266860368 266860403
    0x6080705271302040608100602010209090c0c03070c121103010e030a0c050c04090f0507050a12060509010b280e06092202040f0f150506040504090201030f181b03 71
    0x403602561041500004450a440d9003000d140c0010b0005e060b41d5120b180340750410001040c4030340c6243c2d11003030441e441400499020b5844140050300700348252241a164500c203507041e030440c40fa845008100142c0d07141e0008001d007400404100890060350741e60340b0003003080d0501d826200601e81000242d0801c10090b10074500401c07001581034011b0302101c03500040d140c04241203038494032043e500c601d200240c0d441000000c0064001074107080d43c00d1030300c180ca402c030151855050080001d007030503100c40c0000c0f10750710258040c184a40e0300900700401d0344286080c68010a81d09500b0004d800003401c0c0100d14600207085c05405182c020b0141c038503075a141c540d0150403500003110203559440031952080540d03143e00800a102d000484005400b0603611a1802280c4d01820400c900030301c0c003181004250b40300d4065034103d450503600820200c51920040700107240c034651905006250080006000040400ba605002e02c504405100199100c4082c201d4400e1880010002d80c00500c40652 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 266862868 1250 266861618 266861677
    0x1060f03090c080d020f06010911030403050702010309052a0a051e0a2705090a020f060a140f030a0b060f0d181a0601090b0a08130c150906080705 64
    0x207407405510503812503500c0d51042c0d4105a06a615030b4016805083d11103c0e580040c000c0728010f0200c15004c02c50003a40030384c00d1030b0302d000c010703c0541400b9011400700300390b90107504450107041d881026603884c25450740b0520541c144203564000c0c42489901c114079942803c1c4c00b41c00544000510800340e0307030000041070160849400308541c00c1441920000740560601e16101002616514040300841031466400212000104081c8090384400000ca02603154004e2181076094150746c00c555a04090f0f0007525280100f08520303400302c0000400d0101000200080c501400364010280224011141044403500880c4001058250200076208401d40c499001d1280401c01a20700b0b0451040c90300e40445204100e00110b8084540804101c0151b074000350a0010307142044581d401d1940150000300664001407410300d08418140f07940e801e1000d40010240240040b402948480441600c01030010225200c0d500201e5100404109818000e000342c3e0108000108282080e0040c010a000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 266864118 1250 266862868 266862881
    0x507020d0807060e070e06030d0305040b0f07140403030c1101020304061d03070902030a050f01050a0b07031b05071805070e06090f150307020a03020f06011a0304030201060e0403030b01031401060f03 87
    0x150f0346a036507642d070040e446050103814002d244041d4a00304a10342103041c0350a000a0103181d104041c40d03c030400000071201d040503500000312100700c51095503070020a070382030401122091050200481d00100b0541c1c80000880307514803c502080400b00d81c800107903601e000e503024490220300952001c081c01416903000111009004048602203a6984144e100300d900a0b40e8083d090360701c60003007005d01061000c1e942d004010aa84c51200146804111031150003085002001c0100040c140c518005041161010301c940243c2940d030419078800d580329900c940394414a80e25030400c80040e11080c0200b0502c3c0c00300340302030411352610018a040000c0d151462807030562106040904c0440348205401951140c1711580003440c1d0103403c0d00b07001c0c1c68070b81240c0c14640c00e030f84002d00500c0540c44584195095000d02a50740da201d44491500360b000d001d258100d0840307040720504000a040e45230300803048075402038070104540e03e01540202d5200c0802d0042202090014806400c818429403208 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 266865368 1250 266864118 266864123
    0xb09150d090804050913050c040906150803031801020f040e0a150e011412190206070611040f090c0804110f0a0801060918050601060804031416050c010507020d0807 72
    0x452415560524030030484601080a448542e00854140280d04240c55941d0b001150601c002c00d8148a44d5500355075401c0e0314041c0e502458850a9400400c032854000c00f900700500041c00300101c1e11004495500d030001c41391040d002400040d00e0140d141c1c18400c030341240c000711050619040c00c145807420440e4000c1d200505090751014188610340407090000c010748500300e105007441d40b40015810181100091070713441050f84440070745190400007081e6400b0901c40902c081c0c0c000e00350000844c1030040200280181d824060000d00910074040200b003610b0740c00d800790050720f03203a407000b00c2180c0949100c00003107454400031901241d0241c000d00c503900320081402c41e003134004001003000062140d00103a0540c2d143c503001d12118165003d60030a980a0701e1010b10316076141c0c3c0f0340b13a036a044184265400d0009144c0400d0a062007540c0d1301b09166104c41d0380c00e83c2c4240310074000007003940144069669024040c80b4804644c8030354120b40d07000350001d140242401c11511003050030340c440c50f401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 266866618 1250 266865368 266865409
    0x11a0f0307050d020304030e0a1406180a08031305030d05030402180a06050a090b030d050f0d050c090a06020a052a06090f10171b12070e030f03070501060f0b09 70
    0xc0c540442528001184547d1090f81e901c030100100170b05020342155aa003002982c038803000c80c0d5540ca521460151624007842001840d100d11700100403860302c0340c0a0300030001500000903410080c9400748440c40840740c1c140d045641d40d451249044400d400140e0b40258400b550890a0030640d001c1c0100a410007038106c40000c00583d1500015441030580d804000c1480d122001c140140c6424020801404680c1c1812407900e50703501001c1003540b28800080c02d665070f40d5000714070744081c640159048810003400707141a141d200c4801035035400003508200c07034910507110110040038100c11795030103048900d251020b0f80c0b080d00042210f02d402214102e40c00081e14003140c851640c03100c1c1b10304800351060305c640390b8000790740e030b030150307920702c0052485003038440c0701a0041c0050742d00000c03074400c0a4081c2480b000c584401008407400040380b18030b154180304404943c91001d4000c8000c051281c0701e10300800856940300e040c0c02982009100f5250b1403a0b0520804842d418003021189030300030381808 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 266867868 1250 266866618 266866627
    0x6150904021503130302012906030c0706050a091e02030309120c09043206040201050315090a0c1115041101020715180503010513031101090b040f0209011a0f030705 72
    0x82030302c1d194000311003c0001103400100c11051640a202e40a04040f40c13041c040c07100c051010140c407010100d5401c1c28000c4100100007840c00e80e000d0107888101d0303440042030001d81070100c1000007030004000107442c40d800601421002c40c1c403248020901990180c003450804031244100104a101c3c445e201d2542c0c0030b0341c403000255a03108518248154803408542000c2d41a0b140002194242040f180d80380d5582852a0b8002250004081d035129030b0901c0e005a40303940701112800e95075000400160008140b60178031003000380d550050034503801a03a4542600d014045001646c3d9030441072400e10f40200340e00840c005c05c0003040c150400781c0042c0111003800b541c3e2059119220008441c0301e000032a2500c0c03403250740c5040400304004003411070080c0103909102c1d81407404062454001824841441110740c2840c8081d000003054540000d4012064607040c1058120041080c00880c412419000045400c03e421883c440b00754545c41e05072418019118800c031416072002d001142440020702 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 266869118 1250 266867868 266867899
    0xf08120a1a0f15160f080a140f180a05040c02010c0219020604090f0b0a0305070f0f350304090506190f090c02010603020904030203120c0c0a0f02060f040e180615090402 74
    0x42160007401e01c500d0b4481da1f0b624101d00d004001c08010050110b4105c401c12450031441c00c0d520940f0070503401030400d4240c00501c01c00050340c1d0350f0381d9400305801905221610240640642c061161300050b5000e4807903040c0b486036800481001c594009602c418248001c1c4042240e581c0400384180c20101c000a010300070303000043d140405540211103540c4000e0042c010100300c00403030002044d00300320001605081480c070b918000d1503103c0124420b50f01104001003074207400d405004003031b460003e9990320790701c5041c1c05001d41002c60b2a1030180e112a0242e000700c0c003d036103c0348216039004448400450802c40128003412940b5038410841d0340b159004005a620241d41034040ca02c243c00860780c07081d4009403001e09000040000c1c45d0030400b03001c3e030404024041030007209268011141704054115100059141c00303000800020380c1004640841c41c588260f00103406800032703840c814400700d00360b403804d9a5034908440c0e040e4580880b101d03039191418056400c641040c80144503000103265030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 266870368 1250 266869118 266869133
    0x1c06050d080c01060602030304020a030b0417180102061b0a0c08120a090506091501170709110310090b0d0f110409120f0804020d0f08120a1a0f1516 65
    0x15015207103418006510b40035242c00740300d4100103010a0000d14114a4250002010000940300c042c0c60400a40002001c101c0052143e0800d0095200180d0710754982090440b404181c080840c1c1c013503c11a80481c414030f40030f00c40503000100d03640e07445140601c0010201c409900c450f004a8004506204401c015543d9050040c890040d814001500c1803081c10a01d180c5007001d0f220503240d40040989980e0400c841d003217141582c06281a5051610f01c41071540d01c1c215455210000052824140b8101000304800940c0540840d00c02c0c1100c4607207440d00f0504503602a08170540c0108802140400102000380220000e4000da2020710310080c400c010900740c0c4d420f00e5003103031180b1892803010b280580083e0810100142e07490020b030145095804102229074004003e0801420035040404000200c400c96081d0b4041000a90903400d000c03802401400203036682d0740f5504400d000f880f1031820415815109450024500c0b00c00c4144000c4140741c0d07a0105200c54411021700707041c91b0209552 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 266871618 1250 266870368 266870389
    0x1050d060801020d060603150b0315090411090f07020304050d02060403050604030201150803130e04060b0d12090e070203030403120609020f04050a05061614011517010e01060b1c0605 80
    0x1504009a0364034414400c2d0812070b105c0e50420814503107040701c16003c0c0c0340644240300598000118544d03981d114140302203003070162644650350190418042001b00103122051503200e510036109981c09448641e00c0703e103640d00407a80b820050380180020845454800000c02c03000340050482407820ba02c80d1269420607004840540150391907210000c10404101032100042003103101450030445603140011078111980300d550403502c0d400c001705051180769800303e004c800300249602d00c1143e440c50040d4160001c0c4189001180e032410000411051320201144200c1040e4040c52450743e4907902a189480342400e4802d041c0e60314900845d040103244010310012400c0361455440d00d10b00300800401c0e0f17050b9002a4000c1506105807048615404034058031140c2c040c0ea030b000d20303c1d0361b111198010000a010154469240d201c0061040c110500b40ba0151107070500030b0041c41c5248007820f003625480e110301b0510050030460414074000c0310608100948222601181145d80e0300002440c4528 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 266872868 1250 266871618 266871629
    0x1020c130b010507231605010c0201030209060906190e011706011b06061202040e0309063c070201080709080c0103020a090b0a090f08070605030412030b040c0201020c07050a0b0a0e01050d06 83
    0xa810100d017030030a02040b00d6120f410018001c030a600f41810002005541d411900905160300401c0a812940d603080603100080720107000607448010308003040d054090300000b00300100d01d03c3d8540402c82d5105540e491204a6900b0031404640c48600044900c0c4c60008503000c030003d4821741398800501c0a000b00001803962004012054501e40100302c110388441804118a500030001040980c035654180c0c2c4440d00f5400c0400b0000820240d8000310460300e1107190800c5003005030342500c05150002400c490f500030b0740c0c2c1c0300d6955548541901c4c0d1134424022000607505c001c580c060b9a40c801d800800c0c1710040c0707103080041c0e15a00c0c0c0c040400391b0042d0b2920703004601c8000007405420b8804941b4802030411500030500a8a00040600140300c0540080c110000d002c10780c2c00114000d81000d0000c0b9806441007150041d10325009000b50021048807815020302080000c04d4900341d094801510400c401552030203041100c1514200c00d800754142c107022003448400d0901c11035100d03000081a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 266874118 1250 266872868 266872913
    0x5060708150303131403030d05090a03030f0203040c031b120807060e03030c030c130503060a0b040c020a0201120902010e13060807050a0303050a0305071808010212010501020c130b010507 82
    0x148000391810364444003810038081d40c014042c6100400405600c07008907622030800341442c805e0308010900394412040002841400d06091051010000614881d800d0080d6401c0010035a45001901a44800c2d18041c2410054a000340080b40440741882c1007100c200141002301a61207111003e0300a0044003591561710201d062800d108079030280c41110f130030110195165103081090340301d107804082c0044c0b05049011070201e8404501d0481c200203407600900f00c4d03e01c2c0c504019114003801110181030301484c2080d4000d22158000910030358500e030b058484610070309900f460b0100814810805074104621803a920840d521064001292042284070102d046801c0c40152072800c841a07200d60f0141c0b003103450420200e6400f105464500e801442e001c500380e101c01d0780131141c0500e854401e594088800c5400a2034000540c014841c00b907000803080b00c00e07a07a400040e6124003110b256190010303030381e40e82800b008016a10810700b0000505016041ca200fa8864030043c109281d0b1504044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 266875368 1250 266874118 266874121
    0xd0507030e0d0918060602060115050d0f0e0d020606030a0821010e0438072106050f0402040303050306210a0b07170118021b0a05031c0504020904080c010905060708 72
    0x11200030034984044410b04c0d042c000c540c5400002952420148500000010014403402426102d5400c80794054a00c0b0401c3c40440c41d0031040704003c001a640c00b051512455010500041c00856650b110b200010068075201c0503a8450f01e056602403e80003502c3d044001041243c400182c1c0007501810040080042d14074052070000340352001c00c0d004080d24200d480c04446241c40c0808092030b050a40d441e0395801d03481d41c480660364079446030040c0c011030f03a000d00e4442900205d503000d0002c99408442c1d02d82c1c6180b604090100b0dd1103240030140c0060801c10001d100d82c1440c0c803101107811201d4104107503800303a40e807180e03003000c58000c4210b49000c00e0000344004c550f40078034411540c4d1034030580e0b40d9482d40b40071185192041d18000c0344007415008903070001030b01100003951b0820800700c01568084031031868000c0d202d52001e210254060350f0b10003024660000340c031601d44921b0f40640149140e840c0c50325002c0083e001101501c2581d9250704258002840030300440d40140e60303a03100c00040703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 266876618 1250 266875368 266875379
    0x304051207050109080a0c0311060d090b06011812020402161208010e07111b0d02031c030510060f0302030406020417010506010f03020a080615040f030809031603080d0507030e0d09 79
    0x24000035600140705c59112821600208a554000310200c0b03500c03001c11480080711402051271030007603540c2101c9440c80c000c418410320054090180c4104400d036038022041c400d500c0744000c2192180100112091005020001420140c1c01007081e200c485d01d22050446450341c0b008800c030300c80007440c0005036860004002985120071070a420801c0b07801c00c00c040c036000c0030b81e0070390300c10303840805040c0201c0b82e91003107032607884141a80c4801c2d41c02800340c1d000c0305000b001c002c1075412560003000009140400140800c2c6400c032030700e01541c08039a5201c0003d88600e104038041d4102900650b1a160308200009034a40c60348440c48005030fa01c4000f103401c1c50b1450000d843ca00040d60050207140c0108121000c0540c4812000c3d8020003c1f10364180b800c0b002c5000e10154011904810111030780101c1c04020302c0322480290003004802c40031104d40c2400d003001c1d611000450310004020000600072500404050f07000203030b00001c107140c0041c200d0240c8042d903103003082d140043d50120300d401e0400d008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 266877868 1250 266876618 266876627
    0x3170703030f09021e04020d02040b120702010c050307080709050d050d0908011e230405100b060a0503010b030702010e1e19020a1a07020603040309060f0f0f0e0303040512070501 78
    0xb8000e440d0001000000b80039004645925004c80c0920ba510a110582400320740e00e680c151540800e411008546036a100d442c0c0c2011356210b4042a0001300010000076002441402000e9000c0e0b0555506815030302c8000050307030310303e0b0054a001e0900c112801e01256a0302d0341c0442d858410301490050150854000014001c4151600185901d034107080c0a0841c040b4001200360007100c0e880c07800201085001d00f00c90000025170307000a03020258206010074040001070502c08c40c086440100301840540d820006184601003149c80442c40900041140368084405182d01140754000402d100d03000a000505180c1e80c544a2018a186685400c0c40220104202c410311118420500c0000303509400142c24048544100c0e40201c201c601001e242d021108159060154050703c426164246890041d048020703034091034001030600a2a00000c500c2400341080c1c6e42c065885002a840000c201140c01c107684440c2e90b50944001c110026403521641c410001d000302100c050445607052200060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 266879118 1250 266877868 266877881
    0x5040335010b0906070b0a020301051318060b040b1203040602070e0c0f0a090b040b0304031b0b060f0f06070b010906081516140304030c0203010b0a0e0f0405070317070303 75
    0x10344040c125418200000003900460548110003806900c0c1c8035810000b80c02c0c1d00c9518001820780c102c903400c0c44603551144d0050b505070b5030200d400070380842042252004680e500c10701c5000b03050b4031100c1d030300100340550300030440344101500c0814405c00b94401f00700005071744201d1107121b07800000c0c00c2040c180c1c180188006420301e40c003a04824140003074010118040d41340303d031000200c00101f0500040c00340d54002c0050000100154680c0c7d59002c28185d1600121800e901180340c51581201d4000c0150902c07030800e81c040c1b00750b42151a04402d00c14004d4481c00225044864420010025642c460243c10100d12036042c00e4010341c1000344020a99070319910101e016407020000d6000d1100d00507038541c0c440140742d104050904003404c01c6a400c48800c00507075140100000380000e0590007811280442d000b50300900803171a2002c103004066006128001c0c0581d050400324420604031210141c0150041c0201e501c0d8a07241d4840c80e403400c4c950140d810342e00600241100c1010b070940901c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 266880368 1250 266879118 266879177
    0x30c06051f03060e03090307060507020405010605030f040f060b120c271501020705120f1501290c070f080609011b0509031507020705040e0d0f21050403 67
    0xca40700c03454007072440107020a0000030b00b000d4450290940401c400c0007640c2c0d2648008089400042e40e0310006000c43d840100d041c1d02a0781068000700340c41d030198040307038010300c21559403100d2503036552508901407142c40801c507455515003410700001d41c1c0c0c024102c0318206020300a00100d0540394100003401e807110280a0f025640c94440819020205a1072540f102420355080c044c210f810300100c0c1425060780250381e0040e0104484840c0c500009840344410072102c0c101c0ba0310300c040300c900c41c986001c24440e214610142c0d1039004612010311801240f114070b0070b00c0081c1000d800c0700c01c0c64180b11990300200c486808404082115580070090560008a81e4008021111800c9455004400ca1100d01c03024008001055002500d08000036503800c01e4080040d03205042a01000707403501c04610500c0c1c0700c1c41c1072801c100003123507020456542921540d20b5040342264113040940d00540c061040c20f0020200c441c0742d4030a1001c03806401d10480c403da82e10542c3d00f0801c140f104800c210000318 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 266881618 1250 266880368 266880391
    0xc271403060606341a0708060a090c0306030212030a020d050c0d0c05030c06040503030a0b0a0b030714070503040609060f0503060904151e06090e0a0507060c02040b0904030c0605 78
    0x9100480d103c5004a404984058007008002510124198040a42c9032000708007406041084410302c403e20110390800c6050881850031030700d0340d80c01100d4214050360034a40c002050305040201d64426849028461668140802d072103540e600040c945014901120003141c000007016501140e0520650f2411805400c21311f040c1801c1c0c490309591112414207400502045000081c09d00c4010400c0e10340801d1250304035012840d143c0380041d165002a5101c4c120f4a003009602c0c111494040380e60342c2039a8403604840e056558101c1d04998060000719141243c060401000703002c80c1c002d000420141440d0344584020616242d130061044031031444090411809100303000865035100f03d4a5009034110302d038076412124510b0441c0050004900c2c00224001e40110408500a5138114104a0f50249001c200c120b001590701903e071090001e0040142d0403145050100070f0003040c080f0030b0f06001a100003484940c1c0300c0400d002050a5405902240b181805c902c03c00210703003d002d030b02c0803c202e0b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 266882868 1250 266881618 266881621
    0x111130501032910030e060a150626071b0b01030b070914040c0e0301020406020f060a0203070f05070302010603020a06030902090a022104020d0c031b08060f010501030c27140306 78
    0x182c002e003108007901031044498583ca610f50b0740c400d40000c0c00c002481b0064032142c0c00d0000c14100240f144591501c040c0300708800020350340e40660400c41c403844030311104ac8644100d29807503402c601c400030400410311205000400145644117140d40c00740d40b082d1079401d01d42d41141080b651500c4003d0543c010030184540c240504155280d4914038200c0c1594046480398803084280e90150500c0465070700340d84007142c00259141d00041410410000c88250b0b1100e8450042d014264401100e020020503105220441401d2150b0001c241480c003034800012002e03201c1e80020f110f01850b80c0400c0010740c0b10901c030000d52030329141151b005a20320700b04520313220800484540341c000383d6003107844003048840041c066455010704c4201480c4c4c00001014070755260310b00b10609010740340c40c411499400781e0001c50401c0c000035009008505032028410542c1c6488011401b801c80c190410b03040107400700741202d0b903000c8081e858135200c505d07241c2d071901d00d41841f165843c52802ea02003984203520800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 266884118 1250 266882868 266882921
    0x112050601080303040f060b030a0206130504050a0b0f09041e060c080711070506070f150203041407060e06090402210601030e0601030b01170307050d02031b06070e040509011113050103 81
    0x21b01c0312901503849100441d10300440c0713000030f00740340c03140b040a0f4015000090f403642240b9081030100684a08440030003894803450756070002c903603501c080603802c200640c1d000c55140c034181000748d6005204204040710740740840182e10080c503118000710740164440d1443d111154002c00138070307800f410503d0300084800d550300d12280c3d6004140f02c1d017401503800207641d0b03003400140c0e00700150164010034440c06100d90985104023f40c01214161454904188840e00402011800704102d4541d5590f01030602907603400c10545a002211a961059080110100007024000300380b00b02c05c1030b0340410b4080c0c58540c00160940350282a0002113402c00702c0103000141c003030020707181942c290622980740070307601036001886d51141440c040c0862203444200d200540d800001800c07139080145440c1d2a02ca2607078829035484d5800d07036031003020868000c40c00285003420b034000c1345d10640304800412500311360341c840d00e40c660040f00c3c108481d040d00102484256014040c25040d038100795128104428440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 266885368 1250 266884118 266884133
    0x109080c130c0c061802030c15031501260601080106020703150e010204170109031b02130e0304150207030615180b0301090c0603090204050f010614030a14011205060108030304 77
    0x40c009041c00a5584445855940c0308216000b4007552002c4100201409030003000102060313424102d1091249050502d128201500441b03604261211260b04580760060b202030315410060449040241011003c5066804100c40c3d80d00c00b00700e10030880701c0c2e05018000401071641608984103661003500b00b0400558a200b01c5022503000e0000002c000e00c80c205a80c3c0a0701c150f90100c2c4506080144182c0300741c0c8194051301c81e1f0761203503e843c0c0e21000c500c0c0c400204100b440b01d000e540500000034140e0070754540c2d0400111a10a40f058a10341a120100c0e41c80f01c801030498840140c0c000507042c000c0028910036000300c0749044012180092505800c1d1913101c07020324044407219220a540c046c251401d4226180242d40803007002491900d0354030080040c855501d09134815410705002c0b4440040c2d00d01c84d98180d400d984e540d00242458554185680d90001d4821100c4a9175803000e0b42d0a036110318010740c041c010840300208210107504000e843c2541c1030f00407010f5034004009001c000341c5107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 266886618 1250 266885368 266885389
    0x150a050a110c1519020c0d0e030a080730030b03061005090403050a090e07120c08070210091b0801290108070f20030c070602031606020f0705011a0109080c 68
    0x1440c0300f0754255200419071080c0c150164482544c640041445403988201048901c682580c81d51501582070b40842003654a0003c101c02411440c07003084039401081010411000d001004a2141e0041e80d11900e010101900300b01000e0010b50703030755089005403030148102a08456070701c288995060504000907020100948000c0a0010002c1c6840001e402507800d0002000700c42c00c802c030a0702e00594003800c5420102c03140b100c424906110258800c2c040e450b19070242c0c10380d500070400b5049600c000c800070812050140c944083c066801e00d803041401c1d1068010705506c200108002004c1e4190b04090704542119012600c400780300f180040c1d90010203541d01080f81d00d00b0403a4108840c2003640c81207503c80101407104a102244032152100000919840002034229452913544040490701d074010128106425659148550046040c68014050243c0703201c0c00a032130165180c2d180703421a4800e0700d0108140201c0b0350003070785661300500d01c0e07001041a0005000044907110001d00003400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 266887868 1250 266886618 266886643
    0xd030506090f0717101503020705060c0a0c0b0103060614030609120306060c0a0b180304050a090b030313060305150a0605120a0605030a0f11010906091205150a050a110c 74
    0x102040003c1510344510201e140343d181090021501d8100701d00c00c0c0100120a024400c0c11444000221240314400d100319500745402001520361919108400b202607804900b142e401c00c60318100e1a4041501c492030b5a0003507219050002c0d2161a095083e60a06910034099120b90048401c1080308070000c0340c6161030108160307003550b80350388980000720103028145040342d1600c6031405102c1006814107413280034090340010340c8540307140c901c003a0b541c0344101d000e170300c0d003020072000200101d40c401d0f001a410360f90020700396800c00c00b007154003032070001c80c82e0310690003e0b40303c0040c844143d0341d405048801c1603040d036102c41d405081000203015071049010b0012020030003170004104d50110b0344004060030008003550000e08040c00c1031110355904130019150340809100300005507001c1c2c0648003c40e030704d6464000c103da00c0e15204c038005014841040e1054010928000800500c20204500c10603000d02c0028041c00e01c4a039080860342945c0c00e82d10187c0c410031030a03442040006030381c07400c1766 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 266889118 1250 266887868 266887891
    0x82107020103090b0a0506040b0609100809010905010c0207031202010b010807050904110f090405180706120b1909150b0412030302040515030601021603020603011404020c0d0e01020d03050609 84
    0x1065480120010807141c0c101812004800050041c1180345400c11405103000310f8090155240041c01c002c91442150302244c1d010b01c10a10394442c0901800242e58800300700d100000b00c0c0d8109031621070079508002c1e800700050304040c130203000304884001183d4a00520b84000c01c241840e400020b8003805018121009210001c102015190345c0c9410482c0404400065a49c48010325640d440094200d610154422401c1600080c1584280e03640890006154402030181341d2501c0c1c1d0a039070108003640820405901c1d200d1400b40c2c1d4807840084d0401403e05010103000758944048201211071107290241c189a107602c08102448941060741c00b43c84c0c0300071008850888a14003680248226131006800080c451242502581190042d62203020286c09440360309101c800c03502c4180e649408025031201c1c0a00042c0030311034040580412050015000620703003024030a00603c1c2c5141140e4280014100c0c0d2800c119070350341440305000d043e4a41c00d0901c820304022000400162000700004401d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 266890368 1250 266889118 266889127
    0x23040506030307020a060504090b0415030308060d1a04060501061e051b0105010314150106021b0a0512010e120f09100e060c0106050406120209040b19020c0c0405010821 74
    0x10341d018000c071900342d03074020803940d56203541c5d50024115401038414518500d20344030f83c801b0386041c2400303404a4400301c103419800207070550380d040d568024058503003900300a403403042c100002c0070543d80080b6811a0f481030ba030185094030700310050340d505801c14001c0103584a03a80400030300c5e14600b50425025424056206c2d55109181d070b14291082921030000d6007031100020601ca120303101d40f03a154249106464050103410070003814140c007032241d0b1005a000314a100c400911110301c4606000c802410a4004d55850707001400c04640850520f004c1d9554014030b40080b1000c0160800811811401d07508103040d0f0342c440c1e8101e00a030803076107009150441d80c0c00c01d600d10400c010b01070b10350300822282c3c07112807c10303056000317118501850380114609803003c2400000400e0581282c3e82c010485483c0d5540d07035481c0074850002800b82112900844445005440d440c0040c2440c00e8041004014409128042009584069100e07502607084019a0f0002449114010400010301010180d84 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 266891618 1250 266890368 266890381
    0x6080a0209061f0306150906120e241503010b1005070507081903020d2c0406090f0b0301060b03090d0f0e0310020901020114060906040b0112060f0e01230405 69
    0x88444941504070030078240400c00e40f042c0e0180c2c01081036504501116414a84110040e0b448518500032040443d0403c1c40035400904650004031550805000b0707500803101b800f11440c90800c0031905001c031046a20f003004017107081140c1420314040128000d000c00204140030400e21000c5940c1035041001c0001d500040c031008104200040c24100120360110301c0c18520182880c11090081340180a0046e5420300a40701d0050669040c1004501034203000059080d0000091901d05442c0c115440f80d000040c0000144104c0031072004112020540701c0b1024201421100c2039000b052541ca824400c1c0580000000380c89103440384241020809121010401d075225041c00b0b490310f41c1440394560006054202c1d4024000783c0d002a0000d00072388800050407104001d00304c4100b508080d45c00c0010304079161980104013011418100390462600c50b0304940b0590b50550800340103585082c0003040801603202c0b10301d004061803860a0409540e4000d80c4030000070200d0128483c40d00d81c008a0740 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 266892868 1250 266891618 266891629
    0xf0507050a05070b0307020616050f09120d050903070911090d17040602030403031706032a0a030b060f090c040501140d1b021603020306040b0a110307080108060a06080a020906 77
    0x2000b900701c011a800580e4602000c03486900c220703103d6006002d500c0c040780c5040c0002040d51810074007602d495090002001c68004070360442001180d115007401200c00a4400622240480d12616550300765540c40200a041c82c00030b2681c40f513103505182c044020300101f419801d82d108020221484050b6000508021440041c500c00082107000e000500060540d00000288201c81c4691100707500c140112401d070502700400c461580d050340020700c2d00201408891070524210703402c0c481754800e0a80c1c00021849242c07444e082240c07d518a14144642450007103c003540000c411280e2492174540050a0081030080b8803826041c8030351030b070340b503d0606105400d80755003003100042007110310781e0780301d014442044140401c405805107078481d0101c1c400c0d2882003410b690300030340100190b81b1a1750f0703808100d45008040d510a035130780e0820040342900c00401140500407540d01d011055041072400d40c205840030707044000340c40ca44641040458004070b0b080f0710aa404544510307556599102050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 266894118 1250 266892868 266892883
    0x402070203070e2203080f0403050408011806050c030402130213151d01050a02030a1209060e0325121209020405011d010909030806100c15050f0a0c0f050705 69
    0x70350502426401040800303030500d10320f100d084090404004041a00749801903000c501e100980081c904800094815060036449500140300f4070f001441c10b991264030f40c0c00c44e0070308040449900c500340c0d43c1c10207000480c01199000310700c145c0500c0c60741c102940040c290f60304002c908560309401081500e030f00038041040800400800c1040409400c2c0c0c00f1000388048211800c3d8411180e9000103a0301a500c00e00589162210a40085141c04900001550100f00b0421608d15158030381060000141c42c602640d1344410300c043c000c60711440c0d4040c1d44841d102050b559002c02c440500d0310b042c007088a044141d191114a07050241c68542080d0f003030009030508800c045d421905050001a2100808c002610610f0010300500000d98980c102c15040d208200c8003d8000741201d00414000c1c500740c0f120312540c11141c00d0100c821812580c810714005c0d0001c910549443e45d81007001807210300c582c401980000c88130802c100703000781000043e0040c010300000f14200000450364030100002080001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 266895368 1250 266894118 266894123
    0x6090723090403030f0e070e0a0e120d02040321050a0e01020109020909061504020c030a08071b061401060e22140103050606010e030706020703020609210606011e120b040207 76
    0x140740d5482c05003400342c080e09161000c40e0205280038600f41541c0f00c00702e84401a655080704140c5161188980940901503102c0480440d009240341440b6610500008100d07041d0070306005600ca92031820111103109020301110900c030b4007010344096139507200084800d203003103d0030007042550310304004070f0051030a814020340041c40c81040c00789608002810a01c100c0032004461842d00b000340078032050b4040c030601668150b00c14007000c070a50b402180100c0c1c4c4030b0f25910f0706640f281e41d20007840d80d480010550a03201a581c0341e030549140c11024050034050001d0341440364046059501107142000d280250a680c6009418244069001a00f01c101e100009030880c039155612801d1141e2209012b4691034040b0344074020355480d42c140412480c045038503503005081c0c0d040c596000d220155100c4004188d0103a00e50110940b80740c0800381c036100c500d2000c07005020301d00c0c1410001d410f0041201e07000107003003000928800040c0c0c3c0a410100e101340041c102041100407500889e0180c003d40400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 266896618 1250 266895368 266895379
    0xc15090d060e0a05010b0a0b040b09210307030e0420030a0f1b110c04060510050706020f0a0c0c080601140f030102042103030f0908190e12160806090723 67
    0x54410720605402c044020402203501a0610356620008c0c4d200d84502d10903030b1408402803010410a2809038071400a075044402580c801016260b24503042d40d200c40e40c201d003c18544590307041a803c2034850224201540480440c401203800c08001c11804014081c984036034560414414030b88150b00b1014000c2500d42d000302900b610700101810581c9000f082e10309511500c3c00c00103c51607d801000100d038406440d01a400d40f94200031a2982e00c069030561311b4903001c1080c403690036190703802099140503a50366000c8001d80340c506058007956540c030181d00c0707521000040c4442c142c0c403000410b103500121821700d50300403450b02081c0a030241c0e42c009031403c4010300440e600c1300040041b98901c46e100781d40030841030303400d03040f440215000710002616181050040d0807580261000f00f034544103190500009440c110b10005100506481801320b540d008520b1746008156040040310140000400ae8981ea1800f100200d030f542c003040c03003051120b800041c8403080100b1625420a00054007401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 266897868 1250 266896618 266896633
    0xc05060702030409050606090f060a03150e0106020118080409230109020915040623070605090705030d03140c030c04090626060709030627060e0c15090d060e 69
    0x30040d45a402502c5959206824480000c0141c5002c20450710120340003866500e41c0702001050128a030450303e00803052590b60010034040c00c20303200d1400010304080703091442d0b0b5030404200909650030011122942c04501c1d803030b600080c1d56441a107082c0e54030300c0c10014010040b650b883c4a81c490b40071806229060000011a50850380e800400c284102510b140080c074008400003550742c030031481510300003203642c000f140076842920541c403d02100680c805040803229154034046030401e4a40142e503622003541000305013002d01034007142200b01e0408112410310300b000caa080000050051b05401000000110102c00c12800d03540078000f03c40c810801583c43e1120925207652840b000c007400540c0c5604a1001c010000300c1e139200e03120a95030044e00901d0360740c81c44094102100128139a11040601c0f016502402200100c82406034601040e400840c4140b2810101034914103402180398514084003103e01904a901c0028250344004000d08035040c0900100340b01840e41c02140034602 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 266899118 1250 266897868 266897881
    0x9030c090c0d0e070b2505010f0e0c06040503120304050a1407030203070b03190b040204080307030804060e0a0222020409110903070b030907060e0f060f03040b1e0a0b010c0506 77
    0x1018000301009114204800003071610352554030b40303c0307104a000301c0034100030100c02144159449889980320506d1014412811741d15a429900e0004680300e425036a551170101c840008c2102151403030301a542a03190074240700c04a6100c2011412091561100002007802c1240402c103d21000750810714040701101062401c0703850741c010740b1003a407182c41a4180405e2191030441280d005e940b180c0c030300d946100317591a240d0026141066100d0b9015a09010014044e6000d00040c01c04606c20303500d00e500c80c603003881c1100484001517036010360740e8080d81010005031070300c0102102c0004407608031a450480d8240d0354007c2d200301d0704002c0b800390610141521341a05003024105108080b420784041c80e4807000704210500040b1107032034503a8041001048000d001e00041070030703420301174040800440e482c400b00300150311070f055441c98030358008100014803441c2c0409c3d68200319805942c1d01d810400030801040020040d181c40202c9545200b80d44083c1e00490070080d0300d680c403c003520702925142 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 266900368 1250 266899118 266899141
    0x4050a02090c070b1506030711070b04060905040e0a080a201207050105150913020103020d0612031205090618100e1b0102010b180c0c070f060f02060609040809030c09 73
    0x30201244d0708098040441c2040720024030342c01055402415290440c1c0d290035040b58004145002c4040300d00520310003140030407000000340050101a21040310301031420050204546207140808802d810101d4103900080e40c4a0071101c004800d460301d00d10449841c45010101c10441150114070b1003a280100050440240504a031901450003007182c0e81d41d400c180d2001a41e2240c2c030310381c0301c0049400500803d0200301c8540c0c40d640103140050070110007200701c408440c044c1c1c1000c0c030301014040c100d104240d4000300f00a50000300d00703814010390400b52206584c0d4400a40b00702a15426900183c0d00340104202078400d00508100c01d0165600c0390b480c241e00c80c9604800c103240441d1004540c659540140500829401c0242c9006c4009040c00084401028080c240841d40c010030408039048400400200015000b03803040c010f2010b1030514054144030000720300c1e0b402e540000d4100003196942c5440703242d2058005049d29502d096650000e820310b8042c00d0042d6104001c03505000c0c0c0716480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 266901618 1250 266900368 266900377
    0x270603030c03081812031825080d08060103020d0b040f1e0903050f0a09030209040b0702011a101805040c0c0c09060312050c192406050105040e04050a02090c 69
    0x20f5100c85545880f507203030f101440701807403142580d141c0c040b41c9008044441d040c01550f000da5032441503c0302e07a40b0140031a0610036002d51a0324030340e501d00300c0880d520307921a0280008145183c0102140d005880f4041c1022800070401414543d02050240d40c101c0d441e0000451150024005c00c0300014041090006021034440643d40a84525050096a00c248a11856103401d5100c06092020380c020902842c1d102c50700030010401d41c1100000180c88029480e8007451041c1c101c60500c4c5008000242100c10094400703444510022541206072264800c002e60340403107190070a8000700c240729800c035000c1f165110580003840c0007244038000e0362200111a21038403030501004038070350f20b548400690743c1501010303051100c0840d580c4030440c0558028880d40d02c944d400c0d40c14803201080c1d4020608010311003035071001d198003900810303858900d0301000c89448401040004a0030000024400d0040e8042c12a4500710318002c1020b2003000c200b84055607500034402c180c2490b12104000b820307080f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 266902868 1250 266901618 266901623
    0x1b020409080d152d050402030702060702060f060a060e01140c0705030c0405041a150a1724190e061303140f030a0b120604030905011b020a270603030c 66
    0x600550f02001c0c2d0500c404403801c84404102190080043c850420302c07004404a0700c1c0341d014002900020b1303d84036400a540300e11110f4000c0c001c54904180c0180c10242d0040015202c0c01c040e0f020000d20b540c1300e074541e000340c4985251188203000003500598a0041840c43c00c0e03140c1c6404640c0111800d400034141080d104150107a804000c078603014041641c0b0140d41c02440030001c03164a50b21040f8100c44254441c0491028050a0b45c442c00850584007c80e0001a102d822160b0b0302100350a0410000900c4800c1803000c84421001050307011030b044014154480e109400001d01d07001184940001140d00442000e640c80d6091481740d041c01ea42c6804000c0300401d41e568200306900d00c10006580041e0741000f005861541c070030304050010040d0020140c1e010040c8206180c1c14103082103103d1003544a925480a110304120001d01a0481e0500994a10018101e4100181c440720810412903107182141440070b60144000704d201490688820030082c41c2000000c241603001403103c1001c0e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 266904118 1250 266902868 266902871
    0xb2805010f0905040b0a020306060415020a110d050a030f02010603060e03040509070807080105220227030c01050f0a030b0306090a12090803120901020f070f1103060402010c031b020409080d 83
    0x250b54880792400e4502c11100503210b002c001d00010300c0040a5002145d1001000304541e141c2a2501d0014000c500c121806d44016440442d20b0700030002030b95030315411482e0460b201401c0d603a45685059841500010080800141c6884c2d80381a60007500314074003850b4002e0f414041503005601c0380e40c0d2500300c0c3c0b01d07a0f4843c89020004c034070540d0045c0059070241d1519a11400242c5c00c0000f80032100d240310000c200305588072100c12800c520303144054424030001c0300304c0380825190000303145122086403071220710903042040c1c1220340c0c0c1c3e003110864141494821106482d80a02d240075030007070510241403505806000e04000040001180c10300500e4854620414113101d8180e0899101500e8011012503500400c000b90200b5001003405070702000070780025141010008103000950440342003146c519011500050402160b10384400c141402a40105550320b0f1980008214620540f8041c0c00d100c000c41000c0d07034803904000020045900940300303000c2045d02c0d00d84130b0080c0d40581c444070002c0303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 266905368 1250 266904118 266904149
    0x1505100e040f180b040302030f030a020304020a060e03070e0603010f050903030a0509070608010608091204120c1a0403020616020d0f120e0109090b0609042414030304030b280501 78
    0x207000d00d2280c02c06402243c50740c20500182c0b503803580c01034500540241c1c158402840b29404070752a40d00110710030070301c60340b02680303c1c2014818803594000c1c42c0c0000d0248040d100172000f69803000078818044803020f400d10000c41c0c40c6c4c00c02081c010a5840000c4503107908000c2000030f0b80743c0c000015400307084202d400304050744e2804c1c0007544807040c6001c0d0714001071030a001041000d110303d440c990000342c09003d40701e0012580181f0103850380f06901031850605806000010310800b81428001008054040c0c515426202c500592900c0782d800007c0c400e901c04626403078000e000d00da50701340440d4082c01c4002c1d000001c0c00c20130050009000111351b08000702110792002881010401071032a4180c54400d000d60403d038034200500404a1342c2d0740c010105005896a5030b0350780c001c155800030580806040c1d44003451450448540c26081070701d00c2884010810742c5501c000049070102c0b07420515003852a11941007501200c00118103400303608960801c04920001c0a0748418100c48030014031905a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 266906474 1106 266905368 266905391
    0xf173d03050c040e030f040b070305040b0d0f0b010309050c1c0b0c0a0905060301120605070909050415060503190f0203120403050d0206070e06070201031505100e04 72
    0x1d95001518681940c00c2038424402c0d1509580040d52400e24583e0b000502c5104e03500c6020202d20001600005140c45102680d02600c41d000120f030b43c50320715044c0003018160100584088520308280b4a040d9800ba2050501207a440006420041c1c4041c040040c1c02d03540302c6e074840d0050b03182c2c0d2100c00004d241c80304046c4a00b52140d41c16407a108115001000c1900301c1e00064010b02c42040140b2140070888401c0f213a00764000c0c00801c0d95619498112500e013031300c0d44111945401d000c180800c01440180e0300c18920a2040f081009030f40d0f5008040d51001404200c1e218504500401800f00d499055140ca0701d034000740407540b014507400000342c005e0b0300650003a5441d0b00080352a100013941449141d820407080e00d00181c41c40015000910140b040d004001c3c149540c81184807011105200328100810000740340403442c040e061405081e0b5906510602d1103246420138203271a = true := by decide +kernel

theorem cover : BRFrame.Cov 266726618 266906474 := by
  have h0 := BRFrame.cov_init 266726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 266726618 ≤ n) (h2 : n < 266906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
