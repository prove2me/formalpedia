-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:48:52.494186+00:00
-- url     : https://prove2.me/submissions/2aff0182-95ad-4878-8ad4-b83666aa1767

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 566546762 ≤ n < 566726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 566548012 1250 566546762 566546767
    0xf1c0215040f1e0c09051503012310030501050a0209030d090305030f03040804030602070c0501140909180313152a1137050916031a0405071d0312 64
    0x2e540380c1010303d07084002200e0801c3c0030203980c6800818076590b0f444045496070f55400d01080c0543c400040814a50a40080c400c00d00d02e4540c140006030b940d4640c9a04618160116400d110042043c1d03000717541000082c0218103000ca02d0320020351080300014803d1162019001d00c02d400b4030112021030b5002000b45040081740c184000540c1e100520841d04ca070020040880040d40d544080e1032440c0c00b409180e1011390074040003400292000300006821001481009600d50701c0c4d01080364818540c0106090362020a440a851400703500b070700c10440ca80036800801d03d5046d560bc0c3c24481e1a15a80380c44030002107480d03280303c7d004d0403452024401d0310005c6020100b489281c0c58203417208094581942c1015075800b40751000c40c010a482d91103154040c050611000d01546038028103011a2040100e05051400014241200341c0d5101410744031043c059114100000802c0b0002010304140407624007588002c2c0408801d0000c14148142e500c00d00819007000242c900c084007445881e00d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 566549262 1250 566548012 566548043
    0x405010807150807050717070318080a0609050c0901120302191707020f09070c020405011a0a12270b100503030a050c0c0402160510050402030a12020f1c021504 70
    0x450f43c1c00002c2002050080030060351002401916a40f10300d41c569213043c80d141c585510b8000e00c11075060446041944584000340031051012490108046d4020f000003000003007440d12905096070348810300e0740080d600c400058141049070118680c1381c400d509550341c010384000380c21500c220100b005400000d45982d4042d0700d11801d401480d6250004111001a0b9500400101d00340c0c4221100c2c8001409480100210300301405054090264000350b001300780514020002940240401d8200300101064030f105403044540c0200316041034a1080303400031003a20a803105c10403d00000b00d801040400005102c408064021810359000801440c64015101c01c22200c0c0e401000c030001c214012001d88514a0307507644000c040e040ca42540c4001d20107205e01b085818002050080d00c2c14909007010003006076008220300c5107095000e0240030205d044d4440480c90012003c0705041284070b8642c0510f84040861078806003c0c101c0d41c02c559180305100c0000b10341542c00c2d50000d08001d4500c0e0a10b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 566550512 1250 566549262 566549267
    0x304060c0509030d050a0f0e03060406020306010917010b09070e01140a030213120309050603070804021e031b0a12230102120a0603030f0e090f060301020d0911040501080715 76
    0xd00000c005450304034204204400064200004559110003003440001c0b140f1070541c1059840c6039544150404d00d01c03c0115601082c0c8400c0c000b040101700a900100142060380503030702940242c0320a40440c180240c5900c406402008400d01c0d40e44140c1e000c01c0000c418a2066400a4820b0300695035104460240c100120040e0070007016082415001d00421b911880b10b20420001028075001302090030100e07003806040f00c11a0340001d130080c5000c104002c00650444c0c035142e000307507040d50006002c1182e0030021a5500e4400710540c0d06008440d210307d109020035000284001c021a05120038558401c0b22180303403481e20100600d42c0c50001d0149121205022000c07081d807081900240c50070600c11003028444030215102d1040702d0f035554081c01030503070100b44071282e505c040c2420410380000d4400510110402000d01d41500b040c0c070001002600c0c20b4055030003201103024144948011450050701541c0c0000400b40114a4000005903182e00041c21794125005100c044980039100c6004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 566551762 1250 566550512 566550521
    0x5010f021c0c030b040c08011509151101090b0403080f010b090a05040f0902030a0b18010605090117010609020f09120c011b0f0b0109061d0709050f0406050612190203040305030406 79
    0x1004145542c4d410b4000702c07510f55008110510446a40b06200e03581030100196500c500358002d5000c000c0d0070307442441803104c0600c2c281c0c2e8001c0c01c0d08040380d03041101800381c0c0c0544092000103040340b583c40140030400d5080300a06000d4034071326036054420380c0c031016500000d01403441c1c2c1c1640444499001c1000741000e5001d400b114480c004041480c0d41d86402203403410038814000c480380c9a01400304156114501c01400918883d04000d0000518000010300c00c440c0601a007071540401030003140c03a802c0e0035400000100141c4a0035922512038000300e062a0700032b01400c500a140c240090342424001203920551201c0507102c05602c21001262960238a02c41101220521011365540012031032a0308560b000f045103000200d195814840000b21082040d6403981031045034000744040540c000c0482d1050b11800e80b15006030f60504030000c2c000d0070150f4800354000c000000c860b6000c1400d402610312507400415804050305500c40346800320700c0110740203000500140301240005169410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 566553012 1250 566551762 566551781
    0x1210b0105060a1103030906010512070303141621021908040e19060b030a0b040c020d0302031506030103060c020c100e0913080c0109050c01110604141905060405010f021c 75
    0x11321001084400d14180d10310742c001c4e00c08500325408040108242d140018507541030408030000342c04036602c4d6540c041e000080e130103081e1000e44000314030043e102c2c1c0c818032130802e081e401c0311454103188402c02d0703500549800c0031150720050089451051409a0500d81001000e81c061281d03842d2901d060412006080c0103040762014980448511603c003800b0700601c80a07090100140d9500d007132000e4080204c0d604941c005001d01c2c285504030f5020354010402442d086640c0c2009640c030740d2041c40020407540402e440ca40d011b0008000072060044035480400700344d02c00d400b10f43c0000c0d205000c12082c00301ca00420070002c0c5a41c0c0f0302020301c0c1014889582c0001d80c080c1c9250202685540e012583d0300b0440b034008541e9500d480c071a0900008000c040c2c050102820480150284454083d46511005202074072101c250104031090710001c00a0701c01c1285045100d0994162a01d0103903181c100c02c1c1c1d0165030301d60070614107a01c142c5170340c800c5a4260003016006500c4d03004500d402d0300a0504400f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 566554262 1250 566553012 566553017
    0x90b03011508071806080d0e040e0d0203030901060f05060a0509041e14010b04060c06020c0715091716030605040203011e1d01020306030c01180b070b01210b0105060a 73
    0x501ea04040d0001088001e0000e0a0190031498108202c5a40000b240304048140d60700f04401003040d07034008510b51409010314030f060101410f151f404103015007012050314250b482400c0c00c413400b00d17a000c4080e500440d1010004e01c0390558a400000c09108240141c030b83c044030802142d000107000e1801480a188041d2004c40c2007e0f11020103240c414440101c00c0d031064a400c40003c6c4c882c42d443d00d25001d80403484c6d40504040c20102c0040c8491103282c8020711280d0700146000701803608000d000000e250450f018042440203140040c0420054856504a98000140c00120500c045001d00c1c00617881d8510204d0149034bd1100d10140c040900141e82556032400d070001c0e905207000001a8141d001d0b8404114010002d07080540c095600c4d16208550344148280042c0b913030b021502c1580e000b02441c0c00c02000300401c07040500003800341c0c0f001d44180e0001584d11704006e03540248604030744810304600da2024a900400301d821b01c0301c0500038400d464490050000340381420107090121500e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 566555512 1250 566554262 566554271
    0x3020f10021204180b0d0519050a05070303051b010504050607080415110a02070f050a03080901120e0c0411130b0d111c0b3a0524070216090b0301 64
    0x551440d0740d0b0380c1c4590030500b00c0500c2e02d403e4441100441c06040c100041c01c0e18802100186030301d9007a00c6423041d240341c00c509034442c8111400e116080100e075802c5c540150588031402c0d0340b0728024040d07520030110085401482c81000c03840c42c6042c45654800c50700000075016680e201c200450b070707030440240202d6081114000c840341c010403e1050204030558100302c00c0d51000308100180c40e10200c2e0380140440d0100d03c80c10320103519143c00810840307900101070740d00d40340b60f100140c2e0203540100885011516100c4002c140550008032100e10b01c20a0302c041003c41d40803a0000d036284941c045050002c0d222580030800c1d901c2450091004040c1000001003c2a4503400500c265203c0d007040112062007008003030342c0924a102c1c0c9640c1e0202200c005a100f000b00f4020703981007a0718285410300250500c0002880f20300307071510001c40b59000c2c041c0c40c4181e030400320b10034940b11403480e43d00444c140c4200041c800c50001030451890030743e4514010348a4908030503080a08000e00388140c155495 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 566556762 1250 566555512 566555533
    0x1302090717150102070b0a200109021302071a06100809120406020a06141b03060a09110d0c0509060d050606160506010812090f04020307030e030d020c100603020f1002 73
    0x1101d0340c5070107408010459985002c48600080c5400010b400c400c900c1c00d0100030070701c0e07402e41007944d143d0000050400e84050358810030165004080c0c0d0034029400007081045c210706400f1a03030050100611544154000c00c410041c1c1c0070410b103080f6a901d80044001c0344411200d405044070359400b83c038503001c440b0806055030284015800503482003000d41e201c10300c0041001040e004240b03001d0f80707000a0012901e8181650030201c00500051a4040c40001c00308000780c442c650b0f8a80984a452814014829010035405c050380c0030300b0801c40198584007050349071520420458140201c0240030318100450708405c0001888040e2101c0d0740003400b08400410b9561512800b40e03114010400782c1500c1d807406140a080c8021042012491181080f8090295031119120390350080c050794010303203c0d5030f41c2c4000c1c0c00401d94003129815910004c544841c030415182c0081022094110540d11074000c8142c844042d2070305400020b61000360348540280f00e04040b80000003224040c8100c5103034904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 566558012 1250 566556762 566556797
    0x10603020a08150f04020f060f0f040f08060f04022103070f08090907140403171605010b0a0b040510050a021609060f080a050607031d1605011713020907 67
    0x1c0d6548125038940100700c203000e2081d0b442400c2c590011061104101e0361403da40055084011503124510030500810740c5030a400e0341e4010b803003201103000c1d1280c2e81e403901d924070000c0555030351242e030030b5a01c50300001400704469904101d0041e50701914013503104a4080071000076102220325654184020321020000c0780145003071031569802407070040e907a030740c40c41705100c1c000306c000300040b09201c15080300c114400031450486003200e070425400d085002d03207612000c1580c894800c6c10300e0020040190181030140650210815003030460711100303004c2c0c1e01c038848001e034003862050a6000c9248a2002c100034006c84c000c0010004510545451100c0c4c1000c107114070102d0b40205582a64400e0f040c440a004081ea420142c1228030080180c0b0501e959080c0c2e603554000c150100b095112840002c0501950100c0590070100d00142c411600c131380300c0e00030040c850342e03c40c0b1350005400c82024104141e0011440c1c0c003032a4000c05d0f03d003c4403001d409010030304801610000400c0b0011011070b64040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 566559262 1250 566558012 566558029
    0x60c0313140901050a0e060904030903080d1b03061206020a09030b0c0909130b0601110c03030406050306030c04090309030b070c0804180c020f1504060e030f0c07091a01030e01060302 80
    0x484031110344010075409080c0020403034141c221901803c101041400b5030100b400040c1c1c0d00480440343c080da47e6075113250842d0945020341c4010300c20302000c54200076400468100510148400c10050406054258118143c4c3c00f039110780502018400103120118504e074008080d41c142c1270030000806030f43c0360f5440303110f98401c8803900c40107500880d000507e4038003c14013a8010507401000105036000f9180c940440d9005002c017418001c42a111008034001400035001050004055944484da2620042d200da8402c0380c549209019260409181c4c0c0f4040c450710560540681c0e035981460700710364504680c03640180c114011320003c8003c01e0006084200104080e1500d1004d0031a0441d00141c2e0794140e0b0742420861055401040421b00d03241c000040340540030441380200940354403030b41042001040480c260400034000011010010b21181c00108070fa621004100e450042d0b0b5201944125184208071015407203160346020103961017504103903e031420100001401c981d03a6800140200c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 566560512 1250 566559262 566559269
    0x140703080403050607030501231305070f020610030b07080a0f15140d08030c0d0902030a0b010614030f24030d080a15030c0b131508010f0602010218060c0313 69
    0x840020706004106050100ca03400c08428181880a9410800d038104210a8121011a0307c40700640c685000e660311800d0081c10b40980504000604182c3e400415203000400300c40c015200710b034080748025249044510403a90003030140c02068031040c00884541c0d801a01c85039105448220000c8260154419501d07a80c09401c2044081490600c0d100c0404a05501451103002d682d1411070208944170200c1c8c0c1e000c0741c0c03003001c0ea40e110081c043c0c800040001280c043d4140c481e89802c0010040c001c110705060f01c145444000e440b99035202c282e605440200d500d00c080c21640f5002c90907a0a0320380206a1250000c880580e04d5200c410202e8070300414040c1000001c2d0000c41402aa00c60f41e21840d540628404501003c142c1183c440040e08040d910030030902c0d10001680181e0351030a80c00c3c0b00c004d0f0190301403020300704506941c000c03ea02020b01480020b2081030000040c440c2c014400c03103d98812034004c044540e07072400f00300107403500050b41504282c082040401140ca8030b1041d1140075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 566561762 1250 566560512 566560523
    0x5030105060a051b070b040e0c1606021317010b09060613090908072a050102010209061603030905030a0c0501050709140d03120e03071a01060c080c3d0c0e0d140703 72
    0x8031494414801c023851800707415002c4d0528100000b03000300074004214803005420101c0582c2d0f651705a000e00360445001d40c0151410b240358241c2c03140658064000560302501101c0c120555100d900070800c8601c0382210004150046907000c0080030625080030b00c0060144506a051200c0364603180c0201440c80e540c0025110070800c1c201e04140c40c0040c143c0901000c1c4021818445814007243e254070500700c00c07981c40d24520030704904240c42600002da401e5402026a0b80319510300d80040c0c40703a81d52000403030b219428280042d480070310840818049400705000351946802107400d019982c512004240e0030000e608500843c1070003980521610251050000c6a072602242481100e20030a9450070090000300e400401030603520050070581107030080f00c0580c1da6504140c7c41840c02051605594060070103000c1942400ca4007088d0800008414640305119510340a80204498403119800017140040f0300c0b41210341070800c810400c0521410582d410103100703980c0c403407412919034000c60f030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 566563012 1250 566561762 566561767
    0x7050a12110720090709050109030b0c040f0e01360b0f03071719050718090501090303050711060402060a050a0e0405250212030627240105030105060a051b070b 70
    0x200b42014100950b000e517040c600004c1040c140000245514418400030341440e4120011411425007501210000e1003910210318800c2c0c4e8460710445041c07001d00c40c0c00401080c4600050380208840b46119507040114550300c0406000726116009183c0b1106980d00103000d030040c409944c03010003000000d00b401c1e134912550329041e840c66600d0200c2c42c0b2028900d813660245100d002807030005441c410f8130b2050683c41008841040300d00c00420401c0d00c050920740c00e00311700c0c4013807581540c0454001c40460b91000010100290020703624030007a20020f421601c10445c20180700c3c03003800074252002c006c1c9000c807660408580090140c90702034900022480c40c410602d41c810022512403101001c1c54005440d1790850b0010701c42090000510702c6008241010b0141c00288405088485035424045841c1c01c41c1040080019684091984407400d0150707401e01c03070000d43c000c005880c122800107211902c1c0c0003821900326403075000501aa6568a0034001d0307001c00c10018841c0c10060801489210b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 566564262 1250 566563012 566563073
    0x50a140a0b270103060b0d0f08040e130f0b1005220c021612020d080a02060109111303020609030102070804030803041e150c09090c02010f0507050a121107 68
    0x440e00a031100310000b00154140100040744900400e1811a9001000010707407844c1d11000c07a01114070b0440080ca40350700d95144004020490020b401a41c5080076222026038902c648002008004600035008c0ea49800504001402e4450704580c40704146901c070050550314004140250300e0300b54610103005000f03031041c0d8500114400d9180e58041c6d0f200401c040e4950000d0704841400170301491070b0f10f0348040502c40a548446441019480e40f0510299035102084002900c0324820301030389842d503007010401504480d03c4002e845004032480750320909185181d00f0440c4d107600c61070b134558055400b071005401040780c40f40500011401703140217a5a914091402941040002c5100750844404481000c00304640d21021008504191800180704c4068182030310f090070b469000400d6281028100c8035840da041d0401100304007082c07014000e58554a0040c0c80c1d9020340000000000c02c12500c100c1c0c1458641c1100741090021001d291074440152182d2020006203045503005110007914070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 566565512 1250 566564262 566564269
    0x207030908100209092e1e0b0c0d0503100f030b040b0603060f1f0305010c0c060510050603070c0606150c0b060108012105190606031502041206050a140a0b 68
    0x5503041c041c10300b011443c01d581030000441043e0301a101c110715001c6078407071141d00880c0e040035003d400010b0a030200425902ca03081d181300b01402d405245241c521500c00254540b0744815500b040d01c5040c09004164120f01e030480f2180c01c000c250594401001c6000035184503444a8400030350b01440d14000240380c2418011441400900901c2c003a900100400903030011a03450320707810032441c2049049540c85846408405500c03500041c03c19480d11640710911a0405000b240a0303124034818001517840400800d4101664407500350000820000181c82610131626421b80718410100050429220402c040409440a40000101c0c0b500e0500d041407151600440f580120240307001c080702c0d030401c104281d00703001840c84034009800016111013000814402d61180381580240c02c0c0c0c0103003c90410030f0280100d0310084c0d81c00313001c003204002118003500032501607402c405900142c9042d695240c00c01803000800c0301440c9a6200d00d544010b9544290450180817241c601080c81413484040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 566566762 1250 566565512 566565523
    0x1b08040e090607081608010311212d060105101e0207051c0c05011d090f0f0618190f2c07060e06070501060512010e1203072708010207030908 62
    0x1403000c556204c05c80c0400d19900240c00740c19030f071b80301c951545030014a40c0411686c040c00070010520640c03401c01c10070f094000040f0042c00083c000701c020302c5850031051086507040340c1c0c0b4142e80b03190030400040c842400c4c03050000402d00b41504d0641c0840c1070003402d004200510442100050700840340c20401498101440c1310003111804032011800515174804000c1c040303910400781400b00b1301003480301e01f000c6079101c1d080c1c461000d4200b80030307464121034910a00b0b8003100c12495602c0c841c404140b050902c0d01150207041c0400d2003408507612507501070401d40d9000240707165410345035200001c8001c0315028115000e01c1540600c3c88c408841d251030100c02a59103001d24180e0b001d001c04024890b804404c0d0380d000e400655045546802c0d03810709030f000d041d82c0d8122580081070051040da0b4a80150b101304c81c0310104074159404108414207002d40761005845020008029800b2421500350601082c42e40038004071540781c01c070b5601c40302142a0307004594150081001c01e03208000e01d8809001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 566568012 1250 566566762 566566771
    0x20a080d1a101d030102250212030a0206010909050c180604060608070903030c0813030c0e0609040f08221806050306011a03521b08040e09060708 64
    0x70030340c010b99000500100740c1040c2c54100d0b181d04191090f54041903c1c294102d0b00208960110a1100181003643c014504018002240036004541031a522814044203807030007054194050aa140d2a02485001402d01d43c0420f0b80c82e4003e00815003810399415107821071108541600740802d1030198100f100f1201268400e5050010b200100022540c0c4007801800b034075803505048100101c00e0800c21114003600c508240b0000d5055004824001903004110449219400c844901c3c2c1d034510921800701000d644c000c11a00a0b0032400e0700080c40700d4050401c000c0035081e4100d008020307220b52415545a503000c0300450102c1c0800d0160000a400342c1030150106078002c050551414004284400c11940e0348412a0000310100350300f9200d08071150300d03400c0759109003141400340b0070149184c681d452000040491801605c0f0f22009054002e0703a0640b002515100700784807001c040c21103c240440340449000c0c8007000f0118003000394a00c0c40d40100041e600802c20740c5007000024128440190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 566569262 1250 566568012 566568019
    0x3030a050406140912070f08030f0103170c070501031d011e06092703050f07081201050103050f1603140f01090506034b0a0209150f090601020a080d1a 66
    0x7070403c04030780c00004284014103103010517160b6a030303441e040c48038549212201c0280008000014001c0e01072647c0302e4141a04d0007440e03008840c103000072104100c0e10488860945542015508108079802903115501d04120000017441c0100000103c03421102511580421756608640b0503c11841610407003015041c860400c20121030030300c882074105030552481e036a11407501c4a0020803d41320380160348441c01d6218519031200201c0c80d0000c011b07048621516080c0122500001e9150300c40e02401d030041e0520381c0e010310036403540c160b00012480150010300501d500d40340030500d0040a240c000c3d200c1c1192128081455040481020607540c025007040d00c42e0340a91620329800341d0740001a00c1201d03004400a5001e80e60401c00a402115810780300201c4d441001041070558010880d00c240398400c4078070b0780540e65000550b4001d040320101640d04051191035040c840d081a001c240e4000304140100c61010007555103081080d80416120442c55482d4001240c170001d00d101507801c410b0088 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 566570512 1250 566569262 566569301
    0x60a03050a051617060a0e0103030905090a0203010b0306040b041104030b19060602030a0327050105042105071b0317040f0603020f03131b08150903090306240303030a050406 76
    0x7841d001303140c1208a50ba00c44514004404034505640b046c1640c801441200001020f543e07603800c1c041c064000c184074080c05240038a001038460010b52003280d0584000400003801d640701c1c40140030007404402e02142c0c00c281d503801c03200086070f01c81018000443c400d01481505d46000307a4a00e0b04c8801c941034040d085818100d05004864001c800c0e01d100c03880a1400080303214015410f0b407520007070240d42d2942081804118402d000c07064100764800c0e80a46815040400516a4140c0c1a02e241e000840041d03030a104500000300c120f0111441c42a41400c01c101c0242c40f5140d2403954482030285052225000500f0415001041e1040005000d2030404500f019540d0500c00180d01c4014260481b41e040e040c02d0f80c080150420020043e000e80b081903418594446070f18564410038400300211940c0c141d000600c2107900001141c0f01d65401034050702564030b8284940300a40404003100c005807006000000312503d0800155100300c0c0c88038400700c0c0604040c10980100e80c801e040d03124410703440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 566571762 1250 566570512 566570551
    0xc051207020a23190308180405070f0206011715070215010801150b360411070c170316030f0306050f0a030809180a051803030f0a1109060a03050a05 65
    0x1044951140c642003942c034030a03a49140c03507075141940d04c0b83d00000c00902020900019411501e0700c0214036800c151800c2043d07803030f61002510040010807040380107a2003007006111000d20b1611034000841c0d5181252209400c03001008503d00c000c6036000300503485401d0180e206041c0300729140c0141080c4008000e00340b102111040190210701528212080001c0c0f850b0103045401100804481d1151042c20040c400800d4202c1440d407500b00b06200781d040c45001e8040c2a90b000407502ca55500c0000d000c0d01501c0d1020164981c0c5104802d400503010500981080080f00148001500e110350307140390000103075200140484615400160080050790300a0035203071078210744001034a4029441d01d843c3c034110800110301840d512048014010305170107100ca401101c1d00814042c90000c00041c10103480c000c15240d0b0780c00122000c0c90000c0c2860041020f00c40b01d039000091a10254810600e00842600800c142ea440b40100e0300000b5603c10030049480a40e2041540000461200741e0300c07000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 566573012 1250 566571762 566571809
    0x91b0301150903080a030902091e060d111f02100603050c0d05010b12030301030c060f12150e01270c0c0813050a08030a0f02061014010c051207020a 65
    0x140904524000d0041e01c086005001e4010b03070000f10b912a003115683c08003400020054080704904074004c05d40c0a02048202c600c92001e80c00e40741c44203841d04407550b100c404110304d007003003039000781c46501040000c1c071a81d440d4101e0403040c10039504100e48284582142c024905100f4038070501005180480c04d03c002070002c200150110b1085840a56a14007424001d0050003a0b034032007a803140d8104558181e11134080007641c100c900400710314113031076507403131095690700300c11128240016078202254100c110705500c005014501c880702e00843c1c6440c0c1505044c4100d0030f8101c402000100311640c82c1c9400d012105005070101d801d03060240804145015100800300350005000c410049841045ea400f070045100c006c00e00142080c04081d656420103031070341d204040040006141030340b065115400041c505011740c40750380301340d21114501030b0310b204007009650205041040240070320002c40d01c1009a04d445410300462603580c1e0140344108204501c251340601e0048003a0341320b02c0756844 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 566574262 1250 566573012 566573017
    0x5010e060916060503070809070503012d0c080f040507050405040803090d0f09090209030c0a060c0302070b04080d05090d060c020c030c01031406011b06020a0203033102102606091b 79
    0x46c035080480c0a40c648200c0f0a08000c11504034a4042d031914480300b0f90f01e1005210381c400c901600c0040c0004064801c1000b003034a405190540c089404000802c100794103107046075a1081c042c0007666400764403040000d041d41c0007503500760740342c510100a000074144180060301310010300341801106101d4005000d04100c143e4441e042c01c542e408a400c00040c0c8003406084000b4800500d0728540507200ca0010b455a0400e010a0b00144a4054003007103180c10301c8100e9080e20242001030002200d6070100300d919034448002550400c504802c860f0006915004040840307000703402030325001e40c4050905180c1501600054101801e00f405030284a40c2407000035003103c0700303182c06090000b020503020b249030300c80c1c81c00414161000800f0f05506502201550040340e64400c5200d012610b18244a02800581c0c1a1408c224039a00f41d400181f5051001c8507800d41e0034141801107480300b01c000440c60000303018075024521fa400404c0401c4c6401840c103a4490a00e040303026095808011804190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 566575512 1250 566574262 566574271
    0xd021207111e0f0f030406030c0c172505070810020909010e150604030b24030303071d0d080c1002041a0a0302041502030a1e120902040905010e060916060503 69
    0x30b5290540e08852030410b0040c000d8060407001220404400c0c0c8002a0b0342e68003501c1040d000034508444a115507120b0040da260b01d54021045502180d88903500d500698826580801c4c081000e04612113580f4050341d52a054500850152007031600d0402214102503a1490717003079606204001060060366244219410346a28a038400f440382d0f10a00d0010384110090141d0f6070002000c64004100580c400000b485041c480040305071106860703880c0f4422801e81d006199150300107100265400c1d1080a011201d540c0101c10040040c070386802185281c8040501650014000036075560b01000400079144080c100910440c07401c0d18000e11204a03611107032043c040100002941d5062511a40548002d4070031842d6640c402c100b070300b00c042d5407070b40100d450102050210980c0610070b08c800019050380e40c000d850b05d40c003038043c800921008001c240c1d0200d0b1b2207641c600030000810740034440d0026004a14008200504140820740e20b030480359070800304101c03002c520620119a100c0d0940f50030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 566576762 1250 566575512 566575543
    0xf0212011401050f21040c0f060504120b071e0c05060c0f040302060f07050105150f0909030a0c0c0f030f140a02060909221119050f06090d0501020d02120711 69
    0x145e07031900402945001d128042c1148450340c00b404c0c04240452990a101120300e00001c0620407941c6907015100340c05030740f1410382000b40d656a480041a20050019484240c501d44440c0314020050004500c580310340d00b640c0021a610051420801d003001201d80200740d40d4032090078504c5810700400244200d000080c02040c002c1480000d120584041e14400d551000c021700203460b241c146180750501122030b1900c0b0710120251003100382003048102d80100f145902071440c00e0115181500c8c00541c02104891100c000070000402140400485014502c41d000940c0140010b050030f071004448441e2a000a03003000c485480141c0d036a600711000290203641d818140d640d0181c007010b4010800101c12420101702e0010390801c0711400c032044040d8011110001d0b8202c414614150059070b501400390405091103001019141600103044050f000408030043c80103d5a28182660004441d00903076940103e02c89000b003408000650740721405141c07080340309030fa1191781a510080f042c8150724 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 566578012 1250 566576762 566576767
    0x110304180b18130213140105100507050a0c05030708030408060601180909050c01030c030204031a0406150e010501030c0c050c090a020408030a2a0c03060c030f0f0212011401050f 78
    0x1401d441d41800340d075a6032100a010006032500f036050304240081c02c081248164001c0103140d004940520441031016074040c101c06031070b82003c05015041d4464501013080c04018031505000490400940c00c04900c00c00045064510300000e2510b000c040d6000000c15400910052144050000d0f0203a131069007440c1c42c6414285281061001d050383e90000d41f14242020381c81c17030600000182050911500380e804101903140308104034200e01030360100424a03210000c2c240340c50505203921a41090103010001512800d101010a120b1403d911160f00c00d80e03050700410140d070301071150b804480f4160130203002013003150361400e444030442d9242c1481000d142d0045007426404d6410744002d841103900303c80c0d0310380b070110000d450416542d1100030006041b01038144500f0717000581c5036035141c4c01901400b6060850b540d5101400c4400403034000c0590310003c07004221024000c1c060380e00c0c0700500050f980c1078200700754810404141c11012164654403054041c03a40d00008030740001900124458 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 566579262 1250 566578012 566578031
    0x80a0c050403080c1501050a1412280302191518050105070201021201090b06040b1b16090c030e0c01030b060909010f0f091b03090204140408030711030418 68
    0x12503034055600301806a501c04601c20804100010f1035007101400200c00646aa0740e0301c0411842c0049401440c00e08010b191410403a03080c0500144401e07440b0606031707084881c589200d10304074000440121004120003a03010249034040c0400c560380d00402518103c103c100d40c40d803490140c0d50383d5038004581d41d111141162142c92400d207101055011000707101d1800c01d03a90007400703900b01c02d003115560300d80e0000000d10070006c1d215200c0c44070b80150032907050500d00345044403542c0100b00712a1807804441070718001d1700c0d424005802220507201081d0210303070600b220401255980203500d000e241c070b001c00002c1d80030000030700707901417400901c0c0c045003158000780407c5c3c19001e49075540c0e410043c03800010400045c81d442c003800307480080c010b40400742da032003002005644140080380000802506001c0c03038a031090700311800c10b9001a2011400170301413503091081200840d000d40d40d00034040148494240c0c841029005013010000075801c140c02d06a28080d0341c1740302803102c40f419a4031000759 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 566580512 1250 566579262 566579267
    0x2a050712021608010609291507080415110a03081f0f0b19050f0324061909090b0105120a060b0f04060e04050103080919080a0f1703010303080a0c 64
    0x107140d100c100e07902c00200c1c680e42d03020803400707020203001d109005410000182d6070b01c81c0c0425002e200082d038514684514030b4080c2805005242c94102c90132102c001c0140d100401d45900c004c0c8000e1091151035400340c0c4400400820321046202604019045079030003030b012a45c00171480b0703001280402d52401034080540c40c0f1003100c2442c0e101c0720f104016441e000a224140c80003806500f403900d9450010819204802c17582c070b101d45d18062140c41d500b800807420304201040e00b80100f05c40c0c86441d00100d0843e400007011500b100301c00000b84103d903004418010b5224208500803c01c15905021026200001800c18014142d03a1003401d45c0150005030041820341200300100f000211207a0342e03191500d0360042075806402000086601802515900c0c2031a10800e0f04890b0000c04150400c024801000031024000c1044000c2100010022882004c14484040100c3c800c1c4d803c082e0164180c5043c1d1100c95507002d0324a04141c05000400219401c07034803c42d030000f03501400141500d44100103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 566581762 1250 566580512 566580523
    0x2060d0e10090c1a040e150d0803010902071a13020f06160503070303050708070906050c07230f060315060d06150914030a020102100b0a03060504062a05071202 70
    0x80c52441ca040c0809002441240072251055450b00200c0c0312000315940c2200381c992090f1300c99036078041c1c00c0f0070010703043c03c080118100714054000c020714400c1c415030f120303580719410a8200381c100a81c006a228104810703c800c44044603c1c11798003001d80d01e000c000301025100c405034041c0c010112100c074200c003503071140c0407105042003142e41c8900140301400c15a603642c1008074110046480c0101142400b402510201d05c079803c070350ba070003e5890a000003101c044c1c00041c5141d44130b100748d40c0701280c80d0045900440d502c40450010b02240341c1039008100c1607a0720780c00070500801080080c003c1c103051141c144402d00c04142c54450703642c01502a140000c081541c001926507440244c58500720303038428184411500e400391006901e04000c0101520f4440f05000217000d6481401d56503156281070b0002c1500c003400810801c41c1d00d030780391a89010788a0445007100c6442d569000c0d21007020795480d2941c1101c0348582001e100403182c500c050306030310502074080c007000340604125a2283c0308028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 566583012 1250 566581762 566581783
    0x42409062304050a030c15020a02030a030c02030f070b0a021e030417070803030903121503070608100e040f02030609030429071b06030b22020d09050d050a0311040302060d0e 76
    0x2d16031017541ca0400f03070369240580c0140e000140d00b101c4101c40349480012502d4110b90000e0241501b07158595054a4100f1418012a014012820000c4010320113100b00b4000f410408605e55848d014500020b00b008003240070100550011104144020702c004160360030b032070909010781608103c04420700d10b00f10a540c032411142c4400820400e012030007001030034100d01019881140e50301e40d11001a0995298003403540c0540c13048600f04070440c41514559040151004500d652070717210441640600701c112019148045e0308bc02c1d800860508200d4568019004405142044c0c14401c0f10044170000308803020068454080c0304400c1e103081001c0340c0c2c1540d445030042c8407919003120010f080840a220340d0011910b04101d4840c0c508103c42a5a001500c92440d0382000404010b800c0c000d4111501340008107a43d0822200056030030040d05204140315101c0c80d843c1c8800d0500141603500402d40d520b8407010038803040005840300e0040e14010000340102003000d540000c4da480c41c102d035489 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 566584262 1250 566583012 566583019
    0xf070f0b1e03070f1214070806060c250b0903030d0207020301110a080a060920130509070203070501150b070807030324030213090308010e100b04240906230405 70
    0xf4055010341148012034403074280c1d1604419620f04569581c00c4030b085900701e0042560040c0041c801ea0320622241340d11500003800542809407a1003100c2c40c2844d9683e40400c2e03e141d180c01401c1800003520341034020609411100d1406001001098880c0180b0032134494140c0c000c9030540031507400703408c085800f25101041c20b4030b411040000a06050003940c500403140e25104002c990b0242c40d01601c12124007082112603200c01c800c14007202644241040401905038070390205840c0e556800301400b40340b65070f00668a03a203d60a01c0d40c21101440a159000e4031464010004415421700b510f13500c0e500038820607142d5807a2705080c3c01a00805040720f10700400300442103040c1c40d0058100301641e000380c2e510004800c420701c4100c11100601005008581590010010000b81900c04c6500400d4141c0741d000896468404c1d80d80c80d0025000b11175812015080500164025861841c1c2c1103441d00e4803c0c002403801c0406010b400314036050640742c4060228560407008480121001804042c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 566585512 1250 566584262 566584267
    0xb0a060801050c07060b15090d080d0609051f03050c060703051201090c230301050909031b1b0108191104120803060411180105071a0a0b030f070f0b1e 66
    0xb11810603c56021031021a1a1131030080d039610a07041c4860300071940d01c2070021152502508408210b0120100c850885100350204aa00d9010740c2c1030103020002d041541000c43c160a181082100c1005400c0040403402d66030101000403031000030350038201d8001540c00c540e90b140c0b0360804403150b04c1142c09503c82c041c081c5000244c0d00c0c4003503006100c2040035a42d442c4810200255207981ca0902041003c0d2000040c80103004034540070a00303a070002c1d40c5004507803400d030b543d000c0d002c44a20000070180391500000810a40b0f84070280ba011443c035800d10b4561801c1c43d01406115240380100b5145510070b690300542c6450000680c2268042d000c04409000c0f80081450480000d60084584a0051f4144003a51001c0411203094600080f2200104e06100380a800110b80c0d50b02f100f141560458545035071600c14201901085000311040702d0040303600c0340c4100c00d1602c1c1c0f0202800150381c82e0b02c011030401585284241100035900e009200e5503036510411880d000402d5040381020861900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 566586762 1250 566585512 566585521
    0x5030c071218080304060e04020d060e15041103130f06060b040b1b010b100309020103060504021809010812090d050c090705130506040e010b070204110a030c1106130b0a06080105 78
    0x5065010100801500c030090b10392101400c645034000d5110300350115a070989400c60a280940203011000c00b020000038005070f944441d0001c5800c02d481405035800c800d034071504c07070b800d103801002c3d8002125118240303582014602d104580c40d003000054824004051180d007003042e1604040002d1a0190070760b0380302c685807006101543d000c3c1425000c6002d42c2244000c02003010702410a042800a004602c450307101c80042d800741c440d070941241007655824010900740d8652010300400b840300c081e0103d11038201404c1c0309001c20181c115180c540d00003058500303080586170441c0c2e5080800e9400560801340c03403404614162805640c20390001d0f0003010440300320741c002e001c0c15914521070076094046558000340300301d03032045000305441d0b180920010701c407014480b4020f10800e4405000040c0c0d03a034010a40046c207030401900c0c41c000903219018201000c4e1f20916007a00c0c04049000707441d207402c204100c10071041c0c202c0e030010000e00f40c6000081090034580e0040000308003410080c44607140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 566588012 1250 566586762 566586767
    0x130f0210050a081008032a06010f050f0102060606041202010c020306040609021e010c120c050114060a0e2401020a0c2408190b0a0f030c06171605030c0712 68
    0x1c00d81c040b800160b40d410028000441c03061010301114860b001a500d0441c0780c500300030803c61540c014034aa086c03400645620342c20200702641c001c111703000403074a0683c01c00080040541000c06202e0441d4400c0051140c2680c0e03440444089a60108540b07008101510058980d810b112001950501401c010481130200799004002040d10817125203c10200003400000001c5078910114001021f0604060000d0300c440300500c03c0f1900b070300340100040001e60301c0b9406c1d1030035040074903502c4601405001c01c0c0e00744050100050315007640340707004519003440d001040403007000c0c00c04010400d480c00004035034000e1004072002504003040080741501c075211101200003098480d2080501c0842800910344640070302030040c81030055556120316200c000b01c029080d00d10036035138482c9000e80001750201d031510150000394801d00d0030b06802458110f015081e91603140244049042200400c20355601100e0f10440800d03c41c1401a00c9441e21400d0740d60038001d0300e90003052519400c00d060707200e58 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 566589262 1250 566588012 566588017
    0x601083c1b0c0a060f140a0c080c0c1207260408060f0601020615061b07050f0307270902060403030c020301110c12030c07051c020115030803130f021005 67
    0x1000001240c0a00386142861080c511800b4442e80041d08a5400d000000d00d16401c402c00c01c0c8002100880c107001c5900003a81640815144d0504151755071648881054020704960391080c4c1001199003080c3e40aa0256200d920608503001c100400003075090410200100351070700000d030500006031401c1c03c9001100c007036000c1c0c00351010900c142c000082c43c6a05600d0310522510060b406045103448d21042ca28410080703070401d55000d9800c0c0030400d08200c200a400c083c44120030010401a03140c107050280d0a40d031028402e0080d00044c0050050b102034088024481c1e4500e04101d0090242090800c020081908001d600c45000100041450f5000710107140c864000c60013040096103c00007050b05101e040401e18598004410290031441070308051944283e00f0307400c60b4608180365455604090703003c00444240fa55502c2c0408100303074244140502100100401541541075850300126404010f003401c00c0f0f51000104c41d010402c480f41901201d5078081c103c20a40000214090308a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 566590512 1250 566589262 566589271
    0xf020703020a05150403050f1b060907050414010b1b2a041d07050f060c071d0903070308130602071b0612200705070f0803210601083c 59
    0x244595201ca440341032484c1c0d405401141e154468074507000d5109a00c82c01c94110712200a4140d00a400700702c54840c0501040344079480c40c101a00249061004101c02c0344d00300d0241d24182840e54005101c02180d040455031021b0403160305036040842460a01d107414118140412040070040c1c818040c44d07020700303a041c0081c0044a050200207459101c3c80503000d02a15000b2140c0d0210100308441e0400c100a2600000e014201614050389a03c1007881c0030b03030703d80c4148069041131800c40310140107810840c3d081f03002e20b0042d500e0000c940c1c8000b000700a000c0c2180484403150780c100001c00540b981114240340e4002c0400b400b21600e44141191010b2900c502c001113800c0300c4030107407180000c0c810340d10f90300780e0644210f10a18003460180429000440c00b11030b20311a900010690520454100b002848850020f55444d8922030782d46014a01c2c02c4242e03e84e034040c4200b070100503a040041154001c1c1c034507000c0c2481108800e240c041c0b0303901b900c200c1d0780e403442c030401541b152680b2001100d206 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 566591762 1250 566590512 566590523
    0xa02160f03051e13051207030b0405070503010605100905010f0512040c150c05030301120f02060409051902071212020f0406110f06070813111c02090a0e0705130f020703020a 76
    0x3c8070300300661500c40d44111602c1c07520b8420780c3c0340284014500714908440000c0d0b00303406c4590240c1c403a80e910030901d01c141da060f201c60380200e108005600c1e0034041c0102414098030017051380180c3d0302001e0101c140c3c40c010b40741800b040c01a481f8006100b201a00c22840744000041480e00301401e0150840950340074400709514940c40e80140c05000c0d81d45182c1895120300190700d180c0ca000d1240c2a482c50341725080f43c20455025040780582d92b6031001d07002400c0f140d5030025003400c08410343d0004014190171000c40600610001022800b001102d98480e4180e0400d0390025059209040003442040d4070124481c00200e8046007441e8440500020707102e0800440d040d1080049055507035104c00c9880200003283d28002800000400355144140ca100703102c2c07498203010a2000400c000740411168450700c0218001e0301c254549071009542080c1321840802c040c440389495642c843d801402054000c1c0c0c402a14a10340d10aa9408046981e00c00c0808549401292030025211040c0143c1540c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 566593012 1250 566591762 566591797
    0xf031106071404140402090a080723090402040507021002040f030c050604032109080a06093302090f091602150f27100509010606080903030a02160f0305 67
    0x400d42d01814000d94941407404002d0306042c608a52291080d10001406422031380905c5410119214109079102508414018040d6607040c07810496910749461040c8001d00d0380c012950001381c940c000101d81142d0140d030702140c5076032843c5c4164a006004100010a948009000913002110799400010f8070f100e144080c0171150343e0300c100321881c0038a020103010050b0506141809100102d0388e9440c054071400d0800080b40e41d1940d503810301c070b030103007040e0780c2036481d0341c0c81c4010000c015100c207590081206c0c11445046120241c17140d8040c0004d00e88501380d0f03001510845a94684244c450384645c010300620003440c20500307020346080b0440f03070100944248018106006400114144903030301d4408502840d50360690500f214481c8044503007801d240e0f41c20340c1c030703e40442031241011074801e5a6021440c4c1c00d0810000e400c4078801d5002c041081068014003800140c040100c030b4001203c614050380311041e094038100c600c00b000500410480c1c01e085005d08058000014214800d07a00e406000e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 566594262 1250 566593012 566593021
    0x80d2304090504170309010b0f10020c041104030611090102010b2704140105090703141504320109030e010801051f02010e010207051b0609060f0a0c0f031106 69
    0x2800116a260050205000340000d114a000a92006a1140c052981d4807104081d900c50180c1990054030000110794450701040c4c2d5a08201154015002080c0c44014544440d220000c0d15083c0c01b085036440f80c0e480c0d1900c04500a44070043ea40950707085042000303480410034020980340e200c0090b140c059400c6c0181d02c561132500c003110301083c0040d0b0503102e80c0303070b511071840c201031520061007200e03080482c81d5040d01d07603042440b90a11401e420801400500d042d0304000004059450407482d599000e501c410308410901421b0980007580b04541100070003500d06616500100310310390f041c61f055482d9030044919415040078082a00989412a1041d031000045800b02024061150003910200c4a4036685070418044c00401c2610310000a035034440c281604c1c2aa440b052085e903013607021800c40d184500501040d180e0750703241250001d14003142c41011640703600504000c540000d50116895013030600030060b030345816901ca01c0d02400c4802034034000d8030b00980c5d01801151032041c0400107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 566595512 1250 566594262 566594297
    0xc03030d02031909080f0307051603020a050f0f190f06110a09080a020a14030f1902011205250c05010f0504150624020f12031b160803061801080d 64
    0x680d00c440d0040c01c072501c0c1070186c01d918200c95202800502c20807034200860849800080035181c1841e110790b0181c06c2370300450030b00d24500034142e900d064080d00010440c0e01c4c1301000092035410100100f2014440b1425406c02c035a0266070442c02a0543e030421540c0da00041d60b0200402e40401d494582020054480e2200c9584487c211301c000c2d00300040f400d00348100d11031403250075082d010003070440f180c82c0c1700d00306031b2401c010601c50340c8226012070403049011036070041c0505a00c0749101904100324a804100d0401140d80b4196400403041d20440e0b030381a69225070381510209800400034042c000088200c480103002c1160199180c1e6519900b511300340e034150190404444480701e55013101070a00e03a11140100c2590b035034005611500c60292a013041c00d1004202c00d51443e10507030703100e180c5040410109140701c8810250b91400f004a03010b400f0642805004c3c0580000c0c14035203944da0394001c50100d02c002012a510a00140c000060102c00001c26004110f140c5c1e40300d640d5481002c000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 566596762 1250 566595512 566595521
    0xc0210090812060616050102041d130f08220f06021c03020c010b04090f02010e01080714071401020705010606030e0c09060909030f0c0709060f24020c03030d020319 72
    0x144080c0c0708009281c0c402400e05101604241d00416841c5841d941c04250500303e0040807040320a6500850200b000750341032941c0c0c5800103105080140b8500c1c12003052080002d203036a00400a289510b0f00506100d44e020a4407103400304450300492054200300080c4c0b0f00d02ca035100321035409003d0540400d20030f101082c1e842c4001026940186a42103007a000d501942018542d01102d41d6569941d40307241e80d46010368442103014039520b100d4807030f490000410301a1030f84803090500c0128800c0c002910351002041100700364028450707441e0300441c64004240c200c80b000d00c0c1702c0c6600220721602807040c1944810200c0b40b058404024900d0200c0440d81c56010710000a80d001c004d0b08006245800e10114a60780a80100c040d00d2521400800d43c0070107400880d0300000305e07032001400b801031551510500c4040c11401138526592864100b4445880c4000381500c1200100c0a0300590700358000c01081d0100342e0700a003520348a00104401c10000e401c2141d064500740601001d007a074a461500c01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 566598012 1250 566596762 566596781
    0x1150e090933071d1003091e3306030b07110f0705011119030c0b010603090b15040b090c25020a03030f180f0602060f190b01170a0c0210 60
    0x800c50400e640e090f1050360041d0f005081c041040024000100c46903980002006070150a520002040c00e820304001c605980a0544900050b1540300124041880c510100d10095400c6007a040c1c0c1c5000031299016038400c25440110309410243d01204110103003d94610980c2940d540079801d080a410003981c80410301c0c0c2200c2c40d500041c1c030601c425441a1400202410a603003143c081d04c82c10f080c0105800d50000c0e050300002c3c1c0c403001c1ea10800194852082c0102220300d001d1140c01f6403600d4011483c10090074500b1829100d5041507131710744498100388440c1c40001d20305071712890701c2c2c05582800d6100c40041c001c03418001240c0120311404c010300301c88540d0090644942982540d6040e02c418598013000c0c414410801181c804940c0c80394010360141646044e062001854034901a20744400602901d60780807601c000c1084813410007403441c0000300c1066011604881d001d005039001182c80b8560100d00b0700707a200b04520030015402614001c00c81c0d0703003111002c00c4003080f014201ca66802 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 566599262 1250 566598012 566598103
    0x10219031407061b020609070f1d15042a02010608030307030e030f0a03020a0e04020a1d060c06040807021c0f03050912030c100c090305030301150e0909 67
    0x18285000075030302002401200384604000540701400450800d11515203a4600005078440010040030460610518000340804050918900c0c00e1903c3c1d0a05c4000d0f41c2c0c403221100c3d01c400000740c02107a61207030a26468001520800c5a50399040c010b402c5800034110340f41c803080704610780f07100d2030b441482044101c410080145083d501c400d04c0403400b800800f002d10859103c1030000b6141c001d070103001403442c01c0780c503180140d40c0c0e91402d00181c5400041181309202d18810700c1031083c4c0c0c43d00000500da0990801541524968076603000136441d02800c01000d02c20f22500d01000b08102400004051090013241e40c480d50f80050303080c10f40d060340c12100c000c012101003410040001d00a8010348a04e0f900144001c000b01c11740d0300c03070300d103107400104400344541d100510f0401421007521881c0141e003810301d0107008480c103580b5802d541e84018891280507166007080c0d107030304500c961050844488014100e2210b42000b040a035034900301c01c1840c032004484800306040c0d5540e01c1c030f00b02c095807140d01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 566600512 1250 566599262 566599277
    0x212131b06020c0f01020c1c020907140a030f0618140901020306180915070c2006040608060307051c0302010b010e010c0609020f0310020a091401170a1112040201021903 74
    0x184045643c04200090661045001d034107019521000361208402020410344c002303604a00410135905406803001c0700784031280011490343c81800341113900320002401c003c284900f03094a40c7d0002c0406500c880d0405240c118a007081e81c40b2a040100c1e1019480e00c448042d8076a0b269103801c0780300580347c1c1c41c1c0c0406031013204460409042c1c0019408005001512030803903603807510320111941191000c000030701c149040800c02481200358020300940d407004034070391103101002c074640d40301e2409440180140100010090b80e01007203418003a203400f52aa0301002c0c0100601881c45142c240d00b14055424290f100740c4c55440b45003940c0204074140d403540c403110035944a08005040e1010140c0c2c01034041d200c0c001c0707181c0301041089407a958010005070340e0015410005d2940c0e01c2da800008441d04480c906400d10380c2c1c040302d10492808100c0c0c038031002d41c40381440d0f07400411015410301c0312006c01180d21100070000340c0d800d80c4114000e80a5580010740961499907108000e60001c01241c40b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 566601762 1250 566600512 566600533
    0x140f0901050f091b0d0e160e01171e0c03060c07151a0301050f0a0b06090604061121090a0e09100e010e0114011d07050a050d0212131b0602 61
    0x706029075003048044100d49801c11100c070b14086694171036044a030726203807100c0c820201004100034107442d51000ba00010360b282c0c04c11807060f000000600c50b00344004a0f003e10306580b044280500d00782c006224000a43c440355141c3d0240c1c0300e0b400d11a40754468019140003d61103104581104c41840d8007010781c81241610030104001400302c81000309203100c4034042d03003000da2401d100d030074007483c4150408400780c64001550710075036800c842800e003d110306210320070464031503005440c01d076a214202801da0460419010b4549210100110485800207420111440e044002005180c000751900c003021901d8010307a200e600003c0c0c40604180d07100d081068540700c42e90b8000135100140e4800880c24003203002c01c039800c0d10712944100400580c83c41c0100501d08d00014520050040d00f1041c4001d8a865000909240140041c100a001001980c0c010408071036040b9201c07110b4159003100c2c2030615148140d00c04160f8002250041030302c2d00c45a450008440e0395100b100c1a0b42e000f8000700d8030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 566603012 1250 566601762 566601769
    0x60f08060d0303090204050708010e15130522060504030215090a1407050d300f0c1104050a02031801020f04051504090e0d020607030b011b1b140f0901050f 68
    0x1c19100a404041d910001200140c3e80c90040c40d0203900a80d850100e40c0d410442c803c4901d5401920100e02c3c7c4402c9500c80c81e00392a01c5003160074100b4000000209a910300303515059548068280c070f404012048114004c0006035800a0b003c1da000f40e003207805c022020300f110340d045002030f2140c2d41076030700042c4030000095040b8000e04560701044191081c1d10ba480c00403540c80e0114450840d05100e84072907401c501c04040c48045140d00b40e00d4a10140c0c2d024250b0b01414030031885020740f041181a40c1a4014000c04242180c00010054400c100d0341c41c14001c0b080003034200f038038429000c0116024018012405000340c0b59440c0d414040c051506141004014800c1c2e034008616826110070f01c0000b400300e0780c46c86030260240020300030303113600c04c803000c0000e007025801400e140605180c2400c03011281d900604000f8080c000105049541540e818100c00c1401042c4440000b001d5003c40411692a0000c1803d0848000e55198040c02c0e0320340100f00c46103109006541d00000f08102c048901d16 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 566604262 1250 566603012 566603029
    0x10e0a060e0115030204150504020a0909051b040e090f030a0305090f0619020a0c0804030c050312040803030112022d0a05060f0a080c070506010e0103110f01020a02100e1207050901060f0806 83
    0x800300c180b00d030003150b548c00205050307130041d00080020400d400c0c0200030018450150039400900c22841d00000749000c42c0c80e4609000300d0181441602e00c0700d0004600c0728040060554580c007140440341c85442c0020002d01801d8100d419001c10700038820010484900000c0301409001145040a080c01c8410302090003074114440038410404442c52040100340110000d101460240051029142c284000c1c5854030300201b00040c403d1000700010040c03c0030100aa078151892407410800341d154500008a190504281000003c4018503201094a84102140c2c0e043c1c141030700d110703050740e6540e420072100b40218415100c43c1070b0100214140c6c60310440005a0040207030500500346801e0340c540c3c0380340040c242c220f180000d0800d4014024080d43d5000003c450504840d100880442000001e40b04c04c0200e400038080c0c035140029074041400f802110001030401791205507003165241c1c1455035a211481030074066407a510010a24510444c6c4640d84904551140040798581d14107201400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 566605512 1250 566604262 566604281
    0x100209030a0b1f0b070c23060c07090e0f0a0b0919030806010e120a0219050613051009030203060f04050319080601120218090c0705010e0a060e0115030204 68
    0x1800740000e5040050b100740e280314020410f2610200105411038510000d0280f0f540203906001002e01141001600802262094034084071003052101903003c0460640c54200c883c40d0f03442880410a1040d400c4000750038403c5401c1100140280e4800740816a200c41e00b43c0e1591ba034a821100815010502c102d0380325400402c000100d900111451440f120f540e1030b01d880440010300c801c001d1041a6900c4408494038400803250b11901c061308410446d561f1f1150300c0001d02600d11382e0300102419035441c2c240f00041c140504415a205211286451000710901946105000807100c1c0d0b01d6051140c141d036010b40b80d01400800c1640c5170082054100300c001007048529210811035101c00840c50079110030380002c43d4584040f641004030002d80181d0f80952104038803841440041c0403031841c8207284d00035040c15211a032460f00c1c0c83e0070000061140000240066003402d804203001303a00055941d4645024900030040507010b6030310350b8240c4001c0004c0c00301400d00d00e41c0520262501d5800131186 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 566606762 1250 566605512 566605519
    0x3051e04050c091608090c01090303030b0f060a0201020406081e04031b1b031401050417091201111215150d02090a0b030a3b0304030b1f06020604020102100209 70
    0x118060800066800d0710450f030410b0529960004c1203100d9800c07442068225040001624a061160b00000c140070030354030025041603103504141a45845101c00c1c4500c071100a0001d40e0394076904080a4040c0d84503114150026480c4c100281180121102e0050568400204086030792100e8400b114442070fa106045071101011850000080098a40082100328070103242e4a00b8510f0404401540342145200003590500c800c110006242c0c20b01c0c0d198010b1014156500c1d820302e0000b0546a20020f1002c3c944c41d845e01d0754115030b0032606000740c922407010034800b40d15603507003e5090914035005d820f1650096148a84d40c0d90000450000c1d0a404003810001070070210004000741c0030f10210352090803840c0001041c007081c110207001d205600201d10100254a10000d01d011a030940c90284064000c500340c90701f50303100682801220011600001c0942e01070412244441d0391420b4441e25020388550401c0019103140040768491007140c05802800816502c80c0d004000f946c4180e0065a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 566608012 1250 566606762 566606773
    0x50d030e01170f01030605010503060411040c0e090c180111030307030906090605040f0302060606070b04080d060f0f0602070e0903032a0d05060907020c0a0314011512050d03051e0405 80
    0xb032018508429031281e02aa504602e4551460400b081120b4041c0c01450194100100700008100310111030664001c05980c00104201524803c41d58a540701c9550355200a407042400001003040300030305401481110582407260707021005481c5a95214007022980d00305000090754240a54014000740380a80d05c0072540c00700f695100303000c0366011075049603014096035040c4203040e410002103a020300c003541e219191640a44400f1110b240c000c2c0010248180051300728650303002c0c1d40202d8001c040c0e0090f00e81500e501c030b024044405800380a040018450306e035002030140040342d038090044004c14069444c0d52664440c0c203230340c4e04001920b4a00d20f0101d03070782001c10900340001820034040030345001803103003404410054055400740c052011540035010300c0c00b140c0e440d6004001140d40c0403040c200c840c01c1c450200341c050a01365131100c1c0414885407000070380405240107502c0d4140300d00265260388070720000c00d404442058801482c5607a035100303100c10b08290142030740e802500803001c450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 566609262 1250 566608012 566608037
    0x30c0e0a0f0216110901052b020d0f1e0b07081e1f0e27010f1a0111011109100309050a0809030d020a030e0112090b040507140109050d030e01 62
    0x20243c0c1c0c003880c10381004880d91a500e80030b10000381ca000f00f03043c41c210f5100800354506400030b2075804204a1210361884012030b0340d0195a0740d40c60721400180e01400d40d40440303410342000446103c1113007003950200155030810805003c2000c1c1c0144982d482809590700b6140c1900072240b1100c000c000001902403040780703006407408035100b5031041880032081d0303c503034509481c2c000c0e259840364404408440494244441c1210151120311031030741c401d01c1d8200001c0d440c5001ca0140000326020121180740018020301d1204509882e10000381c2a2183c02003050701035080c50032110700030701290106100340004c0c0d0a9180510689402034850f10300400c0707124a03911f80a05025000b80101c1d8000750014a055242c2018810300c910405180054822a05c00c1c0e20040c00814a10981504200d046036184440300300c10350150102d1034101e4010081c0340303000e02c1c100f652203007540160302c0110b480c08039891030756100e06150001d8850140801210b10002d503815586a10702d00b241c103060002032241007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 566610512 1250 566609262 566609291
    0x507031413030b06040e0f030702040507050d09080a080f15131d01050603250905310c0f0303050d020a1e02010204051c1109040501110a05070605070207030c0e0a 71
    0x88007441c000c002d83c40807814040700308411901c071000711900c282c001d401a0012a0400b1043d2076000780c0654001c0703195030700c00c201180c051240d0b1180120b00c600e410001d9080c04078401c0542001304094403031a02036201c03100c12160f015012287e4120000f841c8140c2031712030a00342c50814150281840200703880035195035000070382c201484060500ea5662081110500e001c010131440300d140102c071100c60b00710b0840c00d050030703000a003d071600403501d4202003840581500002020b0440c90601c4044480c007403410902c40904298003550320886c06800441d002c03403510490401ca83d8140c0b24186481025010305020350861584a014440201000c0e2001605414048030030342ea40d03800169600d051a00308001c00440284aa15100b4044020800180f4190b06501e04400c11221a0389950f01e528040703015119281103081c4010020a41d00b201541010103080d996200d01414843c981d942441240e441c15180b00c00707041d00d0b03c050b5042050300708071001d9640040148401040001280460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 566611762 1250 566610512 566610547
    0xd02070506040c0509010e0705090307050d0503030601140a09090f0603050d021c030606050304021e031e07092a020c0316180b030d03270501050f0a050705070314 71
    0x949503500501c0820041010201001000d000e00b00d03561300295043c0004100081c50017803250061120004041104e90713420481c02004010080c41c1c42d5004556140042c1c8903041079481a0201e004540c0c454000000c441c1610344021301079481004491402e035041e405010b5204019001d141d84040c0840400c80a0100d11000111600101040e0300c0b070a0020100c40a1443c0c00340c101403a000050003199401421290002d404079042c126072071106010f011307140d0303912040c6a810302c5a00c56803101842403000155507010501c0595420b5952145400151607084606041d000345041388141c2c000c590640304c81c41032210744112401141c207000401d16114140640010108407564100300f01c0d02c550b895611000d4100c2c0382404003015941c040707540c9100d0038425405142e15100b00803015103e4220407169000580382c05c01441655043c0b99008100c1903800b03481c07540c1000c00180c2144010300505003e00e01687c2d9940c039010564404039400004003c0c0f051240d2410040c640c03210118604 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 566613012 1250 566611762 566611777
    0xe0106030305091c0f050a1514070e040f062403060b0702010c050a08030103081305120c01080a18081e0a091e0510171e0a150f0b03041e1211030d02 65
    0xc1910282e01d040291801008d44094050981403e1110410003251075403070b500308180b0b0801103042d00d005c0300017501800d41a02e40308051407400078002101409003001d030401c030845406400308084a20021003e40b10140036181c1507200402c103c100651054185141f914015029103115244665400a05070300c04c6e8029035050401281c00c0d20b1001d92080e070a0000c003c202d92080d40aa2885d036100e440791440301c100c606204403a00000d002004036040a121100c50b140400c41d1400c840ca4100c96503001840c07070001010022001c3c407403100160003261920001d5481c0d07203400e549002c0e180d43c00503030892a1515042099080054140c541050089110b14280c0750000000003203205460f4402008050742075586204880a25180f040041e058002c00c2c0031a01084000c48014451030018071588010814520346400062a0141030701843c0101d20404030f10b401203e080211210341d00c02070300d019012401c0c490320100d10a015045a00c0c007008843c06580c10452980c5020040b030f0084c49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 566614262 1250 566613012 566613023
    0x30b01030b0f130b04020f01031808031605131205010b0d03120c020d2a02060301030b070905100518040902040e0106050a050607030206130809031605040e0106030305091c0f 76
    0x2080c01100750b40b40c1c94040d80405403141d11060f03004184c03260240c1d4076015101a00400e4088442452030b40300b50020307100520000e00c40c1401c640d0307520b80301180b03610458660400c002d1621110310707154850000c072403c48044001d0700911b01d0401264840f5221030075070448582d075032032410204980360241140f0344c1a0003511903000843c00180c05409445001c4490400c40d00144003845a040d00710103424100c10013517401d0007005105194086034107a08400c060742c0014040000010400c1c8462898410038980d80c030400415941d1060015042d0741c1f03880e510118109006c10079032004450320410162100520119102c1020f40200d4101c9100d1541d9003202d0351114400e10003410501e0000300140016650940361404030b4170003c0d01d40d44050950845000001d50321028007411030246c032881d10000b403d48080d50841441c1b10800c13a0785220f014011410103d405000700c5040c0304440403660503403030391840d1444643c108021400856002c1c0301007140c100c1c0c001d010503240901c00210b1407180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 566615512 1250 566614262 566614283
    0x60a02071806210317010b0f07150608030a020d0c020607080307050d113001092f0a03110a17180307080c060c040b0405040b0f03030307231201140a030b0103 69
    0x2400c009020080d43c000c900c090702c0751300340108040d0600a04a48260b0814030f00741d501c13086039241081d48400c55410b02b920b401e08120300032540040110040001072a15000c031b8030b1404802d881074481000e24080030b940701d1070170f110310000701d000c0304c00035944000c05142191a141c500104401242c411207216030b05400e012420840300821103c14406a540001004130440c030a28400f40381d22034140903011096442d029500c1000c803c5145040d0010704241403281034004c0c0181091241d04091841c1c000681004407031519542c10200300c034800400307a82d03212072640c050161307065610809020b0b201c200e05a109031f001407100520180800c18414002690b4480400e42501d141c010094082c81d0080d10401c0108400341401c000c0354202d80301590042a0003941c10000b600f81c2d80003c030920380601000081000065000c940c3c81e06800800802e01c41701811801340317540d00c1c0607030200344194200c2280148103001010340c1c800e081703000040036030400c2d1b0784903a5403d40701c000a86c82155a440304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 566616762 1250 566615512 566615579
    0x10c080402030d03110d090203010b06070602090a0b070f0b1f0603060e0106030608030a0e0303040906030b0a0c211e020708040608011e030201080a060302040c0c060b060a02071806 79
    0x80c07000c0201450546424030122417074001d00c0810384528414030240c6651845d5180c1152000c3d00300c11b4440800600c07039525908a030400b000030703511007551544185e807101d4000c07914421141c02ea880c800d8001c082100f50000c0b40c3d56095103000050001c40a50406003c10b01c3c040c0d00b0103144401400b01583c020901c2880c203800f0145805e01a00194180b504101c4280316a03800001030301d900018034541610004044008a41584910f4101419150425001000348012041c060f8050f89001c1020403844000410868040800c0040c42040c0d0704040e17000a080c02c0c00341c100100e0100817041c0031115102c4201507078101ea008103800c58107410081010004980c002820310b00500c2c2d204803000160509440020714031106000003410300015801103030f1018080d87c05800078507400740c401c00000721404800341400800c010125a1507060550040c0c5c207081c0041035038500a4250010b18400d4104044540201380c0c0101c804051541c40c40000b800c0303042100301d0030107508001c0400c00c16104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 566618012 1250 566616762 566616769
    0x6030c03070909031e0824030d030c021522050309041802030706050306030d120f0c180b13060305060619090609050603070e010513030c080c190b0301030609020a030203010c080402 79
    0x54000000641100c00c4040a0301d40d8006c4d40340f0341d20500c5122a050b440068100c09030303d800c100d00c549509803081043d011103198050b401150120342079000c41d080b6001030303210044181c1341169070752034007180180480140c00381c443e84200306038460b43c256402c0c8203041c00880d0440e005000d0740183c03007040b05001d0f0250700f03003030051501404152410070320398038002c0080380c0d4404c00f400c600b0081201400031304103040440d6020b206410041d8005100202c007000d00242520001e10018880036802d100002e49058510221086e06020b0060281258a031010503070040c080244401d0f0410000c000c03c8400382e80003005450840c0486c0c80c0c46840e43e0070308100902c5414945c005c01d009103810000d00400320307040703a00c2c1501e5080034646565180ea840704143d0100f800c0c0d900003070404089850100b07099201003240b01140d80180c408407011070418050b00d100c1c00702440b803200561400c000600104034241c000032042400600b07103840840c0e80b540400c0c21900522800ba0000d002031007403004525 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 566619262 1250 566618012 566618027
    0xf0807120503090c0603071e0305010915050114030403090e01120303110c100b060912012702060d020703090b0309060a24140411280507080405060306030c0307090903 73
    0x1000d071800c9400d5160100c40d180e903403c0d0786400c03613105620120006100c144581881c0c0d0b1043c80543e0307403a140ca41010000381c09800c00b03005e20181c0600700900c1c1050690380d41e04010459405a5030344298180c4018109240d5001030000e4040050440e00403840071203a07803182d070007400c40441202c1170484c18180201141c20390380044e4a00d60f401c000c45040b103480001c8041010316000b10000b04c50519400141541c8240c03651203802c0100100403000311f40e0194040d01e00a40301c441c5000350004400d01d990b00015108500a6005800380041505a59164080c1640620038100081042e490703002c24103c940003160700020541c00402001110f50160040c80001d402e1000f0004401c5603280154050207200e00a80e200c841442d02e48400035a00ca402c2000300ca22a030a280350349840142481d0040c02001104503a80345400003054501e078271034402c0700c00710354100070f05c642402d0030f00040095030b6001510055040c440c90301c0280d0140d809003e0b5400424900c05d0001701805589406000b44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 566620512 1250 566619262 566619293
    0x6070318060f08040b0601020f0d0201060518010b0f0c0109020604030b160e100f022503050708070b030109090501020705010f0b190b0901050901301a1005160f0807 72
    0xc644009480c000c01c3d00503c12513001980b103100a040c079a29400100d25006200964481900c076032401c03485001c0d010750125050701c4050710410701198800c06461302c14a4207110b038406600c42000328180610001020700044500c00f0300118100303000d500040d01340c1d0041d4005460814a94042c0411400c0140f040c501481050421072040400399000030788100c501c0648509020b001114485014820706c9281e03018200d296a8003020080034022440c00241c0c4e000444051207240341c04078100341300050910460380b104e145145107030300384a0041e005d400c020300211119034003481503c0000e40c0a00074458001e00044000520740100310401949a02000d0095150041c00d0000d121074900c00c5c0480715094400c0c200700f80d46010620041300c00864080418001680c2540e15440b40c0d4210b03031001055950f40e003010b014420110300c141f002134220316940e50303101c048144d840070b455000e03801400b031600071030a60850300231003a110000102d0903480201d4681100084d440100800103000c0041c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 566621762 1250 566620512 566620517
    0x50f0108010510030605091617070e090a030c0807050a060e0c060a0c0b0601170a020706050a0219120e030c071a03011a220e090106052403090c0607031806 68
    0x6034103080c1c0403c40814168003000e40000c0d1181c1c00603014400810040400b04420304240101c2941c034100902010b400c00080e03285800f8a00e000594205805030f1940503a5a5001500301003d05640c00e803003024582c2801c852511060040402040c400d020080109010708400316406146100032400d02c2c0c07101807042d11032681840a2465154801d05003403d071544401e4600c51501d4490041e034038400142c0f940c01a40c0c0c460420081502e1645d005040d44501c1407109014548030300a03150268020b2010b602407580000742c945058901c0307245070910740082c441d0006544881c80c921b8a0469001c0c0a440441391300c80c0804009003000c1c11901592000410021804c2d94100010fa40380399205ea440341c07000180c00308000390500079000300d04104500a805180700503503919140c080383c51046409140a510306180014541044040c1a40901410000da4111103682c000c844040d000580346c0c1d80380d0311956643e041183c49070307001420018002d442c0e0001d038041d0003103507050243c1150007141c02c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 566623012 1250 566621762 566621771
    0x142803290f090d1101090c0b07031701030206030a05071103040f05032a10092103080a050402010813080706060f150906020606060d0f110d11040806060d051c03050f010801 75
    0x1a94070300032500f0010340c50345107441e03d03100301802e1030507005d01207081000c0c100f0910a400043c468010030001c007030203803098541a000c0b8001401c0c145010400344000380d04690200300152000c0440d5005a42c440c03190f040c5182d50341c0c55408403e180d900645c00521503c05812002e02c1140f804020104812083c102c0301002c111081c030340039402220340f0b00741c80c0c09482d901100c0c0d0341d618001c0c075a180c0030b0940c2c0400ea070401c40c0b0491840312402d2001c502580400c0e1030401117016514a4000d451040d501078581c503070103841d03c008401070115101403d88060105101348800076106009a10013040b440d1403440400f170500d01554070007150b101c0f500081c01081c480401c03169801003215a80060200d91103900c840b41c15510a001d802031441c8902d0a51900d1940d02503280700c6405030002002840003008040d1054051306020f10130b6004808507035103c0c400085441c601a0340d00c017001c920440640c1e1a0b000640c08901c5220300ac3c2d80c5444c0802e481e0000c200c2e070220455980f90040801034000d01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 566624262 1250 566623012 566623021
    0xc0705040b100e010908030c0607030e0f1b0d060e0703050c0108091f09240614060301050f0a08060703051e16120e1b0901142803290f 59
    0x5031401d4a2614030010b12901011000f12a8002c0714000000c050701c2068030383e24402043c440b070b141da104450031030110b441c228001501c5c1d040050718601c0d8007415801410b0895009a480601d4816940c88540c404000d205003c000b3300c0c0742c025511640303c140002d044d12400c61070001c0c203140c80300da103040c1003029400c100711110034006030013140850310035205501032018000c203a0191262040c0a09002c03109074101280340c0c1c40c00103105403010501c20400815032200300b000d9002c03080031015076010205200501c0680340c400d010f0b00204100070b04640010303582e880740d41d0401400300c5006000c26955010400c02c0c83c01d014035010300030018000b00704a444c1c1761040414030010342407080200007028a0440014890758410400c1600106c105d0340461061080b202e0f03a480a00319580c080e8611400001302d8480445000100c82d000074612801c42901008041c0542c4110180d1811445003200c00000700b5034210705110000a400d2064030184d403002240d5402c140090040700b60b5009040030007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 566625512 1250 566624262 566624269
    0x100b0a030b0606070803070e010e04050c0d0506061b0304061409010c03030f06170c0411090616210c0614060637020a0b0c04060c03050705031606020c0705040b 70
    0x606403640059428540e48482c0b001c900c090240708402014120b0000500141c140c01120b10659202c0980e0348080c080156402e0200755030041d140001c49000500080840000300d0304038650186029002a007090041440035403040c1c0e2400500351180c05c0083c082c42002c5e8010484500c40007414481c41c84d000310040028203201e00d1900c06820190f640e80200320016258101400402e04040003101590040c0350040d00e540e00d03138801c4c81c4241d00d0940c0000d41c0e00620343c15076100301e800800b210b0511740104c6002c104400401c2044403401c120003442c078090884c902c0c004a8007078807513856654080003032a04000711040b5a079a4031071403148108109044d80c83c00c040360340141524592142200c0506440300800c54880a8204243c0d0009034050388107900051090301d80c4c1c041c00f50b1040b1511107c004190030b01c141d02601c00080c00f6405001c020a000344014006c5a200302d089a1810480080040c1d85107051507017112100d40000340b10101020412500b00680f00807101080f0125810f07001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 566626762 1250 566625512 566625529
    0x6150f080a0504020d0204090b06180105090105060a1205070201050610230f0d020706020703020d0815370302041a0f0d0c080a06090201091406030a0e030906130305100b 74
    0x140380202c0d1107030700040c00c640328068100d040396070141c000d01c552240c03847c05204584c000c84495018040a01d1140c212400031000141254000390034503e4076400c10080c40559442405180140000004c2c5002c40784598400c9510901c45030b0700000b01303820100108150110060400e00801448540c4200c0c00302d20740391484441041c2405007030740c800208989058600071180c100509505c00f050700350521880e5001086198840d070f081d1890000c2221094511303510940e0145901c90311031389010202e04000103401071603020307040e8035049032a04d158448005060441d100315140382d51081081182824010200c02010f00412100c40c41d00c040d011810050350068144d11034401300c0005001c0c4062006010301424000d81039800741c881c107040074400f8001241b0b0890029411781c134001098a10a006401000d800903c0384d80395854907041080901000702c0664201d0200300300883c1241d0b40d150043c04a00c9175000181d003042c2c55802d04a007490250045850000c0c107050624100d9550840c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 566628012 1250 566626762 566626771
    0x1c0210090302160305150606030f010b030a201e0a020a0807021c08070b07050307050f09042a110724090306060e0f090a03080a110d050a06150f08 64
    0x10001800810350400300c0c80e080c02d455226505264086000c01486004035030312031651401c00c0c000003983c607002c0c1403083c6d03484100c0700d2240b52602b0400510030040000700840d00001140004031380c0341d2250340380c403da801170700d2108140e0b241c00044403102ca0030001d0741520b00c22408100c1d28200024603070041d4a5201c1003d00074061000060118115a522030f240c0125030b5841e200d9000d002d1583c0f4120500c1d910405007555034143c2200090440d911620840744610440c0d92110b08100540c0c2e00552aa00484e4046a10a45800b03880f030703105100b100281c50385c240091800d45600c0d08c25201030040c6484645507003154114072801d10031800380b291410b0580703c0d1000c1700b0388103503101401114641c8070303600010045414500002070300400300104070f00030400d981c51242244c0b0703000d20040d644c01004c0e01c0100031591050005a070103506900c44983d0340801c445441c40e00e04a4500c000c1103076012900304034216034652042c80601000c04400708040443d040c4001c5801c80c282010b06a28001032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 566629262 1250 566628012 566628043
    0x2e06241e120912030221060a0302090a0e06090c0109091401120318181a0117090304051201050405010c0809120d09080a030506040b0604181a0306090c031c02 69
    0x641d0100d00112540c001002c0903040a1518a003c040c0c0a000700039510004c3c41600c5e403611038184070f45039528480084e005201c0201482d102c030740740d6400e02086240081038a00101d540ea0580c00c00c40906021a501c03800c83c440c082c0c03508003014400034240c00b00d144c20022090b481c1c400014410604012058152034243d442440c043d142c42c03404940c00400c18500710200060010001019000f00e0b61242124180300c1c0d0612445c40010064006c440c80000001e001482407132881d0041c0351114100c1d500802007509032481c2c542c8610201e0070f9898a50110461070303640e9010003040c02001e205601c074424842c90041c116080030f1111a0b61100c0e400802490043e000800c40700c094582c0e0b0000401c02e0380010096100d030318400d0701800a02c001c40b40710f03002d20705100790314049240490446059a1450311110200c84501e00c0c01001000d0140c0d0709022840c1c503420712800c6130ba08111040c4a40c010a0042c80c044104206160900780001c50040031180d0810600400b203802049050301e40641c003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 566630512 1250 566629262 566629277
    0xc0a080a03091e1e05090106030b01020318010e0307180c03090201020a030f20010e010c050a0207140d0f050f100507090510020a0611041a0403052e06241e 68
    0x40c107124180041d1a0b100b00d44407410201e103540f01e800c0c92030390071048401c12206d405180e81e031114207a05803490680710b5801600b003003001c1d4841c0301e035080350004600c0e0185000840d0850f1400031074584807180e0480340a4001d281e8180140784400e002c2c07984404801e1505004521150380041c2d5181d096040c01000c0c03001c8510b1000e1190f02c035000700e01c954143e102141c42c400c0d842c00d0b440360003415600680201c0e9424040c00d00c0d1510b01a1044802c5455243c2c01002d9403898003d60501d00c00c042e18605500c180b400c904000400c010000040d01540258050a00d0740d048201c02d40c50301003a10341d80001603061804011041c1c3c0c0010000d02140c0e015a0f4114002200b030b9412802c0041840780204010300d0400400000c054050250041e244401950f40004211130301c00c55441c09240320080c465440303100c080a10240c0700e10641a80c0d94211003217440f40b442c5182010a03070325587c010b0104140026065920040d00204092040740c2700d00744801e0b07802804542140f4060401e003054180700e01d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 566631762 1250 566630512 566630549
    0xf0d0504031709090103031d01092103110d030605091005010507150207050a0c0504060506030c0f092e080f090703061109060d06062616110a03020c0a080a0309 70
    0x2e5900300c03200039500030040c2805603100d103000740c00301070383c00641e200c000d900b80280c1c8969401001d10000fa00d424024124045600d1000684004401d15003181003003540000c030008070f0002c100451501880da18040340040c100814000b0307812006100d000000107003101008203036000001c07544410303004011081801c595917000c0001e48142107000301280719042800c400d114281d24034509507482140d05001e09580c6004000d0240001c0d10030311400901000081c1304074107a00001c0c0781144c0050268070002c0404c0002882d03111940d00141d00d0184644030080c04c1542c05400b465219611038511820741c02c083c1c0c1320950340c0c04240001031180c0d42d41c0d1003500d46e881160041d01c1e01d41034006d2603590b644200040c4040603180f41d2141002140c4000c14040c0c0300e181070014070103031070a07244803c030644e60342159000154880102a90030320801c01c00c1140084001d1140625441c0250001e000320320070101031100c1d8000c2944800d00e2a0011810340700002c1d400b141c103070b00329041c2c400c4e4147d4a502 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 566633012 1250 566631762 566631803
    0xf030809190303020a210f0b0402040b0d09170a050a020d0c110904030203040b210604090b070f0905060403031d122a0303040f03050c040c0905010809071a0c0f0d050403 74
    0x404c802c4401b045000a0800620241543c1181c2c0762120100400d0201140c5002408203074000d0740112903103048140401012440d841d8000b064a6000e00f100803000660403100e550701d507100c1d0104e100028000034281046035010007920410080501e407040781c4441075101c1c0300245417100c1c1980e10a802080100d41414420002c0c2d401400104ea02542c1c0c4200c5401c00040d42c0c0120b1100c1c4c0050314050001540c02c1c40d0a1092034102c43d0000e031500d4080d5610b200450381122090007040034015041c00c0411584c4a00010340301941c440d40b912000e801800d8082203906958108240c4507a03280031103c04d181c1070110301d501c41c4036200181c040309294281c4282c50242e05c809007280d01488041000035100001480d000e00f1680140142c07000e1010201c1440140d070060164400400c00d8060200700340d504c200500c90b807110030f01003600c400325255810345803c0118880000303803414001c10f0a1440c00002d114045403002c020700103008100c03c4010290890081b0710015042c02d000c10f000228000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 566634262 1250 566633012 566633027
    0x717030c0736060906080309030708070e01050d060f0908042105070b0d063803010e0f130c1e120b0c09180a06140306060109260105040f030809190303020a 68
    0x210101042c0b060704c1d100d03814941d1f81e0b08030301d100078071a2141690003d00c2c1c00010400c14107584e5182907000e2a68244414000c0e6400c00040865003e541c0c0d401d10048046240304403805540301d44041c9640b6454a004103500c4480d9681c501d030010804001200003a9000440501310740000c652642c8413030304091b41d000241940c0e480305032182e01030000164400f40f0003070682d5400c600c1042000c1f041510000030b542500003402440701468108001c5045505400f00726684805065032842079000250f0318540d01c05025030280500c0940d6076007929615861300415000f40c8440900d0020701010354603040b82c0d0301400385c801b1201000c0000c555030719440d40f448505902c00310500e0700c1c8560406903070500c000c111a20440c1e82c0a860034488180301d290216a41e4020001607461404182c180400b02c10340c003d16008070100703031010080cc01050b5800b030041c02e224500409013074100e0045414054000e52004029002a4205111031254580c5074181d05c640c260b014a40180c03500350741101a50300c2e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 566635512 1250 566634262 566634269
    0x60e030a0c023303040b0f010602030702040f0237020313050904031103070507140406142803060605120d0f080c0d060e06011107050105090609030717030c073606 71
    0x102201180c84400f04a42d00a501442c0724054001d12503a810500100441080c060030005030001c0003e0130161415400071f404902c040e042c01480c000c1403400c800440703005482034005812041040390000d2103031860040c178035a414009035241001020b0881c9000e40c1c98020076119200200228081c14401c024550800c40340c602220340d148000d040240c1d885096118840b040f03502d013242500c4500b040d014030812140140c802e0b4442000020802401009942c0407124500501d159505100c00c0c8109c00002140580000110f0b14140024003041c1866081510800e40c0041c0172041c0d1541c1c41510b042e0301644929065503071782c030f8980c4016054801c02c11003804907810410f000c58000201d0b8443c83c01110240c8498220303411182c54961076001e141b11b09404110103000003419810441c0050550510043c10740d40c00701d032902c0c000c045124104494003426403010410701c3c0c1c0e4074010000c0724081e10400582404070204000424109500200d2108280000141440100d0b420303801c8100603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 566636762 1250 566635512 566635579
    0x11090405090a1e110a0b0318010f020f04090605040e0616050d050f01170d020c04181b1703031005060901020c030106080f070b03010e01090e03040b030a050103060e030a0c02 76
    0xf000407180b1605100b840c0c00181d888480300000d0803003501e00181440c00311b8450001960840d640c0040300705000c2e410200c0c84040c0c0d500c50310040969081c1d80f00801140c0d0315541315503221800e0000910840321203800c00c50046107010440705903c0d0b800a15141e12111000340301010101e80e05c0c04880345e0141c1100c1151441c104020b00c581e846070244454141c40c03501c207201500b03c4601200076500c03080840a0030160f0007000803610582020381110303060082c103103e1640409442e40d1010b00100240c125000003c40300c01050006108001c100b450085000c001107056040ca28801d2451880e035126081c801c1100048004c0a40d00a0041503c4820001e008100366079554444a4a8508403400152940a550004200ca400400540341038400c02200381400d40c2c20704180700000c240850700c610940c03005002c00611741d40380c240254480c04000e800031807039515601e040415a00400110b4080d50010301000256036402042a10034680443d4040b042d205403802400d035812600002c1800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 566638012 1250 566636762 566636783
    0x20a0902040801091104021801030b0a030b04060b010f020a11010503150418050607030603050a0f14030309030904060605030601020613020f1003090212060112080f0f04150e0411090405090a 83
    0x5101c02e041d400f07807001a024000f0f401e1003000107001c1104030711805003104d1200c01d214506444a510075441502d26441c082c0c400043c0075203035181c001f1110720032201240c910b901c8820031a100d507407001c20802c000303903103000a00403600c1070303907a1407418007805907810304016002c00040c400c082100d103540154140136108009185150040884003403180c802500d09100301c001258600b480b0f4400d000c12a5003107405003807468000d560b64070040c90030500650304c0c08a00207120011000c2400254014902d0310001c0d030342c031600b142c103000590350390f5404203040c80800c0c01001090791b0046011980130307001d1201c0003850b29030b910000301c2c2028812411034001403004814400380e03030036612040d002d60085810444600750100400d54814090280d4840701c0070403000600003d41d01009820607100e80d9200c00e042000741c022010044d041030307100c0502505450100d590880d0841000c00640f401610b045c084030f02da11400c540144141034000f40035542c0c030b00024020307060500c10001d810364040604103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 566639262 1250 566638012 566638019
    0x9110f04120209150a0e13020301061d1f05040207050f0610030c170d080711010c09061722030905060f03040203070e040b06011d0d03020d11010204050a050d020a090204 74
    0x980840714100d00590740c540110780c0500b08211100042c1d40c00070181018641488455030240344064000507042d411990b0030001680d0038050714010308900000369008078941380340c1c603104502c0604402c2003000c0ea03d107004038081c8890f0909041c0c0704161005642e5201074a4103038070340212075060500754000d01e41400101000c6078141022a80030b091940516030b120b000a03400c2149182c1080c0195000d0741c51810028000e03840300f0307031040b410700305407002900c44620b860a4a10790018400002d07090702c1e0921030190012245a001c10090104c172145250582e440c104a0351554085c000b2039101d903910300f04240c498540203015041c00b400c961307100ca00c03a40c2030003010303081a00d0803446402004000300d40221100301041c82150442038084054452600544041015001c060000e00642441c00c090f40c80304d490711281c05110fa4010a07103194100c1c0000d01140030801400ca099004000c104041c1e555185000151181254501c104900b60b07c000342400e221035212164442c000706000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 566640512 1250 566639262 566639279
    0x111020030910090803090918030c07210f1106040330020d0804030e040b090f040615060915110a03020307030e0402030f0a09060e10020403111909110f04 67
    0x18040828180d48048248107000400da0f0b07100098058840e1541c01031010410919200300650b4100500d0214026403889803810b0380e003141d00801d807041259005d0501003100d200420307203880044065250003100c3c50308541d61040052202ca030701506000180d40f1000c07840c3e41c0c503030803580110707800014078154040c901402d87d0080d044180f005514040c0c040010882800491029510f000d1940e07204002d9540340c2d816500404480d880c1d5400503583c01e850086a160020308900510300d0210030b030114641441c0c034501740c8a07003425007031403465180410440d044d0040614003c0c0d601100c52a10a54880c1390111101c3c01d20400c41d403c01d200d220b03c03a0060603008001000e50038000d59501c40441030750b1080c00141c3c401a01c50041d8400c407039000981008095003c940c150f80302e180c000c02c842101802d294500352400c9094006c041e1700240400401424210078659904244d03181340081e040020310745410003952080c00c80164840100d0b240c04400d035000c88421130541160a82c9494031080b03113 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 566641762 1250 566640512 566640517
    0x6090409060e100c050307110c060a031410050d03030b120607050406020706300e01050a15092304050109020307090501090525050705010f0608010506010f030911102003 74
    0x3442d005004680340112240a28040c00c0c5115007140c0b205403440c3c460b95412650800300610f411000e000b0344141d40280e41e9444001c00f03000105940c0420399190140d0300d2080c861014266108884e010f10041000e034a414210511140e01400c000424480131404a521507104403c4003d484c0a81404c000b070268200c8003030001d590302036080301c04a94469005540c034071078440e0a844940001e81c400ca00c0003130708400c4271603040d903001c00204040480c01036590944106407a0025000d8503011900c0400351605006002000040340500c102ca1200200e100000341d4a1100a010000c0100081c01e02509400c03a650031a0b0207402c440c032050341d03448104000c100a001e0300840381d0034040407030103502014040400350186c1d040c440c1c07003244040c0d0081eaa2907009642c1141c295485141c00c40c40e001561040d00018600c10380045050329091000400703088641d00c181050607d0142800c020a444040c0304040036010b03950141110007810701921f090b940381102c0c0303003c890f001c0074002265401002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 566643012 1250 566641762 566641781
    0x706020102041d060102060c0d091b090b04050c0301090506060c0303070e010e03010905120a14040308190206070c1112010f0c02010e030901080412030b031902010906030608030a0e0609040906 84
    0x3c40b902d000a41445600f400c1019542c40340181d00200100710b030130292400829844005460000d0184c182f50785400c100d0003803c542c2007100c0c0c0884010419002103010780404c5480c101c030308006030f1400440b807001030302041c0100c0324215a100b0005020f03454240c00c0392041540c42048917103030314040300c00400c016058110540020110059480942414014669840e5103d005440f86030b2011020b0011600800d41e03244c1008840742c003603181001e510740103002642c0100f0071195514141882e661100070380324050340466010804020b08154080745d01d687c0e0740c1d0300c07200c1c21403902c29040028003251104824441c95510f04074180d07003000700e16404103c0e880c2d0306400a000c0d14690b42c802c07503140c1c0503c0c080b05020881c0d0300b000a00094030f00c203030914000c0040c240081c00003840700200f4580310300c5001903400031400000c40780642da00308501d60002d214a240c03d201d5241411b50458503800780404032014407540c03110504a541d00e1001f40c0c3da501501038400c12180d0b050b07082101c040c040b040e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 566644262 1250 566643012 566643029
    0xa02070302090a0b0f0a1805100906030b09011508030a0516060222170a0b0417030103081308070605040b070f06050a09110418141002070c1e0503100914070602010204 73
    0x10045c1100781008002c181c01c17220201c1e107071200c900c445030607140680001400310724001c08011003c135008501e13100b6030000c0e50140864a8462038800002801c4502000c100a0144c6130403204201881c000802c681310321605203401c5840308520792584468025180008200500126003100044809030111091050214400800d44c0c2d54448158803081c08140360103054109240f03007008103103040f0380250071500c59104d03003028400e000749041c4250800e030000c4804e0480041c1c1d85e24031440024581d0050f141c840c01410003071b441c00b180a4003900c40c51003441802e62022440d001071000c1c8440503a0036940180c000e011070300d4445000c0c4001d10400703100b111100d40c8900c00c4900790800d0310940140111042c64000301c1da40d2516003060302c402c490b08241480c842d4040b0311103855030a00140002c079200700f0780318240c3c60400000c844006111303070068008002d240070411095070002141050021310060003d92540d240c1084e80d06045002d030090210303c0341c40d40002c0d03855030540c000e0003203403e0310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 566645512 1250 566644262 566644279
    0xa020a1a1603150506071113230708040303050a0b0a0303090513020405090109110c2a190b09010302040b120412140f03061807020f060901020c120a02070302090a0b 72
    0x35034050b800c59038001080d112803084071006018905007031009096090082d0300c0e1402041d17280340000d040104a000503110f083c2c4948004058400c2200c11034804042d4150380086444d111030001d00c011802800a42019250b00c003050b000195030340100b0a4440281811000c076071281400742011a06104140c010300343c0c62110b0410450034404d0f541981e000524940f1640d01c3c02d4504000380100003103690010100700010714807080d080008035801200b0240c200c01540c11601143c0d0742042c0e40324101e00900b18540300070910b40c008194041551058414283c4424107074004034000c0c0900d42009a005800160001c0e035400451000d503ca07038403814003003c6552102004070b43d03040d8026055800e005051210819031250000615413000c009440440211402d40004800210503103641d800750300085d00c180c0c443d80d000e10280e030b03100007120000e6140c0481c0f100100e64a000c10844001d180401060100490b44207004080045400500ca80a01e0070240104001845500480c3e4400d5000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 566646762 1250 566645512 566645551
    0x90e040c0e0a0213090e030c0a060b0301050609060d0609030e1003050a0b01020a02030703031b0c0e1e070f08100b22120c14040b150703020c0a030c03080a020a1a 71
    0x40d00880722040e80c19004130102c1131803c518440501900d20a81049000c14440301d054030204102e0241e2081c0520300105981c24030600381807c481002d08040d0241c4184400c02c44207072581c0f101003501c990b01500000303042169003000c4907819002040d00c0c0e40041d8841e64149003d5140e0040e41c000c0701d40c118104500c4081c4c078016a07450011600094158000b0780003000403d0048450045009021150404200c559a901c0d035480202e60049180c180340002480014038032494002d03545611583c501500e03090601000c0e0100940c2011a0b040026030400034103003641c0c2d0b01c1e141e4020501d0b04403564490460b43d480701c12000c40120849445100848000f1740310168440d00c1c0c002c0b070f41002007506801c0c10401189400220041d1050b0016113440c0c00c04d0780c940310b40100600c0421311510300c2e074440b856403800905000c44680c050348500e04051050012a407020003160481c3e40c401c185a07981c0d400c08806031b04080d803907003020b040e1000e024042c4503c10351241036548540981610384540e40d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 566648012 1250 566646762 566646781
    0x1401021605010e0603040c09050a0c02010b0d022409060f190504050112020c1e0f0706080411040507020f07030c060e1009090b03010608100c030e150a0c090e040c0e 72
    0x29125582c0080e00901d120a0783c1e04000009641150160807842d04141d240d141714001d6450a5482407480c036942c00c0e000049550a00c122020780600311004002e500194001462141d405405d0307405004820126541c108503403401c0310031840c40030340929140c66505004618640050390b150308180010160450614440e10032607003510b005868154040a1018101c4001d400034981201d00d40306040901300044840200401890704100c010b080010020a101c0e041500e20342c4241c05121401c4148800a0111003500405080c166000200b40e5102141280703003c010741000d0f80d690182840220910030411500816a4900d171103807000308943d6418400450f200d401c1400000c0c6c03202c1824041c0c907031360f81c01100301c5490080010030b140b61075030460740c1040400c05410f0340069643c084002c0c441d030103020710303460780001502038540300c0c541c5503ca006644000300886240c5545100c248005405112014050314074110030940c24942032501c040c20070520300451004c51040d1001810152 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 566649262 1250 566648012 566648053
    0x9130b0f0103150b0d021201050412020a0c050405090a0c080c0108130206071403040b0c030301170f062a030106020a1a070c15020403080c0a061a0d030e19140102 71
    0x81d8003980340d40b0b06004039032500000307284c680255948104030300000c0c0f015a550b030760104680c0c0380c450f0001406081500c1c001c20303c40000f8074502c06540250030500c001c1080005402c04540c01a41d0204540c0d031004402801e004a0001c0144046140714001c22502000140355a045000307880c1d078401034448040b8078205543c0303400000d600030301c1080580005030514000e000412081403c503401c041e2522203510326a040007040b40890f5001000402c9001028508885000c0b014005442c42e2100168003d0b2121002092008010f10615030341042520652003250307061440c030300058895131100340080d146e11410f001034600350100d10f00201101d0352882164000e4419071141c0609030040da9036120a00746a003642140d0b26800d00000000c50041401020001c240d03c000c0d020380e280a103007100c03c40b02c0ca0201c4c008c40500c00103107408251180e6655128554050034542c14811894000038043c214205a1030302074a1200000100f02c0420752400132130030026002c2d150480388052607a002c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 566650512 1250 566649262 566649269
    0x9060506040f172107020102071d1b190e0108100503100b030102121315230c090d0b0a0e010504081204080408070b09120c030a08090f09130b0f01 64
    0x500b10807008000c1c2000c00e52400c054103150360190341d680d050203110280781222107202c400ca2001c0002d505002c540e418010400540440b542021201e2031580c0343c42101d401c005e00440814a41c41b841c3c8030756241e0360040d00d18a055028080d0001c2e422401c0051100044540c01404509003030049000030211944400a40d40c014004009074000d9800b0ba10103000d001c2403e5415560810580c4055102905000c3c0709100d002e00c40301141e60036140c0010752010080c00e0400c01031402180747c02404c0b0002c181142007809241500351030301e0b076100d041321a104c0c0081d59170707001c00c0070b06603a000c000b4005a080d200d200192404c01c400ea01c40d001c00740c265007003110014900c060400c54680c00c000c0101d8070941040c000d4103000d080603120808940b501c1c01d282c011006a1341e0100303444440b4541000200c0382100200d010700303c4044420042035455480c0348004040c1c03200414003c8050f21451140c0d6003420000382081840c0c00d04d154010012103001d202a0341030100d86000841515140714154102d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 566651762 1250 566650512 566650529
    0x10603061d0d0f0e090103050d0f14071211030c010c020c0406050102070e0c190207080d052823090a0b0304050a0303020d1e0506090703050105060a11030405090106090906050604 78
    0x4030004010488204001d5140f41041c00720400d10300c809900c035800e500f4041c41c0302d4001494009561240a024280308081300010041d0304109018199010820707584000e40c44540b982034022001700c1924045048824400703d444089900c2035007110542007098600060307000d45400940401c140000c2c4c070f4076030149a002d07034001c0404000710019050000c2d88000c444450700c0c2011345521403481c0008105045c0d0740140d00c0b44800f480000400d01c14002101210b00b04a4074142d141c84508900083c1b440101c0d0700941c14ac05030f06001030040c080f0003440e54400940072039a049050300201c007900840c90380d9000d103041c079a0214440c8442c43c2200d00030b50300040108541407640d64200c0203540417002d0001180e403111131a040362004182e280551041307070340c0040b540b85010400c2c03080d0340200810790700c209410311004104a448441c02ca80d00c4001a01d06654002c102010144c91880b03143d004e07642003610708000007801c0754400980b0050b19075440c0700307000c00c070fa0303607000c008142c0114002c540c0d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 566653012 1250 566651762 566651773
    0xb060f030a0522080327030307020615100507020102010b10170a06060206160c17030105280612180b011701110904020a02150a0b030c010305010803030403030504031808010603061d 79
    0xc64205406540c0c03011ba400440c1c400d0000400030300108201d00402c0208551001c800c1c0b10049030140041503001041000e01c01c801d088110005030304801e0318220b03806102c40060350805592003900192820900908040000d07000100001c00c01090a02d100c0207603a411004103664148a01800080700c1c210b0f4014110b54032540c10500040c043d510460082c004203a602c40e0008554150228441149110300742d03d0758036000600051006030201c101c04551109040040400c1e00301e5800113581103440e1158502014640030002042001003000d107558400341112704020141c844141a160001d07401e650246020900c5801d98241d001000c00e040e006211040c0281803c4d070180000e00300510448a001424001c01408148180c5e0080555502e80c048160385042c20840c1c10305503c820f1800b0402503240c002d51646170300000d00000c04050704e030b07008142410f00c541a07450344a030705092031882d81651040080c0c000d00027444211600c40c1800240404655192200402e52002001900303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 566654262 1250 566653012 566653081
    0x1a040b01031503240e061b0703020715030612060c0e0604030b06010509040f1a030d14180a0f090e070e04050d0c081e070c050a051e040b060f030a05 65
    0x641c1039180345a010500c010982038848611140150000021400e000c6d103858182008106a00380d00c501d154000c41c482000540000390307001031084216042240c0ca101c800400a80450141400343d000303000400c49280604c09000041d400350728a0701103510340e422004d03034050921100d8011488081c00c250b050b100002e4055000d00b0040511190050001590a0903805c40d07004840907100c42c80d84900100d02c4901c86401e0801505002159904003209504c103c1815090300b80310b50f8195090341e20403802404000d0710743c6203011014104200d07903c0070b040d40300c0010200134450100545850b124028000604208040603d03005517040406080b04801040050340d0262081c20207c0d8034403420072113000700444483c04e0005082504c3c588507a80d800703506002c50300c1500c5811440c0b080040500c00c02031076a490200c40c3c40060800080d0240030300c002c000800600022072526002040014032501c4a84e40000543c800c43e80404d00b00b10a8841d101c0d82c41081c81420f034801000f500000e00c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 566655512 1250 566654262 566654273
    0x306020904140a05090606061e090406030c0602061f030b13110a060203130b0307020601120c0305030703030906150605160c0503070b0703080c030601120b01030f1a040b01031503 78
    0x40022900c080d01c00b040d490401468040c4920b81180c034455a00d07a18010700100d02e601307000c55a04101d007281c010742000c210324101c042045070030f16001d086100020f2880c0181d2648d82024000715040441c820085a80b0507001c0d4460000f1120b541c40c0000c0e10158074041c07402e1882c0a03081d40d4000f640151240c2d00d03030810800344022103000b0703124000303501e8030800e07a0707070b80c0010403c05000580d02558444400064003456102c0640080742d0303104050041010081c0d0000703d40e41141c0c00c41a41840480d640c1c14601012122600080c007a4000025000207042d0503801c201200c80c441c040800c50f0301034804040b5005561030090740001401000024080c101d01d007401d00790107001c0d9a03040080ca90301c000003480c044480c1e10001e018034010a4000c249600035420720307030094054006529625014000a049604407841c0300901a66034248003004e9100c0d034003101034003801a43c03c10081d640f10180301c040004200c03905116600340380da10070b01540320b8002e0b201d403c1e004410f0f4910050559030780 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 566656762 1250 566655512 566655517
    0x3031008060a1b0f170a0b041515050a1403010f030c080102031b0d0b030a0506150a0f090507120f091101090e0c1e070b0405010501120f111c0506060a050910030602 72
    0x212400c00155110503c18003d204440d03034018800c421b000606c912103e0184410b89a00c1c80018261a20302d00e4200549500060102d406200300e240180c0c1d0361034808020784610090140c2d0b41c0c00041c001c1f0021840805014000381500d00440002800359031350000300b030a07803004460000b07088a8404c240c18042c903030407000d0005011050302c0401c03850340031404039191100000041e520b40d4050024000030f40f0b60350360708980b40c02c0c0640304140c11505040381074460b5252481400c0041d0340c0c607030002d04110301c643d2650b60000d040ca8400d20644000c85001800703044141740c00e4600440003180482c0d03d41c001e036058070840d60101142034199450075100c8846420140030109019042c0300d10183d613405081c01001c04c144113034201407e0b8141800d02c107003101c0c4141c21070300780c2c1d03942c0c20042c00200c1c5d888203d0740009a817004640d60740c66500c4000c50715801418030f1200c902c41c414203040d010060081180c9106110994910b64520f507140704201252905480c06140452101e20500210b0540e800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 566658012 1250 566656762 566656787
    0x70516060b06070503071b052b020a12030f09062a0506042a050607060e010b030d020d11011107030809150a1a0904030801061b020303031008060a1b 65
    0x1595000c520100e6055800660104c0319600001070304402c01000c0d100080000100b44107841e0020705060100305100c3daa04000002e407403c86200c20b1041100c060702c2503407180e001e0b14441c4141d0380d80b881c0b0111088501000c80c08100c1e00704108140d01d00c030b00c1c4010708540f80b40d900d07070716000403048500064400382105804928201031010020030010451540542d20804048401c10003c1c0c07600801c400c490465243e1813000003100300410b980743e90969a00c203403c840000f0711002c2d800421401068000021501405010103016045401140b0a0303006840c0b6110750362042407900c102c80c22140589440418801c0a00411012a00c00c0000980c8103074194201c42c031158080c0c1810101f0704084448440d034036241c9c41200548000c101c15246c0c0008182c85007106810642d401038440740050140104020300c0c1c81c00c0a03041168515555442900503090300e42c0c13400c0043c61403a015030b0380c2c014143c0b0340c41160003040003890a03200b0b110b00e2000740381c80465020b6180004a40395203610030b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 566659262 1250 566658012 566658023
    0x20c0f090c1308011109130b0a0b030c1e09030d030b09010e090316060204051c0f0b070905040207050d1b030503270d031b230f07080c060405070e070516 67
    0x10700410b060303c007489030442804c24400c0365601d80c0c04600800220048000110050605045800d00c0603140d80d02c03014240c4981000c1d0a840740d0f2161421700d92401020071340c40070502c090382d00d10240c2c0b8410f8024401c14a01f58140c0d09150300c1c0d54000e40685018006550f0071005041c0104203c0c005184059040a00442628640403d02c120f489001080d4841920b92660000d4200258a803818150b800c10207031708105444402e10380c0300c0481e50302c0a0030000d484001e01c2c00008007018842c20114000d0600200215120381c69414481d640314400d640450105241c0d2003802420001441c12101d265419925149150b842c1c21482c42d10614500f104803004000d07198008400c981804400c00b40c6c08290390009145034900b94001c0290348212141050015803070030000c0c203110881026010401084c441030396414200990a114890101e006d0f06100c0d001c00c00000d842c0340422444d0080c2d00800407607640f55120700400254100a41d186008910100b01c407002d424400c2100d42031170790058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 566660512 1250 566659262 566659297
    0x209030114070807080708070f0c020613170106060905101112160506060405011404110405060721140d0c1e0504050312090904020910050d080a020c0f090c 68
    0xa450078500c0030303801d49410300415219010841043c0e031040b0819807014441c607002c0c44500701210042c080317014803080902003108041c10362080d034407a401151840300c0311280300c501441da2508842003001c0748003484400365080c1a00000c20911035260034058a800400720b040c0c1c152008020344070203000707840d00aa903001c0c00410449554805002c2d00524440805032142c1380c14a140150600c1c800420701c600c1249054018004001e044008003298113007994005201945008407042c82e0140ba4017079036119000143c0c1c4402c000551202045085161a2140680040f05030a403817003140c404440c259401e040c8081c40d020712654100003101c010b60300340315074125200c1c072480c040c0f0580582e154003c5100010200282e05081040111019441c4e2a0324100800394000444032040584044d1041d400040824180f01811031040002c100080c01c030f8410200c0b62811035015000440014058051040804084e05221400100c0c03420028030140c2c0c9a6280e2241c9090380d00468038900442103403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 566661762 1250 566660512 566660531
    0x1050306061b120702090703062603040e0c0a0f050403170702060903061015140703031d0f010504110d24090c091d03040b0d021e0d0c030b0f09040602090301 69
    0x50143d40c11020255410541d00c2c0c00341d0050003001c883c00740180e0201032410004110042d45120f000405e12030081170021243c0002d41e0311413540c003940e08520f294000e07403028000174203002c034000c0803001d0702902c5e02504224841421f0303072640981c0c440a0407101c482c0590380c810b00300b19001020003900c02400300f410f10240c074010900d4a00100c414904061381d000040c440b0306a030b4071410710581c090b441c1c00d64520f40c3c07500c011150743c02091070040500d130312813092601c000409086d008000007128201c549030003110400301d001c0e110564065078a40c1c0d542e0b000c60001d007001104165095040540a0300d440002c8040743c24111031081a00e11041c1d440d43c1032000100702400c1503006001103c008103c18200710a107041d880c5450781351801580c0708100400036881d00c041030300d0601c0b050580058491106214004141c20485203816042c040080e03400300030035488c3d11810101c1c0c84c50703070304010410003601885010540b10500b130b40c2c0100040005400135072142c00801c007802c009800442d1802d41c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 566663012 1250 566661762 566661817
    0x604260a0306090b030d140918040308100f03080a181e05090105060703230d020f030f01060219020d0f050607020a0b0901090f1115040f03030e040b0105030606 70
    0x20160555000030344a190400c000003c0d4040c044141c0d5040340501544a9591000b40000010813001c02d44c0c040302182106c495038402100f4074a07070115850b4581c051400f80f60040540c41d081b101c02941c02200b035008241101c0d980d04a00549901100c498030342900408140c0300103074200150840c1440885020403030341d0441200040101002c3c006102050a2504002310400305802541c0900300034080000400d5001a03190ba640032943d105041070844001104040d100c4c580c60150082c0c0009070101a007102f41000b107120707070304003801c06915036201e031401c83e1607840b07000315040c24824a40c00003025150400d403881c1464460000749040e01702560b03078542040c1080301d00c2400346e0402004c21040c417032400402c59002d20100d000300402c0c4000d503074000c2e601025550103450b01d000c04241207010340700c0c6062903080c0c10200f001d02d501c40b9620305250500c02c01c00d020441c0010044202d007076103800e160144a8a0002c140c6030035003195600c105212440d00b04d0303203041078906840b010045c070098 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 566664262 1250 566663012 566663017
    0x15061508090715022803090b1b030304030906020606010216150909180b07110604030c060221060f06040b040e04020d15050a0506090f01060e03030717040504110309060426 75
    0x5070310b030040e0010f10060329107030f0080f05c1c2c0040d0f0500c1c2103144c9404070b00040d6100c075040080d85e50704440d09071111a45c03200c080c80b1503c000d8061920b80320001c2803106040c1c100c1d9104013110011703805c0311603d6803a5401241c803140421014410034000c4170051003180004807601402c4c45a626006081540d10104442960540303a1400b0150005501c001c09001415025035031000445c00c054041041c49482d6664411004201808200d251a000c0c41045800c0d0112094261504007071406189281d4039803041c8002078031040c0c46540364690102c2c8a06000040e1004c5901c0d00720054245803810514402665005004903404000071403503070001003c254400303130b00002041c030000b1140b0305542e481d004c4540281005214641e0441080000d100c200c0006044d10111b240c050003c29035a40440d185014102c4c004002003400b59a1254808084001e4800c845040724103002d00c0400904980c110304c010703030f41c280843d08050001b074082120801c12444907809030003405050500031000c090642c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 566665512 1250 566664262 566664299
    0x220507111c1b032109020d050c01020f3c03030a050a0f06030203060a0f110c0307120804022b14030a09080606100806041b0507150615080907 62
    0x349004111080c1d005074414402040007042d02010003190303c0c0a4100300154100741d18600ca51403680c41558840d400c00f8400ca0340c00341050103046081c0c0b40aa84030684c119000c1d0052080041e403002108000a0643d41c4840f1080c1c080c80d10422018010b81004c15140c0c00140c00f40c01c0800d04400754400c1004510690607440000b07a28104594500b05540000c003143c084030742041018405a034012680a800541003000041c0142d40d0f130601d100a0460001c402081c10000300e205211018040020041c8500c81d100c440001d80d0b040da8142c038074107410b88002e90002142410b00708100550303006401c040c0e0810005910707100c442c4d9100c1001040f12403184400d60400305605d20031a401000d984090203000c00900350b1890031a0106034100c0300c181c0c2e100b00b00180b80e03010410507204e96219107000740b1a210b0510514090150182c0301c1c1c3d1011000700e98010b284c900c030b409c20010b64400d50f01500e070440a00000c1c42142c0c04100c1d134000019000811a00401c000007985a54404404001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 566666762 1250 566665512 566665543
    0x5090f0a320918010506030c060d0e0a140102180a030b0c0a020f010213060215040b130609020303030a150e060303030a0e01020c0a0c06090807081c090e0a02130522050711 75
    0xb092543c07010f007801e441004c0e204501a034464000170f0b0f115580c1000743c807000070541d00009000e072190a00145032070380a0740c0240034060346091241e14024190014021006000c03070390300c5010406010b12810145521001d03294042c10008200340b14403920081140b0b196901c12100e81c3c0512402c41c500720383c0b01c3c0e5601c0c407082c024600c04000e401c2d014005101c051500c41d81d802d0041c609503c882141c0940209565080701c41c13801c1c24010004507070301c02c0a05980150490380c0ba86000c5640e0740081500317606041020314076100025408444000360382c8640070250145040d500c941c0100c501821640181c0c50320b42d5000d204041000b60100500c19105020700e000ca0745140c0b038010060f0848407280c02026141c2c002c1c0c038043c0603030400090210503d000510400c0020030881900310f130a100141c000b6400041c82c04140201c150054019010886e65400340b0030116070344804001e03261b450002c0c01e100c91030000d04c0d000c21849071980120b50240107400c00201000342100380904203584240765264 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 566668012 1250 566666762 566666791
    0x901052503080901020a020604061815050a06170a060c0903080711100509010c1b0e09100b0d020102060f090f030f0d0b030105010e0406020d02090d0305090f0a3209 72
    0x41c541d0010103190040c40ca04000c44c40c02c2d065010080d110440144040c0c012500d500c0c0c1111644140c20364000f4440d0030000d40b048110844d2650406040c00f039512425203402c1c0038011900d20000c0c00c020500d16071031001460695426a9941c020380025900301e400c0c00303d881c0000005c110100001c005280c4100341c03418455200c1c0c01048480b81c0014406010170800b8001140183d800030302c950b01c02c1e1303000450101080d1143c11101900403550304054130055010060150241000441141419101070144850441e9806201c0b031080c110501a0060b0301110205800000100b100c1da00580b12900360f8014010450003549943d00620031802100c0e0006001d846007041d6200e00c0b00700c0801107009102c10351410481203030071000030300043d109590008628058146503411940c51050140198000b225030703041c05002a00b103000c115002e003241c82000364082c5801d400080560f11065500d1103602d03001d0510010064072212030301043c4001c2c496003142e5503520b002d05480317440c800e00800c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 566669262 1250 566668012 566668087
    0xa030207090509031614030a1d0d11012d0e040e010b0303030402090c04030203160603140903160f080d020705070b0a020d08060f1207090c08130206090105 68
    0x2440c052103680442210391411040c8019a8008002c1313403840860b80e01e50b10119025424500c108803108903003030015200014613140c0c0c66070048410a10010031003151500c110040041c00940e50802900801c4031044104561203907004500101200300720a004002c84440c824401c1c0340035071043c464002081001c002103200e4034141c0110350601d52040000c0c0403505150700440c0e81e034003010b0300091040c00d0020004410080f1b07441a84c000f036030001d085910025500c0b15540104841d8001d010000e4180703c4590290709002c5412402424046c008524201c0451550b44192140110450320383c0184001880402c44034800b80c00080304403140161780728081e107042c510b0403505a104903202481030001d01d240030b8000c00c02803080c1c10741d8107221030903989500004600c00703044020254000c0d94013008080104c00024844183c81206404100c1c00031103103030540e007a0f102154561003419120b00300d48014206000030308003220741814481d0800b00b0301c899400340c980308001c0c919140c50240f100700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 566670512 1250 566669262 566669267
    0x112110a0f0f0b070c050d1a151002030315010e04020f041404061e180f0f1a0a081903110a1505060a03032f0a0317070e03070608060307170a03 63
    0x1440c03e414003d01e00302035566a1410b001040c8102c61144240b402c0d1803051015201d03404a005640c042da9401e107260548152000c4c000da0703261035000702d4060000d542c1690002045a0285013010070700240501c4881c01142d414180c0d00002c5c3c1c000c0c0e000d100610091080b1000380000d01804c2000c841d49842000900c001ca89241d403144110150400802003680981c282c80b0301503901030503801c8000c2801c4254070307024200071003210140707518000d907802c1080362943c403002080d07984070380c403164801c006000c02125014901a41c0d203a500142e5950940312211142441003a00c00d081c19130101c1c2c003440700c090621138820000d03241c01a03036030001030205030207106940d440b0808680a400040c1544c900a108004220b1400780c00101c0369140519a0f901405852102401c41b048404d01c0c001460000c01182c4035940c40085003c884000c100f00341d010f070350280b00e2058090000c140d900d1808004451941019101540500502c580404d81a000342c02501240030b03480d00a24a01d070051400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 566671762 1250 566670512 566670539
    0x1110703091a1306080705190c110301051012060b030616020723060d0f02180321090d0c05030a030305010815041502090414161b03080112110a0f 64
    0xc2e0350004200303d8209a00710311808182034501e5480d01c81c0250703840f00f030305444a10400d0010030b42c070300b0864a0b03449144e40c081c008606080c40703071181d070344c40903120014142a10320a8448a00d084000c00313041c0001140700802a2582d406440045111000c900101b82000010744804414044550840400680402100f0004c0034161100f4100f03101040c0f007102c4545003d607803e44039110001e00000c05c40400d8000001e02d00381e20074115510300217680d4a00700c5240342440607000e030007014000400345044a1144030405004003d0b03a01c1c1034042c00410200328125901140e00038186040441c098604100d11120395101e5280011103505207080c0030700d0043c0700450701003c1c600b044100400120b01c41089c1d10f00707880c210805611050060000340207000c0d43c003100280040390000b00654000c03e40005840c990340340e110b0400c1c840f0200c000703103045c40c1e03000005804200381c4401000083c14403000f0306101405051582000c801400005844020943c0000641000000240500c9594524 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 566673012 1250 566671762 566671799
    0xf060a0201061d01060207062006090f1e07141302030106080403030e0f0c01050a05160503090405060a0e060904021201020304051c020703020a180b06040e0901050a020309060a0507020111070309 85
    0x18001d00f65850910025507070041c40c00341d0301c10404400d40800031038024403107aa400034403c400b590058034004411665403c082e1400d0341052244001d00c03603960005203a03040714a54817070050480a81801c500c860603080c20b000d081c3d001350149242614403e030354070166000c0d200c9982d4061060038a0305009090301e4044025510130340100c20160b0400c00c0c0043d00120380f480c00e003080303074903200f81c4803051b541400b5041404c40d40b143c1c031403010f108002c008001050f80354000c681c1040143c4070b110034070825115a01801d001404a6400300e01e8503c0c2082d802e6a016100a000d8000075805c68201e5003680c00c04e480c00c07074003a0b12180310b007020500da40c080a03040c59201d00c000c0401c589950009000544c1030f206240c50140804010f104d40ca00039048003828120141280e5515541c840341c941c1e203c0001c8803001120b51805002c40c852040318001c80303008a08000085c04a500c41654200040101603d01c0301599680c0e02c90411403e103800c06410114000d441c1ca540c06850546140b042150001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 566674262 1250 566673012 566673059
    0x306060e0f04060903090801140105030d0201050705030a09020a030f06140901020906090603040c170604030212180f0a1a0a0e0f0d0f050c09040606150905030c0f0f060a020106 77
    0x18208401040c1d0118a158455080705001c00c00150a05040e209601550040045542400540c0b6000c140c1c0904590480340b09030119411046d1010703040b422148151180000074008102240f080c4458ac1c10185a440c001040c400f0003e9496940020500380c000d805c85216855200c8106651a41480349911401c1c410003945403c40302d00002e0618441e1221441c41000040041003d1141e2140c01c4405440350b4030b403c400c074820201000c1e84d5140100c504800510686803c01c02d60820b02d42991080064a61900d03e198021410404446d1806e40c100e50041c1c05804001020304208858001001e5004c141c9070303503018a0304004003203a01c5c8121071801130320f4004112401352510024104d185410800c0c10198650a01d819405c1151120515600c0f003e00401d000a0041c150700010840d075010780d103101400701504041e99140c41d144070300c6034540c00c684d14090740c50400c48420541320718018800003ca10390400000c00304d0300031001200060707545103024420b00d034058403114055048039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 566675512 1250 566674262 566674289
    0x1608010e0d02031c0b060f30160201180c050f0402030618091f0b010e01021501030b15060f07031403040c1211090f06280909032106030606 61
    0x7200042d5981c854600311004145405024614064517544550801c0e800281401d81e9244121140c0846030080903030220030f05a800701c0d10342c1d0040c2000b01d00c005205445518a0303284d80e14104c000f0340159680205041d5520780204060011741e0310355480e50980310f4400c0c1c40310b650a042c14409070b010344004080c000c51042050003a540d442c0d8903210f0f4044071060b403c0070b103aa90342800f00e00342204180a00c4680d000070003003460907c05608481000042079031074a51441c0140d004a82d1003001210704001005440d005001007141c4510701d42e4080c001081c408440044400400d00300d510202d003645410380003003000e10070568020400b41e203125021001e54211706182c1c40e842e20402240c41448000c940b01c0540784100613030641c04190340715008101003254902030b100c2d403006507001c4074220b210300c00d011464540c82c12040b0180c0740800d081650304400c50705005540c4001d0a06000030307400d104807800d200c90780060703404080044542c80c1c01e01240003131952034480290794464104400b1408803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 566676762 1250 566675512 566675533
    0x1e11030d1106100f03060209010e0a0611010c09060e012d03050f01050109080718110301141005190305180a1202101e0b01031d070e090601060801150207081608010e 72
    0xb1004580c181c9801c6a401030b640e06030f23280180d50032914500803130b07040031480c0d1001a1250300301c0320180c0e000c840c140003031200042800302183c01c09030394000d07400810103034091410700354070580b0400c20804032000282844103a01c21801704900100702d03903800003034580041001c03180c0c030740c200d09004003000e0807c84c0e0340742d0400d00440e8440707819000e84070100c05070b8030008030141500c0c4c2220080c4c2034844001c070307900c2d61914904800903e0210a0601030014090030112061203401244c001d00620290844000f5500310110050310303014004146045a01e41021083c01c1e041c0301204000e4411008bd8a00c0b00c0c0c400000b03820300130084103400b507142c5085400c841b14405000c0c41c0402040c10780c0005148218440103900a10700c2410161030141c0490341d41e15510300000b202c0d801d0f9542000c2103181507a40c00d064554820090085100003885a40100200c45000110400700c12150050300c20054441568038036021403580e19000c1240100e0007046407c000b0700c9003014940c0d20f0406442c00010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 566678012 1250 566676762 566676779
    0x4081e071217120a02090f0f2209060c0c0309321306030b1b09030c0d1a090a0c0902070317070c05100b0a0509041e11030d110610 57
    0x250108007034440110b08100c4490902c0c02c508580c3c0035485501c2e40780003030404050500007900b011480340d004801106490050307240c54102116184c07002024401c00035400c25814803001101880c403c5c9094460340d80500043e1180a9044042100c1d41c0341c0004074842c3c180100401c0a5a1080e0040c18007505a143c3e49417450416031843d0383c162900c0b400d04038a61002c00c0354181550400f050062920001000308800046900e0141c0003003050001600000750440300d941c82084a0f00381c3c075910801c01d0440c2801c1516032004028000d056081611014102d081c002600444040350a038104c1003c40c0c0802844680f02c401803c2c41c02230842c104445540d000e000c5101c48039590105802420014103550303c184004e401090380030044c0e6898540f000c810001a28100e00c28a00c00c1c070055402096606000d0f101031311035508800616055000461000c000c5240e15034150340e0000e0ac1c802c045001d8504004c0d840034081540c1c1d8008090354002891401c1900107400c190100102d81c03000c12010a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 566679262 1250 566678012 566678039
    0x61201111617040e060f0a0e070903050f1f0c0c21031103040b040f0804080318130b090f040f0b010e090c0f013606050301170604030f1d030304081e07 66
    0x1406d4450b0fa928158120003d403000c8003e46c070002100a8800c10410300310b0b0710403082c9080381c1c4920308403078081d00f2800e041c50b200c444850241d101d81d8210003442c001307819541c0000d65440d019041610030011203840304500841c44040010b40d030301c1d00c0c114200103654036104078440110400080d9045042640d201000200017501c041c0000e056070034108107006408080798024010032313048994400340400c2d21300d03640320036250b240d100e5018079410300c0e02102c140c025011051001400b1400590311845c0c1e00090200190082e90b0495001c00420000303042810000d0207404081c3da01c071110314216042c9841d10f42030b0b010981c064440344c941c0f0031840c0d0f00315148480c2d040301142440b1484502c185200800c0010b03417022100240202000200c250b00700c0e004505881c20f1300c06002c2c1c0000d129040c0c6039198815100100044c1c02428111005449181e156081c449207501070306810464200007499500070f9006091039030040c4c00b4146040100d100c3c09081081d010000d0400c003803501c030b07034890800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 566680512 1250 566679262 566679271
    0xc0307053009010207091514150f0315060d0209100329010314070e093102040207020a03050d0e03121e040f03030f0f0314061201111617040e 62
    0x2201c020994600300d80c020b2000b6030241002150811141262020001180382e55204030b08484100307008800c0756040400e0b903000e003050b103540c00c545017030001e00c0251110350008100400780d14418066444507502d80e0300501d1401c0c008400940c031201c800007044003490315000340b1410315240ca6045103040d00d4000200c5c0051484c06011962034010100590107842c40c10444428040c240c02009001500440070392403c040660360f013461640d859201071a2841120b910301100782c02c109404018100608040803200d1001c1c001508020b1160b0109561002c80d410031582d0360042494000300c0c950040102010b032030124000d2490030100303046610300d80f00707806181900d2030700f0f48815480c001074072040300e00510741c03039031100005643c03414020003010030001a2000900d1002160326024800c0c0603841028003103500302007460325032030100301108807005059082c954032001a92020102c1d0009802c00070700f024a02040072b40c40d440c0043e1590500401c2d8002d095050100b40001e0300d242080c143d02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 566681762 1250 566680512 566680603
    0xc0b040f1a070c0e150d060c0f08070c0204050403200105071101090f0204050a110c15070302180d031806021c021501120f0b04030f02281b0b0c030705 66
    0x4549504c500c1709100d15114000c190403c505801400c10003e040d4004800d00400e5960300c49101461003040b0794404003601c2c2d200006103480480e41c05031074a5880503802520a0810044204200265030001c00d01d488201d0001d035505d00c10015803d40204000518a0b403c00017003040c5000c5545050b4018540790020380900d5460740000c6945115600040a969500703104a80b1100f0511800ba912840e000c0380140c3e4000c110086001e40f402402554024020140d501900c10b03c0354091012032070158205500b00000e4114808510000000d080c000d400700350f000c0c055122003014980380183c0303085036003011584041c1000c0c0c8007000008080b41502d406103030b01000113641d81864020b90401d118050200d030300d100240003c16402034503090524100b078098800314944170040810b002900d00c1101800b400700a000710001e0448182c024070040d45d180d154036525140d24841c18150480460154036600001d4040e0500c2030800008074408030801200c0036501e400500710a460b00041d845420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 566683012 1250 566681762 566681789
    0x11d0c01090f081e07090204030b010f050105030609060f0f06130e0f0106020304061d1003141b031306020d091a0f060102070306021b0a150f0207021503040c0b040f1a070c 75
    0x51001301403040c4001440300403c20354659440e810421018007082c8036142019400980014140d401801070705d20600005144601503900c0c101440882aa6084d4046d4450341031521402c031961080d001c0c100b00030700300b045015294149024080020805425050300c0404c841c0100800c40d4000111400e1780e09512300301c4405054010041601c400302e0200c2a444442c2d4030392201403d516a22501036090600403141864071601813180e02d641c582c2420f03980310002003000a01080f41100c507501070034803c50005103802c0c00e9907100f40843d440b4040c04c460100469650100003406102456045025072740048200e06000c030000c0d650300d0305440000e01d1580c0200d04103d802c44030144c0750f000100d40d041921a490301034a072546450a1510841e5240c62410011004500c49482508c89003030380a0001d40911028603410801604000d0040740c0000580f400410b4114a21015100803c00f002d00b1700704660038902101e125080903401a2150042405000c0100340c05400c05403c581c1d5414074240c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 566684262 1250 566683012 566683063
    0xa030c050f2208010501061701150e040506060d0e07030203150f0610090e0702062208120402030106050d06020306010f0e0105070f111e040b150d0e011d0c01090f08 72
    0xd04242c07568060303141c1d94a890300002e80c260f0000b00843d8503c10350b1031842e0440c1c1c0c90b55401070031600c144112030001041041919500d00f056400a81c02c81d40050815041100b007402c0d640655070480290066600188010401c604081000b251061102c0070301d111140340070321201c02d40c0d940080c0007901c1803242400351a0341314025a152000f500d190801c000300380c6001c4101950381d00c41a02c2c0340540341a041c007048985240401c3c0e8003511540030020a1900c080d007441300340384c29000b400c00d90303246d50707202c030001540e60301d91b800070b04810b10500300541c0f42c2c5410000074004241d080c2c011300c01d000454002d100319a9102044030295507101812104102c0743c4c0c01e00c00300700448080440e800100f0b0100c002d0510340d105100c000740090485090040700d502c401448520f00d401144520400014824298070200c1c0d40c10039144800d40d0000040c0c51030b1001c142641c1805003100c0c40420342c01034442c5a440c0c1d68410b89c03030000307050340132150a00240382c5201c1c80c3c0d03149030702c03100315900e50704440004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 566685512 1250 566684262 566684317
    0x9090c06210f14270718090206040503010e0a030806030d0f030507020c040c12060b13170309100509040f05010317090a081c08070f050a052505030a030c050f 69
    0x9000c0400940010110314045040c84240705550704102c072865244c1000e103007103040015842c000c0e6140d01440603030110428143c200500414070089034400410f0102003400c0e2400d2040441032071122004045405003400c000d01801c00162009000e0740102940040143d00004e021901c0f0f034040c503000a683c3d8490504a08081c1400300f007a42c00303800e06564140703580d406801c4403840140f8000400a8664a640c150080e1291017008801201521010060159116a41e17a11134448070180c074585104000000d61399002019800c2c00704402003401185810248642d0300c0103000c6400401c080e5041d9103401070401c818082280486c4000500198a41c40d80c4d04803034001c02c0000200c03094001c0c1a03141d80c06038101c1c0c5440740001042c0b140000c0a151149642d040e410213546c071040e181c4407102030304a80541c00741303a02032203519042c81c5a00540040d01c40071801240038001454995907292170040a5484052807041003140900c03088a4001030181261140700700404c142d004804c802d24803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 566686762 1250 566685512 566685521
    0x60e060d0e12030601030b010504031205070c031a27060a020f1c090506070f1b0602160516090b0a0b07030c08030907080c121b1909090c06210f 63
    0x103031000b801284034400c00c41c0c0d2200003942c01040262800d022144510004403140d005600c000b0700031400c200c00100c00d007030003400141421401800a090b101c0d03140d8403039140c0014034503401c035050540401084881c0c443e42c480d2130000040030403003078842141c82140b40e949020103020800e20590006649502d541d514044503240e826081c40075001c0100d0071480c2000300301d140c02c184c0d86400f526000424003071048500d0044c0c4603194588140c4e4610301a022003d0504c065022130f4030359820082202600f00b080320490905d84034070010100e05034221452710320035603907a2040f0105070a0040d0066959102040315058035880d501032900c4031880e040885a85008020140c10400c00100b40507090300085140c40030780b54068101d440c500f0420b000e101e50841d0010075604181c0081d45038840701f4201c00e045040c03208000301101102000d444458404076201c0c0d1043e5155075a5414080400c80c40625440c020312240c01c00f40301080c0e966103034012030395202380081e41c095130710900111000303000e900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 566688012 1250 566686762 566686781
    0x6060d05210d0603050109021e01050406050a0c06090b1e0912090f0405100f0f12060209011106090709050a0e03041806090216060e06090304050d0f020301020c06061504060e060d 78
    0xb041c080c25030f49007042d034003d011001051340101040603903605100c0c0008124403070340f20103943c1c4a180c1703403030443d04907001d030003110300f0a007000300790350702000030900a010700f28010b409020800010f06040d0300c4a8100f024400414801425180030000b40c0e8001140c2c000903c1020740e1916500c41c0ca007800104414a442e40d000e43c032030711f03181c01e101c0d08502142000040c1c440000c00ca45081351a0750200f20320041a208007003c2e08241003d00d00000c81d20b401800b0f1400060408143c2030f5141c0119034203040f000c0310040360341e511400c002c11008900707014141d04081c40f08001c205200a00090035120b1069020394500030082c08458511440c0c01c1e0b01820051004181c110748a0b810010740500344d11508101b507078241c4c1070481d050383d06000030070014020000000118503252a00b4144021a180ba20054640c1c25201d039189002d61401c0c002447d01480c000c0152100d441d041e008c11041c02007123140c51a00701e1061009205454110508081414007102c2d450b8550280110b920040c0801c2407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 566689262 1250 566688012 566688037
    0x10b0d06080d1e050c06040618020901030809040612080d0203071e090f0501022b030906050c0306030f21030c09040903090303081f0312020a140703020306060d0521 72
    0x80d0072040360b0b40c401c00109030f09081959841048800142c100c0b4140508510441560024404100080c0840d84444c940c3c52010255010504090f0001420304902364000e541c00c0c000052400500d107862700c1070b000604454000902608400d840d800c050f130140c0c05019500c19400008110318500401c1d110707600c000003013011607480d1103c3d0300007021802d0314454164007840840b8003250560002c11400300c000314506800c203102c00c6000b0503200700822100700800385540d070840503000c2465070140078032407400c200140b9900c0c10260b01745450308482ca15040402d800051a510002120030184a0f440280390603039038981e00e41464680541c4500401c0c030754402d107010784013030401d90410451011070340a900c80490907a10784850861440040b450061980740e88982400003401c0c03040140c082298510440c1c051404682e6564504015002c000c1840c0e80818020002c614080106607404032003652100708028241d80c60700e6440c070203c891886420944510f0070300000504003650312401011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 566690512 1250 566689262 566689273
    0x506041b09060605073f030f050c09040c050f040e0103150b0102031204240516050405031f0605060c060405120a050405040e0f011d0f01060b0a050708130609050f010314010b0d0608 79
    0xc8540384020100d01d000b0201080c10050b03561400b1240b07228052040c074195012b54540300c00501080000e0202d421400117001d414082d5410300031040d40074102801070b4480341ca25550450a0040310b0109540d99202400d0800000711000d07607005c000d03100d42d55020304100105480d1440e10510001d10001d5074441004814129074081c3d80c0781c1c01032402501c1400540e440504c40440032641d03840b03103003c3e464040c3d2000120005030744640d2001e640c40b05500c040000c2d083e480701d0004000b82e01840404995900640074401031110910000404400c1d40d90414a802e1000c0c00c058100c1c01288285481a0ba4565211441701030520124400c0c1090070000c04c0503400b00c006110b980c8001c44001e420a11400140b1000600c052040700305540754034101c2c1e070a24026840485d660780c44040104d4082e0014401091624804000c80014115940f00c0e286464208000e20104940d4082964101030600d0300c4001c001000e4010719041d01e0300c90559981d590319030b13904100540855408150f103849039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 566691762 1250 566690512 566690603
    0x21302071a0f1911031303110304050108040b130f0303020301080c0a030213110c01090302030301030b070815040f0207020607111c0b060d06090506041b0906060507 72
    0x55008100e494461203541d003100c0c14035640c40251030801c9030040075264a40c0c02041042d148402c0390907122581030b4020410001000700310303081d5007068030a18902d03103100c000d6004254001c151070095846140041d41011700e008002410303080050b202406241d510004191007420403402c040256421041c1c0b810f105a05283c0100254024410040180150042070500c1c2c5000c0d402d210031a40c00420701d20920070321081000003030014003103191a45100b0001444104000e001e180c452900a4010b1522589181803010344008000d00c610b0420100c0c3c020003d0041d02126020602c02c003e803400a81c41c0c0f119907618009115400c03020358024004034150f000c0090f0000c4841c400380d403c0da0607001b0300c259640c43d680d4004158000501114401c40091a681402d600b14585140580404941c80f086c40d00c0386414600b0a48041c1c644100095070f00404030704412120004280d50002000f045103000d000400c076000d4140c00400b000060362400750701100c02c9100404034222010069007030f802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 566693012 1250 566691762 566691799
    0x90f09031611102d0225050d0f05010b01030e1507020c15031905090d0f1206090203090105181504140d050301090b0f10050306040f060f06031401060509090c0702 71
    0x1381c1c50040b59410300f25401442d2900506030b80b82140d0b00b420303001880700c02c4a014030208420b007604441500c008152000103056a1820802e10a8074061503411017001810b0400600b50382c6802910750516042600c100150307840040c2d4155a1202800c046800d51182c2000302d00340351503184110341c011a4442d44403640c0c1c200314000e5004000990303200f150796183c801a00d0640d40c04030340b503040f190812200702402d18010b4950007040216890880da074102140301503021900780f504042480ca6000c0200a42c5540c240314851304040da40c404103079051140301c4c015a469907007500100c0011f01c0003010500300011221542c0007801c402060300c034440030048004280c0d4000344510403201e800c102890750507050131200e0002054014281d40a180071818040d02d0661000d0401600941d07514030300110030340a0310800000c0c2451210003074015281030401001c0d42c04817a841030042526400402c51a0740100c219440f443c020390309000d090352030100c0d4030703e00d018200300a500310000b901d64004405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 566694262 1250 566693012 566693027
    0xa0210050109021c050c070f031110090303140105090106140d09141207020f060a050c0f010b01180b032e060f08010b0702030604021903020d0c0302090f0903161110 72
    0x1880d6034190f0111003600c404050585206440c0840b00751030411916002c190300c20440d4050b18001e007407281c0410f0701445564070303007040d0003a038004083ea04e0304cda804140d414010301012241c101c654032529410400001e0b803581044c8100c100b417214540e41200501d18400986204070b2508000300300480e0750f41060800b410200300038a50702c0c080c00030710400340102d4a0607038680540244c03440d0410035000b820f001e441d078042660303170301805418030010120410070090030110070740c0b031400810b194800c0000941107a480051300c204140c0c81071001d2009000d0041581d90201104202c24611f110381403070105000620a181d1400e134035210300124600c0c1d00012141c2c0c240520f0354880744241c1e03036510b11038034a0080e182e000354190000c0c4046409490540b4881183c40b16011940d0002c9540e0350001b0343c02d4001c41011070b40814022001c0007503282a488150b4440b400f0085610a850114903054aa03c5500a411180c40c0d00f515520280310809007410104180580803a40c1001009030140416 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 566695512 1250 566694262 566694277
    0x6180916030609051203070f081026010b0f010c11180114030d0c02090402040c18080615040c090e0705040f060806030c0604050102030412410601060c080a021005010902 74
    0x1e1240d040d50200341c6250008030f87c42182595900d140b4001000300440384060301905000b0b5400d8048808900600108946441e650580ca103800c58550400041800c1d1580b80301c2c0c96128614508603e1402d0344c2050316448540d0384445540d03003509000c0000303003003103075010035105680400800203d084101118806000f8008030121a8085039000003103902ca142140d00940000342ca0b0045001414180c01c00401c5c00183e08081e008a800134090070700c011005d50005109500c0041805588408001072042d4180280c0c0c0038844031044020103020402e0742d10482c203444080383e0004034518810700940d001740003807030200030800e5074a6000800c042003c1d01c1ca00d00c07a001743d45500d00302d0728121007154212141a000355080c01e1614451030b940e0301c0c400a0682c0c40c40c1c3c0202460301d42d1900d00c0c003029140b0403142c84043c044081c80b0540340b0027181030003c7c2c0b80390368006001806015040102040003d070702001c059660076024108070305000e81e0098603c0f50a04000c00481c192480d6005800c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 566696762 1250 566695512 566695523
    0x4080f030903041e0b0a08070903060c0c0c140607120e09040605180604051e010b090a060e010e0103050a02122506020d090f030f03020a05030d0f0e0606180916030609 73
    0x1204c0b6a0380980040122900c10110315031010401e1180709406146032607840881d81c2000000c0310717901e446d220103540c1101e8082000544d00300d0010308005600080c03c010b414100c180900c200001000300d103c40c49004400741c44c590706054040b044c1ea220340d44240c2034290240444483c0d0510785050409080c0c04d64424140c1c4040462000003024001503c61042d070300440109070a00480030380c0d018081440c10341c01d08654a6120b014030b1610ba04072403070701070004560006404c900d044524203941d0030682280c005040354200400c0485c42c000341940500c0e8040300d00217a0351003951800c0b403400360103c0c0d522070030b41c0c2c1c045040800401d1406494007107414540a0350003003050030b04201c8002c0d0356030058403102c0c1c40e00c41d024004184952003803845284039004441101d0303c292105172868100040c08003a2603212881071a540040340101c080300341c500d400800d42400e000d030024a2110400c0a20f4403c034500c0300014007940d03c00c001030020b0441e468940d01c0d0b81c0c0d07100d00700f000c094401982c043c0c88 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 566698012 1250 566696762 566696789
    0xf040b0c071a0702030a030f0215090c09070212031b390115181d0303100504050702030313021c110a05010e100f0e101701081b0904080f03090304 64
    0x1a02ca040011600d0095005001d0248940c10f950195119181c0c050314a0440c450081c0d0a00300740ba03a41e020328007481000004118101c2e4583c10480c0c018030080c000380864204000d01c01001c8580d1058a410040452446000042d0b505e21314440d800b842c003507001c0515a04420b03480f040070000090b81c05509194944681e8022400d400f8261240c3d0f003c41803400200e0388040001032400c80400e41194071161004c0b03010011041c0100010b81da60201745415040042403185a50140c03004100619007600d062005141414020303440340401080a41e1411044000200b15950741212208890280503280624109400e19101072100d044203540240000400860340c1d601901010b0b049070380040c01650107507842c040c1103a0b210004001c1c0c805210061111700b00c0340d0380d608102c501d0b0b24180d54501031811001001c00300507603410780c084136603a000883e90301000d81c08140e20007680c402c10b0b00c8610507911a0700c4c00c3c0c5580d02c034070318015610140100900c00002c03404801481100d144000b140c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 566699262 1250 566698012 566698049
    0x1d150d0c031505181f15020c040c2c030d03141305070b0c0102070605160f09060210020a020a0b07080619050306060f1908030c07090e0c01050f040b0c07 67
    0x2d54041d0300949621120562080403010301105410768800c070340f040130905e4100481e0307052a21051642010003071219405131082082d41c100000c44d105007044809022450300ca070405008501c0418404000c0ca0031140c0310603c1c51016228291034081c00303400c492900c20090001402048481d603030303101c51614400031580c42c2891400000e01305030407101070302c9100c0c54403480340259489203030742040342d540a1002d01c020614512415100381c000ad0700301c69502c1e2000c40c3c0205440c080a144400780040000c0502816a0029154400e6a42100d005030f4850841d1820781c50829010801080d00c601d10042010456200903218002c0c1820b0305c0b01d559450203880b01e412440100e00070b20341c00d86c2c420340000f5000e2800940e40300394000060a403c00184401c4a107211307840d01d036081345c080f560000410107500403003086600000c212417582049100c402d003882d21384401c0500c01c080c1c1000800704005d1141c002040854004110846150390348111003d5000d403100054490752040300a00c0e000700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 566700512 1250 566699262 566699291
    0x803220b2e08100b0109030b0a0504030305090f0a24151d07170a020c0d02010b120d020c37030614010b093610151d150d0c03 55
    0x400946803010040d246000c10b00701a01c00401c3d0b805501c90400881b40300c0000880d0801d134a0a002c1ea4541c040030034107261034140602074607405406420203030b001c1381045011020104141d41500c1c1e101d100c0b0b200000070002c00010280d01000c1c041e056030b181031500040041d07159511701c1258003403c0444419038403203450018044c7c040380d001011032005008224501e10080529602201e101001414641c0c000f11003407918420b101482d0160399501004056842c3c20707088403280000540080101ca00d410324000e481e9015003a00c0c43c0141c1e03030b09155000080280350301480302c40d10001e44030840800c9518000c1011410710094a08624280d20702c0d648014096455042e80d04803980e10b0316015244003445054040303510300c551060301500c25204946602980014240b144104000b400e0801d15410180310440b42d2041c1500811b9003520f2a003e50000030031584022800400c910355110803011426070340928101514a00300040e2100202d005a8032a0381c43c5442598200254008000b11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 566701762 1250 566700512 566700601
    0x6030c020304090c0306091a090c1908061c03020319020d091e050301020414031203090c0904030e06070f0b070815040e0106030212010c17040803220b 66
    0x20500180c008001c00d20680b949500050260030103440c00150b1240d4418481007203403501c803a005400e1802e40e40d204890300e13140c60740681180f40380c2c0030b036454520f44184807004908460780711014070000400280031a074402a1905016030700c1e00783e0b802c402c0c8403860000e4681c1e10101c450414820030007203000d20507100142c4006c02d01415250440b045042103001462011603c20702050300098040100701a01e0038001350004140e03c1741070710000d085110416050021580c00a00f03000d009004010103508005417550190f14243e40a0007551200d0030120f0300840c0354156190010800942c8a040100c25020700304114000d00d46400e26851310982111001030598a02d1075072403004012044904d06907205442a510321170000903515640d60110b901d81d075100181005030796480c9014040c264000040d944006c02125818400d80752035510b4000c140400391400c43c002188110001108034015003001d01e683e0002400a51441c12500783c0510283c02d2441c0110042900400d441c0d09140500d07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 566703012 1250 566701762 566701781
    0x121d0a11030607090f12050a120504060e04090b010e19110a030f14070302030c091207140a122004090b0403030b0d0201051c02070c0803092403151201020d060e010603 73
    0x40c10005190002480b180240500f0a41c7c040c06171a1f454000203041d240200c9113003581c0d84032640c03134528019010303103464149004580281e0910110100140010006a05503411002201103589a40c1d41049007040d03001d404480042c540344004d00e03019803a001602e503903c000e5400703010fa036080c0d4085405507901c0300750f0254404d030a42c01044003a400b98020b1a40902004240c508003030030240042c102030359081c2a14900d800002c014011004400c9541c249010191503140d801ca1801d14014191100e81a001e0308451040310344c0804504114404d0002220040003031007010514107041000c01c000383c4040b80820f01c1d04928081900b801d0800c505016016103500c4e0134203145c044804444c0303800c0103d001c2c030b50340d08015000000b009042040f011b0080341d80115140d40c0e5210a00c160380b50310030300c200700d001d507460003602d10108040201e0b5400341d800180200311411590100c3c40e0032102c98550440b950000c9150005400b050b401001110440c0300c5c1c4001d01d903610542582240c040c400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 566704262 1250 566703012 566703029
    0x10302040f06060c2a0f0806150a15090b1b0f060105100503220302030a090506030606040314070314010f060927050c040515010f030c121d0a1103060709 67
    0x41c405004201c821182c000c00000b15142844640c0294103501807940c01504211b1140d0300300035050184074810858035a00c0250f0300d6900c40100d0000c40000c0002c505849801e070140010340c00300c0801c9204078003540043c408011704640f07072140103110740c480d0f000f80402c02c0841c0c400c00c03020113004d40d00002c0f028103c84000d44004c0c05071031384c6a812580b030750004050390700b60301ea002c2d010345140142e905142070700d80c00782d40516161400c8890050560140d0b5101902c40c40c814810b10800d940e88208840c2141d83c0074408a14000314810001e084c0041c96002416a1580034684100c0310410b402810300103460600800480f03072615410011142c02c2100c8041403103804050074075000000c0030362140140a01c08462180c20301000180c1511003c898040b5403c41c102d01222440d60040803507194003100341810320100050b0940201892913111595408940310900c551540d07201b0750150520799a910181d410145040c14410403400400400300d01034441c21001a9546120342c040205460825 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 566705512 1250 566704262 566704277
    0x518060403050a0c080405120303040506100305030a0302031807240c0b0103140a0b070c02090903090927070306090c0605030f0705030c090603160e011103030a05090a0f0506010302040f0606 83
    0x1400121181364041000b241c80002c1040081400e40c0da0038204611020040019581c4c1d203003514045040903000b81c0b50307280003550240240009070700030013a212080041d180c010703125600c81070410400c040d50000102e060240c014007150106406210700102000002086218094060203c070f08007500700002d840e41c528107005000090b03510310844161141e90301141e0300d000258440070302c82034090713800301e0200c2c0c41c181c0c1600840c10b0002c04d4551100319040614240170b407650200e03607200d0005045601294032420a44000d6a04000da441c019890300b04840403d9143d141c420020040220148c5410000c401c000074460300c1803085900c10020032513183d42d140c440700d80603101500080d20201c03000c0410320030b40d10241c8900c80554030a0b20003200100301072842c2d84e00a000822070501c841e0410055400d030342c090990001c1100c0d000f081c1d11000044603941d00d50007034204002000014110814603003404148203000a2690680340200da04001148005030103070200c0cad1007481000c0100b2a40e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 566706762 1250 566705512 566705527
    0xd0201030b33160f060b1509030105060105030f040f26040f080a02220f14040605011707031b030209180105100e070804060609020d0c021603031e020106090f051806040305 75
    0x1360f03403514420380c0303d100040b072122041c0340043c0c5030080c00303865000001c2c40440d1066003840d09000703c0303810040030b00703104d4510300f03090f4684000000e0042000d00701e11501510b0400b0000001a91055200306076181c80034202d20001d50034080d40144200c0000300f0b89050042000c1601069a1580b2a0b00501c3d0b09124003501e2494407910030080c1306824610f84e01c0580500c810303000d002d23401d00001e01d500b51810310300d40313860401c04880303068000e84101d081401100e4492500010f282013540d07005620380450030075003020b040c101c403080e030002504a54080d080c0000c112a203803640c00b485040a001f40000d544512450405480d070b8410710144117104800301b000c10b0300600d6070940044c0a02030203d03881d5225040703003042c0d03071050500340c10403643c1c0c3c221312026030b0f8107001030030144940441c81c100f52861900e0003072240342a980000342d410114040100c400d8001d40c4507400070084c10b035051141d502e00e040804010282210169803415020410100d4a0030114000c0e11480e41511680d091040c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 566708012 1250 566706762 566706773
    0x210105040612020915092d01060e0f1f020607020f03130e090a0f03020c040c0908070905070c0b0a0902090f190b2106060a0806070804020d0201030b3316 67
    0x3001342811012200c1031003521180d031aa699494402c10381f01d581290150a401004406800c0450482c161080366800501c0039981c481c120a00c958411910201e04840000011304014120417110b614107110b031000e80308841e004102e007485010305c0e07001c1c1c410203d10a121181c1717a210b940c4042c4d060f1002c04070140031808108642c1c50f04881508222212510541e07594101c004400c80181d000d17a01c480e0f019102c901d03040c094814109228070345010000d01d4042410b036208850300815000546442c00a9040c5118200741040103400030b054a22600b17004445000420b85408103038000c1e22460001208450811152030050080001d0380a0348070303100311480014544103810300c0e0722207142c640508001910700c1d00b0320f5881141d9006084181007071420010340c1c203503d81c894005c07a0012020015995080503100c2e42c841d40544405034034030524170048006062482c4140d40c450320502d00320304a0342d43d03d0684804000707071003615048101d06140005450040103c1030084501400e0b004000a1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 566709262 1250 566708012 566708029
    0xf020d03150b0a1707090f090906181104110a0503060907110304060314150a0e10050418060c08090a170d0203090609120a09061107030821010504061202 67
    0x41c51441e28031089626101400416480425224002841c882d901c101000309182126000341040c149000c0c0c071464620408010b461610940b5031260b500e241034001e0242d1034001000c0c50384034241c2e40003802c0d2203180c04440c000020b21224040c0d85802c1000000c8d64130942103603003407031894940906554483c01003000608008040b0301c00c001e0301102052405004001420203000d9030780700494551558010314001c00c4004003901c00b0036001030a0742d07125484028041c000e40c4d413418040700f5555540d601602c01c00310280d01158009141100c004003030b1542d040a5080c843c89504207016400310080c04880484054800c41d88035007220038560001444a402d02100800e403501c40c2e0300b05140e00f08090104c0e0011242c0c88050742090003040010308051000c43c0c1c0c951641e403251410203c4a00d0020001c01082c0107041c01d114000c001030606404c208183d2005544c0005065030b2801c14000c80e9800c0a0504140d9800500303000c00070511745014010b01c800d0301c440d0348800c60b480e0010740030003a051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 566710512 1250 566709262 566709281
    0xf0203070b0d0905011103010b07080d021e030105010314091b0d08040603050405160e070503070c0c0306021308030708090402071a04030f11010506090a0e0102041e0806070f020d03 79
    0x18410658002603281e0800054408a5408240018000c0c02c078207140d42035960700b24218102030001c04c010300040310240c054600042d00311240307603203604100403480000c1c41030100c0d50710318225103040b9030042c50300000214140e0344281e80038003605110a41d84285190140e60460498008079601180b250700304012042c8090018096202c812264803140c2d029801508140c0009448004000a2140c00c02200b541c440c089030629034403514190360b10207400c801501e80d41c1006000408149500e02c9518011034941c1c0007000c11200039503038074000000754040c103018a0750419400c000114031601200381c47e01190000c0d4114070301600442000003c0d885001c08640d0070000d80030310004c0d40204110144114869102c5126108112801429040c1c1401c1c1d2040203a04100801616440c0c0d105406d401440c410701c0412103c8564018901900aa401c408190741c2005080c05a0358000302480040798005c200750380c8151076005040f0740000176518584e002d07a200d2601606440d100f03901a9140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 566711762 1250 566710512 566710519
    0xd030c0206091e150f0a0b01110c0910090f1d01020405090a020a170c03040302060a0c0c0f140d02061602070506070b060a050d030513060221252306040f0f02 69
    0x904d900d07400000390306800d469041c1504021810040c0d40c95403880380410071182420308540c0007155582c0681c1d030b0301403100e034140103008143c0400e07104142004040c001d80701d0408240030490f909a0808028420410001064814001c0f42a01d040c010b20842c1d00795180508030a010b6030b64038000c20041d41c003c190103820003a2241e03c050200d002100c00c10f010b50a030111065076420305040003854000003425042400d031419081c802c2158022000300d5020780e11a0100c1030001c0309007840c0415000550450f19140a0341c500704480c4e59000c160700d4031400101d952031082c0c01400000b2a80d60b421030247d1600003400300080e801040040607141d521410090075240910317203600c0803d00940301e454040b030100d1808509401c1d14000400903101601d4103200a1404084049103402d215840c905d0030390101500007449a210022050340508040e84407004a00b602c6c52860441c44d05c1c2020703681c410841d160000c0300c41500901280d000d0040383c10081c2d8003003541184e1039a40704030603142d1003261f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 566713012 1250 566711762 566711773
    0xa0803040303143a0b10030f1104080703020a1706010b0c0102070215040302041b120903030207170a0801091404140f07180e010501033206090d030c0206091e 69
    0xb10205281c4a25071404c850f82880b04200d000d840d09030180400030000090340c0c14102e000c05a034840300403540c50744c1054078000c1043c02140b6401e20082000c00b50003640c50000007808a12800000341c150100ca2003680c0170700d80c21b507450000c0d89110719805141d0030340b500140010024055440050140b100408000500e007a0030380d80080c10701c1110485410400b0000704040045d03107841d00c00c8000390380c003081e40b130106c8a00303140300102006415105e50560340d40d10507408082c140f00342d064440d0310341e0040c18442c2d02e0011503151138941e00709803410030000b1070070b0b000032454250600403100c82140030b585c5412562030b01d6454564502107511005441d1140c0890280764076420050304d00200301da1009914121480000c0c18140c90001500e001168104001000020319242ca0750710030400946a00c424101d000b03408010081d00c1e080013a84600c602d40500c040810049408071030f28001e51010050f4449040d020b0761900720032500c44030b403508050048011655100130350700040008070150f40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 566714262 1250 566713012 566713027
    0x803030c1e0c10050f0c19081506042d0303020a03080612060a06060f0504080705060309030c070b1804110703030e100c020106050906010503010e01091518020d0b0a080304030314 78
    0x2031030f12048816148182d034407001441001c0031440c41702138000c0c1b04200b078070b460003e00350f018040c0c1900b50300c83c16041001041c001100605c185104c6422903000400496499507611210826400704407449050441c3e1040d00b070340090781407185c0d24101c9515401400210700316840036184000700420190300403a189207a040504010b10401e880340740f0a840008003603040007402440d0460386900e01051100420090180e000c002824400b102ea04480070b580d203986400101c2d0030350098080d400302a01c0340345070100d03442d0845030242401000c0784050701d1412204000700300030707034601d9088080e9034503082090401107403003900031000d038130f021100301c8220344941f06205040b158503207200d0300142d640d080140043e2400d40340349a00440e091030070701d042d5410310f0041036807280103100f207480065a94161058102592080b8002413010618007003002101d001044042c0d4002c02004520394a020700c040380e42d1801220032010b50744080d004500703050855800392115228103440c1821800107100c0701 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 566715512 1250 566714262 566714287
    0xb1c050106080f0c0d140403030c1236050f06150901031106092407031d0a0b070501060f0b03150306010312120e03030709080f010b030307080306131508070803030c1e 73
    0x21405540300e07640000e1440a030f1500100000c10060190a03c40c0c1041e42d4020900c425100224544684188528000074033282c08070001e01ca80701c0c01070980c011200441004040802d86501c650004c1041d0010246a0000c102c030503002404014041c1c074140c030396202141041009820b140c0c0018000700101250341107440741c100c55150340c0c030707200c2000002d02501300769100c070500c00b644440d1054054040e100f00000340c4440304900078000004408903d09003448001d40180f00140b610101c1003003500d440b9800c98036950700c03c4820f01ea1007126400d440c4581e040c0051114120fa4004a400a5035060030008440f040e40307401403c0f541e80e844e9011100f0300c01d003e00c002c600500c81d9071200d0040503d0001c02078180f1800941048060b4940b401c45c0700d10343c8010080303c1d44558403546080c0c0c0c0781d85400014903541501509c17801e40c14603110707038000414082d00703010040d00c03100c50442d0f42503a9100c0e0380a641c1d10048510340100c00081c095200c49180ca209103145c00c4040300005410403030070b580034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 566716762 1250 566715512 566715551
    0x903071403010b01020c030a02151306050a2c010819320403020304030209041a0907090506040b061e040305030c01140c040302090f0604060b1c050106080f0c0d 70
    0x140c0300400e0300040300354285424414092920020300140810604c5200081d0315044200c0b006030040c01800000d00d03025126100b100da0102c28980d651b40c03060703201d4000a000b074000d10b60450120b11503480b50038450740350301c040094034033710400c1a4215840070001151036040280c901c01603a030101c02804130407640c0d03019114604501c604c1c043c29814104420700c4403480e051113400c141003015010311010036800301c1118141c90f016074401049464519044140c0e1000c0d06001c2550300304201400b8a643c1e0102d00e1304202e4004100511060301d4041c1004100e61a400c40b0680c8100100b06103581741104e030b2202000b0300c6c5003141e0a41421b503a074036140e085038056124240d01342d5481712a80d003800001884a50070480041c080303400c050441c1d0200e00305410144c150f4a005441c071002176240d54a580100001d8240c1400f542e07240c54904120f011b2500c003002080e02d5003800c040000c213210b0301c5a581580315180e10550328030141c0303a0a0441b096a8014081035200c540c541e2800c0415440003c1d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 566718012 1250 566716762 566716769
    0xc0809040b011b03020c04110f1222050d030e030f0a0c050c090f0f01060e0d060207170c0106060e0f010c0803130b042f0a050f010e1003020a0906020d0c030302030c090307 75
    0xf0b04260824141080112340000107000403164040c0020f840c0f5031403000654a101256600080150325484088130807958800301503409001c3d8400c035041082004a00540780d59080c0d02d0521032044440346040d102c0c01252450b2a5400c1c0030300031407010383d206158040c5110b00540c1a11001800c05011a00c03018040311405030308400703d801d100099124005150050174240b40c00c4c030314186d6820008052800300d03c0054042500800d0540c00c0c803000c05001004020110722080d070352810140c55034082c2640d07200300c50200e074188190360a2030528007060758180d9016510020100102e50b14640240c1028080c03140048811110b00e0000d490144054000c03030240c08001203500e0107201180c20201840d5241605059803400000c003511800255070039101e084440454651006004881d9403150115056001c010402e40707000c480c0e050b50003440743c12400d64a0081454840c48203990f0b03190721000ca10009480046e01c1000b091090f07003d5900400c0d9651800c0c1740c0004000060b1404072140c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 566719262 1250 566718012 566718017
    0x1805130204060f080702061f08030d02070510060305030313021f11070602010510090c021009030504090c1b080d0b031b0420040b0a09090f060602071403030d09020102010b210d0c0809040b011b03 85
    0x4008003400b0b81007041cfc0c1540340040d5010f00100d401c2d0350701c40b9207130b00000c0e000c081c4d082c910b5a98002155903d090050b28120060f581d00d0019010040c001d040c1c1c486c009071a144d5018056003c110140706015943c030800121700981c0d41d661800c400407008140e0000c81c0c004501070741c9540c4100025a004000b9894080c0e070718651203a08001c4144103d030789409224080c040044175151501041c1000402e0340c0341c00051307058071070b40803c3c1c40314058405d80c101e45905018880740701c1c40c3c1e500e000e403c2c09140501514200b1240c01c1c08440114003014040302c1c90700b40c1d07205100c00c21240760140c0007050207079550b10f0600780481c0c1d10032030003040d608003d04803c942610741800340700c0d09604000303504c020300010313488200217058100481c1c1c40b4880c41c1248402e9948848510003964000d41041500a002801c142e801c5511000d07514000702501070307101264010003034240c900921500e140e04080f40c2000000d450443c0729030400006140c06051941400b0780220781203400004e210f03003c0f119500a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 566720512 1250 566719262 566719267
    0x609100f200c040c020304121a0f01120f050a0b091c0306051503100b030f0103030e2710031203060e0c0711011805130204060f080702061f08030d02 65
    0x440003400200d01d41007051046802600e0621444800044126200205840000c0c00e0010b2103000c03801c52090360001e6851001c0380c44850b081050135115140d40000300340142046450703801c81421a07101c01c0c440c4030720342c0004011807008940c81113004c42c50503200700112281c01d41ca513514a00016001c0740c030051660130800074400300124001c80f40c1c24545451070108011170a2400250000301c0490b1082242603002c400641c00e040001d4868000d80100c01c0c4158480c9407030090449084024001180002d00a5681d140c89082c0441055400c117642a444403401401070150151024001e00300c8482101213400007000c00c10300074240880189958010480d2400c0c070340b00680300e14002d0140c0320a000208455000319003100c0264078800c80904c3c1052102d5140031108403c14000d402181d40410461a810342403915540180304650080d129001c0040c11241c05a9090104895035000350b00b09900080c1c5028808004c51422050403522981d0f09031150740d50341c6075821549946801e551b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 566721762 1250 566720512 566720537
    0x70b0907031509020319020901060f030f0501082a091627230a09020c030706060605070204050a090c06080a1805340603051b070605060114090f090402060910 69
    0x28840d103021400d1650b11b030118545a64042040c01c40148600400c00013145004604c80d84290095039280c036006806010b2546c50b001495203607141168150004240c00c1000030b540c2010301d03481e040310328004024440d19680e2040400b40145000344082c2005900c0c4003212142d44800ca200d003441601e41c0c0111541070810720b4504d200d0040d031203541c0c41041d51818660044c1d881d08411410f8940452000d611452586015842d500400100904042c00e141d03011031941d03448006000520300855042c089a2561000e00044445011015000320703414002408014080d10380d081e00b00d00c402c000041c42c5c01c80a0740c1b07004140c0ca0380c0400c95483d000b000710884544081840d45000320049181300989200d5406415040c2100d803140009054a500004881c8589001420803049603038403110399507003041c9071010040c881110b4840c0450800c440b00e40240c0c00550a40c3e2141c40301174451704654890b142040501c044c01481203038800000c03c0710400646841c1410380e5840c0190b169154502403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 566723012 1250 566721762 566721769
    0x5040b090f010207050a0f050a122304050f0d0201091a030103060c030203220804030b0c0c100b011d0a1d180127060e120406030f050c070b090703150902 67
    0x640e401c2032401e030300501036400030031000300b2904051a072100703003d80094218174106040040c0d015000c0c00001e011080b485609420855406098a00307014000101400343c1404e102c0380140e000e1a5000514021a04400d041480c186900140141403242040341e03940103611184800c0c0f2910b501d0b056010004004100c414002c00711491414142941541743c2404510300c86014880c20350050a01d00c0741c1c80e0103003c05001210051078114035242d4461810803000c0e00298400300c410700d501e105111030030f1003680461242d038407605816941d41d000710141da000c50003040280d80b5403c1d8029460a000a64203000740300200009042c403d02007403030b1800c0c0a00e54640d1015040b8a142d50b414100c0b0303d030440d084107010002c01441c00f1400ca000048500b0110006c08140f2011502d903c201c1c0d42e0341034500b1920001e8012960036070b60600c10b00200030801d00681d0310030313141602e03a104203010500004d51140399481d40b04002204507070102d940d80e02c4602c980001c4051400b5641e0341d840cac1300c500351b06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 566724262 1250 566723012 566723023
    0x909060306010317071104020a08180f030d150503070f0303120504080a110c0a030506010f0503210f160303050105130507020d08190e030310210303180605040b09 71
    0x108110302910a039071641e10340d05030b800210700025196080000b80202001250500c4001e410000362085441d10300268010700125020385101c2464040790941d00860000040d010f90310840c4200503500b80b404206010002e000d40d90044091544140b1000c50311380c80412030075005107a22403002001500e9824041c0600b4903c212000c01c107070414007040007080200003141c0d110191031a111a24600d031441031410114240c00c0c00d9400100f100d8008188440001c500c0d058440322010204400e950b034040580d6810a000380700410b1030b40308031880c40c440301c0750081c00e00703c0b1040b04418a0050030751401d108030281c40d032003200460b544800511050800440004221400c000108000e041c4503030069511004012000c0c10001d0300400907190080005242c0c4100b00112402d10800803603c0070542c981d041111007918811043c0800502c41030f10030700c03022400c200700e07c9942c9104a9520200c01900b40c068811003200c1c00c15400d00001036031440780620070b0b40180782c143d1041c20482d05550400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 566725512 1250 566724262 566724271
    0x8060f0a1b0912080d0207050c030f0a050a0b060a03080406030c020705060a0531061d0301090c0e04261809150f120d0804030801050913030507031e050909 68
    0x1010078840c0510340580100e55401900d00145012901141038680840c652082c2d0602801c2540041f40b00c0080003400a00c0c011440300032016251950008004039580c1e00814034040c2166020f03071b030b200340840c440c246030301c1e0011700182180503001d40700d0300e038950160f015a0005000039038828400c4605941070007000081d000807a4824900500404010850b0203000d51380c2c0802e00b1320002491000004080000507584a034070b0204540b60303121805004194030040c4000c0301c0900d05c0b61035800385810322940300310300d42c4444000c07038007410001b0403050f9030301c01401240d580e090030301400c6034032424058010708180349000701e5507124040074001320214103040016000da008030090044280c50040c9580d41a03609440310b0900c030307050100082448008101004550042c6c0c00034828259000c800280704902917196940785903661018003003480001c0b594051405020710320030001a10460041c0034072070007450a42074000c00c510650689c80c00503001c0e00d01146c0c00050250081c2450703014950700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 566726618 1106 566725512 566725541
    0x9131d07090606120207050a03200102180f090403051602040b0a121703090304090c17010b030601031515050c07091a090a0209030c100908060f0a 64
    0x502c001e0140000080115030303055607985590080b541050340c02030043c02c00c1d45460300c1c1110000211200000ca011806c3d112100910003400903114006030b030304a001034a2800c1040204220704442c401c2c1c083c44c4500200004a43c209041c0c44141d242c00515010010300c6100250007000010926a40000c1440300460315034155069044054403409488080c8103590341208106d020890707030791100e030b4030030481440303401d0f15a000208084164205140d2640c180d048001591100360004020400701108001c2c1640c0e040c0200c806800b0350300c003040d04007420700284298120075001008207200c3d002460701c0c2d8600041103520000c0000c1c0f10704002800b0504801620b954042902912450309200070802c0451940308940040500600800c4207494540a01c0300c0000c41c081000140012362500081546040c00980d1051541c0d00c0780d06900e00e01f007040304040728840c80c4c0f088070 = true := by decide +kernel

theorem cover : BRFrame.Cov 566546762 566726618 := by
  have h0 := BRFrame.cov_init 566546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 566546762 ≤ n) (h2 : n < 566726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
