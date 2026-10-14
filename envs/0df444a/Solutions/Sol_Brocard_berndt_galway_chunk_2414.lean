-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2414
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:10.107414+00:00
-- url     : https://prove2.me/submissions/54b25d0e-1f03-4587-b3ca-0cc2a3191edb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 433992805 ≤ n < 434172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 433994055 1250 433992805 433992809
    0x6060301090c0c02100e090c03010f0e0a111b0c03010510091e050106020d090f0f0b22031104060b0f03040320070e24031b01030908120103030306050d20010306 70
    0x617000f50030034444940d010b081c85904000c018001c5401000156010400c081036034144c13601d13182c84004140c90886a455141009800380c008580d5030f140e400c4055102500074420b400b01700f440e400140381c210140b2804d1408203035005000b40d0501c8200550b403000081d810041d00e541c540005256820380c8150b40c0c0d92104105002e00720361610340042221600001c1a1000f1070403036807441e03080f54443c0602499050980b103080c0c0c400c10240c80c2071010a0303485d00940001c9492012082c040380030381c0040300300c07007a690340203880340010b0350403200c80d0341024022040502410038000d40703030161206e8940d00c0d900c0001c00140801c100180006010380607080448400f034901000c4840040c4c90701c1c505a94402c1c25169003060100d058181c038140304220304400074001000780500a10941d00c421001081403404000741016a10058400003820fa540a0021509004c5001040d0b60440c9030180854406030000d07881b03101545000c0d070016000015482a02c1c000b07600580079400c110005074045d080d20323 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 433995305 1250 433994055 433994059
    0x90c0804120f300b030a030503070815040914060a0608060612031b010209100c1a0c090a08060f01120b01030311071a0909151507020310090b040b0c0306060301090c0c02 74
    0x400b640c14800c50050034500f804020a03402080b42140042c00c050b900c01c00141c006001c101c040c0000303098180035655a55001c10702941c1c4650142403500014112111860121110400c104052101e110100000313640502c0582040010904014411740e5422000301194454080d89840300c030303069010702c26502054003000e40c120a0034420180d1074044d41101c5003d901134000b41101c1129603204044001260760400300c4d90000c0c0d81c120340140d0b21108024080804000c00301303e140300c5a211101490300901059028001c5802e00fa000c8202d144010307840b4440718140d440d15003011941030004d0604507a4075052000b405950902c143d81401c00f00e41c00105070a146010000c3c80821003c000e0110a1040351648aa90b81c1c20100690310056a11010342084107a900480c00d02c58160080c800d281c002003c50b00d61941d400f130188292885848100d40c1501c410703041c04100403804c49041c5d00140c0d4900700c0c505515080c030108015020501ca019621500c40a50510f128010f0742880002600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 433996555 1250 433995305 433995347
    0x607080a0804120201020f16061b0302070606050604080601051c02150403260307120e101e05040f03120e0604031e050c1015090e0601090c0804120f 65
    0x1141001409214040b1002ea4071254081c0000540340d10603c00c4540c901d40c034040b001d04141c1291001c020441080c607003110207541d031b0f090740540d45100c0400c0441d0341c1810742d000340ea980c0d650714211007500d1040e40110b02401050009105100e400b188c6070b419240d05175030380c0088a21000c43c09103c2100044040c0d003040c2074041841301e8078540e07001881900c0c01110749411001c07000c01169080c0e071190000040010052000c12a0a44101d0f1000c00582c1b50400c0031440380030842d805410807910201000003299104170529006041078500c468140f1088000c005d1450a81c4500c04414000c844c02010811007c52036000c000c4264040d12001140c9030482e213062400d0b02d8050711065012000e000c1c600c5c510001840501c0c4200301302d60020705408054019040c62140c4040500131486400c503c0100940e00403c0e8075290340320351542c0411540003041c003540361240a40c02caa8145101c035080000880801000c5030409540070300b29901c0b803030200740d00710704003a040721210007100802e8101c4070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 433997805 1250 433996555 433996567
    0x3020f09100e0a270f1e05030c01061505030106170414030703030b130b03030405042d06060e0f091303020705041d06091c0e030c0a030b040b011406040b09060708 71
    0x2c41e132110b009400038280142226003401003240d07048014603001010002041d5202d800900f4020f61003620179008100000c10410070f50b202401c58202ea20201c01980d5a41020411820f0520201d100c0c0591400d09034955410a14010040c44104914010042e1010080741c10490484a81d00542c00d200c410707030b0303164200c038507008000e048113280242c412081410100d5034150b00d84034214a803000140150b181c80d207402c0034800500125900036038400c010413103001c20900c10000303400e481d852202002800f13a040c05030140404001d880e07842d00654185243c4c0d03400c0e45940f401d02e504445100c0b0030404104880c50124504516900b0094200d130504451909605036140342d0002182482e050b10710968074004d0040e0344500300e0003804074001d100000700e08a1030041d0f1580100903030290076120014040c101180801215070300803512403101000708410b20884030f03c0785001d8400f940d10381c0401000c2000240240c02140148842c03114002402001c0c1c3da40c85040f1164640d00c00360701511a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 433999055 1250 433997805 433997821
    0xf030228080f0108070807030f05010e120a02060c0307050a12060503012d09030503041b2c07031a2205010e04020a060509061207022407020c040603020f09100e 70
    0x91415100100001d1104002103507601000c1071780000c0c0c03409200105010f500d9501da000314400b44210941d055543e600024401e00014000d082903640d00c00e010642d10001a80d00170f107080402404500039203028030070b03c0b0b00c1a0780a01190288082481c1c100b0200100c240040010002980000e51543c07900641e110300d5a072500b080141d604008000c0e680b007000c1804030303800352a07008a000300025402c100240001d01c1e402070a0001d645c038036a684262644603640d030100c0100d04804512480703401607a900310000c092150340d80c40719003460280501000300e46d80160000c000382040d84030320100081100114210342020403101003c00e800c1c00316507542c000e040c1c8202000e880503401200440e4002c10b10034041c404a544200014264521f0030040c3c0c0d400c0d01c0a41009070080013180201d001403604041130595050050000382c00c1c2030a54104107138040c4c981040c1c803200c2d5000e181441c0003000543e0313404440c1d10000a0607507214a5036600c00c03500d80c00c0070707230190001c7d060301c001e09052000c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 434000305 1250 433999055 433999067
    0x9040f050f10050a0e060c0a0c050f01110d06081f050a0b09040606050a05011803081e2a07050a03060b04110a030605040506040207050d0f05190314010b0403030f030228 74
    0x1800c54940104029015050320948580c2e08695410b10414100300c54108c1910440900c4036080c0a0702c01e550500f0305142c02d941c00d4400c9060704807051000450b1410800c07805c0e04c91440104690300c001c101034045007034406103400050428045a560b100d000030900350540c1c000040e0260000c18000e6645003034500303400100410300071b917406250500008a00c55014a03d40503c005c954061400d149103940c1d40e00d003c07035004161031115654400c00840c42c0c1d10304070000d8940800040e102558100c002d49a04442039031090210384154041a420040b60700c48040900c10340303802100c040f9040024a0118014003810704589008038000121036054035032542c070580a4030340c1100e0511103034a50324104000d03802840340c082c0464021001d01c143d000d01071a0040e00c402c03401d0618504025a03030742c100100c1124808008003203a04c0d404120540c0582c03510a42c09000c8901301d0a0805045440003440801c1d280c000c1010302d0b074000303021100240035014814141112044460445000740001004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 434001555 1250 434000305 434000311
    0x60303020a0b0f07090911070b040807020f1c0b04110a060807120c1d03070306050c070302120f030f0745060e0123030f040210030203010509040f050f1005 68
    0x9904a0800810400c0e920519658019150fa5031200300d0b640c201021ba800411407200c0010403010100032450000e000d2030201032060b1700480c1b4a50f10742c001c0340144a224400c00c82c161b403013031000005000c1078103500c00130b464001c1c2d0400300f0f009107695a840c000341c02c10743d40c00c5465030041c0c3c800d00010b02268000207042c8502003590f14000c0411800414800b61100c2d0b00f15140418003a510440030307010340401c0002c41400040c00c40740700e19665211038084400584206c0881d01002540400b81501042110502008956030501c0c1060b604000a614000988040700e81da000001084001e44119240505082101c4070b813040c15450603003a084005c0c448240d081c1301c1181216031041070301d044e03103c18101c410940307600d1402480d900c01192000100018522007540810b01a10701500520145101d500190310295042c181401089100d104560316141010f00400050180d80c45008003079420590242c00301a00c0c0c00710345040784c201894113038410a14407460035080050070440c0c01041c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 434002805 1250 434001555 434001563
    0x112020d11190207060309150f0b09090102091005390f0606042318011806020901090e0c040b070807020301090b01030b0907032307150203040e060a0e1b0d060303020a 73
    0x1d010740d175a1082d0f0543d1400c1c000a4001040984d50b610007408640201210f810101400206044060001110414103442c44212a98080b414501d41d0030310f00001c00d015082d41c182203051000c441803c160410560b82c1c04030300d81c81601100d148d0181c800f0348045903000d98500740c030005110600d01c0c1c2d0f030b0b480040721707818803c50602036900740e000c0402922060300d0784891940c4010b5642c5040f0652040791840c0202481c2d03685181680c00e004002510701d0055114000150740c0720501000186032207115040725442c403162005101c011802c002c200c40171900a140e1280c1c94105c1410140002e000e148000f0b5019400c1c8a414000c12510100032810b8910585020180e40c07102d8290750303900e40c0705010090490002c401e411021140300b141c2c0c540641408022544140d89458a09400701e0b001a2500003503400403c0c10b002e0300f680401801d1784140c043e2520100c0314a00f44502003046800713071422070061003142001001514440844a0310041e00d00140720003030f601c0c03500a660b507400301c00a071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 434004055 1250 434002805 434002813
    0x80a0f02030d050405010f030e07080a08031b09210703080c150f150913020607030801080c03031305090a1b0f030b03010e0d0f1e0c050f010504020112020d111902 71
    0xc042c0501800507502501d4040e52081c04a452500041d402840781e0118540c032032003110030011f18000c04022100489104030001502c9081c150b40444d10f42d105c0300701d000000001030003442456107070001c0000c074002c3d511a00480c01402e00580505002c003a40020384030f640000f44003175070004001030350510b40044020342d80300783d522408501c040e650280c4402c2d10640c011a108406481d01660304e039004501840403480081d1598005241c90744444411004100b03071000410200b9002d01200c110040309a01840c681b14813240d0000d60668a0300401d44034450701000310b46190b11651260700040c00321070140021003210800500b00d8481101c5e490300003400c01a10ba412410103004051205c1601d070018921226005420303518203452081c0b07901040840342d92800c1100c010140c08000350f820f6103d500e5410000d0811b14144144045c3c2c20b1305583c100000d010060368400860310350f400a40e0300050304c0d00380d800e03a10000f5100142c0904103d0002242806481810a100f03041040440d0226 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 434005305 1250 434004055 434004073
    0x180d050d1e0b0f010c0b0a020901090806070809190f1203020d06030510060603140103030f0c120315090c020d0806030a02030106140111061e0c0d090507080123011509080a0f0203 78
    0x115807031605c03080010a413005900c00b294940180342c01400d1030020504001d940e4940340e0755110702d0008102c5610002419010500400e020180301c084002d0317860344014442e01015407550070b06080c0d500001000e40070000c0c566200c1503ca681074410342c030829101444020340d603040807a9504c1c041490a40014540b00e00021013600910480b004c0440f095203000d29a860740e20f041da00e000c0201000741c1403101c1d0301100d40006015140c0f20000c0e02d00c9460019051080c049003007841d03140754024001c080d1030070890052203038000442d00404145445e003100320f643c403080424205800401c00035059803c220740410013104050781c00c41c40300d0082e40c81d00b07803082a060f101990307440f041d505098203d0001d403034044d49401e040341b1240c0c42604407268500d4280006070803411242e20702401d540f5604248800e00804c5401e02a0409a14000c0f0f262004180d0904105031000b0040c0704601c00c412030620943c9606019003c0e410083c9040d200380c915600041c140200144082402240300340604152 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 434006555 1250 434005305 434005307
    0xf23010606020111160209090106050a0308030a1803121505130b0907020c0a0b090126040213020a0e060c0109050102040b04030302100204030b01050d02030f061e180d050d1e0b0f01 79
    0x1511492179411710007900b2040c80e6001d0050804014003000b02554880b9404201a00d6507081c0d06d00035880345c01103e40d40d00c2d20081e030400b2518140d103071498040751411048040303540661982030042414a002406407642c0d14210020481d079400030390081103040741e0a5000001d0b03030105400c500b085e900e0716000ea403680360480e00c40b030360401d025611088415003400f1010490001e44034110041c10003501c0041c0d806034020f0940d010342c0400500c00c014a041104504141f5022090381016103c00c0d805c2036001703038014100302c9030a0100750203030710085401d04c00600c00750410040ca54211008569a0791030300d00a03002a8000d01041d40984501012070310107060070b1088a088036004820740000c0e034240410460401582942030f44d0603c03c4006020004c3d00a11031140a030702d0640b0b4200e025050f00101c031f00710341030041c1854010030202c0000448041c0101c0e42200301d25032880c0043d9241003007654540280f44019044018100c4160361564181c01c0b40d0010345002c1080365605682d0b088980 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 434007805 1250 434006555 434006557
    0x71e031b0f020705121c0302070f08030115030509060a020a02101a0901120b1627090e030906070b040201021903020a0b0a15170f030d2c03070f23010606020111 70
    0x408005c0d203074030290034609a0010300e60b8880d0001900e2070054035040d41a01ea5030050300600d80282ca155000200402100444002060301d5a00c64182800303140752030716050b038542200505806000e0f8002aa80f0b480c00e00c03c0c080d0804c1801a10070401600394860300f048025110300ca20640923540d1b803400425003000c0b15804120066100c29402d106a032004803da44104524a0010030303c40f829190701c02e101040111600300280d07082034500071518102c40e820079101e0703180032100c01b41c1007080400d00302e0b01e41d41d04440070b06401c0306805210751681d00c0104c1c50304099000030342d28850001c0e20301d020103a003c40c2080303066000c3c41003a2101e44448610f00200c415128403025070801910701041400d0303600c0210700b03040640034181c840082d080103490b401d541c0030f043c2890102da541e0491000100c510b141c440e0010044561a0100e58a507258817540c030310442e40c016101d4502941080300704401508180d0040d04009200008041645202c80c0a042c20b4090a0055420114045081108a8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 434009055 1250 434007805 434007829
    0x1090509011d03071704051f0905180103020609060c030c07030b0f06010c020123040e010515031905060d083007051632010e0105071e031b0f020705 65
    0x8405103213400003036030312031242884800c401d020007601071000080b580c1c0e8900901260060050902c7c5100c0701d010401801503c241c0c0100d44551310b0f0582181c0c00d80c19186013581901d505541c01c030b545407504000900940201d40022841d84400240405404004600031040760720038038035481180c42d441000284160201e420b1400158102020405503103d412240b0510000031001b912002d1020f014000c56801a00a104001c107014010016802d0005440241408449010381036017000d2810340d1002d0030050002c40c07440e48030000b04050b60380301805101503540c080300a070343c3d445507003401c10000320800a00501010304a8400400790f017203c10118401c44182e5512481c1100f4207080c00513a1103480c0c4156440f002d01d48504140d10f89034524024140d10100014116920800406083d03419103100076429905007010b00c9080c540003400c0081c110302100000d00c1e130300d1489100300c0061201a50511860380e400e07001002c05a04900c8e16442540707141e081d11011501c81051100c50740f900d0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 434010305 1250 434009055 434009111
    0xc100209130203040f200f0411030c0a0e092403010c0f03020711030105010303020307020a06020c0307092a1d040207080f28030203010e0f2e09050109050901 69
    0x405001080381c1010b50041d03a10511038808002201d140da12402c8654000304010007500100504c0004a481c00070a504070006017101c0c2440450005039068805020181a80d601207001042d0041114001c505051b0302e02e0020b0000321103490b01c5507601c1e4510210a0307404500a4200500081c0d0b41418001d01d0300c1131420340c80341c0c8200c03041140101c00a600c0031409544080550188042680c0e0030300805008600a80c000c6403240000d004102ca01100d96000710299480b117690315031541c0700494130404581e014007000a00f0428a95140c0742c20707003a410f10b4000810400324130201290001d203000560380190180d2a48210110180022880b5013840544030351800c0c400e40c0c408440720300c010111010580d1340c01e00c110412a486803115441403641c0408a5004801803240203880c3c00c20582c064030840907452036042c6108100a200180b0035010004560495068400002c01820100070043d00c14100310b29a5115014402070200f50380c1118075500b07142c4184a0519683c40c0c042c040010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 434011555 1250 434010305 434010319
    0x1a01090e060c0318010905061e040c0501080403090305060709080c0301090b0f060315161d0609010c0311030c0a0c0603110409090201030b090f040218010b0a0e0604050a0b0c100209 79
    0x2060042400750f0401031000c66210300060220030300c90002c0c0116040d0501c181d00400325401c10340c958010783c0c00c0000611521084240400012501c402a0300d005c032402820281101e40f1182000c07901440680c101030400e110b80310074040c0784e9a1003001401154084001d9039011030740f02e400c16007602ca00b2340014046420400220b5056440b5402c02c50300694018115060310300b605410520044007118805001c595940c241d4015903004550741e84030400d44400c01c2109815000050598010030301a28108401200c02800300f41c0104603a1040ca84e403482183e88070041031103050b80d00c240b01c001c122044000100002021070103030160210303100c500c2000da4102810043c01d04e009189145062b41050307107070f00c248021a1202140c0c24003402256011074554941070050007141100c511814510742500d500410038821003501740c5014110901c1d0405c5142c180d2000a0550701942d0019548120303202000070f1072401600c000c000c0b1609101c01d44207050400100744c012401107038070321a04244 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 434012805 1250 434011555 434011561
    0x70f030818070506091c1a0606040f060302031906080706031a0d0311070b0301091a0901260111040b042d06260a0203091b0a030209070215041a01090e06 67
    0xd007901c0941521940034000c008142d031031a8806c406016034242c03e540603482d0240813243c03507540d9564194071030742c242e40e2580362034900703018a5040c445a1203003004242d40800450b8003006034001540615251744010712000f600c9004540e00c07194180302e660007003454104000134654410b646007011313250080c078420303c00601c2d8600755406043c2c004166200c0c02140408902c040c1d85002640c00b0344190784001500900101ca0362812241030154a84140050001040b003200425107140d4075501e004103c001300c2c94003640ba5400340c2207800c030706803081d04003090126003015480c002d401110345042c03400d0f01c00007181c01c4091001e0080f6000140a2003055414448140264008500e4409481d4422810505201e100003180e40c00d0b03802400390740c1c00000380300c1d50106c01c100514a041035450b0580780e0790400c10005454200c0b0b0321009009801030700026039814000d1101c4d000900d16502d155241d840d1916020754003804c0310206004020800001059201042c82808045500c2034010300c6d0b151 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 434014055 1250 434012805 434012809
    0xf010b0901090305030a051e0c07030602090406050a08100b090405030901081801050a06030c1505070b09010605190303080f0f07030b03030c01020a02161a070b0901020d02070f0308180705 82
    0x20348000c0005060220024000000900c100004c2108568907900e0540315414844007105060b102e014103050300740300b03000300c83d0b18900200f41c0b041125481500103940b040040081000b40c41340350320059000c0c650b0030b000203c500d00410003288403501c1c803100b00500b05144082000301401610042e005070300500080d83c0320f50041900c41c3d045a140703d29401d40004050406003980e81c200c4410580c90b841e52001c104110320b031401c2d00d000d01007202c214030010105650080a5000e900405050341741070002003580d100c03080d4030580c051710b40075025941c0d0300e55020007442001120300c001c80000c5e941000240d0420b9420340c20303e0180c01450134450f026110004100c0250040304110f60b49808100040b0303021060034801000d842c4110f070042c1c44480d4424403112074549444e4420382040d60410740070120042410201c42213290320212914094a40001c001e0080c043c0603002c0314080d20000b01481400300c0e00d403090503030358400e43ea004899543c00c00003030030b0401c440b000508541e00c000d40901c814 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 434015305 1250 434014055 434014057
    0x1060c050703120f02060a180611221403060103080901180806011d0f07020d0c0c050d08040510030c02030d0e03071b0609080a1110030e010903080601020f060f010b 72
    0x980500d0403114055103a4440a607000c02d000a0300300801c085030041c000d101d40501c84a030b84992000010000c2d9240005500d100c0b1011000090105686012203000c600103401900c13080840000385940711a01d840ba480400f030241e0283c60303011511031440150a1500040c118183c039401400c081c01d02e4407090041d19568800020411150601400494032000400519008200c0e010401d161204040034180c85200040c1c0380b80f00c050005800c2200281c1c00043d91044010a89005c5480c42c11301c3c108011104511f40000307510601d031051482c00d1003101c0020340266038007107e144001c050401c00135421035007041201070141e0801c2c01031440700000755000000ba00104800c6d03c4c5408059030f02c8411146d040c4030b506000400309102482200c0e403004044002d071052600070104150161161481070900c503440750b00c584440440d5283c2d0728802d07080b9a81390702c0e245000340109107580c039001d801d04904a48250052042e01c02000031001c0c0040c0403402003c007807040400f5a420040d1040031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 434016555 1250 434015305 434015327
    0x30603140d21020d0c1e021504120215010f150206070e0f04020d02070b1b0a120209040e15010501020d03060e040f140304031a01050a0605030f0a0f020703080f0c040e0106 75
    0xa4950900a10401061a01034048444040c0e6101a0321b41001000a00801410368076441194804480c440300c60306c91401031a04103401404101c07622810300c0c402ca242010100c4600800386400c0c00000310480401d210f80c0c00d903517440c12071803032a00300d03c03900703d0303136110121851000a08020303041c03a80c50a010a00c1d4540e403101078070140c07500400344480020780c0d0084404036060002c040c1040046207202440980d80786041c0f180c43e103003140e0400d00401c95241c0d12480b8100541c0007803120616600c0e80d000d000c40d4070f950780c02d0b907441503401040300522010920405016005610030450714600c24401c81040c0c0b0080300240c0c100703403039071780301e500c00c060460008551a400c01c0340454070300344080000c0d1000354030480c54940551501d8a0041c0d03404410b82c0260b00881181c1e400b1b000300c9070040c0a41340c3c080c84902146c9810307540c6c203041d80c000d0308082c02d105201500c0050342001f8164401ca05520400400c0d42048680e01c500400c85003c0c802d40c807400710700f0000701c001800401c0c85002c0e5900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 434017805 1250 434016555 434016617
    0x10e03010e0d09080c040203010e070e0f0d0f200a0303141204050a1401051918060c111e150c0f18040b030d14070f060606030603140d 59
    0x300307030140d404081c2c40c1500c0c010000021aa80e901d00304881c1200700922500200250780650441d4903008151405110182408083c8209103e80031865103d80f6201c00c06d54100600168030441ea60901d00ba4400380c0940076901045411403110009403080720001c0b030340a000e89880041b600d140c400721186110503040d040143d00410090340042d10604600b0b009901030703c0944400b10341c03840d20000a2103955061751325a41000200103103010100c0c04441510004403011854041011030b400080209090041c052440d00420781156035100c00c048003000c2100701110901924441c144040780c000240880035a40280d05001c40d010303480c0302407508295403c500300e09145519041c0714a03a0091040001c100c0c629140e90304a0703190034020f0090030348054002d01041100c00e40c0041000340042d0450302c000000054560401640c10b405060721604103200300081e546842c402000303868641310503a1203410f42c0030011842000400d0b20008048242c6803107424246102d030064007031700c00200c0c1103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 434019055 1250 434017805 434017811
    0x1b0f020c0303040f06021014042003250e060a0b0a050f04090f1406090f1e10030201091512230a0b0411120c1303120c0302060c030f06010e0301 63
    0x185450400190018100c0e620136608460f040510081ca0031201801200b401c0c0d0505055401921800030314542040e00314118240c84010004007030b1034002c001c0c0b15150188901141003050880000b21105520b40e13590000407280d55070501c44044040035584141d020058890811a400200c0b000303050584060401c14248101c50004090a41243c1d001243e01da4a82d00241c11704040ca01c00c0000b02d4080085003051410b00b0000f1400c1c10700000d1040d02d03c40c1180f40800c02c24020343e8040a038049500c841c45103640b92281103c0c508034440d100c03ca012072440760022a000c0b1001d1407100720a110303036071803041c495050b013014009880d028003c14401e540c083c80038201d066551300b40c58415424400c0200e41900c2c01810301c0102c46800385442c541510600030341d03a2094500c155190010208440240c41d07040001c035800c1c0702c9150f580f00274203524030380402880a58004100490700e078040d4007900c62a030381c0c510481c0b045100407116501059442d4000685660040703101d0424420054000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 434020305 1250 434019055 434019073
    0x122a120304030210062411030d0603110a05012604020f04110309100c0f0e041401030b070f090521120c010b030f0109030207050909030f030a0207151b0f02 68
    0x815a2a8000e07a01900140c100911040e0350040d54010300c802004038032100125114030310301141724030301007510f94000c0080c090401e44410504106480c810364074080c0410a41d650380c41c054050a03030951845000708090840011598010683c5000c20069460020380144074114420100e040042c4201d2748140340d0f1031a0fa259448620401442041588440360f40342011840c0c2842d10304d906010340341c0c0380e0074040446911584040c540e00b11800074100a281c540c1c5210003d800f5200808250000403070820001060152480941c0e0284500741c841001d885d1507200110b0310722045010302038028103820300d1414205801010610254148401e5581706072565007042120b600a001c0c1c884030769159446c504441c0307000c0c0820348900b10401c00800515600d540c0280d16010907100d402e104403112000144607440c10720496000156002c90b040d42c0740b0303091004400942088030180d5210b610035604c019810424410410882c020030019601c10003d964212511644036101d002107018103c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 434021555 1250 434020305 434020333
    0x60806150d03021c0801030b1b19090b0a03050610050405030a030503040f02121e2409070e010e040c0b03070e12010b04060308030a0c02030f0a030f02090907030608122a 74
    0x4000040d55450b504d05d4559451800c1500c06220040c0c130420803c80300e103000d0003802050004a4500c2102411450780d500b00c40003042e114605540e002c68038140001858042c2c80b94194461449880c003181c3c6401030341d0044034101e6541c0624000c07946c060388a001c1c444003290140000d9a440342c031131140814004550380c082040041905a508141c2d031044107240c2d040700c80610380f10144100760b8000c000d51035103850720812001000c035200d084852084003182c00f0003414420f40c0040c12112003015003c0d6035400903500000b10494041d50351500752030000c06d40c5c078414411640a180c4039034400203203180d034808000740c1c07802007402643c45641c0d5598400c502d8440303000d064029030040221030b4503860000c403030005540e1038421210440d041000380c40b000340182406e4807880740b02032070002005500080d203180240304540045510a58210802c1401c03645a0062420381d40e0340c5066401361041000d540c081400780c00300c141040d04208420003858001482c0c03c40560f0390003011500302c1c0c406941c2d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 434022805 1250 434021555 434021593
    0x705041415071b0b131203090509040305030a0501171507030b03011d0105060d0b0f0402061b0105040203010c390606080a030e0a05090604020337060806150d0302 71
    0xd0071560000c0f80040d42000e240100c0400c0010050001d0591824095031206a4501e106014410f84c2c125600f04007410326101c3c0345c007040500009400a1054201420050044e8004889000f0428103200c0003145040e02041800440a0f0500041100e402d608066030004a4010f281d00304040e40e480f183caa05543c24051414248d040109400b55415481130311030030750b00014402401a0154080303034000900490485901404281146480b034540b440060103610442e00040c0ca4444a508801e07101366065000394080c5208074000c1015124000c1e0a68014140340c00107620340c4110402ca4440c00c00400160f41e1582920790100e080850903584d080840ea00b030340103914a680321440503820541c10001c0e00c0c2d8004001c9401d443c1c1d0900d00400208001001000716001d80c0d0003002043c042c10110404804403040d0520342e0103002c40007060064500c1c084e050072070096040c5280010400808902103001d00808140409008444810300c903259900710411001c6219004c09a0b0405180c84 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 434024055 1250 434022805 434022817
    0x30f0a03051b1303020406050604051503070e040504060b0330072109030c270209010c051c03230a0e070b0301090209040e19060b180a0e150705041415 66
    0x100303e001142076006000480d00c1d10341007d80504020042400300c0d6648a166002d4041680955650785e90fa22000311052100480590703000350404083c082004015080640d80d0401a811141d031440080c8030030290300c104038401807044070010780c079104484003200240310181c09407681c000204901080c101d00c1d104419519000110100000e1041020030124540100516510004880308030f0440040d4181c081000144c02a80011100010790064034210183e540220549405508503003490035404038010200e40040d02d458040440d50050309441207406008101c0941390f551504200e9001b03000c0b1000d0014148203174140003a070024100000c41c00f80c40214005a10b62119a052005454000d1103241d03050b000b000c1e19280c3c00300d000e99521070740ca41021000c0351020008010408110101058240e108650b0003001218603031030b00540400313080030302222640089607104040342c80c002e90303040c07000610402007085404100b1381003100305040104101d1600078003000783c80103036002c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 434025305 1250 434024055 434024077
    0x90d0b0709060c1203091712010305010c020a0b0402090a021c090201020c0a0b070b0406020903240604050613020a02070506040909020f01051606110d02120103050609030f0a03051b 79
    0x810800300950000c4070200034003050614400952050ba55066036546000080c02015500c000e603406000707403840c0e000807540e854040240d6901000c025225165406d005c156425820840d584111901c002250600c8a42007509506030307031607135800c009900750054800c2004580034058500038a590211800300408036006c00147e0f0703075081c2b001a04114003240d96070307c1100604406c102d0584420201c5140c00e920040e5200703181c0d074030314159000703010f402c3d130583e00751050003103074207040c409541c91741c0390100340c1c1d940601695202d004100036107008840440e00242d03503a41f403203450941600541502034050042c0c801854490300421121340056002c2e940300c6848030244015410009030f040000d4800380b03499460480381d51510499031040c490011314080e502c00c034448100161800b074514401d6001025982c4035610341008000303c0c000e02041e24240070325030210b80d5400e00001102c2c0d80c02003441c501390419035404015001098004c255840e0302d000f03802402d900c5460711005100c01e03028 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 434026555 1250 434025305 434025323
    0x111306110d0206040b131412040e10050a12030203070b0c0904050a050606040b130518090d0c020102150a090b07030f060b040513090f080426010207020f011103090d 72
    0x3500500e408201d0590009540080b8203000100d035a1000c05544044588200d41d0402d0f95803601c034520b00442d00d561600d600070950011403980c030700001030089460a0540110301d84075020441180b90003480307466800461814104408030411307100e400000d0290055904004a0303071101402c04808541c142d15619000640c01e81d0ba2405118240d0019000031041000d464943c000c50b100380f190380a50380107030a010031081d22403e0f00076214000f801d0042c10301c1e4802440d02c4e81d2500200d5003943c05040c03a0003010510909280f0541120310495016070003040f00400510402201e2040a0303c2038650307a0300c500e028404a11a036030814058111581c000824160b007a0b0840112589a0031000d00044200420002ca030343e0010188100400c070b1500140c02509403038031a50b01d14405000070040c0c4004200041d42105500b11800c0d0204102d5101c004050300d00d04031400c2703220b8440003c0d0702900101400505511a094010010100004a920703001c08040096070300550301d2000c440a400e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 434027805 1250 434026555 434026577
    0xc03060906060e0a0903090e0c04090e0601060e1002070e04110619030b0a0302010909110c1009030e041e1a15030117150c0c01200901030c180603111306 67
    0x214030f803942da000c2641d0504200c08a00703642e00500300d44540c41411b042c2e0b103020010441d140e6420040320001d001104c000c02c001c490000041c1d03240e800034818a00807903010a203504003824900c005110b80b40182d030152101c1402c01007500c8118002600075076019802100880c426201c94000302000d030b01c00a96000c03000310a8000800356094480c400340078604a01e81000140d0b00070108500743e070349040001c00c07108030303003200b10100740140154544980b040c1140303907410350200d5001119503030103a99490b55070038001c0f0522095515418010f40f0364035070f499640740403201550181e40813500c03401e07074450515580c1001410b540900e003819078203074000100401554111440e800c0004410602500d81d546005d02c0803030032a0001002e01c4024540060100c01d034134020b6100e580c03082941e80d20309149a41550a0726040c1e0065800c06010a00d0183c007134400d6401440d02107414042d0769880d00c85142410812400f4000ca24500b9000720030074403490106030440410503001e081556146d0817030b01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 434029055 1250 434027805 434027819
    0x712060b160606080c0102150901140f04060507020316080c16060302040806060901050609010f0e1c0302010509010515040b060f030c2a19050a050d020607030e0c030c0d0c0306090606 80
    0x3d00e955000c610315a01c000d00e42022a6004507441100006000c6000c4d1a07589813007406001d0b08030386c1d5210345c0d0780f5021000c0000808005403664042c5008100c10045aa03600d501a80e89115040a640c00445e001003804000b604100003048000c0c204000d54901d08a6075601c00c00c0c00115410150100742c011030123103c04001000312590052085460261a515140200b91f01e0702c0790034641410800e20a1680b80c160b40204410b04018030050400d40640c0c0c20714980b03a40c01c0d107220900f00e0040d402c140108034218414010540541d0160948080c0c14504600300001007000c0e00d0900d4001170309200c0000c1342040d40d40914810b20750000c1c0030307545d01803856000c1c44209410001400300c911110352102c40041c00101c3c1214000009490321940700c2d80e0401d2890210f0120004006204040240340e550303901107a402e002d03d8403600c040c841410f0384440c090311040000c00040d010307030013184001c22914160000309030650064040840064498640c82c0c26141424030039a040c94446000300f01c20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 434030305 1250 434029055 434029061
    0xd0e010b1201060f060302090d0c06020604140a03300509030c0706080106091404020702030109030906091202030a0b07030912020c09010b121620061005180712060b1606 74
    0x28441c000200001810240100c1e24003c250103070302c080550202e03a00a80b6160350040005e8160803601070402c07296035080080d0b480390100c60485e03aa8410610529283d0070014841c40c00b140d06441e1008048000004110000303d03400c071340503000c0c0f010701100d21180e005101d00d90240c00c0c02400b070b503502c8412642003483c0c01011751042042140c03003801040b80035440340070b02c42070300d40c3c080716102c03c103171a07a0000d0064003819101940c99446c2c880d0600c20150003142c0c40045841585418411942d141c1a5009440300080e001e90160000665100040c1030a401c40c0e0f0b0241d9103090004e541d061031303155800d0041503111030102603808404460903a10b000203101e0300404e0b030001c0c0585468100345040940100142130340c00345824450111403080d0007800940c5402c00c40001c203040c52285118880e503207800c00e45014041c0c03490024049910300b4201f6145041b84511270440c103d41e201c42c174084401c804041c42813132286542e00e502103420140c100c001c01b40d00c03020002411540000d82814011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 434031555 1250 434030305 434030329
    0xb0112060b0a0e013c05092b0c09021b071a091c08070c120309090506150c010f1406010e010f0e03011a01080604150902090f0d05010603050d05180d080d0e010b 70
    0x91100a1020131200d030345c0c0b806040c41c1000800e0715074044000c1c8c08443c1000200b1030f40f0040c542001004040b944540c140d004d0010152003110080b21a10036007511074980249006000d8410080d5605020a480c3e4038010b1105140160075000141d940000f4410b484000e100100d070b0444001030440c0911121003510006041a4007191415100e60b0303502130203003c1c551007180d440a48031300000e40140d454200314420500001c81c20790790342290306100c41c000d212041020550070320302580055000c4c80c66280724801c102c10b840e0400d28100039001900c1d029548001c04003000b401c2c2c541402d03240c40a005510381500c8003640300e18400c00300f04c005008042d0090403d80120328010009012201314000b2404070f0380e01c900b00590b01d0107502c020a142100036031009400c00f60108400041000541c09502241d000d40d00b076915100e070580e02103800c3d12904000421000150006000c6071803c0c0503040b6055125000c082d1515900366082e100b540e80040c2d203a0320303036503441149500a051120b08848 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 434032805 1250 434031555 434031557
    0x2a1a0919080303010501120b03010903020717030315120f030c070302100509010c0303111b070f0608100501030f0e010504050d0207080f1b0a17010b0112060b0a0e013c 73
    0x2009038104400709a0b01e000510030141000808400d1401524039640038061900c0d020780240400300c0c01e070a02958030300c1e0a100d440400c00820a454441603404000e4a00514000b40007803050130030340c4104115a1880c0e804680d00c1e0180d069442d414800070402440b0001445010340a02807441c01004050601c6407889800e11004106441c0b8580e40700ea82080c80703030b91500300010502101c0034580c26a003d0b040e81d004800c200c0d9101209403900008a03c0e04032408925242d0070683c035214121510b007802d4030f00030801c06401c0700501c405d41c066040100301496094001404d540c1607c6043d09652007a0344c00d45040e01702c801201076060381401600c0c050181d450042401000800c0d201e59650b00c21340508954402507161005182d446842d0302d0010080c050344001c10001080ba42402801041d48407804101580da400d0b4040740c06000b181c0858020004040c10309110000980d01200000d440a040103030f424032442e03c81c956030714203402481011200103540a120038041c0382002e00303c0083c030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 434034055 1250 434032805 434032849
    0xf0402030c0405040f022e080108060705070c03110301090605010306020c06011e051c0c0605030a0c09030201050d240b0901110105042103140a05150a032a1a09 70
    0x4c0003281800da51303a01d05990541d01c0140281c0f0a42e082001c140c41c00440003039107034050202c0f120f0140c0c00184d0780c0c141c69040d015140f154442c08400d4071144200a0700400c2030103086d5040020510314009881501c0f0068001705404005a4464040301d50982080340c1c0582c0c0841c100017590001c00415000d0400742d00d980403202c0050703103000900c0c0845e1241601c40c205102000e1107403130180c0070300c01800b54404d000c51101911540003a0054108590902207a40f6001908100302d00c180400c1045070303010f03142d1501c2c00402001140c0546846901b40390000607030210007c1c07d040e15a041001400c00011181d20b41c03501d20001441e05100c070a296820781e040505120110b002144010600d92284274030b60082d50400c1415801752248440742d525044805040201c031180070b42025200b40d00442e0404c1c04840700604000d4501414003010b455000407410711700369a90444001c0d000c44000c641401d4016958100c1c0c01c01703061445517000719a0502084820450900010501281c8040700020b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 434035305 1250 434034055 434034061
    0x1020105010e0c070f02031b01020d050f03011401050c150108070f08032b020403030201060f0506130b0a11120405092202060901050c01091a01171c05120f0402030c0405 74
    0x703650b80042c09000030001010008011040240c000802001c9642c0501030f2007803100076021014200402500c0c0b0350160003220850060140706208540908038a41902400c603428030001d445003528047d025030600c00100618a0109401c04c000500740c0c0328022550819030404051034108101c1c1d0b0301003c0300c1008404184100100401900c00b803042800d81032141c0010300442510885031500d0b05c0c00e80910005010003450b506400400030341d800140451440c9541e80d0512402e0710030059001000f0b03003864000d02409420b07a00904c0300c1c00707042c6030101001d002121120305024041d0582c3c0a0740000090401c0207040c04050030f1752081400031060f94034400b142200e4202000010000e00c500c000081c04062680103400b511400002d0400070414200d840c13501c1d90940345c0202c7c2141004030000000038500702c5038822102038104100c080d080041c803100c0910300403d210302c560814040c0902c4020f5458076a10b8030f940c4125110b14070a40c09007014018036040c210b01c4004240154105010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 434036555 1250 434035305 434035319
    0xc03040c08150907080c01170a1103010e1614030703110408150121080f03040f080d02071a01080a030507020310050c07151815111803010e010608060118060b04031208060102010501 79
    0x1405a100c0000005111540c80100c40303001003c0402e400c54000c5070110010580010070f40dc014420184c0f00e6115a40c1c19138a181501c1d84580343d0b5180001c0d107810000110590711039005242e0f0250307400c0c0d8640c00c1c01e454600443c1001013464010780c060850701c00411200c1010034041100b4102c0460401c0512600d480d280c0799841200381065222038000301040800c5144505c54860542105640342c4925100b8804006075005c21020350340e240c00c0c815100014541c01c9a118100c0341c928000b0308900300340e5601920241c100d5401603034103000d034161b6545080313000c1c0203a1744240f1105038101d60742c04107071a000000c4e888180080070b085140c548141c0c1d0200a24a04503000c6400060402414491407650400350941c10102603101c1d0000c2002400d940020a0341c1c040164120001e00c00002141511400c80d000c80c4100010755002000401000131041e4040a41d0046028045045520b512002c80990300c1b07a4821200c0c0d07110081e03214200340e4840d058a4012000b48020700055240c105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 434037805 1250 434036555 434036567
    0x70e0c1b0708070909020f0406050604060e0402090d030f0906050f0306040203280b0a080c0d03050a090f0b030a0507080610030c230405090106020708060c03040c08150907080c01 78
    0x2909040001006190030039008001c01e03001031001108480b5016100d0741558040c0240316000c81c0514000180004940f405000b400181c480245c005400e00340390543c21603030b03103821804658209508000544e41600c030003410812142c06600c3d82c0d217010f440c4050080c00e403041a40120100541803140002e400d090000302c0350420340c101c9001d03880e9100c1c1071184504488084818106010358040c1e4441d2004581011003c580300300c85c0f80035425034491000d52a550107106180d403142e0540344402c0000d004a003d81241591803501e00e61903502c41502c910101956008298811400f0041021480e0a4051103038410041d00c0c002d081d0741405404510b0010740c100c4024107068031107900b00d2010780328a080349803103510142600000445030495548980c400d00a41d40502c480500203d51180001076040451386010010445992903181e003400e50781010f80216944640c40f54001940d85080100a03503064411030700719114205040c3c61490f03e100e661058040b07800502562080360780100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 434039055 1250 434037805 434037817
    0x818090108030c0303241e0a1e0b0a090b03010f0305010c050a0804030c02060c030406030509070f03020a06050309010f090516060e0f091503190b010504050c180d0501020a0e03070e0c 80
    0x404244600c50030112446c0d4851550680c0c250400c1082400f040310b00b060441080c0405d074280c0b4820612511030300c2100200d034011005441d07481c0403003002c02c00300500c40c00070840042a8900b500d65a61650000f0120358400e0b0b2012210078294001401030100038410407642c0e1955080a0b40b0f803801d503003805005140d00070005002d01c500440c4001c02e41d101d550448400b9403500068907074841c1c480c80050002c1805490b000d001c0c0c40b55a8010400754400b443c544242c94008000062461400c20115140e60008200e1110b40d502d8144282c1d43e401c540c0910319440e480760000d8090501c06e4500096a00907690116042143c1600c07500f0094843c0320755882e1100060f01ea82040b962006401030f0062250503901d50148642529075041071140c0200b02200c6108000104050344e0b0b4804100c00d0b0780040e254409413000410062180400308811241001005441e0b60000b180d543c65480c2240c01c84a01d01020429141083e51145024003440c0c1c080e00c5c181600c40d15034180704807820040c0c002c2e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 434040305 1250 434039055 434039071
    0x903012f090f06030a090606080a11060c060c0a05040906030605010518070816090e090c010815011e120501031110110c040c090312031b0f0c060f02070818090108030c0303 75
    0x105655145c61b03003181c10a560051400d0040c0396541c001150f4802c1219402d030b5003184070f5086084103182c2070041b00c011404450040c54103442d25115180380c2c0c0e00a121500070301c882044001038000040c003030b140042d1f008032400205503140c41c00b4401041e5a500000c10609110410090102d0b00400040d400c000f48450050100b002d10344255440880c0d80c100101d034240c00010070000aa0001d040c8840b10421303a5210055103402e41d16401618401d01400c0c049084036041c5013005280e0b0b2000307400205186045440c00749054005002c0f143c003a0402c0d00d0003115642800c48605180700019501400e40c80c0ca903020b641c4400007540c0b54841b41031403a00c11502e81d00c03400d0742148240b200c0405160020180503c1460146024006051040d00b42d5900417000303000502060041401e03000c80072164483c030030303182c64640e194001420003c1104018036405d004000102c1c0826015114001b5052121444814502c0400003050700503401141d5542c070802c00742c0c8c144000801969088060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 434041555 1250 434040305 434040307
    0x90605040b0a062a0501050a1104060e0616120914010509060904150b0c0610090606021e100603050a02030708190803070903121d0105040b0a11030903012f090f06 71
    0x1c208400d0a0321034a545010324502d1404135000c2c03001c10f41c042400b40c2106201046801ca102000040c1d6020724490b000102d8940c43d41c50045040c030b5030003407401e6840c002c1100b1006000340c1ea84400c84d000e6120b01c0d400103945030400c2c01200b214100c1081c2c1a02c007400d10a080c070707035894005002c600c1410081c43c0515141d0400800b0300104000203c05400007101d0326442e1410b0040c0c4075621241140e8030801005644000036595580e8824007041d1021030f4040d22044901e6003481b140100c003844136030403510880b001200d00407114402c1f031000d14401c4024200c0080c1034010103180082c16000346616400810041804015150103003410355402090036849584560f81520030001641c4050305900318148180002c030f90003103001c11b0034086008419071181d805001101c090155000d8076150107401c00c5040003050081940c044810b01c0c1c18102c914180748140030a080d50701021604041100e400c0c066401042c1d8070901d04a00c15030f04c450079042904481c000740e42030f584500340b1401820 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 434042805 1250 434041555 434041577
    0x4170705191211040203070507030305060d020a06031503060c02150c0a051c06030b0114030f010b010f030f0e0a060219030203060a060507030e0d0c0f0506160b0628090605040b0a06 79
    0x200343c0d40074501941c0010411901c03850604c1010380154003440080300000e2600d0300041031803a100403000c0760160007030070328035a460510009034014140920b401c94094452400003000813558098400c4001c0d665000d0034203001001800f01d41030802030401d2807505020b002801115921900f41c59031000d8005142321020004000c880041c4002e8001810001d000170000c190000710584140c08094168119096144111401401c0b155400c0b01540002c3e08a8403034103420f80309400200da10074445100050320000d5010052816240480480d500c13078021a00d030110200c0c101c0c0381820600c0d5400c0942c81e502e0f140c00001c000d004140551014080041503801c01d041c80340d00071001110020700024603041c585d00b88080700c5610344c850307086810084032010804d420f151040c1c1d503201c0001810184503c0352944c401c001d82c2001446960803801c4540a11100c000000211144851014001c042c1500b80000f40e010703140707641c00540c007803420a20712403003681369031441a00710b4425150030b0151203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 434044055 1250 434042805 434042813
    0x140603011212210b180f070518120a0303150b0418060e0403020703200108060603090a051b090112030f0e040f09112704080901021002041707051912 65
    0x140c1c5507010006400c90003c01d0069040e03140d002044050b4101c81480141482c05840c143d0094200c48403500c4100360000304803003c0c0541d000d404006100d8441a64241d02d600104500440009a281155001c002d59400b4103425204206910a0b69440620b60742c0c01c080c0b10107064415841203c3c20520f0348400c0307003405841c0b0390101000d406c41a01c3c84030581020304000390380700c5440c0400c0c0c07051100c0070600c100602072008140c10140d01a110320025654201c10001d86400050145e0402d00410a0030300024205005008883e1034607011840801d542c1030610110200580044581044207104440400d4210011107035154017440d210305214025004600075040701e4140454040c1001c4040d420411001035502c0c403200241e5400c8240038500c1420702c600e12031b0402084469405c0004240401c0e40b101c000d08842d58103004603011001500000c4040b41d02641c080494048040c0c2c1883c2d810b85c0c103014030401028100e9011040c4101140b0508400c00c00c4c2c4100c522480841e00940200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 434045305 1250 434044055 434044067
    0x102151509010608040311160b090a03081c050109110f0c15090f010e0303040c060c060204031502030f15031c090806070e012606011214040c140603011212 68
    0x203200500301040341e50b9192400707049250107850480c08116900e5030a8044072002485864103030b0540d0402c90f0051a0240b03075015a8404520990003130700b0441c010011900c2c80d0001e00f0502d20004500c415600d4000d0a0001c8890680080740c409003440c080d00c18282c800820f503841020a0040d15640300000c50f40c040c50112208011403502040341e003081010040459280004a01c4500901c48200c0110441c0d48a2000f114001e2050300d84070340a001d001d200d443c0000d4058402d1a00500d0140c0340e07210600c090320145d1032142c10b01c1d0000704001c1c00845940c5426003003500c94580c2c0341024540b82c00251900041e0740107041058044050300400d6101c0e48100e00200f100d0415a031b542d0a024000034001d4044500d61808181c40d00c111646001c010601040c0019580001602c552030b000c00448130280c503130944429041c6c54984100305031242c1c481041c01036104510a540d564030f03110020440c10285d11078203220788000c1c80100302125400c00c100f10011f50040300f1038034000c0121815186 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 434046555 1250 434045305 434045341
    0x50406050d09020315070f090b0409110d0908091201090b010515070f0f0201020706080c07080f04150e090622090f0c031101021923011e0f1406010215 66
    0x11510451440d1440b2170390b9140d485028800f10fa48040c680c0640440035907210380d09201d481e056030760802c010005010654400c21a0108a10309149444510201501900c150800540e4402c200083c0e03403620707180480300b0460b6a03d40000074040c0c02080d45642d6a2000148a9a801500c3c0640100c0c04006408116203d0540c06a0f40100300340c014240a017813132000340b0040b03001d80314603140851998010905140b0425101c1c0300103240c4440c0d070b030717903101c0981001401581d4200c00740f00c04502c0030028010710391004082d40d207442c0c240021401700b005400002d00047e02038820101d29906520540030240202800c980d4003140300d01c0549490800c40d55609400350042e0ba0780780c0040104038401d00f800120700342c26807c884002150071850311500443c08402000b2222030608070080e410b480d00717418030300c417095000056200303016072084131181c00340e10f404c03074686603180d0a11004040c188a07907502c5810b0510340c00403510f41100040c0d0382d51100082001c1844000c0000ba0304a154000c890300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 434047805 1250 434046555 434046559
    0x180103060504180c09020309120931050703050105010504030b04420212130f02040204301e0c050a060f1205090d050a030f0615120b01050406050d0902 66
    0x203041400c6103624468207070303940031135035400c200a0015a5140600070360f030281c0074110203402d459503101104038183c1c0c448903903e5000503082841803030206000c8100d500241d001c00000340c000400903205021540014008410315248c10b00502c080e99010041d81c007540d6204003050f12603141c07070803d40700c0f106540c41a580c2c007600c08101815442508103500c048803660950b00c0743c14100c00c1380300a0580c007600b4081100310040c1d00c0064580c4502e0350f1400c40341d600403c01e4101100e01c0d81c0104059902c20740001c600303005050b00580740da200084041d801c003078400f620320520f15034540d22035100c1d449a510b00e02085558a00e0f40060001c0c5caa4840020b10b401891090019900d2801818844142c481e403004542c01c0c1002c0d281c0f0b55400e0140b01e1003040d6000242008000d18241134442e038100030a0401056590340300c0300d103c68074a210340c1014140c09065802c01c0450703020f000b0811402c41407540c000c582020100c01450b6081000d507010303210182017460311440d01e0016440200903490300a9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 434049055 1250 434047805 434047811
    0x80904020412020a06020a11090403031404050606030c1804030e0604080a05070510110a08030c091306080c03070312050d0b04020d0623010203030415060314160911180103060504 78
    0xb5200c2c546944a81c41c42c2c425541d1100495031100e0176070716204060b0001e440070740b22aa48441c1807814604143e4817a1107818005892140e0140c0382c07103e06000c81c3d007110154003410511080d4982007103000070341030048841d8030601c0b140220b040e602c000041d0000781401501c1640d10450341c0c0340001e4030b0150046a08884001d071080c140b0740e0750b4110700d10440e0300444d044d07552004480c0c86100404102c5441000030b01031032005a60360f03142d5500041c069800c5190500c4204056956015681d04800440402003071a50500210308e0406070301c403030300501c6588007070820400103001024240e9407900c2418555240c2c00d00240520103080c08826181d4014400034140e0041d400781d0340f00c44256010010010b60b55181d01c91400c80079042d50403135601590091002500064510031019051250307100086a500d58964581984450803500d50006411194988100818000c02e90b030003041c55980c28010400da0001c00099449030180400104500180b6501a81d019070004402028090010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 434050305 1250 434049055 434049059
    0x5040204060503031611010504230301060906090504120f0807030e15090607020c01110309190305071728030807140310030303140603061f0e130209091b0103090809040204 75
    0x150050030316400d013140c1e11010044104987d521405c280c13401d442c0d5410086203203d14980100c4221140c100b1003641c559250780000c28019101d0007078a000300403410300400c40341420300e0aa1824005400d440741000070b050b24001119038000545900b04180703040c006000c2610070001424540c03e4140440207009400501011131000242a4440c0c22175500307072034a00f84514011941225180b90038081d56105020451692800d0305d43d6101c030341654071480b170041c0d0b0390355901e90405803c2d030312007480c1ea00b851004145500007407160b4040c60050f1125092031100015641000300304014000c0c0c100845070002904a03800342c3c42140b12044503011040c2c40740b6182c214000c207400346020440020b4103004d0050340d002140b011603400780340b004000d001c0703956078001d041c15a1410202c41d89221020503000203258142010b82c40e0103840c0100c0c11150688843c014800da00710701030a035420b96070240240b001707030300c0104550020b90310b42443d000c038081c1900e042544543c05005a4a98010320000300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 434051555 1250 434050305 434050327
    0x90f15090611180118090e010b0307290408070e0c07022808070b0a080402011b03080402120a0c230a0b03010302010906050307020d030c14071416060507060504020406050303 76
    0x280100040c0c503005160580b515034011170300741100b000051407958004005000702082c61304074445002110000141c068041f5000034605801075110540704480282c0c0449205210a03890f040400c400040c01d01c4d062420070020740d0303030f41d45110f580c0c0c02c2400b00d004105004c0d42c0004407076030207400801b401021100b159041014040d09250a1503d038001072001641c5d03072000c0b0342081190004800d0030300300045820306030b42031100200200e0410401551350050095080707201c440180c02940e0b4001645010300c140300071840c0c00c47c1c000d034182d0700c04440880003071140504442901e018500b039850f50740800143c188054a11210158056505031012a1080d1504d01a50480303000341d036001850343c1e9565003503805110564427040141c2011088903980c4c3c1c080e41200340032000c0d505c1c00300700360041c4171a9812550451802140d0401c0900c40328202100204000201c651120004007030179440d081010304148100c0d48020b02031910b44002505644c0d03070b42c0c040401018040c050b030350342d640c003010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 434052805 1250 434051555 434051557
    0x712020d05060109080109030e0f01050c0f0606030601120203100f0e011d12090907112d0f0304060903021203040f151115011e1802040602010f090f15090611 69
    0xa03030b0360000300c10140002c0c004905003d55404150151a0041800140d20038085605400500141440010014030150320001c2040d0f014a080403070182609085c4401010f09150040e4026081d40081004030300260b500070589205a25040740001000040307010340c6006030124040740c06035546045e00c5030002d00c0c00007000c8101c2c0074140095600405000e011803000307028410000313800c072004200081c6032500480101d00401003d10489050320980b44140288100ca0084c114810400200e40710001d401080a44003451910000c2c50030301e81050320080c0098606c2c0300280c460101c0741004c03203a028050003280d001e0854205260349440e01d1b06440c00c040c00200d100e08002034041c100e2203448207008202ea4075002510038903d40e159282c880890201b584500b90b0b0070b210140400001800700d04410301000c03800100402684681c0381500180c211422030f01380024a40c00c100300500000d007c007402402d8140d0003034450047c0300c481050345006100240c001071609182c03104001119407804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 434054055 1250 434052805 434052811
    0x7021c050705060a14070c140102031e060d05030d0f02040902130e100e131406100f0b04080304031403121510050903150a1515090623030712020d05 65
    0x42d08403405500c5501102049800b030070418190a100708010800c8503104108120501d4010030f0300b2003902e0051200142280c0c404c0d2150041485402c1040300e02903e450320060340903030215183c45111040f9150b6546030721031301808640b40c07a0340d0140c41c92081c829070b06680203000e07401c104545a101c2400c181484514a008001c68040d0302c20000304642c00340d8080000340c80d1041a105c6041d19241011115a401007400300d031740d1007a80395801041c900400c40c0510804044108042451906105010700541d68004030480001044248003071140041180d08896001001000012100c0b8117a41103005540d040c0e002d090f4030700f00340b00031000c0d580384901d0280811690202c081481c00c400741c44500c5803140c0580c05070401c42c0d80245c2e6201c0e403d10b55a0000c0395500208184043d541c4602804200c2d8014000d00d80004001d02c04255020750800c01404a0342050149081c09041512007038050f03504000d450000000004e41e554459945003070080025141036444204100561020b01021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 434055305 1250 434054055 434054063
    0x613090804080606030d090501120219080609060a08061807080d022401030f0f080415050322030512100b0c0c0306090601050109140f03030f07060e121207021c0507 72
    0x443c1c0400c4c035034600840c4983c081c0744a52030b05164540f03448019101c000a52442c07a44c103a9090100504645111400d0400c3e5800c41d82e4041d1585800000c11080c0d83c0d0140945009011403802413042d0070300010069044400d00c0000c1c1c11340c0c040188440d140c40382d1500018000d001381c0740c0301c0f0249030700041c00c043c03030714074021281e07820520b00c2e1880340141c2c50920019008558004520000c582452003a40c4c8083c010004241381944621035071700e07e4290b43c2c6d061000100c00008021035940e162080c04e00c480c03221914100420010340b8002c0090184c0e00440a0f041891000f00300c000c2940b1822000602030000e0142d00c81c1e0f08101015101d4010a0500307000340070300000103855145c08185141070383c0050711031050550500308084c6180340515041c4c2c1d0403200c403a905406071f55040001e0460503000e420042c0d6100b4040ca00442a558175080c0415690702c0301c04010156042070b025a2421042280580101e5540400c12481c2100c84004000d90700009403001d159980d006008040746805 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 434056555 1250 434055305 434055313
    0xe0d0207140925020f0303070c1104150608070504090606050304060c17070c0201020102070203010908040f1a030406050405011806150515070f03090e010f030308070e1305061309080408 81
    0x320060094051045420506046200f10320308505000c103400c191610a4a00c11035200c150190205407640d8400e54001010544241e1510b0400c1500c03084402148001d503001d201045040d00e04000412140c0102800d100040d000219010311910682d8003d04101005010072a50b60711b02803c0c41d40103032010381ea0780e42410b038115409401000001c0e5042e0103007140210340e6444150440c1c4624000c00d040341107540070009003002d680c00f400f81da64514000c6071001c1c1da9900d40700081034115080d078408801c11300d018171020810420201a00e6002d504900080b500741d866240007401403003400030006010005511003820300110303501145001c0a94047c00440b2900c820401450f20001e051000645000704200c10000d000300180b0f200c11482420101c0f441a111184502c41d454240c10a000704e00d0040001c00c24541e100a00075000701c5181414800740303400d100815210f892410040b15099154004121315448064541c080c001110408021b02c81882c9440c0180d54058842e100180c89 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 434057805 1250 434056555 434056589
    0xd02030f01180e2d030c030d0c08040b040312020c0a060c080106020c0a0b0d022a06010b0306061e0c0f0a020a05120a1509081b010c0503091506040e0d0207 68
    0x418480d6410b5801c9600040c00220070445404c000341450785041c1d0300244040d400040e01084c104043c044404200c4007542e00c0b4030140074030a0403107580f4041e4404110802c0e060001080c2402c01090b007098042c60070004007200b600000380644511000c0500500c00c1001d00018010180c0c080744044202d60f40c0d03c10117903a5200308907681c840e91401954815002c18007000007041403001803803003406540025040402d400d0000d805d2180c502c541c801c1d0141210050402c429062040d1b41c05400120581401c40c2002000300d141401440b02d40090040c101e2031780e8807802080000e0300c1040d1084411144608a00184941c80742c0d408907040f07000300700300321001c00e951400d24003148016551000501c1804a0307a21114001d403040c071042281195180706103008211340d50700038100201c42000f614050038802c8200d608481891401d001004003e1051000c10380001c81c800340030100801c0c40c1529911507500040041c5644102c0040a110398244c0d111519008940c420403100028081c0644072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 434059055 1250 434057805 434057849
    0x20a021f08090606060a030e3d0c0f050a090e01090e0712050c010c0c0302031005010e1609051203090a03060e06090d091710060e0901060801021606110d02030f01 71
    0xb030304ea95500100601003000c14511070b5020320884282e0400f102c41a40d409508140040702c00c036800309540c4c0c9013029450700e286403181c00c2408081485030402444040c400010201c0c08080700c507000704540004d2018030140b2400202014040f40b86801c0011b580d158200002440901c1c0d07000000d02030400c00107001b1000946081b100d0340c2080250440c0d0030b101c001103034890040708086a6482030300c03501101503102000182e40034201207900003910350400e0312416601070004d140e4201500e0b00c00050307912030341c0500414111a0161101c0c151940da045210341503001e40c4003541c0e0860110140001400300031f80100b01411002c0c6c09030b0b99951a03240d0350356161461480390300301091b8a0401005a0030340100001c903010070074004d03a01400605c4200c070301514465406202000e0018042c882008400c3c460f060050000ca00214641003c0b02c5002c10b94a20301030014200d10b981d1084148076522000440d4a503542d448005c40d41c915024800900010081c02555120500404045154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 434060305 1250 434059055 434059063
    0xe0a0e0f2401080d0302070f120206150316031b0e0411011103040b040b18060a0306050f01050c06190e0d09090f050606030f04060e0703030e1302131203020a021f0809 73
    0xa81c0e0b03e90090310984001d200b00381d0195000b02822520281260f01610220f0300c1000040c554411540c06080b250902d501c14035005c1c0d0344070410f944030f5040f000c0d20b6001c0040c000d01800440e984412800001e800300600f0703050040d45a446814013408a100304010082c6003520100801e4003600d40718004012503164036504c0c040c0d80140d6145d0310040006100e01fa80320f1010300003254411905841c1c01c2c2d00b920210340c0d142c000d01ca060000c03985404040c1306c1442e052500350041c581c21f10f085400c000c00980216074641010b05040d20039490a4010510b10401e03420940124001000315189c0b040c83c014001d03c2c0d800309100b4070341c490380360030030702c0320240668000c42e801034000a0640f400e688468455900d030070000740046411540e00c24080041c10020b1010400450103903d44400300204001480082034021904012540c41007000d021401e10a142100655840c40c8890501c0106032409a15114880d540030350710440c01c00e81d5200300030082c00b40184042190303540b01e1040c1c460310845551 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 434061555 1250 434060305 434060309
    0x50108010501050d170d1107060b01021c1b050d080406050609041101082a13050906010203070f05160f14010f020316080909070c0b07050c070e0a0e0f2401 68
    0x20085204021030b0200302010f05d0a016205100d10292038446400390500444842c5000701c16140404200d51041c407009200d69180207800780003410701c0d4815810312000241034008500d0070b00000345a54110784005020030300206921000311a2400c50005d006070178440d04490845a05050400240722410b21078890340c044c40e880b100921903c4e68540047d1036245008200988000031007408038030032040d601c2c48214101103112125920b001c201c1c200c1115048540000e40a040100c1c1404840d0740d00004880b81e0b0f98011680d85102d4140d03103010380c10566610440700c064020a840880c00340c000326803800445e1340d08090b00306003170701c000015900415480e0541c0c0140e0018002410b20740703001042500c2e141e100e00c40c40340c600f10203440000c1030100c054910100240030448140100048040c2d020b8100c800750034424245098600043e60b030f0101e50107888840d000301c002080310705010390062002c070408101034600d9050051117480c0e644400d0000000e5840c4060628800f495210741c2e6181 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 434062805 1250 434061555 434061559
    0xf0b0a1404060e030c010c05040503010b090f0609040c170105160e030703080d060f03050708160b030604021c0c08160f0813022205100914060d052a0405010801050105 73
    0x4810740c0c9588807580240300d0a01e81d443c1900003080a4000c1d003001707108094065840c0d48480351100d00b0841810708443c044001e103401041c05905010f0a00c0c01c12003500c1c0c0c41a0101c40060260b580e03840c080c3c1400a09d0392001d50005e07600e40701c2614042043d0405071045c40c103004034403000c43c1004800c4038072014140f40b4941642103034409101141e800d0f002031203000c400407008078026a445000900044041e8004d880c1030f00005c005000440040c01007690f4840c54001000000f0300300b280d40c01c000d11000d042140714944c001a4020300d044040c06004a4501e100002c03c540c03070050308082c0030a501266540350348104c0410304400140101170380399103020344c0c0d170342c00c201c41c3d450402681282e0000d82c8260b9003c0c40c405440c20f87d14a0200381480307030392402c00000c2454288041c420703024510a4000b000c005c0c1c1072200300c00810b0403600100b41e01240484a021142c14507040c240e0810148040300000e4900750200c41003848200c1d101c0148089058404000f583e9803036150600b26202070042e90303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 434064055 1250 434062805 434062841
    0x1003170f07060506150a0c060b0f1503091e010e011b090e040c0807061e02030901050d0207060b0a080d0216050306010b0f0d050f04031106101e030c030f0b0a 69
    0x4a0441d41c015544680c0c0034144180144080e03031008401e4100d0703858200000e0103031101104101c0c3c1c40c0501d03403049c2825144007039481140d80004040400e071074100c0d0741d0844080700007503040e01c0400c1903108002d00c0901d0600c040407654816030290001d401009820742c2004000305000c01303400103a44000f4025901c440001d070138084051007124000d08203581400e1401c101091401c002c3c0030b000c0042c44651141c070540302030000113142000380c0304041010b6410901401d07030684d030001b0445481081c0c45400690318030042c504030340100304241050381c0020080602013120310001540108200c41074084900b52541c11010300c0e60012640185501604101d0041125541c08000340071b07032503614410542044100c03c18002128012134101c904131146070180818550405061321104000a014080750f182044510350100401c0c420284030b0141c08260b1440e946215014030301855205080100d9150f5030b041c4500c82c01c01c0880c043d180040312038041040400e051264445440301c0243d85 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 434065305 1250 434064055 434064067
    0x212c0a030e060c0106051003020a0807050c3c030406180b190512041212020703020c060d0204091a0f03031801031505041d100605010806130608061003170f 68
    0x40002500f100b00c0b070070001d40d2611400701e101d54031031051b00c0344102960b034010784540810000a04038400a840c0009021080181d01c0031450041841010860080c020094440310700d013110030030001e032a801c50b84c0140705060711683c1c07090103c01801158516038401c8a030b02d4500703001802000d8180700d03103505a0002c2140c1c1c2c1c1c2d00f41040c40c41c01400320b400d0808608145001910001c0d910089404546c5074240400300034507241c01000841071001840310450600110b6a400380d45c420100b19010710a010104002d11040820740440d409070200b40b000744600c1ca1400a20b1101c0e200075171015100303403075042e8036400a040c0002511008030dd00c00e800754101c00300d07000540003803c44c0c059020145211000100d0342c1d85850190740642a401c2a2030500344510055590a002046007000004d5042a01c100f03d181c1c0d100100340c0c4c218104807658011105d41c2c410180042c001580446064001e000402240c040c44812403403c0701d0164480164080401000700e07554440c3ca003460304044414004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 434066555 1250 434065305 434065309
    0x60610170703090804080a0c0b070809010804050c033a05041e0918150209012102040806010e01060e0306130813030b181005090a03212c0a030e 63
    0x140d40c0c00004074140068a142c19448400080d44075410013610f43d0300c410340c010100201c1800d654024007200902034204101c82c1d541c1d0b1094812400464100001000850306000702400001041e00c0c00508403024883c00d030303520101c002010a8030060005e1050244007118642103203880210446684446ca09070800000d060260071560302c084250b480c000011402104906c034000f0b0b8055208080c010303600e000d1170103414502842c2443c001d801d005000e40c0302c0a07600704200c428a0444c2c7e40d5400c44244084442000034003a65010300301a04c180400002e01e14101111030f416954165100d01c0b42ea89110141541e5039010342e140d00078400307550704140104450344081c004c0703031a4170b0340f072914096540d07203441e0000340e030580c1d0546400e505a800079803810000c101c040201d920b030720800d1025182424846444e008500406000c1c48480c0203a41c0c2103105222050155101c102c00170000c001d04030004504c000240c00344c141002640140c80910fa060014507403c4d141d40c95510710224800740c0d02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434067805 1250 434066555 434066597
    0xa2004060804230a061b1d0112020f03160906260402010507050a0c05040e1603020108190603030e090f060a06050f04080106090e06060a030f0f02151b060610 69
    0x2101c03003030341203420110010740c1d410b104410042d070103000c0104101480070041c905001803229031106010380da03030601080d0101c0704420003195909089c2244e028110140c0c1c00060305c1148001d00c91100c0000401400e562480c0007141504819512488803a40b201c00541d000c0480000e500c44400310002c0607540c00c4101000d9a40c00351046c0b500e01e0500526a0f03440e460840903540448560b52a42024031850a10384211610041610000c0801c4040e64070541d042e800a4000070381045162400121881130103d030001c1081a00300e01001b02907600d05006080d41003820f101d41c450f10655000c40c04111580070751364001c202c002c0142c0b807030078540744055405a010030400d11100d0310a01000802040a11038030008240790100030540d0003036141180d0070460b004000a21804400c0030900204000c90040500300390f1020840b00c0040803400043d00f5075100c2c0842d903102400009400a206a42e0100c480c1002c649100725461601c5281c100300d070720f000c2605e10000203017804031041101d400c800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 434069055 1250 434067805 434067833
    0x1b0601031a04052a10030b031605010e09040f020604060e0f040c1704211119080d180b070c0203010b1509010c17130f050114030a090c080102030a2004060804 69
    0x2081c0010313052404408150108410400400480d54448824042c0d08040c49654140582a90070000d0035040c8000a024000074482c01e5000d03a0f284400942040103c060241007150002c124a40719991180c000b07001f070b015407403294040c001440101e011418680a075110103280b42c0c032554a181007504805d842004024805ea890280d040c00203a440300007142101c1d250b06440d0382d0000f4804070509241d207030850f115882c2c8810401ca20b9044d011440060950340c124110101c041078000c050035614900c42650200500005c582c1010301095540100740c207070741c4e684290001d002400c80303e020808807021540382340501005c104030640141d881130503001d110601c9490404001071800800300c1280d00301c0703818050102c004920a2010b03c42440090700100001d1a10180d00e007007071540c4450a00018101844440d101e01c020410030840003210800391006000854480c81c200b0107103800fa240302ea08100c0303802c100d81c1820380c150f4684411036050f550702d6120050180c503142d071100300c800303031107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 434070305 1250 434069055 434069113
    0x11090406090b090a05160e071101021c0f0f1e0c020304030b10030308090c03030d0b03250f050f06070b060d170a0e030c031e01021b0601031a0405 64
    0x3401d10341e0000362644900b07402400d2070b50040c50011154030700203103840410b901c0071042c2c4444540804c04030048440c21036000e401032400f02c20715000d44400764068000d0880c14190307116000809076100c1107030b174002e0400011242e403d01940021741191401c69040c512400c00a51465401c01c4880310103401c0044030300400d10441c3c2c82e04e5a00e8480880701d21066607546040460320004106040d4407481a41e0001200750181016103040400240e81c1d00c161072403042d407140c4945143c40c45942c2803169040503140c03010f110044495040c68a17404014034044d00018000001c0b000c10300e4200154081810b1001900b294a044003948591407950801400251312608843c003a1000541da41d5042e43e8801c9550401c0e41c03110741e900030140080e8882107080b4040c0e0300c540c0014602340e078000ad0283c820502d45086d06141d00d81e40c0d10b11406032280c0c08007541c2e0394807222014071070303ea00000d125040740c0c0200312035a02c0300014240792100c003a040d00c000e44141e0001c0e20b4421a0200c10819007442209 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 434071555 1250 434070305 434070311
    0x161b021c05070f08060906010f0513060b0d0b0109060914090a020403200901060311120709050a12060501090c080c251a0c0f0a03110f04120507060c11090406 69
    0x140d40d10716181822036080751070640460305003044550410000380390412400406403015604094200442c1c1c01c1900c83c040c4502502c102c1d0f00301408441d800380c03024000740c419150340e0b130791080f80c04006070036a04c81c1c00d0b000440381303040005c515200e0469603060340c2c40164049400700c070744410400c2c561000741c030801c1500d5082000000040ba512140034442c0c062808000799a0030120800401d00d00c140d00200074541880c3c580f10400203141c00700c030440342a4103200c5145440740f5200325100304081e00203079040104580003280ea00e62003400c810426100700e00904c141c1c0c1e2110b8400050713850450200022802e01004502941d07690703406004010000d514010340ca4103180340e944900c00b80844140e46628000b5191104121030b40c44065110942c89a2103141c08a20301100c0e0191084041241c1010b40e01d9292049803094642220b011015001d9000d895640310450316a0f81030038130508456a2240620002d500381c000c0085241c12900505d410182002c130f038040c4101c4010040c000c9a0243c4e13 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 434072805 1250 434071555 434071609
    0x509060d180b0105090c0316030e0f030405030f0304050303091c021c021305060108191103010603060f0f030213020711120616031b0c0201020a060207050105161b02 72
    0x9501d104506075940a41d024150380909401e0a80107801c041e0070090048448008001c82464401d04903500154180d0b0700c26510340c140081103006140701b0028001e103000710b000c446a0303280b0000c050b00940c0c0d0220107855101c0703403204203c0d54901c518482c0c141c05170414005600c5518050480701c8405080b410140c080901c141d001445240d205548071407120309111065055052100c1c00b1044503546078810403060800781d0020304441401051184100e615030303d15010100365802c0040d0070444100400d442e942c580e07102034003429141c0506400344016030340c0015043c504803da4400c0b260054110740c0b110480d400720354081e501c00030058520081e419010050758450000c011000c0038100040d2135030b82411a141408519010020020503040c0407180b5a1b07640c0c00c00c0350b0240301d001410080111051440140e04206298902600da00d101180c4002404410740245110b12220030f00340c025420003081c244c0b42c0c0035014680a25415410b08008010300700108841d00c1c03076941c01011000b00c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 434074055 1250 434072805 434072827
    0x203071203050d050a1b050a08060f040209030a0501330b280c0506010803121503190803040204050c03040b0a050a110c100b0a0308071101050712030b090108010e0d050906 75
    0x4c0d03001e03110741404075034602409a81000b0203070000c001c403074146001441e090001c9402012424050320041c4560002d001103556a501d5030f04036000d5071800b80654902d1203003401d15600818118942c0c04d040f5000c90b00541a540004c0350b0b0800c40784660f0b80a809050501c40e0b81c00c1590082042c8181000010800c2e10703418003442041113959500d170303480c0d102801c0c003440c00a00b01001a03010302c2c29503005100046950031a84200380d8804601501c0000240541c3d00103480c00c011204450031105c800b580751020300c0000402103104038001c1c1c60038070698450103044001c0d84801c0b0340103800d4801200100d00381c02a0768116603000480e400c0d01082100b005000718140741e04c0b00d03422b44504d622903842600704e25094024111424000ca8080c2203003861521408818881c4000042c00198a00207601d140d03801401510b150603085034000f070b14213079900c2c0e000d4010031180030200d2240700304800004203070905008401c2c4a21100000d0000c0b45202c08094132142c02880c1d81c1c0b60b00c10b1f000e00054102c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 434075305 1250 434074055 434074061
    0x915040609170307030608030c1002130b030f0906070203030402130c0e3f0a121407060603050c03010b10030c0509030d1806031b270308040501030f06030203071203050d 74
    0xc5054100c4140d901e0070913a40250855501d80d0010003103400c24405801c000d030001c2444100d00c0401800541d0b10740315004c807000c40c14400d4000d660425004400c0c00104001021034610849600c4102c680035140c2c0c0308143d0341d07804100c90003075100c8001000c011520040d90400004800c1c2c0e0304095040942d03410008181040b484038038040d041c4182e02202c868000c1130604480e100701d092003040b922b10a42259501e030880c940c00541360742103000d42c008546200750007802a0461840100e6190026132500c280039007000c0c4002e441d103104884481c20a0710f810700c5501d1804c2c0e802000c4244082d07106409a0151203428806424370000344503010240e1020301c0100038446450707032140c5a01205401d48520750b28180c00c600c007050700e84800410303440b4030b04a0540308100c0c41e00303082a007040c0c840009038214859103041c090302403214000000308160720010f4425180c09880a002d00399a01200e14102c0707031a4840654994080e6100704480103101070b01e102d1884c02842c0c4589421011310700c010076 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 434076555 1250 434075305 434075333
    0xc0307290109020310120c05040509030d0204060207090c18031e0b0901020309060709120b1305150402040c1809050a0e15070e0a0b12090106090606080417030915040609 74
    0x8483d400004000d444102618040c02504483d194680100d0080d150f8800161040c0503150055a07a400810840c2608005407040180062025550385449060007515000700d84030b0300c2a605e00b03183e07180e51540d0180e1101100850281c961034803a5245854041045204c1c0d10b0402220004071003036000724041441c082d11814040b000543e680c2801c0260518215006001504002c0148000e200305459009101c54180e0805490340c069100c408410800002c0124020401d104074000410f010f1107001000784114000c171010464004944801c0c0c0e00d0109500e101500340546610500424245131b01030b070b4001c1d11180000903a0b030b24401000b4030f00311420b1840ea030803104140420610320381c40000c41c41965026181510302030700e00741d11405035019144000500d800722200107441c40c0f0017544460014441000c051040c03954900015018020517a820381e10456004407214203050050110390003400070200800b1000f020410788120010080d00032186c0350785a0220b03a002c16190120195 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 434077805 1250 434076555 434076569
    0x80307060207140d020d05090301060e160e010f0e0d050a0605190506040b1c141e120708040302091005090703240303140d1407050301030201020f030c03072901 70
    0x80d0700c5441d410300c200000f080b100c89a0050b440800d140300788550200d08442054a079003480c58440c40b8010000e40036211507040122030381d0000f000c11554034421001040071110316100c6440001c10080111402441402d03d04045815043d180b20f0301c2c18040d410b41034450046d01175803418580c541d2030b88180c4805a611000000c2c241c8684296942070b481000e801000803034081212820b09408581010078940c4a207250101020000d0107001c0d201d55040e0050105009507400c0c0c0805c8042d4202c10009803d468078a0300c505001c8440b000c04d00400c07140c03c80d0b004000141403a10315402c00c84d407600002c1201c2c0001800d408001120344424a002d0f024511940b0045406c10b0312a0006409180b100c01043c100d90000300c007000420381280c2d2208215003401019651741200c0103010014003d0700c02048140c04c2c40004001001e503004c07029605a034400d82c2503410380d07940b036415659039003d00c5d24483c005070000c1000400080c02200b5250f500c8a0071003584440f40b1a8481c1c010300090700340d02c000307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 434079055 1250 434077805 434077807
    0x111070b0109020301060c080901050c063313021c020409270b070e0d02030f070521030909180a0501150504060803040b07141c020d081303180803070602 67
    0x1404002200c18094054841c980c01103041d50324103007004001e01c0a0700c5010309410b00c0080c0340380c1585d11400c101c45002841034221600d504122181650100b80403003c511825080d1703101003041d010700712010041e202d000b042d484003c1d1040781000003d520640d034020600100b01c41e000c664040e2030010b8401043c07109800900400301014000c0c0a013010900001000c40c0388400800007075031110001d400c43e150386030804200c1c132800086000c0c10740c1c502020b0351512030440301803002000054810706850050310000103211001c500001c02e81030301c140860039500188413503249424440080355010400402d18020000303e42045420059268070030348031a51140c1c118014901042c4001e0018481a90104140c51074090505c1e20f900803405000751400000800d1000c1c403c0d45190300d42a080030101366940340e80c4090080740064440c94001d809401a034140084807809100241d1240400310b551005c1446039075801c031707001912048590f01412001b00007291350b0782c08001400da40c0e48200703001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 434080305 1250 434079055 434079067
    0x5070206180d050f0105071419050f04320616030c08030408030a0c1103040320041b020d05040311090702010f0612051c0c1e05030a0807030e0607081609080111 70
    0x41c207550008200200744608c0b00300c4006081c951b44102d611800003e188540e00303110307818048600740300b071a00880c0103c4000c076022465060003c5402d0030120000344002045002034030710300c0d4011041ca5080c1e800381c414003e1042007001c41d40d40b0090280310307180c6002c01c86c4084c1d480c0c0340f03140c0060350140c0e5680c1c0003004010503664240f10b40c000d5034550782011001003200000844e5248180d010080c0095000c00012400c04005007103510140c60013017050105814a80710130340c1107611086000c00600c0f8101031000e51902031000c807016250000b001e115040103000900081c0301d400b8010700119036175280210201c0c5010302c01e10000e80110208034480242905016182613500050307002807400d156403103081c2c10341103807801081d0340d03101000846078040b059210000d4071201c4c002824174080003c0d6180b4080e48404039600c00c00440e20100141c481c105403580d9100c0c011110000801d881002107400d01c01e0ba8204113544940910341a0300da59201d02003103096400c40610640102804204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 434081555 1250 434080305 434080333
    0x8010914012c13140a02060d0e010f020a0302030601080a3803060f0106090608010806070f021e03040608360102090d0b040c0b0307092c0f06040c0f05070206180d05 72
    0x1005041d038840008003507170012070300003e140d40702e00c0d601c0c1e42445030f03241058190710100790404c0700c80484401045441c0da41c40790020740a54000c58101c0d00080d100d40004544045a2040d450319095a81c1105015813103021080030030480c0003008080d885d162031044c00d507a94100b215910940c02d4400328500c1c0e52421001405103030094215209010403100144030742c0c0000030311664441070b81c0c5092225001c2410099003042140d14100040c00e504480800c00c541c800402001141c0041d940d0305020765035012200700d801440442e40700c05035980001c00000184c110400040480700000051074600301c00e00007208010682000c031b40d994020300800c4248178031188800014100d40302d03500d24601c4c2c444070003004103400b8040d8810a90a6030f540540d60143d414065181c1110200000ca10b400c05140030020342c0403c03035005101354141180c0700c800d10b2080f550b0b094014103507100d8038144881c030341c20082c9a82094645480c81d03681c50310306d000d09a84861003002c9d003034083d2000e09001001300b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 434082805 1250 434081555 434081573
    0x306010e130c02120c030d15050306041214070209040605040816050604140118080a09030605010b2208101a04091b080115030f050f031908010914012c13 67
    0x213481d80000501a00050240c044100c074400302012900241ea00300b0300d0595108000700b81c01c0540c061003101c1c00c10040140e0318920031a6902d0340c0e111200210b14401c40c440c030500c900c50000350070825020109002032540d42045d500f0500c6111818184040705000d0b00902003040d00a40e0307a40c1c88034081c0818000c030324800140c400700d02c400078001c18111034001c41d03128075900402440140300240300940715104000c90000b4607400241071000d965a02e02412668114401450601407420281d00364031952044050031030b0380e02070240009903510015400208406e440c003031200345404043c0c020b0b5680310f104080d4601e200b4586002291181c0081403a821740c26000310b881a0f140401e0044920030b144034035006c90340d00003821191207881c2d1410714200b8181c40300e141c52601c808034044811302280124000303140c0c200e5607002c05603a030f03802c225416a85c2400350540010130b8038005002d100141b60704e80c02e0900100c40c601d0080a1040c27125240780308100d48245040340170f40642410041e80507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 434084055 1250 434082805 434082823
    0x10c0f03050606040b07020607080d1a011806020606130e01020c070e0109060305030405101701140420040506070c031a06040e030a0e01050306040608030d1a060403030c06020306010e130c02 83
    0x10302d41c282070900304042900d141c0314220007c0d200e91000b044035400c1207442c000315481700110035010321803010401d0b101800c01c84001005800300e8102092042d0700d01c10303210300300c0441d1040d50090490340c40340d40c107101054540c1d20400b00046d84a01c2e183c50070b80d10900091500450a00080c00058a8007040103465030042e0040b181e12820a81c0400200340d002040d2401d545c401c0390320f24542405000141c5008034415028140514003600009541030321800c1c0010114007a1414808034080100c3d8840b95281aa6207040d01141030009100506000002d00b80c0248034a00302c0b4521500d0b511080c0c2c1c0354101448481406801c042048130300d0804e40031f0b24806c00d151800840c1400324900c00502544442204241040401710004109607030325000900245000b4098035550450818213101521509018008480c81c04140c10100d060801c100d40850381c0613503403003007088550f60b105000f035400640700504200f40c05a0805096503070850320045003410b00400603041c280b500e006400e240801e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 434085305 1250 434084055 434084059
    0x103050907080a06021b060708010311190b09010c080f0301030614040510050411060c010b1c03230d05090a020a0f0b040905060621010e09060103031403090a05010c0f030506 76
    0x48071007007000e040e000540c1d40303420340d11081c00768540b11014081c0d0080808800801114801d10052004072500450428140d9015001000d500301c1a1020311a080d000c0c820300d080d22101c201d100304441d154040c080d01d4102814541110581055259070510740c120003602410103800000420400000344a100950440904031304001e19090716800d071a80701d0f5804071104952034400203010448103580100e4211001440203441d07609140302c00303000304071009241e0702528480145203e10400c03044c0528040d5416903c9000040c1b102e824000d207413141800a00c142001031001d040202164001c281c031030003800d001001c115840340100b1520380b0260340003074400c1c1e04420060000102405c03c03642074460113503010981c1e07254140441e00170320401c1e80701c4090491071000314940c21010303c0c83c24101c40c0c5d03540d51141a611800b000c0d0741c076000d00784802400704110742d4092456110160155600c180c80d003050350180c9405886450a46045c90b0b840e000050b00c400680a11503003600c5055048841 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 434086555 1250 434085305 434085313
    0x6020f0c0306070503060d0c030c09021b010225112707090e07031505030a06050613061809021801060302031b07050c0111031b150106020a0b0f091203010f0501030509 73
    0x8650303c054414440a07242130701a414140110303090102c00c940700d1000711341c130405408000356a100d450000350406500c0714400a42c01d1445a008481402941c07180b59985c0c04210500d64155071880321428014011100d40e08013100b2000c1640d9a011007801040902c901380c01c10b5100c825040b00c2c44400184500c00b48000c0d44002d20200001022456010103641130020303000c40c1840340b4000c901040d501070f03545441b4860b080c0040001e0f40c0c000c14020301b401c0e1107109200c420031a01d00242c8445015501c01c08070600303290850031006811646900303002500002008040c002d07403a2290300241c0004000c00e07000028000310001e002161001c5514280d0b445003041001d83d216034480e190341c6d80150400c904904901041c1c0d00a00417540c1c00c5040d40020a031641700d21513059150040d0804550880080360000207810340045154290690f000000801c1580c1d042d000c812200d80140c5000003500c039103105802c83c9c451001c0114081c0ca01030041e10001c0d03140200040903204010060982600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 434087805 1250 434086555 434086561
    0xf0201050906070e180c040501021212071404090207030206040b0112030e12010204230f011d130b030109030c020a050a030b040b3403060905060609010e0301140106020f0c0306 77
    0x8503080740c00510704e1410f03060086031403000076809095400c2510042012100b8080482040c0e001401103d00c00e070262034201c40301d0403000ca4540503010344044940c4c000030010301c1d444d101c1c0032324008001083c1c07405030900380c030b840d007a500302d07044603102300d0140c0d10880034070082c80200241e050061260b80c1c4030220300541681c006000022069010b40501e9200b001c60901800a4055902900d604411440043c0c1c00b810641100116208058002c030400301c3d0400c40c41d44220611a02e1200c81640d40c00e0f40702100081c042c4088840c1d104118080c0c1e01e80b80e24078550703401c1c010740c24000e02982e07480c0c0d0406182d0041100541c1381d680454800c009080d01003000a02c01c485141d80140c2180c1745414aa42e20313000d40900d801d41c40317101c04040d00440241c94601a9092007198102031aa8040018545442100044070001d44011740d04c01400c3c049140c6641c49440d055030480c04c0600003081c41c404210201d0541042a080031001d608409525078504800300000321159000b1030003001581 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 434089055 1250 434087805 434087821
    0x302010b120111160807020316030309150c141507090311030105040f020d06091209090f0b010207050f041113080f0a0312270501060609120809091803040f03030f020105 74
    0x1201c3e410f8042c4001341200480c1050100701c0d070560b154560041d007966480c1c0304581c002810300500380411008214a07940208810300d9802c07130740c07072240d0483e03c0d1040400c0c0c1c0e079185c11810b00780a007810031b00b070f104140040d80390302c88807000c160262a00d5180d20022904518100045030a5550840d0003030785403004100100b04400070031107045405692914070302e1010704000010740203801c000380c0005080301821099035441546482141c81c001d00800000201002d498265010224082e0050348a00818000c1e071070856650100c0440050000520070541d980c02c2c3c105e42c100d20590002c0e02106034041000d1601070040b81d8026103100003411580745542d42c00742c943c200d1010f442d2a996585d0351040c81c0345c41d5180046800304065440b44220300300e41e140040c081c108600503100010307000400006c0b040150281c07030000a0780314191a0420100c503051166005005110f85104515016140301000b410300041020709140c0099044d100c0c110f0902034a8522034018000031a8508006c0180c94 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 434090305 1250 434089055 434089057
    0x702042c1e0d0c0203210a0905030120030a140a020a090503030304030504210506090a021e180a1d010b011b11150903010c03061404020c03220b070302010b120111 71
    0x40300250400500f01031050012904d44040d000c1102e5203d01500e0f503100401144101400159415079944011642c40e4401e03d400c1c4c1d44010040024039214208645500c07d45c0c1c0c0c05140d00c00b07145071001610f040340c09048442c188094681d503820035030000d41c400b0707202d50002503500038120503002903181d82066a4014218030440c0300300b404140e4501d83d50301c08a0459030904000e0382d00002140c8450409030103091b107994414000324895a10062a010103061925201c1621b034401408035100380d01900c0d503945205c1c0003d182e1a02c00f603542028481002c641c0a800c020002c803000005100002d140000d01884101c2d48407001280103000e100c0300062295003002e444002c103030340c008040000503c00e442d55010390010f0540c19401c01c4480c00e8407a505034081412500e0918402021303200c410144001ca11401c4200c09503a0410001d0414204052070406c55101d81c2c4000030080c941d030740034040f0494012400031030060351145c075400220314220520754001080ca900030040a282c80c441c864032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 434091555 1250 434090305 434090323
    0xd0e042c16150f0201150b03060414131b030c06170903042105101a040605040b01080f090a050601030c080606030c0a060e010509031506030d230702042c1e 68
    0x8102034007201449a5200b90006e204000b11300310700209403616421805030540044458500a03441c103144030200780c082d030384d20714015548858051245c410075161207080010b1102d19040c2c07010110340020020b203055074490300500ea00d40d2180f950b1521900208820100503003003050a1344203002c01d0280d240840c4030070400f5494801451070302c9146161072030601540000802043e850844600c0040c440f18030b048840f9182102c081040b15100c1041004840e500200a80080c0c2c130800007580c280c050411894004845100b240d105a8059031500c0c5080b03400d810445422041c00c90030000c40390f04100d90b50300030004801a06458024078041403040300701e071040100f080366078491651726902510464030f003c1c602074251400c0540d100e8000131080d1083c1c60b002d01034443c420305006181e1050454409806416620001c0444440905401904411000c0c0d80c06980c0d00c9017143c1500c980c541101e5120005040f080d039024142d0308841c28505000001c05050000da0b09160f4000000300f0080700b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 434092805 1250 434091555 434091557
    0xa020c070806070e013605030d030204120b0c0d0908040312050918060409021201050106020d0813030e01120212040302070b04030c090c0203040f0806041110020d0e042c1615 76
    0x2061000c40c034003110700740489511b000324140c40d074034980c00501c0301a200c1d100b55042542164150780039004103c0c01ca2080f0302c1801c0e2404030040d411070019500c600c1c06a08490500500e905120542100304103e82d41c0780d01c01c681010000a04208210101030000c1c14000541000b608040c1c3d8440822801415520103420368041e00c00014410381d07036580510f0080e0340240030450b250b4031404071180200f00030700885001d880740486025900348640031681c82900b000700700713270040a500d58050302d265000d02412810300c0303040c0700d81c8961600144007400c0e040c00040c3c0e5418841c01d060070040d0800480d0f812a102c403860400c030174004a585600c000d011180d44520000f08445004c3c022410744c0100d402111070440e20b40f1002500c0e0720005500c5003c0c07030107a00c0c0c0c0c0248862100c100241c1000c05416200541c000c0c3c189600041c0c011f030300c2c0c10701d20740001c0c0010600030101d46a00381c40a0741d200402204d12044040b1030040402008641031018001d201c0742a11810003600404a40c801a5a90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 434094055 1250 434092805 434092817
    0x3070c02120a06021b0d0f1b0b0c03160305070203040509040809120d0909021206010c060902030d02030409050a091a0702070f0b0d0b1504050105090a08060a020c070806070e01 77
    0xc64540424994001c08604290350380715400b45400c9003e540300c11000d0038642d00540d03a20b10045000b00d80160368141e107840d0301d410300310344e12401d440d4444030800106040b0f00500503a0007103109644114032500e08464103582d01d203013078201101e4078030040d007421040620340741c1008900364001013268160b400442d4104800e1392945091511481045e05158002010119421181c503001421004112003a201e4180031501c580904049010714440000d104074094046959540181e01100305203000c2c040104810007580c0229190107840d2501c0300050303100040030442004030f480b500740c00c800c41d002e00340b064041d151180d40358500100100030301e01c0a0000403403003541c001c10140c0d0007082114040007541d036403400350001e580c000244600c080c90034040340d04103515000d10f01100101c03031407608a00342401c01c4c0045541c3d40140385c481d6040601d0150104011104022071071052480650142c1d851040ca2200c0e0309100495114051039840001480300311504400c83c00e0048130280707010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 434095305 1250 434094055 434094077
    0x608060f060910081b070b070806042d0b01180b03090a050a0f020f10140c010609060b0301060e15091912050706021e0a12030e120909130302030307 65
    0x8295100c1c5660b0315601c04080860291801d0704049580d200c0ca03c140202101e025410240e001c0602c0b81e07000046c004159840001c02060280c2c412a07003210300a0f0000070100c8140e03502910b4640040002180c1e4ac1000700062440c8080740a100742461003842d10b0b0842182507c2142020315890141c1000160301000051f0f00b0102000420384060b0020211b4440f03a800d401c0400078102c1600c070990103040507031400000750a00480c0202c142800d59503c11003241c8030b0301e0100a980040c4000d12080d500c8080000380304d9007502800c0090080200300e140c0d40d5140840103010743c00d0304007202c2d0154640c0000060281224000e540b0032141c145c810101c02121703048890540615500460011040d0324112802d00000140440c1550455001c031400d224041035524070081c020075241c40d69030b20852080000a4203502038070704c0d100590501107203604c0102e400d0342c18039001500720034841700c0c0030803000c00c903281203580c1c02e030001c0b00384400c604621841d8400a40ba403000901ea5400e1011600b58 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 434096555 1250 434095305 434095309
    0x3c0305071202190f08070e042105041203030b030118051513020d030c050c0f030d050c03071e03020706080c030103140705060f07022404060c05120f0a03050702070608060f 75
    0x12003100303580300c0c8003c074080315254040060013405030b00a03101c03644a036050100380c0d8264400c010b03000300d40000c0816a80442c42c03c505403660151039900c010088140800980c0d202c020040515462080c1c41c00310b03100382407000f41030845041d2525801e0440404440e103002c50000310780221200c014034151402c0303607641c086c06119071500d01c00c003c3d000107034510100c060550000c0f160440a01c100141c84420700040c0c2084810511641da8982c16003080d2014400d5030b004000a002c0d0034a01001d99003000031940f1290000500c0c58030321034142499965034820540e0510842002d0b2516040c800e201e030516000168603070105000080c0b000c074640d1414169070004110843c0100402004190b60f10a8411140401d80084100701c0c01a07101414194040c40c0c000099400502c001e1200e50610785001011941c410009030240c4803800741124080645070340c1b000918082c0240c0320301582d2100103040040450308000d150508540244c9410700410b51b116448079080705045a8490141e01c403000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 434097805 1250 434096555 434096569
    0x40201230403021e10030b03060601031d06010f211e050a0b092103011409040f050609030406090617190b0a120b06090106140706063c0305071202 64
    0x1019601100701480100b22501c414039000d11342e0010343c1c1514440c3c48020080e010750780080c0846501d504028001010303944660701c5801800540c12444056142c6080000c1c1086001c1e0408040200c00352014400503210071004802c100c0f0340000c030309641301c00d0f0b11000091020b000798070042e80c50101c450001d0000800c00030101d250000c00c03a900300e040c42d405590756215101c0c0700024031100c0b4a50114022040f10a0381d0490f03d0002c109203405c0496800c200400030000c00403641400f000650344040754040114034030030001f00005503512800c159000e01007411651120303040021a031142c0444c0c81240b0361702038015211150748401c00542c40b81ca400a44100071105800c03210010380040c0124118290840c0d1034043d8440c641540c9a18041c0122407209005100c0810904201600b0b5091024003c00c5428001c1e44001402c0e1b458030703081c00340b00341c01120b0302c844140d50039050142e42246c00400703521051401c1031040707001c0c03440c0e039401d441d82c02d40c0c802d5283d1080d90917811025511628 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 434099055 1250 434097805 434097809
    0x8091504021314010806010609030c030602160b0403030903080a02070f02010f020f15010f0e07171306050103030323060f09041104060f08060a0b0a14030106150c1a0402012304 77
    0xa0424806019105400f5110503400d1064500502c2040d0001400d01e028110540c00d803600070701d000090608584039413000c0d500044004081c0d6071080320b00400716201c1c544050241e44696800710f0010120f00f80109003440203000c44011500c100245000200c1e00003540fa800d650a08060004024000d0168144000c0c10040301035401580365400c1000141d030325140c10ba9000385101d11202e07455a91926072200222001c002140c0c40f0f02d5903151842c0c1c4001c42c264003412200c0c8500325805242c0d1004245e44084e4421000b10340c0303503425a410403210645031082200300c550504c4440c40d120300011001c500d01d21001c0e020b540c40c10040390601a40d482c01075029100600107101c0590359004c0410041090f03c034040f841d0007944085070541c3c1150144400800c4e0040030b219002c2e0402604d1072038509204409a4159a10040000c0104a811040d001542c1540b1001c500c250242448030003880b14503007070f43d900c000c030303100700001070380c004404255100b0385c603642c07030810f05d9030504c0e0551504c51a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 434100305 1250 434099055 434099089
    0x1a010819020d063f0c08070b03040b0618060d11040e031e030f180c09070e03150f040602090a270b12070b0d020906070b160809150402 59
    0x15202d10034055078011004441002404044000401001e240b132824110340d00a019010308004500000203465000b080714060f40480405503512480e05281003110f621a964004c404410031017408102e01c0a00d502030300035115545001400d02c9a8142c8040082442d1b00c5005007000080602c4140c20514903081c401400030401d0f0141c54016a5a0b9004003409800038807050a40507481892041568042c559415240e03910340c45a80b00c11240e8400120480620310485c100721240e40c0d00c001c551405041c1a4445018049140040c103003000d49038220101080100c20030f200e214414412007036845074000c0f800503142c4c01008002410301903161710540340f800c418911001410b80c15440c0300b10070799a840e802c2081061400501c05156000b00003015941c0103010204074a001c40d5000b001d01100c50140185016035160008106401c0f403a03055401c809500c04002074483c01010403051301155051418280c0340c42002e141d81c5407401d440c02849600140d003c09c00f151102c101c521041458 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 434101555 1250 434100305 434100307
    0x6021c05120a02130b031321090e040807080a080a110702091801020f030a0c0f080c030718091e06080c1302070c09090503070201021c20030d090b04050c041a01081902 73
    0x1f40c1d2000c508403003010400d540402d1503031100c10400405010081800c41c13651203401800c0d180100d01d101c0c41c080104156050b0317000b0400b90000441c000b00401f148a032940f1064070741d04007041a5000c54004da0307006544544200080005a075907901c0d00d83d031050380c8a14603201142c1c95280e845c060300490000079800c1e1301c0031052000f9400c0e00d401420340b541c050390780d0008240308030300c088850701001e82e030940802d030040000c40c2804e44503203900080b5000c03115000000544d0754480a080341e15031020000d20584a000780c5800d504180aaa4001d121503070041070328a10140c001500e10010880a101d0540d000032218100410a28500c0c000c0c08002001c010407021410025102c3d44000400c9005000c0c8135141d86082d4a4181100e102c20403680e5003075604d4131407c00341869141c802840c08028802480302d0200900031340030b8000e8491044d900c80d02c0c5401c0a180c95803904030035030a190301c40c07803c12015001040300498125000b000900e4803005644400302428003080740e00d1584c810285c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 434102805 1250 434101555 434101561
    0x30613050c0a0318030e01050702191502010614090705070f0b010b0d1503080a0e0102010e2e060612180b01270b06180a0f06021c05120a02130b03 64
    0x21400c0107070404031010b440900804c1000c03c0340052101003000014040b8444601301304155110b0000307001603500c098842100e00c00d429480e000d01c0d00f802d80c0110112500c2420107004154203000703140043c00b5000340c0f94a440104000030b103005000403d40400c100012820009014120090072102600281240c0013940c440701c442c44564010039100c4651410b01d038100d0b01c10241003040c5c0381100d8021990310b04040d814036040f00c3c8152001c8001c0c0c11903484c1c14440c00554000e019520401c4000c4414181507030178520224480030401340329801070307440e10504114a0707402036402c06440c81c07141400241d6103004100200f54240009025200700590400400e0401d51607400503001001280812a01c2a0a100b40f030140e07a4041c048603005207040c000c6400201d0300c90080040050f000741900c4a868a9919100c048000b1307621020040c2c0c031080c10031014901d200c3c2d400d012040303a0300d40145080c42200404a01030340c05401e003003101d40e0004607848a184440c8200c6d01401180d52030780d603241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 434104055 1250 434102805 434102821
    0x7140f0304120804020f060d200901030b030601080601180e160303030b0604030201051902120325090e180c031002040e0601031e0906091e0308010e0c0f03061305 71
    0x180040750101c034039012010300501031902588480c0d228a038000e0110702e00500f01070500061303801c940c0480d2005074030349900d034044850074500c1865204810903032640311100c6c60001005d4640429019020b41c01c040d00500904001149943c15030750140c21090302c541d041d4205100510254208525602039600200c41101091024004a0f4041c1c2d805204440405041010500c00d40c40001d000c10810414002c46070002e503402080e1404034010b981807100d542c01c0c480b581d5481180da050500c900032818005000c0e211920b40c050b101e02d0300d42500401d0603c40c52442480d80500340c903003841342c10750032848508000c02c18404555406819640001ca28100090182d0094060416800c201c41c0004603107500c2441a4034801c48022aa1090000d03040c031120020030b1050030035a203c0e0b40b20720310710001c220035030712090705072417007120ac10f05090380b0313080c002c1074b824040c4c100d84110358003e005d004031600d0755400c0c3c49144802d22000c41d540d450b6240007130108000d0880f02c050540c20300081000003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 434105305 1250 434104055 434104057
    0xe13020d0305090a0b04121b03050703241418011e020403060f0b0315090304030f140d0305040c261005180723130e010615030516050307140f 62
    0x4881030b54441c1c0080d0700c50001c017019004a004441403180b102c5504004a1548040c829440100c58003484d10280c481d00d91504207131185c0c00507035000010700a603408151284011034495a079181c000c10030011040c111070102d4001615884181440b0804581d410500307500c560440c104150144108205080600020350802d10040c2d40d003915080c0ca400c41d6010600840242520042c007500c0b120100850f0040041d0b006401002107110602c0040005501c079020110220300401d400b021915048021610381508501c40c0301c10507040205001c0000c991100100548030700c1284c0b28402c42a50040303402495030466107007801d1080c2d10540040182c5580001c0c02000c0c1c0206c01495040104503280d40c9440e503101c5d084182c07001520040f4080e480359080e9a415100400c04100c03069a078450300d09031090903c2000c11a50b454104005401403516070003c2c144071800c05010342d00e48100010160004017108005120000000075130041c412042205464907440882e500c0b8100c820340d84844d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 434106555 1250 434105305 434105317
    0x20d200a031d09090703020405250e1c030903060b0102210403060506030a0b0109020f0705010e1f06031109070e0307030c0305240a0905030904090302101506090e13020d0305 76
    0x4003603a81900400c20303007008100e0321310550101c00105040340c5191300740001800010030360a5403444c4150399003004200507600c2c1c1008100d5035110341c1b000e41054200404103150281003008003a140d240c200000382c00008110480c7c0d040400040d81e2000d91005030308060f4504400640f81c50200444100001640c02400a0720f015500410495858000b4507a5400400d100a440041310500410155900e17030014000c0c002e400000c1c2d400c009a990380c0c6803d40c4c00d480f00e0181e03583c1000ba000b01c0986034404003031103200d40c2c200381402498655140d5006d00741c880510103004001e00000610300c640510f0544140000240499074016902e04029240000c1c5000480e01c6004004159040c02465180601131110800c41d6180d50340b103181c8080003e1180b80c008654601041c05648030030741d2148280b4010a00070b40140c51501d4135021076800f222525002c0c08009292a4000d000d41580051450b06846d06c501000000382c8800844046030070781e4000c0254003143c01c41203c420180d0240c05490 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 434107805 1250 434106555 434106587
    0x60f0a0302030a11030108060a050703111b060a06060c06020c011d0d0f0201290d05120c07090c090608070e060703120c022a06070606060c0201120507020d200a03 71
    0x49545000c4814644c58482032241000d582e01c488007003150403031980d1002d80c00040508001607961002510010990040c0d004001c07018080c81104c420700300240071503540b03d00c1a45081041500f40712015008000c1314001034541d99005c541200308410940c005d810444080f15207c1e00d40200c0c081a031740d00d0410f4460f4000080c28a800d0812940c01400b135089400e0b00c00802e0500351020100346803000000f059115409a0804c40b01400b18109100c102d5260300380805950b92484245030302c915103103c6c0d0380070100e86232420b0181403441e503010030ba03282070350b2503032414040e1912444011510b46040ca00110341c001400160350040503000702d400341c28007092050600c2600d0500c88140c1c0c44e0b40e10040000e900c4181180203813102c407004c4142c416254030080800d801d140c1c2c20303110501114110b4008101007001040b04900303560308418080104400081c0a000b14549008029100c2220503081c001740170a440c85060182240759250140d042500b0480d034081d8228100208401500341100d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 434109055 1250 434107805 434107811
    0x904050a140115051e040f0b01020f07241e0315050d0b01060503061215010e060d030f051b0a0303050a0e0c06070206090406030b07020a060c09061d060f0a0302030a 72
    0x2202044060052400901c41000302100451400c2c040c0246103840c100d007810012412040c04c01c5c6983c5078480c070310408039103400c00155a03044074006403918449801c40501940410f1007040b4454480c0d50090520320410442e0512004148081d034400e00e0541f00c021202009844a0180c607a2541c0f0100940b07084940d02807901e6912803c0c8012a840b82d0006441e00101400610689005600458000310701602c001c8000c0502d1383d40a080c40b42009032031071400c20f654010414010840d0105810160490b0041c0801a203a5070150078941701100000a111003c181c075113414042c2c1018a1060750540d0030303a025810140340c002c006000442d540301c0c00c54944054000c2000c0f000884940300d580241c607103464240d0a808000d02908040d008c96071080e180c000110005090140075401101950001e1803000c146140041c1500c0e200030907e810080b00c01e004001d00355008400091100c050004288000301e51808512280b1410310540a1000000383c040b070081e91680c011132203916011820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 434110305 1250 434109055 434109083
    0x60512031c1b0804051207050106030c080d02030a0c150c030506010908120a03270f03022406091f0f14030303010b032e06030504030f111011090904050a 67
    0x1007040b0344a100344002d1101100403008011400f8030000f5801034040d0301220803000360182d650156a03c908803c543c2e994403501c041003001640440d000103044102e018041c8881c003d50029a280030310840c510800407130240b40004e218060300d091400c0c000010050040c803c2004d0080e0107414161201d03400140e03900b2001401a0b0041100880ca11407041c0303041c5024180d04040b005020341150311602d222004600c0e28bc02100240d404444920401014412035020f04010323040002d517500240c2440020304ad00c0301c1404a20344400c1d84610103c4070900c00da2200440980c2601507803d40600c030302443c0c0b04c046003030003602c1024401c5881c40302d81524080d1104080c9030f120301081c49212440c2400303001044902058064503004010342010940390359070008404014081c040d0700c050302081c2e40c2d005020616178041690900304400e410800c4d07a000f650080c1555404184011000155940031184520b5140c82c003140c4026100400303000d06801d09040158940740b14110403a0310788001c01007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 434111555 1250 434110305 434110357
    0x60a0912030c1a06090a0f06120b100b0315120a0f0b090706031b0302090d0804030b0a05090309150f0702090903030f0915060d080d020d06030b07020307020607110406051203 76
    0x8400d02c03451000e811001741d03403241900040038000d903800081030b032521041d000c0b80d402003154140c1049405220200e0b030302d084c1851806c590229070b410905412200f001008000010000d07030414a0600b81e881080500e0b1900280e401d06030340e900d005140800344507464050000030700105009080203010b403230310241e80b5001a8212001000700800b001042c0c0a504140d82c0603070701410020f08003a10740d1a410916a03103a00459100341c10442c0c08112000521910204a128a59000c5911001545004040d10010f528035444074103455001c1c10005a440c5010f1103001650034155000d04040c0560130840300075070312a001141d101d03103c01d50040002d01c990350000740600b254a000c0c4115160390300c0301c00c203100866000a606541900c03003000307114007040c5e46100401203410300c050006141c2d400c42c42c04444003503000e00390100319132040c41142c026031342d040101c0f00c000c4d6000386248000c400e41f50200c0e010304416807009601624079442c44240308004402410f04c1c407100f03801d00d40b03c10315001d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 434112805 1250 434111555 434111603
    0x9240105041e080d1b1e02090c19050406021b0a09060e01080d1b081303080412030f08010513050402040609020c1501050a150c0501140907180b010c02060a0912030c 72
    0x521217040c1861124402c002c900000e04039150401c04088550490342d280e004140c2004040e40d025008090000701c2c07071170109807101d84c1e031080350b024504545001c9c030b0110000d5503403e00d14014030f84c20f41c00d50402c07180d41e55200900307801400c0055042c481c242d524900700c3c07a107040034070034590700303000e119130414031a845892090b8914540d40401004407406840c1c60a45400c03000e000a500d025180012010416144c0500001c0015a0703010464014500d4000c004200c4900810144241080103000c40d544106801c40b07011944000001e0954603400024060440c5511501c01d0503c001442914440c1c0801c8014034401002da0240e0b131a40e8803818420314008601c52500030b221511a80754482e4803448140180a000d1b80003c504052040040c480c549029030315144681e0189608104a56070f080d4402c80030f55a862080014050f0703400007800c03090445a001b842900001111610030303002c0c0884030082d09000380c1070b0b6010002d0785805004070802900c1503d03110721480c004448045144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 434114055 1250 434112805 434112827
    0x41e09230c040305060f19090f02010e041509022a1e060402030a06050402120607050d0c051303060b060c0109030c020a050d0221150c0a0e09240105041e080d 69
    0x1d80108911703039451402450000011f80061442129000c1c08004a0303070318040c04d400c0790b015500d0440e09014900c001f40c80c03c0034003064680210300b4680803100120380f01da031507011580c000502503a1494210f01c440c41c40100074040598800d900c20806081690003c2e405e80e170f8880e244000c003241e041e1203031440d40e147c2c42102c0003945a17201001c9480010116004550030a1010f800003402c2280315880c0f0781401d408440842c0080d01c04a14003880d100f0720b001380500c0a14a0902034500900800c03642d80101e41da010180846440350503601c0c1a4032a00e0403940c41c0e00440008201c0d180c0c1c54500203009120100c02688600100c034004104d51401c41c2940c4c1e1081e90080000c80c1c081d41c81e074070005094481420101c0749009503812906000d42c00c884c030900c01c1001034881030b594601c40002900501020745410300802e00c3d84108481807001c0c040b52901c0ba00f46100c1c0d0280170100000494051055800103449507a20701030382d0351a4000740c00f18005486004c02540c1070000c1e01c2d98119560721001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 434115305 1250 434114055 434114063
    0x903190c0b0d0f09050c1504030209060f01090e010b0d061703030f04080d06080604210807111f020901080c18041508010c0c17030606041e09230c0403 66
    0x102000704000e000302002010214812880494010740d490406011a454004156003a8014508000c41803a00c1c440300510001804000b0341407a0071500401c0d0411001026a80200152142d20000340e0203240004020890404001030301d40c1c507032107070030407139046000085002420040046016042c3c50f0703d110204070543d00850550351182c136914502c1c00040c0c02070351040401c02651072400c5c2180651809080d40748001c1546041030715021403000c4420f0b446074192081ca041c500440c41e80840b0064204105242460886c1d40c0308009504000c483d010401018284c0684a45c1030401c64000c0c040020007601c5103045aa5440300c103d40d2845a1408024103000b07800c44052280f03450380c848000384c400321001c0048903440300740c802c0c215506181e08001164068039401e0802655049624491181ca200c407415401d104001c140d05009501600a4400700450411000050138002400800240300c00b0300c9100000b04d048105071503440e5a14001c05023800009410a035804116001c490780 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 434116555 1250 434115305 434115323
    0xa260a0809090a1d070f0b0a02030a0f020f011508010c08011503020f0712081008070513020307110d050c0708060c04060c021503040503030f0a051614070512090319 72
    0x4203078100315010b603004000b01c882580c0d84500c3c124400460100c214101d10b4070380180310103400d06001134914011544419001c0104103caa4030850b03000c4217035000c5049174249000b48841281d41a401c0c10503071408a00b4035840c0c210107294500c1410603203404c0b83c00c41d0000300650000c0c05030444260f8001d010340e0002e031a1100c130705050b80344030b81d008110302e548070203607103081a1607681c0d586034071030880020000084041c005e001e64442c115446400600c666402009014034080200b030b082001c021044041d10380c0440029003441c091150035003000310182c2a99803440e03044001800382c1e040803a1669a610076030f180400e02c1e2000140032405440b12520140c2480d00c0c100080701c450b654020102c0c0c0020b9610003d02d11000e411004d9809248240059902c07880c00510074480b05000420155602d41454140121101412607200300000646803204240c28074001c4041944550b007002480761048510840055040d04090803440d1000c030107545800007000c0040e40000b1070a28083d00c4054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 434117805 1250 434116555 434116567
    0x10e1c08040f110a090509060601020d02190206090f03030c0a150c02062a04151407021807050c0a060203011e180b011808010c030501061b0b090a020a260a08 69
    0x40c40c0c0c3d1078041494003c00b29644141c5441305003080d07400645040c034440e0300c48424412103603010700100d05617031366910007800102d6201c01408005a02c005010b40111030002c1c4a05160321760312401d00346c00340e0107030440f592072084c14041543c48030a60b03815130b03a0449014950610008030700580c0d601c220700d40c0c0200900d469465110303102520b14280021040b0400d040211240d10b204c000d00000e11406900d6800d915140c0c102500ba070303401d04036408214608110140050f075904400350481c01941d070700c80c5215941c140045c2c0f06481200440f40e211f00c22459a00e08202d510b400640c180c03241e0420a0141c1c05120400c260303101c005015500d814078403080ca807500320650b5400400d40c448140740014280861240c60464414190414001c07039440f0500001c070a90540102c0b070040c0481d140205c6905003003032141e48094065a002010300c05030ba0b010603030341d2108002244020343c008000a8500355900728402000d41c1040201c240108012031246100300c0100b840c1c8036644d00008440d00c3d01d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 434119055 1250 434117805 434117813
    0x160b1c0e0a02060c01020d060621050c04030305090112110903120304020d0f03030b09040305180306090304060507030c1406010510030504030206060f1215010501031a031002070311010e1c08040f 85
    0xb4003d1184200550741c284548010940d003230050100074400e5031074002605a444085280003200394084207407160400c410f20214014080c02c450480380c26240c0252102222030040b0f840d544002c00a8030354504100300001440a640e00a162038007084085403030040d41410100c0d00b5001c2103078085e6001415511941c08544142142100503100e4900021581c8600c0000b5000300010344080c0d000400103d0300340d42d07440040098115540c02103008021501d040111503940c0d10850042a08000c004260744013058044c4048100c441d600403c580914080280300030742d100000d02c100ca100b000d40004070805503009200d15401183c15034003801c0309984150600006110b00c007107250b0090030f19105840181810b00c03042040104030901c0811b00e5140c0300c001010366010308501008106040c240301116900000e0300c1040c600c281c240541c545889043c180e035040001d1851344419403c0ca20700341840078000c5100030000e50180b44400700018081d0b4112541c4000701c07802004104500c040c0d41c046 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 434120305 1250 434119055 434119057
    0x30d0c020a061b060c020606040b031c050a0201060b0403050a11010503010e01030605190e1c0512040b15100c021003140703050a020f070f020306090a05061305160b1c0e0a0206 77
    0x241d540f50800300004030039685884c22101195070b0703080142c0254052081d185814091240150401c50040009441613803040c0c59046240d640a0305000c000a081c0c220103000b90400b40c01029100b00e43da0301d81d680ca0400315200c1c43e0118046404c180d8030269448158010001d0341e060311100b01d0300f408581e0030356a442000b8640600741d240301e000c09210340381d110489409810441104c4801410384982403500c1c19107580792500700101800818450344503100e681301a8282e0041d0008056401c1d6200d41428501c03c6440340411608400d0200c1c68800c5507030001d03510b0440c5842619005100b0201c00760490480c0c4030801b03002c081070700820215403401d1083d00101e4100149202c01840d140c2c4603038900a10740d210620443d2082e0300600e44606600c0c5c1840502d41c02214000a02900c0741c0360780d83d40f9190080188428034144206c0441c0043c842c080140c402c01d055810b6011100945901c140b0f505a080301c0800448154840c1e01d01c20710040358010403c501021000810070400d80c0e41c200985 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 434121555 1250 434120305 434120327
    0x140d0504090e0304090f09060f06082a030d020d0e01020604110d03090e010915090e06011a0712030501050f030c030d0c0f080703030b09130c0b03190c020309030d0c020a06 75
    0xc0b07844140008240a021031003004060b2030390000029407a60145007a070252407200401000d01460a80b080090b41804200c124400a00c180140ca0000250760b64000c0d458a245003035825208485110002c03640014865002074412f80b140c44e40ca50f070714001203a45034000c440003400c200c0e809020355500c4c181074080c08030441c0310741004c407422615444560104502603010398611503c42c150410386045900b600005484001801e02110320750f0ba400c1e9a86803018071424825a40854003590510b943c601566401580819402d04951240300010090402030080da480f40201e941c004902d0720b400a4051aa2080031300541980f250011050b292070031586c00c02e607499046601d00d9800600f108008050741072298500140000c000018401c5c0040020080b0654145411010020500c00d55048044035544001d031a030300d64030018810a5071071703100e00d014282800c0c4101c51a1240c2c0100140c07041e11404e0b07049440c0801c0514084900840300b400294000e484842700b405800c2c4a5044441c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 434122805 1250 434121555 434121581
    0x905091507050c010c020325020f101106100e0106020321070908070816060512040830190903090504050901090c0605070c0506071e030228140d050409 66
    0x414100007020f15425102c5090401e801a08006001c40c681d003198403a000c038134440f44250070050401940813965554084144501c601d02c0c804981040c0d07441740c8070140c4050400c60980c2c446003031401702c00540506c1d5006881400a0190003c40c0580c400000c0d241c82032505c0c0b82c12007601560304002c007050407018142000300441014081000c100c100401801000080000e10700c024003071251001c1205a904410104071040101c91700f001000b1049603007003500002d90765070f100c1c08034524241807802a00c4541c01c01d007401621551458002d408079104005400016a070400c0c0c402607001141e07803c038001004105503407014041030030950320150f800f28802c0e0001a0044c030340d4540161110b0990312810025a0000300c1a04114024803941e00604d001d842060900119680b817402d40c004840800c80e480100c1003142003490710030440c1b211103104403181c2c00303199100300101500700390105030240c0b402c2800640c10a1805000105140d0454842d03a400381881e0a00b041e180250201c2a4084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 434124055 1250 434122805 434122807
    0x1603090f03030903050c0306060a060e03010b0409111305130318081c02010f0c05030a020310030b0c0c060f01030b18070306020a031a030705011d03070f12020901090509150705 77
    0x86000101001908041d5000e6159100301e10310314079265141c080c6410b40f50f80650401c4080c0029511001020f100341c58445c2008480c050841e00404c0c01070610701910303507115040160420600503e88418600328405a03030038811a48030007280400d54a0950780014254020000781001c2031040c050702251045c401c050070241d650383c004403440c240401584080b50b40e07540008001c80c5409100c4c280440d6407102060141c520030781c1000c0c1850100a0051444035000000260604a00203c41c40559030148a9202c40c0c1402d55095040d0741160468010324030842002c501c18400c0c44d40030382c2c100c0354803042c207003400c5e51781000003041d524038680c02454522800300007000040d0580043c0c807584440c0d0344c00141c16080c2d516501c00005070121080d005e90004c075814813890360b21401e2800214254400d8141300008040801d2404060754804200009000320109002030420b60758410740e030007154207008a0340c90328014421503200f5540001340c0c0d40224204078120340c2080b0100d501450f542451 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 434125305 1250 434124055 434124059
    0x5010e0f01120911010809070303020307141e030a0f0e0d11060c0105070804031719050903090a030830012309041104050a0e12160c090b100503070203160309 69
    0x10b050b25080242181d20040c00c01d54458156400300e01c0c03982c1301f1442402080030ba0302e140c0b006034407803040840103040d00003031004d8901800030810010107000d159001910b6240014030320142c40b904045021000201a0031b0301d941114810980160b407900c00034241c401d101400e681340810865034040c83c40d08100d0a010a101c22039080c840c40b8400c0e0360315102c0000c6440c01e4940209007030306d81461107a041c100c2c0b10a1100d400811140c80004001c0d2034000a0280c807540d48031840e40c010700c4c01141d4840d80c5002c000c0308001c3c1e684082e0a14401c9a41c0415100540c00d400f00903080c5110354640c0d005a0310001001420f945039020004004280c41e011040c00003400810700d000c03001c440c02d4941880402d6118480d003402d1048035400310044000300015000510683c0d1551920420381c0081d00011035081411048002c888405550044445903032959400d9510090403551030203d10910311340b911516001d00420449100d209140d0245103804841b01045505010720700303064007081812000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 434126555 1250 434125305 434125337
    0x10905100b0102070b0f0c07090e0c010c0c1206290612040c030c08060615250c15020a06060909020a050405130507080307020f0d050c010c1b03030e180105010e0f01 72
    0x905046800418044d0b4540050003200d12300b01003580012000e52614546c11000c41c000f0030301902c1d000d007d07e422a00c00100c5e007001420840203070490902c0348103881c01031080289a500ca100030324241c10126403a1107d0b4441c4a0360003403c0c045260704603c00f00700342080c0d0322281503c141e1041c4500c440e59143c03a241d840c0c0c1c0c4030040d00794200810981c0100e00380f120394a884260b1080381c941da100410306d080015480d00580000703110204000c1341c419012141000780030031184014003114298000e00b01c5900d40c009660b030480a4042d01d403c0d2901c5404101c410b400d0140003030043e0040c0069030400d203014240300060000030a1103940340b9610300d90ba00011001d00640b00101405401951100b22600402558078030624a140c4540b0610942000245c004103d0603400304007401c05580f840f40c1c500304008071490320b4003281010703803015002000701742e000104a10303180c10943e4115110044481c130100060420300585011407125411841d2518201081c0130302c0c1c1206251102c025200004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 434127805 1250 434126555 434126557
    0x60103120315060e2e0c02041b270f050105090415030c05012a080c03041d010f0e0f2404050c0705060606041203180314010606030608010905100b0102070b 68
    0x11100005075800c0c501204c0e0b140908441c40030900c200504031020702082e9003940401d030200812814030074034050240030b540da154058000454004980c941040441da8010720300c402a1011440f9001c0220034841c40010110b10902603c4100305c1b01616541010010758032034022a04880c0d206450b002040c01d454013080703c40009501c5510305158103810200094100383cac0240c005206c00755000d07441101249103680341101d4a422a40c480d03a600407842c0c4540c01c1d8400d0340c100d00c2001c20038005c4407005801d03126190f070407101d07100c0c10411103545a00e000c1c0352820058416000d000c08140214003409514032008950085841034280c00c20a0030380440c094a004070340d40c60700e1182c04138000c1e041c0b11040c003c007036118a00f11080b070320b064148203146400c0000c40c400901002910903040d480300110301c1c60900a1034001d0030403980c00508103c800d02070700090198100190802000164000c8140103c1c004d03140d01001918140c8030011080d030080095802d03c604503c1104800980000004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 434129055 1250 434127805 434127809
    0x6090c15090d0c08060603030c03090f010306080f0a15090b06010e03030d0e030d0e0d02060106080402040f05090a060b0a0503030a050d02090a150e100503010b0304051e0d1b05060103120315 83
    0x510350300f4056180110681c01d104000300b034140070740c00c01c100c0c594014801008903008900212071080c03030041028012030090105800404c3d1611951254071108600028030119141c41100a10313960804e44403601c003071700d460820082180301a00d010981560140c0ca44c01c0707800d00c1c05421642003a0346545103100b5500c0402c02c1a45e42d8000040c0305a142d200c500a882d0050b104c0710050080d6101020025910300d4140310f41e03002c020100020600310b54881e0001d61890724040001d00060501e605000e03100c3d1594101203415619082d0700c01060708102d1000411154010082c50505140e42e6040d00e01d940103c11018949500700095900c80d65003c0345440640901880385094003040744000d0614015191520305c00d010741c000303078079405a00c8011a03054802c1034103850340301d1b00d030361800520384145030548040714903044448440c240c1c400070300310f002492aa91174020888894445111404015502600c250081c00060010174208950802c0f0715200b07180c0091490600c10f1080359040440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 434130305 1250 434129055 434129063
    0x7061103100503070801060311150c0307060227030c0103020901030221192702010c0b072708190f050a060f110309150c070618120206090c15090d 64
    0x6110140600c3c101003210300054000304000300540c9046881d4100e509080b00f10881c4198106018940418212400d07030303c00c22280c9040302d4682c03a8510301400a9000001b903450040d04d1010406560160000707140400c030703c0030340684820454500110040d6000c04c0c25141819020021240381040240210750030f01504c501c81d610f1810020203561098101241d210342107406c001d5500360107038200640c4424440c40d912443d105210610050b200c9a009100140010358404204113140f0303041140505607681c50500000410010784410590b81614001c0d98050340c81b00700700b0f4000d101c442c00445041e034011201c0d000d24028039034465241104c0c2e8802201d425840361803250104456000c1c201e500700c01c00303030494191710301904101e580d4a50414501c90380d6680ca008107040c07083c80c108a444580d00030600b0f0040c0e09188001491940049100321160070102c0103000e0800d20100742c45004801000141c60840d0b0f0000800200030811956416240000c001c1c030f681c5682d9001e0304c5a019842 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 434131555 1250 434130305 434130331
    0x3030c0a05010b01081e1b0a0f0905030703030909020c01061502030d05070801080c100509030d030204030b0c07080d05040201050f0a0c0b060907050d0218030d0804200d020607061103 80
    0x41c6000d41c2076074410300c642818000c0382c5041c8032075059400041c14416651140c0360380316944400c2d9030000c0340b54016100390f0380c490015100e00b074a0b61000030110345044a4544a100c0e030356441c28541da403131a0348001360005a0800080c840088076800070312018006034004070304c1684034a9400040310301c1c0b0318890050b81c00014032450f001c00703500541d42d1104450500424540c504080e41c0d4441a00c69000c07403042d11400d451821035405103059441080d00034048a0b441110703002c000d4001d50040c00b054030500d40603000100c0300d4111700d0450707404036402038029081030818000c480207404050400c9050080c24420b00c484000b00101034a00a6001d035035122a410850a1582c500080178080f10b018612400402c131499402c2421918400446a40180d4510402d50700341001d00020300f4056140c040c2445004d0001d521800f1180182d00441c900d1321007040c80f56040140d803113102011a0070041c040b100701c01502d8194042c012460051801180007425544c000c0d9240c1d0080702c206150050b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 434132805 1250 434131555 434131573
    0x406051504090f0606050f1c0c0c2d14120304240905030f160b0f01080d08010f0303080a0906052706130b1e0106020c01030e0114070305130203030c 65
    0x3200b03000f481a1510b105204220781c9080c00710052942c841c5000102c107400c00091030f40032604842007103094075000070700c04001007405400d0043c0b5450848205640c42851708941c5c008078040c0c1181004440400c242c8444c004203076964802c10300d9509010081d1500034105403a44200c0d5007002948030301d00c201000031142c3c1701c1c4032914154410641c0c4202c0f42030b20304600c92001500000803101300844140314941c50b1400f11010007021504164010240390201040c4003410180d41d0f40e03507040c0c0e48550b065820b550040802158071201c24480d080142000712410000320b80111022034000b806d64102181d00115031300d0f02c0e002e98009941a66060254011003001141070b100820805100000a00b01074206602402011109414041c1040002101051101c03403042c0205240c5812082c2d41211581e698002035203034051000034a02180c100884410001010f2256564084401a0b250201c1d01d403114114020b10300103289014861003441c408000d80d500308090114000720744000d1800d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 434134055 1250 434132805 434132819
    0x10e0102092112030907030c0909111503060402030c1b0c0102060108010b010806040b0f1207030203060c0412060b01051c060f140d0807030311071112030c100b0406051504 75
    0x888240602022406281c500c8042e00e030010401d224a80d800424498803901c0d0b9a240c5810f1240c40e50004222036a180d00004082d04103820050709680540040d201010110041c49200018240300d03504120003007000559528003130b4095600620b03c141510704108281806420b00c3c002c1101c0c280711613012540c620f03115a41045a617024190f040001e2017141410000640070140c0909814030603929903603045810380350356070302c000d8040004000d00c01aa00390040d842d1169440d0000343d0003802a40002501114040d04a8084410006400070030802d640c440100138031f1484102410400d04015002800318184a01c1c2d0320b600c03800200052040c501a2500c203103101e1584485034a900920b824901d6036507000c001c542c1150401c015035594009031074110001c0c8201c961603511030001140241c244030000810049e080d100b5200c400c901c1c0c10719045130b42c0c2d0f401030805100007944408503084d0248082c0e08200c50032000581b0101d006a26000014036452802d01511214200894104098 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 434135305 1250 434134055 434134069
    0x60115020712030e0405010906081207140717010b0301020a08060405060307030b0a14060901290412080406021522140303010303050c060109090b010608040f0f061d03190c14010e010209 81
    0x4000e2300d20b0400c622450280903a4681020503034a107002c690201d030144c14000c8082140300c110030800c00307581810303448012005500310041c144800329841c080c0c25401e1410f052003105d0158090317407120300c0a980c8007010400603000c01490250180500b420000014642010590140040d1240440c00000d1107011029218009204500c06d484580041201f208994010001440215010034415071403440c0304015201715842100ba002401c90030340701348490300000c0c100361a125402e4400b4400701e61030304440f0010540b00c6030b181c004070080401d820803008500380f07445440741c445070410b03a1852102c141950002d9000341d000c00c400282c00007800d1018400a409423041880420101072103840c1d0460100b07050282005001c4060049410b00000d1b0aa04242c0c0307601000d10b00c20740c40d440c0703025009080c2c007422240703c1c03050a481046006102105549104401e80140c416011901c0400c55002000b9842580c460b080c014840186090a004005100c0801000541d03140034a8041c0828 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 434136555 1250 434135305 434135309
    0x1020306040e0a0803060d0c0e0907091b1707020f01020c100c210213090f060603060605120a1d060112051002040806060904051015030b06060705060115020712030e040501 75
    0x6030080568040050ba188003929080842031387c05400e0a02d8514180f030203074410f0b0300204503a40801c01000620305000444100b500d9005c4400e0105a101316011140c40c030340100364902003007141e192505582d810141030740c2c0c81881d5104507103003020303100d030360307900f241e015510701c00d07094206c00e400c80ca9148a601409a1086551500c2c00400703a100c0c1c4248000070b00c4003402031685400041d00040402c03816006409400340460400071410b0130110a8020b0900e0300c03820703000c04e04255000031498011002d0f02c0341c10b81d01005c0302c0c4455841621200040180c031040780091301a4040c9203640600420005000c1c084180b0000e05d04481400e00354500743c0c190000c0a15180100300034803082e100418a01d400c05004c0e1211001c07a00e8520307101d428601991030a1154501d00752501c6500c0c41c1124140341142d00848003607490b61210030520040340310740b28002d0420f0b0b0118004104000007000740d0f10141050784180d81140d52200306080e18022411015000181c000240284034a841d1240c0d0380 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 434137805 1250 434136555 434136581
    0xf1404020906180c0c0a020a06021c030203060112051b0708040f1208040311031c0e0f10050301030b0406110a11061003020f100203120117100b010206042a080102030604 74
    0x61008010740d544143d2100900140e01e918000c561502c200004200a40a90340d009200648280d20f07008000c2d510b49840c060312818008140b82485100c2c040e1088a02420060f9510320070041c00c1540e80300074003409006191072007292030285881c14010009083c400f40b0599213150741d17074608104410b404c41160000301901920b0030700400022000c0381101c0850341e002c2d401d00f4015005400090038000f80c904a00f03003104401e400c1c40c0c2401d81c82400c1e2068000201c1d440c840003c0c06d0b60a1000c114003580c60b460109608100600115034240c038040d91007803003802c1c007044100000c400c3da41c6076001040d4101c00314000c1c42c081c0d000300c4028880346a00c080d108070054041e0346545c00240200d071130b9403521401006082040d01c8498424000c84690381380c1c8071026481565280ea002c412040e0007204103440e0300039100740011011850040030400c60050b4002e241c1601c41e034079144840c0441c2000c03849821003a4455200768659844804020025480010303140d00c3e250b42444151101e03840a42 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 434139055 1250 434137805 434137819
    0x80d020c03120f130f05010207061d0d051204030e030703140604020a090b0310020a021203040b01080f0303162a12080112020a030b0405011d030304020a1a0a0e040f1404020906 77
    0x402c031038500c40704440b03042d6001740c01c122100300c1c14188140280701d11080038143c182041001203041c00c0400200d10403c0d41078044070021101c0f60021900c0d4010a42008201100c0501103008071b07200352440c1e08240801015918002d03a69aa4140f1081c59103845a100741c00500c10842903241c580c107110005c05914100388100c00702500000c1d00c402c0e00c00000e039420b0754041503085082d8800c02000900b9103103207002c181d4a04045c100b211990000f482003403030510031060381c803000040200c1980d01035480440710510156001c0130564020040d0301070003800503c1801c2c480800c050600303801c000d0f40e010f21100c114013080c0440003810004141c000300002c81a0101d00c40c0140c54810a44084a800002100d400d4940c2d15000d03001d8905903c510800d61a0310b403402c40340d1200400114041ca100b21640000c0300e90b203044084240c0700e103e02c130745031940c402d1003c000c40502501040000c81001400081c02d108092803e104a911828080040e10003890400045040120f00d16030408400c4802c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 434140305 1250 434139055 434139061
    0x10062907150b04060905090d0e0d0f02010e090a050a2f13090203090303010602010b030c010e060319050c0406090504020f070807080c06010b0705060a1a0d080d020c03120f 75
    0x2045a4899444028200d10064520206244060380440c62180c0000d20501c08103580744000c401510094404841d64050441007414850107102c200840c0c05002d4007820b030020341c6864a0f0140840144140e06116501c252805160340b140130948c8079420848000038142054810075044500a60000242a031074403e603540d420420039207500901c6031103c44030350390701c03a10600a074900c074582c0c05210b0141c008420301c4503240300440a10705854a40c0d008100320400441016606c0f104a035143e4045444400715030f09074240f4200a40d401180c00c0480c89908500071004011580100c46007015980c0104060080c03e61208810008003800c0303605600300140920002e00740c0c49448001003050400158500800c1440c40c140c41e2003641840c1911015a55404000d0780d980c02548100e80318000c0100150302001c052242034080729940b00e038124240059420721500b0910004161031042c1e0900041da0119103030b000418030030054402654803072403561140c0210b54405010820302070801010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 434141555 1250 434140305 434140379
    0xf061c1d1c050315040603051c12050420010c0c0602071d040b010504051b0703020d08012102010f020313080703050708150c0d020d050a0902090c040e041b05031006 72
    0x81c1c98006542c040d4080c01c81c040301300042c0092101e580000c085016212102d1a800310340c1c7d0342e900007084035464190710b02500c43c00040c100c9408403401442c1c111400300311303800c1255407014003100d036030181403115460281d0b8940849030441540224010303405600306012031011441602202c01c151a03040c910742c2482c0c0d40721552001e0500a090103196110009031050503401141c4440c20b040c580e11300e42c1c41c003003800e009440d011801904030208280100008080041042070010070703030490445e80544005900440b1440d444000007000c5100601c506028840d82c5440c440c02880c5610081c03860520f0351600314100621540803140e140c21120f0a1211307000c29084081d8444201c5c1c2e109541e500c1000c511200034019490a01600c914100820402c004103038020721000b0700071a0034903103a5544a8008581e4415409841c030505030800125000940001c650403031801d0385070504103020b13250030101e8600200e0389190a110b6071074180c10009404202d01032f5020710342240400301c1c0841d403015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 434142805 1250 434141555 434141557
    0x31e0606090902090a09030519050a0315140f0f0604140f030c03060f0a0603151d030903070303050912061609050109030c1710110a14090f061c1d1c05 66
    0x3c41d17500102d40300ca550808042c0b14000b111800001400f100f488144128002415504840c600d40042460100006c0001c1c0100280d0003c03a04101c5071105403c50403400e100b9441201000550012080b00d407614550b0743e550064001791400f02d401d120656907110801c085803d84203002070180c0c0100d50001500d44000c071f1950307800588440c4506c0107031203440c400c1e030003442642e1014000c10b000050146c070407a00758220700301c1d415503545910035045004220300d803030f8460900b03120b606a00503442040060f010301d01030000144c00414240e9801d200514181c1002801c59082e040e8041303200700c01051917042074409015101c2071038880029030460b80d03010a0b0510b60701035500c10400a81046610b641e00b00420380d40140381d4001884802e41c091040000c0c1d8000c1c2000c14003090107103401c94070b0000d02100703407011118020440a4031403462018002554401d4180000e905001c0d41904400c3c00107009640300390b6400d8001f00b10410300585998101200c40c02c480600014004600d00b006600c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 434144055 1250 434142805 434142811
    0x50c281a0c0316020c0301050a05250813050111070b06120304050d0f0f170405011205090309120a060212060a0b0a02060a05070905030f010507030b061c0f06031e060609090209 77
    0x8410744044440c140c2c900310305d404002c0d506600384003c2207034440c00740d0801800703048c10340c032a03407140110b030030340c900514050341c6004002514620000f46080ba40c030106445c410b000f000001072030102c828004115a20454066481401c1d46081c071409003800c00145003000e0b40c0300b0145003030909010006800a00c1400c000e011194880300350824810b00c00c0c0103540d0356900807400c1609a411540311540390b0858421540032802600a01c0d060400310701480d40b003495490051403070070aa000410404080408001c9498440c070701070400043c08600c000c24904000c0703108840746103400303c01c00c0780b08038141c1c00070742880c601406551044ca400081c1c445d0480302ea0074004c1040c0d56141c03404c80f8001a168005941031050004483c11144107501640c014200f030768040c42100c00d15014410b1500c01c2100580d09803101686010606070242d01c9022801c04a0740e001c80c0f4107a9940b41e5050028450195940c0c11201c040302c1400c01482d0320a6800030440c00d1018003c6800940004030007520003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 434145305 1250 434144055 434144071
    0x60c110f0c010e0f03030d09031d0a15112a0105213303150903030406090507050409060c1806090b0d180b040b0601020c060a050c281a0c03 61
    0x40b49032002140ea60403114020204003408403507d0300d07117a0450402826102d0400d50101d40e880c40141c12284554050030800d2401502c82c0030180e14054084000c54014a8034600308510f004804070b004800b8030940d58001a4416080d41e00e0a040511041c854003a1a405040c4901004400d00300f082c800c280b180d2982102800045942d1043d00202c4003232204447c0d0010300b2142039441501498400c0d0b10601d8401c00d500301c8141d9407681c103808005000940c0c040660350300038000280000d00c3c0b40c0203680c1c039511807020f40d4041c694030000315094410b0221304030354807900c503541090761a07071112132081c0391511841110700951800c03202908840ca00d00800d0b42c1002c0004408038003519a400c20b1b24001480790031074050220700e06000ca4000e90981c0c007100c0c50b2003000040382140d8070000b0449074804000780f000b0701c2d24458910175121580b000d40c0442131801405032400d42c0c13103a03191008104100c0081c4a25600f046841d20148201080020000f41200d1b841031003d80141001607d50100d04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 434146555 1250 434145305 434145317
    0xf050d0b0a0e010605040c03090303060e0c031f0504230906100b0a05040807033f05070f14011a01030513080a02030d0f0603020f0402090f0f1804060c110f0c01 70
    0x2d6071119805028980c1116400c14100391100b007030141e05501c00c600c0c03940299010000c071512245c0301007100740160398030343c10381400b403000ca084648840700c081e00e2030340d51030503a855050303070f400215003914140c03140360f048403100c80c44844800244500c00c0743d002d4520703030207441c1510309090144000303001402a040f802d0b07000b094002c4043e004004860107800c035603007100e0556507a481e0002001c2c0603041c41d40c80108909126020720703040d900404000c500448886035036000145000c44403500f0119040e03644c0c03c0450008400305041c840c00c2100400e0306d10002c540d45c80300e0036200d00004103011469042501e07000c05c004031090300c04030580d1666401108199641990001203155005428100803203038a081c0d02c012510300254801d000b128800d40d007019101d040b0b001040308074010b200c01d2903007103c00406881c045d450030400a400d203090040c0500311803140d040c58980030b03480840f0112201d5a482c8044180f07183c0000808411070f010b10024040306001e141001c1c0c480700cac1c490701e040c14025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 434147805 1250 434146555 434146571
    0x1b0d020723180712020313110a0f0303030203060a0b0309060a05011203020319141603020d140909071b05060105150306010f1d0402180405010b0306150708090a030506010f050d0b0a 79
    0x44242c00c8000718180b001404c5d501da08101c02e09500520443d0421122400241301c1100d41d4103020820400302e0b1602c40703500c0d810710b1641c0c406402941c40202940e078015591003000c140c3c04c007660059401048407000421180ca400b02400007110810707000108145442c01d03400001941c0003045a104008905000c0480301803803200b621030381c00c060620740980d000031440d150800034821120011502a5080b0303070500d042900305031852000c1c0c402d903c4a214040142c0071039401c2100246401c030303d96141c0381c9011240310103014010149101c04503400c0d00b00c8001007190b031801070151000c02c0400c8208524506003000047d060440000c45c100600c80e800041c1042c0134000c0003800d801e120b0160040d5618009500c40c4250615200c41c21440b56144c1000130407070b02c1500f000d40740f03d0301001d8102d805218696900007a207811a03002142c1c0d070002082442080d880c0c0c0740501d00210300c102c00400301c41d41401c01c3e0b0302c5800c0301c9800060003814000c1c8410085040910342d030f504140901000176000e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 434149055 1250 434147805 434147807
    0x1306050f040509010608040b28180c26060c03240619030e0a1e020d06060b120702030a0507034a06070506010b1b0d0207231807 56
    0x10049511503030f80005903c000103541ea400c43c1d081e52142c1c0c0300301c0c402816039660140c4403290301c009d401143c0090408002081c6507428a9221280d607240b0740c002880c4d112203030707510031403188040d0f01302d0300814451590326550488105562001096414060710840c034203a020302141c1e0200810703890441c01940c0e04a050b00d0145032002240901c0540714641d100b030705202c01a815640c1c0b00101d1f002a16114881f20854400305004202c0f03a8080103401005541c00e26010302500d4041c020b0740e111034410103a40001c8c51070301c244001040c419000ba03072100761a4001d9201c14400524503403c0d134000300f001d8040c83e40e01000301c40016034903041c00c4401034005001c400d003c1c20404851422840503888901030382800c02a000d075448046403a21610408507800d120345170241c1900203100354459001480340c240000c004e07085541da44600307103180f4881000080d1030038040007041400768110600900040100040d11009155005c180410384044000401c02d141c208a14503e041580000495650303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 434150305 1250 434149055 434149057
    0x602070c0902120f0f040f0201050a0e040219030b060f04050d140a03182903090a05031902100203010b071416031a0703050906070c020f0604060e04050c1306050f 71
    0x3816500d60708540340e007010120a009802c0035034400e04101040000100e101e0070150034280b05940c401820018820039a00544003500405540818031540318003031b9080303071a54806898414022540300b001320b29408400707000c0754206603205004080030072110809284071702c2101d040b18003c2e50103000101c80f5042414095060220350410350280207858824140e20051411030052008220303102d03d0b5440c5441d9034000c485c4070035404415a042d0310040c2014041000e1680f01c1403980c1a034030703445080d54982d801c552050540c060391111114452120035410410300c0c502d080c1c10f040841c959410407070113919030b00030404010401d62000002d184a0a000d104420302c1c555505d00d010425034491030554803c280b21003580140300444000108200d00c0387c0a00d0f030260341400041c054035122840212182c86220205a82281c402c903041262626024010001061155246400c1c2c5103880c0800c4169070004e02908c06000c024000640207009504000007240c0035401c009660710050101d411907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 434151555 1250 434150305 434150309
    0x5180109030b0c09092202010302090a030c060c0606050a0f140f0a090e0f0a020d0b18031207302304050d020f06101203120c12060603090f0602070c 65
    0x16550040c007031030220b41e1001d403002040440b08481d40e03a1b40c0000031030580803201800751600001c0820701703000d940290b0060910000c045c0c502c404003600ca0310303080b1112510b0361011f000035800c60040c20602c80e0500c14400544812a143e4188500d455140007501809000d448800d0466855040040c2d4030b034811241c8645000d0118014103584039040401004808400c43c0c890207001c0c0000c04e0130324040344019076207a004041881c210801d071981031200400a2469000b08280e04141d446120104060710340d02c039000d0782d800090b00d08506c0040080d40c1829002c0d4241c00c90440046081c4102001c400d00c0c640602030004000560603221290b005031440e44412004079201480140140811402e090f406240c00301c4d02d1002c10322283e1566000106c0d5000c044500341035062050810926121486034020328005d50315129980580040f80c3d4081480e201044d81d040b98140180554000c1400806060404000403480c0f510340011080d0340703200c01066698001107450420040b80801c0c80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 434152805 1250 434151555 434151563
    0xc0f02010339030c020a1502071536050703200604030605222d060e0105060f0301060e060d02030f120711060703020d080402030c19240518010903 64
    0x1c581c900b001160340819040d120441c0064107140d04210000c1c0000b400040c982c4e4007071a0305000c09020050003000750001417080f6081e5202ea902d60900c24660700503c581c101c08114051b2526495280400464240b20041304120a0501e500030120300013240c0d42003180c0e001940d903548040001e800c104540c01402c04140c6c8410042004410301c0440c0d8407070340c89800c80300002c1c40c1d4000002c81d0707400c62950106000304082e14000c003085541802032802110542015001c080b0b000300303540c610013070301ca5a20811079641c0d517a1080100c030340f07000c484803101808190020400305050400b141000800180000d01a01580804c074003151020825242c0c60703400c49043c1c980c0c01440400e03000b520b600000045c1d0300b06005500041d410708c0c0190850b070085902da001005100403001050390804e80080c4207903814001e6030f0500030b6603294101e00c24074200c5030380402da803243d040c24140f0103440b1108503240304405202d2450310b0399a402004803500301d010307049641d84184041c3d0040301c11810300d0301700030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 434154055 1250 434152805 434152871
    0x6040c02240907091b1d180709050402090f010e1504080601080715080708060a080d09081002040806010e1306060f05011e050d18020901080f0601060c0f020103 70
    0x40d04060300310201c03401806410203840501d41d60b0036038041640d16800e50b01e40c9581e048100080a14002c1d210300ea200c3c014440c1083c1c80f0100100010a055900c078600036218015800300050720f580701329040090030040300c08504000c0b5850204604800c01c8007000d050242c1c10060550541d141d81010908a0b111005a590b40352112103003621903c0070b124448191148803404600360f441d621a001801c003060380c40300780d41d98a10f481220b103d0805810182c0149049802140b1404244440c14a040440d1220141c0914107112549407440b00013100720400d00c1844240240c00300814482d04441c441d1040c007031701d6218a46c8d0850b64125031400145900d1405500081e2580005190b0048600036200c01c6000103504581c1c184c2c500c81c443c940e40015408102050f10700070a5440840c0761400140000c00d058050703070100c0d80d400743c00c0c1c0020320b06506c110148003c1101c1045002c3c0980002d10701a0f00420059490000710140140000d0525495000c825054603030310110002801c00d0240c08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 434155305 1250 434154055 434154103
    0x3040902070305040312140d0209120a08041e1511030c2b050a0225050a0305010209090c130b0a170732030417040308030a020301050301060f0e06040c02 67
    0x3800070382c8603100c226440074144000800c02405603080030902d07480a480c86142490814003230009620200a10342d102075070083d1607041207400c01ca60a441481000b9207542c4ae410602c41100c10344042c0d00301000c98002003008c0c4201c0d00031088511140c40c0c24104407004e40030a40d1154207500545402070482c0c860182070785040c0300001c500d94404036420b8070300c031114811454100d50310f101e240300500140e4400b1483c3c4001c040f05d01041402d804400100340152a1518001500c80030603600c10b4a6503900401d4090f450300e8070311070440d0810100c0161910303200080c401400600352034491142803440c045025000c25000701c141c00300602c0800004c804902c0c1456010745542020400707200c3c1e00340300815902184e071203071081510720b00b074840c8a181141d4a698405807100010005000300d82002c2c000000040c80c4080614003c004503800543c072581820281800c69020798080c8044030102c0b8010400071059196050b041481940c010480c1035040e14103902d4078400c558a20102c104001d6a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 434156555 1250 434155305 434155307
    0x40207020d051f0e030316050904021b0d110d080a0f0906290f0609060c06010611012d090c2103110114010b070309080d05070b160e12030409020703 65
    0x14400241c02004128030100031150420104c070b003401e07000000c50307004101040c241c6030608a0f40d842a10310b45003048c40e12031000041020f80e00000d02046c548112114103c801c180c0601046d4464940741c07401201c0d5402e80e0798020f640d5aa204031010a00042c00e02180240002d0b8100007810429280d05000c421824a0013000511041e584601520454400340100d000f01100803401044000d224481c1402560300300a600c2c2e0000459a0b8080b00400c03032a00d06680a00c06035000b018242c443c9603840c164040e80609446601c0c981d00c01c03131400b0100300b6420f13168120340c0c419444801400007401e540e041c60054240140c44d04051a1007840c0016044401c0704441c2e070681c154800d98508040754440e000b503d0a941c20880703401c0310001c0050060002851000c042c1086d03e0107813034032100e415500c0008508040006806d02c0000f040010580d05108482d0607040d000300006000c0003180114460003010f5910700404144289030385501202c03a01010810f032005020444011075480780e052170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 434157805 1250 434156555 434156563
    0x2070b0d1b0f021005060a05040c0c0506010303020c01081003081204020f03010609060518010f1418010f0e0903030601091a07020316090b0315161403070c050609010b01021506040207020d05 83
    0x14030b10014420a540d660f034207103207402141e015400240240002504202c100001792503e200b103402004050658a80800d1040100600843c025001380001099000c00142036540040415075840e001e07000800000f0455011601c46040030100903030b1030b441c0d80c40056807204c81e0b034114550540c04d0540104440556511040440cad404899042c1e1984e901300b009c1d02c44003001d10820400d0100708104000c805c002601126042d1402008407019500d0807003a6411683c00ba0001080600940824428424504035054110b12503000a50552801000003400800540500c41170501d0f18001d42d12801c011000b41c648841d40101a2050107940e1100c0d403078656802d2240c0ca18060803c0004501424003150003400034031401216640d6a03140041480031505010020381004034201c0c52540e030321031440186004035207540d5022010b8566040041c60540043d0101070684d02d00104010140c2c0c001071014050a101800412503940301000034009024070000a0b400100c55094142000300c041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 434159055 1250 434157805 434157827
    0x40809130b0301150f050d020402130303050a02010b0d0f11150f03090709050606030a1a0d08070501060509090706030911150c0f190f050a170d11090102070b0d1b 71
    0x60000c000e150a002240010604244070b405005e00749950300340b0881c1401100818803038006031002d468107440324188000b01038194029030000b1004030310ba80c40c0c01d1b42030003007404464080704e0300505007031140c5542c08803550b2440c00404a0010b2030601d0229220340a6107074401000725821601c4021542801c2a40da00440b4074410600a03510f010039403020905c43c90f401003801500d0a411a034411701244024030031401480d1046600c800310800302c0c0e50b9a9001d100349403154110356160782e901c3c5840c41c00c0d03d0554125620030480502001543c0b0400900c01040700d0036480c0110b113452890a000590403032225078990004d401a0240da0500001c10041c9112070f2a2000ca9100f29100c2065070703200d03104010b611a07144000c0424901040c18450802c419500404c25210208420394070500c084003090050101c0000101d608a0084010700c290494003e00c028102e18003000c03000002d49907587c1e80101d031210314010600a054180c244d0100c46040500000c0d0740d08040d60420203000da40c0d40c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 434160305 1250 434159055 434159059
    0x80f270f07050f0603011a0d02040e1311090606030a09080c010c080106090b0a050904110904090309080f0303060d020904031e02060f0c0a0e040b010219110f0102030a0804020405040809130b 83
    0x10424601c20f0620400322812907240c0307110f2000d401e840c007c02c21400c0d8404528140b04940030301000c41c0c6a4038090340140a85901c4404405400700e5150407400d41c007403110010b00c0740c0005410001c0342d444020440341d100b040c02d180000d08110074640502c40e40200481040258a805021031105804c404001c4c16102a5201c543c4540e6075166510030038450801e80c031000450a1150391a00d00302504020080403191180c58103002c08500480c08031210407600b0303000200308c0c10f0100090701c0180a51900c172125034016500c1d52828902140038002c0a4400a014080d00c00c005018944031350208002c903c01e04035454020403c00074000d50361a010360390040c3c0d00c0b001d100410b0b06454194100c90307102c0059185c841c1c80214500403c401480821011410750142c160340e031040700740340124099614441c40040001054400a005003d603c40300c0c2103047d503200300180411141c0240b0300580c03040d81150080382035512841c158079540110301100380c1103d81d4a500e0842c0c0001c8c0c0c0c00006d454281 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 434161555 1250 434160305 434160319
    0x30b070206090d0c020f040207120c02120c010219050a080403030e010f030c17070216090204140102010203100b09060d14091501150e0f150301030c0501080f270f0705 73
    0x1040540c81c0c90342038008450002c07441107108800107050141b0b900105943c000c00c01400c0902e0b80e02c030a131844000d0440100018401503070202145014600740003200301c500000c111410355200044d507560300744505407240380511030300c0c0c80401008100e00065241d00c181540d80b250340ea4a800307444040050507031408a983d403135103009418440e1060010230a070607a110741c1da1108420940b01c00c100003415410460150850207444c01c1e881048400042c2400640103a64515182c0c00c000140e40403489076045900400c1405001d40d00010703e2015200801d01460380c0700000c000280141c03042a41c04200390782400d076803201d1640f03016600c5200e44216000c0c0c1d201e0800c0e900070148040700901911b031790421740c800b1981045200d44007110701e5200240154214840d0b080018081d00c0c0d000080c0c003407001000006004108611212800806c400e0800850b141440300d0310039840c0c00f00800040c1c01c2078103051540c4018007107030208550f0300400020707642c204296418050b1104003d00455000391030b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 434162805 1250 434161555 434161561
    0x161a0109050a091e03021516021605030703151407090305010c360b0f1317030d0e0a02040f0b030c010e090a050702030415181409040206130f030b070206 67
    0x30b4030b0150318000755002541c6406407018485941040c0b1034100180d0444c41842c0240614144a2038a28000c45a41c0c642000342050741c1c200901e80030881d0007860b034215028204002980300000d5190032340e984100031205101ca8510f0ba00024074040c003101e0f810403400824803c80c5070300701d40840e0581e40650024041ca40b803c4800b540c900041c00461039071401158601081c12a091060001d019100007000108a9460380522510303000052030800e9000c001481546008500120320010090940780c50010082e0503412a2a400317800d0450a40740c5d100c0a07644801d9605000300b400442d4000c0c42005042088001d0100801111300d1207402445500d2249900f5070151200380c80c840c3c1d0080905280e41e80e400c03900d030081d282c064045010340c40f06000c081080f180004400f6000003595680001d0000058445581091280e1004617608002c03d00101300362520b0321156802501924607980c2d40802c00f0a200e01200182d00503480404940710110401564640840c01801180d0844607951 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 434164055 1250 434162805 434162821
    0x50a0e0102130501030b0310050109020a08091507030c090513060f1a0f07020121050703052d06130c26010f1a0f0a08090f03040f0b161a010905 63
    0x8882d40da407a5011003820b180c100142e61003500084400140a400e45a5071400c045103001980d40a81100c220142c000c10813004135a4008800f5601070306160081c8034004e80503c0d07131100107001a10300b070105902e1b05005604640a03408003001004040c12600c40c0d4801007491500401d0980142069102d102d10000f4102c1c60740070100b1903807260310b00110303e4400d041c604401c080d44420000c17418445c1c4400d00c02601406500114849009420041007900d8801d40050071120020040c0007003000f0a40d030307021000001c1e140c0030310710000e02d0100851925007800240440c070b0341d04120500c150601400306007096025541c1075441c0410707580000f060040103001c8821100074010382d85e0300500745c0c008012907200b031141c104c3c5100b415094140351203000c100c001403940c4503803400c07008561294140000d00108019014440e0750340005503080c40d06000c82c50f00e803c1018425442c0340c03040407a060590003150703100000255408200b80c3c1885054070420000c2c41e10074441d2003100c510f01000180f0007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 434165305 1250 434164055 434164057
    0xe18041b09050c0a0e040f05010e1902041202090703060b03010b1803011a090a0906020f030702100c020607030b011710170a0803010b07060207022e02070f0312140a03050a0e0102 78
    0xe0f9182840a820304c1c079140001c0710602480f03403000360310507200e01d00185094000d1180740c0c080e00c0c41d100801300c0d901d04102030b080e080c465203900240a030b104000800c8401560401010620f078121800702c0c040c0c60b01c000441c0600a04e070880412060008000542007001400601c0c0040d152200044e0b550100d408140c2220031355486112503078140860b45da8940360442400342d03c502c080b800020301c41b81c2901e68608070b80081200104c0d010002051001180c0c0410601414041005083c404000e40c007000a4540340050800c60a1503160b0b00c0048181e8080c085200d108114111142c0407446e21b400c5480503520984100c89841c07482d5055907194001c0401c90080c1c0c0ca410090552441e482d129105003540d010700002c2d50b00320303420b01000b001a502c0c0504400003a1403140c140c00c4103060385206420385c1c0c0800240c90103541c0650000c2007414128200c00f41100d800914084036018010001e41d44001902440b00e000f80001035850341d4581c065014501441c1107800c1040502c1451743c1c2c207400c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 434166555 1250 434165305 434165311
    0x708091c0216081b0d08040b180f0d030e2b0b04030f050415082206061505090f0f0d0f051c1403060405071202070b011d010e070e18041b0905 62
    0x10060000c01e103070240e0308042d4085040c40d132080015514040d07440d2030340d42d410b4000ea0080c1c50343c0703627890115100d94540b110f80c00300510811915640d1210540c0d8029200b03d42c0700c0401802243d0f80c0b0b03500c485054030b060100c0060140340c02101e0201130b407131404000705c110454040340441d2446203000c0b19184039034180d45c2039408030f0024107124021860192500940205190030080900c1b0000046503404560f51410314844d40307001c10028100102d0342401880d0058581c2080020704c1100c00d1039842200884040303d0545840b08070410410205480488803200505003550302e40344c0303608101001488030f070349481c80d01800d1054180c5200850768904030001010040c8400c0c03021507014031713040e17010580005c16414210002144803a082040c2d80100e9010707100244080010021140c4143c00c3c05d00c5050301481d0340100358100b001d607100c443d038003402d0401002840c28855865440d01d0501280444802c0d402c90107902d000e1a000d800c080c4440ba8428014250550004001e0070328010640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 434167805 1250 434166555 434166583
    0xb0c0307060b0a12030503100602011109010507020409060e03180603060a060f0c120e0901090908030c030709081b10020c0f0d0611040b07050706020a0b0708091c021608 74
    0x128240141c1c481a020340300040341030754420403502002070710440b072812030070f80e062094680c15280c1c0340c00039410090454981c0808103590401460310780071a006011103034050824248903445200e940080303001040401e5004125514100700c10302c0d0b20302c0010290032030103034403003044009400c84003d00410b80400e641c1c4941001481c0c400344000b40c01810020310449480c03800042404294076565080c10b00346903190042034044000182038100141c0d41030262044400602000500d82d403001140c1c40000c1c4110050100032001c141030038441da101134018480903003166444003038000202c00c0d850707060500a02c03940c007241000039118004101061103410081c2044c8600082400b8096400d81d031680440d4200d5641d84210541e8051070040d0010b00003c40001d40c0340c62181c0381240c5030132a40d0f00510700b513502102d41040010001c1c1e0503a076012809140030703d075580766004480e00d09200301c4014000c0c500516891407d003980040d42c09490035200c030f02c280500d0365034900c2c26140c4200807001340c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 434169055 1250 434167805 434167807
    0xa120305030a020a021c112b0503270606090a090b24120604050d080f0c180301050426070503071202030c0604110405070503190c09090c180b0c03 64
    0x20b40000c241d039000e083c610080e801611741111403202030b024806407517811000469058400040340d0401084013160015821454400c4101242111048440155852010403e00000041501d0440100d030000b0105080010400e00e102200e240d44501e022110303039001d8010350b0001001854a07001e07030411036400140051040e140d214410010340e040407a110085140428244002c1d1120744901001c00301c40f0010341818101403800d82e040860740c0d11504100f00101042c80501d6000450b8242c0014900824603a9514441c900604550f00c1070710165040d4681000c00c810b00500c410a852656038100c100082e401c07c0d07500c0201c0311b0080c813401074a558001c1c00220300082c81c1c010240100320303050045a0811040710700162400808441c100c030040d1864589224500b064003810360001c2c00350a1407411444d00c1c08580c4100c205000b84070308010380310490148040d004403110341c05400001002d001d060060700000d004515801101c0a400b0b8680e40300040780a10386050301c0301c040c100c001071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 434170305 1250 434169055 434169061
    0x5010e0c0703230919050405010803030601080109390306150f08040f1410050601020c3304080c0310150b0f0c01021801020c0103090201022109031002090a12030503 72
    0x260810a04000301500000e901300034802c115a01e950010f4005c20749035982a41c2c06007800c080c04180c46041e40701c0981540180240841aa008072140d070656084100c000782c0c0f4081000c600c82e000b00c8030050208503440406541c5040c1d15002c00a01d240801502c00380b00c41e603070350003034500f003c04903519810010f0b206052030f0007014401c0d503c040d00540240d0707200a80407059201c0789212920f11070041425440401c460240d500d26004807640120f090028051801d4007a0118520320143c52291604900c0b40d13004000203480282e19401e43e40c0746e0031240b5200c50710703081d00c40d030b45010b5000440c0c880c2c4681031642d000b414140c00340850210310704c003990103141d203020070804003500800d0084481050511500403100c40910103880300c1140902d815003200300314030029080207040b161550405080c852500c000d82d80004580c41a124141c15540c1c0c0c100803c0503002e064000d0f005080d9143c02034100c400c40b6030400340c002d015940000c4070781e0000d007641c80c50310600300c80380c030b100040c0070070005c0c000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 434171555 1250 434170305 434170337
    0x110616030c03060b2212110d0f1a07090803030c0d0b01110124050405060a1503020405031603030801270903110a1401060f0303121a060d05010e0c0703 66
    0x40a000910706090124480c1d496200620b8035811866840e9844546003d00118400980c3c40c50310051106022a008000302d6840f000004c05171104014018078881001000b0400e0001030801100e405c00391507102071006442048080304c0646038640002c540030390210703070100044100c1c2d001c3e20b24074804500e003682502d42100602020010281400303038030405042c0b40c000c00c0c000c40d0075460b0740052400070b01400b0844001c410b80e440e0481805030345460100035541e260215a8401c0d5442020001002d9444c1c200442c06403080e07402094142c008c3c0c52150704002480c0c000c040950b0301c00e03203a5180a81e20340c00e40003103140448200100e520709a5540d80c40340c1c0358940c0600b190034001d1802c51900c00c01034183d075281100c45001295000020707013007a4802c010a00c07550303024056000c1c4120301d030391451b1401030427803622890300554566070701d641203199401180616912000944040d071a552180d6030325008010034400c1e804220400c8002943c81942c940c1201c40701545511400c5040700d18a030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 434172661 1106 434171555 434171561
    0x4051c02010203030a0b19080c04051e0403120f110d06050901060507060b0a050a1502250b13050603010f1e05060304120309021306030311061603 64
    0x112400140e81c08000c0b40d40041c4844404106901c8403000984c3d00344d2550402c003920a602e0704001003503040460034041c4202d0480301001503a85000e403800c41080d00d446400003068103440003800082c06040c0c414061132401000190801100008504a8031071002414100d6400b145600480b8981d004010140200b07032680344165252a1000d0305500070f0400003041e0710340385d10680704180c4504140c800100801403800603519619040e00620356040b982c00c1e8014080d05010b00442401a00c600c01c8166604101e20801c1d49840c0c4140115000180402d804095400d070020f01070361200e001d58060250550b810961728030b42002030440040ca00841190112142001c000755540d010a4a92098014000f00390301c1c50340715005c500801002e08020740c4a2010312101d03140341c280f9030196082da4032a44070070003403c645000440d6240700803214000601d13000090ba80c1c0e1544030b50 = true := by decide +kernel

theorem cover : BRFrame.Cov 433992805 434172661 := by
  have h0 := BRFrame.cov_init 433992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 433992805 ≤ n) (h2 : n < 434172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
