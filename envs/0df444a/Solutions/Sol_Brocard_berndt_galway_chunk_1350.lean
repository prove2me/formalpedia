-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1350
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:31:00.932117+00:00
-- url     : https://prove2.me/submissions/125f8ae7-4fe7-4e13-8014-7cdc0cd0907e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 242625899 ≤ n < 242805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 242627149 1250 242625899 242625923
    0x90905041e030f0e0a050f01320703090b0703140702030a0212030c0c06030403020a1b15052a190f02090106020106170102040e0f0402041e06052107060804 68
    0x58000d101c0240d010640361001c1108541d000f0703050000c2e901040b503801d1009410600001d241c944411176541c10085004400311041b00c04441403807144080b110b0b1507445000e0005200e001b503220300c104500194264a0000b0010300c9101681c0e401640754580e80196074900c01089170580001005903414800d1818000250b12034210141001c0a01c2c0050341e90b80f140300700400e151115244400d0b0207107a0800070040401c0d4042200d00c9040e5025411030a8100c6156541038000900d40203d03001d00180910484005d070080001c0100d070310710900314006401c820300700022009100810015a8001c81d09195456158074000c0c1c1c11140320b0716180511542130f4020807600c000036009078016079960f80007401150b001440b4040b8078001d9600961405041c8010124840c4029010030009d131520350203e8215070f50f50b04114400d070142240f02c0380d050481d11500c40034081500c14680295507580719103a0f1004014041c12002c51004018245540341000840e803880c4010005e07201080241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 242628399 1250 242627149 242627183
    0x905060d020d06171231080304060914010e03151f0305070e01170c040504021c03121b1b060e0303090a1106120f073c080709090504 58
    0x40b24200142c80e0402d549060329040d0540d083c50440f03080b48010005500f40442810900c1403200100324110403462542180051b80448000030515001101a07010104020482d2640244400101c4010846d02840e03000c41900645034400744004c540e4054116030309084e0f8035881085101c0c0c10040ca2070960000727200742a110503403100c45800c22100e075041000108040b0160074503050141c901401c111045064000752507a40b2071480e1a51070140380c440c0002400c0d99942d0350303031103503069600e000c1c0c00c0500254500201042c03406030469826610345146020542c600005600e07101826454500c81550b4240c4132104030200c41d081241c1240d00c1d4041010742910a201460203286108010f040d503151601d002848110503611ba00d00078581409583c154100c03d189003074010b84e07106002146521040c1e4101d070b65544401000c4115949510382c1000d210301c11601c880704035000000c81c1c902c0f652012044400c078000f0b0f0341c0b023000a280c1d032000344075000c0a94801a082445030000100c0d4a0101d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 242629649 1250 242628399 242628401
    0x6120303092d120509060d09050309060a03092006041412030a0504060e090411011d100903050c0405010b0912010608011107032303150a031403030601020d0f0905060d020d 75
    0x420302110071039040d0b841c41010045401c9940800502600304642084d2411000c2005801554040b601040d1955007000c02d102040c0115490b105020b416140c0c0d5003a4214003901400654100b2600020b4a140301510500c925030340e00213480c401403c061078a4a0b103110340c285d080d612a0800e520201d1045504404c40040005048400c03140c5c9405842d0762600402030301c001000c440150041e07451008101c005401c0b035a44903c0510242054194040010380c101400503001c0e2840340c004000030f0703440d4292034125248404491045040350300d4055400148001e65201713101c0c085901c0424032024046160483c0f481402c55000c0000041069590b80d90398291022007402c3c500785c80700042c02d00149a48000549000d92400b072096441a160f9000c0800c5848000c1c078010000440b185001e81e19038404e00090011600070980c6980b000801401648075881503c07454098824142d06d903204a004100b150041c0300c89407540d1000e2450842481510345c8040e00b1080195030800401e0f03042586 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 242630899 1250 242629649 242629703
    0x81c0908070e091c05040e04030c06050c1b0a020303070204090302030c150703050105061201031e06050a0219020601060f0e04020408100501080d0309170919031104050105040612030309 81
    0x110b1140031030700e0030401c56403401c0048241e035200449484541d00c13061141c01c24221401c4a600341c8154290f551903060444111603c03600013400c25040400b80072f05090040064000041c00c54640310358070403100a019a01e05542100075010380080c0564809441c09610603412903009006a901c0d00d40510b46403810074049601a0040302c01c800140a00141c0c9845a44d001d00b4007510322602d0141c9000109008c279005110080014000c899401d007044000b12110200359400310307040c4a0350402c203078018081c0d0001d0681c2c546041000700a0a01d651001440314102c401a8841d280b0003444483c00701c2d5014403015219402c69000c110004200b103080010f065444149000001c2950400c90150304001c8189001c0301098200f07007002010a1141503030303000703085401a03c140d03507080c44c901041b048098004100400c0390160400014005c54840750315101008a6041165030307224810441215914040c1810320b1842883d12800a40240d00c1420300c54080d101c00181110b401c6003407620502 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 242632149 1250 242630899 242630909
    0x60c1712040501060602120f12190608010504120504050a090b0303070b07020a03020d21050a0609020a020a060b19090209280905091225060603060e1501081c090807 72
    0x13650b0f4008108155061100f41c00140301c5840048c5803013041310f00d4400310301030b020705074500742690008245000e00540c140c00c00c0c2042440e0602c60b082c0d070750b072806001b003a04444c251140b00d95a081c01204520400488007500d0000b030020f03101c0c9041000a40040441000301501440100800c00101d01003017100e40c824861a4001c00703824215240003824200024600c1c4141300740315a85d641d1985282c0408210741c81d41207000101c0303a682800040140407560f0024403550301c00216490b00342c1c0d010400b030012a006100c2030010400740d0007440003643c030500610383c0e09840602c0c180a241401e03002403181080c01007450405409100700700b40541c90010601150714200002004911064015241c0c44004003002d04004d5080d0180c100e03881c40f44001c2e0000d03040b40111604650707102c0d219038002142e04403000300f05040e03d92410000820b40010004098401e0b4807081c0b8440c0300c5006080d050310700b640040c0080c400d03051480b102030400d0100a20900a1144c00030580140800c00c03480180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 242633399 1250 242632149 242632151
    0x3111504080a120b01020d0c02011b030905150715021b06011403152a0c01060e0105010905030c1e2209110306010f12111306090b0109060c1712040501 66
    0x22a20110243c1001040d070030084010b0b0030f080c0f00c402c06a80225000e906030700c3c9424411b80852141c4012101c24080ea1034868800f010714082109042c1c0c400c88a00030390b001555004040e40200d200003819005094000701a43d081404410890840c0d80242000c03800301c4070f02d0540c940c1e44002081c00d02c002600600800d900000751035100d8a010003070312055408605200740300e810812404040490902d4440b0389003032000048040210401c4101c804c0d00411400800c0720700d45035100380c002c8507002c1c8280c41c00164038500c0400c0c0c515010036042c048002c010800300f181d0071b485d1a05844004941e104680c0b00c0c0291303030800c2d00b01c0c0070008000c81000641c000040c0380080313031500001034010600640c0c02940190014441282851000b00030741c0c10940c4050030070040b516241100501c00788040c2d82201b0b50380c0740619101010342004090b01d2090105000c4c010340000119001c0e0098820140041c40f142c1008012071140b6000c041c4100134000101c1c9403d14a041c0d01c180610152000c03a41760b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 242634649 1250 242633399 242633407
    0x140a121b090204030206030408070318080703020f1806010804060608010207080403020a1203120e0a0c0b0324031009020303040305070617010503120304021c290a020310030311150408 80
    0x600c99040005000d0032029008605140c00c45c2c0115070300e4000200018100240001c0e2001410f008075040d415610340400c103400942c1d01c401900c0c0d141c103410f200407400754040442d04061460a204040b074620380c4100e2100782c17583c40d5001110408000362040c0d4006551714000310b01d01e01c0c01e00040c54104d0064603d00da40e50700d14414862000c045a002d46004c5074000750200000b98480743c00030381c241c030a10740415151440c0c481c05042c4600785d40020318105403034100240000c2c419015612540003500c1800030580b100e104040c20102c1c003800c00d03500d50400090b40102803100e9100000660000c0c1c100d07410305450b036275824a041d60a400240200d00c01e00d22400040d0310086541d40981001c0d0045d10000e40c4481e801c210502001d44028440c5042403503080c02c0c03152207401c08051303681001750249081550f10490b030700349410018084454907000000f8040e01b00c00e00860b40620a03243c505280c4500c1c46d1030480e00080e81c050103000a00a101c140401d078441010300354044c900a901d01ca82d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 242635899 1250 242634649 242634683
    0x2041d0321060a0807030308041a070f020114070f0c06140703020c0d0306030506060103180b0408090310090b04020d05030c0d030f14040c0306050601020f0a0b07080106080c0301140a12 81
    0x400308010301042c450f000002084c00300b110081804030403a54142803400481d1198a407000300500003d500320b80011070f0004006050b0362103480d0000100c0140c008100071721b00e0100c00b5010890403141140452071180700307490600d108084110510f40605800034800f00c2c40040c4104050066a00100080e00412980b010b01424402e030030194103d42000c0158038515a41c060716080c0060115042c0f40d542c0708000105212410010726095001084022924181c6025405600b010314068040e2283c0803215440130a03c1c0310749400e441d003100c1c004840796251360800080c07402c008800c131654003040c0943d408802c000c2120300da07400300e60f840c04591070300c8080e2078404440c454001310b05c42d06224014032000c1825035401c0382c04d8030b400150200781030f0340340001070780340c4409003030040d180c0e101b400030740414001d4120980340201b81a598030fa40e1170342c0c0d855044640460654070044c054a08000400801100750a60340e20102d01410702e4502c1076444800c8031100031800815039200c5015268052 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 242637149 1250 242635899 242635957
    0xa020c19031814041802060d0c030e340807080a061b050304030c02030c0604060302130906060f08100b040603021810090e0603010906090c080f01090b0402041d03 71
    0x103450408410140190b40c684038101d0a00b0015030010350103281c0d150100d0740c1e140320621501c5c0300700d600074251035640c40c0c203562103030000c00c824100311001910341460160303890404213000155503403161070384550800c3c8560711072003502c1b0228011040500d200000844002c180309800c0100102000740c15541c0443c200002646d80304080c40c0410a0740f01008803500e5008029280c210307405142c1106200c1551011900d41580d21002c40d0703020b200414006070311681a002403154007980c01d402269150744102c014290f80e031038003404010944084010803c581305201c0d443d4445020440c02d801c0036071717400076204143c1c000e0b08440006900062100c07008020700c401200314200a0350300f00e91150001c840117003690024000c400c2c1c0c1e1010000450495a0300350004100290051304c10082e11100d0b2422403030030180c521804c1c64900800705840b4050906204111010f604070700442d4050f03542e54200001802040d134442401d081650068092440c2000606413000740403010547c2d40d400104881 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 242638399 1250 242637149 242637167
    0x105040b0a0c0512040f03200a03020f010203040203070b1c0911030d110d0507110406060f020706030c080a020906160503130819080c031e0d110c0705090a020c1903 72
    0x2070034003030200b002e0302c1a502581c820903481904040404e00c00031162400701d07101c4448c03044e8216045292001c58420720800301d903d01159100e60200e6802c2a00390350040e00b40d001c01c860107541604503131001c11544407200010902641d03170301d81048141c4469007a40c1d00310b40d46444195404030010f15450170300d04042103000100180744c00c0400031b008410614560700d48000302d00301d0410078003040101c10001d8428400a40c80c1c00107005120b02038441a00810703440f09000c03001c0041c07103400302c0010828081c0c03085102c101c80507680e000050b610000300c00043e6004880d180d810000402c2908090302071030101060203489078019558410011039402c020201581004070179421403142c403c281d007400050194016481440700c2e4032040a061841e05600500c41360709100000840c950150540f010000c0800035520700c01005045440b8001250741d0007032101e035182503801902c05101500e460003180303611843c400720240ca0700701c080c1100c4c1d003040c40c60b44074402c070074280c80f50800c200350700030001c1c0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 242639649 1250 242638399 242638421
    0xf0102030103171612020f0f0c031203010609090c0504090c09150e0108150f190f1203020d121104170f010b0d0b041a0f060a050402040501050a1404080105040b0a 71
    0x40d0600c56180144003048000510007070039501c3e01411020170714000e000c2c520360390221405980d400d881d0b4050041d201d01450f8000c031b110f80140c1e05400b0b9050300765002e49040c1c81e0107965103c00581400b0010b4006c0003581e00b220b081c440d05000c0010211120f014400106109582d1008514a0041d08040c04102d4403524014002c007540c0c06c00e01070b41d01c039244a43c003004010002442519820204071900c4003502005d41058030010101e00120300e080017441140c0b0031400085001742c1d9010841300034034600d0b000400581090b8a240344880c801c0038010824101d401c00090710740c0080b8800c880c20b50103640701d80800e8140303e50509d600c000600c140021099450700074400103449030006000c24480c0d0741e0040000103540e001c02d051002c0750094135180ca000103041c00850502c0071322540302c440215002c500c10710041c0300109480c14607000380c0b8115072341030310ba1074101109283c0984039800031b800078101c020805e01c40054103803004d020b4640528002e412541c00f908081c041003040d501e1040340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 242640899 1250 242639649 242639693
    0x6030b01120c061416060b03061806071b080c120301060c05060a2f07050a0303050108010507020c01020d0f18060c02011403011412100e06090c09100b0c0307050f0102030103 76
    0x4104c0c2074550480300c060107a40e1040e01001c0042c50100c0013880781c1000e50760140300d01001c00000b908021802d40702451800104c0b81641e44a107030031980c1d609041034640b42c44840448400010b001d500103450020b200d50183c0da00c444071100541e802e60000d9003c8400a6903205400052150600c90719030009140042804181185c0c03041000222a1000e0001c29070080d100d240400c40398002070b2800c1681c081c00b514510030060600030080d100a025100700c65203088040b40e47c0ca400040d459000e4031042e0060134a02c4c4014009603816201c04030041d00388042040c131699028460020b4074050003042e158100041803a00004090b204130320b04200d46584100014014030080ba4890001c90034101c0e810303280e9030b0380e50b0f01141c244546040c0304520b107800c1c035105842002d00410b80901c500d01c910221403003c030303c1c002081a40344003640ca403010000c198600340320b48203101c0020010121107600312031070503800395121460880e800d84111202d0b50b0100040c400c1040c0040709440c8001c50700c3da = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 242642149 1250 242640899 242640917
    0x72c13020c060402240432010e0907020f0712030306060810030602210405011a060a050405091806010803120a02070b07030906180501090b07090602060403110106030b01120c06 77
    0x8901d603520407000d080640300c0c4c1c556030800440628a07000160a0000010b152038403266144124010440541e02185551015414096003050b0051000e0354660050b514420001e100c41f0038448401c4014240c00210700612002281d120170400442005140306c4001c900f0030001230400804172003864101030100030001050040380c1855042074420350341c1043e001640c44121034200d041c0b9420b000044c810f00c1a03400b0800081c40419030161551240542121403450184c4003000307103d21461000001040051205200900704038460729404040c92800320f00c000c007885d2507145040426401102d040c2d1001600051003210f024804e030308000d0b864030035420311066540e20040214010140402c25a0752658501800300541168002001a24092410200c035003041c0b4081c08500d4410b89030980458040f03221188106420822203500b540505150780ba5554201c1d16030301d200d00803d89641d26168003101084d1508500d41c000d219000c40e40e01c15071601d00e40101840030300d500640034880008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 242643399 1250 242642149 242642167
    0x30d20072a0501081605121f050f0d0602070606091104090b010219060e070312050405030610080303012108030f0619080309040e0f03030703090c0e0c090603072c1302 73
    0x510266040301c003400903050a80040c15049070580141c8484001f800409010b00c203640c440c00416028000101000342c05854542341402803070300c500b100d184d80000041c2d14000205c1c440b580030300072a91190f10080741080e900c40e5500166200c9000c2c008203484001020401200184540a5001d2081c0003500c9a900c50400c00401582000e0014103140d8488410182ca0720082c820000595031050f441224060100c00041c1160010702450303012340708001c003246406011401c840d0449850400840c51a820100f0400350203145c142038000300b8892001800c0000d130144007071803142100342c0c04007160745400310410100e00b082003050134040d07141c0032041c084c100c130201c112800a0001c2c3e802040d0301041c040782a26003c50303060308c460107000100520094581c181c01001c603070340c0100a117611150321640355882602d41a105841100d00800591f070080c2018409140e010950b41001d00907185104c80c101c5011240210340c0f001134620280220461514240c58507000c1d0117a030045041c0300b204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 242644649 1250 242643399 242643407
    0xf0f130609080a030e21060108070b0708090111070306050a0f050112020f01030e03040b0d0c0e01171302010c08070f031d010e0f040e12070c060809030d20072a0501 72
    0x2020f0080d0400410303c2c0500380c507807501044014010a4030461355050005010900e45441080c0910305603030240740c074000340c04c80400b4180c5d02c8898000010914210300d40c001500c550440b800c1c1c0c0711542c0206480000401c2d080d207e40743c40350f00c1e20800416424100d080880807100d050300407404000c0d4075684c50000d40c03500b40c1c001310050f5003820001040046600a20315501455100110b4440002026202c5603041c1e040b0b40b00280348c686030211400c92800c010356001400705645900a00d000c000142e01410481c0015035003030040c1402001401e031a02c40344035aa1150340155980c0604e4844d10040541c4241140d0382240d0178171800170b03241200f000007032910342e5094035a845041d80b003800d038400e41d0303c80e40034407080c034008412104180c1079124085c646400000e0103036004d4400d204009045409904400c1c40761101002440c58655103141d50001080c0c1d4011050b200120030194550341d0300d00f480103005884c0603030030710942440c00c1d41d00f800300c8424801600901c07610a14040203141d0304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 242645899 1250 242644649 242644663
    0x6030209100e0a0c0915020a060c050307050708030a02072102060c090d11040e070303021e0102040308030118090b0109021806040503070e0705071703010914010b090607080f0f13060908 81
    0x41450115508190502c00c803031709400340c3c20114222031040c92864220340c00042c601c2c000e910405040c070401480b004262840e0204a032906d000c00c804010388400590320300300465002d0100e480060034045291214003800216411030080c09080300482c0340d409804000e0607612024102d01c25207400310312008109041e00010008090312480c01805415584070740210414020a1040701c0540f80e403070400075a00c1a4240305040d071920218000f03030b149030040c000c5a0170750b904206010324592803d410a00c0c2446102c0541c0c0d4100d596040c00781c006442603030700d24001d02840d400540c0360340780c02490301e00001c0c2e0303101c0040c8560410001007100d0784011030010f003210303100b203c5d0a11568880d14180c070a03220703400d0b00422006000200c0a81e9540400107141030f20b00300b04080103072a190081147c0142130a02032062001014000d88255290180041403103d214040ca103081140c0000f4600145e0002c4090142c5642d02150b01c0c3d0b17803841c0310712000000b000a840d2404044d80303030501d419120380f5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 242647149 1250 242645899 242645911
    0x105090d020327060c03091005070f020d05031204080c0f150c0702011e020d0e060c07032a090501091b0509090a1d0607020f070503030f1312050106030209100e 70
    0x20140b00d54504440c1600c40016070b04501524880ea6806510f10442d121f6001040091103820060344404046100d0000d8510940e8041c807101c0b08050071340c080207001503040c00126118803007041502c0400a00c400054001c512074a14262201000031115041228a0000e080d8541c00340821003600b442d00c46c1c6241d08000841100c41d0368581500049400c044486070000c0c5051217030810752a13807640020a015101034640e90400d14041100400003640b01d0108225541c1d070200400380085840019541d424a0f2214110b0411783c036500c074010070881c1a580304000c03450351a8010490035100b402001001601c42804d0448500ca070140a482e80c020f004809001c0c10402c400550408070b140d00110340b000c80e41c2606da01401c0c42c0c11034140d6642d002c41f10400140500b00410702d40060001d044010340c3c0c0014059810185520b02048598111190307461852041460008090503281c04c1d00c0c043c180079100100b011401c60041c48040c0e2000341000304000b0607607030108813104808400c55040700c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 242648399 1250 242647149 242647177
    0x1e03140310080a0f020915030307060e0309030f0106080c0603010303091208040909050a03032a0509060904180606060905010f1d19080601090e03070305031f06090303020105090d0203 80
    0xc1c40c0c00d080011501841e4110381c1c0d4600c92900044140b207400e410b90b80c0f01901c2150600000e684450b00307414402e0b61200c44942603170052102d2000107901d504000b54041d2030790100da04148144c030001c1d142441d2034000c505203940d40e00003441000c0e014054580d10720000d9501c607281d0b52540d64010240c41c0c49204000da80150468000704101c00d600c03c540091811030b6061008500c541000d80c0c031190082d40480c0482d1501410420700030701514000c1c40300e81c604143d4070490f0344038001903c01d6484250802e9110000700030144103030343c07244546400d00081030030310b040300030a625000085030b84542182c01801800c0c44104090b81e84103441448064240c43d200a0128510811178480080411030550051580c1152121844403c50640840b424142114105d036a07490803003080391404c648412042d0800c000210200c0c0c066402150401c010500420120624114600141582d07030090000038194840400504d80d0900505400500f520090040c2c040030490103581d070300c0f0f9008198420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 242649649 1250 242648399 242648401
    0x60906120c0d0603060c0815150f0c071413150512032701030c0509060909130b01090c0e2205070315080c0103151a03040f08070c031e031403 62
    0x507000e94015a911101c1503501072280701d0b01d07460281c0242040604080024124100107152586500c0030607019500140c12418180a4002c001440d980012402d10030f0410402c08140344003400c01600340200200104c0c40003141c2000100010b00104c0003d040a80742000c581c0440c49010300c00800c00c072001229030308440910015014194024000d440010400788250850b484128680048500e10266001c10821140c000c0c00e80703840c0600b90352a03402030000c0c06007041038213003085500d401681355801e0700203220b126070350549419401d803c80d41c42c5079100c0d10302c11503003500810b50006816084038090302588034510b28100f08044442d1480341c0039240c4010411450003544032540e9038581c040d115980e9601e901038595261142100c1c5c50001e85070011150010301d02c41e00c80b1003070360070540c0b651b0000c0d08a031010200e01e81028006403940c042d0008003c00090108004290a07071041c40e1401030039103035081c09c0ca02c06050703124501040703d41c130303001c000001e5001c4050039110780c3d02000700342c032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 242650899 1250 242649649 242649661
    0x7050d0b06010302090d0602070b010614040b040e040503040f1514030105031c032405030f030910050708091c0203060703050c07021c021512100605040e04050a060f140606090612 78
    0x101c0c00221b58060251880050b1850078004600301c418162031140c0c480d58100c0c0300306a003203040c40c03042d40b0960b015080d0501091110a204005294005004508807810507032681704044401c60541e10002d500b440559198102540054070100d11441441a5505640c5408042a04c0f2200d120070040c102c070580d6a01a2170314081e0b4008200aa0655641c400700740d00c0799589083c003c0c042c0241407080c402c100b04410500400011203846180140000f03041e0b0440b284181e615400980c000c0ba0394110500081145448103181c0740042c501110548080c812903006250920001070049030825052038104040d0b0921f500865290b2541038401c80300610748901c100146140f0789000941c00407020380b03c401c200c4811405851f02003480e00303010503640c80e04d601141c0403030001c0c41034202164060004101c410000318101e0340c4240554161141c2007540d0380c0d8801103a030484080c41c0001d580e800d1189400e4114104654400004d442d41840d00407201d00140181c00740034200100e0801000006c2c80c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 242652149 1250 242650899 242650909
    0xc05060a09030804062106120308040f05100207031107060801050f060c06091c03060501020c090a200c010b0d0b04020d080705060405030a03052d100b0c06010807050d0b0601030209 79
    0xb940c02c070030760307940740d98540300018600e12210803c3c01c001c40941031802d0441065219500440780d4001c2c3c10b520541481e0b90644841c1c2001308141d541c60307072074482000440d0b81803009880b4032161060060341c0350032511b4081c001005914400d0340b01d40c041071080c082d40750042160b9040d03510032220240c011a000000895a102d10074030b590481c05000d050200c80c14000402550b0303610000b110003d00b5860801c102e0803903640d84529401a440900c00c401e0754142003000c7c0d6004006204007080310061402055161070701d07050443d400c07000006000d00403540130701c00d0819500382254003c0717500b0030548600ca050000030701702038802c0a4480ba03600c100301c294000c80700b085038007105580540c0b80604059032240c00000800380070a050030300280440c0328284450aa4900c0b00c1e8810340307480c2d10501d07804200d240080480030449035100300404c0e007171303581009040b0082d046401420785605120f00c00d0b0500d003843d442103009070402c90705400014203001c1460f903c0882071900603203483e48000014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 242653399 1250 242652149 242652167
    0x7050c060d1e1a100503070806010c050d090e090114041b0302270703020304051b01020111040b1b06070f0518060c1507050c0a0f020f030706020303150a030c05060a 72
    0xd0041404028040002d01e94100e0100d4541c01c103864001000c208040c410a4070500380008002001000050749071401008200d401260624150115503c15500c440c82d2000b4035126801007440120104465100ca088040c0e106c21198000e200150a8040304105008041c20003802c1c07030f42d50302c6002c1d41e503000400e540300155001270003034100f0249001014503405401400200e00901400010b00d1117010f802124012030740040288804c8061451700303030b8803c01600d040e07030455496a260b090711009000c041c2001d4003d0840c1caa82d07036600f18400081038603546a182403031381c01c203a0400c60201c0d004142e0341d0000300c031410401d03078880e01c01c240c100c80c221b08080c580e40e02650110b03401d8801100010160030940c1d4a45600320141c03240101070b06c0b03a01500002d00c0741907100312100c40c00076445030951803000b44003401c80380c01a40c51000180c1040803503004000181e20120811140710303400307900d841d0700c0401075418014203803d588400a0841650003924011080058030a0145214041030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 242654649 1250 242653399 242653421
    0x706201c0903030e0607020f0607020f030304090c030e160303050d02090603330f0607080c010216020312040509070807050d110a030c051c0b120601030302070302120307050c060d 78
    0x14540e110180c8001510000c038601080d8001454021a11918103181c2d08403060b0a0b0000c0c500b08140c00c0721800c01c0010781c085082242c1085200f00b20402c07646040020b000a009400d01c045401c8660f0b03080142201c9980b5844403240d40000001001003505541401c00c0d6034041c03034103e5551040390051030203845681c0880b40c010b032000080000c103c41403820381c101001c040780c81c01c00421801401203418100c052541c1e40c03000d400d042c491124035008000740050751141d458107082c40c078566003013403ca03001060207a0050803955040c204600d010b10071b6914883c43c06e5003031030409081c03201140420800514a030709008041c0c0c04074401ca8001c00035681400001da405110b0484d1401c02d034041d80e005681102d000c2410b054060b00d450703000f0720903541c01003050b00120244814480f00d01010305025034501d5004264400040e10032403052080c180a1402600204000c0c0e1840c418000c0c070058280c50f400e1560024803203d000580081698580614104c4e2071540760350721000c00300010201e03e159 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 242655899 1250 242654649 242654683
    0x50c0601030f23060106050c0a0609080915040612020307030908030a060e0a060b070f0201030917030114040b0d06091509050c0306010906051804030c17070b0603070620 74
    0x708004405810203403040c801c100740400e4040c80c0000610400c0d003004000000c0e00300c400140b0100e0b210710017810031101c41d44202d41030311000d500c806013180d10410095a03c01c4000400c803800d8188211f040305030110508240340b41501d080b030010b11030003480450781903494000010602d114441c0d04203c9240f07802800b035075a6400c20101a00007404644204011002190005082c503002489601c007100e04461f0707000e10700b030303c01e07540c011640043e010202e05041d61007008001090241186100c000c0c190ad0501e070752541084502d071449041500098442d80c10904450807549603620080e103ea03600000104181c83c1a18000c06001340f082d5107110203900c0c11031075038284003001440101815054080d1191a40c03600481001d6524030b0142c15041000001c0320103540000b03584486c0d01138060f00e408c40b002d990390703a918150792101d509040110705011801405004008d00d1407500004224010a101f034500700c030150a088400c0c56085101140780f5022070604c03000c0c00785880c0031040c552 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 242657149 1250 242655899 242655901
    0x1e0603100e010c110609030f1e13060212041a031003060f1401120206070308070e060f030a0c110613030c150501080d02071d090a050f0c1201091a07050c06 68
    0xc107900812100d400f0400180c0401d030a14000c03130000c01d107a4012562072018501e01f101c1c04180c8503081c0c1c4503007001e0500705002240e802034203124030041c044001004080f44442031510310000d151113009080c001003507004010801055100060300301d00400d0140e641c503160780d10110010022a09039101511990401083c81c6c80403566a020807503424008284a103141d807140304007461001c524034000d4001000300155008603020b02081540020a4038142247c8803140700490029082440030841c00c21000c001c3c80038558140c059401808036500d086589a07070300b41400703951a0005001b01030b40b001c011001c103052512a2a04941458000d001d030b03034580702c46948400c002c1501340300d140114000e1229902080744085465070890304005008400e4016004081d54500300c081d04100c8188190000c0301e000410500041d50148806800381580710421018400243c0041110f094982d140000400c006159a01b003a00907045205c001e4400b03a80d020b0040e0b903a44103800e50454213100c1c40d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 242658399 1250 242657149 242657171
    0x309130f0b0a06051b0f060403030b0a080a1b06110d1101060e0f0f06120c1e0904030f08090d14030402010c051e0c0d0b1f17030c010608061e060310 65
    0x240c010117642003c3c00e099100050060860358803254454010303075035a040003010401091083c0c01615070002b00602c442405903584000526102401c0011100c252070303141c0d0620f0302c0b100e03150200300804040c00c0c0303040389190100a503500c50785208204000e0002c58144594415000d43c01308001e4505440720381d07000e0816074400100104102c4900352144e005500040c11810484480038444000d64018201d4441c3c1030704029035040d100000344811610301d5481b000c50b40d10f62601a000b68001c0d2120781c1d202e10109401807404000600b2009294414801c48100070703030140c4051001c904070411162a6151031004070341d2812412b1000e00b442c070507e881c00c01000381c0c0311404a903d6095800702d403140c010009c24442c010300e040c02c001e400c0008482c002075810300342408030941c2d03000c880784c0070400ca40c0b140071140a020540e41c00340001d500100305841d400303000744502c2d0080c0c26071000a0010780340485191048240080361521316504960115005071410841c0c4614460801000c0c40120307445 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 242659649 1250 242658399 242658407
    0xb030703050a060b030706081306140c0702010207050f180c0c0f030a0f080c0f1b030d14010801020403050712080c0d0302030f100503030d0b03030904140403110309130f0b0a06 77
    0x415801e450413441c01034210302c9071400090810446800d40c48111080e030b00c1000999640b10b100700113695071529001c5142c1c52106590f0664414485844070a80725000d60000a140c402240c1025010780c01961a00013640d50700d244800400140f00a240c90a95404954007014000c100c240c0e10345200e050b04040040c2c00201c041c06812841c0d54030101a950705200c00c13119110280c3d08400c0070b84082060002c500301400c0240603a5204101c89041d1403241900140703182e20040c1890800c950302d03240607181c80c90172400b20340140500d000039800d05003180c882c0c0e5100d0390b0310b100d0118585001440582081125020760301e02905520507900340c81c8007144050040d6004031800442040c40e00c000407401000c1c4808042624805070007107080c00f030f501503600c00900350380f5421507140c032043c86600c6403a0f45034041e607026010082440e07102424549400303401049655001156070300248a1181e6640781d411000781c201e51400004101c2106504401d4020209007400303980205402201140e0a500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 242660899 1250 242659649 242659663
    0x30201060b041d130c05010804051e0105190902060a11100203040803010905090a032102120405031801110a030503060d06050702062a0304020d02030115061701060906050703120b03070305 82
    0x2803c0b0507980d050b0340b400d000603200d54542c41d005100c40c030002824405544549912540144110116401a80c107084018112401c0600c0c42016030345600400030140d80023444c8694078400400309200c1082075600084441c02080d02e810104800c40c0308a440078207040014004445201d5070465480c100790038400d016500c24010b0a040c0d030304060215200d5140054010b900681581d10898011902e602c01d641d4992000440c1c40b141d40c080c8410a0540b944e00140c0340503601c14001583c2d1000211000442c014080b41d010b8103000e000000710003010b07800f0520b404103aa0502c0d246560f9601ea60002d0b804034000b07200035001500c0d1404006255800064082c012004c1c038804200d6000e44e400d103600282140000007802803c10b03c0424018200560101c1c0f2840c801000440c01c010000500c16080045034080400182030050000c0c03079980ca0100e49024081070b26282c1801da00300140039105e07200e8400e00404209144814452841007903000c4004014000c0564240740c0e070383c0c2026940c1d010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 242662149 1250 242660899 242660939
    0xb0403020d050408100e0f030f0403020a050604051804020303070c0303032a091202060d0c1d0a05010c022707020d0809070602070501120f0504030801090506031b0607030201060b04 79
    0x400c40001c00429401142901c04840c0c20900414070342c1603107440070026000f0040410924802e000e4182c01080040c8090a60b070000301c62200d03140d03031942c0104020242694440340c0668010441400301e07480c1c503000641500c00307480b000d961549480c404645540308103240a0042c900c001c0b030120030598140c00408500701c0b14a10b490014a000302190002030110071000c0219a2100c4e081140b03500562800750040d0000303001d00d0410f40c060034088241c0710101c44000000c1e1058081080d42c2065001e4501d4031503003604d80300c8480d42030800107484403200c3c51019104a618995000700b003ca004010158100c0441d100d040074208000041d6039000070306201000b24a80340300050070034800044850440382154010600a031030000191100e252000c4202901500d4040d4500604850300880c2d0169101c0d03130b00c025042d0b01d88400385049a20240490348070f50844908400d50b8440069200c0c00403204446456179a903480c90103900404d40d542c08080f00410201e000101c54082e40c81d0354882c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 242663399 1250 242662149 242662153
    0x412030912121d09070e120706211505040b06390a02030d05030405070305060f0a0b030a03080f0907030213020a08100b070f14010213090606021504020405070309020d0b040302 77
    0x41d070740a640703020846400ba8800e401104500029491700c0c46070b022038001200c050404c20401c0c803a110081e040000ca0b41021010501c42c810032010030038515020056400041410030500c1b02c140040c54401d0101d10401d4840c9842d4030b06502d41e82e0b104400c885038103900d4950f8006a5544000507004280d2018811203111030114464911810104226001c030354014090800d00d00c40c083c0c20b17203203600050020f40b40340c81038490120020380104400c50081d01d414138255054034140c01c6400669082c42080381c000c2d0008841000040c0c0c00c40d80d01d82d008039045024017209d40d0340c03c2c00f0625143c85a440a503111201c020440d4459149030300a2104041e42d03507a0b41215035402d5a42e1041181750302c07072035644020410400f4046005200409001c510643c106068640d90000c62130a81e0442c0010848090100001708a10303031961180c00700400603400035050112040d900185020001403019004030b84801c000351056100381c0c0140b0966074018a900c10035111420044000b42c000c0301c00324058 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 242664649 1250 242663399 242663417
    0xc01020c15130f0b040f0f0609170f1b0f0706080a14010303300e0d021c0509040e0a05010203010b19020a02060315010e03060106020109150b0303041203091212 70
    0x1050000d10b90000742c5070404411000044550360b002204031000b0070540d1440344564540d070000c2c1e022004990580d014a40102d00880c1c1800c2140040c0441e0f140801045030403c92640461000b0b400c2e520b001912080a2410004c80003400d07061603000e0380908242c0c010801d0108aa68011620500803000800b0801c0782c071007048035940825000f80009000304210085001ca804820038400149041c6441e1004c0903a20000d69403095071000c08456480e5000705118a00555042144154108480c0b00c81005121403a0000e415442100700c010f0080b61107842e134110000040050302601d0380e000c0000c555a41c2c0d5000f590540e500300020740c0007001c07815803552005620000f510700225400402c0d551541d220b01c861b50303842d4850346039054140140c82055805594052181034001c0c9141d4001003a20100e41c0361180c2c0c050a41c0c90040c0360035182984080e50350b28000103803401d0b2032444046440c220703064101540d07500c80310391040d8001910740803c0c00800404405c0c500040e00d25450380451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 242665899 1250 242664649 242664661
    0x120f0d06080a0809090c1c09140a020f1201060308031501020d03020f030a0b040e101d011515110307060b010306090203190507030204081c0f080f0c0901050c01020c15 73
    0x4407642c0c0d4801614003a400d1040c0e0f16036150028681d1380040c40011010300c2c11070300b070780c100c00303030002c804d0400c14096611100c1d602031154034024018070b6507066000d00300740d14682d400036406a01e05034890340107855038114800040c1c0250711070b10203160009540d54036440d100036018200100301c1003590040c01a02010507403a4064001d44d4010350b09d00b07070f4103030031507951042d00401442c501d125268403540320042c03c0b190401c03c0c00041c8048001344004038107213884421500440d408070145200c643e00d444249806100d541e540030082d100340010f0b41c10b00303a003243d4040720199008810180036000001c0c0c41800c1140541c07046580103002e8074140819551000d2110403400200d034141d00d8034400d400d0101d0011040d6000d00c1c1e00400c542001070603c1c0e101c044180c81c021039a8601000d00c0e4903a0000c0480300d4002a01204007e66031401d1565440c0500b00382d101130341d02500b0303510304400102e10f81541e81c0c02001a02c40c00410031000f15158892507003180e035143c0f2500c0c140c01019404e0404038203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 242667149 1250 242665899 242665903
    0x3010f03110d110d0320010501170304030506011205070305061503010507080c191209150e0607020316030212030c120702010b0f0112090204060f0f120c090e120f0d0608 74
    0x3c0d00a001011902212404e200c420f09101c0401c40800803c02c01c90115566443e00420442400000002d1550304200800c00e2240c10524154074551060000f000050000103005064403204450707000c510305d0914100f49031540a82000f0301c80d01440c4c0421486010041820128510440c0240032903156500f095400d84800d6911003011182000569205d01d68410340e90012456403818410700400759010703a045a40f0600c0c111030308000485130001340349650013045180d03502007019103c3d6042560b0080e40c2ca00c552104041c0041c0300349072040501d4000e01c0008801e040400d6016035910b0146120750550b444003880c1c4141c4001000410708a13032051184500b081c4015018880e00c445960040d19504003c03000085015254545000141c07240d000380c41c010140c0c0c07007654076903500b04038882030049800c0d004065100e442d949204086490316600c0c100f11039100030f00080c0b8040e40461142048540c440448800c6000146030620181500003000180450502004800c0c1c407600110307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 242668399 1250 242667149 242667169
    0xe0108030c161d1b0a0507050106081b0108090c0d0303051915170f1c0807050304080403060f0f090b0106090501020705150c1e01021903090507060503091203010f0311 73
    0x1012014204102c122040c54003c0c41d810242090040810b015031069a0303000d54010000800000c2c0045041e40800000740a440003a100c580054100b2105550b105a045142141200d04010f0982c020032100716051004001c4418007424403e8100e03da41000b4000c0c0805480b080c070205c4824214509c03110152149419200082104094651504000c5000d041c420300942c080c9000d100c2c0300135403d010400c541030440e038602140325580c03184000054a000402440c010038408100100301c00180b101d41100c0a90760b1085001501040ca054400c0c02490b1018825010381c1c41d1504610030301600f582d03114100d520704c0d81c03000c0266494400483e00e8129a115958001e00f252900345c1c0304141d01e101600f807103910102190012840d85410002981421402c103800e47d41c00560a009000e1481100c2d44403507880c1418840c594240d0340e5107aa480c4980302d03d0342086808000300722541d03401d003d03502d10047c54196054595840c1c1401041284840c40100e0301c030341c0b40755000714407810000d01c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 242669649 1250 242668399 242668409
    0x5040b010506070c060e04060f0e04051509030301120c0503160801150803120702121306181503050726060901170703030c0c0515090a0501140a14040e0108030c16 71
    0x4044d1501d0144240c8401c2e00e41095941e20903100c02001c03946009280b81c8100a02208500007114205400d180307041000280142d20365030b82000803c50740c00e60000c1246d04450101e0a00224103080d0b0408488001154000940c5402075a554036401065410010203540d10a4020000802c0c2c40c180f4280b001c400f881100c2c1a604280301814012608001c0940d02c03150a005075440381454100a5100390f01024151065020600b000e0113403507807041c140d200140d510411b1601d00c44c00c1c01c030f0b0b000604080580700000c0544030f100140d045072003035040d41310740d014455144c03245e00c4038650a03003800d0b20100e40090083c3c0181c000080c840c403440c0402100780c1040c20103050140d003152000c03941a01050800d442c0d0740200d8100103496118501400a00e00320500700503150748901d803c005440506900c030714100b2503070059034032a209019045610104444c20004208450319114400c0c50140344d2103541100c403600000501090040020210980c200b02940c004103c07003005404ca0018034020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 242670899 1250 242669649 242669663
    0x90a0807050a09020f070c03140606010305040c12050c0907050c0f0c1f0212030f0a0b010c0503043b0412030501080601050d08090306011403121c022101030605040b01050607 76
    0x2000110421340c02020580000340301945000c1d0641c5640c00e905403a54030844110915544201c500641440041e4114109280c11310842c1402d0b01e5843c0c8259103406601204554200c41d0400c0040c00c10480601da003000e01442441e1505150240030b40e00404084443c81c0213502c44083e0008000c14541354001c002019142c00b5524030200f01010754030440c0100a500c2485840f891a03070300200990b00c6107101c0c100074002c9207080013070b41e401d6914400700c03075040c001e200d1007080c0003480c0402510140c451000782e2404101030311032150107155541d4441484496a00c04114119480240d60b0b403085010f1420045040c4040c50110200c0d00b091044482d2604104c00500ca2490482040d10301d80d40581d01c22802c0c1106c0400080c103103002039110381204094103020079041c0c1000c2c025040c204541c812002d0405c101500bc03980300544c4210310380702040c0d0005c0d452000e21301048445c0c050f00c44501c4650825a140d1810100030002560161020390086000098501c0c084085917601540400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 242672149 1250 242670899 242670919
    0x3020c030a111204090938090a0b010801021210180c030914010b0111010c0509040c09080a030504080c040c0c06050c1605100c030b01230f040b090a080705 68
    0x541182c2180001e0081c2d0307464050301c803032070b109510502c0150000e4002d2030400600d090b001c0c5000380d8560030840da101813040c0c3c004001422590542c4403840c1b660b2441042840f0751f99440c981900b81443d48100925241202d0008185900305501038111a52001e80a046a4aa41d6040c0c1c00c1c0d01481c3c800c0c550150100c000800181505400203010340b401420f0210f4842c0c1140c1c0d641c8004041041c091041da90340d9506607102d507a0100307040c04102120b9008010505d41640001c0041c4a0040b035640101d45440426280c1441851000300400003402510041c0c1c0103480c008016070f0052150410741e1140605200c07243c40d05104028450081d0344901144a00c1c0f83d40f10005000d00424500810105021075040c1a02c01c1c074141440e41e10541c0a070198958030110b0f082120783c0040300404041c948448100b1503600130424215600c1808588040c20904550402c917500c00d544803032046e00c0c4d0200e800218508000702800140004540c044510b41c0c40e440c08650319001741c440c3e241e1004c4242 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 242673399 1250 242672149 242672167
    0x230303040b10360207081215061b0c03030c07030c08060f180708160e0f090718020d1b0e030d1e050906031302130903020a140a050a031e03020c03 64
    0x85043c507810310b03d0081800b065458600b1a400300e80201100762510000000c400c6441082540b403a41d204141010301da0604070f11401086840c002c2c825140c00700c013266560708446107010004403100140080840f941c2c2c0d500031078601e4850b141c03480101d840340020000031402d040d010401c5442022417022200d0940d90355600c50704118030080d4404203d02800c1404210384034240100b2035908038490182ea0030318580360411046c0c4000a0010440410340c0c0c0030b0005814010400703e00300c940c0c200c03000364070452055201000b80300e0401295051403400000e07258003e4092100ea166a800b5102d8510705c84d015030615803281c40702c80000c0e00041014040e10031034941c1903290b86240860b4945107040000101c007140995006075a246110510503a003003007185002107582030784410340c2c40184024034980c0d801a641342ca01d00001016000c098542c0c40e0441030030000c00744516005012941c003000c2d50300740544032400d40c1000c2c20215041d07441c590102030180c0221001c00b200d08004601e846490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 242674649 1250 242673399 242673449
    0x1090209030a12170f01080c0301051303030c1202030a15140a05011d0909061006050708430201020c0103020a0207051c05060109050702070e06010509010c230303040b10 74
    0x4030100c1041c0158401380c0700485050103402c40c805c039007480e4000c4840d41044480c40c500b41e01b01d64040c2c8203038100001c0203c80329404000d004599418100811a2000d04c8401c0e2210008040c0c581403080c40401042414201d0307030014208410a002c6900c3c94540700c00c800302c0711500451035140c110f10542010401d079407243c0e0100e0084a00c05511003440d0000d800003038048041600c80490560140302482002580015000c005201c0c1d070800c540740c92450f0365103140d01c3c09078107a5100301d03d8201680d84603103a0880e80e0f01500d4201802c0b600750211220a5a400302000003000340d00600c030b81810b072034281d4000e1007110b0300718880d500142107a41c0340408001c03c611803c489071101c1c0060040d1440002c030200031441c0070b4041c06901280343e141100303000386440c01a0b800401c07048560300500009903045002c81c0c408031001c1c40c00c0201e4900c107050029001200188280403141003c498030812030010014600491007101c1c0d4841c507894103001c0030480d06d07403401580e400410700400303175040e0303500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 242675899 1250 242674649 242674673
    0x30d0902180424230108010c090f0627030303090512031902090f03010c02060106021603030e1c17040f0e010602190c030f0309080105090d020c190e0103140601090209030a 75
    0xc1e400301e6040d001c4110702103c13030560130b041d00542c4010001030162000030700416040110310315010a2191404207654254187c1e4402c0780309102140700072000000c10340140c00d0300c6500514202d80e60340c1d070b41d1030014000c0000010a48281c0121000111780841c500e0490340501e14071003440c408851720310204c000030340c400f0101075401042c0c10044034041d2070071700920401c1400d40d0064541903240400180c01c01d100d070503440107a071003041c2c130520009420508050345544240c91100300505007070103200c1c2d44040d104016056a40c55504a0006200304c401441034620348140c40400a40c2e071001360040d11001c0c0a41405a000000c181d002192000074803034900b40107c442c000c14a96984420f0304030b020000c415400246000f406000e43c0340309005541c0c10500c900010112030058400c02501da00c40364955600c1800d5100300300c2e20b14003141e01c00001810102e220240321396907a142500058000b2104c4840c940200400000c0c49038080c400d035140144054058003620850795564982148 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 242677149 1250 242675899 242675963
    0x90c0f022a0a030b0f010603090302210918070e060702060d0209011202030109020301060305130b0f06040906022701020f070b0904020c0105130c09110715020c030d09021804 76
    0x4501e4904140341d540705a074030021401080c14403a60304000e04200fa2583d8160848024541012012000a54001080c0da941e03007204076103034200980b1200300c6240d4441d00603065409030280302380c014911a42150140920017079110a020842c05070240b001c1400361380b10103980300c0401c3c0450340c00303502c1d02c0d00100301000051401c081101080c2510780e040780c200781c01040d80c1c030341d0210040c06456054450709800c01d54001c07494424000d03130360b10548035160040c0544400760300c09010070465100d80e04008299030303001c8800e40d1503002000b1034043c4402503e00c0303d0071121a0844a0210354008609612031385034401c040d003a00c2d400c0c03070b054041942c070403003801d03070071a070f080182c4000100203200e01d47c0a480b660300160024060350404161051030780c0c00c01c0340040d140200c1e11012820340021500050f90015104045410900d03600c0003d000d800c0c034014450000240c2e10301c422802d5405240e00320310072100b1141c0344400d04002010134034102c038002e041c1428008210011585040d41c100094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 242678399 1250 242677149 242677213
    0xa11030309060a08010501090b0705060a0f0e07060206040c240302030c0d060806060f0604050102031c02091203030901110f1617041e1202090606031008030310090c0f02 74
    0x4540c05002c2582d076405402c81c440018003001c014041c3d5a41308130741ca00201501d0b5070250810655441c1e41c1c0d1a09800303080380f00030a40e0b4601c002900b021540080c21a0361150055030036507592558007a403201ca0840e02104c4a0300b40c5100801c1d80b0041c010044840d40d081c1440b4603000004120650082d800034110041d03072141805001c10001c0c09014070005454201301070450341c2026018441d00c40c3c4014845e034429401804140940e0343e001041e6200303160b504100f40b084c0344107821820300031300c5103184180d00203078103801c00314244074008011402440103070000c00c07000642a40500940c020860b03068241d040c204586801ca500780300c070040015004100fa08807480c40762808402c1588154040448003c0406d105c900c40d10707541c04654020001307844540c245040c4c0781e002900380603000700902c0c840c10001c1702161901d02280c110380081c00f070030411282c0d0303400d0032030340c1c520940084d100380d001a504254154044e18440c1c800c981041a00b03030000c0051035030301c0c040c0d0503009001000c4503401c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 242679649 1250 242678399 242678407
    0x30b07020c06030103060c030e120a0c02130c05120a090203070e0c22090e070e180f01020403051b0409021f0e1903120507080d0b22050601110a0201020a110303 70
    0xd9032508021030007175115000018607040c02a8000e010f440c150200740c50710350826003992072a41d8140b011220400b60308e01e403100c00c4e02c2c400e10020f912501c92403103250500c0e00c0e0103024079285421400420901c0e01c91101d880303036a80e41482d0281500e0240c8002505a00300d80020403c05142d400219001848150b84a092000b4900c52100801e040b610401c103684040804200c040c0c040d00c0380403001d003680000b800b1101d05020a00302e911001418880c6110039980c5036442000041c400b403500c03c0107000007036645513504d04186a07104a200101014084091640003992816100780040c89901409006108400034021140000300d51003800c03c0c44500801443c042e95003642d05400000000114241d982c11800c014805201c02c52013041882800c12003900400c007143c1c242d03618880b00c054041102c50794000440e64405c0c036050303084140c4d012010041c0f031b18035040c0c00c454450031003030303a41c0318a500c0d48290080c1c0d81c80303a1010107400360700052041c5000c2a6800d1854202c1200a8110392030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 242680899 1250 242679649 242679673
    0x540609080a0c02210c1212180a050904020102060402010309083a0c080c090316062105130b06030705100c0605060d110d06061e06030e0f07030b0702 65
    0x1940e009203611000a03280c2142c020071468440a050b04a542c0e4035654141ca1203619001da5071050100c0c4202d11034840c01d04000c000050800c5243c008003200c000301d688400343c02401d501c01e003064101c894490181003030701007024205054010b1069405900401c030a071243d40065008217039200b010f5803000001c111004038400d11990800c0801555900302031540c94500d100124103013401c0503100c3c80d40c1400b0044001c02c1d401210141c01c8095020042e0b030324407542c80002c0c68410000003401e2940e403600e50024680e50400d2017000c045c06001e4100d04c3c4546007c0b104000c8400480320720540404101c2001c3c082000d05040d10342c45113018080f40c02d450303100c0000408900350b030828100001d85413005e410400840380601d60b0070040603501020420310b0740e59018005460380072128026415490780505002590704414010300022840710a1044504050048001c02d4000c24022908000f1180d688210005d40d15419440d000042c02070b050542e910800d140d00082d01c4c0790214441c141c09100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 242682149 1250 242680899 242680913
    0x1a0a030b0f19051e090103020114070b0a0902120a05030406030f140c0c1c05030414150106091415220320120a02030607080910540609 59
    0x780340d944014022030043c500b10400c81c400e6900f26042404c42c807112002d203101d40b1880b0010f8156642400c20038400c4400c0040d4110600981c4009805128410305114080c0140da01c4082824000c2e54000c011400b8008011342d1010010002056940308120030011984039500a64080641a0780410200f0f000101d13000f031031700203a4840301515000180310f1201d070000c200d11301d901460754640320448000404040e0442c0801407010b002c503030f0507a4002050301c8042c022811201e195148961580d61124070040a1001501420968403580340d05000305103040b03100310b01e9820030a0811490240110307021504940c4560703840640307919042c00400060b10184041d1012401540b148165880caa402c10200a1440207003841903002103801601689011a807650311a1003030820304159242c2500282c586040e014540941e1441c1c55001d402da49103011850a5111207a05c03816000c44509850130910b00b01c0c1d032040181e4014603000d117051604959044090300f070186500250705810798990407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 242683399 1250 242682149 242682169
    0x6090102100e0c04061d010e06181f0b0c0606040f022a0d0c03020a02040914070303180503030306030d030504030e1201051b18240c070905011a0a030b0f 67
    0xc2c60580107100303820340c40c1c140f9124807001004640805400b001010021212004043c0120054143da10700020641e82341c101c0d49a100c04041e0703200d02c143e8900031602d60000c1ca4100c0d45010341103d003e80000701c5250340c0702640e0540030b040d0302400c525101c840821000304801120074081070b400303000080e0b001c1c54841c20900118a891240b03898410000f401d242458a050b5600092000e9440d001c0d020a81c0000e10811280d0305450004d14011036052104090108401c140b000744509000030081640c81a0001da00b42111506002c42e1501c0b00c003016200e00007102d1854141d48103800c07492501c0d103c0c0d04259080340c020709002d00392014160124060200c29221002c06039154824010500c09490302c28400481d004030081c108110755080c40c10300e0044800c964810a40749400c005da5002d4042d01e07100444040081c0ca0340e8500d64129551180198403541c0711003454800005040c401042e00d005200c0c1c0c0d0540414a80042220282c00415040a1040d0415000d0703000d00507585646500c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 242684649 1250 242683399 242683421
    0x2180105160b2409011202060d09170703031803050a0815360606220509040b040b0705030609072015011505040509060d03021002162901050609010210 66
    0x3c080341922040038031402d0300e10001c825008034a070400401c1610324401c2010603865046030700550703a542c0c1e540c502c4041c180d107820252508050b10b5068800040c040e0080406034400c2e1400d03c1035441e41d03915030308a1000c0303080242c0840c0042002c4103140307224020f0541c2c0110030001084032415400c001c04c41d5120b42c030762106041c400c074420a044481c03410941c68942940d0024094840c6801700204030b00307000d405841014444407034400039030948420798000c080c06014220417010714203424980c103640000c1e0340c1656040c5054000c07440b0180f0900c01c6074800c50000e0205900c944640c07004407542c0303000d809a600407002c0c00c0c44205070001e05005240e590320104040854650411405e841030011090079031b418000100420809500d4031410a64080404c490304140b5441c2410f050b424000041c41c200b001d50f10008042800110000162200c82d000c1ca240e2621110108903502c80c8145130700711f003a001c94915004001ca0320300321004040c2d0b04030610550307421082441c00d00b015a00030683d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 242685899 1250 242684649 242684671
    0x9041101050705120702120d0909020a0c0b0f0a050c040b25020d0515060d02030c0420030405011e050402010203030f0603030c0f060105090a0207080301152c120102180105160b 77
    0xf070502981f400c60900204500000c01500d890109224060052401d07481803004440d000b1400c480b003507000c2c62400b400e068010300c41018a00d02204a080c06400440f049004145040b0100f068804000155410794041d5140503107021010240004816821201c0410f00744c1e0400603800161501c01c0e801d00341c140300340b00520040da0f807d0840e905806000f0a90f81c02101c6129400e005681c1c002420074158006881c00900d00804078000707418400207000030809010300101b032000700141540160081a1402d001502819181201005944090b100a40107a00c00e0003c520400c14580d110313500100001c04903440c0c07841500b80c5904001f4560741c200129080140100a141810128540d001c14251300c03c524000741c1c0e0f40d4034a00c9000c18040c001514001c1c022840c10070380243c5458102010300000022540b101c64080085030000e8040d0328015810174a05012141050007903c41662003070076410460310b00c6100444094100c200b918841540b80424400451a65030340c0d14080c0070b107811 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 242687149 1250 242685899 242685907
    0x60c0f060e1606030b0f06180a0803040e0601091a0c07030210030b04110316050307020a0c0311010315030819020102130306090209010b340203151906050904110105070512 75
    0x150452040740b40e0320400c24582481700100e000d64612419110b0790108803201903c8420010702640003407480740340c06c1d421000d840e00100d0366401c00006402180c0025040d441e80c1d0b40c0b408011120142941702c5e0140b000c00441c103100c2900605406090340c814201c08440070b403941c0c3c0d0000713180100d07a203150102182e1342e40d404050504090040d0403c0c00d441950003891801d02d0a51a404401e0510514013040000f2010891846c405d00810080b40d40002150400c02c2d201d04081d4843e98036003c24502003032520440b108910542107280d412a504020110b00708408522440344641400e190001103550821560800001940291005d54003135000015540342c207205000b07102c04103030425034120f2414031010b40e026030321400c005840f051008290700f40301e4442c60386c0210301e4821032009506000d0a01091080d9485410303184c440c80b04480401000503085448900300c80380c501034907400081001c0020702160b2605082c403044001072502c21301d04541034030760506084080e0341a03441c11030001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 242688399 1250 242687149 242687173
    0xd0f201305090303040f02030f0a061a01020c13150302040501080d03111804091a0403171501020604080f130806011406030601020a020d150e0102040810020301080601060c0f060e 78
    0x5403080880d0300e44100801c164148880d6040d964000108020900d61842c2410b1086490500c14044840d80b00c01c2103c18849003468060080c0030900c500c006080c00700b20321407096620001c0c0301c66640d40082c3c080010304c0f1242407020b0282200180040381200300310fa0010040e00d0318811107000f8006170014154510200c0c0b0010213842c071002e01c0c00741c02c1c50140003404088109400c00454090111800141c4050307600d084003040d00e139025440074139040d070410403080c103030000d0f0744a40b009400405048540e603041c070075101c00d204280206005a010301c0000e0b000079407443c000c000400d076074842c0700d0414140d034035080c0340b161141d006041d481c1c01c8900100180707408201c81044944003103070442d00350300e0030000003036440a410001034850f201141c00760707041c0201c914071400580d1501d00180021001a2900c5000c1e5206105400d500d1161402a08015040c1c1c8296818bd0381d01c5405450030340d103021800ca9410100c400300b52002c0300303140050790001d40a071044290b4044450013070101c001c040c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 242689649 1250 242688399 242688409
    0x11010b030f1b0402070b0a0903020c18180607050a081015050d0b010302041d0a0f0204080c0108060301020403030203040b0a02070b0d090209090705060313030302091009032607020d0f20 81
    0x1880c1c0b80c5024500500981c0c00150080c0c840c19400a04200002440b12442c10102c1ca0543d442c40000c0c3c02000c0203c050f4803000c14441e009101d188075110a1081e001c404003000d594420131035003000000c005014003200d03030303100703510444d009490070200c0c05d046074442828440710fa281e51704040100f000010f031848004003500403441355540900742141443d28011909862070001ca41c108035502140000480d01d400c076900c5020300d034600c03400c21911582c40d59032803562980350302e040d1400f00300b010b0b0024040d45414000c0300c060f80e40c19400395050600d071402c8141a5003048c10b5080c00e600031002c02054541070350000e412079000308c402c080f540d440d160040c005848030140403030300150840c244c188040e84803801220f400000d01c501e05d50411050741801c83c02805031540070365001d990b01041c0003199074400c00d50301c01e070382c020782d8081b11110700b8070b9406008908483c124080342509109400c0540b604001000e40180100145296544a507550001203074211000b0703c030150b56800c180d5034034140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 242690899 1250 242689649 242689693
    0x31302270708090d0c24150602070909050703032f070501031b09140a120b0103052505060d02040e0f01060f0201180b0a0e030f03090d0c020f0111010b030f 68
    0x11071005849044e100300002480b01c50440405400b41c007015600640764000404110810080c8410821006650707190b041c003881e10030301c21440113104d0107e011802d203100340b2415144580c40341c0100111451940d00b510b0020368100c2d50307c006071244640008211a09144041d0b81c1003c00c040e00c50304e400c0800160488902140030700c3d4403090f90100440007504a4035000a48808010244d02881104005901e40d07540303030404d01030040c101841100f041501410701d8140c83c8620196203180864043c0c4100b14a209041e402100754070460400082c10600010440e401c80f88601628180e26094042494141600c1c85c410b0501158010000b09034014101014010306100030700c1110811244019016440700c4040d0040304500c1c082500c0f03195942c0602258613640080c3c80d1502d0000d01034203c01e800440c0c40801501a8003030440e0054483d01039503109039402440d00703040d00003150044810740c40d118804003156588010100b101d075000c00c010409003001c0c034020820007007000f10401d10b0f028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 242692149 1250 242690899 242690911
    0x301090615050d1d01060623090d080a030f0203010e07020c06040f0918020a030506041415010b160b09210a020a240501122105031302270708 62
    0x1410300286495500c82c0c101c2d0440c10010b4008122100e2515003810392072051842000c40d5841c01500042c02604201e41120490a0782d8980074400c00c1d901d00c0381070512540700f031541d200c1087ca520031f00043e01a00505503086040c9400501042080e1880b000c0f80d1081e084001083c0c1d030710341003211035641004607020b07180c1d0543d80d040c1080c2c98404450441d54850040d8002c1c0d07500c460a05600b803104a84481016030024102c801680c1d803401c055072031700001d031804c0d10f0482607048071b803101d603c0000d00b181044090001d5900c0c103a1a04100390b078175411a1203900c4010002c1000840403076500c58040340a2815940505180d150f00c8100d88400000d80d580c10a0543c824003111a66035004101e000d0003e8111250540c2b80d280c1030000a466203c80c100400543d14002c008550003042501e4510003520039120418000550515490201c945801120000c3d408200140e8541c18a241d2002814070150010013a6810074551001c0c40340c40c0303140040007c00c440100700403a07034000e4500d074000f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 242693399 1250 242692149 242692169
    0x5010b1c1e0b01051c0605011403061506070308070c1704090c020f0c010818060702031c0902030a080d0b090c0304020906011e05030705040e0403030b030601080d0801050f06071703010906 82
    0x7a00d655100414081441000d1146115050f00e01c041c10340003c01450469100c44204010340c0c440300340c034260000d002d12442c020302c29000000c1900d024100e0961404400802c06420094641d40444215000401480c01c100401400000241503941d280303921100407a1960740710f0b818200c00100b00e0718042d44090865004910000c2513150100701c00101c000d0070b1900448690321a224160084075884820202e803050071304124010703034003202924100560b0368900001c02c4c010044407007a40e2440b0300180d41508162101d00c0010b40b581d0051107074080c0d0030030102d8000d404500083c60001c0840b9420342c80c0e0b07800030801c0b01314175090f5001503110409007444803d0320801c03e4913140c1d200710154003009114000000c80e46490040060710002d00810700110520b21302480c0050140102c100150300074841d001c00400e4022021682c0521180d40e0755600328a40c4c43e1108005130000042d6006800031410420000424030b41d1885c2040d9400e90320105a0302c1d4945403101d400c44599600040d101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 242694649 1250 242693399 242693453
    0xc0204141b040b03180319020a03081b03060d0203010b0310060e0c07080a0302030604020d0603052109030d0513030503120f130b0a0c030608100f050c0313030c05010b1c 74
    0x10f1441c00c0180c9070400c030002d0714140301074141c2c114246580305900b074800c0c441c1d651000802c42d00da40020b0710071a10384a980c4040d000d440701907200f405141d1300d02000014070303018000150726041c0fa20000010701d000800214020601d031003c01e0810400003201c0f011700c0e445103024005410600c0e00b854001c4440501039240c5007540e00c2e02e0310035004a4081a04047d00000440c0c12562150151a01012484070801c2116520300d0028ada03280c2d581c04114107203e5003207880d061080600c00303490a6160281c0500640c424014048800342d000007500c903034038a1009404004604d0403c0034140c4143c10050119490501c045017204848004101100da800710030b5003030001030300d20200c003038000142c410081190301403e40f00350098099508480d07182d204050440e84007402c240c000310700254410008002d581c90f0f2000d4000c0910040783ca00080d18032038811900028071a41c40e02903400c1c040e500010300f1403170503000200f5840030758074451440c8008c00080000e0021030086403a80b90b00d08034080030a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 242695899 1250 242694649 242694659
    0x40e0907080111070b10030b071710080601030227013b1323010b12011802010c02040b040f0b0a090506030726030a210203060f330414240306010c0204141b04 69
    0x14450050100038000c0d04220b848244760101d81280e03e6540141c0303840701d01c656071203014204a591280340108580910503a108845d00c0102d18461108072201c09002035681d80c03030403034224a4007100e0003120525003078544003403105040b4407203001998a110000c0340040c034000401071030095003007142c0b015034035049403c00510007441504004641c2030a2511241a507400003e0051601c82c0304070384c05c01e0a28104a6204905034445409120112643d20301a501c03100d0060489000b02d4021f90941d0081006102458003c00314550300440651800451691941598115045210800042806051104000402041e81c5101000366440031425031a0850000c0c0b200c403132034034440e4055400742044024504000041a041a20a0110b08044804010b020380c03c3d910912401c00c1010000b4a240c5081c0781141c1540c07040c29141d0007a00784c8100510031100c2d19030001d0034180c184003601150100503141c81c080d10124204402c03540405260001ca00008c0c0055100604c4080038104410702c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 242697149 1250 242695899 242695903
    0x1906061d0c0901031e2c0312061e0a08030903060a1b0e1504061d010306030503030a020901020c2d0303030106090b03090a08040e0907080111070b10030b07171008 71
    0x3080c072100740380202c0d022041d51710300c02c40024402c402040782e50800c4d051030f000e0b14158100b805080e0b50004402c1a40702050311807a02c030f000e403815140e8a00700745000305d1070a00c0c203040d84000e5603120201100318400c000002800321407060b4029480d40d000803c00300d05910301400440d602824025043c03102810281100169108015188007440500c0301c0d0143c6035120040c4400e02945d40390501542d40d5140d10020380f0740b50080d10f810020b401041c45d50507032075110707000310380450f50b201c8004c40c00d42d102c2e4090a8069082405c5450442c41496940000c565410303408090f5a4400c030b4500d5110488094000200130712081d865010754000c1004100305540649048225011141081d803240c0301c0124607070401141403030241a221021a02142050180b800b450007001c034803007183c55031903450f522071b400d940b00e440c04192515010300007140031a6104015543c4065080000e0318425100e5642441c0f002090b100440040e03081000036a4082c4101141900a000401074925251a0500c425 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 242698399 1250 242697149 242697157
    0x7080f100908090a03140f0105070e1011121803030a020a02130f060603091a07081305010e030d14090111090402160609030e030106061b03030c020f030c0c0117060306040201030e1906061d0c 83
    0x82c0160324003418052002d2084800300380c000361a80a172b482106014201c03060a400030000e240b07184851000d001f50fd8030340007003210070b00c10340b0307030040c00c07042d29150200541d040315007000780040c588132200d5000c1130f0914455140649115200000d8190840c149100c4d907100100c4020740655540061003d015002480030364007207141c242a08070464285005805402c081d040c681e40751001050522041007560485541007011004c0c0c007105544000600742645c40482052002090420411200b801c060b002054101480c410710707142042d075540c1d024222000180c003038002440ba0303034401c0141c2c80d081c01481c0003410383d450111080032220310082210060f0040040a00d80d6841007241e03224024040d49807130408500a80b038486680882c61074070b44c540c0c24801800520308020011500c3c0c050510076000b50b801030010401d0390349560054008100d000c1d540109845040f641c042c0424201443e00042ca20600012405601d0009482ca10079032154000350041004000c1020101d1084261 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 242699649 1250 242698399 242698427
    0xd0605010609260c19030501050906040515011202040c0e030a030c05060105060f030c0a090b03040312050a0501120219091d0d03050603100b0105160b06010207080f100908090a03140f010507 83
    0x9202d07100e10383c1c5c0142d101c501d02ea40018455400c08081096105d0007040151041d0301400030307100f0301182d1016a800918090245419000d417501c0300f20090b0619500405012f02d046c2026980c0044900c00203103810ba8542084001170050742c1034504106007400040d0050500b40c80c0f0b00c0c142000c031700f00058a40802890b2078043c040c00703d03180045078801e1300031070001c0c200805480c2d500e0410703090050407d80359916007080d040c180800701c1c1d12842d0034841d0720304881c2d20480d01101e071505a8200a02090034031882400680c1d07440000c02c4000c00361003950140034a500c41c581400440760340c01401d01350200700450606241c9410440c0070f03100800c2c54914010112000140050301c0001a1442c0c05440d409151146441c003030881008035a078001801810f003602120480c56590814a41d140d4107042e400003150002c4085003000302d0160880803100e442000101d050201e81000300300501040e600035200d00050f40b813030040c0c900044c010f068540c0103101c002d0040346014135015044104038652 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 242700899 1250 242699649 242699659
    0x9070605070c0302060a110c0a030f080c1501080123061503040302100911030c03070b0a140702040908030103020a06090b0403020603150406030309080f0604050613020d0605010609260c 81
    0x21410030000c0990b02d00a10340c01051a500d469a03404010004054a20840c0b898410703030b26031103014541210450300712980603085010035280343d6508040c030f40221010070000c0c0b2034540d0345a4540c0c224030b680b42c060104980001117151041c00000d008800201622140d25000030a100e565102c20402d0b02c1502020f000780c540c1c03034456103022443c2208ad070741980f0343c4901d00382105d030070000812907048030407500b10220b541140403641050b8640b150341c071844a1201c1e00b002042d81c06030042d0001500c561200c4502400c0071196008242903800c40700f000c0ba1842000001842181740c09000c0d9800b50425140400e480fa007409414a124030031400040e1040d100400020101e2000b0351041e4001c10000d4070a21889a480c60041c0149055025445580c0145004400040070000d03105210b0350f0803900819964131144040e0b49041803a10040e60480e00303181800303000ca00180161402800d05a90303000d002450038006603179500601d00483c000110072454803128080002c0c40490003041218 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 242702149 1250 242700899 242700907
    0x13050408031006032703110303070804020a081f180503031e100b0412020a41010905040b010e03030a0206151507020108100f290c1504170309010c140309070605 70
    0x1c0648a641d01c0d1f6002002622001041000e801e61200004c0c0c0203034030a8889902c680c0c0c5524038281c940c49421600c00d0101f60040103412079403815000800514095406028028810384034207013545d10840f0003143c59aa1015000c0740d800800d215598801c0e0062281701d038071070030001c8184540c030072407141c03444401e40c3c98548800e40d036071000010000c09401a20200e01c4400d003283c0c40e041d0141d603612000c04002c60724040c52071004000d820980380e00c165030360b480a505040c00c0000424a881c0150f040000b020156459038a0400007001000030b42d03001401149055215001c1c60184241c15038090040e55944072000e55024040c1c40c4001c0c0e090a141215030384040d81120b0b5450a03a015030034010106000088103075110b0020514402468402c1c00c80d211401107003841d611407640042d856502490002e07088403054195160058881c0c1e58141800c0481e00e81c0d29125001070f140031038a43d66524500040301d03040031040c40c1c07810b8000d40503400d5180c120041a00e404080c4286814014005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 242703399 1250 242702149 242702153
    0xc060a0305100512010f06050609130e03160f1e08030103140a060204180f060311010f0509060304120210060b0a0f02070306060605070314090a03020f130504080310060327 75
    0xb22044000e8030b0054480e5620300301c804851406440c03540d041d400305a180400104003410b161007103610400c005820500f0b03c0f946141c100c4014a00703c9072215040c042030044511240341c1485d840c00443c090700070100c5000350b506144201841c1291030902c0c40d224000c0f07110004500100743ca04482d00b200c152020507903410324181c1040c190306401005107100140204980c450350400f41034135070700580c1c208416640d44488100322a8580000707081c80c0071301100034400313620401c2290070320403941c5080c1c5d090420340000b056080e081918201d529038954aa261100c5034100031460003c05042c505200072894203140c0180c0d4851400f003142007101448001c519a4000c100c242c0003541e21402c10080c0e1a59004000c02603000804110002880514005000070643301914881c11000b00811419482c55080180786903a091250381c201300e180c01c4c448800c001e00c0c410144920300602119540e40b501c103c180406240603001402030501c1c100800d50b544074040c1d5803c120b070f4404010711010042c0e0b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 242704649 1250 242703399 242703421
    0x30c0c031b092003281b0806061b0a0b0a1a0603070c0210110f0c040605030706121d100e0105100311060702040e070801060815070e011818090210020c060a0305 70
    0x75104000c03440c2c102c4a4000a0b00e417281d8080240808030300603030782c52040c030664211400082990030315401041407200b004407403404402c0c04c0056242408541042c01e25030b2f40d018501c50122401040540c0d15418a0341e0305500b50b4412100b01000c840c05480d514007140c001c0e182502d15003010303000e40050403c4210b428040d0100d84c1600140601b00e4440846801d5655560016a01440d000718100500060607042c00910754040e1a0642c41c1c208240c046800e1010013407400d0000c180c401c2510403c4c00d0583c8800b44074091740c5002c07146000c2202d5030040c4100b401d452010301046202c902c216801c001244c0020f8005daa242c1040b07441c02e542d07085070300005003d400d81c070203c2001401851400100c40b181503000030100c84001e000e4410142d404866184149400c031800004901000032070081c0b90303c1800702e1280c000742b101885003441e0b1140d00076000c00301c858004924182c1c0d07410009081d443c025a8140444600340700801e2014500004120385000d0000d0504c241910741c0d010402c001c0301 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 242705899 1250 242704649 242704681
    0x50105010905370e07051c021003050a020702100c020102010c0e0f1c1406010e0106030203010608010605090a030602041e09020414120c030a08030402041d19030c0c031b092003 77
    0xc156403c2c40040400d826136a1280305511405100e00c0d0344148a1740189104c1100802c4940c0082c2000301d10000c00005038080c020040200d000c02c6d500300801c1006903070300c0300d11801e1058255a4820aa60a8400a421516072000140138001120718410460b5030b600a801c40c128015107240d599551105000d0550b0a8013100081c00b03041406444c20700c0c00c8001500034121641249000c100342d030fa5413401e0b002c03440b083c0510b0300080ca4260060103010701982c02400740301c00181480740c055a503903d40c041240c02a070001da010b103684510400030b841c01800c01002400140c04114070b05440d21450000c05c4401c0e0b403165014800c01102c0070101c1c6030520072002844405800d6174800304c842c0c504060030343d0040318224400c500e04a64003c40e801c02c1d441086040464130001c00941c0c0c0702e00424030404000180440c200101c09004400040261425500541c41190004084c0d841071194000fa0b41c41d82c0c2004da2042d1401c03080c1911f1500480c596050b08610713058407035032901c40d03c5c02d0100542e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 242707149 1250 242705899 242706001
    0x60a060f05010f2a0b0f0c04090513060c030209030c06130533070b0708060a06200304080a02150c0604080d0f05090f060a090308010b130819050105010905 68
    0xa003d1139855000c20200110001c2c4911990925040341d981c2003200c2c0d0b0007182980c41800b054030078031042c84549400e40c0f14582015904412800d9811540e5859040e00c450203030f0704000a40100d160025820100854022007400301c5900c1e090002c206591499000e040c40b54030f118003014010704c41c11441d00118641e60a0300341d00c14080c10034103c04400c010b580075280c21500c130010f030400a07900300d00c03030076069020b950000c1407008450f18041044a41a140c0404c04030042c9001140e411000800c0009100070700b0003130041d0041c0740007801001010208264030f00c108000400040740700c0d42e0081281d56029903c1610307a03842c1e50100402c2001003035001425009245440140502c030400040e2281604000303d0032201c44e607480c1d040080030b962103100003c01140f80d90b401844580180303000340004241c14540c44000d9595180c10614002c20900310b945100d031201902d0302404020f0160f240540301c002c0c001c4c4001e0500903155601101c2900c040c0035101c6004101030703da03102d028510350002c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 242708399 1250 242707149 242707187
    0x30b18030d09110f06370c03120501150c020619030e0c03031c11040e0109050411030d0f080604020c1c17060d2003070b0418060b0a080a0902030d0809060a060f05010f 73
    0x241e0b030f06c0151100c0780c94403041e40070900c42d54840e0140042401031342e050b5000005942c0031405800c01c15202ca02e0302d001d00303d0303110000b8000c0301c0e80d52071412000b00001480744d03404201e00d6011016981000040e01e00c55000c1d0308108061110704142d200039000000ca903a0001400c034101c0c400a603414040c0d0380050044c03046080000880c44040e40242c1d0185000f03d8640c15011010b82c1050758410b00555054007007054043c4203542035020f0344d40290710140203800949030171901c094842c20401081d0000c03032030030440080c868840b5030015410302d207680902000075243c00c1400c0001e0005010890040c000b10311904803224220788100c4404401c80d0180407503110030748850614001d070b0070038080c1308800510b620085e400145603018150458222011091030090140b10031103104c4801081281019283c285510050300c0030024044490650350301c2035002e05000c1161818144c01a0040c05881c2c1402030030f001903200c10b44483c00b01e8509081c0303c039400794000000c0c1c609c05441080c0900e01c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 242709649 1250 242708399 242708497
    0xd020d1a2107030f0602090f0a05090c070219240207030209131a07020708010c021203070c0215070f14060402101d0312130509040804030b18030d09110f06 68
    0x105c540241c0001101102c0c41071441c5004000c1c0304203102607100d030a50144500010551010700f0308001c0c814180064501c240c802c220031095100c030066980310800403200200c1e0aa41d00c1c8010a42200725081840135221491454000406214007d0004d080b00240c1100d0343e020043c0110900e012400c05040d0002103280c4000041d4803800c040c410128a0f500f0035951496041c03020a01d0b030485c0109095031360443c0c55102c000c0720211018034040383c00c0159001c40684481038003001d0103110340715041d2003100130860f1600340180419195420540c0d801001408010380e510742c0c140d4401c00c1c0c0b1785801024081c1c0a0403420100341429201c43e010b0081d445d252008149800003000410303070036081042040c0c4c0d1003050107000c84080b500600320500501c0b05000090088014540202030855003030300b9000c095154a007550311201d14810341e075944656000402c05c40c2416442004c00071a40c2d04500b800c01804281c09100710324080f0b990605510706114020303218442c1c24800102c51880780b0f10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 242710899 1250 242709649 242709653
    0x105070f0b060f0109081b0102070e041101031d03030703110d060308311503060b030a0506030708211e0403080301031a0403050703030e120d020d1a2107030f 69
    0x51024142e030310314020824800c01c0a4254050507842c41140c900400420349880004c81d1603d0280b0600c20300d0741140101480042c10b2a0750350101070189028000e03015039568034000140031265645024812a9150461200c0c1c01d48040152540030000781404280440d220130740f41d00a100b4482d081640070720780f50011041c0319603d406450b0790000e0b400e10290010f0000d91000f11107100415594001e40000c8003880407182c0c4440d4036801c0002810302060158545110404a0b001140c0000055648404000703403807038104a140000c1030030704041c00c54000140d103607007089102c4c002050a40e4a000459400741e840aa00e50509000c0090043d0340302d035124580311809600a00c000d80f0201e025040b982c04241003625a0f500483d4542c035910b161040755903058018003a40028201e46004103501401004165001001000089c0c0c0c4010794601d503080f1203030300300d9842c074441100e1000c16204040b244d44039540072440000d500d0341500c5203114180d0105161240c5504010703d81ba081c2e085030b0003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 242712149 1250 242710899 242710913
    0xc02090a06030b0a0905121b030406120f05061e0621042001050a0c1e03090602070e01050f30010504030e0603060307090f090503040e0601140403200105070f 69
    0xc01e0b2031180d05aa003141d20381c00b41080c2a108aa00042c2a80d0004404000007510000013480c030122041d40e00d00d03c407010882900d0031030300103503c00301c081001c511180100e5100d40c8506601909551420011405d0800c0421050b9840548203c4910054503000041c1c5e40c4480c10307180801d2100c11000d5001241c0038000600d00c1040e101190401501300c3d01e001a0000c0c0701448261181c10781d86d20342014540241200c141a030894181c1e82141072880181070480300590f090b14640c080d48400c10b001d464014000d00d40030701580005010303410380f00148801c0d526000d07541e09406080300e50f940f41d02192501c48406a03013020034150346400e40030700004103242c1904060b101d10b0103a100c1c00c403000018010f105452104803032188d4103802416080c010284a68011660103040c240700054a696a03525249142d0044d0005414010b05008118181d0703802048941c034603521028280c01d0030324503074a000d400b09000008140ca102c6214450341145d2141c800d94801542000c44008106135a0421203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 242713399 1250 242712149 242712161
    0x6030c0312040f0e0106020a02060706270209160806040903181202040c0c050d0c05010b06160501050a1118040b040f0f0b0f0f010e03030405041d060603010c1704030c02090a 76
    0x1c10f01c90803620008100b0f00d414903040c12150340d03801a040c010710641c02c00a507644090011546c3d11b544500520b40c40c445100c010301c4901540e15000d00f110250300401221100040c5500010300844050b00880e0350302448454006000303540c0414024003514060b01e50030101a80070318000084c600009094402900484510340252420400f0710780d641c1007240d00140b4a003019040358064258001d10a2007031581c031071070a0041c3c0000030107800d1000020145c2d84008081d0350a0610224500c0a0103030a04c5020b0300241f115008006044a442285000c0c0c001c00022a00510200c40794418070f48858000542c40d02d00240f003000702c038040301c00c5500200400e0b00c00192003031511f69211070905104403d25522a030061442034a010504011114000120601d0b60035000c14000007a19890b0b40c05040c01c0a09082340f01300c200d942c0590395620384440141903034400d0381003421070f403a29600203684524808a031010f210b507595442c20241e81c41c48061400941000c910030030800104c3c12035100d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 242714649 1250 242713399 242713409
    0x70503120f0a11040302010f0e0a050301020d0b030601050d030807180f090204060e01020d051804090204020a02010b1504060504090c030905370c050d031803051c0807080f06030c031204 81
    0x20800d007801d9483c030a0450243d0300000340460f40c02008002e803103000302169840d018000384191202c54030382002c03a099800c1194441c0c106601c07400e079a152442c0c1441234501429054030b1054506d0682d880080800340090114424032115499520019449032029000340150707500b017401240d40e842e041c030000d500611401e07001414925a401c410761000c2085901750445540d1700d030902640b21490228155400c481580c8190b031141c00d100180c03981e0004c0e04000075103400000e803d904940510181d5620790b5010030980804010504c41d540c0c210042c1d800f1b990020400048603602000300360000c00c03140d80b001e4030510802c030382009544104034010b080620040102c1008081c01c1c0d4600c0201000f4020041c48001304940a2215003482110040d03060300074074082c03450307003c17460680d00520381942045d11300750000010140f140c0a41065000c8007441c6181000007868210b1780101b072050b0190102e00f00d1303400d1801080199404200039002c0400c0181035804141d01440c58500c0c9500034811 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 242715899 1250 242714649 242714651
    0x705010c0807080a05070801051003090510061505041503090204060803070c140102031e0307020a0b13050607080903031602120a1701090603030210020306060d11030601030b0f0a0b070503120f0a 85
    0x14010104c1030180502030106500c03003000b980d080c80304002a51910f40100d04c2015940c2c0560400315034100110701e80c0010b040e0707000600c0340c00c01c45410007a000b600e142c501440000c000400050002c1710151059440c0c500d0001404400780c40014083c10315580203510910022801d07505020101e0602400c82c2c64030600010003140030001a81c403801fa41c10304404e60744060303150700700c0600c2c1c034401035038030240c0b0344184e401e18900359407084901001940c501e100f03280034400f81010480c08105054104010303003000d45c101d14100d90b43e943e50348401084403807650501c0b02e0701d01c131050080100e0030390f00c21000352094580c0c0031548000e04590a0085030714001e590280002400b024921609082e80e801d036001e00501207601e0300c2c40c0f0296201500e51038100608000b203204030696403240001c103402c607000d00d030741e00c0c2415800101900c0110404500c614200304000300c15135a00c001c0c950885d8078000c540c50300d44005080c0f80b8118090003c4e00181c0c10504001c01ca4103403049083d4034070030060900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 242717149 1250 242715899 242715901
    0x3050c07080d140a06081e10020a0f081003021c030903080307020d020601050d02030303160e0315070f111c021207030215180c060708070c29090303040b0a050705010c080708 76
    0x1102c4c8054038518814031100d42c120005580090500383d10a602102031402150400b10034031070100100e031702881590001568260140529541c0600d41d940c019000681e9119404d003940c00140b050040e0901d121981c62450481104060103100d1440046402810b0207403640340841010b900c0342d4484802c00014050400040b4861401d8170190500c1500170b00194215603070310754800031316129110711f8001d20211508204859404010741e58000d80350341b203031043e039040105026040102a0501c10240702051820040008001485d4807156040030f042004e2041d103400241c1c200610600a88040b10002030740c00c00345500000c043d11703807a61150b03131240c65075151050f001815003a02410f0340c179900660307a1640c0d1031a01402070450f142c043c0343c0c04c502e400c001c3c0d079544c83d000010717900085184901d42103c0c00d07000358214040b203058428991003403401c1a03d070300182e201d20881c042c0c400100c90100d60700640038414415581e280e540b042c020460b140c8245001750003004112024400240c20300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 242718399 1250 242717149 242717161
    0x6050a0806040b0402101107030c06030e0a030f0806010c0204060b03010e010e090a0308041505090c040c03020a051e090901090506041505010c020f01032003010510030501080a0303050c07080d14 85
    0x307000742c46907812402096164682d6403c101003200c1046002080001103207549205140a2001d00c005521940d400300303a151510b48041c0c00c5d240500d000c52080e400c40d41c0c501c0c001c2038024012441041e900c3c50021000c1e600c1400590f94000b00f400003940080c0b0b090404241c0b00d4091008605a800c1c1d0300c3c1105551fa65042081d90004084039015015002004041c000901611400c0c0c0c00900c50031050840e8101d4098035030840700c007140c180e22290311004023848581000e04c119040c02d40d0510f010351414032801c401420a2264180030304003500541d0402c07a900e282582947c0c1e21074001001a606544d607100020003825007555190320851801203040320703d1007078180980450781c060b103821000081c0c6800300903603900d840c01403074103054640919001c08985464007007c699004010140c50354140001d00c940b240e0714420800626150100500200c0000108140c20350740c10300d80070443d90703520b80f508010f6006071b80000300f2014021038006061607084d00111542200c1a1015038196110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 242719649 1250 242718399 242718403
    0xe031c0e1f0e01110a02060a0b0306010803070b06310b061303030c03140c1b04050106020723031f0513210507122106050a0909050f010f06050a08 64
    0x142905800c020070a280300368041e1264102407652003400300001132201000041403c3c2d80d0115400400517048032003003080301d0038280f1038600340c503c0980c01440c10750306021a0a0ba64420351001130520344980d00056030a64890182d500d15500c4c2c803905e0300038208035050100080f5501a0042c42071030a00c0c40c45951820100150f0303e92010950040d860507146460503030741c0406112042d03041181e034805514005d41d60000804010b15060000d00030907401411f003881c85075641c0741141c4101c0c1803200401441d9030000b8150103403451050161040d141680d86c05440200d20014190540127401c003440000e00507016198104410b80c10034480740d55810180b6904c400b25010081900e01c0032610007011003061200405c100302d0a04106103403180035203401d0610120703880014000381e0654182c2404442c40b408000c08041c10a03014022142800000b8840b000ca5005601c191a50b55004030b040c4071040240310f602c5070a0400070440004101c0040010700b01d10f0103001e000340c400843c000703410307100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 242720899 1250 242719649 242719663
    0x7030b070327030e0901241b03031107060507020c01030c0e010c1506090504050303152d01210501050a05030d1215030b010e0603100b1f030e031c0e 65
    0x801103600e2075514074200d40c82c280b54844441603040001d091407258494581e686101d0181c100383c00300f017401d042130001c0700042c0c00220b007401d002c025903113031480801e0075854130081c181545810041101c1d0742d00314660025019061010b460385081c90144842c0c00d4000c91540500f07403081c1c1c0c081c44840304800c4141c4000100d20707902800108400900d40c00300f10034a8940c00c1640b0f0000300810440da46080035010703a05c080e10160b03801d40000092203601d5070329601d02040c03a80c0c19222042c0f1010301c19290031000b4500c03205482140851120f095a82c0c5c0701d4284100d203c032046002d107000d00c95100340d000090409000300c2d0302949544402140304d140001d6051140d07400c40d80c80440c14181a13141201510415140d618022610103000c00020041c00301e050103880c8054000000703150980c101403421140000340640c03030386407200103826501d41c0c0c0070b418542c942c000310280203ca10003104900901008821141c980004200c101d10101481c8141c0b642d803030b265805000c2c00781d1541c0c03050b481da11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 242722149 1250 242720899 242720921
    0xd080c010b010c1511090411030a0513050604080309010902120a0b0a060f050d02040902031c12150506030709050a0611060906060102190813090902040c0e100e03120a0207030b0703 79
    0x10220044080450b00100c8540d05c808641d94209a8140042070640300e004000c900580404010014040010b00c62107611030030702019485550100d4a4054031000050409400c1e40c1c00000060015642500404005580078100340c80290728401e2450b11441c080c001118403044020125440926a004136070680b00811400520f003807816040118505a10780e0882e04641c6980940d4003513030b4107204810240e80340704d030365003c2c5220703d00c40204000c081c00200da00140c070304002c10f55080c042080301425144190b85407550791f2140d103426910003a050f03000d241c1c00403001c9404030300300e54801025030107810900704865903500e480030740546940041700e28030b005070300c4140c0c580351020b1180242d101d000d00035200585007040c0d124904600e0909034020001c555215000d10f400c50800b4072071503c03500040c1c507144951042d504c00188607622001c05440c100100401c8030071190703500740140000c102d9200c0c255075445172038860181d00d4055500c01558420300b50350000b02528028050300f0141c0c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 242723399 1250 242722149 242722163
    0x1116050c01021b010f0912080301051003090314160506090d0f05040e0615191d010215010e09030904091a010f0e0109021b0f01150b0906091e0d080c010b010c 69
    0x8883c0119010702100c85140100101048002a521120403554101d2801000801c0d41d942c103100601c010f1130ba5140c070f4201050b01d401c0d0800042035100600401c2401882c0310540d4030094000b804140614044000d031450080c0024001e04880011b800c2401e00190f46820420349040d03941a01d1600561141000c81d5240e4030008689107010b0682d5010300420b110f00030f040c481150f0003044543c0d448541a80400c1c0303070f1481900c2e1070b14032900740c0c46160000d100500704008600390b840410f1034107200c0c29000d0005003010900d0584188291a4031680140040064003070504103d48844d1052144d00c0c107400c92100080b80d0820442c540409070380002c05d130300e80035900c1c0180070380c0294001c00c0180180806040c0b0012035640900440c0310b00d070300301c10000c20346403a0440d5071540d0340341561020703418110030859918640c66400c07d0700c044400072140000300303040c40310700840180e20f6035440c00d0344545403018400412142d000030b046000c0d0700c2030082040806480047d076121586641c060440d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 242724649 1250 242723399 242723443
    0x3021212040204050c070506010609030302060a0507020318060d020a0c0c090603050607080a020706051905010816050f04060b0a08221104051302120109110904120c061116050c0102 79
    0xb42c14140c0006800c40c2c03414035401c1ca416002d44401c0e05000007a008000013500100d003c10a00d0350403c8240c1d0000c1c4582002c2041d400d165030007035a01d00c40c008405594443d402441030050f0794035015200441600e038010f554460306103100038460b615103141203500305a100e201195a10081c482c490039284d00c4001400151180310f400d4891440c0104910300c03042d002c0001c2c8000852502600780600248641200c000650004030700540c0c005070080401e0f03610000050070044038450401b001c840b402d031b913014140c10101e00483d026001300c0c0c100149100300058004c040561060007035100b060200d06400000b411a240c2c01c034560040d0001810703c00300ca8032502c2c0b0718505548290f0304a0541039901c0a0521a54003003610030054454000559541301100c100380074082c805107102c81000c5490310440d146c6a84c6504c03000c3c1e001000e400400c0007500c001002c101d01a13005802c842c110f4000261640800020843c0354401420100c0d01802050591301003540000f071700800382d804030040c0c8420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 242725899 1250 242724649 242724653
    0x50a0c090b031810060303120902030706051b010e0309151204020418020a090e2b051c060306020405040b03060f180307140c040b060c070315020f160302121204 70
    0x3a8001034000030483c1080400c5a260799002c0040c0079031205541c0380030030010300c0c60030098480c940000c00c0743e0219003408100ea00680d404141101030303c026050903620751866044a0347c8002e0140c88414144d0311f0082e41d120a00c10000141c481001e0480700f030341800104000101090080021540242d60103a01240043c0380641140e44803402c2c00300e001e20350210303d8000400e80350903a400b01c059543c1c0c806e401070020100f440060001e015007000c0b1008a501803811261024800481030100030011a0800c0d19550301c0d00525240d02203000144105900e07030810702c000f0341c068840e8a01c0b40d4070b00501400c407810080350703286c030450780c6207160702c00c4e42da41081005594003404501d090350f0104006810000d050b0300004208035105a0090404006410500007103c00c40001d0a20501c003e01c902d043d00c64001444900b80d961103080d02c0c51541401c0840e1019024041c0e03101045a00460011061903c2e80f01b40d40f01c89000fa030841d60500310700688aa4548101c400c040112400d4600040c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 242727149 1250 242725899 242725919
    0xf22050415051603050c09030a060908070203160603050f09060a0b01050d020a0519080402030d0e010e06070303050a060509010b043005030403031706100e0111060108010f050a0c09 79
    0x94030034040c000318014190000c0c030420442d08100c618480c200003a021880c074540d814802e00b40d0100c1c40300f02240c81c00d1110300010b40e840d95422001400c1507240c401c01d1007080041030580d480302d540903045406881c060100111050307114012000080c0c0340c000001d419044000500703006181c44c40251900ea25250444009031103070a9000707060100c208440d1045540e94030041000c0302c03260b510703152916904803414006410b0f1428003001c101c804030600c400341e54003256506404c0054140341444000c1d4100603541c0300b01d94840144d00c1b42001c2401024140c241e00200d02c0b031101d9040c01c00c07001d603c40c0c041040031002801040c400741d80074001801f8820704841410042e1540c0d19034080c8210400c2095000c40000f07d00c11185600003203010010190440740d00b180001000d01009428581403000c0703004290317410800d0081018541e01115541d016150403a10f25a841d81910a1036131071320b44160107445140051010b091600b4005105410340388071f0051054101c2e0368086006180810b205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 242728399 1250 242727149 242727151
    0x6090712020d0c030c0906030201020c03030a050405010503191a031504030210020a0905060307030902090709030f060b040f050403021e0c180702070906120c1d0c0a11030310050f2205 80
    0x443c6603040400100104094888050050100f50800f145441c01c61000a00303240e01890940d00961080c8928004e41b9001020703a01940d000307103040c1d522035480010321201081070005074690300386044054441d404440c8a050150041903040360701c56005803403014440f0701d080303c024005030001041c0501500c070540003411450036034609042c4d5540c460002409590003622460701182da43d0120701c1c11030400b072070300c681e00c21000c8c1400307500503295071503410007000e000500808c5150740310b0b29020036070740310f9021000c08501300b44100102d182030300d40a561500240c024881d10b175a040481c0c6184580080c080c000c1f010080c0c03e991030002c001d891588000b2000e00f002c425802007038800700d842d1040e44680e400420745c0b0103003d09050898100031200c500107400010345a001c98045d01d660341707807511945400008070454103a88074603075142294103002c82080c40c4007a00000052082c0f0031003000c450f8082d51012116040d02045501c10000810120140c946e54503041c4203030705080684c698001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 242729649 1250 242728399 242728403
    0x140909010e15180615030c0717071a0108061303020c041505030a0501200403050c09151215011215150302060a05130603020f040b070f0b010e040506090712020d 70
    0x90100b60503400049007103640c803040c2100d40340d02e04104a40783c9000407800740c0c49414060b40b0761035070401c82107107a220710503005c002c0d01031004401c8090350b2805a204840001d608100242e01c00ea00503441800040000c0c4913903505440f032500030a00c103007104508811429030640050100311003d50901001d48001d440c1759065288291001078035450a2110070066485400000362819440d03980900a855003200480750210a01050001880024080035291000c84013000c1568031042203061440e03c402c2c10a80002403950310b5400020000b50700304d60b050a142d43c0091507a01d40c04240100c40340108050074490310f42ca0443d00e00d884c240e01588007600c0075130301415202e03125000f040f0300f130384429041000618001403607403405422031a0803020b80390300c0c43c0562501222000580a500031406040700c8214001910000c12000003075995840c0e50107010501d0035a52143d00da05829001c603000e407118080e1600041000902140c20002c0c0d0b010300c81c40104a12442c0c0900c03d0780c011992007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 242730899 1250 242729649 242729671
    0x403170f071202010606020606181008010c050c0f0c090f0c070b0c071b0b1c02090a090c02070e040c030f1e05011e05010b1b0a0c03050d140909010e 65
    0xd8000100c034080101141d60140030300000103038146000900310340302548001e00319040303079050200540e100b0704008000301c903c43d8000955110b03440195500f401503400340015618243e40041e00c0d64205000d40040081513050b602540c00c0380780a65119440e800e40c446d0300265800016440010b803c60450b00700c0d4002c40080d09040d203650390040e1180301a40c01c40c88000740400e298041008040b10314001d800442c000d0701c501c900d00824494107024440c00600400d550341c100800ca04076650684400744401400e07480620b554680c40b1000f0302d20704080d100140240302d40403e0049100d29681e0040ea400010000041c1ca541c0310360004504240044800ca01302c0034080c1040d0b403812a40000c070f98004c1000180c10043d44113560200804002c0350030f0341c80d0501c80100b080c0c80f469002d55407440344991b404801203103c400d0560505442d2070f0020140e040e02000030052040c00100d0701c060344099142c13000303440940300c2150540d0090a10705c0764030040e04001800210301a410303e64201c90001a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 242732149 1250 242730899 242730907
    0x170c07080705070b12070f0e09280912050f040303080a0612050105090d020c010914030f06040b060f010e030d120f0c0e101e0e03100c05030a0b0102030f040317 70
    0x2d911410078507a5403220038404800700d00910003000e42909140c0113134540c14080c4002951364005080c0040f2014100d01c0740c40440e002070108480c203400c000d6045100060300f07643c20070114286009290202c402e4601074900c000440d0000c2c0a0760071079142d91b9032a6426070500b480d55a0490301d00c000144115080780d12058000740141907800420b1000f40b04800104503850002081032805000182e03203011540700c04400000c0741d0300700e45620260b0381281030380800c100b0020046840c00c0c0b2043c1c83c01e080c41c802c040410083c4822a4132a030700a150869820100062801c01151010300c0352580662540090f00650480c1c2d014910607a000195000d0100300d031404844001d00715649100c409002c00d042c3e0441803607600e13100c0200740c040784039400c000300b0100d06894244c8890320803444107024849030302440101d40e6810010b1400610b810031080c800040045d0b001003158006a0710002c81c6410040c06118540c0040151940e90750030200042c2403a1a58489054002c28142030317186a0701c00b00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 242733399 1250 242732149 242732153
    0xf17030108011a03010b0d08030604141602060112080d0c11031309110304080418020c030a0906111b040c0e090702240403050a03051f03030906020706170c070807 71
    0x185009003111000040e01c1c010b501d42d10040010510305140c440e0b45403046801c842e94580041368041e036004048a522a5581e602080c004c0c130803000b11403010800c1c50100000780c45207560800707100d8000e5003540c0150341d0b92400e00d2500c800c0d04000600c89842807007486880c50460b404140b803400315241c40c0840c0303030803902401e0555001c0e0592410240c0c10030424004d00205014883d003905004403054514078085e11000703481d020314026503030180f000441448101d92260140c914030001c0304c00350b0396124201d4401034148501807250381d0109c0c40904201015690100301c400f8500d1012010041c00603c40e010040141703109a00c1c1402d020f5003e00308031550300d409041e00c0c850046900100203110041c040360382c4030f100500103200591089010000020703401001d42d43c5d88000e41c20042129125100c0c4824401d50321a000315001614a200005041e84208240103c41e0300c0e409883c41a5100d000032a02c80300c0c031414951401c0c13407140c085650b0345400002009007600505143d401e01048c3c4d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 242734649 1250 242733399 242733443
    0x70c1e081506011b05150a0203103003140c0c13020325050409050c040906120f081305060309100c0c02030c0d1a01080106090c030603030e0f0a05031e010b09130f 71
    0x61f07640c002295804420090015142031041005c2d20740191142c200c0200030b01581c0041110b81070340200041f1041a0b0020127000d046c180140302c42551070f03642c44181c44159a42d8401141d04403034850710b1150004981c0305200d10889000c0d0010b401400b0740c0b100c0c1c00340e60300005040400c15034200602007000007460b6119100d5035001d61100d01c1400da5581c1341910350ba082d0390060301302c00980c8500c009504001112201001443c1b50701c00b00e880c2d01d6000201101803411201c1d4000740d00314600000300260110042104000c1c145038200c00c00070940e806004440900f28000c00a41582c020080c1258030715114607210310a40c4075410306507401800720f854001402d000e922420903a9190302041c000e0189a02908180c012145001c000061645c0c800615582c0745a521901a545a03030f13000983d6220200c416018003405411100391032800d00640500c504454050355040d4030f400040003080c5800c2c05194010b08002c180071850b030116882d804500d281054007191a040010080071110140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 242735899 1250 242734649 242734651
    0xf0f0204380d0e0f03040f230a0306020a0f110706080c090402040e070f051e03060a1a1c0e03070813080106030b0a0507080105010212070c1e081506011b0515 69
    0xc10000303d101c45420328440e161012941c030003ca6904284001d00000c0c03ca225588100c0301d0a038070704000d21841d10880d6440b546117202d00e940003040c901e004011b103ca00d40080044001c595a400412001128122030b038508204484456400c58442088450b111340496500114104080340c60640c503040050101c0e805644141c802050120401071665001a02400182d0a80c1000d42ca400c0000e541c24140c0c00e05a80d045407521008000301e03a01e6103a02001c280a0032204008041800d00307100700d1403080d00300c0c8801c00100e0600c1b400000301e5000c41d00a004a203907241d0001c42c185940b036940c1c00c806070000e07044003103030b09103a24001400c1c0a090144800850090390841c04a0801401072400d440005003840148010140104080c5c0d9000174100c00d08060000c3c2d00c6c0d04c030000c1d031600180005d043c1c2d00c4510301d50072410400a016441c00c1c2a1800c0311b100808841c80c012101130301184008040389c0031801310f40c84219504603c0b800203411b80c2414801e03010f0300d41041092101c50303180300c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 242737149 1250 242735899 242735917
    0x52406091c0203060a0e0604121106010303030f0f0204080304121b120b15030606010e01210b03011b0c03030207080909090609010506010c0506010302060c150a0f0f020438 75
    0x1c80380007020b508003484081c0e0000303940300d0184107242d5010007241d40e0352405440244819803510018840034459030040401c03503016019141296540e003070081c01342c40113400071807907545059a8003040f51224801c841c1143c01410203142820300d0f294011b003640c07031804400d8a015004051035100890204020070142c000e950082140220f581040b40050200510100a0580f450640e207841d0f0340009103181c1c00842440c00e00503000c40400100e80504c42c0c1c00c4454014030188420440c9041e071030b0010701d24003c2c00d074000c001048200810608240c0d007680c0d44000320308801045804039109030028018a402480520301e44200e80c4c010505103a4210ba5250751a0030034000d0040b100028040c8680000702481c1c0740c00103000a0700c0c1c1d42d449000610000344180000100405802418407010102d0381c40104007409929003e4081c4015000b0751441e0503480303151040d81c000c2088180300341d8090703800e03c403144850308103046651501c0c1c4446840303100880c00130001543e891540c00b401400100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 242738399 1250 242737149 242737189
    0xc070303030e061b070f0302011e0b031c17071808010906061728050109080304032c040c020709050a0f05010f0302060702010c060b0a1706060405240609 67
    0x390307501c072103e08100d80580b49000d45141c010894503c6030401d42a504182d8005140c00c4030326000c0e01c2d00745d0041001d46500031030a500c41c00001510354240e841400c0212042d420780d0030210030710100100c08244000075802080d80c47d0030b40c1d4138a82d40c1400095210040f42011403c00f4032414182c54480401d51142c22269150040704040240a000e54001440b4600c840c40c2c000740c003808516103417140320075074214019482601014020b2440c80b0b860f10960454000c02107020302e41040c12080d401150141c0100314141e240c0c60190720712800307106800b980c030708003031075400302c0c210400020f0816071405070114480c1d410041147d03040e0740702c2c0a005507550b9030001076450200c001031082c0c4005a01c014242c0f00e542000700302584600e0704694504d542440c0528801400c2d01d4840024401c114006400c85603072900420801d18020801c0d82c0e1595150440e04296500303010041580d004072008a01840100403403020b0b4190060740c0b03c0c0b028802080c041c2407102d03420208680000000c0802484 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 242739649 1250 242738399 242738411
    0x50c06070b240a09090606090614101106071b05120d110408060c030603031605060a0513051e010f2a0c031e09050d030c1e021e0102030c07030303 64
    0x40034400a1081d03040e19000b040c01a2400000080e022507010f108480d407068843ca03003e810008141e02050103000e80f28400c000080c0c40e540703a80b69510054284500491290349411503160080811070252207690005009560310610220b40d002e0f110105905142d0590700407000191041c0220115010b0116110340c485a1540320340c400e036a1070f01c00443c0018030811040c0000040414200ea010000c10607150703a23901c50401003072a43c031400350005543e40503030240c0c00030050301003042401151b80c2d42f0144030760740300c0c0c150101400c41c1c080801801503214110b02403825480404540030440b0300000010134200150881007903400b008085041803404040c00e0034134246445c140c02c7d0340c20a92800c095010020fa4005e04811129000302025070f0402c030303141c82d1031881070040380d0180201404083c0040c00502e409014901400f0048030308074006a00d6405510400c0004241140c000780300711507034001c84402c2c0304600300c07602c1030303a045001c00c20000061401c2048500001e51280d82c00043c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 242740899 1250 242739649 242739661
    0x5010c080403091e090504140307050706080a05010b0a0e0a080d09090c02010506010527060d090606061407020910030c0e041b0f050f040609051602010b101b050c06070b 74
    0x214030444d003110807900c8025074040c003103090394000ca10030307120301003070026003511582402c45031180c00035a04800c44c4400121a0304028010502504844076074a074150941c80c1e8181d002c0c140c840c00d0060310a00c0c002401880c0d481489100b07a403000c0040600015415070319900818180f5183d40d420801140c440942003144000c03c2c410380d00c030100d2500c0204050b06000340000c110303218070b003186504280d2a400c0004800359042c121454480020102a0382e2480000e683c0058428030a047d16003a00d821000202c0f540102c00010310800784800084c505071b8240c7c20800d0381140640944000464450044001040c0030f120b5000303400c800c90741008619047ca019078401c10300e011342d00c1446001340e0040020310b860000c95030076144100c0702000c1ca240c2c404081002080107620450310941803c00380b228001c107000300556492090b40c000d00204400d078060003085c40d5407600030070001300c10303800b518003104001138a03c0d645449101030f02d000c1004180000d01607013203518166002a144414014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 242742149 1250 242740899 242740907
    0x905070302041a091f030204090203070e040c08100506070507030804030503030f131707061806020903010614090105042a020c0f030f0604030e0a050307030602070b1b180d05010c080403 81
    0x556210000c2d0146001840c0010807810645504c524400181180d243d4107506c3c00790f016200038008a080840d00c925005c07000a006021402050380074501d080102080c0034404c030082f031701c15000340704405906031070002131102d40e510a80c429912401485008400500c0310300c01400114000d5000b15264100346d880300d048803070701620201288880d00329890000303a20402c1c0380c0582240301d80640d02c402881c05e00b2009030050542200f402c0010801540c03c01031250301804241405400030840c003501c40f0345101100310013500c1c0c43e42c0300b607103100100264035081d00144030f008a002d02e4010101d400c00755620080001e1185000540c00240a958080c100392150004e42c0500310000c282d041c40e00c0000300c1d1a07990150001d810018030710304100702a194903040000802e809411111050f6803801d00c64000c0d04203070001c540c40031001000c107030b040c440c2c2151200c0050302c0e0302a01d0f242901d1000c16502000408105c0c64002c0441c04115012070400c1c45806081e41c200e4a400c7c05a15141c60001c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 242743399 1250 242742149 242742179
    0xc010f0203060f060307020a0308070c0204050f04200105030c0702030a0c060c02090a0606050d09020316090e060709031a100506070b07020601081903110a211b0210050d06090507030204 81
    0x9001d83d0060080240ca19800110304a0882c0c1608140070381c3e8903214bc0c1154181c2d0b070300f00040d406c54108018007900101c0098094030682c05015440919070038221001000301c60480118005071050012418030190200180500707440141122292600b035603c184200000303510441c00f041203004003c040d0709040c940154400c4002a0401845042032400b4100e80038259026440c540d58909080031034500300071100c0c5000341d402c1e40c070002d035668111b11005460754420143e041d008000c0462251801413402c80240c980c03000c05c0041c0640002540000c40c0f6008042e1003c4e150501c500080c0758441302e000b410410300804d1003110f03a1801141c042d00d4000180c0c0710614540c00303d0003441d0349400c01302c8009011641841e0000301d45000c10074451030107010f150701408113407100c886281ca1804803c01000181200e49600e0210251282968100c04125001a400030880c540510400e03100d0300060811076000100090840e494140c090110f40049480d440881d900045c00c3c48992034080d4070b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 242744649 1250 242743399 242743429
    0x309030c070e150d0f03030f090b0c0c0c0d020906010f09050409080702031501030b13060b1507021002070503100f09140f01140402030715020f010c090e16021e030c010f020306 77
    0x183e1300c1c060082d80c48403421800440301a0400d81c0c0c0709601c409080c4a60000b107005070b0018400c60042c00c20342111085503000f082070700b49503c201000300c030003803d008040c00c04d000c1c1c00801990300b40d500c4400643d20307240d103514840200103030340c00042031035611481009070300360054100320385614052051501d012850b00300c9140800b542801000080d2144900550001d44e4140d1103940cc402c92810070050561400015404403c40040c1c00d6800500f00143c40c1c800c5c001c854111240440700d50607a12188035000340e075010303081f8003a450079004d01504104ca0b403d203d4031001034500d120f900c4201c02c401c0b0340404040c054010940c03200ad03064090084508141080c81c908101d414168000791f81c1e40e01d80c0c030400111407103000b149260030b4003c0c0402e085a2a00100070710900440680041a1030003038021141c181c050310b00811600040b6016640503400c1a800600c0400b0b032008a0901400c100341701900c1611040001c1004d0760401e01442c0c0f000b559203000503840741490410441c01c41181c0c008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 242745899 1250 242744649 242744659
    0x4050304050907021b040e0a0b0414010605060a0503061918050702060703020a1706030a0c15091d1b0f0406050d180b01090c0507120507020f0102060601020a080309030c070e15 77
    0xa080441602e400340c0a00d1701800311b50004800100e5030541d81002070440b006030103003100a00704418040821001d03c48601c1e40c9000f00181d85c4c54104021440c014048280005402880010450700b443c55030300410918020070f003030007141d94074001c8403c1c02c82c0140f011911a12030081c05070036501082408c1e0003007040d080643c2422400c100080001880c80340c40000350350010f0200c0da09881c107000c4246640c0d0003843d5202c1058851001b50881d0303282c0598040081c1c4140000035007901e10306950648101c0802c0c198950f6141c0403080b515446801020303c081c3e841c10031091580021032402030004287e01d49070b40d6200c1f07015001c403600322400402c6031500703000d14012180c001150040c1050544000800000d40406040c5017240c942c065250010440c1600c40710464840313410102801d042442110003180005c3c00b0001280c948070240e8030280580c2c00300c01c2d114000b6844c007028640c0111400110f9040480340d00c909454400140c2c4881014003d940a0266000718103440610031201565 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 242747149 1250 242745899 242745913
    0x30405120f09040b1f031104080706051206011803060518100c0306080606150a020109020a03030c0203101514030c03060a1409060c0a0309021f090f08010b030601050105210405030405090702 83
    0x8030a034030117120158400c0416580b5010700c0e4a1164200035100502814400c503641d0a0b21180060025403002448001c07412035580020015031081c00e5501041c0540000d000c58107245580f8600a020040c3c51416600841c1d1000c004444080100c00460780c11128049031103006000086c04803695900000d00035001403041201c991106203054000c94044213011356034007030029040740108102d4030001e40c041c10080c400070038547d0028040c0e1019000300c00b6940d49080030808801251800800303401441106c202c01c100d04d00c41d90b14441c42c075400180544004841600c0084d04103682100c0c6401d01556645000766422103442c5100d901848103402441541005001c100d920f0183c0e0440100b016100c09103082191100281860034819400c0404186041004054040b1a281c0118a102c4c2c2010b00000f91455050183c0c1c8040b0708050040c208076400c1400458042e442031707283d011586010211041c010352492340c060b03c21402003020350b8a80b810312041141940001d0181011580a10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 242748399 1250 242747149 242747179
    0x909070e041409060c130b07050601060f050c0a1203022a0c01020d05071106091807020129060a050906040b0a17060117101706100902160305030405120f09040b 70
    0x580e44c2d0403000080142c0e4403850103035034901412000e5000170f510071f14041141d400700900040c10905940b059100d101640c0350b080021655801211b04603c507551254108602080e540004680244050701e400b524160700c50040f200164a4581108010045043d0308907001f20305028010054109202500d81907029041c000c11a010308403020300284514101010650340c1d440860307840c103101500d0142c840703112801c2500c2c1140200ea440000d0b5081560700500032803c51907003101000841c2c807100c240c500f40c0090004c07070b41002030004180001000b172a6003590700d813800b600c010982c0c05403a41c3c0e62a07030f081c001000045074001c001050f6582c0800c4c0802030784c00c24584800c0d5114185608095921313060300d0100da014543c0300855880d5960f003503031007490001c03c40e40d21580980404446c0d0701e03580c800d01012031044281e10707400d40e0300d251031003000039100304010341d04107005004a844148016101040690142002c95116940082c185095050038007800300e4200c411611070140240107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 242749649 1250 242748399 242748403
    0x606080c01050d0209131404050f07060c03030506040f020c030c07060905181509100f120c060f0e1f1106070801051c1403030415110a0f02030909070e041409 69
    0x20f00d0304068000c2e004500c91001d501c644241b96091070b03c01c003050262449080c505040d1200985055845000b64540040315550004140c4211005030340e0ba02c204060f107480840003044080c1603180e00c01e403074142d161841d100d80e00140000040e42c2d005541d50f4100203680e0351410032540d00510520103406404c2105070744440030355031104015038103050a81e88205841c80103000c2e007102a03a00102440c00e1001080588680c0c0b4103495510140840882e20740001c98440c3c0c901d0326009028aa00000c2071200380c0c454030b42c42000580c24241071040c03240500000d1701c4944040802804000c403501120b4102d86c5c0b00304038443c0c04650301d002d41881e003441e1078000c0400303105005d080c2c060a19101c1880302c08041d0080d07050410f802100c90f581c01b440740340240d5140e51003624181e850a41803901140f41c06d6861180315030b480c000c40103851074490211419982e101410b060b44065010510a80019403a080410341c82102a6a903510303086580e5000c002c21603110b030314540c0000a0101c2040070f20800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 242750899 1250 242749649 242749657
    0x210506010e09060402070609110f03190f150203070302090109050607020d0b060d020303030f1806010e060f0604090c0809100c02060c070c0305070305010209040c08090a02040e070f080a0606080c0105 87
    0x1610400d0b407503a11680803402a12903800014000e52401c2840c005100080c000c8103030750803048600c40e00021301e030000c140e0355440058154250b503e003c0404c90010796403600b1403841e00d10455402440103038480300d010880e041265003002003900000c21603001d40c0e0003485200941001c80354607007804100c1c0c001c14010006100010050680b610102c5e02c2c0d9500c41c020b00840941c0241105d641c1e1034601401d006002c01554a40c60010301d401055074500c00100d201416602c0d0100d10005a130740d40070801851008a098440d0002000c120100b44c1007003c1c050ac202e001c0294442d10740c6c50900f401e0b21441c2501c2c5e0810200203901c0c0c0070100c6800c0d13a010401c1034104c80315660b00741e103410150a1540541306107600050041c495404000200310044d000303460021011a0304004841c80100c00b17885c00c00d4212142140b80c0c004950842c01498258001202a0340c0e61089074180b60300c40700441106e80858105090350791065036110200841400384c5000341c1510b9000d80070401ca0301001a0480c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 242752149 1250 242750899 242750927
    0x100305041106070b19020408030a05040816080318060d020c06150108073002040608010e0c0702010801120c030605090304050a0911030103020d2a14090c0a1b1221050601 74
    0x5d0070b40e80c020b1342c0403603901520f0140c10000c2c1078030394030040b90b2409480b950052017002294011018007d05d10110441448125142c140246192601140040000c00350058403a41c0c004814050411015820300c050301640004000a2000d4181102ca9100303000280c01c040d410800c0e1481084201507200c03e0742d1800c441c491614a4100c0107896604100b01100101d072001d1500c0030a00040050b40a041c4034100c801482d080c613125294400240103510400102034041403ca40041202c1c000403926500454040c0110040454980d40d812040c1c0b881a100d80300582d0012400707014a04d841c4039444018901402d04000c0410100700c0f2a01c0c9000502c8080d2042c150000018148000c2000d01860061018404215a86a528a00c048540a0080d8819000d041c1c40c0c43c45a41405d8a080c0d0007616542a5242041c0ba2108101c0300500c004507050120095140460002982c11491010707000365511078242501d0351054031a1007070068891007000c01c1c108400d100c06a6000305207804150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 242753399 1250 242752149 242752171
    0x11b0809010c020f040507030b0a1401020a0201081e04240b03060f040f080a03020d14100902180a080319020703110d330b030a03080a090c05100305041106070b 70
    0x7282e02d0002808100d805000d01c1e4105040004001d42c89034107500c0b45200010131234807101c505d61100381c80861450240034003405070344a100c80c1c03000340d070150004035403010221810b10005500d00c960700c20001000c1c1c07130460b21508000c40111800c09080d01030782840e07001440401408000c000003c0e45d80340081e1181c0c280c1e810660108062040c940d88403140c80b600100c41c9684c900c0d203002e00800030342c0198851081c0c2c61405580050b01c02c0c1e400003041c00752401c07012002c0d00c18141100744c0b00a40c481c54ae0b00200d1440d540b2a40e80c00d80340d51000100a00c00e01000c0d64035007040c03917503041c1d112032080084c10840d0400c640a00029000c6c3d0042031240c401a5040c00345060503141c1400ca18030741100085c070803282c02c01034000c4060b4100c000e40240f0607640c000e10000c1c011701d00707166541c1041c2c1402804034080000142014030150700220190340143c1d4202070055a074008074003510700c6480c3c0c840001e40c5a034208810b21204428900380d00106556031403828900d615030300c00410000c4c02180c1d0b50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 242754649 1250 242753399 242753417
    0x30b06010201020c07060801080606061c2a030501090f09020d08090315041101030e06100303050d020f030c0c12041d1b040b040906090c09060c0318090b011b080901 72
    0x40c0d00c01d40c103482c03221401c94111002151600c0001c2c01440e001d114150540c0304800000da05801c004003940c01950b82d0f0941d41d0590042020018041c4c082611500024419441044103082c04c5042c0300c0140b1842d91800102541011800c1c0c091710070342020440f0190404070364000503211508401c07030aa41107124252583f80d4480080e00709900410450104000d036414041804042200c001c0384040c262004c2000c440701000b0181c58405c2240c1d0a200c46101e54420400300b409907008003203100d41220018500180b81c50010394941055405000440c000b0402a4052000f009014004055070700c1c4075040c02c0c40c2c190081d104108415516150400240210304214521a42c0c449c081140050480d1500c1c0c68040b00344803a0040d10034803c2c22030419000081509891189541160481e5035004529040c518243c403450381740d00d0202c0400c584021064184c0081d60406e5000e4100c4c2000030414070041c900050569522290710306014020208502c009003000044074003000007800c2500c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 242755899 1250 242754649 242754661
    0x1803090510090306020d0e0d1d010f020f061f080f060606090d021e01030c0306080a03050703300605040b0904060e240a050f100b0310030f03020106090b041401030b 72
    0x1802c0580c0001c240b0743c0082034800c0741c1c0e4842d0704108030014000040b100015924030003105c1c02100c0000004c1002401d00d4000142c4d44200c81c514030b00445401158500c0740d815103c145401d9081310342045107000784200900c08440414900014080c51000f4250b00c0030907140c5984a2502070a100d00c0b85c5c60010300c03c1c40a80f2204c000c0c00189030000c000c00305080002c1e800742c0e041d1500c1c00c5070314006440c005111180c10301900c20714083c1c1d0200d0005100ea454650b0701542c25521106055013401021403401280402c592060b52a81c1d40d410203d0400802d0240354405440054110b284254140300e0203e485403244040e4075032080d000000403880721040403416086c80821000c20b07040d0311021b08018500c1c0441c40380d440c007403002003404100d00c3c0e441031403a2051240c15a41f40b021510107040c03c01905448001954024465042c00c013059545d0391394408038441a200c0440243c0d4403031208218002d107a10030040350260595041c070000c0e446040c060b907148070500005102c0b890382c0010980c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 242757149 1250 242755899 242755907
    0x12090103051003050f010b12120d050a02070b15090106170a0c090803161412030412021e010f14070e060d0b06040305070e010902070f030e0d0203030a03020d1803090510 74
    0x200071600704c0c060302c0782004504112406412483d1159000303076800c5400f41410000040e42908102070910365600304101820030602401c40940202980d5030240130340004100e66240050051101c104c808104010000034810300c2e40050344144140041f4001d5205003400c8081c40c00e41c030043c2d001001072941c80400b800c2c0d030181c86c3d50b003003d021440040307005114103006020002d90f481c010f104005103d51444021595813a802031442c031092014408140090306106803110312600380d005030340400c1d01514807a40c2107403500c01c00d0021607448007007140c031302100351080141044107488400f03000e14021f00c0140038041c107002c51174001c01001560307504080181d88075040c941d00043c14681e44d90b83c0c0381402580d0722100d0241040101e003080000800141610817210090707804281c4003182002910280c0d10f591000211580017080348810100603a018401000120b030b80c1e4800503125038840003c08212003903007a4049400b03045010601c0401e800038200301c12100c0813644d141100301c40c0301c4111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 242758399 1250 242757149 242757181
    0x30804050f0d0c020a0b1e0c0102160f0209070807020303010b1308010f02040f0602010506220e12030a0e031e0307021009030503060f04090b01050405070c05031612021209010305 78
    0x2200034003072800a00c0549510844a06283c4d00850396054100d480312000d044601c906100b142c56007209403031042094200760007030302601400c1000142420309903004042d544481f4a011601c4151400c1d40d0021407629800a0303410448629010307115161142002c2d60703c4c48180150000718030041803000c070b40074201c0c800308045c0c410103000340721107080e909942011b500103002d00030861448420104140d481449074a1280c04010942004042c040421361004d03000c1d60035030900c054642140b4003045104000d4822400550f0601070341e28070300501500103d401150302e01d82030750802c1141c45401954525a04420740500841d5503417a00c81010a134544a02c40c143c81c01c444e4180348009040c1500240554410072094031000d100740991800c03c011100200e90090000301000300621650070b00e540065400b145500744400700700701c2a206c040c5190007a06260840e0b803001e00202d010004001c3c00c1c4100005117000034007000c000200301184901030000d1550402d40d0764400100c04001e040b10304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 242759649 1250 242758399 242758423
    0x3c02120c0d0f0308090f0703080a030f0504030c0213020a05090613030b0403050c0c040203010506070b090118050307170a0816020307060c36230613080c030105040f03080405 76
    0x92840c00800c0e250603141c0501118090f0041006000040c40214010801c0307001c1d1000140507002c41421a13940c504140c001c01000e02c10190348000c000c4034100302d40300b51402580641c5402c00b000e5594410841d6030196011312980701ca00503c440824030782c2000542d1007440080301c000b0b0f00d403070300e4150031160740340e89901c00303070180e011003007880141608a40101003043c060390942d14001a040140410780c4400c2c85040e80001c81040181e01140b8807051854002c110940080b42e04c065030500041d6000d0010420345045e00001660010400d9400013001090340d101d05c21030900a80e4100903155040042084103480005403e86551324420300850310301a61001d410404d2411914004140c5508000c4140e085114000750305074014001c0480d02000c1d281c12203c0c44c146090241f2034030b26900d000c507d2100010740e0b2051114556440b00548400d00b2144981c4080030b1802c08020700e44915510040e000745d2403c814400400c1c01e600c05c000c0e11079050b0500d80e00301c1c0c450f860300c1458040301c1d81e04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 242760899 1250 242759649 242759659
    0x60f1409030a03080f09013b07080f0c0a0b071502040308030f0601020f150a0c02190f15050103081803030715050618160810030605043c02120c 63
    0x42d5010181c003c99001d00031446014055455528015000d00300c03881c2c40d030000c054101c41540d443c130b0350654001c401d051902e400d5404451010b01060345242451319084194540c0054204141a100c00c000e8540030b42400c9806c01c000520300460440750784141c55019009130755070541445808843d0f0103c1d00190703802502070303543c0d01d0007004204409509407811401801680815402110300044840c8015100c80f50b0384095220411208010015150440250f008042109464448038641c2c1e00300c01d8012007290b48030002e20318058401035103440d45040603034684801440444da40c0c6043d00c0b098140c08080b48071b80c02c0040c00092440c041c8400050002c1000108406001c00c1e035000380703010700360a4030742489007400102ba2190680701101c2e2409250b01e14506000d11512540c8000e404c0b0301414003031024280c5030b85906082e940210740c1515840840d038262a030f9289013110520005d428401c00c2e43c5c2c8104403500c1c20f0365a005140c4081d11914038025201e0308401c040c80500030307094000742 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 242762149 1250 242760899 242760913
    0x14160602030103060b1f0513031b0303030c09080a06020d0207141c02010e10090c08120901020d050f0910050d0608070e070207050d29010b0d060f060f140903 69
    0x545800654001d0000326400e904021095000f4180300b50940741c0b101310000126031090315041c2c02c9849400505d00382d00d602005980000116203403144a503101701500d86c0401849095080150948103504460000c01600303010400100b1000302d840c80d55a40d0264000da40c8032025149480a805104005042d10f180e50307036071300301e100b90010360100400c80d84ca203880c17008115104281c0c200c90280e450078403140c021025910655160340d01010038548600c952071010790319006554030303214190011010490001034071051942c0c0401c12810381c1480c41c41c0031803901d0b402903190021400744030305007400388860b84060024140a82c09482010b0034504042040b15554000c4aa507901c052040a420714041f6000c210b038280b02203048003d0f650040c01e5119040240d03075a2002c032030304c005841d40c02c61840e5421100076442c101c9070746d0f008200c40d5246030740303030200f00a81200320b885660041d001054810740c10010308be003000001100802d02d052407003040040c8240110345204144100e54035000d118 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 242763399 1250 242762149 242762153
    0x10b0a0309301205071d12010905060906010b03010513021c18021302090a15120204030b0702060702060103170901050d090f0312050f010b0f0d0c050a1d101416 70
    0x8002d81000401580c40c40910b051400511045902c2540d038400080c002c00c4040480742c0070400850000b60b40640800c0000c0c60391b088070b034215444000100c940b6040542842407801003044018003600d20011428559450500060441c1c860f400720010f40d00d070007040c040c6c42c0c03010500344118400100e000510000200c0280956442c0340340350200e2080703200c1480c500940482d07100b664a42e0401038540142d0505081101420201266a41c2e0810070042c00c658003100781c0d400640020340c810036030b00050707088c6400d002e4184007004181c2c00840d03201070010800700307114204038160032034200381c8107581d02035a00c0103d41d00d03c50804440115403c000d101010070802180801c40319009a860010165440841e04141d071020389185d00e08107030000060190602410050000c200002c402c149414940c0584c4030a8802d440248408540c0210310a215107802c0100c080c3c600b10740c80041440010030310b0014004c500703e14000b0080008014040f00300e0b459810469180442c078000e400623104240c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 242764649 1250 242763399 242763473
    0xe090a0e06010306150e040c0e0c0f0c010c031404030804141e070501180b09060f1b06010305010b060a02121321020f09070806010c06060504020c03070b010e010b0a0309 74
    0x80c2114185c034408202000680c1c4c2031101c1142d0140d1f501000b240d00903450700c0c0c88001d0081000d0241055031078100410518a041007006203651040d140002c990407440840c0030f422240b20a60000c3d8003c2c0b800100400650300c1409154060391102540000d4040030b46c3d00d0b4508680111030180000102509491074040082c0c094100e07542682c80000c03441c000410211650481e1280284c000014042d001a0340341c000003078250105060089414440f54034480c3c0c032040ba00500f0521145c100070014014450b00780940d44224400381c034080d140402e0b50b1002542d07a03102e0103100003880340201c0c071080e60301c0004031110000c00c00011882401d50500c81c00d60b40c24040280120321500600f8000c1c0564140346052500c9a41c0d41c0c1c44408182d584e80006652203d0000d0084808560b83c0801060542c0e45101074126004400021500d1f9503151400c4400c00f281a000607190001c81030040003c0e601d00c40499242c026203150104201081d482d00c01446030904a40200f000d40100030800e0701072036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 242765899 1250 242764649 242764661
    0x61804090809061204210207030b06040902041802150c0d120b12150105090c0d0c09030b07030603020f040207051914010903120f06080c0f120102040f030b0f06010e090a0e06010306 79
    0x60340c001c6030780090301ea0600500410000a06d400b503041000c0806c00305042160459100300064070200f03000040798009000c85a080b403508c52141002c1d50782034290b0900440c007080007560341481500d004005400700365212000501d40040040c42c180f220710f0414160480c4400c400045c001c13844c8180d4801101d42c40d01a20b6080620310500b200002031103181191400e8040c6012a1405240c038665800c108050700c00800110180a100200040015508403046d4442c02c002c0d031307001900d10f0440c4100100402030260a41c4078900600400c00490700220f107420180d402642103c07007040301c9240000100441b90303500314207546031144250515070440d0300ca02d48030f80300c690200034800c0004030240446407580510046a03201c81d10107440c44c02c10151002c131128000380341d02d0100401260060a99109400104040f28001010020401403010150700300c030f01250740085526080000a000460001482d803240784084081094505240c2c010710164503110141e80c3c266031281049030140c94 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 242767149 1250 242765899 242765903
    0x102030f13030c06050402190b030106140918040c0306090602030708061e06030c07080f0d0b030601210c08030c1e01090803160201140420061804090809061204 70
    0x100000c0000d881031529925081000d078941c64914006140e9241e04e802090001c100302e070440324015200442c101400040341c018214078104643d213606210000b03240050f0440d420828074014008150659180c0800c2100300c1d1410000001a50703c0742000031625420350b01c060f01c11440c0036054428040590000c6120340b0094035500c0780340d19600284a800c00843d0244000d00e800918091000e05e031490096402c44804a03800d4109030341074a595545a020043d1462060400108680a1707038890003030291104003103000c0c00c1c056142200a100d180e0500b1a240700184c040800981000700008011010300b4804089a481e202045a51552040b0b094010340c1900442002200c44400501034000340540c4451000e0950b11a03034403a01d4107040004542043d03548561020300c0031141e5000080c40385005d0130801c000703060703548540d2040c21804001280035032000c2000e03804180641e400c059500350f00384c40014286006040540f15400741034000755002d800080c0e2041c0b0b801c4d81d41e08403030183d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 242768399 1250 242767149 242767171
    0x406030507021603050c01080601260603060a0606080c0c010f020c03090a05030f0c120705030a05060a0c05190e150310080111070506042901091d0c21070302040e010203 74
    0xc0b030f90940280d180c225480002c044d90b0041c0da01440551003207050769000101810503006190301c601609280010917040c07408000814802c200f03042c6410418039801c600004410048541010001440c0090050030b0050851001544040c3d0f01c6003580890080a9141011501c1d000d045610549940c01075004520410940c0320214440ca000300c0e10030800d200400050031420140b10074411951816210711595000e10500003035240c9040c041248803038420006015640b8185c0d002e5804c85200f0420301c02008802e100d050031200c503006043d10695918146003081c0d0801e0400540440544541407414280c080140301d81c80000c1c1c001a400d03105000000c0c412000c1c07002d6000d840e4010820040e0843c6c1c02030022901141050485203501d0009064140c0c00480c298980182c200003a070003c12090350340c414100301c110142450b40c0e012041d007000317054190700c290005400021a4490305203090036040180710020303030070232446c0000c41e4060420312100101e82c0a9070300075001203c01c60030b10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 242769649 1250 242768399 242768413
    0x9100908091315090c051207030507080702010504020d11061b0f1002030c0a0513032004050f10172a09010b0f03010306050c0c0a0b040512040308072006040603050702 73
    0x180358240603c0058000c003140d540d4000e482e00c08a0005000c0f00f07480442840401c0001c104440e0100c00c43d144a180b95840216140c1041d900061025200500c2c80c0c1c2164541414003005a440104d11102e064021044184281c0c00f800060841d11413003039080640119010b5119544201040d28004220b9687c00d541c001020590040183c1c401152085181d580c00c001444000c0d00441c0a05200030704001c0101c081500c0c0d80e5910910713a00145142c0120000140101035450300e4000d040c2d100551071005042c900b081c052107410004507004122401c25002c081e01325010003000000300030072401250b00f0301500c1200da030380d5408080690650058403e40004550005500d04854201210030100f03803840e841c644483c0001e190207400c2c980fa1190400c00001035040c100301442d0864000c0e0f083c1000e60500d071070b01c0c3d07141110401811055000a001c1040451415415140406d820038030f14003206100401030740d004404641c2543d80300c5408540454460b506510091107075545400b16484 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 242770899 1250 242769649 242769679
    0xa2d0521070f1b110909120c15010f031101030c02030c070b1207090803031302180408030f09010c0516020f030717010e0c06040504020d09020a12020103050c070201020c090910090809 80
    0x10f843d6059801401c6501010094012414046265640400c038401039902100003106040300590101c20400d00ba50f00040300d40500d20409500d103401007100f00b108890061a60703444030010f640e170041481c14541e0702c5008a813654020b10450712411405420341c2d00c016118544503909400400f01c102c4140003044c00501c105019150003010f4444241c005c42c1141d03620f07001003800e44051042240c000c603a8940c01c0c80c584107403180c05c50080307200b10b40c496260703c3c00c4a40d400081c00020300388000c0d41c2c102002d94100c0d9401104540d101e51034104416501c000c4d500102e840132486640240c0c1520407110009140c8038080d07081c000b00040b500007031014000c654400e69a49100c03642103580302404000821843c41d2541c020284005140400325109075a43c00040880206611201d2080300d0030500100319030345445440c0e80010350020040c01d18401340c000039075802003442180d0042c22040c0120380c60074002c000707201c2c101e0b600407028003000085103032510282c0c108024860041ca0303070102c0900e07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 242772149 1250 242770899 242770937
    0x30b10030f08030a0e060c0702040e161a090d03030e0615060f030403030b030111180a0e131a100312050901020a1b09020c030a2d0521070f 61
    0x2045035008000400503010729110190654005401519010ba4809000b001c0c1d46040c0902c42c410b00d0042c04040e12a01d80740180015209400707402181a0030044840c14000a005503c4007552986100c0c05001018296680c0b0070307110310000c450307104120032803d0b0b040541c15082204c8001030042030340c00743d44401840800b074400c190b03840ca60000c4180183d4460500f95005564814021b14005c40d4002c4100301180c00c441c00162440c420110004e404001c2480031748075000e44c1c000540d200e602c0f052804e150362411840c06089641d191040b0700e906002d0061810049480214842031078815040c1940000801a840e1100315040c0700800c0003a20f846005005890b00c550040e0050081700c031080d030394243d20140301074104c0011000c80da408190f050152010305540401080219070b07418601034087d0005812070441c915015840c0310703002200c01e800483c1c0b080b000040c288152030300c1c070b01d0014915040c0e61007000c500d1254110208202c1c5544907110411844142e102d1f01c0c52045000e50806c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 242773399 1250 242772149 242772181
    0xe0d0e06071e1a2703120a110702060301061214040201050d0c1e0207090608060103051002030c07020d0f030f02060610080619180612030c0308070c02060310030b 71
    0x16101c000072050703034a194804080b080300e02c2c900c5465054100395800034030440c09002611684000e062502050b0400c0c5420f05807400c04103140002036042c40c0d0780000000ca018001040703106210b40755071650422841881c203852100d90b004101640b6580c644000a040ca0208400512140d051424402e142184610594012601a582d161400e50019201c0e00070f444114071403010402c1c0401e405040f211100301c0d8048801030f980c0070344062481c03c8000b20070748140740c10402554100754010070003e10000b400902d201610a0302584a5a6028101c0554040c151010b500b1040d0f001b900c5041000740c1d01c4c130f1512213200e40c03a080700706800c450080780e460740205c40f0789800082012030540300c113014203400d6502080061954004c60761404050000d45240da00014059110b9400092075107520f020302d0000d000e501e0320496240d8081d41300100308465658002d828042003030301080110388502c1ea60080e081d00641019a02c0c1441c8422a50070800b44c401965030a524001040410311002044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 242774649 1250 242773399 242773403
    0x50a210f0e13020c0f100b1f0504060c03090f120510050f060607060b04090c0e1503060123040915061a040311060d05010e101d0c0a050c010e0d0e0607 66
    0x1006880c06540342d120007035002010b0301a05100b44400510780fa80100300d001c00c170781d140d44d901040d0901d03810280044881803455222118001d03050003400c259004c4195000c5550754a060242c86d011410252001e071025001b803016030304c1d240f101182c503030f0686110070015407054003120200b070f40c828000421200e080c1d54100207007401c4000f044461802030050580e680c01030000003034400603900000c0c00c03508040000c031108405880f0810840506010983d4010b82c0b00361245446131032140040c1c1c43d000305000d105209070b0301408142d58000c4001c84888140070291082100010505100b01c12a00441a851100342440c1001c103448048071607a11a00b420825404d0600d03045907104810955032207c0a90841401d110150811002e8000c86008000e401c1c00c01c0702c00d042c015000068040240c0000c00782c5403150300d607142a07601c040350669100116061041e201e100300f0b201140c0300c0c030440400b0303103556007440070303e60206101107001c0030300b41e2007034a616580407100004d00c00305000305030700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 242775899 1250 242774649 242774659
    0x7320f0307050d0b01290d02072102100c0207030201020705040c020c18090c10121508010906060905100602030304060921021c05090a03020d050a210f0e 67
    0x4114164244410082810080242070303918240c2c669010511507440d140055441110042c010403895440c184989a0020808090b420042e44030b00940700b18072034002c000c20303410340c0000c242060101005030b600012801002147e03000d0400440250707034003214510100700518288100c552781d40005a4101140d606801034014146044100030090103800d1009055000b606000c200c683c0d40c11042060b074a88001420385a41890704070945017028080d1030321301511840344040d04081d004013000704190038020010500b86c030f50701c0900c007201980303038040c200541c24001000104150f40d000074058400c0790303004200c6682d41e501205421959482014056042040440e010038050703040104514002c55080380c501d05014042601d46590b004500300507008800c84803400600342420941905141c40c1c881d040480000008800f1101342c84000d108000b103202c01c03000c003e400e00a4403400f9030000c4003010807010705100d07030041040ea8281e6a0010383c0090350b03174040c9030042000a5054101500c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 242777149 1250 242775899 242775989
    0x30906020c010e01120f0501060207090b0301021c0527070519030f1e05070b070b1b04090905100f0902030d020a05100f020909010b0901030e12030c070f0c03030207 72
    0x30056600000c954900004586c88400d84146d10810340604c03802031410354000c101c11440c0c1411801181c000c0380c0300c5480f0380d00422018114144e102c08405020940110004d50383c0c613004591000d945100112840b841704200381c0001d0081d01007440000c6803025a50040010f141d070300c0200c11902d00c0d00008041c1d030f003d8845200030810f1001121058a5105404410704800351a014a0f20b4078170351240d65220b000180050403c00840c600a80000000a0ba5284244140051103481c001c60250074581950354001b441405810084854048070360710f01088845034494107200900102c043c00d0b40a48a070308003c810f0b0910000c3c4103440107030414064514445007080c0c08014002e001c0c98076008603001e0181c980c0c00c1c0d688890490003041c0311440d85a07030340820800074064440d162000d82164212045161031404042c04490b4010811403440e07545488038544070f01809911400070300ba0040c9412b01204054002848205032005126074190040e041901440c1101d40c0251000c0481c148103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 242778399 1250 242777149 242777177
    0x204050303070809240a031107110103020c01140108010504051c1b1103100b19050312030a0603050a060204050913020f010810091113060c0c1206020415020604030906020c01 76
    0x1805840e05401c000c001040f141c0c280c0ea0b1546a020703017044041d01030721002841910f00c2d0342600c02e101100f4404507605080090b142c41c0d07048160f070307105100c034185034000400c0c60b01e1403020350140c011120802c5d60240a56198801c003030007800101d0301151213124030020320701480710340520324041521039230360608243c994200c90146100d90b040c080715446001d06c1000c0e02c0d5541806000400c082c05140001c012441400700207011415080403050041c05180a01140d1000318024400c02d41849170b2560707070b44541c00700d04010000c0c0d606c054500e0140c090108204441e50300100212030b012900c400294031020704c14030300c0b001d02d07560007175000d642070700400201e50140c000a54421000c43c0c09080503135541072800282c8680d0a555041580d00141403402000d000040307002422940c6001c00c400320b160343e03821900000305c4c0984034200003210720100402a0980444020784841825859231036190b010107551014203642c100e01050009602240300c0384005410000340105030341e0310210f130b000a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 242779649 1250 242778399 242778413
    0xb04050c04030f0305070807060e0c01080c0f0924130504110904050a0b03030a0201090309170d0503090a0501020414040b040504020616020a0302040e0d2d1b0506041410020405030307 80
    0x240c044040c17100500602002c504044080d044c504d005d41c0001c070f03410345032044150501404003a0a4144503407181070041ca1907414050302c075402038000325140e490b14180c001400f40320030580d00c5000d0320340516a0403110440500a004420032024507100004c0d1640208005e65400b649102c09050051210030b21502d0980c11050b00601d14000020f00183d0040c04641158031140a110160391901c407004c0c101980f02e88044002c00c010075007402c0c2961442200c584072007804001404004011003c203540c26010301c007151160340c0c840021075640740c2c0c4110f160312400c20907400301e01c914500f5508880c28242400789034862075004003010f00c1e01d15080c1d203aa043d1050050240d8000c0f0f400c45010005031103034400e551400c0440d070002e00b218a00a000203100f6403071400c0040100103440d03040034800e084280c040401000905144260344d0342400001146506440c001d0070f00d10580e02400f050245c06525072508081076025180c0e18041d54004100341d12035882410f405600400c1800c02107401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 242780899 1250 242779649 242779673
    0x20702130902040902040e010203100801021305040c140a0e1c1a0a060906090b120d0e220c030c0201060f060207050909030f0c03030915270313060e03010b04050c0403 73
    0x402400040c81303040a4021030111015021480c400c2d80d03002080c4000705010440200052410f00002e42c80c1c81210604a82201c40350700c1000d000e1500c44002e020700134002d28021800155000f14507403203040c0b50f40000c1c0f1044220000d6401810750880e082803401140c03001080d034607000ba0302c00d00c0c502e8140d103c00c0d42304c0c1401098070400d140d03a010080307a03020060250030b0003401c02040100d11042c0d00340400424400c0c2c81d20701072017a807141404404054111060b04041041141d01c5004510056844c89840a0b84407100e80094030782154280b0b9540c0640c886041d090480d030081040c0754681e1140c040b038980c240603550250380944000c00c080c0c94015542a40011200d040e6800e0510168000507660084d030040d20340754001108003c4804400c002003200b1402100c003010803818600e0324210801c4a81d90201c1c40d102a03041709402400b410000c45038241180c100600c0116036503036000f40b50310801d00c8080c1c400c0d420090748049501c0e150103400c2c01244007501082c60030f46541c0c1d0300d5101103d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 242782149 1250 242780899 242780903
    0xb1308071403090d0503030603102007150c02060702100e210d06031a060d0b06040b030f0609160f0510050a0219030503090609010c05031503072112030207021309 71
    0x4400c2060309940d886152a0071394052103100107684a041c94808c050500148101800740c052400c6400c1a60b00c8500d01742e0019a260103000c0c0b0f031ba0b0034650134100000701700d00e12414022814404200c2d0002d90000d203041c4500910742c259291041ca411002c0c00340e41d8150011070f159031060707192003600d503440329102c00b02c0c681943c3c0842c81d01c40d2918040d420340d20198400d0f0f440e2900d499250301c0e180480d0040325800102118054503448190342c0e240c0316003801500c49409665100c0328400c1a44040001500b503440d504100d40103460982045aa2103c000c0c01c0d22004500c0c1e100e00203440c00002c50106c0a03104010412211643c250500302c909030071040c00d8804512a41817440d10100d04024810701003030180d0740300369603490030384542841c140c4094241c622607031408070b1020318294400f040da90021001046c2030840d440d030748002840c024490704000400fa89400501c00c90040146800405a1040680b010000d0390001c040d000ca00900102a4020200711900c03480c954482e4004050f40b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 242783399 1250 242782149 242782153
    0xc0c0510170103031809060501081303030b0910050310020304110111030f030f0402041d070524040b03070809060702073309050f06041d06120a0606030b13080714 71
    0x81e01a21544503035000b0f80c02500419404161440c02189403905640a00b03a040c0317051201500c0e040008044030301c01080e00048800da02c2c0c0382c40405119030007412044500070700103030050078a4848012400d02c241b0405200744120070065400d00414001d403803040d908404620300e105013000055500e00c1d00c112900641d070000700800d6802c3c025a1010318001c2d40701c5c1c03c4007103051a00d84148000c40380c00b01400c040d11246000d040b1004100007503110700f66902a0361034248011010031a030310340510a4130f070074004880461301080030150350f8040c5128041641c2c40242c2600d0350300c04240c56181c1503d00400580001000307100d01e4030070071490400706550f6000c1c155008015895594042c21410711240040c1101c0c10401c8a40b8141d0b0b0707202252181100c0300f0b440c0a1800101e202d42c0600281c05540c8415048001005070303540d0b04075074910f500b1003829503042700070314a4400014915804121184103401c000300316011009a1680c156550040c1241d240180644800407400c0300ca400e550f07414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 242784649 1250 242783399 242783417
    0x724090506010e0702010b060315100801030b06130213120606090e19051e150a020406051c0b0303071a07020d0c03051321030813030c0224030408190c0c0510 69
    0x13070308c5410055100b481c44901141c00102480c04100308604d1402d011020000f44030014030100380f0404080e50094412120250b050a0350008070020b03028120045801c0090708a00103002c54800c1640c00301288600010004540c403040c4000c1100e2014a9203000c1c0c0d80011003601c500910202089001406901119242d01448400b6140d04940e03205103420340d0002c4031f488191451050005801290506007941424100380009081d406804e0130b402c2c82c07081111940380842c4003544858020900078040d244d440f1220305100701c0380301e6420b0000c03410207d5400009c0d90144003165600102c07005076195402c40041e51011140c54018070302a000003441f20380009a03c04440e0301c0002c0d460460000600e001d103c80c10040d041860050214001c689a145001c0c0000da0041c0032136085541100c0c22140c0c1c4200351641c101b81142d1481541c41c81e0000420b2100b401110400361041e80c0401c80500710b0203404060403110320051520040c00048151410700280c500742000702c080d031400e1310f042a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 242785899 1250 242784649 242784671
    0x3030b03010f0e011811010c0f0507090c110c010203030c0c01020904060306051504110301030308270a1e02090a0e120f0d0605010906020d230724090506010e070201 72
    0xc680302c080d8000000355495180a001c2d4600b03001e07041c4101c0c801e0031140032100154030b4404900304800d081c94104640505000c00b08014001481c02e1590000205c981c043d46480342c001c01008441d2903035012481d0003074546a4244c00044404411806034091415900e64118902540c1c10440e240b1060b950284215140f90b01c0c1d611601005502540700170a4504100340500c0310310b51040251030185092a030107a111000220440741100c1d45464074401c01e5440b59140b030710749440b4618800b030a030340c41c0905d034000001c0010300a011500440342003c200b0b03400002c0312039500400d04029040040800051030308a816440001240000360507201100000040c1d401103905c5002c03000c07411007003c201d0f138441c110b03280309040c090701007802c3c02100b80d824544081c2d6104c0d1751480340402c004030505141d034960140351112115884450301541c5407050341c50900841c0b6040d5041c880c8041000e503000c41e8060844c00307052001e80e0888060415a401c11a0f40c0d03494002c018140c1041d50b40b03554070742070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 242787149 1250 242785899 242785901
    0x50403120504060c09140609090405010603140d1d0913020102121b01060504020918061906030912090f0b0c070e011d010e0f0a0c02210912151303030b0301 68
    0x200c594803030f000008240d482040050900005500070000e4030189048001d0705440d403904481c52040d0403070742c50880756221b26115005d0103060300000c000e00c00c51124201c452000140e044410007594885400e004030b0034141c100542c10a00c940703548940b24101103501800544c101e0f81500e401881a10561164440040c0c40ca910025451200009442c490812014280b0030b5901901003200e01b90300d00120306d0005506218002d803040000310009002c94a03503a070f43c0140402054010768024281c6580360b00107402030101c0c50081c5c1d0048691104444110300c91400c00c000d035081c910b600c0d80c181d4184102110301c0d03000300c49240c1891040600210f0b1951041c48258020450803072244180800329010400f80300041c0d105090048812050100c418a2060815840340c00c2c680c00081403445808200d2401e402204208040c00040c141c1400311044c0000174071318a80140c66903c0c0750784003007a0140d07031844038450030f11142e603018001c01c2e180d000c1e110a02490038028a00410300d819007000083c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 242788399 1250 242787149 242787151
    0x60409050d0917010e0c06161a2e1511030403050a02190302011707021005091b030307150c02030708130f0e092d010e0d14030c04090504031205 63
    0x200205502c2c0c1c1c8200140d000e440e281d101d000a401009003d0003119034450b903540e03551440300920035074010641d003402c05104454440300381d81015582200b200d01c6a551181e003803098401d80164240006a0201710301c40c5000308034000781010721900740d14134254032051442091408101081b2035804180b6021030b00304043c1002c2c5000e00d000c2c01c1c51040600c100b001400f844a040b00d44260203180400140c1c1c0c100c24a1214681010b80c200f54070b40e100d0b00100d0503d091070303401c0c000d002d00c1c010602c01c0b400400203503031041720540c05400104d081c000f001c01d03031340740143c1600804203107100c5400810720001d500300582c07408450048a0900e005590341201c06e41150f0208058400466801c0004100181045e0003d10003030f4050403044c20881010790715030600500141c88130100c0c11800c0342e040c4a05014004050b0303400c000700003c078039240e0140d031200008051900003640f078500d0701020300c0400044a0050180d00800c1b498140392002c000094003000b002030301400490b00da15130420285020706 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 242789649 1250 242788399 242788423
    0x304050a02012a110301060807180906020c190b09070e150109031406040506070f020a02091b070507050a05040b03100e1204060f120606140706020403021504080c0f0901050906040905 80
    0x500200319154042c5407c60b000c030351109003158015402000100f02c0b0203003c21007032441c10404580c06409003403510182c41003550700034461180c0322890b158000c00d00c1096098074850b040c501c000f40c449040076942d0700f00a0241002d5105000003045c0018004500311284402c18100039060f00d0380d035152444520b01034a01c2c418250088001c00c0100035050182e19400a0b003410301140c50424210000e60f02c005480b0024021901000420030040c580c10140710726012846103655a00e11074900107444450501c2568041c6085071070125041c42c1034003c1c0501081c01074018000603003214170001c06426000c9280c02d142c000d42401144001411008002515072519400031081065600400140d5800d107041040b46c5030010500c0496030114441000c440c00145a585032645410880000e20490384000d5102c03001105003007034024813030081d0084400030010340384500903440c184152080c401217043d51180e1100c00502840c038110704215040348029200052050f00caa0302c0c0361601c5540c07030312 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 242790899 1250 242789649 242789663
    0x702030a060c18050a030c05120705130b190e0606030a09020607030309141c050c070506040e01060206010b0903060c07150c082211010e060d020a0806150304050a02012a 74
    0xc82001510f100584000b01019200400344601d03644030041d03402180d0050500c10260184101c003441400c00c410310107003a0040981d1383e184d22601a803001052440001d078013642d416413110441c030804482c0fa400720b45010b000e0210642e152010030419510080c125510320340d5600f500e001681310400600002440781e00c0004411405090000b0340a04c2c014030014194031826004441490003154020000310f1418000c3d26000c00d44161340c00d101a41c0c10264120300081000a40c02030000041c07812501d1a800392002039890b0142c14070103100710002203415900c524040740c400c0c480e0f44002c0c2840d500a0313414841480490064030103a40c00e00440320005800c3e5802d104011138180140c02c80002d46007080c0c10940c8062766005c0c1003690b811046030510041c0e00c01c5443d9a00d500b0125181041031a008550b41e0281032400303400801c09a0340745010f5151a40302541a0204100b00c0c1c0c001d6412030020401540203900440b4520000300280612178880c052a81c0c0b1000c0c4200802c203200c0c81040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 242792149 1250 242790899 242790917
    0x6131b09050f01210305090a0515030a1113140d2906010c110906010e030703050f010b0a0608060d061b020606030111030106081501140c030d060b0a020d03020702030a060c 75
    0x202c044001032042e08880808490f40d2100b04030780c45000c011a99055040c02c0480d02c42c14034200051b07622603540d02142c3c01c0741780c21020f848016804401144246040c0e0402c201c1420385800d44603060003542400c001c50061750074140f10076260396032f150202110040150076105071075038030a280411160302e2058490a10340c1881c07404100d10030704640c4041c0a18010204018640f21074440491500703041e4040c84041c40490090391190480d400030031005012142600e603a40380c003650301c0c04010036980a9510708a1447c07241d01d410551002124103d644446031916443c04001c241b1082400444110380d0b66002e600c0c110750141140e102c3c0b081d454015080525102052609560b45880044c145000800040c0600c60300881c100d5004810f0081010070440b10304016108542c980c40340d440000004103c41880076400001441203402802007400706035035079044014180500400040540c10000c01064086e11a40c05080042d0009040b20340c03246540c1c07920421141c84280c18000104802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 242793399 1250 242792149 242792161
    0x50a0b090307060807090905180316140604030903060b030c0a080705010305011205030403140c0405250206100603020c1c0e0a08120405010305191b2006131b0905 71
    0x110030b01c801410700303041c60b078007a00d41440d0042c0440d02c280208400380f981c40c0c0c080b45603844043c0c8010307000010542203aa0700d03080d0302030503400700a440718112107030101850411101c04000c00d10b0f90040344c0c543c071002401411583c3e04400382056038156505481000d1170301c0916900c2c0380400c070061101c600034245907402c02c8001030076118141c000584a22840002d000010000011601142e03000000711400ba0400300d5020f0502c0b0386c84890560060820f0306200003401203040103a001c02c1240141d2201040c030703844c181c1e01e42104aa0104020000c07143c04c00459001c1d0f002441e0003580c00b0280c80d03011102400900343c04500c00382090020700c01503140305507401c0199003036000d0000d1000030039401c0c100b0150191a48294000c09041680350404130702402008014150014001d203824044020b40001d41c046403400801610002001e840602c400b00d090b4640d0012843c94401c040c00e51590740f081c50207042a00204100e50088040561a000c22041404440904044807001c0b0303041c1825 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 242794649 1250 242793399 242793403
    0x160b041404060302100c0201020a080f130608160315050301050c090102011104080604080708040e0711011b1d0a08030a02010903091a09010e040b0409060e0115051003050a06050a0b0903 81
    0x4200d150069140031003d00c050398401e01010083e010600d010080c4118500c0100d04000d841c5000424104010985826002080010708441804074201e012201e54462003140d15001c16280001600c0742d071700050134268440c0d004030356a440031035906140701e5500c1001c40c0c00c60f4404c489020300c54801040001007503034203004910340c1110042000381803504107400203448000160000702a05000030741c0100f000300e02c0003510018241c401038180300c3e150807c0007404101d80e44401c19155440c046a452000c1c40301341400000e00e400d507641445c200c0e141e181500110000000d40d56012058000000300440c082000b40500403917a8000310307900c0315a203400380a551031500f14a9440307241c52000c184289210040c0d076909030b024a000400390f500c400110f03000f442c442074819001804e2000d08401e0040076080ba03005030007000000c011040c45444c0c0000b000ea018090298844401c1500000d2544139400c140d82201200e00c0001e580d554810028101e000303d0f5101d0211100c000c10070300101e01e02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 242795899 1250 242794649 242794679
    0x12010e0d09050901080609030d0e0a0812040b180c0405062116060212030609071404090c14030702030415090503011404120f02030f0703020703080708030612012309160b04 75
    0x2440000c040d18280703c0d000e213441c2d01481254601031a030798030850380d030030710208055201c01d500441e0840daa00c8101d1074dc0e00700302c442100c00b80e80c41c402c5000895614a01c440e0030f0712081c0d480c1e4016008500e281820040a000e000d0000c03940241000d150b0300c2c0181d4540071010b04604142e004003894203140002c8942030000d94003c2c0c0554101344040c1e020359031000b046903031144c0200d072401c0c3e85555031300d400d484603900c241c40c440004901080209044050368407401c8140816110a0501c4210350394100c4248000c84200d00160000c0c001007000404101014029aa42e410b25801c096100c001003421203010100303150000c0e44030010303c82840000c280303028031800c0600d02984248070032140039582e07205e011820411800e002901c442414030a201c0040074581c41024980d8501c29410184040c3d003059800740e206042c0da81030340d40c90035014460009000303013490f000b840d082c0b0009094880e121006164481034010500a1100c898080600b1005008149003060b243c5050811080c00006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 242797149 1250 242795899 242795909
    0x2041706010801020703050a030e030c100e0f0c030a030311070503120402040e01090f0b09120d0b18090a06051806162a02040f0605091306050709120212010e0d09050901 74
    0x11040100d171020030f13482401c0362041600e504000ca00d441d604503e0034914810a410300c1224001e46ca0540c55403007003600300c0181d0302c0c182c00c100c400d05201142c00c15112003600d0289541503100301c803da00041d010340c00a15130300c6114030b082c0341401441d40f551400c650000700081d2001030400300308000c40c580b0740306584034400f089008201c3c80c200d80d0740e0444e01030036948014225540403000a1501d4100700410380750000c4010125450307103070b240380e044060404401654811103911007081e4402c00e6224856200b004813030020100103280341c0340c5a0051402070508101030b240c1c4e80900391441d10400c000c50180a516241d122026050b010092041000071810040e10103483c4035920b540341d03907040300c03012160111000500904d003242d1810041805030301643d084550082040351030f68810030b003440c1c0603004403c01d110a5440300022619030410740100d800341403103184504098101500140010004e1000000740305035441007945c60b0109060032a000030703410000601c82400c094a582e40102 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 242798399 1250 242797149 242797151
    0x1b01031508030a08150a030c0e0a050702060c1e030129033c07050c0609060f0103030e0109050406090e5808040b1f0b0f0d02041706010801 61
    0x742001010340d103c0c881c0030801d000300820300d000f0414100030140c90203c8000000c05185d90039946c3e2a0480c0d6144042c4036400c1c3c0c1c1400d84e0009101c60519000e0503124900316070103000190341d001d030303442c0150f00030701d04030107102100fa203810842800c0f000086000c1c1c492030615000c00c01c0542c1c0d210419480180080708054010b205200518008030344007840c980d03004060f041d91544158070319045c2e211628420034021340641c107110140ba049001408220040304c2a55125070302d5146499030b0b81c005940941d010740d001c800402c0828420b100e604403190051401c00c3e20302d0b64490005055480d40d81003000764503030320031044650940410905410f040a41080c04021036010820140105034603a90840a10440495271901e22500e40040151803010b8881c0010520050010106e00b801c0340d040b6103c1c109007011803030300c1e94807480c1d003014100040344a858207400c1240038441500311400390181c954042c020700b00d058076980041e0001e001e02c2d842301049021405482071030240107078412090383e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 242799649 1250 242798399 242798441
    0x27050f16030606050306040b0d05070608041a01061d1206010806010807090b0d0609170c03090406090e120c1501031104110403030507110609041e060b1201090c111b0103 74
    0xa11303004002c0d0395000d00c08980004401403803c001c15003144000f54028507500408201150098000318194002e034014408181c0e5102c901c0d40140b1080c90070302801e400720f40c810000c0a00800011801c80005402a00c0a82203c01b0f4555440c45c0823403c0c4c000000c070b90041070040c02100000c00141f401001c3c840b000b48440c4500d0004207203000c03c3c00e04094619501c510f100307020700031420f44120003188600051642c138051580020380b00e03081002d0b0b6522680c181140011a1700540c060010b5185200001e0400301600c1002680c07258000d00c1e140015005040c00c001c00110f04c5010180203602591082c00309404a07020081200c0c1c000107400448601030106001080e0b202c02501c403016484905644401582c100040c05805141c51035544607081207100c0242d1144440001c0a0455070801408040d0b00c80c0c200304818000c050060300e00c40a51001040906400d800180c107100b114240001200e200320302e00d5003071030a68a682c4000341301d038410b02046540e01d803288010f80c00c001d03a449400303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 242800899 1250 242799649 242799659
    0x1d03010207031709010207021003090c090204080309091015050409050108031309020a14030a0f0e0606220902060a0504081204150e031612051c0927050f160306 70
    0x2c1c0d824480d007160f0864007104002a6815401d41c112403103036030002e002426000c1c0c1e0500040103006120400c031882d005401000561110ba8000c1d1400c0e2040344003d107003044030a40034031446000082140441101c40360f00003030781d0071031003000d0b03400302500380c1d2000c0e500c0341440c9041060300c4040e480503440c2c4d0310401c400900b0b00201c0c002030040d50908600540d6a10a114040710b41e03240c10500013145c843d00100780998040f459024600701c00810005202c0350481d540e1403511031008a0354580c00180303c180d80b0000c1407001690a6000743d1a00d40001d24480c503402103003482d00900c0f84000860f0000509020b001c401b00700e15440180030300c40b8070b4906400c000007655800e0b4140c900c18103002c0180b00300c14aa80d400d00c0b103100c0c109100190b16a00c16030320140c60721800c0c101001a02c603402010300292081040c0c1c60490848005902c030080003500d08420300c0704002001004030a030262501103c100303450f00307014680c05407a01d545440040d0070540241c00d4a90b84180f911000c0c10710306182002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 242802149 1250 242800899 242800907
    0x907021e0d020c061b1903030b01080408090411070f1a0f01050604091e110a0e01021b0f030703050f0d0e0102030702180a060902040308120f0f040807020f09071d0301020703 76
    0x2043c40c109503402c03522600344030014600007443c0354840120b030043c039840c0c074078119210680d18240b90299409028400c808401903a010b0070580e00541110b4040001221a06050700109803584a0440e1076181c007805850f04091003d414200b01d4408850b00344100120113500591504a1010502010554549000590607204c0ea00c04d01035481d031203903c8039441c2e88540111040c0400c54580034000d0845603c0d919249034000109540803031213155850210303500c00034040065440c04440b2800d44001c0320104481110b503e034065a140c8200c540100000310140450b0165890020051548450805020f400044c042d03004c1411588280700350000740c0d54028003250b203017803a0121500755890391407861000e080c02d41c026207446c0f800028004108006000103215408140b4400c0403a520f03500c1d2803ea846809854a18090401001080c089040d6000030160140300a015000c00005500031501110003140c000c0302165500341c403d40b980110707108208440004400842c948012540d000d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 242803399 1250 242802149 242802163
    0x311030c06010e040f020d032d09090b030109080f071a04120804020406080706020a06110a0c0b060402070204060305030306100206092e0615020106050d02130203060f0907021e0d02 79
    0xc03c0003500341c00302c0c0030b0103540c004411a15401801c01c210420583c00d010f084419403e4690360002030444807001080724001a601c0b45846580e00d8002d000c2c5404d2003440602411001c1650555035002d0b50380004206000810400195010003916040c0a0500c0002445c18070014030240d40300d031003000005a04400d00d0035161a0b0b5084c1030009896900100d0002d25564101c501c0da031017440c0d4080350154000410400b1244104d5080c88040c1c548041c428560060303094000c0464840c0a0b1000080e0000051301c3e480040548014101045a000a401d848845d4006c1c0e5454100200307121650400c88502c0c5031001e0140000c0049003000040141d489801d1043c20071040b440350b0f800a088038952500403a1400740540910501e42ca0700d041c0800b0700740c9180c0c0000550f1070720000007024101001e2006903a5001801d030b02c124805c00300342c003020b50b00051003564020503104a25a071607480081300c901840e455401480c103000d0f201c2045c0d0b802001c404d60f03000c0a91002510088203030780040e0321 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 242804649 1250 242803399 242803409
    0x40f15031b0e13050a0b07030902030606151603021018062009120304051008010f060801080703150209030f16090603020d030e01051603021b0415090b0a0503060c070311030c0601 78
    0x80280801c19040403405d0181c082e40c020016100c1500307000445606811440e4071358000c906460322502e8840070405d00024964441809400511600052080c103441842c0c4140c0640140c0300d810229010303520880300f11210034040000001d0070072052140781d200345100c0c07150019110100080da041e10000c180070b5401060320a188c00c01200d10305090030310580740100009049100c010015040c0540718500900900c61102203c1c03d00080707441c03044058a0403100b01201601c0d46038251b4441d1140844504000300715150200040b4426072020019029550441006881440811600c0318241551540310000c010304140c03050016075240d43c9007d0398964181407408004101c400140d49501824040c410f0341192003551005040e00824001d5000c08140721920420300000204022180c2442c086020440200d50030300001178540d01c04021003c0007000e18035690303600c00010703142920403100204403100c085403100070940c110241c2c000640801020f18101600c4a8015645480501c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 242805755 1106 242804649 242804671
    0x9050102280203070b070810120b01080607030605030c040510030f060207031214070f0e0301060b0408060c0a081b040b0a050912010b031902040f15031b0e 68
    0x480e04c049500c0385000340307140c83e81c100496400c540203148c110f400c0300900000c01c0d4a41c0807446442441e200d07030402e00803503040600c014107181d0040d000c90189400c1c820b0500c115500070940305c551a90a0701e001036140e480c440540320601c60b80d44041c0c8400001e4010506210300f44d00101005806500c6102c000d012402d04102120404030760038404007002c002051034940b00704078094105020380340c01081c1c164050006803c45481e6400840f501c00000340401815805003d25a40440180c0c0000d0421030300000203806c0d011700900c440402d08810301250030000404060301d003d0304080780d0158a41d51001c201034010fa03c944070081c840e401804640400400501880c0c0c8007c8001c1c0240103695100c80c007080003040040002c0fa40581c40e0300d9000c1510030301c0d204194620000c0b4088225240c90342c200310240d0182d030015031105181066043c842c5001d030261301038100031400e031 = true := by decide +kernel

theorem cover : BRFrame.Cov 242625899 242805755 := by
  have h0 := BRFrame.cov_init 242625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 242625899 ≤ n) (h2 : n < 242805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
