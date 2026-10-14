-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3411
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:35:11.268681+00:00
-- url     : https://prove2.me/submissions/2e5bca18-aa14-4025-bc29-7bbcb37150a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 613309352 ≤ n < 613489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 613310602 1250 613309352 613309397
    0x3011d010819060908030c1201090e03070b090111030708090f030322020f1201061403030a0f0f02070f060e0f0409030210020f0708130602060a020403021c03051902011b 74
    0x31903030203540d02c009181400071582040702d80c1500460300a59070708041e0300544043d80720b01c5070341c01d54048840000c10342c3e280314059607100020100080d42800c1880d1181c4040d9000540080e066640c1e50201c084441c13450310145209020307a45852080b071a00c00509810091160700d8000703c0c6d00308104003c60740c00c2c0200c6515212150f890b08170707600100d40c804541405518a50654044040076010202c0d140540015054401d840d640716481c10405d41419a0f0703019031200c00c9d0109400362820728405102d03800d582808040c0748105d0b00741715590030002c44c004420f0b4104000082c2000703030340b40b40c6040030702c0201e9401000351030401c20400309445c000c4d21001502c01000b1040d40018410a054282d00103860315039400c0700034140d440880001c80d84000580e4814880540501400030f01000501c2c400e03607080365000f410030360a01d00b281039101c4000766072040846c02d011003445203800403a601104400e030b4003490b400005403000d00607890032100b040c0000801c1000b07038880e80c60702190717030300d211 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 613311852 1250 613310602 613310623
    0x1005040803130615091e0b0d020405091005090610080a030f050c0a1a100f1a1e030702070519180e01201e0f0a0c08090a0b03011d0108 59
    0x345441c0780581071600401900204c5040b000280540c40c0205165a15a1115442130000f8181c3d4842062a0034064103480485410faa444406001c240300942054ac0005034002140e00030341d004030442c0a0040201c500945035010184c0c0b10342c041181d030b6600c3c2c0d203802c005882400c00900c00e400343c5681c000c00600340444500201b05012030b05a85402003000752049055005407203d03540015007083d421900780c21a58801c000e10345440016075203030180c0c00602a00c01200807100500c0018400d41c0303480d401307981d602c00b00d064004c002070303200c0c9100340c05180a07200b66409800c0b6a032a1030308125501e48d07400810132045a580c8130400a01c08d5200d48401514000603002c00c034528640c481d50300401c080000e1800500318814a0554440d41000911407141481042e490000d10311034010424007544407034074419a000c21075090501c0c0205802d224183c801c0441e1441c10540402040358807041e680802c0304078001200500942c07082046444022101180c0f40302e07250715001103141d58080c03012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 613313102 1250 613311852 613311871
    0x50706080103110f0a0b0c0a061a0a090c180e09010b1e040902241b07030314180a090e060c1204141213062003030604022a0105040201021005040803 65
    0x3014180c2c11748815440500628003e00d4564a0340800404207449100940080b00c589151101d20150701c1c000c060b5096803d0000307020f040e6464104000c0b04003e100000c40c3c04180240750700420554060344540e80081c01122286c51741a0610020072801c0d5201040e500d403081d9402c80c6803400252403608104000030003201c4c040390800079800030078505000040030f08012034a42d01800145840b03180180f0704514011070038034164201e03c1c80e0640321f01d034030b010090004043ca400d070a104a10700e03002e002d120880310b000415004a40000510203951640021419a292181591b5004081c0406903104050311121460f0403030a403004150a04000d00c018282500440c04551400c030400c000500000001d1103d40d50f0784132008600c020100c0d0381300300e03000281541c104032203049844401c00c0b44155250300850942d00d60000f04400381d0044034192050b07400002d00307034010b40080c0483c508510f100d10000940350819000081c10030340302e40c03080d00c030190603c0288000645a80200d0b94411080d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 613314352 1250 613313102 613313119
    0x506070c0b072406060e0d0c17070e01060503070c150f060905010f050f0d02120a0f0f020a09090b0a0209010c02041104060801080d020d0c0809030d121a090a0207020a0312030905070608010311 84
    0x145026110f032340c0c803034004401c0081904010a2500d00015080040d00d9070308441c108207070b90301e000450b10707480212040c0000a20015981c4001056081840c550f45030b071260100d00123043c00403500c11070310982e104205e010b80b100010005000d002140402070302c4141c0f07001c2440e204038008540382c0700b8040e00090045005c403403825018041489841d0070300b60300c42d4030b00442e0344c02405d0240401d19040c50a80c8035034031201000030394040a10418004036403001d000e502640e900c0c05001d000b904800f40140c14404a80f5420f0016901c81c0b1a2207000c60309044500e444500b0584000d281e82c1058005001ca0387c0030401da00030031500001e2488031a070780d601e07100818030800c0c80c0003900d44c02080d0140780c041c4185e6654509964024a800000124060081181003111424151644105000c1641140d032240c0816402402500102001400a00440022036030782da110744092110f04503050001e0342d80c0c6070b004100007040c1b00c0341009100ba49420051941551141d9010500211403a4400d4866 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 613315602 1250 613314352 613314379
    0xc050f0901020118051f092307050d0602180406052805040207052103070e010809070b0c0319050f0301090207060906020f0d0e01050f010506070c0b072406060e 70
    0x4d400400b0307400503003881d1060f03031100341c603080350750b24051190442c203100d5288080c0c6104206105124289420448c1880b180c1030500811511000c1300100701c8450044400201c0c594407542d8008600b00c2c440c940050f81d54011004501c000140a1010b520990030413108000c956200600c5188108602c40301c44042c038a000403031107480b0f07401c1e403103035130010b0000c2001014080086220004024100c8041d504d0007503c0c203001c45203100855400c80401c09040e04003606521540000b070784130801030201ca43c05034482d258800c40b90003a07003104803c3d1f400000c0c0750b090700f00c0360440001c109100b42481c904100c5580c02c0410140014015000140d50106032142801255009a104541c0050007155140c10010100305154000e01240065504060703000480420521416104030a008603804103642031004009003548503580958042c0e44441001c5518002c41c1c0081c0020361041e0b109124002a501c414400b46c00003014039003a02d486c10108222141d04120000583c040c111814002c2103507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 613316852 1250 613315602 613315607
    0x11119050307050702030d0e010e0a03080d0c0302090a0306090314040608060d020409020a09023f0c0705190c0611060c0c0f0a080304110319020d0c03120206190c050f0901 75
    0x1c0c542c8017a5161041c0c103884008203401038000c2e0321001082c0d95001182145e134003030088100f40c0d0303c801040f47c0b00403c114030343c40030103510039001000307a860098070386070f00c1000003444844550002d6800d542d0b1803003404101070300401c40701c00000060380c0d05800e037480c1c0440a464800001c00c1d482c050200031100b00c0c21951164000305410350300400030b0410b99200e0100038000d40003a1000240540c241c44d582031180810482070140701c00c6000700500e80480001a844400400f07031402c0c480e20300c10700202000650501401b02440c403000321401201c1d100b420a20341d010750691100c4240050585412220a400300c0c10a9002c5c1a140a0923514030b14174610030718044911940303821a003d030340c90000400c0500c030000d49c001c1d4081e610080a00c401c0b42c1c109611004206210394194042e51300f030400504003a40361040070741c00340200c0000d996990300d0b502c035124025941d050040e0081420480803400c40c41c0740d50824100e41908000301032740e40c0c1019220348243d0001088228020840b05666807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 613318102 1250 613316852 613316857
    0x9050403090914071407020d0609030e06040308091302070b041209081203090f0102030f04060b030c09150901080f150406020d020c07060801090203190203040317090a0501111905030705 81
    0x8210841084185982c07000c03c403224a09988034400120340c12281640c4e0361081056a800b150002d050f0084031002c0d90700c50000340b034400c03001c8051001c08951584c0690307a40b0080e00003503010b0380c0c403181d50f04000c404004051920806600d415441803002001180f100764803d58090f0b804140d07112641c804080546481016034000141c5200ea485841d0705c0b040d2201c00381d801480c141707044542c80550024110b00b82c2c0400c6032120084e450950000700031030300c40c0d040a44004009001d4600205604011901c5442c04039818031a100300000300c42c040c0c0c28020100c0e801458a4401b43c06202152508245c5601080039083c002c0a10800424240000b50b4101c4002c00704110b0115961030010800700d0311084580708103400710301c945000080f000c15034021248034840e10032044081a0300000104020340000d001901041700280e1000c0402e140f600e81130340500c0030000108085011843c101d4250f8054010303160411206224074080101642e0814001494500740305481c0c6d500c410b012138590 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 613319352 1250 613318102 613318109
    0x2120333120109020307090615050a0c0803070c110f090a020a0201020909090609071401050706180b0a1506051e1e0304150b10090b031b0f0406020f15010905040309 72
    0x2680e010031010081005621084205100350b0031b4490496483c006941214080d114514886405500401481d0710071001400c0f100708504003240d103040c0946526245400403110b44004c1016856040c080c810040c0203601003070300880b100d00c608800135000c40c0c0d0014001d02842800354002c01d540508038003e4064800e941ea018214450764600690410398480d0250350b1700180b4066040e000c1342001c9590000c100c80300301a1030345842c01526a8600000b880c09540c0d03540390b60030000707403440080c01d04031442d4060702000002041c0d100c82803442d4004200300e58800c505100d02006110384101d0a2000d81c007a2664048090ba1a0460601e842141c140746440d41d01a4850001c100802c01a400700b85130f541190307003e410050310710320006001c2049001c000100c080340d1413803030801c0b0307880141c0015540110400c0d4440400420b41c0030107e1650001e404c0c40c9603204000c035003407089a03030400004440e400040010000071603d099800d00c2410180609174400b61148001010f0500424889005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 613320602 1250 613319352 613319359
    0xb131e0605130509040b0601170412050702042d0c020304053601060512060f03150403020313080a02090a020f030103060504061b1206080f1225030f02120333 69
    0x50f103001d14000b0000507003240d4150118031002740240c0082245c003002c0d84903561018041c105070220340001c0c2e400c0d80103100100e0384079445001c00c5c0c500c6145035598000900d003c1600d1149001d0a00900b07040c0c4940202c002c04561042c00b08120558a0243c007140d000a10348850040c14030207070032001c030f030b944000183c03142d9114213000103070459222005200c540052044080180c0301d130410800181c205e03d135a031364154401c0030403c0000e110881c040350032034403900440e0f1901010391400980403003640d204103220381110380000258104000b1081d1300c0450560114613060400048034020300060001502040d60741b80001d0800030254422101d0b40c003503031562854902c04070070040829080070392042600d420428000395442000401d6041ca45415029042c00056020030320f486412101c005415448001d5031000703c03100009584401c2400382d6580d4108902400019150500748108002410703010070400101e40314480e04048100c04031030142142c10f48880324840d400e800c03044140d03072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 613321852 1250 613320602 613320619
    0x2270a090501030b0403030614150309070302030105010f0303020106090b03031914120411010206160f0e09010b03011a070c03030f030902041b0e030102131208040f0b131e06051305 79
    0x602451301e030705034800c0d032190b9014030416880d0380d4401d40308170b803403d489900076909142481d41d8280764005913a000b22200b003281d942999a80019080d81e070f003a07002c074507100c110307402c2413052541c28011180030b410320660900038840c19a021a13079030b00c41d00d07100011821070508023603915885540000301c07819544400d84d8881403170508869881d035054a0445074034946445026132075002241807445550f01e61080070800516042c2503550382170448490041001200002502d50b80e0a45481d001e0500308032020340f41c3d814150560207000c43c003881d0650902003488400c000483c1d6000c0c0c002980d605141c8100b025020740c0040e070103131007080030007075006080103030724002a4118400703544143c2183d50b131590a85841c01c1858200e00c60a91000540281c1d203809100d03184030b13421110f01c8a841004c4803440c0c15580c0752520301981c029040f810880c14005401c9000201415140000d013003000d1851480f00e4624a40900e1200700b44502c0b4280040441c28074556803d00300c000008003c0503010b180c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 613323102 1250 613321852 613321859
    0x61206010f260115170a021012020f0301080d0206010f0b071b15030c091d24100203070209061005031f0906030503031e1021060e0f07060302270a090501 67
    0xc41030f003442c0112104d05417801c14495110340d002030004035064000d4807503000306802d004202d0304100b080d10b5201d400e6808001c0000800040001540280500b03005000c1e02102418028188401a84a49500c079812042800a246228100c5d641c0603408002c100c2c40da82c00180c40c400d1800c50f68818440d84503404a83c80040d600741d00454a5101d4554a24030903684881c400110301c0d4802c41c9500240c00000f0000d600810480000000f98841412040704035443e40c1c0003d101803150718080005800200340c1c02c045090030b0304210740007002214401c070701501040e00140303035010080c108074420141e00141d030341c182d8000d02c4c8000036103441030007070110075100d0401c03694961041c0c2d010b02c80000020030144210180303041a5001e6018000152105031800000c40e40c8480400d0094007010002c9201d60009030240c8120100d031011a03002d0000b0b245c000325003e041c21016030201d410305004000000c90207042500c500c00140040b140320090420000124240c80c0c456004060440c3c6000c0c00071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 613324352 1250 613323102 613323131
    0xa0b0909030706360f050d09091a011b0609080406030207030206010807050d140304090203101d06031e0a0807060203010f0b1608031305070e061206010f2601 69
    0x10b0440501038801804841200b040d0144e29070b1610b10907200100e200110244a0042c1c4c036498140a4003a480d240703205c80260319040e05100302020414081040c51000300f0410005004024024416500d03e0048500b5031001070068841e6840900180041f80403c0d820400940d10106205030001061500c1f140c440328050025070211100f42c016110b07103000000c4900e000100e500698402034808101c5001d1503403070035040d0968010345010380c0000d210200300391109101a510958005008410062400040855400c031440310030345001c0c02c180c101700c55074900080810a201020000c019401c80400c0034a04001e101c032001446044009014801e20803d40c015506891500202016a41d43e9000044142c4500020340800c901d80d07084240100d000d44015650001d0640c940b1a07031549650346888c1400102e0300070000b040b00c00c41c20f0221604000f1140c0a200180c2801015654141080c1c610340c21880c1c460609000050014a00100b800b0301420400103901c000901c00c15040744c240c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 613325602 1250 613324352 613324357
    0x303051c0f0b13060302131e090309030201120209090c0322050c09010806070f08070509030f01060603050601300b1c050c090f0a110c0a110f04020915030a0b090903 72
    0x443c403c160381d076855040c00700c0d10701c54442100d40c001c1c070006141401840450240c8920310030303440c041003070040c18010320740b55004214400303100ea40d494080c1030540c03001510003d241c058400d0012320620031038105480c2e00c0748158000d2003108441d070b1a580c5402007640c002c032203020310360400d5041e5401002040400207000d04051401c6496100a07030325125032659a00cac00311401d80c009032b064480960a075018200464000c4d441d440c0c96840c1c080c86034040382c641089900400c800e607545807010016154188200c0d9003000d424030b04080c0c4d041c086140f25200e086445125841ca40118041c101c403086035a10607411002c0103442d07100e001440c138405883d1004040f0b01550700c0c0c050034021a400d440d100c00c1440c0700300200c106201170b984944281c40000d102210803400800e00c02c00000500345020010200041d104008c0100d100c500c9200744541d001c20035100354000d0703006019003406a070711402003424409441c1c441d180c0342c1d41d5844003031010300241208690840a2241403000001c1b01100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 613326852 1250 613325602 613325621
    0xb0a03060203040b0106110a0b06010207050d030f1202090a03141e060901060b070f0b1b220f080a080d09080a081510021c09030804090506030f070303090303051c0f 72
    0x4030607013581c0e030b40000b03803203800e12142007042541108094000090303040d2603d41e0008010f10448038955141d50124441c820b00c4d41702903000c81c244212181c1f0f06a84104582c1249154610640c104401d900200742040010301006110503050499200307200002c0008100812100d80c8225982154100607510342106035004203e6508107103010600746401400c54035400ea00440c2c8140d000c3c0280c54850082001402e43d0212020a640c118000c095140c0900241034865455208002d10041c0794202039070103a10800500f2001c034800c01c07a082c2c0c08159402215000802c40360380e507201c0b00079440100550900240791a0021032085031481d40200d241e44070342d64006100600003900c204110003c0d202c0150040164040ca8415001005d4031080c2d1148803a181003490880d0788a640c0c500b815001508800041582c82c010015146010000c070241c40b40310401a111843c1140c40040103c44140805400c0c444000b5483d0401425188140a4981e403030000b0003030041d83c1040c24029014001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 613328102 1250 613326852 613326863
    0x306030212012d18050d0215011a3406060501030911040f0216060e160605091504080303070e090c1617091801030302060f0105061c0b0a0306020304 65
    0x10031070303106000148241c1e020201c0707108000c41000110602421451000c5009140303040d1250210700e80c1c1e44a000d09107102910820183c000704803642c2c0000c0c42d014441118001c07541c0a20b004000384c801d060a1301d541011618085680d4902d0609451070030f0491908280301c41c0c2150614210060100414805880c8210800d1000982d250011819502c3d007030030140000642520010f803d14103940444034030b85031003401605002040c400590745040d00d90055817503d44030113a404a00806114004c50300303500000804096003444d100034841c0c05083c420a01411035491b02d200da8003030850545005124450460342d0f82c0c542910018082001000d420f070080bc1d1220105181c4d140200c251484150302c1085014002c3c0e190311965550480c4142201c02c00b07604101c0c000480d202d08001a44508120f9074100407035246190007468404001d010f003484408000051160ba40c0d01d804aa414040784503140040f0340c0400e0300d1900400040400c10f03070140e0011320000401203660041c5200d00c0c0541c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 613329352 1250 613328102 613328119
    0x18040e15010801140f160c170d1d0604030914010e040609020d2a0813020a03230c100521010f03110904030e061b0d030e011b021c03020d050703060302 66
    0xc0d500303406400090300c0b221001b41c01d0f8440440702034801c110325031400d40203c03822802101c4604920100e42c1c484580e081c00740d52640e000300602c1c5050f94443c0d0040200d0300c0180703411318090320010043c0c0018003d0115a90b490002e08240b81c2c414030003454403d00080c000c00926a55900041c000c0d40721f000c00d60b1025080c545001c0e88600c100310031102590301c2d018003503010380342140200c036042001040402000c00f080e41950158072400d078104040c500c2000500c925542091203900040540300c88c0c0300e03c56116410720700f407030740300d0030099042c2e21080c0c20026220b00d1041603451102c0da501031741e4000c58124200006240c1ca07076011041c11280124006901c00484500b809004002218003402240b03003000d105c01241001c80c010004160740303030500007110300ca142c01c45007021502078008000036101c156080d4601000e01c2941c0c0c0c41d4004600206001d05401c001079140e40c45c030681ea11944801c401d040c0d040030300070b8045602c900c00c801c008029616010101600134085400164041c4000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 613330602 1250 613329352 613329361
    0x30c09011214031c0b09240d21022803030e1015051005040e43030f0b0d0206090406260610080703110d050109030908010f0218040e1501080114 63
    0x3e0124002e001c016038003800c20114040c80c000101e14401e10035048000c41250f0008500070f128142c2d00200310030005610049c9e0b0b058003d10303004180c40b01185d00111321600d2108080c40da0781b2490307007039818280820f9a082c0c14451600b490510341b0014100c904005111230303400c43c004c00c048151001210f100412103002d1108850900681c000c440a0000040c04211181c4050000c40c062003000c4803c00340307000d040050019141c40602c03928400c200b030321b0104400785030180101d005141e00101d08100a201600000300305201030a03010b03005a01c00994218651901d8100d800603191850740409224030984200e1001600f000b003504c914003c01001c100401c800c400600111628680100006415a1901c5100c05150500c43e580415080340b68000200d0030300598031000d02a45466420070300d0180d40d2801c1d10004024008600d00c100140b8076403007540c0c0c0c0d01c45411042510300240040c03260760114035080b07500d2b40f5818000190320000441e014150464a401840991140706d036454 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 613331852 1250 613330602 613330609
    0xe01020702060301050d0f15020d05070e090a0f06050d050c1017011e0f080606150a120203090a08121e010311040c091e08010605030c09011214031c0b 66
    0x10940d0080d803000040004000310304e800ca01c150700c2c1c5030050420f01288115a952003440404504281c0280e80d004944c40740101e01314401c6560101c8241046821950700d04005650301c10000c1c580d18040c5e81c1c640030000c4440704c030381c0044042e00010b003009421240c0c42c01e041d642c07981484145440b40c3e0700790300403030b1364144174036101c3c007100e42028001d01840e402c02002d1560408108440c05411415800014915008512050040450703d0280005050034800c1c0070071250139072200c2c1003800b0104140141c00d0b44c410a800d50420b00f031031005840b91507801d44e46003032400d100006090a00042204203840001c030004501074000b901c0d4105203100b10368400920b1200900c0090000d00d0300d2504081d42e400d182d0841001076800c0d14090074030507210654813101400f100200032000309884002c3c806441d092040230090182107006040d4807400300000760307100310140a8020482c2004403510f080008180040c4d4400403180103482d00c40d280d800c01003405082504c008207400d400d2806403615803c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 613333102 1250 613331852 613331857
    0x120306080106290702220b040501150206130503040b0a120504230706080121051b03070b0f0306041509020f09090c0a17090a051005040c080d12111216030e0102 70
    0x203901905901900740c6d40d044040e0450010340503403400c25105c15042d00280c0e80c6214007806494202400c0c2c0c08011740c0c1e00b0003803a1003030040c200e09070501e4006020010075030000556013120040c0303c103140c0c1c4060468080340c082d407920900064650071b00050008100c030304000818400c0c12407004205511f20741c08415034448040c411000030400c01d1006210041d4001c9040704d1800340b074010754030a4441e59840f07130b00e400d01d0200b03240c160004000c00100540703800c1c09204010030400c1106400c000340721f0304145c86844090302652096a98003c11802030590f080150b0060050150854480c48410b000c80d030507511031480c0a02c6080c103140002c5510401384161010740d0026640d55000c1c1824800340c40314404050f00303007401c9201f000e07101340000328200001040095440c1010415043c0f51034140c14020035904006e04a8011440b03907507916901001480503a0a8480041401124680403c429106400c01105e42141d20000c00920500b810309003196a0000e60701003003403406400c0701038202e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 613334352 1250 613333102 613333117
    0x91005090c131809140717210705011b05030907090c0f030e0c030a03050c010c020106060f051c021b2109131805150609040b0412030608010629 63
    0x2a20380b5005119012082c6004440b18041480c000365080107603da050300c48580248007043c139404903100384104540880140d9a1804903c01030a5200204005035640d0105ca948118218404503d81c41800f00940005045032040744c00d0144805c034032200100141d2046030b00341d14620800f04000746c000700e18810010014445d585905000d0042d1804401605001044d0301d41442000340c21b0034240d400744117000c803491003512569910302e1294107060030b44a10020420542e45000410458150807041040244140e031a10990b0f0b0302185050051480207103603860200352001c641d2500f1108654000032004040b05c0440e00c0c14171180003131407403c0403520405100030505000001440c280024060705d00c0b01340399000b0500d188500000b03e115992103d003601c880c0d1154440b9480c100e1b1100406400c078600352440005450b1076150031803181c8016000400c000c4028441c900e80902c0395000b00041c14141c8000e01c0016600c03041f4450140d00d4010a07007a1002c03030740c01d8880012080f0308a5004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 613335602 1250 613334352 613334377
    0x806010c080f0c0a060203090109031202211e04030c05010f061401120b060304030e1009150522090c1106160507290103201e0f091005090c 61
    0xc0c1003072a200c0186a4101c280c81c140f15204042103400064075600142d48514100c0740002250032090800800000141010401d541c0c410060780c1c05540a2188611070602d10701c4a500c099203a140622410031500010362507184685020710040560183c900000180500000e011202801100b00d0480d070f030512605020740d200494490039540507004081e2511018a40000d0324058800401e80d03070790048408034001550140340000910340760700320849004441c9840c40d43c1b2400c0c0f0310f102c15610003070000700092220101d81c0c031110401e0b42141032980c8003030050100409603030340031350405001509141d001003080720404180c2c80e0070001d4103c0c49030080c9018a84600c040035001d032400d40c0540030030340c0d580c46040406e1202e040440c8002d00d24007220055480c0719851800c168040e840030382c071141012404142c404150395140305000c11804044c0c024404803c1212001416040c041c503841c5030811210710400060f40c460fa503a41c02250340958241d940b80d501c26140d0b40443c4541200c0416 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 613336852 1250 613335602 613335607
    0x30706080601090e0a231608060f10020f07120203191b0b07030207050607030804120509030f0102270619020c06041e050a080d0507050a081204030806010c08 69
    0xa254400c0c40c00641005060420390f07a426112100540c104e1000c40d15500d600e629201e014407481c14810800c800d541280c025040141000251141c040300603803103d80405c2940c0020500395658281180c408110040040310032140181c40030351505100c20040f0071030b010f45040014413900201e0466200c0b50b001780903040008140c1d0406e45007919204c2c050f5112401c0c66048a0042d00035003e040203041001c00140d25881c807031034000e02d88106030b003000d8040c03002441100700207600000c17500e811680c0034102e107105881d0143c086882e800360800c0c0d00d44c90711039a000744005000660051101040502c08200724000c03c03e00d0300a1095400d10294011000300080c1c24800c2d0702c100b2001d0300d203140b4415940c0b04a070030700c000340290b0015044110340b40111450b415640307942e030882000800d426600011414507080324182c03904826082034090040010b04002001800d00c066070202c2d600c480d41a440d144040104501c0d10821141107022840c0c2c04003141040d0300840d980c005082e4045441807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 613338102 1250 613336852 613336859
    0x903040308031f08060f0106210902040e0d050c060603010504081605160308030a0506030109030e01030903050d0608030408151009091b03030216061704060c090909050309010e0f0307 80
    0xc14540c0010000c0500307103040002241581007501c0140300500602c4c008004900f840c1c40024000d41069110000b806088a13007014016030b9031002000b000380d0b4140001e08290140003042c090081ca410b07010290145151070225560400c000d0f01c0161111000c80d1110b544801c02c0c18200d90003954054050601070004c503d0085101940640c00349c80386050712102e54201d507482c0c01956080d042242c4601c808410042490784601c51399074820000c500a001c5030400d41c401501c1a000680342904040d12a0f580b1401d2601078000c40d00710601c1c3c00d104201459651481701c3c2c0b030350400e00a00701e0b503005100c0a0783c04040b4410340d8900544d92100d001075407524000705200244103440040341c0311002d1a10b0794007525401803410300118000d80103031240d1080c0b2202c0e0000c96a258201d502071100c00c08501000d1581322a2150b0702642c0002c001030031152282c0c0c25075070302d0115404894041e040100c4041082800b01c00f500800c10281c03a40c0d0700e080441070800140e5042568070b541c040d481280200b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 613339352 1250 613338102 613338113
    0x80f040f0c08331b040305030403300e10110619050c03040c0e07030b1906030e030408030d020a0e1002010204030204060501030e030d050a1b030b03071721040b0a1205090609030403 79
    0x400d04c80799400512490183d503a036800741190401c0d841512213658862981d28600c0700b0101c01e040411412000d001300c0c40c2000000b410301c03400400644e026002c41205c0d03221280c0920309121401550000301ca64600c0c049402c05c0c01c0c01e000150651003a0305000c0030031141e505001c2520302032036000040034907580c04c00080340d01f92400201000c04040c0c41d00c0d10520700d40c0ba603401c00800f013424906000c0c0c945040050240c1540c03031013655400c19502c10802003040e92004000d407000740034405009a036840035444103c686814000c00581e110030b0402c0072401c81a015030080003124826101407110781d641d280107404070340300c0041c8840c0c25082044004483d555940c89554800030b0642c0c00952181049100049010310400d00f0740801d80d14092010b03646010803101000744420090074280d01c4850140301d8850041011442108442c0f5080e0380d600c81f4a481a240070300300c001d07046031b12005102002800300e46440303200e1400501d008003050041c0c20105003944100000ca00462509255a4070b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 613340602 1250 613339352 613339381
    0x6080c0903101d0714010c030e12190506060a03031d18011d01090203070e101b03051803120414010903050105010807051e01080f040f0c0833 62
    0xa19505014031800d0190307403800343c81440d1041010004020040341e042044518201c0e407030308500780c01d004c0c941004005031780c4802809541035051402d020030b4514a408074403403c50300450b1509500810705d428034620652400e1400d0075000340100d410544541d03080c440c80c19054040940000c0c00030080041441c007104603120200c00242074402884a40d01803400d0f550400c1c1c01480b003400017010030491100c1d0362043e41b03002d005000011491410700c00b001600c10656001d9213805035a0002464107018003c5400307541000284c44207007011265031400030100c1d07104200c04c4175442041125001c4074200040c800305000359003030200b8a03007400c100d100640c8030080e000300c60411032580c0020000880a020707450080c89904010902c0c1420041006911065401020720001e004240401603030307441050305070000c0890507030899a46550030b0880c00c0303941d681000762052101050004400200240b003c1464400d42241d038100c00341c0440d105003201c224100b840126140401240d500100c102d003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 613341852 1250 613340602 613340617
    0x2030f16060315030314090d11040606030605130b03071e0f150c03030218130504030206061f050d02071b06020f010c120b0f0a0801020403033b030c120a02100906080c 73
    0x8002d410480d47c100040c0418007100c1c42102e080b03991000246213130525014010180005080603c103003401d04010844254804941111940c1c6903000f4042646060091002030b0452600002e0080c01c108441d411130600f501c02c003e020f81038900002000c0d801d50449003251752260b5503003000ba041e40d840c201c01030340148607540314018119003000f102d907480c031501030050190036001061070300c0c041c10040e0404800a1031180201f00003d102901c16074079800d020019146410115150750408041000a0141950040040601d080f01c07049802086040e10b040302e5050382140c14448080b4203443c20303100b40704e01240100e4450784001d418002d15410004050780080c183d10940011240061101c802603404600140d500040510506601500f01400f404595440801031440f4107a111800410445265050206040001550790781840380c9800d01500900c0f207103003890144440c584421102c10201d1203520101160940b180c081e60702d032811210b0380c2d00c854001c0d503517803028441c95a02000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 613343102 1250 613341852 613341887
    0x3050a030509120a11010e06012d12150b0f0f0d15110c0d0311040e070905030d1205062704060905010c0509040b01141605070302030f160603150303 65
    0x10308651410340c4003005403007001c800d50b0b103170a44000003900d250300311181d1b005450f41541106006002e440b1103101c0c1c400b140321012410400302e04404254944650690300004000e403800d000e2042400007030521070300c9640090724200a060903180400c01041d61210105401c50f0814101d20400d141c074010402006014070000015940e540c2c0c01d05040310368081001140d0400800c040100c0d0000b04602d03030440203d82400c1002000c521001242d6016911401d940b80c124100007415261103001c0310703001040301500322070104059200280c044422241d071041102d1802001035842d1801006440f80c03004610105095444e840b40700b0580c40800410943e990798031084000001f0b0740900c50842489002d070b41d200d444103481400c0209450203c1002c0c0e042040140c20216601ba0f42d80c101c506518100b0070001140c80b06180850030021142d0002e1743c5802034090045c42a0004a071607036510308180303401650b050b12883c0c15422241165610302c60329002043c18030020f400787c0c2110250a0a09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 613344352 1250 613343102 613343113
    0x19020f1201020919030539010201150f060e1503070f0507080301030c0513150509090f0709022113030503060f091302010816050717040305030f0415050703050a030509 73
    0x41e000c2460135400c0110700c84e08030984041001400300c140060403110504150300107004144180c4965081020101c1c090090202d08072100603038002d50100000b0f46c0615404240c1d170381e4a4541d100d044c001317480317544042348481e21420614501807401c0801c0c000450031590564603403500c11210221000c0c004803d0080801540300440c6020010b14001e600ca9000d6445c10307402c010a01c448508501c03030040f05607007020315008505040ca0000c0c0155181581c44d00250f07a100d0030050301d40724000c00424210301542c840803c0c45581c1d6002000b1a040c2c540c00384044100c2d56000d464540021560300e40e1411940382d40d000040d2180000350341240c0e0040c480301600900500080103900241c40200031300c1e01d400d000c01d00310350b0003414442d4008402449061308003601c450241c914410844003d112110640945518112a400791030245400004898441d000700c0400410741d4843d0003a081e50707101410b031072460684a64115000598181e841c03034140700d001d81c415005408040c0103a815802003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 613345602 1250 613344352 613344367
    0x9031209180114030c04050705031302130603060e0f0a0206160204021c0e1209010f0809151303180f0b0903010e010f23010b030103030f1101050103030905010219020f120102 76
    0xc03440d4403806841000043c2141902207010140b811082c0c1000302e00660030300e070401110a40240c1a01c3d03001410f003884480f14030382440014040c00490b00e0f02483e03d4075042c40441440807030b0f40040c0c641507040c002c884107a041540c0040e560844200025841a400c1280001c621102e010611050b840038001506100c03036004495110040d40c0507044e081644d410300320301d0002c4204804400b014407000e034035103042d554200003000c0b900113001c0e41c000d1060141c045032203ea01008888407441500c091b07984281821a8041001e0861200a60009070b040c00e03403145412000001d42c003142c20019072000481d10309444804990440d04800b507040d5600d0400115004080c09104143d4000c0c4400040c1c0d0401c0700c4560381b44801c4004020b050389030480061280c1d1810030100c80c15130380c05050042030900611412107240640c8220404a9400c250000080540000407030b000c0e51426026204200e494011607501c401300800d010b54441c2c7c2400ca40da07114140200d001605106640004d40340a00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 613346852 1250 613345602 613345639
    0x11e05040c0f0e1503070c110d0b040c09020a020d120b1203030619051003090f061119032a020304050414090105010e01030f0201030203100e1305011109031209 70
    0x541d00100790200d00c2615103104115030001ca11000860203c0300c0c0c0520030b9190f405007001d800020555802e120045440b1014050314101c200c1003070710010310320b4a8029085c40d21303c12081f01540c0807900c000c404280494010200d00a8406580c00c641c0140010070180400302da413902c01d9031840c48072070ba6400e8004611717116510080c440c4815000110ba581c01c0000c14080600c0e1801524003034400d9204091205640717410642e110b5050038940420381134080d08250304448000500200501c0c9090925a401d194050280c03141c081420031481d04001c0d01c40065080e59500442e246d0302c1154441e4800d1015850405042c0c0000d0300e1044904158554002c0750441d41107441c0314903540300000400c4060482400741a014000d100f4800c0a1945180c0d20421554081d810090602d40c010002400d028087d18054005003071000f14500142040d10a9401030281b04d401a1859401e2400321585245003c044500ca124041c004011000843c0c515109a41007501010751118826450810301348 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 613348102 1250 613346852 613346861
    0x1e0c010c02061204030918090206030c0f1909051504120212010f0c051b01230603010207060507030209100f050906180301020708040806010603061202060d0920010806120303011e0504 80
    0x18880d46403203c18a080020584111f1a080250000c4078100760740240140c5459090300e4020102d0086a82c4a0519010309000c038018949150603401c15082c40e1807881d80e0041d032490454100f6610340044101c02d64242c285403181e40280e60070310307403200801801801c200f00483c0b021132564000107400408604900c00307507210500743e1000103402140980300019005c0350301065845620003007002303900000d074a180080c184200b0b25043c218010000c1c40760748003034044602503507008404001e0752910380d00140c000d41080310824000d0300d0b1080904401802280c0f2000300c110b0644940381800b400c042008016485110102035813040620b021800303072800d001170181d151040419540f594185043c1d00c1c9412016445042011b0420701c080040c0845040501c000c590190b8800390b441140380c0160000c4c00080c100200b029060300880b00101d060b5031a04c0b0341c0d4040076070b1810001d84a0000f040681040142c14000a42003000108082d0100d103201551035070a4520b42000140d4850003c1c0889 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 613349352 1250 613348102 613348111
    0xf021215030f100b091617070e0306043005040513060f0e06030d021b10031e150f0509070c0f080301030c0611011a151308010b031e0c010c020612 64
    0x65851340002101032a240c5505a8005a00201d101007000759800091030741b100e8500e000314281d00c5c0b601050b952481070414003400000a800c070b0b0a142001d281201d1651102c40306003844030300c41007806e103809541c544a5a940c3d1003a540d603034101418075003000401c042060b00700648694804000a207440d100b000d44008081041c1480c17158074109043c103040400290007201150400088103c00d851141c2c1e0840c030642094035101814012280700760010100c12580c0301d4020301320b82950000b40d009801613030070310184e64096510680e40340100b0785141414003030340e03920110010008009501c50340484030003601588916200e21915140c4840311381c02030308142d8450641c01e00134419981c1243c880c0c0c1d54060341c48002c00041954150103075040101c114140c1c0304002401d84500a0f011800030f8a030300d10250b0303000e100f134555218a00c50003042c40c00d030194000d00070990000326402d1541803500c030455252025001403003140004403012100020202c1c0d2109050010403105529581480d208 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 613350602 1250 613349352 613349383
    0x20414060f010807081314010f15050105120a02070813060203090f010c03020613140111120109060317090102101b030e0708032b021603030f021215030f 67
    0x581032400a005408414001003418820501c040c48095a8008150f40d44042074411544076000d09181804500034404c10000c025800e10044010f42c41c1281c0c44240c0c0c1900403020300440c903550320b0064031940603d022444544040c400000ea604060741c004043ca1441841c1c85460b01400103412455510140c00460043c3d00c08100100380c0d0615443c0e12540c2407003401e00c0301c1000b005540c003e6855200600c48a411000e04008104204040d1030301d40c3e1800c03240000b40160300b905032901b041500704640070b0701004102000000c800c1c40903c686402d40e500701a407072862030200d03d1408103130380c4000541da0451007200c81000d0102440d109040800c10700000d8091081c920740310041c103a5502d00c50a4009030480c02e41084600c40c0002100c4490418011b0034207542100602035189102c101c01c620005400082c2a04501488441d840c1186100e5201085100702d4903680740200e02070655814680c0800b600031a400c0c01c8aa0742382d21070703000300904580c80180784069003401e1050311140d440c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 613351852 1250 613350602 613350641
    0xf0611011d0d0e1f0c03020f011b0210050105030c1e04020d0204152d1b060204030b07140a050d0b040911040f09020901050118080a0c15110a080a0c0204 67
    0x1560342c01503156032001c00444005540c80c850b2a81d000c1410132000c0814140300319144000c08040c02803200c0301c064560f440013000406000d1030f6040514080743d10040c014040d449404d040790b941441254141c400140040c80c0070301ca41d1080c04500c007100002e50031120342411024040e0387d82e5000401da00620088056141e40c43c01c5500c40d2000c0a5800715014481380c0403001c0880d51942c1300316109612004621034080071020010342c7c0b400e60750400c07081112042540c550610555070000c0049034481c170301e00f0300280d40b0054112807100c0138503a0078200d8241003004568091007070000d48840860b00d00c0009175406100c0016048960700002100c4120707100301013882c00e00c2d0a1040d6951111500710501030310545600240208105001d0b01d414010103641810090011510300320160000070300320b4904040300d09000e00301034803030710403030b04010303900d40c0050411407207102018804410503005060820080d41c4006090308888420130800c090303403003000c0c050b03a2030307020385121050220440003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 613353102 1250 613351852 613351873
    0x40306060e04021005031003080403050309011e08070f0306051002010c080610050d0c030902030607030b090105011b061d030412110d0f0303050c070602030915100f0611011d 76
    0x10344030981c1c001981c1c40310031010030001d44c441c51414846141c0d1403400c641c0e25a110380c0c48058500068201600c00383c4007280200402c81c00000804c03640009803241d01c0015200c50440c058000300302860800192a5000304040138015110b20000b0451800c0115170740352501c0228180b40715044280b00140c2d1600100405135401c21000d50b000314068483c0801401d0540c0050000c0c400c4103a904001c5544505006201e0711070b034000e0307412907030007025200b281c18000f200071b0203060402c3c0301c544200c0c0c3c00743c00000c0300d6002c4e0100041095040d2160140030315030b621241d0042c58040c0c44000701420142c6000c01000081c03008001074a0241e803400a9211903062451302082c40003d030720302a451202d603203404640d00c07402054119a151134040361965441d00120300502641d80004c02c05400031050200300640070600b500c81541450303030700c3c0c1c0603600c0d0141020b0410140c030442c41154840c3d8014000d0621401500c2c019010020000c5101e907114520790000908607540c80e07005030080324a08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 613354352 1250 613353102 613353113
    0x1e1d07020a02150d0606030b06070f050a06060b03090c0301020307080f250302181207120303091703010303030c08270c09090d11070b16020415090f0b0405040c03023001020403 77
    0x10001d000e05180c10001c4a0307031640809d000e4400d00d140588441d4160248404010040024114107607100100340711695403000d243c502904240c1d02e400060081c110041d240b42014402d813486002c4be541c070700301716480380001e248078030f48060300b015810207110004028286600700c0d482000007440c2d800580e505200514980d80348003051003684a411401654a8000d50015111302910b0305582e06050884003072409800070554040002c00022008500c03111075130340640550f040741d000e91003d11642c400b1200445940d68101c510054402040744500740b03810200e410034184c0e002d8042150000b0040c800041c40c000341c2201c02c000160b00c601d0003080000e40c0103266143c010385080081c03090b0380c02d11001500900170302407800170f040d11850740384041d5500c98010010000c021080803620548581e1ba82000d0b142c40007211f030703da5040017640200f03401d00f841aa4031940e0065402c080050030b41c1d00700003070300400041e0803032143d2944501a58142c1c0012514119418840006a40d1441c40c58503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 613355602 1250 613354352 613354361
    0x219020313050a030f1b0f0902090a060f0c170909090303011508070f0305060402040302100c06180c051507080c061012050c240a02071e1d07020a02150d 67
    0xaa000d42c1844000300001101c2c144848045e42d4032481d41005100c501c42c00075a001e43d142c3c080c200c0d00c00900c00c005401d40640d130060240403015900b840c88a40c403014180d8040039051a0500050540045030b8041441040040c0201d20b8140c0c02920304040c4400150000809807101040c9400010041200c0864500ea001003001142013003c0c80f0301d001724000c0c12a258a0f00fa40e010300d130326180018000e90315030381103a01840e030017000b040e015841100010302c0c818003040100c0d4000d241c02c8200c1c8918a060125100b190343c4414503016160810092180380405205c0e9100a00001d00c80c02c00040d03071150142c403038444444014110341c0303060f07100d480320840c5c1a4441100c02d600c0d802c00d040400c401054002e00d000082d104040c41c2031002140540400e02461551030040b0081107034003555502254801c21501e05c0003e607442c0d5540c803010f01c4400422440740c0075003100344c00c58000340f030003044240d40d51010480c01a034000c201550082040c12601504910741482c0001d04c003805504035208 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 613356852 1250 613355602 613355609
    0x31005090d0306060807030e21070303050609010f060e040b04090503070512160f0215030106020c030c061201050d03030902090709030b09430605040f0e0405070e06040219020313 78
    0x2c0c203001079464524041d19110001c0c21503c01c054840d0361958818000b005201c0403070118202040e030000204a00561a4100780300c00c6002a0401c404900300d85044107016050b80c000048000c1e20710720b0b15005031030081854900681158540c40001d00c1641e482c411f100031076009001a40ea2038441c0e241050424034000c0c88400c03e80c5091080903100e03010000d21440c0252710209604140c0e1840c00059407101459040041e8241d0010011a0503903000c0743c0d559a008064080712441c480701c0f01001501c1c0105030340c0e40b42c600081001040545401020b000e40741e80241000070394603003541c021030310034a0100d070280041a4844e0f8100104044e02560030340c802c2d568000f804003189000706c600595510150f1400c13041d402c00c100c81007840c1040034094410340b240c2142e0040599500e0001c0c08a800c2031140800040303411500081d070000c851a418408c03548000900302d21410500d140b14900b1000d0040c0e81c01540c00e00003044080700c00c5680c1544400140c0045403184041c16406d420407580b81c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 613358102 1250 613356852 613356857
    0x8160605070312020f07050f011d0a02031203060d170304020f091023030604050c01020c06040f050d080c011419020a020303040602031f180606080601081303020309031005090d 77
    0x401000441e6000025004140f074148025a803017000f81120b0065002e82d0706c0180c200e01488692010700c0740305612200d0300c50a0f440718440b00d001010203d64580506010194050b000007001800b4110b0300300045a0100c030041000100040ca610342d0151a1035100740c269140c6000002e2109500e004920000100021603400300240b51940300740c00199010f209008441c00b84000c1e10204080005d1040684100034080303c0b524606070502c103588240c2e04506034054024011000e03107604294048a041e22283c414500f40700d480d24040c0024125444000d44080c003042c0030b050138206084c0a540d07102070150074544014100012100c0c04456401c0c3c0070714034140b0402000b408641c01000341d90b400f0380c0110005880e581d80022800ca111507000800c0b03484085858040f80300306480f41600c9030100e4803503007001000d444131001c0c1c5035038009a0380c06011646440001b1606a0306041040f105440303071043e01d04100215012034079014402021150064131141080403421381005031200b0b0b41e6a61 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 613359352 1250 613358102 613358107
    0x3061e080105060907020d0e032a0411130e1009020408010c03051006140f040801090f0b0718032603090c010e270907031a0f130203100f0e01020408160605 68
    0x1700f01958400e01d880f600e03028004803000d68480d65605100040c0c1024200022246001121030f46400c6a44400d00040c4a50b00c0d110300728101c841d040c8151207110860515074183c090822555520080700200300340d071b50440da80d0300440d0100d081d00103400140000c0001069091500c00050141c030002010071403090240c201c10460568010308003001141c1460036695201000ca052450307d1182d85c01c45221036080600d142c0401a8000c010142079018200352019038481030411100c1c5d0b0385070382e080324580810107406d0006c600d4011030004418210f280c02050104072064038002508111289503e503040840300a2440d604001c0103800400112403031025448a040c0c00f201150b96a85140c3c240d0b440381e0300240c41070908000c12406140c200160034000d0034900c0d254400c0d41c400300e4103814401d40c1b41010800c0b55015204a5640c070344c1c001c002e00980c80c10403c0b440020030092040002998840841c12507440b028401040903040540241010b011410300388103030410039510650810904 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 613360602 1250 613359352 613359361
    0x14090a1e05070815091603020d1b0206250813051606020c01050322080c0307080409110c1e011811040e0609060106030213030b072705030a080a03061e0801050609 71
    0x2090b0000b588107504025503c2600c1c00103a04800034000d031440205164a00303140070b5201c040ac4510302042a903903908561803561003600d5507200010328016540c0075040003082c1c0100c2c1d4010082c01c4d03800603246400004486868480d1843c124420b005200e60018041e0144546607043c425011081070a0901a10350304220131001c0174200c6c1803145003e4818034481007000c0180f0403084410baa890901166240c01e5142080392903035116118500e0040d03d0b08800000315262503055600501700c0401415119801e40240b04801e903240b0b4640c1c1065680e0119014640c28441949021500511440140546645c203020480c2c501c10400480d030f038440402c01c06400e80009649064440ea441c0258944160514100c0c01d10340c40d030002415180054200702d65283e01c070507861488600008404510040d100e1850a1254240185501500716014030b10102d69900e00400d041d000c1c510300020040e07035440c1d421028030400d60849907005540700c0c0030014441c0902a0603080b80f070455542c0440d041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 613361852 1250 613360602 613360609
    0x1505072f010e03191103160e100506030f1503010c12150e01030f051002160309060e01121a0306040302061801050708061002100203090a060608030414090a1e05070815 73
    0x288a12045845503c0d80c400402804660542d0617860280494202049a00b2101c80c0c1350100d001b021011012403000410036546c0b4114a001c90300c024185034a540c031894450548124002c20141000f401c0713902081a0b84c40074400c403001c2c100c156962100c00c101d14159503040e41c42c541440c40c0440b11325541407040800380e46403941141d41c8008540400a90340c50030600305042415030442c0c092011840200c50000688020b00c118441c1c0c0e1501715040d110311041d00c0a0049050403070000381c0d900e041800c0c5111960060102205110b02c886094144400180c60502e040b2002c4005800c00c070f05002440340001c1c0740c0d003018040b010090115143c5540d008026410040c01c03a84120914580040340c3c500071b000f0401000100c01c829585d070310f0405032455541c0404102200c0d840c0c036001c00003c91003404401e4901341c40038580c901d00306800700410400348940c05000308807510f990342c52039420420041d600c0c01c0110100304012440c1e1800c044094008140241480c1c2802d5820490202c40d69 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 613363102 1250 613361852 613361863
    0x3050c0d05070b1b0a1a0907060806040c030908030a090b0f0402060d05060105070c0f0812040b040302010f110118301b0b010f03060606050a091505072f010e03 70
    0x29043c8500c1601c0e10740408814103c000c43e4400800c031400364410704c10a01225500440d01c4590b4503003181e68030f8807030b01100e50756098107200e8000019040008222249801d8110340c0001c007081c503010a07000c1507508c0e0f500786035000b920600328082c2d844004a0030481c0c03103640386601c0ba9001102112a03e0207802040e0305200700114035607229580e00003c1c1172a0300410507124203d81050b5078860315a129039a10560a84501076983c66214584801c040072108c1400c0743c098502418140d400c2c1442c540c01590381c1d5140d5400501804005206010110800d206411049550510014100c98103060501d10300c18051489058216040000c3e41c0d010482c0494030180706103480c00014200c22090003c106064440b0000c09130703213842000040c208081d000355007d89000d4402085825955107094506101391500c2401080550408011041540340480a00d5145040151611034165034003200d030806e001d00d51510001c82c481c3c150020303070700c1480c0c0c0c01d02540c2800c2100306540d5900000c0d60301e5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 613364352 1250 613363102 613363109
    0x5100c05030f2a010f0b040204050328120804060605040203040803061201020c1516020106051305090106181b0e0105070b1302090f0f13080f0919060903050c0d0507 72
    0x10040061032036400100446040f000c41d60f42c140007540200741c1c540e07840c06000d4102644810038188030312000146024400c42e402c4400040042079503407840c030001d801c00d0390078140c02c81c0d4000301c0814110100e0700e15250084820320542e240c10883c0382c2460441d003118a06d8209074043e41c414030400c00060380744011260040011a03981080d03a1016500e21301a1080500240c0640100903140d1202c60540d040d442c0101440100c0700b8462203840f404174200ca50340d00c211a407240034800885400ea400364040390700300c03071280000b080c202e8a400c480600940c3d41410900070ba40d03181c62001d041c189020342e0407001420307482d0180c00301e0003800c0001d1017070041500242c581e44104000c1100b81c800c1164102a59034060002d81c494a0a80b0100ca06001300302c0d0700240305807215000034006070560800780c0c521544100011b0034486a00744502e25034121000b4240c10007060002c0102e0071004481d054014013269031803509090841c0303066400c10311034106642c0600c0741440c0c8000040e0020500b0803da = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 613365602 1250 613364352 613364377
    0x3130510092a1517011d010626010b07260307140403050a0308010810050405030a0c0609020909030310090e0714010507140d09060f09091a06031005100c0503 69
    0x901c2c400d140079000d099680c066145030000702e80141c4050741140f44242030203c60500310510340c1c0c3e00d4a404400303081030405081d40b068080018040f141c0901010305070101400c034905800f141441e100d2a04a00a801c10030106030081a01d100300108407102051203000508c490814000840050307486000190440040c49070744050b520000d0901c1054400868000c1c0c2210101c40050901910a050a0040c0e4038540520003804800c0f19042c040d1034040c9900100540c42c28248003401c031802144401e040b6102a00d448150340542c0d107800c0e10600981a8602460f580e05040015501e0440c2c0766006140c120304040007130030b0110021680000712900051180010013400004a8251040d818024460b05480b103060351410000038400302c0a00064880e483e6164640901340c0d40380a42d04910030014452000030301641d1103039000344961580503c11200c0c43e00340c440c006002c54008658503c9204404030707042190b454038010401500c0da8500344018080d0301e0b0b4031419124801e0500c500c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 613366852 1250 613365602 613365653
    0x51e030703030818030310060f0507080405010e0604080f010b01031512080705010e031c1401030b061203040b0a080603060c0403030c11030304180c03050c0306030a06050c0f0313051009 81
    0x80d4006041101d070508072240045c0d031750341d2074410507000034200240129000144011442e800c4207014000b103d40f21600328102d64107052400c4011100b1003101c051071a00180b00740800034991070b0401130701e03420f03039038000005c2846c1003204001012a4500c89207850001800e207001c0100d00c0b41f9071103241c82140c0100c8207650381c20407410708078090801601801c5261000041420b1004d195001c921260b2001840900000f282c2a0171040341450a003c094004920140402c2151030880801d200c20303107604080d81d06040c1d403400f0001040c0c100c14100004544181d0812003145000d0219a61201d07483c1d411501f0241181c038003c205c40d07039200d0010500000c140c401681e13650100b05880042c01c0007100d009524445142c0040070303184105e54000801d00f00f03c0440e5008160b01d055038807803007014006100b220410380b90f240203068090f0144507041c030104401c040520070000114400d940d0a0600c54245800e46030051038400644041c0c4207080c900120400082d403071824848440c44102c42070b44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 613368102 1250 613366852 613366861
    0x13060309050a0209040b0106110718020703090503030319050108060f0c1b060109020a030c0309080a0c031704060203011a0309070311190810061707061b0f0c051e0307030308 76
    0x5240407002c440107548201c8440c2000704101c40e01407039034181e50841d542d90806140d941700362641d07150340b8003440540c5405519a0b4800f43e07190b6014100b1280a4508001f0640d5598080313400c40c1e00946800700c04c102103904e4110403400c01d024642c010090350f4010100c62401416001c2c0814000c0e00550390f0310301c0080d28800701c800502e081e10084400c0030580f661075a40340e003200000e40c4140c1442c004a410110f4007000c0d103000340705010178031f40c109003100c0c031308200c40ca0226071001c0e1415003281405038500e40c00c241c07080c20342c0c1001c0c400c078441c030340050b600c2d4105102040c84442581c0c210040100400410030700f20070100e50001200d074002000a02030f13035441f001030306c041101c1c0d8542e4003003e40c450703002486120000c0d0b05c2100d01100c550402c03480307444400c1d980c1401514031042e13002d9031144100f00102c0d07101f400c4d04a042c0980d422a0b0305d50034501e07550044c00300304510056800c803801b1075090082c0d00e0008000c0746200d0030b08541c043c1c14481c0030080381c1c9a207000e1001a042c0140000002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 613369352 1250 613368102 613368113
    0x290a0c0503040e0a02030403030b04140606031f03050a05070e0c070609150906051005010f14180d212c011e0c0b0a1e0b0f04060b0702011413060309 65
    0x10b4025048007858100c0034a0904c402d54001d4208440c02c1e00000e0030000300c07020b2414644100e131840b00014845400c540e0390441800b1250780080d00510102c03c91948503600100c200070f99038051031060000c2c090b9100310307044c680d1400700c240c0c0000260100007010701c15442492400c45030314681c84840030400d0340d0b2a06011401110324056000a141420f04903000c000840c1d01961081d140c8040c45012a80c840004451102c059440280492610070644210740120f0707002d00030b81d114a541d6603d01e42c2d12800401c0d0b002c40c00440c103c920750f40703121039103010300c48406a4000d501d40340e1510012441988031070104440a4045a0102c001c00c08031442082e44541040380d010f0090458503001600705074402007001184040c151414021500410103200076801600005113000203114008a203000210005010796088550300c4403501c205c40f445c54649000e080b004203800f07090183c4501c5e484c0005408181100b80c0640c2c500c0d4104280603407100c0d18525002506c12900e4001081c0d01d492510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 613370602 1250 613369352 613369357
    0x19060e03090d0318230609030a02060703081e1501051e130509160e280f05011b030f0c021903060618060303090608091510290a0c0503 59
    0x11074200a010b2001814543c219081d2074929000d09251078070143d03a403039554840c00e03049001004020500c103000803249440c5015054459008066513222905940082c1d07055014450440c04030b80000200584e00e000030994510b00c01000342130001d9894243e6400b4040d14184044505201d0003003815251180310900d010b65809c855142035a48000003c00d108604403244682072050450400140c4014402e00005480e1125034440400c03200d1040100a40070030300d0001ca501e090501070741d4403c0000518204401043c03c0341d40200d88038100b400060600b0304402c10146c410419282040c0020b130300c92401075038040c140ca032540c181c041074400600724107103051102e0041002c159010007408142e80c032540460300c5c84000c4d0840300c18420002c0c030a664140c4070107404105946001c00c0030701d0113204c0d19613200c501c40040d1841e10303507007150342120b07208242c03451825200018010700c0400700500545101446101000040c182501303500c1c0d120344107042d0035400b003020604400e4200b0008209 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 613371852 1250 613370602 613370617
    0x1e0d08012102101e030e0f1204090903140a0903060b03060f040b0c070c0305060a0501210f02040b03032236020f072f13092117070219060e03 62
    0x3010481028000074051b20700442c29039a5801150301d4200c407450001101020081d000232000e08144c908a5000000c001c0010241c0030701100841607001c0201c0b00000f0800d0b10015264504190305506140741113849140b20329020358000341c03d01000c09040c580d0140c2c06940b001580744540d0b40c10108142c24060754034014407583d4050404000c0050120320a403050b0943c83d000c10080e0307030350060303820560104080d00d400c601d1000c00240104076854061502c141c000381c03010602c210084003003071960340450000c0021900b0390b21103194101180302e41c140201710480e444690b01d5192007000282c01180d120b421420051480304000800c1550150748402e1401d50307419403980c0312401c1058078801c0c0022000d40608400075941261060401c40351328198014201901202d201d404200c01040e030107106840f83c0340e004070300b42c440c01d01c0c1c904c400c08106000e03076aa0240043c1c9100794031241c4805403000301590080080c580f00b20b42c02d0300850f1400b07504128042044002409014190311a240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 613373102 1250 613371852 613371887
    0xc19090f02072001091e0801050a0204120602030405070e0406020714010e03180a03230c04060303050304080a110106091a100822170c10050403201e0d0801210210 71
    0x1004c000054511b01242e0003243e45160090100b9510320380f05d00308a1095002d02c64034041e140c0300c1d28000c9a82e5501941d400b5119004403542d040c0c8903604114281b008607002c0303440340c0c1c00007102d01c10412101140c0ca0312144160090000f601801940e075243c0c001e8072071100c10011421064903542c0e5075105000029034200c1d114908035681c410b5440702040320742503101c070148511924800c00303091a104a2003243e40603920681181c8495855001e141e0103c0c031750344104210103e0590f100074080c890740006041c81c040c000343c42400d008098000080c0201030521400c0e400c0349158500d6000038a459120035810481e20913008400c1c04607a484100c080094101310f0301400803004048444003d010783e103c01001c5943d06405003071905c003600e0040320000c0c002514480d002507103408100a0700c450388502c48c15a01c840c41d9010000c011240290701020065000150b4a9a095001003c40d805400c003120701d6a1400300305260742c0190751102900074010308900c140c000031948500400d110715250003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 613374352 1250 613373102 613373129
    0x902180907030209070e09010902090402070c180c110a17070503042903070906080c04080102030a0605010e06040812030c0910080712022a0c19090f0207200109 70
    0x886a00d5524545400100d00840048000c60032240c05000c510410f40401009024542e0030814800040e402180c2201e4002c0c1c0c00384402c01c0007400840c003540141150454565022113040c0030a0290b81000c0b001005014441407220a4100d003c00c88484940c1c1000c0703000910740300c2041d0b00c081403140075405132441c0804039000c11158000d80c1820700c6060a1044090b002c100c0c00c1d0103243c00c4c4030a564001c00328914490402ca0b0900807407040703a000c0380106289041943c0e41a40500366032044500340d112a03a070741c00a10840d82c0100d11100680400c0e0396040c1803500300700e0034503921280340d06440301c180c00200001c0c44c610750705401c0780d03482c000107010181c00c0840d0f004060290310301911100d011505401d00b8541044117071083d2004242d400c000e483c0b0b1070324003401d83c200c204841c880c04402d5000d07030b046607141a151100007034070a5184601002c4403601d030000510403034040803a000446d038010000c0e84042038842c90294914494080b840c06591904801030710321100f1548644c10641c401d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 613375602 1250 613374352 613374361
    0x20d0c0902210f0402090402150d0f110c030f0f07020d0b1b09030a081303050f0a1b0b0d180c0b0c060f0c04030f170d020c010f060b030a090218 63
    0x96005805484030045038040e10b841e0750042d803042c0300c104840c03854020240200160262800c4503000750004e0000d400a80c00c0c00c140c0d00410215800942c002030b01d113441e40c04400d05114607104c2c54101c040c10300380e0325040a25620b085500c07403158142d490b00700080450f180da40034285c0d80c211002d15078000c007000e103075107418603281c5542c0100b01c4428101c03031070301d41d42c80504522220480303140000043c007130805503907160354010080e041070b0210100c6540c9000c2c04000100100014030101100e00014940c0d0f00140c43c0450802c03034a140b52000c94582c00001704883c0c2c03105006c0e078816000c28072001c500b5601c0001402100d00380401c0203404001c1d62440050700602400c0148200c504100030740b8002d5503103414180101c802a03c0344408445c08100410105d014140d4000c81c56114101078006850300200b0038480f604501c01070b2605030780c001074010030603000b442120f0302c41c407040200b401403d10b840c80c11843ca000007030034407000380c0d203540186045688001c100424070071005030f0310f8050b040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 613376852 1250 613375602 613375619
    0x1404120c050913110411070b010303020609190b0f150a0b04140307030c05010305220c0f06110c0111010f050103080306091b07030309060b030a030f0219020f0d020d0c 73
    0x5540704580c01400c1c82004034880415603096071080d42c2e08100c0b848050644c1d40248801000b264003403812040341800204000381618034600d000314001d50082c070440c01d22094442c20403c1c01e0048200c20852020031000044824407401d40c07220641c1521003a40c0e440c200300603540304034046529400000d00c500400e0140b0307014050001d0f910400c9908882503a0841130544d02c0801e400060302e01100030700c04010540c0709800059101c0c0c1071107070240c844850b041c14443c000d00d140e00103c4240c51215814081604071598110080015240c10182c4144d0b54068544aa41d80b4a0090402103407145c03500c40c0c6e440c00d4003e1614580e20110400041d070f500d0400b214942c10030380d6400d02c075083e0322000c5085039800300d0010500d000c00d5401d1a20303058160354140c0007480c020104642c00c0c0d8407894000040d5400f07000303031403246000c0d8807179040728400001e0007810211940031850700c1210000981c40561142098550380e4181a0303501e5a000c1038500002e00b200c003040900600044140101140485 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 613378102 1250 613376852 613376873
    0x30b220b010f051203070b07090b0c0c100509180a231008010b0102101a060703080601030509010501080307150204050901081b0d020f10030f0c0201061703070b07140412 74
    0x2148007088001c1e2070f440780c08000d42c000161214030002d80c400d1104001240044c3d503180c0e000020b50410170002c5954502502c12a040455a8903060f00080391010003414032503480440c55060340f074118509800300b00082d5848480d9540030200c5408070000031040d181d542d020049a104906610f10704084850064140640481e0031204403902c02100261151050040d542c090070305801404c490320000d4950b00c0101030760180c074203c0802c4507000043c20303100d0700000d02003e802035844078150700d0100009070035107001030460203040e890700d8010050203502000703030b0308541d80c40040140c96892102080c0c1c0030340640d0300301650000641000140300c007400900d05000f5000100107042c05480d0300304200260004082c080d41011151100120310f2408454680c0c038102541400644110315200d40c108807a640d230420030150b0741d589014402c11201c4c0e03900600ae40e052500440c44c24019a441c995403000140c034810500442540200c1128001c80c180c0b809842008086070a01c480e80c1008500d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 613379352 1250 613378102 613378109
    0x81909050c2116080d080910050408091801050609102601260d03020a02030723010e120909090a0f12120e0705010f093308040c030b220b01 61
    0x602c1582802924034031440703c00c0e4200c4595401920203042c45040565200c040104114014001c1055503640c6090740d10940303019a0143c82c0c82070311807001d0020700c03166042020000030707205442e40041105541d0001122418a000d0741c10381038403044044151020904204c891503440243c0b40558428061080002c1c1290040200b8440600c0a040408951021001000d60a030405200071542c02d0181e00144014915841164a0812292036003151a4200300100454410110381d401682c4424060183d551360f004001d0000400075501c0d0101300d11900d20501c0c00340500710300040c002101440020030507a000004400390300c42034500141800ca40494400105080c2a07086940011501c500c03107020402c50000c1c204a8103010041d00c000808045040c200045610049034043c0703245180c4180b021850a1501d00324020070340c8651102030206d644d000c0010702000c100204080031048021a50031190803003e6840c1d01e150406042001c50709450079100c01ca5036541042030b1f01640354101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 613380602 1250 613379352 613379419
    0x324080102090f0913232a04060e0105090907030b01060c02011205130f080f0403062901080456060307030303021602031f0c081909050c 60
    0x5140e80f01c030401812803015500d40300b4001030307014a0400222045000c2020868003400501144410038a19107809600560403e86079410403c801c4800d1800d035101c01542800c5a09208540c20402d503041000d00502c2128420307101000400d401d46000c1c840f00002d503401180300c40341ea40c0c4499002c0c01c890070b5800e04900040b91400031400005a501c01c4901585a5050318490702003151234601040038101000d9459500400c10014102035450080008502c28500420203091020f00c0342d10800b841c50124107441400d078149801070f03078000c000d20f501c80c2c0d010302400301440007140c80d150210034001400a03101850400300d0b007060041464400c000600d03811216911280001c907001095082c1c03101078045d880080c0500000f4000d0300074007440307662800300c01210031081c1c0010b0725010b140b80d02a11441e110784041080a1158000e010740e491203810010145e0801c0c0d1000b07034a0321400d000b40e100080d41d030f81d404001c103c010b01c11540c4e5103000510000c01c0f55034441c100342040c05200d803242d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 613381852 1250 613380602 613380619
    0x4060b030f0f040b1f08011d0105010f0806012304061d15011409121009030f0507020d030318061b1119290408030f06010c0b0106032408010209 63
    0x10a41106116911030303030b40130410340d0b940c2e254485c00e101c4204510000420040c2019008956840300348620b102c84205002500d0003c092007556508590068226481c5660005410b02000c8000603810341110b41c0c1d11582c1c1c515800d1031a2044100708265071080d4407504000300080c01e01c805c03100c18015001488104855601e5400104004203107481b800d60201e1400440e03000c1d01030070280a00b400010140c0b81d1900a0010340c0d80901300b80582c15000c003075550f01c1d04103405040d4015100000400e590410b11716022254000514171000000d0040030140c42d01004203049440300c8009904660103030081c495150a0040d80c204004040c070300c0c500113a115000c4d107405d802c000506032520510326207440c90504154903000c24594840c5451007900c00441545486018801a101c1c803071030190444640702d0070481e0740715042440103040b11b130411629a0300c06000c1072040c54847d04503601800d00103101590804001a1010300c690041820280d401d0001984038040d002400d96010440700600c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613383102 1250 613381852 613381861
    0x40609050f0f0d02011b060204090f050702070303080103080706110307110c0a2102011e0c05160501020d1d0d03020f0c0409080a0c02010c060612110402180f0402040504060b030f 78
    0x400241085252984801608103c60255000300f1059241c40924000700222149540302c0a040e81d0041c3c1c0000003169135404c000b070242005108150b00102d843c400b9100d4a8610b4400502c1c102c0c043c04050310340310001500c0f808210340b99000d00496400641102e0f01c9140000c0003900108900002492278045c0403c09407082c0b412451000513a00d581040d006080d858002590045200920803030500c03451041c058001d1800900305c40a5818654802e8049141c41c90007509046508a4039111031718200c4081c0708a81e00401c0d0306a00340f04519014281c18041a522184411100e01c0550004c01170b40780d042c245540845c0d5500455480c0d002c45103140c410301e050004890840d44050501c0d0420310285015610416503a03070064014500340300c00311000d8456030100c8a0704e0b8003e03205002103a0303280d010040000038074000e11204072000c40c10120300c0b46404007a1005184041d1180d883c000100c001a92a6810b8801404ac09002000314035258241e0031070b280c2c0255114490300442c480000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 613384352 1250 613383102 613383109
    0x62406051b0c031209040e0a14010f06060c300c06050906040503040b0a051c0501030201031a0f010c0807080a030c110c010f141c021c0510050d0305040803040609050f 73
    0x92005080c00b0f0001c105580a5825004054000038651503100f512042c50590390340c800c101c100c0350b6901940220355140c98100025007103a01c51050380c0070442c14000200004e40d0000d00d003000c960340140001d4445075241c050002c0c01c82c0c2c0d103a6504082246050148801e80d40b00c1d01110b5101e103d98001c10064036480d4002c0d030307074901c100d4008000780c0c420041030045003140400303400c807900603040890504420451408681940c104503843c1d0300d54490040040d989e041c0900300c00c00d0700700185411025104404251981030030a0044d05202c4400ca05800304080c9a0456044a80001006d4303218421140014003503c95450101e0004485540202c1d10110124190f4104007058450798200c62a10714240c0c0d9006030b43c0001403d00d03200b4003050100302c02403000c40181e4184c0840069817000124801400c2d00300710501c06900c24503140c00c02c034486900f0502c000035108121400950131515250440e824422034000f1207031800701060000c2d10b02e070841c0300b4405455046400440b40440c04050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 613385602 1250 613384352 613384363
    0x20a0e0f06030c0c030d0507020109030311070309031217040507030507050910060318020402211008030d200c061501030e0c09041401060b18060a0507062406051b 71
    0x850307510a504101107680c0020300341c0100540b010034000d8a090410354645201143c100b211f903800580d4454255204242c1e042c460321071500700c034903105401d24007262401407000c4443d000040412209224500e0200c2c081caa20301c1064610003c810b85034500742c03500f02d403200302d01d1000f01c40030b00c1001d401003524a004048507204d05070660980407000d14105044015007594500160b01429050240015840c3d5000915074414081039644042010b0b400d1800c0c1c48500a21940c08060564000e01c040f0002100b02c032000c1c0f222442c08205a514010610580b05007a0f00b914902c2d10300044a4004840101d98144503221240e28120b810340210019030a85103600400301c00b623040b06a0318007083c0342841a0b6a0014002d05041e0a41400c1c1440142194001e030040341c0c4501c40414200300c2c1c00b98511807040400c00a484060a090304400c01400900545034001d202079114440d48a00c111000803c0c0080c102c40103803000070319030310b040103001d13940450b101c7e81008080e901160964540002c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 613386852 1250 613385602 613385629
    0x90305060703060e0c090a0f0e1b0a020c040203040206130f1706060603010e040f02370f030f1a040c03061803140a0306090e030a020f06040b0f060d020310020a0e 71
    0xc2d246000e0360740e42d240c1803080d030106c0440c651040d100c69001c42da03165112000ca000c3c054040f43c0c3c00103424002600400d5020203220140015001c20034120119070100b01d4010548090f00c0150300d07a00c4620010301c2c18064000351100c030740c244010014258604503151001c88064040c1002450364a080441e150101210341c02e4220000b000108010b80101e030310241c0c824041c50b4405010040b039400550f820118205141804104480c0007100d071070f04c0c42024240d43c01810b08200941d1030000682c2c162440d030720000e03040102038900d94050058a1800c2034071560803880d2120301b49410700d410804410540010f031110782c40c00191148200d51215410055605501c03410244101801c414255600c9200c441d81016214400080c0d030504600468071071050328000345844540c8100007c4c50940300d0040020b5039880f40c0148800b107002c00d40031a800070b8a03c1614240e6664060218030040c084d0300000350184501c05400196000c643d000e400d28481c0d0f0f0303a4203075000502c5c608001d2034001841 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 613388102 1250 613386852 613386869
    0x302090616020321130f030b0103084b030f0f06060d020c0c031606081303050403021306060810030b060f030a0b01120c06050c030a0e01030e0d09030506070306 70
    0x2a9000309184020400c440d02c0102100c88002d0405150b074807001401229025000e8042420b440313160340b2000b00d0021301021440400440c1c40c40d1600c0d038035050103100c0500a00360001d0520100c115495904845a028480d08078650b01c02d11043c00442c500e000e04c0611070f000a00e154683c12a5050480740140c50644500d111034031540c84a480300c9070b020b804a42e009408000010f80da03170060000d807821600300800780009400141c14542403002d61114041d01d001000024400f90341c2020303001e60058400c03203080c000c895030392800355624803803600b001c0d5011104002e4802c1c1d081071a0021000c1d60300e140e0351190141c44e410607202400910f070200802102d400c80019070a03040420b002508558020b040fa10040e900d921010b072000004c0c0c10007500b0b040540000d40501003594080c40052007180b4081d8508074003890829100d00580c3c1000c420030440c000120026032080d0031141c88201d014083d65002a604003024042c3c8081c2d101c202c13214010440011002400703071190742c0c100d0780b050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 613389352 1250 613388102 613388107
    0x150904080d180203100e1e0106050a060e010909110f19031521060603170307020c0f0a170f01110d0b03010605060f0309150a09030e03060411130f050406021903020906 73
    0x24000702600d1b02120701c5029200d000703001e940504805041803140416440006661420082485400e4296410440600c00c0c071002071003031079030300000f00c0301207602504001a4880500c001f0040718171902191103d4a400820345011801444410b41c410015a8070b08004240d00c002681c0d010124511a001d4021034002032452090a0200c55100c40c3d032060b20006419504d9991700c100a560005581d004c00d40301204000415804021642c5080710443d2183c038245030400c00128224400d024038022031001e0310a1a54007070302000604080701070300000f41300007140203481901e160081c03007600251500f415860501410103100b80c105550b40030748881e141c003a806601030f400da400030f02821000c1c4204080346150444102c541806004a84e1004c0340181c4141030090401480c142203d10a810600501001030080240d001d09034000fa20024805045004040018090180410099070030326040108024003031740140440c200c09149000c00112090b022012070003001d0323200d07403c41003c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 613390602 1250 613389352 613389373
    0x1a01080117030d06060e210601090c031b02160501080f010b0307090902030f01180507090e070201060302041d01051f140d0503071b0503030c060a05150904080d180203 73
    0x460300005501040c4070480f454040d20860000450307a0a9100000007000305e00004201e03c1c00607882d002102e0181a40d145210004001c1e130344505040c4a110400c5030f0b600f200303240d220300030341040302c3e4003200b8200032080204280000e92a5040580302260f20400d0140210342d07503018890303281c02840e020280c60303070b9a0b080820000042e4409040079003400001e950008001d01e00740001c500c81c0811070104078643d458040d1b40d1001d41c500d4102455000d090030104951154041d00340710445004c0c0d007010b1050340714540309900606c0d0541001e50040c0c20044c221080031034020041c40641c1400c4006c006070343c1c0c0d0b01d10031404122102c16401007a1045c07074003007042c103440400d50300c0e40b80d10040996102000c2c41da20140795500640c4c003101d0f4005203045c0030700d400402c245003c00030013041e0055440c001c180e20209450340802007500304103954076004100701c0345035652591030706134010340030390150b0a1034105001540c00843c946240700341024a03454180c4400783c1e200042c164090014201490b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 613391852 1250 613390602 613390619
    0xc2f040b121513080a0e0f040e1507091707030b090d0206040f06110406020c0a051e09040c050424080d0e0424090902090c0f1e070b0406020a02011a010801 68
    0x4002e01032048000180407240040381c4c10f9002401da80819445e01c09081200030240043c0308031900b080c920551400003407651042c0040368402440b074202c1d15545e46a1ba40500607a004541500315060201d003040b12400846000100c0800303403800b0b8401040a030f529403034400e684000008589005030058030101d400642d803a060000110b210305030205400f00440c004152a4102ea400540164410851007441d030602c0452540a400305540500160303405a0441e221150b0b02600c4500490461380007506006169503018003400004105012500092003081c015030291001104608400395001599000c00103006068650395102c00c004910a14104002400c18009000394041c1d01803050720700820070200702000d0040c1c075000151002e6640140204210014504011010301300064980d0313003410020340320082d052000540c01e49400202d140d600340118040202007403c008140020401d01e0740181c40c000f2110f038001c1245907080c0900396003042c2c000c07205034085902000188018032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 613393102 1250 613391852 613391893
    0x604050d170a09181103070e01020c03030c070314010902010e0f0f0909031306050f04050f180c030117010513030e0409050f01020c0c090c0a0c2f040b12 67
    0x24000c1d400504802121044515698000c030b01e8040082c44542003849040420390890b1039400303030030708100300303220300706000c0d40c3c0a21002e000101403028a810141d41603100300098a600c1c0c8002c0c00f03507921410043e1400fa47c50310280411603c084024545409440051180d1505207805030743d00c0b40103a0b994000c2c8a040010945e019402082046440314680c0700c0e410100e0050f14200003c554540b407000c00c91030204155044842082010011840e500d8442800d8800b500d00c126084e0300403070020300024440303000d14411009030f540c080040100340d801010186040341d280140c609000d903c1208041c0c200d4100b214005c880440d00540d91000c03e02c00d5000303243c900c2c000f910003d50a01c0300d840755403400141540e841056900010104049542481800d02c81c0d4816a200151400c0c071036401004c9010346810740041007002c03080718050029900c40400c921240c030350b500c16144841c2a682e000c00060304245401103050550100d880d0071710700c08105851282801520001404410b00250344 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 613394352 1250 613393102 613393129
    0x1203120c03042a080d03060305070e0907080d0e100903030c1410020403080903070e070c0b09011514041b0c1b090e0318031204091d0f0f1b060405 64
    0x82510f5200d040d0310114450340319440d60390304980031030040c0c41c110b000b624207a03c41215030100342c00c0490410000740001080d405032052000300c0b40340e55503055000707484d00712140e01c0b01382140302c0d20034410b224580042a20f081c29909844011504044400c10759005082c1d220082c0084c81059500700072500d02c0104034003050381030707064640c06140804030030240d80082e0070545410300000b0380c038460343c40c0400040c401403594408200c170525000d64098003d0b01a450007030031914064001460008080d0301c0903140081c604800c56866071611030030204000100041e5014500c1c00aa9446002a4030f465040e050303109c0d90343e4461706a40c0c3e81c4048a102501607290000a480c0f0404940b4400e240105825170310020015500c0e01116032070385140100c6001e405d40071fa000381304840070304042041240e0544185070b80128100d4901c5040da076021025452140103406071400749074000c036000c1201000f808034078013110001039000c591750300c1155020340c15075413101c2c041000700821700b003d59590000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 613395602 1250 613394352 613394363
    0xf0603021c0e0a080315270c07050118030c05100509070b0a02150a090c0e01031101030506010e0d0308091b060406030b010903060e0d0305010605030f0106180302031005061203120c0304 81
    0x1020703240d41e02e00c0d840d50000d41d9115002d6071702c0e204d9540c481c2000302c0d01c2500422070410b01c40000c211183c00b29580c14001d02a0508c1031000151041448000d4000024074229426619000c2c6201c0c1030040504900395021030700b501416184c14001c07102e50041601900c41e250203004242d2814080c5101076000b8403403281913002e41c1c0d05030210394a028490034070030035226002003081f420919141c200c0a0301e0703400001d2402100001031000c50342c01f030801c02e510102806d000801c0d45680c40147c0b140c0188031704034ae5010710800407a0023056807101540d0301034030302c1e001118890111005c12404a411101c0ea03582c0050702800b042102504c01e4221001c50003044c10a052201c0d140e44079002a01c0c00100c000c4033740e6111440441065605109042c01003449250450a5050901d50311034101018071a010412000f10440c904185601300c000004650040868104a81c01541d1401400d002c585aa03c1a1200001c04002940100c1141e00c650082d14450b0031a0742c031300c04122410340028009940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 613396852 1250 613395602 613395613
    0x1090218070311040e060109060504081911041d01060f060c06110f0c0322120f050102041e170303070c150b04090602090a17030f070614100f0603021c0e 67
    0x3001210080100080d0541d8076441743e19141400000d80f280703c0d954030520410208003c100040b110220b03034901d00200c014042140002c017401c0200d0b00c8448031060310351141c64403540c075001e040341540007e03d21070a48004c0c01030300d45d10314240381c001e403051140c0700104101840b92030002c0d0b4544d00c12442c084010806038108815500c2c00c0b2102d4000041010081d480016503646045031445916140300080782d00034455401c207045005ea04184034001000142240310007010400d00303406403006044640304600c24040212071366a00b8a40b0b51240d440d41420008241d0455940031045038880d8901d80c56034022002913a0390301c100107030b01e4884055800d0f41e03908003c881d55184d00400224074054440503844000c0c0c00b08200c4041c503d540905043d030b2030343c2031454600202006a80c0c20f103124508090f110003050a02d5005410b10507840e0039100340707280400030900f0700202602c095507240c40004608580f520019070172407003040c0740609220b0310000003090001c0241c000e420041d207440f09961 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 613398102 1250 613396852 613396871
    0x5070f0501140718050d0f020310020a12060504060303021c0903050d1d0d0c170a0c0824091905030c0a0308160e0a050f1212030711010902180703 64
    0x41c2181d04200929810881e05020301002c15803140d9032240324420702968615044ca080c000070f241c3d02c08810000c0003103030075112840c107550f0140410705181400c11400e660b91203110100a000c4400041e030412600c1c40c2c2800411141001c2c804e110035640c1c550000e1083c195440c1c440c95560b00344010380c000308082150040000341c414008081441c58a40f1000141002c030038007217050398030b4400a507000301840400d03240455004620942200c038460203408442401c607000c80d0410800c804060107003000d00400142c4450001012890b9901c1d0500b0410180b2443c0e031182400c21081e150203449600c09010060800030311740389000d1051188040324503292a030200d450814000c0c50098010580710010000d601c01e032295083c45a80c0d4601e01501e409905500207076030702e215402068010b89a58110410300c0e1520b401d0310f07849a80e0700c011910307401d194441d20589a0700c12070366040000d02200c4484100700050041c0700b2003a900030003002707080081a0720180311840040001c8201526200c140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 613399352 1250 613398102 613398113
    0x3070611101814010f0c02160b1b0610090b060a05040302040b0406092a0203130902030a020f0d0c0906080402030a0f08130f0f0b130b0304020109180c030b15040605070f 74
    0x4501003d1010021031140800d006080031101000040410754004034861510403181840c2402916000020113843c6c1c04044405101801140800540740c82048140148035400f881d00380211141104103021107400c041c144102c600400c8002c5010a109010034401460701d070b00039006070203007d00000b81c0302d0368451240060b00c084183c80300b642124039800c40c000381d00d242281c1c2809045800214038100340c1003880c117014180340c4503001c100343d07020011600b00940b98044400002d0b15500003911140c1c00d00280004026001c00c040c00f01b041e00030700144042c06249000c0c46550003c1c0174100e82c5d410741c1c448a011110302d010442d1003c00401c003c1c1d601c4518284610301504034400740506240c1000300302000580035801410800d0424060780c103602c110200200240c8460f4941e260710703a2a14401030310240e18075003003144224220383e41c010410003e58041c0400c0c0c0c41a0354284541001d150a00040402000d40564000000c01090040d00e015200500806111303500c1300c40042011f4544 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 613400602 1250 613399352 613399373
    0x11d0117010b0a0603020903010c0203182707110706090b0901180b03090a051b0d170c0102040312180602060a090c0b0c0a050f0c0d030c0305071202010209030706111018 74
    0x440171990224401401e402c0901c5001a040001d00085180200c2d03103014a08051400b030381d40d80700b40b004401c10140080003200c8850a408a802c202841d81407694028042a1040560080714450b84d0000110a449141d59408549050300403524010f811001120443c080312540000203c2061000600c0d0b00c9000095116540e504090040e40c01585412818140107103607240c0343d8069040120711315540c0031164911107600c8680100f18450110100c00c0d24041c1c403036545195440858000b007130040940b040c0300b00a4059481510308a080c1c204403054104c81d00606005a008000041c03000c0a1a4860b0b03894a0290300c51011160f920f0512845a40c050b101140458000140d0031042090800801503001ca0040190444602190110b0800c1043c40c00140400150350810010b050040c0211461980c0049142450b1000301030701a010758401103900b4040e200709100003403042c3c0328040f80c0c8140089180035010a8044900c408040d11182c42891902e40c0c10140d1100041c941489 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 613401852 1250 613400602 613400609
    0x15080102040609080105100b031e0703020d050f040b010b0313021c020a2102040b13050406050f060d03080a0c14032e050607120201020405030f0f06011d0117010b0a 72
    0x1507912420a0b0b001009920b103a813042e50035078188028490307002038101c0582e041d641c0c40e22000351203a4035208029179090031042d0503090802400c00340320072694180c004107606e0340c1134482805240c07034500e40d40c40c5511040324007501141e8140014001080402d00668221001c2040700c03861820603000554103240e01a40e040034460000344e007004504050400380000e24020603520810480044901000284c100000348220703a1080300040c1c0c0d9030750441d07011120040c0034040100740350504c0d01030700621303003030307441c0940078042d44002901c1d4a001c4030400302d00d03585a176821845481d80320809000d0b120400401d01031203100148400000d0000c070186204002e061441c007141d43c4014030580135000180b007100606891402d0912040d11220101c0350307a907900c03041070942108610070480c02806a900704943c54001c030b0b0340201c0e601d00000760403c202e105400564080ba40d80f20541900040780c80003050480041d000104002500c0a088218400300c1000104200c0611400120442e13210380 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 613403102 1250 613401852 613401869
    0x21030c01090c0b040506070b09010603230606091303080c160c06110d0512040c08010f020a200c01050c01061d0a15031106070f0804121b0506040302100315 68
    0x310300c1d2042c4074640e00064020100107507840d02d0300e810100402c030700b4820108060442011600482c10201c0251f120200468021007080e604925464ae0790110442d02d040d0100c0c40d00c82c00b004034185240c0085a14080d641245550303081d482e0705c0e9010398807144020484080140300f44a1182e549190128a903100780c810443c25507100d0030160301500045500c0040e9a2950004001174803441d00502241d8041c0d0319100359028690340c1d0715142004858940000b400ea50a040100e5005910f9402511a180c1c50340c44580b502071104e06540f100300c5400c0130028a5600c80c85040610754002e42c018120b88903010f0000c51000c0e1140d450f50012072001c41c030241c40e0603d90b41006034403e210306c600481e0a4002000044d0039155840c3d005410b0108510503220740c0303000580c217080200b103400c44400c10340d10840042d11944c3c6c0d090700c03104009c040f480c1a40c00c19040d04203030304000720323800019065a20040c02c1d1801d0078103540034004603c80c0c40c1c000b42e06040d51102d081d140d0741c1c0c0c0000800020071051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 613404352 1250 613403102 613403111
    0x109030f0b090f0f0307150b120f07061404030f0312020a0c11040504050c01120b1810081504170904050f04120219080a020304030b010b03011a04060203030621030c01 73
    0xb10310b03514050910040d071445401031844450650070100880d07000540040302594104c85402d0080d0041c011019055840203a2401d254550840403491414a503d03400035622020358641050b600c1c10140c101182460008100510014003200c1c0c010050038024035200401e0581e200b2039500303d038007000800c07022802c000c114404002041c0c641207441001035405114506103590b960395500c48414815041c00713543d00860842211075441901d4940c00100000d100d00c05510110000240c16914101055142580803500c1c0e40c0000310704e5002d52184510300c145a41d40d40707038031400400800f180c0c10908010400010969124001c00e07025911040c480002400d042c44c0900d01804000242415908540b0700b001211440040000c042c940151020b541d910b401b100c02c03401d5104680000300010084800480c607400814050341c1038440c1100039050740400c0c0305482c00c43c4d005a00c82c0e10f005910820000740ca40c2041004c42414514008109a030307100d110290604582084070504c006a545 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 613405602 1250 613404352 613404361
    0x17030906130f05220506010210060b040e06060705031608090a140906100e0d02040603081b010c030b21012c06150906010f23090f0a050a050d020109030f0b 68
    0x200c100200812075242907284078503c500701a41c4d03c00b07640c220101d55110001516079000740070301c41d000105c02104100c001e0300d402b80007030541c006014a2802001e9600014140d061020480b0985074000004509095008900c8c42891050420850784c0031401d00090040303440c0c83c4080f5028200b446400c69200c00c0789418448074010081c00e0500c01c1c80815904402d00c0e8101102c820f05010030303104000040c80b68002305000c2e213400d0780000d0050701c0020b00c82000c80c48040f250f00a8055240090103800d914180031030a490309400d05d40d03804518a0080c4602118102c035030701c0c82e0041c0c10000300d049030130031b81590440714601c004100e40408a603407404c10380106000261f400800400c0ea0200c41070100081088000024407441c10b118100700f900d54840d00032003444600c21078400c0282c41c0c5808202d181016600484416405840d00071465652803900d0550042540c1002e050030041915000c200a004887c1f00c0003a81408220240400400c0000740c014080701c0c02803025a20b203092 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 613406852 1250 613405602 613405619
    0xd0807180312030b0102030903030d2c060a0903020a050604050705150c0d031d06280c08070e0607061802030706020d0512041e03091e06091703090613 66
    0x1410301461222540010620001ea1100c2024018261a1400003080036880005038a035106220b200da5240c800400d891020f01d404d41c000d0008009402000300340c01140c0b619550710a41c2c04041c80c030740e581002000480c50300c0da503132000748202d000e4811141c80ca52103490759400e0810950b410364aa811000e4144a00c4c2880d03022101080d40052101e460b100d421105143c444003141d43e14030030151640c01411204031003081c0c20910709030740020340c0c82d5400d200c04080c07458a6445484070b2603540002d8030000ca0f1210348108200301189440c0c861599480740030448508040061481e4400c0c028864103000c00c07842d12440e48001c0000e10340d40b810324a140105840d0900b1a403007d030465008407070b400c45c060362110685504e04c484a2020380951960301c1c1c01000700d44840401ca03020f1307580d054890300b410f50250b0080100d0f40b4441106d00c1c030311414050000742041c10b00a14000c135078006c100300081310017011b84d0b4a90000301c3e8281d1382044001d1700051206d501c1001d024482a4100038140001003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 613408102 1250 613406852 613406867
    0x6020c2a0306041515142b0201080406061d0a0b060403021e04020d02030c071101021b0d05030f0a050a0201180f1211011113050a0302010923030d0807 66
    0x480503002903032298000300002c0e554003000b0002061039900b0340780d90829250640021907071400351011401015107071840c1c080141c20040f41640300b0481040b0021b2503034032142801c20407110f4a00d8504191a0b260019a00d0fa000500b084032080e81d0342e0030001c1c50700700c5101003958150040345685503030700340405078105032100803440030b02c03400d020031007080181d503414041c20121350105a8180c202c0c0341400050000e000e1010b18401040c000003c101032003060000400700d03248605d40c0550314080641c0120780e03070045060740e13803101c00c1c0321040d81d4420b280c264140c40a251040741101d10700103c40403810328541280020a0118002158100f9074036028010300700301031301807111070050407100d4907168803280301c1d2070003d0800108800104c0d5400c1c07151050219044030b402c001d20820159092006580d800f01d803090f8041241e548003c105460310400d07110840740c050750361106c4d190401001404541d4070207103070101c0d074024103140e0751541c405008585040d4500d407180c02140c40c00350307030241007403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 613409352 1250 613408102 613408153
    0x30219051b0f010b0f0a063603030f030f14010515070203120405010f03050c07080c0a05121b07051509030a0c180e010b01090e2809030f020d0f03090f06020c 69
    0x6c880d452030034080c40c0c0d80605c104481d03130020b007410031124021500ca004a02c0c1e90030000e01d886203104030080103150300501c5441e0500840da43c20801e40080c104500d040312502d4074a00c81004403140100400d14040003801d04030707007044181320301d07204166001038501030380680c0c3c030b00c81c002c1c010900b0044c0c0e40e04019041002c1c586410103120074038010307021480501c15140000c0c582c410210700011025410400800b0450740700b812100c0d000c20155a030031850304808140c0160204a5010400404001c20000200c40000c1c00c8403689400c0702c03202a420b50030030380155406201c0c10400d50003080441400c031000b0725041065a50f4401100e00a8086e90b04000d00e0350501d0f81801070308101e076640315103001c0807500c103222441da550b1510070031210180920f0a901d00c040d41d03145444e030700500480d4010b4144500c240c58911801c4141c51003030362a15001030300c0c400070900c0c5020f401000390181e0403101007184140301c207295140b080d943da04200e07001610304690703551080b02c100030349001c85901402c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 613410602 1250 613409352 613409359
    0x190905090a12181716080c0604030609020f090411010801050d08030f180d020718050c030c0309072d0806091b0a2105060106030219051b0f010b0f 64
    0x607019034580c2188103011082c08010021481100019003550b0106140600440a0400c40d105038107100142e0f58081c1c68294411a507800070006031507600066010484c1c280030f000a0b0806141d40c81c3c04000b040010b40503130b040007921940505a44c1e03849070741407003030717200781585c982d10000d66000420007030058101e54025406841414049140082540d500080c440b000320603954030b584d5560020004424505000c0c030400c0d82a041280d004945032003600e11000c804404d44481492103015203106680001c4075080820202d0100c0042e18001c580c400e405200316614213940305048605182005030b030481100c00c04603c02610a80940003000405920008080d01d08101120300c3e00c56400791811300c1d6101c010802d04c0d03440c0d01c030215018000c0000001050040310000800b010f14114010121a80d0182c1e03000400c1182c02482540c039650340700944c9015080b074442080e202075200c600e02c1400c2100e11100f070648128100002c0718107200b040004a020801c44040c00748041810004920 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 613411852 1250 613410602 613410613
    0x3030f0f011815050a0f030b101a0d291008010303021b0103060f09090b090a050a0f030309020a082103090c3007050906030109030e01031a19090509 65
    0x100c064007851102c1c1c511800e40303001845490b152440c0840c018150312258002407601070005043c480301d01104116809803030710310b0550b40c40a02c440c41c58800c5000b42107450300841c40d0344c3d501000b100c000d1b10344804070b020009102d0003603440c40e850124900c015240220b42c0c0005a80743d81c184110404c030820189d0a02e00c143e5419682d01949400130b02080f60072440a094000480d0b0313100c1e130001001014440d400441e195114801c601c0900381c071400942c2d00c80e0071040803424a6070002107070015035130010068020550142d43e0341051060b03545081d4200364503900303c800903a4600c140340c402400319800a141c000314070f0382c200380034807441c450302604004c0901c100500110302081c03540c0c00034030484001c0c0320245900c00d20712210b2041c003071500400c220f2212403000e2080000790242540c1040310340c0d1441d5a43c4500f0076013611640315004000680c81900324005500941000220700a51400449a0140b02c27001c124034068030b082655003114611801c1040c003082d8031441c3c0d0400c411001030700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 613413102 1250 613411852 613411859
    0x50f0d020d0b06040b0607060f0c0906090306020318190c05061e090319051605060f0d0b0a210b060405040c120f1514181b060c01020c03030f0f01 64
    0x15100c001d824005401d01e0254000103140c0c4d5241c0c1d100c844070b6030000b041c5170f03101e150508040009102c800fa240607010b15015480d160f190103411204110344035950749140071070450352554082c0d08080c1c240c0640c02c0f01240041c110b407009029940080804000d41e0041244a0800011540d1244d1103140210700400c180003003004000d8100b00001100d84115585d0324011300400d142103203007107000c2520003913001c0c658108a4007091503500c82000030400c40c1815250800c00c07049120f0300c4034102c0450010000c54665000c181c0044010a400511040155a0760b55140b03d240c50041417000003008040005810852042241e0b41c211400f03803420010b074034007556810b50302c2485008048040ca0128004802c120703207852204a841d5104003403004100e0003080c0ca801600b041816804044412400100c03940001500781910f1038201009080701a21101d252800071450b001080d0014410032000c94200700900080404502c180011a039030326000e9510380f28090085d0500c5801001d040040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 613414352 1250 613413102 613413109
    0x21e0309040e0f01091506050f060703110f0d050d06120309031b03150605011d101115040c050a060e0a0b090d020d0606141206040f17040f050f0d02 65
    0x1100011400d8900054000b500c254541ca05061001c0c040100d60810120304100904c00c2c00000084011444c00d00249855074101308405041904880d0020014440140400d100b0a0240e41107041d01c020780b0318401c1070000650a0907800a410404100001284c07001c140c91441800010b00c0511035902da40c11060350000d0071081140302c041c0031008060003802c184100d5282c010004c0d80e10400c000d442404108803200030300703624440d06000c03504040d440042d940a40000b090001402403100841545144050340d000c507422010304214811102184030031307034200d001d190140303010b40d0325031011504c0c1800308410701088e50000340401403010390160031074941c00ba4142c10b8400962000e616042c01c0c03404104140c0390844069804020b05080d103090141c039a10920a0b80c2050f00c81211800f0200180000310001d030341040b090b50b0005000801007082e04c0300c980f440b54801c0c0d000c0320001040a02101e0107801c9500101880021240704010794606503041c0d02a40405a07400341005500d038001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 613415602 1250 613414352 613414357
    0xf02010e0703170c010204150f02010c230f0d0203150d0f1707050307032304050f0f1c0605060117070e090606040902040602160e06060409090804030b0106050a021e03 73
    0x300350f000858210070843e0b918009603200000c608008540321036503010294840d02d10030f00200003050001140302007107441070042c0442c944003500c9240c4440030500303440c3c80940200d14500342c00c941c1030200d03d0f4260b850350010b2504924070301c0e025890742012200c040b2a110b070040d450788103030700d03103a110000112850f00d100c44041e04403500301c08103014199004001c2c0f10b140d0006000e40000946030301019005407005008a0070615a031072071800c2480400424800d42c01140c1d03000399842042103280c40c05940e40d0b4445040503088400c501014014030740d02c23107101c1c14211040f5803248100106540d000d590000c00488003600d0340c84c00c0c01c1044010b010034000c680214055140c100001e581e684509088a0084c00c48000456031240e8442c0003d44484d1001406070b0154000240000c115a041103040e015a40003040c1c175180918021803e40100030b42c3c0400c681c1c002d000c0c0400030209100d0483d0600902441e11102c0c1d494401210080c1001c410401a03030034400f15445459641800209 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 613416852 1250 613415602 613415609
    0xa0207150207110901120c0603020a05090906060912030c0118030c061802090705121005280b1803010c0c050714030a1209031a010501020a0206071a0108030a0f02010e07 74
    0x42e0744041d00e06003040e4800071250200e81007031890000040c1082a0300d868250a4040c860010940303441e041d0440a0b03102c0d020214000407000c0c45140c2041c0381c20074480c0c0d00010b00802580ca004440004103108130300c0400710394041d410110310455901002c0c001ca0000c45d801421a07a0766110a54000d0a1a2091350002d49004e682d0207802c4207400126030305907129500105118194600840c0c000d1040d030211034402404c0c3c09640228246024100c130a40c10340d0401130000c542c120400807102c1050f81c02864503820311010b400b00082c40e0b540c00d0000c00b0b0070018480000c001044a80030f160035112030020903020405101b41903030104101040610940b50041c10100c21000240006490180a1400a04103071001201900140d4000b9540c1013121300c03071010081c0c02c5841c421182e00d402c109216507805078200102c00c400510b030050003428a0b0b0711a510450b0803d00e62008080781d0003091704461070540c00010900c00294102a90102903c018070003480b02d20f000048090302c1d0840380c0f1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 613418102 1250 613416852 613416893
    0x2a0706090b0301053604110a060509062506020708041508160e03160e1501020601061b030c060f150b0c0c0402070330060645060c06050a0207 62
    0x204c02035000d101c1005d254501e118802680050529040c25000c24070401c80c064424841c18030001040e80c003034029035581c003c00601c202d0030081c0100340c030040804580072441c030861180710100005001407018184081c010b04285490381d040c90551704444210140b040d050115442c1013160214040004070104201031030300316111944140803a00d04480d903040c4205a90320311002140544c20007a1082c0300d00c10881e0056002480c15005a845020a0291a0020301e05242d20311190000e2006402d04920902e01038008240c6a15840c1c202c8006c02c00e40c64400383c440d00d5051407416603441c1c1c036006d0809039240b10f1914617010381450f960b407450700f100b601a0b80c0100c0d49809143c09241d150038040e2000c1c8068180c25400008046d014410f0070301c1a07076003460408003203044e40c4070b1131081d4940c08080418000074803180c00c144100708620510300341046415a451081010481000720040000351910f101500c1603150620954200805802d5580c0c81030014a0100b021551407038031841254 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 613419352 1250 613418102 613418149
    0x1518030c02030c0d1104051803041703040b0406031508011a01080a0b04050f04060507080103030f0e030708030a02101422140307080304050d0906080a022a0706090b030105 75
    0x1480460704188942d820540e008a04e4180307038051181c1012412900d95045404014940d01e00700328101c0d81c05003014a40e41580240014004081151100b440c00442c880c2142d080a40e0341ca400700b441e5026800a400194031788080d800c00741941c4c0700e44c43c05000e00388001c0c01404208040155211072940c0c3c12810010000c011400c529500c1c0c0c05844c040300050400d209924100003814401c1006403400c032010341c41e0000043c03809101c0d4140314180c1b40d149d0380745004e24a440b401280d81c4200c41e090141e0502400704005080b0600300000c02d0344007880c1c0c000d0240d410070b01958408842ca151010030361b501007182000604543d20803c065a01c582ca2006103600704241405203161007001c4650800d813000058420901140030041d5210700c0c440e00c116441804009022183c0200714854a008290400301080500d0640d401520035501c540c0c0c071001c020703c80800c24000b0154610007100054012402c20310142c0c2e403010240028040003246a89913524050100342000c0b08602449998500c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 613420602 1250 613419352 613419377
    0x20733020a030225051213060e01030f050f100801050c3001030305132102040e0a050a121106010f0603020f0c0a0b090d11060402060721020703151803 66
    0x1e0790644ea19820307002c620600001ea201002c0b154112103a00c00d40e0603208080c0034550f48296001151045034078060a03102d602c2c07601009456041d2038903000c40c1815154680240100301900c1260b1040101200205d150308080c04041d088500c0c941050000341d0506003045443e62281e803c44002480100581d41400c40307203010b03d0040b4103411b0b400c41100d0f100038000020705911001400500d280070420030310310317580c0f07401c5900b0446012802d4122904540d13400000b5292070341c86040c1c01c140881c1500c440342c0241c3d842c3c40c1402c90b0300608980c641d00e40c0d04000c102c00d501c402e45540920100000703244d103504100d070b02801000244200030805400060340d40d4510703502015500101b04020865000120030302d0603d241800c21a440341141c483c1408c103d90740b502c10b505080031800c040004d03000e15203170b0781c00f400780580c007210341510b400b50a202000300c0c40c03624500030403201c0345581c06030403014110301d00514401c058a1a0844103401c0c11f140040144442c0002141c040d81800d084058124 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 613421852 1250 613420602 613420607
    0x5100e0f21040b040b0a090506040810050a0204090c0507050c030c01140c0a0b01081015060905010c02030708060108030a0912020603060103150b0d0204080f1902060c01021606020733020a 82
    0x9650003d241a140100e000100800b0800140c5102ca03002d46446500540b602c0610150303000314419001c035980040c02659210015510040c4c000c8d5400c0030141c40d2985071100c0005a80c02e070740e104400542c00045244c00d00000384180b46040c0c1302140a402c0281840b00000d001c0451002c040700e4100000a0b03441d440c00e41080051503040d8001c030788080b650f82d20100300f80c941d0890b0682003001400c002c80c50135035060355030480c407d0310450789402d0421424840112040710007000e040742c0500c200c400104040004001c40e500900c41d0100a507a5010004001000080c6681c060003d41e0302c4020010b00580e20441a03aa1010081c6000544088001c000c0c15441006074000c0c903055100003820503002c1c41640040c400d4400c00b0044403c461324891219603102c2c4822031408001c035545051a006141500040c8140c1c410480054200042d50010000031044400d08403105540090300b50104450900040366402c01400504000b120282e0503d40404107945924001076001480c0b018050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 613423102 1250 613421852 613421857
    0x60612062301061b230f12041404061e1806030201080402060f0706060f0f171b010207231005090108150d0b0f0919080708131205100e0f21 61
    0x250000c040b094107445d030a8159021107040050b22032203000345044400b03184400030344107074460700c4440301d1458145000020a048051070100c1980162540d074001010551100340d1002c62000e140100110f514040d5a0444140e20400d1050364074100039080015030307082001c00d948142c0503a41989c0e02c04481c0d108560a100d1128005d040514100e004911544404041d4058802c0c4464820400d40c50700b01002511015000324946948264002100c451064803418980d4406004490480307469469012800307000e107008902c01162524140c0f454604004403a40e0000f090600924003521074000070100035005000054100f41191945855141d0034561500d164003d5444181c82c00c06c0b58803c0a1202c080d554083c85125491410703803105090460b09004c1c0b54447c10103071034034200780d50b0240300d0b03081710417070081c01d440c0d40000243e155014901034012600c554040d041c00040ba00307685044503414001c0f14031944c03100ca115200d000000030300c401e0102c514290120140449100703982580b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 613424352 1250 613423102 613423157
    0xc060b0909010c020d03480f0306090203060105120c0c1002090a05040c090e041109010602030a0206090c0f042a0801030c0e1b090d06061206230106 65
    0x10032210100300d4211810743c44603082c1c0c0c00c160b00342c41415200c428110b080e500c2c10740ca407041150204039422a0701c0e040d08807107841d80140792000c01c60a980c0c0c4c40500084a81480300c50085500708500103482030749482000007402071203d0450442c05c1100000745103000d1392030f1034007041d224000810081c90100040d5481a0042e00031220740650007005a40039410000e00702c2d004001d41c400201e41c03440c050203418501115561059140f07441c201060002d684060000d840103800354103010640e03116111014080c1100e9002996a40d840c0342000385889001403415610742c00180c52020145e03100741c084070040c0d204903004180c02907507560340b440010b00c00c14800d150158141a020b00703a60440c0f1020f040301e0089080002e02a80c0c0e802414020800311a80204641c0000b88540701440100151050420103052080080c8503691030078101ca1954000c0c07984208904011810450540901c44103024084042d00c10364201c014107020485043c0110402e210300003038002d080250140482014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 613425602 1250 613424352 613424359
    0x923040516090e0105090c0a0c020a03030c020102100605220e06071e05070f0312150306050a0e0a171615020a08060607020a2105060c0306030d140405010c060b 70
    0xa41407410210400d1004003503140046075205070000303242c0d004030b054981203c9001d0900590365940307408414440d804000100140801d1401d80000b41c1c480360898409944243c807107005003515400007920b4002c058140c140030f181804820312240d140d44a4030f41400107d420b990003451114800030000d4120000a16258821070040000341c41e8000414185403228030303904071104028000c22a220310070110042e214603103003000003000a108184407003c41448101c005071406003440001d01915a038ad0083e10400d440340280701010b10b441c1302c1e0300c56052150b401091600c80315a1218090908004209100c51004c07600d010b02440c0e1a80b440d02481d484504840b103e0040c00e44440250040348075600021582c0c0000f881c181040b004845101d9001800c00d91281e1502c01107108440a92011590aa900d00c2800001820420101e4000d640000041c3c0e02c9281c4070742854500302c92015500c003000b6440142e0080720341c24004072000d1b90401e103441c072940c4c003883c02c19030050807000501c03a40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 613426852 1250 613425602 613425611
    0xf1e0103020403140d0f0206131e020d051506011809090521040326070b0901061a03011e0b0307111c0809100e03040b0c0c060c0601060809030703092304 67
    0x7042e820101d20582821686d854900d004030380351401300e03511241180d191600c0e0940b0021034020401c00090030804507201d20860104a0840e804520b144404100c00c0707411703a00158202100f00246403682d03078401002c3c680340c0c00c0810b007404070107440c0d15140b140c14503041c0d079540088103210050000c05401200110030301c5024510403074034109a0301910040d5000035402c1400b803118104601060560400b020400b07080164030344828901500190040386159030341c0700c00003242c5100e500280001126048025200e41c03502c0501d0280040792401e030307907042c1010030081c01076030300c400b050f00d411640314540b110300841c030960b520f4a401d000c1c2e030115606003c1580740e40201603105d0030092190303e621090f01d140c1c012181c480d006840b10080440c0086e08203001c14842c444282020b04000320400342260703030320340d042404181541d0040031001010341140c03005004194000c904a82c0086100d401180b40110644005081e0445409a9080b20345507804002e0341c00d800304602c0c4081c0400900410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 613428102 1250 613426852 613426883
    0x9070e0711060901020f1c0b15070606090203010e0f182b0e0604050609040908040909032309010311130602100605060c070b07021504090b09060f1e0103020403 70
    0x618040920340741000c20b20030380d00010070720700060090f14421041d289601d03040060400107030248880507100b03808100c0e554140384155503941c0394403849a004205000740c1e201e6642c10040e041c1c075010b80054007011700402c01008003080c0740c0e440d66440890301e118145d41d6100c0c060a49002e0325520216906442840c2009091076505240f04980c000032169514904c8030010050b50900c00340c070300c2a6408ad030705120130091800d0510007005005002400007030726640795a0b503401503820035040414126030f5001e00c1020580c200f41c021030002040702c508100094031144004042c403a07190003a04140c1c54940f41514100c640c03080d10b0721000ac10003c3d480d86921081c0017540c0701c0c10380354054941c9080c0600041c840c100b40048500c44402c0202820380d00381030440c2c4032569801008100e0b0400e109a5005068191410180018013a01080800e824070744204201c0103020140c002403145c00d03140d0710110b841e61600b011900c450810010180500b26507401a0001c2c0165031026250b40d03014520003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 613429352 1250 613428102 613428107
    0x708030c010b011704030906122a030c02030324060d091515050114180d0503030a200d0f020c0a060b0907020d09090e0a080c01090320070302010809070e07 68
    0x1214000c030a80c1c82406000c00a41941c02d0400c064501802168447c2c0342400054415900318140030407032000070400c154400f402d02074404014803c00d03c81c034884414128001c0e410b02800c000035029100640c01d5041502d942c0540340c928400d04000c60328100900b991a03160242074440390580c3c1102080303507143c103007841d03a103440e240c6450300210761408206007aa03014910b125000c1d00c00603540e003040955226920600c591208580e004000039808030b0503a55074134000709203205480341d009140c0380d09159211001392003800c20f011241c452909080800c0c1c4c4060002c0d215601035510007c252a0ba100304401d0084c80340b044841c009005a841c51018801150828030b1070030002d6408204598841c0c0c4100e071110044c815441c00584040010012b442d00d607040000901842401c0d10751800311a6100e003260b51110381a44200d9450302924024140c00001d580b042c00c1a8456160110b5403c011aa84440440c000203041c003001c04085901501d00b0040075018107951380511083e8105024003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 613430602 1250 613429352 613429361
    0xc12070c0515130b060901060c2307030c0906060201020a0e01032f090f060f0406141908090f16180f0905030c0d09030f02150706151a0301030b01090203090708030c01 73
    0x545900801e1008250305e402d0001c0d000d8103c0c0c044c0d94420448000b240d66100b200b600c100c0d003d80200c1c1d0300d201d03801c448003820b001120096209051000e9054074101d0300600b070344d200d0361015041da4070500100c01407036049001c14440e54800d107000564030406030800c02801420207003082002c50702900317017212124414000c00c808d03442203039280500e00034401084480d2185941c04600c0e044240010083c041c0100c96900803d41d0300324a079803d10003044181c400c0300a01c2a00140014008030900c00c984105101c40d00641c0301e24005030403143c1c54800e940d100c0300e50394400c1084104c1c0b401c643d07500f84003d036030000444201c1d01000340044142418540c0c1d8903001030f0031a805a011340d03412100e411707000724124000c4036840341d00401c50003080e03001c00401c8a038858500c00540030030820080090074510503851040302c0420622461814021034440b1021005802d5410b44000c100500c0410031001c0c07003d04441d1030402c090f03a40d541c0d00c1f603071500304903541c1d0100360144000b05020718022010f400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 613431852 1250 613430602 613430641
    0x60302031c1e0906090e13230604080304030809060906010e06030325022b030c08070b0f0115050f0906031e1e0c0f07020103050a0b030a14060c12070c0515 68
    0x15000e41c00e64440d0112511041c007a034000106107c444980400a1201000c54056030480068180d61006400f069820060100d400f260306203000400c1004141e08800d810b0f80002c80c1d200101400e02d403401a0325a606810f0140740010560140000c0c10b95400700200c503e5264889240c41020085079517900d40b0f0051860100e101703c0340060102b814543e80da10391625448004920800c0c0362084d20141c5402c604640e080e10608403c000c80c9001c1800700240902074405540c802819602d400c2180729803d440c120705104000f010044080742c0c5241006072600502d040744c031180e8a4660968256440b80c02c2d14900c140aa10340d4100007600c000c035400c4503034031541e1125641045d41d425400456a104205504002c11000d10052000d0b5219910031940130301e908200203a138002d840c00007481d002d001041142c95010004040e030100e00f0610445411102141707000f07040441c80d038070150b41c4280080003241004034002c0c41c842400300401c801380701d22040050240403400c106640701c520b81490314 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 613433102 1250 613431852 613431857
    0x130f0e040f26040b0d0c03110f1309020301080606010201050a2319111801030b062a010f0f0b040605010f0c0f0803012606060f0111010b060d02120a060302031c1e0906 73
    0x18806c483d82d0340280900004000c00901803450300c01c1000c0c120a054000701541c02111030040804a814911440258043d2401100400c40b51610100090a40b1002807c8801c03150a01c0f205020301e130900f480c006071610300c0c0e500c0703c112540c030000d008070854200c00418541701c0c00e00d00303a1030346103080303500034146001c202c0e0078203080200c00c070700543c00d5900c5041c5980c1c11081c10440d00c192404448603106c5111000c188a18400c0c540301200c600b9034407040301d0991880c4d5141c10501141d0f41921885031540401e070307814816145060b0001e03010a86041455007440340c0c40c00030f0410402d0002c003425a0130340c0040a66201d50710f844103040c2d090442e60054000c40e80c0f0381c84400c4810f400107030031482040c0003040101404080d400440c0e0b96840740c03628000729922200708519542e24600035001006018000603107850201c003403510f80b0360f0050980c120484c0340c02801e2001d0b841c003040b8034450031640503d4400000c0315050486e04011896a00b246a910000351100c0195110f01b07100101d07000ea6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 613434352 1250 613433102 613433111
    0x110a05040602121c02180d030906090f050f0d03180f06080739022205061207030605040f0b040b040501150602030403120c08130f0e040f26040b0d 64
    0x60841c1d0520300c00d2048035901103104e20b0720111039508680003041c1d8402410307491100d4803c003c000c55010b0b0704010080f00800c45030788062003040d6000c503294000b03000180c40c0444003441c0c14041350b192008250101d0080440c001600d05140c02410311580b003200f000f5102c40b0300c0c1c4e901c1d510080c84074554021000028100781c00329481500c10214094801c00401401c0d10290301450020707034036450300d01d207442100e5540003408090303a180d1016130501c030040100c1e00615041c60300002e00302c5030300424031441020380202c485c01d42d51780003c400741907903400100010103031214148aa0429188a0001e0070429035034108020020103100301c0c2e00031441040244020b2800c0490840c2c40f1005001d04030050b03006110030008643c4400d419120380b01c5508003011900410b482e480c01c0c0d948448696080180c0050302006607402e1044e4040c0286052141c0740c0c00344c2040d9807400359080d50404061701d14102595074960035140d2501880300c41020505482d6120341e05c10503c0000c0e006464642e1b0310030b151 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 613435602 1250 613434352 613434373
    0xd0b0a1107050616020717060a050901060602060412050706051e0a06150c08070501050c07050c1c060b040615030b030c04050601170901060902040b0c16050114070303110a05040602 79
    0x198030941d100303240e014029152a03503c1500208425590255050031403003200d04c0015032640f0036400000d507190000181c0000d241192050b42a2100039185941c00d81c58202c040180c2640800c41c5600306604c48c80b2400740c00c0c1e0b040001ca4060060080203002589000188407405c04a00f01034140c03046d01801d1442c1e16a10080200304440714ac2c4078501c0d81e48121070041c000745100c2d2810f000700ea40328107001824016161285400c40b0403c41d02d1408a071400543d0005000f410403040c095440126000030941500a103100f00c4406402401000c007912800001d4596440c1e42098010f000c006040b155542c0405100801a1020f4107040c0c1c0070340601d41c021103c60925000d400d2080e07a040c3c54074144004003074103034820071400420750303011950303a0f5a01140203052400108000e0812280741074071000741c562400e05160f400418440e50b15030442041045036000301c0c1070396548800c80e00c050f841e92400c0c00c080e0007801c00d1200b00f4090100004522661581102c0988140d407030075402c9403040840c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 613436852 1250 613435602 613435631
    0x3070c1209150c120c0204020d0212010f0b040b090d02040b030a0503030a11040b040605030915040302030a090806130618080403230a0312050a0e030a080a0e1906020c07050d0b0a 78
    0x60f04600904845068002e4045060040000c804840d01c0a4001450040d101d081d030000c82e000100b036902c08045e000010054420403c0c41c82020340001c078082031600346402080646846215207043c060710304108000259a80e82d0b00484120034042e042e245051510300c0c042d51654412a41030284c540352070b2500818603003a00699013951802c0c0c0080b49050f06000081c1c0e40740e000148005101e00c14021038000004007001c20314000d500c00d8008540780d071403040c0c0180c0058030300e411101065200c40200310a91001e00400400c1d5504a1000500004444440c03a0f005441450143c010b4000180010130001d50001e8590b10081d141c000c0104140c001c0d00c4c0ea07485180ca6000a400213044c42240c00d0040c0b0543d12464000e000c0303281c0040c2c00c40c0040070f2a81150001c090340e001117171480081000c0ba070441d01a001d5941d0700744001c0c0100c01c3e120700b901c0400141c0210090b04040d40800c0c1c4881800040011038040d18000340b60350104400c600e4540441c05040b030780b800c015411311881501401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 613438102 1250 613436852 613436867
    0x1060902040b040504270b011d270f010c051c1b05030a0b04110d0f0e0a030302030910050103150e0109030801180b100302070201110a05030f03070c120915 68
    0xb0800e0340d082c0e103002d140c0340800c4040c1c08418036080000c4800320461006013001c0300300c07010403846011180074a602d407405a0305900742c144000801c002051040000490070340300600c50b120240f4400e0800e01e1007510316185000b03955280301500350301e000c281030301054000c1c01400002c4501301121215075a020300c204259045240d0301d500c50070206107035412007401040030b160310030034020740000c2c0300882e840003405462610203448001c40000076003000301402405000520b44080c00184280c41c402e46c6510340c1d40210703840c00380030198040b02048081c0d0b03003400401340400045606000d2035840e070400c0b000c580030700c08d0003180b03030392034501d03107001198040c01151003030380d0940c4038446207a1800c407a1460750300010803520001070b501e0b54414030781d55502440036107510350340d0b13401030300c428562001400c0021224640307507003607001c03800300c1300000e100004440707503214030359034558a0351903003541592407a41c1498001e004040000d0000d1042e0352000211089482000a100007800f80540070758815 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 613439352 1250 613438102 613438109
    0x1106191d2d030714151201120201110d08190e070608100806060d02041127040b0d1e0203070b0301120b0f060d030503072c0f0102030a0203090d020a0305010f0e0106090204 75
    0x502c01c034443e1442ca00646140e45c41c0b030024283d00e00d00780c0706601c840d40c1c400d000d03080f6001541c4406128019943d2115a02c1040400c503402000c0101490307034050030484004003407080251140300c952201d03400641100440c8003030b21049650560b00d80f0304c05451650200c50149241d0b45500300043c0d010000264240104c8000d00002030129441e020722010f41800111507020200c104038807a4101c8040e00d24805036050400441021500304c0d0801041d2021005003030310808264490101050303140d03800e50140d10300125141c10755200d520109007003841a5100c003010080100c00001e540e00000d50350b030349041c031402a2550594440c08041c0003451309440c2580c22814404010001034010170095030080b005091002c01d481e140b40c0400240745010380c010181600441c038a000c1c8d410a0001c0740400c0109001075801c05803d540c0007503880c06a800824840c1d040404c150303080d13403500c028801c0916000002031001c02021340383d0388080e00c68030ba401d44256182041c0010f2007401031081e203054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 613440602 1250 613439352 613439369
    0x40f061a04140f041e05040c05030d17280b0f0109030317150d140105010602010501051825021b0a060c060f02040f0806041106191d2d0307 61
    0x80b500c0c410500221100340b15030fa0b90070a40c4e4620241c00103d04056459403810740442c00b281c40c7c1340902d468003403400c41790f106901030750082c081000c1160f045041500f40b00e031080381401083e5281510350000c181c0d44a20400c071445aa00030703015114854002d42030f8904141c9024000c1d480840c01101e111104d4800600011f600d0040030081c1880310b00140e403c280001c40100640900b80c00007003040f00071080407101008107440204c1c06141c2070145034014038641c00200322a42c5800301003134980c092408844150030454000508000d00d89141c0111021040d0385028414620384019517981110070b00d082c0d000c4005c00c1c25130101c1c134241c0f08071410707100c040c0d03100c051807156030380c4031070140003203544461007190240f00c003044074801800d0070b0300182074400c01405181024180203a061484141c2d0790f002d640c00f00480c04000c07000f002240c24403401840c1600070240a02d814000e00100000306907030107404041d504065981d06142000c42c8280d00059480c0314150700c0400d6982d00c0240f044268 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 613441852 1250 613440602 613440629
    0x20d03050606032401090503160503010e071a0703050c01050f1e061c0f050303040305071406060d110102031c060501030b01020f0a020d0201090e090706110f10021602040f061a04 78
    0x240742450310010900303001810201c84050b1501c00190030015621909270300081c0500e001c110902d02401007181c00628072001c0c01da02400c09061045091030018180c100c12030024444c410148104101c5400d400d0f00c0000300803609050004d080e903000e054415041195149500c0c0c5500f001c124102402008000c11b444d14880307a0502500c8826100c0f04191114010202c10f400403600a00003035200f035200e1369609a8a600900d0302c1e481c0c03091403a01d1092554800c20030044281c980700f203c0c1c1c0303030507800c42c180c41d64260011004072724520540304a6480c5003960017084580c2000da4006409a0b80e098030184480b000d92001207a40391024550b06090368461600790025080000c51003410380e0045c50061542522428400703601e020540d660f91385644088420420181d002c921800d001d40e40c0809400c4e112900402c0d03941d1000e107000245641c5600040100c851902d554072002040d50207001442103659806008005103070b140304a540c4800700d034050700503144d10b01c400c0701e00740c6527480110f07035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 613443102 1250 613441852 613441891
    0xc050a030b1806130b150d1b020a03081b070c03030f030c0503010302060903010b22050c0307080a05220503070c0504050f01030b0604110c0a12050322020a0b0a020d0305060603 77
    0x1000418207072201c13078241d40c500c2402141c3c0c0f00c64039020311390903a1000d203a076581076142003e4100c0e00d450001d000005180e00440c0303440741d8040f130091003c0380c141c900032801e80c49500030711003100c00031402801c0c516400128001044402d041d2501164025103c415200c114440d00703400352a0005014000500c0400c018401403030b103240940000400a4000949020300301c001c54074400715065000e001e010992490500f551050280f10b600140d0500d0f01401c41c02c100a02400002020380384242c120345400002d186848100804800c03103010303070703048161030115040c07203901d0390b200507001d950941d180c000109890801d40076585c0916120003803d40543e10f184c5494482100113444e0704d9106840324404103860003a00f000d04401e100d8107020300035040c594a080d40c00c401c51803000c4000e000e414000c100c100030940740307115101c0e80c5e0303824207012580e81e0388005148074501e174001419003240400c1c100c044940c0012003984256a94404112170f4a48808000c900d000441c0c0c4156245080061003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 613444352 1250 613443102 613443109
    0x50106050d021309050c070b06010f05030c090d080a11073501020d0501030809040b010305040b06010c050304050a0305030301180b03060103030e1207060503091005090c0603190c050a030b1806 84
    0x3c14620001d000001801502c0d9211541510402d0710041da200d40d002c101c0790706002445192a0300701c3c5007400c0c44864030604001c041e010380001083c01d51441e5003c1071068050700c540100f4059a0742c019146030b61038124a001514aa1a0300602a8103210b90440440c405240a101100104103456100d00c0b100a2000f0b100c039803100d540f43d03400c455409010700448007400d402214065840b85da4200e0300c903001241030100316020010110704041c00c090a01001c160300c0c0c131507181c2042c028a03243c3d00c00e00c4107040082c03961040c0d9000941080052200005109010018605850007011701124802c1c45141c0701c2d0584111025195044d00070000400009008100c0544850000391521032204100303243e01707040007059071105000c11800020001c903e0300a10503c20300e1034104104001c5400c105903401da0799040010303640c1c01080000f0204080103030001c030308015a80f5060080c080840340c094010701940150090001103410000424034502d01842203419207000c64140c0d1003242e8502040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 613445602 1250 613444352 613444357
    0x1a0a12080c0f0709060510031e0c0203041e0503010e210d0f020703020109030807050c0a0209070e060301030f020310290a0503100504140a05060c0304020a1d070f03050106050d02 78
    0x3210180c0c0b14914150030300c1c2d107040c4004802804d5010001034064503100521244020181c84401003504d814840c2c0e0109181503c2114105000800024a8140d40c02e0680c510300ca0f9410185e2808a909164207840724a56085c00a540d07040d4000d002c40c0c406c005c625951250b00740174881d41e01c41003591482980c141c1102414840200c0e20022444420342c4649004a070f2003402c1c10750041c2d44a180040a06802c210008d812804910300203180440500da0b56448444041c8004d00c034041070303004a9201071061030108038050004148035525692858184041000000e04a029020b180e00f00b02c5c60181c3c40c444d18001c08812881007402170150b040865028a142082c0c0da480311509001103420b40f410040c21202c54102000015181000e040c01d50420030000b400161a91020a40d05c0024a02246017508800d00ca00c1c0c490f104d03184c40c40025010300e91074200d01c180d40b00c00c0000350301c01c510f4102814050841d584503018031401310241103003918024042d02011881c108460104062107070b00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 613446852 1250 613445602 613445617
    0xc0d0510050618010806070f05090a0e040809060c0a050c030303040305120711010509100e0c01020733050703030f1a12030403140c03070609080705121903031a0a1208 73
    0xe40f5480030f141022004158500313801c4040daa6110304208142d440d0400c0031610415540e0034204d09101c551400104440c905000c0d0034516500000803504000d000000e86005c0c40740248195143d0408100895850301c0008054480d0700c500760540849003004812203004903010f80e82c0629090555a03d0507814102038402003c2080003e204400c0d0761003845854025030040000d810702081d4240c683c000d8404421100301240c01a000c0ca452aa800040143c02c03241d80702260384500300401000503148a103620350221300c090603514081083d070f114004001d154401c0c4c800f00240c0c14904007030380c05ca405c4090b1440b18040007000281c0903181074240303840101d06000803a481e098482d0349001203602e00c0000207515500420680c050f5142c10b10580c00900f9403450a00d24252400c880e03c0d60355200d80c030901e8012440320120703074a52001444180440c40000c50308405210080c54020000c1902040a615500b41100316401518200725038a0448140503048030501850762100107039a482240e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 613448102 1250 613446852 613446859
    0x41e21080309100e0c040b030f060f06150403050a440705070806060f031b0108060609091905060a05090f07051603020d0201061d0412030b04020d050402030c0d05100506 74
    0x8150395222240f03000b00020301000101030b02170a0f26480620040e10300240c20309100360814003244031010310010760b003035000707900340b900e00b400341c450320081051030742c1ca0400303e620244000303804828000001070181c2528480c4c09080c65040c00c9203d6550841d40e00302e40e10b0b02846100800248070b2007011498400d4007089001240ba1441300d54071031345019161791042d26150002c01c100f01303551030000130600c3d0064054002d44400c48c00c44c3e908805017880840118103004407180487e030a501c80c032013640c05101015107007040b00c2c00e10381461800c0740e0600a0100c02241000001100c1742062050b040c1103032405070070521680c5030171110705080040140944100041071003826a044808400c5240483c041c0e0080c00e0300500010380242911030135001021400d124a070f101d450300c036030b003070070349500a81000840e1101c400180c0118050810000150380c400d0012aa50b01c644085602c40c40c00b99108504644a00e802c00d401e00000045041d0050300c2600003150b078074100ed40540104d9840320008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 613449352 1250 613448102 613448113
    0x5040e1515060705160506090108070f02151906060311041a120705030718050117041a0a06061b050705060f0d0c03091a040c050d0503040b041e21080309 67
    0x40041182ca0b0400038003911664441480c0c103900d0300c2c410840700003406080d80d00c11326081d0442c002030040c140203441c0104001442c1400100f41c0c0c0b0a1051000404440c0108002410114441c1408850720301c0d58080b2145007200c00190703035001384200892032140c0441207040c5464030600c040c071003485c600361070101d200802102c1951141007000318403440c3c054580707589030b0402c020000d00c010740d500d002510300c101415040c4140c3c1c0c0c000c01504441c000c2641d201c0142c0d5605d16050010003040c0e4064100044070200b4441c0d40041500a28250781d015914041144206140070306941c0b80c211000d01607410141b801e12960400d10001c021041080100c94a0298140000801c68a2101c8503000103540c4082d06010041d020010360390421410303203505842d082a45426050b04280c2c4141442001498230f460204482801503a00401000800c2500e8607650321717004408040c40b03c050340007104c803003e0200350b4805031a05034480b001400140e610791051555181020703071015101380c03074501c00c3d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 613450602 1250 613449352 613449391
    0x1302090106050c0f0f0d08100807090203060409060527010221040f0813051e0120010f091a160903020409080f0a110606042904110703090f05040e15 65
    0x1c114001650403a00028103821b82c03011002001c1200c09001002e4404108004012100d0700040d0181500c4034824016a41e07150340740054000c01441e000106024100420404900580401c400c481d004240400310705010102e01d1368202d1050300490b040d01c1e840b250040c02c000900b01c0c60300350302501c260201c88000c20141c40f8107245402040b1440103450b40c0c40d0003030200b030a140c2a0a0304596203286016152302c1e0f0400041c00210510884606030045054500d4104200b5005455684c1500904011205550500d000002030103800c07402a80880720104501e062004080034001c2a2903903070520041c1941d080001030000103034141d030070b030206001c1a44101600030040c507166000f901c0365a00d009101600b5820140010320300e510440ca015915465403503074441d16625050b0b0340c11040d171110380030300015004041400110102880100d030030420550000c1502c02556101311540710701d20742d150104016102840012352168114004d10308400d11020b100c980c0181440c1580f00507d110f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 613451852 1250 613450602 613450633
    0xd08012115051005060412020904030e0a0e09060606030105030d0806190905161d040b0a0b0304120801090c051210080d050702040f020723010207150c081302090106050c 74
    0x400c1d2078042001552681403060b8460045070183c0207141c240c40039418185008203084210301c5080000e40101f00ca00c00240c2018032400b10400100002000781e001c40b40c8071010400c00800c00c81d0805180d00c1482c0c00b14901c0c3ca40b9006a030b04a8900030002c1055448000c4c04440c0c06202900140e08039054405004034405c04114400c0500340300c83d8006171910300100c00c0c19281407080409010322140f80c0447c00100c8807820141c030101c50681b8041544120f0501042c466103443c0e0140e4040c040100c01d000c1004a41c411104100009a403004082d9890382c1c0ca4100322090001801b010410800071140350a03181c03800b84d94801030703195030b00d5a60381e03648420303178100b5202019010000e5070014841003103150600c204d010844001c071003181001c00e555207451005000c01e5420805012491030150343d540250101c54030664080391800c00301c40c2c0d20b22420003a00310380980a01003640180002e000c4101d04406820094000f000f03001c503070b40703404810f0790b8aa00420004009028071440f9402542 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 613453102 1250 613451852 613451873
    0xa110307142a0c120709110904050c0a09090c0c030c050a0b100503011a0a09020c030403050a06050f070c38010b0a0e010504270f0e0f010506030d080121 67
    0x1081040d104a003089510307946401c089080540a114440c0015084c041e204001141d20564024403000241c01c400007049941c035020300484150700900b0042000b9082c1c001101038503554100b91581090b1946071803c440a03600c00207030303805c0041c90802151003c05e11400130044614014800c4c5e5052003a1510703500c40441c811194101002d0b04a98104605c1c01c2c00d02c9485001d20a0690300218005583c0000c0c04d003254621904400640124203400080002d004403030007198000202c0d010840c040ca4090b020f010102d03040398040c3c90541c0054605400791200703120207584003494146101c001b1003608881d41c4a481e08401c18240c441c1300c05250703041301880902038000c0d06c40b5141c54070716000c002403132001a3700d900ca0401038144010404025814540f000304000e042d8081d840801103108000100303c01722890785842d0500c008600c50040c041012902c000e4004001c2c4200c1e50751005040d540d017001c520003000030b040d641c01004020103071507240400002c1d100c2d140103000c000e52250300404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 613454352 1250 613453102 613453147
    0xe01050616120e1338060a0306170109020a060e06091908031206030f070b03010905071e051201050406050d0b0604020c1606110a0b04030e012a0b0a11030714 69
    0x3d17610400a0600901c44d942c0b034524481d807442a43c2c11320350030820000e80094507070600d409554041008075003240680c103c800900203400004004500003c0035a01030302040000360f00440480b0400300d0720714861002a26884000f50002d89000216000d0160603000b01e0500c01d44100294000300d120b4500b4001000850b107480c4012500381401003c042c2401b40c000e4262105030f03c0080100402c0300b0b498190390449000000009950f0342c1d0381c00030340e6040c840d9044c260910340209040700409070084041e0030700d665460180350140c0e8845044c041128a0350098640c4070100002c1000003841c0003c0c49940440050400745c2405040c04109142c00c25038000c040c03016813029403e101c0581d00400d80039a403a8100002c141b4071517161580c203040c1501410180410003081003441035a4001c9106056601c1034036007c0404c462080000440c8036880542140d4000c0d1040200f0f524443c0d81c0100b032482c021500041c0c0c955242c40905440c8000d1100407111502800d0140f1021794481380f003070b461003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 613455602 1250 613454352 613454389
    0x1418090a060914061809030c011e0c02010c1b0206040504090c0305060f1e0901090c03080414010311310806010e070f2f070b040e01050616120e 63
    0x946040c034030200c2c1920182001c07484101c401500f04000e55070390f45441c40120143c1d40d0401c1c420f890b4032207038038118422490405480d6080141c0380720068008a070301000340e0000ca50070050459035a03412401d9414918040c80001c803262003089004403524850f4410341e1000f040d6a14150740c62000c2400d0b56050201510102c120b614100140081403040b19404428a414441da40c42c1c01c090710046100c4ca210540a03850942002400f143c03002d6100c02c00c01b94000c80c40f5150280c0d24a031102d0349030710a0090a1608250540f1480107500900ae25070340c25907071000b200d003006400710380d141d0004d0186130310720000d00c1840d46000268640310200c00241903010f000d02403560402c0314141d28048090a0b00c0c08100d07803090300340c140d15801660008482a080000c4201d08503504051b0441d441030210b5540a001d034181c0007075582014002041110440080866580c1c2e0300d104001050180082c900e64040d1040a032000040c005248440030322071074203203800310082400c0400c43c410b443d490708015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 613456852 1250 613455602 613455611
    0x1413030c0b040303020706020f0304030f0809030604050c190e0a020f04150e030c06030105010813140d0e03061510031e0903030b01180f06031d0d081609061418090a 72
    0x1131541c140111800b901080c001026042c4091070100d58038402c83c440030341000d402605c28003c00440d00116100c14170001c00300d400e641028201542c0358191210a035200703120038045100e400c60032a07203102c215003202c0e00a104039952203604401a40c408014802c20000400002c02c204504602c100b640900664070210715098000501d03240c100001e003803520404040c40100110380c1d02007000c0d80e002c58a80600d04c000d086a2800882c1c145c64040301c0c4030540039880581c0901640103620700c42d481001c504944407911058070304500e46500c02c00040e006403d00e0300c10391449001e03820a40650700d0b1415815002015050400d04031251003604a001940398100c480c036540e4407589101d14440e01c2040ca840712031400e01d425034080d4a40c40303448107064031007441c0c41704054034850901c0030000344802e40304014808000100200004c071116100f141d0000c641604161241419500f900c80c10f0b1030710004e0000d15403220072980c024400b8800030303080091030f005254039070400250081100310740115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 613458102 1250 613456852 613456859
    0x100801081209060a05070c150e031b01140724020d0b010207060e0d03090b040b0307140a02030d0e0a0c1502070b1207140f130302040b0108071413030c0b04 68
    0x41c00c0c407805421407001c00c0c80034060b00540b503a41500300e500030003440c10040e5442c2000c1c0b41a419115050b4040403280182c6481c09404980245145c2c0c9030031400c60546201c04080c00810309102c0341e06640038001502e2040d00c00c8032038a104020200503000d1800328100c00000d0070b29107030303150901003903050594010500ba00960703154010354014000c240003402c816809e10100400300082440c405215540c2e83c0b058006050190031180060110071400942e500d0702c0f125102c40c0c0d0390041c0e807514002520030254041d4001c44006807500c0720100e5002c1d501c1c0400c81c84400001d0202440040d41d140075a8200d00001401154440300170194813200500400c1c1c0001c0103420803095901c100340107642042407441c00041802560340c4400d050418840318600e44d901e20030640241c140c0820f07004070000c0e41d04140b10b0b00c0c80300c1c101141e10846040c0691000c040044404d0f01003035603854081f80000081c0101030402c3c0d006080711000e40c1e406105900d42c1c9032101c211800050303001e04200040043c003403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 613459352 1250 613458102 613458119
    0x90604081c090602150c0a05090d050a020f271b180a06021207120219050f0d0302091e031906050103120f08011a07060207050d09051f1d100801 63
    0x344000c3c5440d001820007a45a02404071000030014049080d40c03e00140c5948110f008034250388078640701902600d14542541313000343d51820088400d038811800d6000040d10b5180c03264407030521103808000b450701b2000a8020507032007040681401c40151b01d05020701072001441014040c100c0c4400c2d11507030b140700048148080c80e103454011038115081840ea200b508503440d8101c2310381c02d6000700d051341e41080000d0200c1c00c01d40034103000d0014071980503049060100015100c0794174050002620401207001d8801c0c0c0803445400b1205030480821104111450f00c407209280c0c8030f003009801d6400c1c02a900320b6441c0c0c0c201d044071003260300380c4e902c00050041c0004415150007008090820002080501f607024100e03560510480c111562900341c21a14004104e05562200c0d6004505640f640507a1810544400d090300c0b40c0000600c42c0d80c00010316280807090859480f04082c40701c29403a10980084450020786100305030380c0d080e082200c108179211510b0804e6940c2455071492255414a46031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 613460602 1250 613459352 613459367
    0xf06060503030f0f070f170703030e070f05040902010e0621090a0503091203070602030103063201140607020a060c0314180d050a150209030c040203041205090604081c 73
    0x40c001c0e48140003c1d030301e550040b0215030002250058007501c075030480c50120951881080000d01c0411100c0003942d2003061174004d080c84a1080e10248034038160031340015035800c0c2034441c000030305d841e040b005c00103800d0503807008035a180189064a25084124007103903050b40300e07036140803150002d02d0004d2202c076080e0114a411991a00c080c0000c0000c940b215a03407800303000070107480744403c4081c1c0b240f5102c0400072900b203a64041c00a648a684d83d00302100100001d0141c01c5007411401e03e007410325114001c1c0c0c8007a21078442ca5000d140d03401c00f5103580c04900110354264000710100421009070380c52518401c000d014642d00ca0050500c035150040641d0703544421501c1801003808000802c0d1950038100c51f4122091b0b907101041540d50411030710b007000404024001c507000ac2928081a40180c004090b0b003242902221403c81c48101444101c3c84111009000ca803003c1c4500a00148540010030b01c0d01c000401c43c40c10940c83d0800e103800c0018840c900702002c1046c0e10320480a5070000603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 613461852 1250 613460602 613460609
    0x90c1008010f14120d1716020a0b0903040810022d0a050a20160f061b1b120c0504271b0b07060510080a1502040e040f0606 54
    0x40c85001549440a0400380b05864040c0c0c00703800d405100c0c0015507445020103074803038464000448000342d00800c00a40a00d0365038041080100c101c03000182d41c0417403400d090341940143c4d030040a03d00495110b411a4000187c80e405150208100009060208000000704890790b04801641c4448240140310010415028050384199a81c0b8100c241560752041e02c0c5040e150b814055682c1400440865016920007000304000c00f00480c825030303450000031229502c103a00503504017440d8480180c20b180080031301c50400002d0310703264100703650f0800498843c40144a500b03214000240c8a42c4c4c0000f510850b0002c2008040b10a024010702403a1510358005005c19501001410302c041304036198407055a10381d40119170b240e0f40040030480d1504007034204040c1003c001c181d00303480701d03900d03140b0707070310404c82507030310a0034040810101d42400c030075142150715860003031004a0080d582c5c404440c0d4002001c1792402d43c207100000e241007243e9012480b035403080e4101c2c50303181c05510b0542d088904940 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 613463102 1250 613461852 613461857
    0xa050702010e0a151104080c040c02062406070506010e25050a030b0d08040f030302010506060406020d080c070c060507050d080c0a030f0f090b16030902090105090915090c10 76
    0x14480e0b202e0440869a200030070742200304d0035640c46010204401030944040728605410300010001842c1c200400d462489040454050190010185040b41d403000c09840000e100c0120074115494070110078028803181d10003421761400c000f0715031161410910260710441100020500704040080c1e014041a884511080203400d000000d0400500c0740c055101c403201415075402c409015030b41e5110740304400070380c8440301ca5562900c1d00d56840e0400b40078803003100590b09150108003586031141c1550152402a8010510798002c0f210880348004003415200758400300b0482e44011603000384641016103070580b0b8183c0d131501a484c0052400c45400c41d203e041081e5036003440f402201d0b00b011280150000d190124a0035a07004c1040c00070f00b00c400d40000703044d18001c2c6207000c00003c051401e2040003c4a4111007a100f1141d0a50940b01800402540080c101005000c01d01e044002d843d00105201c00f141d000d00c50090101d000c07200203961210159128800100c0c580c0340400390300a0007803503032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 613464352 1250 613463102 613463111
    0xc0a1e0e0a0e0c07061d1605010f030608060606070206120a150603020711010e03010f050a051e042109031b05090106030b06030103060c140406030e01050121141c05030a05070201 78
    0xf0030b0f040d24240642140280190303140d034502c50014464921281c40396001009070b60080040750308120880125108903030104041c001d11413045402481207100711002c03c00074201c5a595041007107a154402d07103089038440c5062201d0300c20f800d09480341501c200c141180010f811a09102010018080e070f41c800d81c20035004015410004004410184801340700382024440c03151220002800f41000a41e16007c0300d190404010320448a900700d94021007030b04545445815181003030f84c03010300b400c480162000715182190040c4440c003030000040300545127001e01c50b042e1655192410b42c0d40840d0364007180c952545007446a464411b15041c01030859040801c111100036001c40d006010510020700466910a141d141d0300d401081181010680c03001c0807903545460300400390003004100030441c0198a400c0012a2403140101500e031060004d5424400040303a0341d487c03a6804291180c24103007401681c4824082103040d1400d0441000151a401d45920f0501141c03021a5401008402103a060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 613465602 1250 613464352 613464361
    0xc0f1207030c0201030b03030d0c2d080c0a0905060c0a0203100c1d0a0b1201060212090a030f0f05011b020f0c06030f0a06120f021002010c080c0a1e0e0a0e 68
    0x300c00b42c02101d5a0a08000c201d101c00c0314002815809003001e0030011300e0406c00040ba03a594004510204000c0b5070722500c400205041c000d6011000070341001020480c3d040100740000d4440b4082c0500c01210326219101c2902d03000070440580207500414001d50015000c00c0440c03405100008240b1445407080101100d41d01c0d005050039030074400341f00c6103168007000052985409500310013511250f0b000301c0c0e8030007004c3c0700c601894030244580801409100100c010302d074549422a10a550010040000e080c1107403607203d00810850001c0314002c0160000c400014030030f001d242c1c41024800140c21401c9070540010f820710030001c1c01c1480e141c007e0044080c0300d03600c490940b03400401d40b8001184a99a202c1d8680003401c1a401000c6141c08290220040004100c07000c5545442075a20f01400e8019400030782c2a900807520000105003e44006100104000040c25820544d46001c11540c1284081440d0540310101600000b40035038118010314109825000e0003044064903840d001e282 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 613466852 1250 613465602 613465607
    0x1051b040b0f0c06070801080d080411041d010c0f030b090f0c070201021e070302040e031201060f030603061112060904050d0305070c1a07030c0f0909020d110c0f120703 74
    0x40d5004110340008040340d001c02d442000300aa0301415450000c4840b1070810140c042c0034400244950591445004481820a4400d8040300d0103a0351107002401c0303081c0c4400400010307000410007505501e207540e15910b90441c0c00d001d228182c4c0d50540341c05034454038825000701511243e1901d28015041c580078440c0780e040b80105030394030413441c406940d01c42c101440100c0c2031942e11144280c140049421034102444041104000c403482100d0800803444110032054507406000108205072400c2001004220f00580030384205500c1c40c139001454503100d65810085450880d00080300c10b03004950300281c01d003070440e01a040582100c0350325481c501a6a501d9540c408200358a0805450394081040e044c028401d0b091280c1d400440040000c00702403605440c000220b58140c0001d00b402ea07081a00383c0109159000c0f60781c3c550300d8000c50350900c08004083d40c8030900c210b40d00341d80d038100c41940d82c0030368016203500b40c002030152121124000f00b140c45c141c5400a000c0d01e10608101c3c2d0000281c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 613468102 1250 613466852 613466857
    0x51501090602070e100b0a020705030c100e010c020316091b0305060d061815020703020705040b030a03110c030303090d090815041203140a0209011812080d2c01051b 72
    0x114801240312440c4d6403c5031105c03240030280d00080741c03507801041041d403450b000715490702660b9094080f610021210002c000740c00226800450100792a800001c0e0a035100b001d5001c18180003404503025400642c00310036941c03040b40e101c207000d5070b5149281c082030303640300c41c03a2890005981380500c2281030580006e0034542044800404041da100b04031050040710b9988004425001090a02300702480e445800180d4003c0c80b04600600030f805022036140383c544201e811004018004211103140c03a03500703660030150001c8003466403080c44804a60340c0e504000440c811513880c006044003000c1024085d101c3d4101d60020b4490f60409030401d6907800c04056115406038002c00711110485040d002070380100b00c04c10782038100d0720f060020048444020780050500301000e981d0b0b10300300c01d54907149500c001058020704005502a02d0704602090589000d03150000855000245441c04070010105444081078003171442041a2405014040f0030301c02e1a6001303000c218134203501107490360000303000e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 613469352 1250 613468102 613468109
    0x602030322020414071e050a140c0106080c1f120c0c02030d0905210312060a0806011e09150e090709182a09270605150109060207 57
    0x40c1060401d03903010310803556810300380c590054020458200610705468a94000b00e03140408030307441c1e5400003054803101c40d81601041d40c5a580b1414101901c0040381c03c011175490303100e90044d0a2007107011402c02841800003d1009900501e4480c001d5014003184558000c62094403040c3c901812420395044103000900700802d000004101440c20400e48021405503000b0b90140304124aa00f03065410100a005690089404450032282c04046a2990250f102512296001400000101840d01c0b891542050008151180441d19400c05a00d000c074240e0100e80143c0b406002c40820390355088661002e01200c0300240144140100b410100b48070034072031411000c912030002800070f0418170031100540710030070051201138081150940002c0890505880845182c070811400920660032180842c402000d007a14552802c3c0c0c0c00c00060280e1600188030394070b0401e0814000c120a1107031100c20380300d2400000c460031300489600496600030040d80c1403164600c024040c1c00e80005040048 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 613470602 1250 613469352 613469371
    0x15040522030e1f030e0705060c19050a170307180b09011d0d050f16050a090207020607140a0b0c030c0403170702030703031205101202040b030a050d090e0f0106020303 73
    0x207074019000030400011202140144407150150045403c0741d054000550f01c1844000b110764841e02d44082294910411400c0c1c071860744600468001010030012581c1243d0007141510140c400c07a484048807050003d030180440c00c2d00000700040960800c6030424904019600106010f0030500300080350310440300c006042c80308020804000c0e59003100c0389c2c031200e200940b000c041c10095250032555509040c0010445001d403a0f04e2400030604d110139842107480040540c1c2c882484d140c11080258440d001c1640c00076010030002011a80300d0360200b0f0102d40040003030030815038a0030801d44030140a800c00001e090208203001840401f40195025aa04095480c904000202c41c0c0485441003108c001d4040c0541d41c000410325400418090f006e6a00720300610056540380c0c0c1203811203580f4001c00c03009d4010700d10078401605013035001c003a07266405000c44482010355183c00d450700c91001d4950000511540301440f001c500040078035003140b0a0103410255504001002e5202d000c01010140c0c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 613471852 1250 613470602 613470617
    0xf0306090605064303110d05031f0521010b120c13140109060611060112030e010509190810091a060d140102040f06020f100f0f051504052203 62
    0x5444c000301e202600f1010264548030703030305100641d00c0840da40010055000c03404c2401e252885140218201c0345c42e1040b5940c1d00d1030359130303090741105040341c24403803001c14620f11400c0851a91189010030f5000c2c400242403e40c034091000300e807400d41e010020b150f03000b8410180340c54159000011062000307e4101e40001405800810101c0140840808003611070340540000802c500390343d02580640740b1594600240e00c00030703c040380d510031080c801c000c42d031140340502001081c0310364007050750039005241c420310b000d1a4200252403001ca0350440311041040d6441044a441c08100f074000350b1301c0c241c4051000e0038481c1c64144810b0078620340e5822800d28280000c04907602c0c03818045800f540101c2c20101c01d40d454003864000c0d0010f00403240c0000b01c000c80410b03c1d6000051040413811144c0007010001c100540d204050842c2c5900351700c24544846004040c0c1085018003480f405907041e11103480b850460800c010380d5806072001000e041401710701d1080c066449050700e010f6806050020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 613473102 1250 613471852 613471897
    0x140403050903030c0106030b06010813030e0103090602040905150a08010b150904020c190209150603070e0a150309021507080f07020d0602030405210414010c1a070f030609060506 78
    0x241584100c00404c2419403a21001100b0030030002c80c00e03030144a080c0c1c3e41909982e920302113501c1405002c1400380100780340b00c3c89424150310907001011084d20568015040c2550740d0120002d0740e2041d1000040d481003d480d900b40342c10000c07400c40003045e0540003409456030f48070210f00d541072089459107400c02c0c00145045e0740e803100e4045401c620098000c4480c460490030160146255409080340301d80c489201245500031086080980d01c44004c108900e1610703604801c0c1c0c4d41903c0041c8040d00711441120002d640a0054110000400162800329640049104009001e41c0c4d02401e240184001d1000b48086480c9030182c504c404d6002e20955601d00684c0000b80300200002d100511260002040204000780400c40b40520861403242c5010600d01111003030f0305005a00500844504002d81000d0561003550701800b4980940140e1150011180b001c1c0c401045c211005d40224080007400024a507051180b00024440000d040110741d06003800241c843c450525108907401e40d046546 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 613474352 1250 613473102 613473109
    0x31812010902060a0513080706080a1d160303030506060a051204050102160807060b0409150b0a050406030c081207030806060a030209130c0e18011505211503011404030509 75
    0x1c050254008040544030318582a009040382c0c002e241056103210a140001525503001400405485040c0c071341d6003041da1580d8501000748070240c03444107884100030001550034001d101c081c424621200c002c0b005242941405070640c1c20240020b80502010000e48410711350150680301d189041604500c0d4548a41c02c105029014080d450405900c506083d1010415250001d00001d8410981480450f00743c43c10403040343e00101000c1c10210349103020000c4803500c0d511105c0b030050020042140c0c50f40310070210341100d03444d400c12206408500d0301480045e004210b241c501010f41248103192500c00c3e50010702c0c0b414050000ca000c0c41000c1080080f40e402901500c4100138050714040789081c500b6030319000740c1014410f02000c181d2000c40d9880909110380c103000f00c00181700a03052964600404c6241031511341e161041086000c1c04120720352600500343c00402c00d05294030200c0c9041440807c10140050b52032644a030785801d00031150301340f2101d80c2f01d50054160820584030b19070301011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 613475602 1250 613474352 613474361
    0x140f13050f06070c0b0f15040b010309080f0d150815100306090302070501080a11092106010e041203021c0e030c0706030515040501081504052404030206070203181201 73
    0x452100c2d010308410025515445014004141c2c021030701010f807500c840e021640c02c494151441040440c1c400750305010350030f06030840d00035120180750010301d8034401e0305c500c042a08200f100003184000001d00300d032001c919024242c10b0045001c022041c4034680740741c4c29500c029400502c5050049440000c02c1c0c0d400c51000e00005540091041c410750171903180c0203440303682900403540401d000304042140c031600c0d845020120200d199180d45840c40c0c3c1020040172013450400400241079602c98130b01d86100901100e80240801c0c6203605550801c1e10388141280340c2002410304051041c04203440b40850b203050b000e0012104100040d20042c0c00500a00754400c4a4614819109140300040d40310381c03581c041c0344550410040d4803142d104c04810003040e29000e129841c1c4d6984040700040b40000e074140001c0d00a4460f2080341c507122901d0784110301519580c0000c40e000c550010400080c107170144201a4403001510281d0301c0c18507480c0d0501d00106060710000c1c0510086412001554001d601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 613476852 1250 613475602 613475623
    0x160b0411061902060106050313020904050a0c0b0c0f01091509050703020a4a07030204080a060905100c022104090f0213090905153403140f1305 63
    0x503066070b5662101c103200102d040210400014031860740009880d0303101d08240e1f4040c51907062020303140c030000d80805c82c4030003010700f0036146c900401c9071000c00604025108401455410402c68917051200502c5040c06108075401149904001000c8006034131068a18460b82c4000c6000961540506000385410b94581009420480034200410070303c400255158110320465403c40007000401d101024081c219000d40105050240c1f800c0ea90300d003401100c9905c0b40c80d6290041c100f40d511104d5905d000c080400649031195260522801c0c00014007003504001c00d03850040c00080200c0d1402542c90000706801925805110342494107500e42c00c041300d000f41018032080c401d41014101e11130013903018120014030041c0409001994590901400c0351464008002e828511035641a102c103110004140070450b81106038201c211030343d403a030f00b13108001200c1c0c0342c080c400c0021071b00541218100740c0300d980035000400420141e558020784103a031000000c4035039458150f5929065140c00d0b0002c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 613478102 1250 613476852 613476859
    0x6211505070509030d0905030d0f0c0f030c0c140901032a1706070f021002071505040b0103022812052b090b03010e070e0102190807020312160b0411 65
    0x400d01600d07560110103030950310400c90a44900761210a400d9a1016032482490f40540020780a41103076070003402d040000f480385040c40d4203000880e60780c0b50191180b40340b0490100e40450b40b1038060200001c1744c60080c1600c00e603c0b11119240300300003280114148801442c10221800a503030215503185004100f55492840d0b100c1c070313503d542c0806040c102e14011044280303c0c40300010360183c415604084400701ca030b000340c040c45000c07042400195100360810303900c8045543d0404010348084c441c040c0f14a000d0020a202c550451042000d81108201c105204440c2c07441c0041d500a2007801c0e8600700c841c4400403200d84a4640f905a0800842c2c110540740d00b138001d030142d0500c80d640c2000d29034510f11565444144c03921141800041d01080c01125010308048001401c1d05026980003562610140101d4003020071011100d1410202c04004851604000ca00c1030700b10b0078200036444812001c0c100041c2071074490103040e020a18901000380104a40002103000d002c0c4081c01440280c0018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 613479352 1250 613478102 613478111
    0x90405040623011d061807091802121f050d020a050301020a0c1703011d091204121103010b06070308040f02060d091416180b04151503062115 62
    0x100399412012409101d21040c04110260f00b940d04902c4c1d040c80c1344a800000c02c96a00d119081102d82c609000042101d07080c8010480081250780c0c801c605020004a031100c003594915030100f046403054005024140506030340c8070b07415910f049103002501610410f5500304030f00700090001880c54803003a44102d8040d4400220181c5240d800003807552500e019031307005401c05d20030341c844202a02c02445000d00514416101400c00001c2c0c20156030816039210841309070b02110308596016511690154801c28038014503602045640400f41981c01c0e021802000400019008a09680700d121802820480c94000003410092010040d00703c9680140c5800e8954980743c0700314000f418481401d907160140e00c2c0103003145040000c4c00d03c40804d0b80440c1c1150a514048248903c080e55060030030341d0303e460360304900707450301c4a00c01e60560200701c0300e908240a1a00710700f080b169a02c0c20042d007c26060410511007044405500d126100c0f002e00c003901070000c5410030507509143c1c40c0030403d201c2d041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 613480602 1250 613479352 613479401
    0x11803090603200f040602060c0f0306040c02030c1b010e01021f0e0703060920040207110103020904021213170a0203090f0d060513110d0b06040c0c020a030c0905011a0904050406 78
    0x41c8005d8000d6404a4007128091384614081009038050003403000c1d8900c1040001510700d0034150008100700300140101c07401d1914914105003071106481030151010000850a86a076a0003540403101e00403e001818100100c1c2c14015008803800c2000d0400c04d07280c0c2410445100100260801180c00010800460106280851080b0740000d403c80040440d4080d60728289018421941075591215103160b504008100560281d04040e5540790b1150342400303d0b00070302605c00040b901c95445541e15000060451921260303a011000c00394404500501041c170704d0940010844044c07000880c4c21b290950410800110b020b01c0e460300013404c9509060500078101c0d00e01e6651058680315180c40007210f56003005104004461240182110512901050590406502c035018105061600320860840c0c0c2e004900d25a4041d44201d868401c0058100b002c0d0800384200c5001d418001c2010305c1c200d0040030b11580301d000e220103451140ba601c20100d8200305003a80304112200640d48510400c0c02c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 613481852 1250 613480602 613480627
    0x3010b030a0b0105040b340606051002070503060117070b0f0a030e01020c070311030f03071a01050306061005130f09021b0607091a0405040f0204050301180309060320 73
    0x355040348220707003403211080080d80510700b62825560b904424070f0514547d002c4500f01001c120300040381800150301c5219011000d2407000c0c400c2801a000070602c0d51606017031000c1036151b03034000ca08641040105002550300460050b044850700c011040d132030400090303042e0400660b40c0c440c00e0840345c0010b1880d000c0c0031000250034075069513107080092083c1400151b090340305030800c030b80d81608900300510001c0c0e0b0360400348000707040141c21141e00c405841a0b4500d1940001c809a0b404001d5040c05c402e115804459240940000d40140606041c0140454495074a090440e0184203001c20781c0f02c44c08440d5600940200451030408202940d0740c004c2e14025440b59071808030410144906403040c16000a4050040310166030703c8140f80e18202810005840110340780c65014010880003e080c0e89501a407614082d82000060761246040700f01801c441c0d0041142911001145030702010941000c1c000d8200c42460801042951220030321172050040f420307504425410201e0600d45008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 613483102 1250 613481852 613481857
    0xa030209100c1506150c080903060a0618090f020f04090b013507090c1803030810050906010e04051003050f0303070e01090b1c0603080d140a020703050403060e1203010b 74
    0x7402941105245881a00c000f000d9628902429032031000085204071071520458503140b00d940078552140c18031070030000082c241071043e42d048012075107407a42840040000300b5a201c0c0d030302e8030741c80400030140c196440319000008130401038411008414610500c1e00d8581004050a500204410075907845510080150012010580260a2464040b21250f01d81c0910004411010380101245440c0240020143c00249001ca04002d8440740240e801d01102130b41d0005180309071288071441c075000300c0d820b0841c44c0a034803552007100300205020490743c000035200c40c00d18003901c000c80d071617840d10399030143c505080c0c1c0020a240304020044616440110185000340342941e14205440391100044884140e540240d4522000130010140f0b091184103400310310113201a8089492540da46400c0300030303007103a22052001500c4008020f0705803a9581203682c80b00e10030408509007000c1d518010f080d402a40401000c1c0c80d6103402600103000308118461140c18010b01c001c0e43ca40e121501c0d100c00f41c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 613484352 1250 613483102 613483127
    0x24120c0306081911030a1106070201031103070c0515061e0312040305010f060608190c0e04090809151c110910020f0c0607170310080f0102120a050105030a03050a03020910 75
    0x22003000600304d05160104100ca036664001c0340f54a0080308241c100296030740300180c00c9060650390068100741c0043c4901841c03041e9071586030380c00d02d008241012401c005141a00c0c81270004036504200d0b096441a5030110b003198001c0c0001c22111034180468030f411f407002c0700c2c0d50088a0103e000020400150840910754522820078840250703102d00a4800500c29560042500b60500000c0031000d055407040403400000e00e0942d419101070000b00e811254801001e84944000181c03128082c200081103c0c0815541010940b824040210700154000c10503504800b05840d400307031040d03d42d250300a42c1e01ca180010f005034081c44003170401a54501c003031840300e0654054016641c0d050716001082e543e5003a002850407410300d0b100701c402c140700c0d44003c020b00004480a8804203c0100c208400c2c5103e00032500010f03929101d0181014027040001e181910550410700140995100400d140d461550b041c20000d890b95a134060641c06805007424040d0003004401c84465102c0d400014400e08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 613485602 1250 613484352 613484363
    0x7090c1b0510111c0203010501080105010f030b040c08090607080708131a0a0212090303010317090316080d02010b09100308030430140a021c0212030103080424120c03060819 76
    0xa02d04d030310980020303404244034881c08101c0a0004000e42c0d4000d064a0880125034500081c40810b410f00090072a4009403100000901c1d00c001c02101010400c00180c1106450070072191926124200600005005002c1d91810890300098402c015200c2480f001813150940c0d078800da8a07000c06100b009400158883c7c0c5440c295070080780a254010003180d0513207030040e20900030a000351994000d6640609003054043c0b092152a070030104a0030100d06c0070301200c0c0041c00d245d08500c1c2000742901e201e50785080c81585040c007032080c120141400c2d042100e40c48000c0e55140d50741c50030035151420b5848124a00d1501036a5080041c12801d021411040c1c40d03a10380044c003090018010266005688816000d40d00100034130b400151010300d00c4000000d10b10403202800b682e015106565002030344200e500a9000c1818070210f50000c0c6002c40c41e00c03541c1e078199010115504000c1c0001c00c1c1110428805070340e0590990444d1282c3c1141015001002c11070300b50b98008504c040b00f81001c218203640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 613486852 1250 613485602 613485637
    0x9051b2b0c06090317090a0b03040b09061b04030213020913060911042102040f110c070605031b0306041b0507050c01180e09030d1401060207090c1b051011 68
    0x1542c50003401000c06481d00055003d800140d090011801c03680100e110560001d0350480c0020402240710017140701e03501c928505910b1b41440a2100d2804001405911520800ca9070141003540700c001038604580c3c0403200c10303c102c8814a903070002403086000c11074000b403101007000c240c01025080802201e03a404001c01440580c48520714041c0902d0140d80c028103500320449200703000b00302e40341100500003400000c03100c45403000c205c02c941030451540e00d0080081380b00042d0b20014012310004240300d0800303910314070304400451321240c01d009000c0c3c0005008408205151070340e83c40b4900c5040801034003140c409039050301604580222901301da1038414035a800729994030600703800442400c03100da00a80b5505000f100c03100780300c006080803068442400b445152a2150046191640700400d08010303079414050020301300000c0e034000001c2e035400c1c1040000c03141e03846131a10004004803600c1d00c0180b03119140840c240807004080035645400e001c1d4400081118030700400c1e00b42a034100442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 613488102 1250 613486852 613486859
    0x8010801152607090f0605060702011704030311030a05010e101401110a0f0b0103050d0c150e1606020c1212121e040b0a050a09051b2b0c 60
    0x3801c0c1c800c200300c41e02014014030020000102030465105410030680b1003012600c90000d0a90b01d8003c459100c040c0701d0ba114014400d001c0514481d407009008140d4940b440e0450680000c0c2441c0d0440c2d801c0403c5400c3c140008040c540310354460002c201c3c0a031000c80d47d900b0002242005000e00b8060000011a01d40200c1c44900c01100a04100d41d440c0246001c40c620480064071080c0c0441c10044d10343c000e80c8650350004580c180707402600f6100d07041110055046040c41407030154098210002e0102c00a545404501c00d0408601c80100d4080040b69058044003550709008040c01400480e040924011030313103540104e01a5100b00054a0000d120701b0015101507840d401910096400c40003001800c100b200f0320600700b94003140b070401e03a81c1104400d54001158403c1203605907001e4050038240b08858510740900c94000500d01c50910401c05035071141510b410000c1e180816001c800a45880c1540b240c001020003402080c0803034400510f405103072180d400504000700c449202e00075021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 613489208 1106 613488102 613488119
    0x5041b18050405042d0b0412050c010e1b180103110a05060f0903010c030605090708091e0f070b1c0e150106020c0103050c0a0f120209030a0c03030801 66
    0x42100401860000503d010f00f8100480701e594503040340d601040001ba11960480e4209290b02c041d034208403001e90365441500914096542042c000c034070058000300d001d40714100007044200181e52000108030a500c0940410004028840014808644010000c03603a01030060b12401007a611400000e00c01e07081550384420307845000600c01c50a00382030190072742100d171904040c0401400c0000240a4090040c0395030200181e08001410140d010030050300204220502c1c0c040200403604810f444007100701290189111301784000402240480890301d640d440752501f0365100075210f14820190180c1084031203c0e106038843c42c8d80a05022200500800319070300105002e8040d0000501034450082c86029065014003840100c140c01118120820000b40743c01800034040728100c1009008044c2d8042d00741c81140480b0041146150544007528000c0c1c44400c8582c0c0c0e201051b = true := by decide +kernel

theorem cover : BRFrame.Cov 613309352 613489208 := by
  have h0 := BRFrame.cov_init 613309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 613309352 ≤ n) (h2 : n < 613489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
