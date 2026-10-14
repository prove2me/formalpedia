-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3736
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:49.161295+00:00
-- url     : https://prove2.me/submissions/2f60590f-2604-4fd0-a68c-29df1b340b0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 671762589 ≤ n < 671942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 671763839 1250 671762589 671762593
    0x1609140607051005070f030e030918060109081209090105270705040306090b091605030601032a06030c09090606050316140d0f0e0d08040602030a1401121b0b0f0c 71
    0x3c42c6203000c6500722101910001c0025103051160190a9810b0060041d80c25903400a5484c20040c54002640c1c10042140b410040070910002440c80e802423103038070000d03c4c5200995100448403616454603034804010540b24842c12030001c10181401e181c01c0300b224410103614968891458445130b20390308014218010808208808000075510b4090020b1a92240818040a0804001403400c101071007100d00c081e80f020320403c2009a6001840d181100d0708032940d0030034a0f400e8911255030000c0e0245c0955009010140040c409625501001017441155038103500c050711540600161800e901c1031100149040c4046402900d040303611008407500c03818040d2107200400b510402310707005003d20300149035680421645111f040d0040f20617070803005001d4501143da00101900807032018002401340740d0301000081042149601c60355103c520082c0350041d560355045a2080e498081004844142440d142420f203d031a030003900040c1d81c0003400c003e0420a29811000c800d0300310307001c010704038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 671765089 1250 671763839 671763853
    0xe2802030d030e10020c0115060f03050a151e120c0e010801020f0a271404051305073804031a06010e010c030201150603240b040e0915070206160914060705 68
    0x4503101d841c02004107003584840740cac200340c3d681000d803c8800c010210400e0a0814084000121141c0c90300410707a0610162000490600c03c4502c85554041c1c0012100c100000400024014007900544c1154000e03005501140c4e20b817204030b4240d020706c24805081001c1806290002800b42d40041244000803640c1190140d11003491070340c1c0403460340503070201041c0ca422070b082e50800c0c2c0a002e500843c0d10000120107074041da11035070b6520507480741000d58070701d00c1c045580303803040d4029000c01840c840c1c4a030001c05400c10181981036020b8801291410b65650702015090040440310744038000503100c2c01520100c880040d0703001091003400303c045550b95034114610904204020000d82080d940001b0007203a8840303160f2503072105070620309005a20b0b030701c208102045041201c00744d41a01c0340c84d0b0f003030340c6030800064988490520800c030401450420002140d0b400100766220b901c0c000190207204480c0202907545001d5409003031060a28111030740468203081004059152247c0215440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 671766339 1250 671765089 671765111
    0xb06040b0f0904030809010b09010f3809101e031d0f070e010b040b04142719060807030605090c1c0b0109060e04060e2802030d030e10020c01 62
    0x142c1d01c0c0c111421030201e036100c0c0901900075000d101b40d01c0058000d80701c11025504100180414011901c85d41e020426503506d040301ca000740c03031040c40c8007004840010300507110000f110f4420b6000011070a00411031000c070949080d1003649400c0003c0c2c802030280c00c55080861084000d40440c44030300300109581c036400c1503540810000130104001c0c0d040640315040c01c2c0400003c1121042c0e101419181003800b06101c0012a4000c58084940182801d51001c03451008600700c9466485803c1100400440c0c0003010b4010f922100e201d24000071741e0f0300070707908641451000c55036103000744a010303800400103100141c255801560000d165204954a0041c1d01c00081c41200c0c803222408031000802041e80100b04030082080d002d01105031060080904225a280c1141c0c001400034110517100d400000518000303201c0300c00841c0480441000c3c2c8925000e03c000c45a0050404901912680784400f410900c644074040b0701902c018003608241d10030320310002c06900040440c1e00655a100d200402d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 671767589 1250 671766339 671766349
    0x1504050a14040506011106011e030f08030703111e031e010617090606010f0e01110111040305070b070203150414030a030c02150714131703070219030b06040b0f 70
    0x80280050300710000307401003203400e02054820107071005042c01a501d404000806021500038191518a031141d100000e49001c82842911039520180003040c90151745824081814001c5205410548091241032001c0300c5040140c03240801c4440c001100901d204040320707441004640080004268480b07103901e4404540c4203410aa0001c1d0214443c0c10050440401e030203005076020381107001400c0649130179400a843e00380600620301c20880e104284500e968082c1000c0141450400d00030071904018130700707408480d07100b8082074440384140d807000281205040100c980c1968003401400036400000ca003401c40c9071014104688210540110754810300082028094289140d600461a103c20040103410800c594540c2810280d840c010090700c150464050100111008070082c0e464000e044011805090382d007000000141e6104010842d00d00000680b00303140c000c50348640d0f2000e040d0203030ba04445442c80300802526002c000108180382990100302104c0d400707800b0702581c01480380011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 671768839 1250 671767589 671767609
    0x4060e0f060d021e03190c02010912020601060e0411040e100305150106080f090705190509040b04123e030318070b09010e040905190302070806060105040311150405 72
    0xe090b4041401c405204440313206080c03c422510000e8a5800e2024403403a80c06201d6800b0489a038807501c152030054402d42c040c00102e900100008a000d1854900940b590400c1c800c403400600510701c000018a050300c5041c3c035440702c0e0b8000c40e00d001e2400b4030141c1c2c0450002c01064501840e208000040781050060041c0000d1071083c2c5545981803000161017403001400d010900ca400074200000c01c00c00003494015180304842c040503100342e04000c03400b4003e4513040035410144440a02c800c00680d00fa01a006600c928001c1d40d1071041d0400071107890340301c5071801c1103c00403080481400340040301c80d020789074900d26218400e00080501c1c0752441d401503070401da42000f6200003451204042c040301c4003410004c03070f0f004e141500020009206d0b049081a252083d56900e1108007005010400708103894046060300c2c907c002d0f1414041d40350300c3ca6100e00080750103050005585580b0070b00403501982d5004100d03030034211100301840160102c01601100d5460300308400304030395448107406 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 671770089 1250 671768839 671768857
    0x2100e0a0308090102120405093d03060b010e031509160b1b0c010507062c1c03050408040308070302120d020a0905040504020d0f0305041203030501060e030f0304060e0f06 75
    0xe556100f600c0070009140c542c880040801c120b200384014030982d03907402d81440e00040308801402000c1700012403000701c07000d00764100700c021407210810009008218081c0045a0003070348100400c2e80c3c02c10054071288054010607a15410034040070310010307030700810f2942080c1c100d0100c4024941c14403016030003081c240c100440c141408511590410344a0450b00034984080d000303007103a500c0b600c00103406800b54003030040c2916140e240300f4500040e40001442c025420402014500301c8201d203007600d4032207107840a030a0302a05280b03100914081c1c01498012580170545602d06071a6480e00c1d007503074000413812400c5010303b036540c4056100352030140c440b80d9003541005030744107275544010f0410086c076402507008a05020130080969901c40c000c1c18580c0d003140401810b403169141c2150b05100d940c00480d07a6030724491529003815415071002c3d0603210580c0340c0860702c2d1003c03010180e40d0000c44c3e002c030049034020001404100e1260700700c1210740c0c5002d040410303804090800194030390000400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 671771339 1250 671770089 671770103
    0x60712050f070f14060a0c1b050c0d0f031205040215071a090c0109290a0519170106110d0e03011e0222150309030507060912020f1902100e0a03 63
    0x1d41152134505000716508028165800c000c002c0c01107070060004960300c44402c000074101400300302804001d1003e2425000006c2c0b4111120400d464810b18070241420700f0340009a006c901507089542a104403070045400801010b034854103a105a01c40760311208003107580c01194188141d00b50001c0d52002c0c003906500e000340641940c1c0780001000103415500c00400c1c00052041d10601521056192172107050200010741c0d10200c400382a2220300c0340d403804024402c10304849144856001280201030002107a0306105666120011690520202402501900071500302100e080c09110b030503001c12001b41c00424441c0d100c801c68403c0fa46080a581d00c0c01e0380004001c004c3c0e0744140c100c2d9180000c2000410341241c1001076481c056050113180d6400d1651303c540f01001c0c14040c1c2e050702c030300b2917201c1c2082c0551003480c540361072450500200b900251091003110041d4110101e80896040200030f40b074030008000340c00b003280c09000750103400280085844215180d46402006001550051607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 671772589 1250 671771339 671771363
    0x906040b12070509090a2121020705010b0105040b0d0e0c0a06020a060f05090319030b1e04060b040501052a0102070b010806060108190c0e0402040807090b060712050f070f 75
    0x62001c2d80400038040a800d81200c0e000c1c1b4001699890108400f0458078884140c1250030041a1000264040c1ea080030104000c0e20b942c2c00651a0010034209129400a004090041c070041d900ca0281c2c0c000c400f120794052281c51061206940b164030b03034800001c21600d00e08801408200c2031185608a1001070f0003140521041c80701310300078602da40100780d00410942c504894425124004c4600c9004800d03004c00b21082818481c0c0c002410305040200416241c044400049030640c00c103440755806913081003000604c480690040d2021110180c513480d182c0141c0d03001d103021a0301090341518000c4019035061460500c00d2014207209032040c1800c405a50520005515205000784a10704115040c020001196001401c40b00401240c540c003090111140c002552203c800a26141d0801d20210f0006a010710000707008048614080f01001920880d409020b036074030403101c0141051000e06a0704034414452001001c000710780003071003814296241c0d1b0301540c05070b40381400c1d10729180803c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 671773839 1250 671772589 671772599
    0x30b0702070609120b07080901090b0f0a050a0b0303040b0f0c060705041d2503091205180108160503100b03010b04050901080102070309050f0a030b0c030f160c020906040b1207 77
    0x4a103c0c400b5000c0d02d4a60111400280d90b41d15142c017008100780204000940824560314003508500c009035440403803a1500d20f0001344003a102207044074100c56440c1000003080718441d44c2d128401c884038014000d507140c242403001e400324a9001c04200385c4100303c10004000c41d0801403000078056040e5a850690781c80c6894601c10000e11540201c51480d85003005100c420849810040d4016a0000a802c0d03000c905000035401000900d00c040c04048048152503542d560220052041c0148081c80d800b200c00c0000045900d201d040320030362008140e00a06500307042c060005558441e20103801d01e8100350715260b8007420740e0403c0c0d001403d00c0d00301040500c003610b0000943d40c050319404008506001c003584004051807814840e850040b5600c40e0401c02c280c49100b2390034065504210050564102030703550340010307401200c1d040d41c90103001c1c0125949400741c1003071215166490f41c80840f2140c40e0b800b040041c40020b02103551099880c00c1c0c0b81e040344c840300b6503079082d42000c0d8007400c0000d280c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 671775089 1250 671773839 671773847
    0x50a09020102010b0303041202040b0609030a0b0f0a0905030720150a0f0305041104270f060501062c0a03060c02030a02070e0c0d020304050f2b030507050a0c020a030b07020706 77
    0x3e213100c0c3c0d10076042400244068045010440d900070380440b4086003190000f00820614440c1c5403200760107000343c244060511102d619250702685400b01280090760324208010212800e41100030002d800401c40c00d80803441c01c035070101c404d01d420169851681c916a0010725407a0000c4000180f40c000483c5094039541c10500b40800220242020301991405a40e21941c2e0000385165070700c02c0b0742e100c2c0200c0c412011740e0b0a400000092000f9003880c4000342c101f078030140c00640e0301168554201000440d0407481100d0000d05064004020042120b030308032422001f01281c0c0445800c01641000000803401341d0094142c903400326000f840d030b549502c6ca002400c044054204452130314655043c48401059642100d404044458005850791100d251203403c00030703150103840c094031603111044c200150040880c45012880c0c0342e4060f07000107101090b420b82c4c00498040d00419030a03c40c01010500502c0820000d40c4000c2a540e07010b6103a87c1d0341420614296034132030051744540020700c6a2a04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 671776339 1250 671775089 671775101
    0x1060903030f090608070f14030c0d0b120c090a0902060f120601030e03041701060b0c16060c031d061c060f050406050a030303020a0519050a0f081b0f0d050a0902010201 74
    0x12502e02095040d05100d00035081c64409041e240c02c20598a00d80414184958943c645038818460015905cac1071a04504030103400c90312100150038940081a88103180c442292103003c1c403000040c0041c10489000c1202e4880003d142e11503142e2a107884100503582e4a0041c0381e031009030b02d0300d280c0710341550002403250000203040c0ca05240c40e0014120110b030002003654121102d0190700000381c010856504d01406841c2c1c401c1c1514840070401e24007451010030400c042e444503a001040a82c4d542c281120515606d41001d000303d00c5004000d00c4a070607000c40b0481081d0054251441c108800115080554220010b801c2c0c0a603904410304c442e810466801000340004c90b41400480e0400300051060015440004c091550004440642c00e004400761441410841034120350f0030b40d1743e08040c0141c0d01c8004624001a614006400024002c040d624040c80000902d1540540e0304d8240700140d522505d8400c40c49203040c0005d42000c50385008003845404010004141c05027039100180c00c1d180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 671777589 1250 671776339 671776367
    0x804090f141302040f0b030304090209040e061e0402010c0210020a2013050a0b060a0e031603050316030203090a03030215070908100f021c09030e0306070c060908120106090303 77
    0x2070000512000c0002502924411030701102c1c001486841617404030000e00b10005520342502011900241c2d901c480d60143c01000c2050b203040c4a5000800c0c0c90a0300c404049600190000002e156401c0d8141080305a0f070780248107042045002e0345e580c00098560601e00542c40041c2e010464880421072446141109560a069650003030f02c0c0090000d0140c0c3e0b00700d1400204a9601c3c4005840c1d200c0540140307015182c00740140c0d0342d446c101500200200b00081000e402446071040d003140130f14524030100c0c01ca9810030003950600c1c0380c5403640c0c030490741031107015400c5100a01580f000356540c0c0a001000754842e4000b054000c0300264102103100c0024040c00034481410006c100d1400f011602d5034110110304800500400c00f220300c98002c4c0184c80486080d00314200b19100c900e0030a51000e540300740203460700030220200c00d00301036480b10111070000000701c0303645419000900c0c6803c46822140706981150511a0500f11002c2480c826408030340002c1440300104181900207000201d01c81c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 671778839 1250 671777589 671777621
    0x203061e100806040b0a0e010305010e070605071209180b09010504091e080415030b0909011b0e0406210221060c0306030a05010c0e0307210605130804090f 68
    0x65052400a424079078020640010b0007641e0000400c103544690080303e48030780c000c0c90f000c405612070f071848602103401d0100300c4540d881c202021014150024091003158085e030f40e12482c1c100c59560300344c0f00b540c90a400c1801d0140604010651050b4221508812849102d001a22a070594204218000c041e4016800f60380790100c8580464620b4420086684000c44080c0c4c1424142c034018000d4801c5500900b070000403481400b15480d8540c000303036a010340464030b500468a510b0069802c840c440402510030b892000d5103104814010500d00e00182401800001c819135904c07990052030740807241c06142c01c040040718030214a400403010200f00b2042017024603122900441540d900c0001d08041c1c5c080401000044c08d40e5810803e010825038088006d00007010703200005000d41019030304640c401d008a040c0484d0400c10344140f0032016581210214000c001a29608003c200161030404240303075035030682010540d4040203200526040350000307040c0e01080d44600455038031b62032500c2d1103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 671780089 1250 671778839 671778889
    0x90925050310030f030909050a060303030b0108070206010e09101103061008010f05040506150d06081212190908070f0308160f0e06091c0501061a0703140d050a020306 73
    0xc10042c20190640380d020384070325a03c400506080d04c00b05040d0344920400b50500c001c002002d0829000030701160b00c252420302401c01d0150042d621450200c07007900041e4440c000410001c440900c80f41d0b000100c2e6000c2e590750101c28030707002c02034070b5a8000703500c20280e001080c0a6039080c4110846500e40080c5400001541001d2001b8500d141e0703813041c0361181d522200420281e968000700341c1e00c000c107000c200c583d031201c1c0002000b000c3e15140c891441c0501545e030381c440c0c021001c1e50488145030042d14011100760b442007412440b602c80501e1101e041c55032011488000b800d22001080740e507004030b10444c0503554a1034010300c0e5850051451b4038162510107403a000320740003000c02c815440e00d8205100d40b0040000800d83c540a0340394625030164260000710303010b40a14200341e041d00e0145000740110307074a13048417a030b644403595160859440100000800700e842001d008401c000c590941d40e18103007044a00000f6201c1c25503022042035400003e200d401e01d0b001982a100c004000300b0203030a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 671781339 1250 671780089 671780101
    0x3200a110c040905032d031806011502030a081009020a2327220905060a0c0905100306081006060f0804030504050103090804030506040f0b010f050306060d06020909250503 75
    0x2c074010509060f071032922041c0401400c5200d800700c4040142d050840b55102d26002c00500f503200b441c0c0014407231031b000703403400482c0c00c0740d070041017640e040120380045161604048e8200c417443c42c010030f401e51031000a040450604890300003001190880d41d5114400e10321421400c0710a14698040000d0280c2000740c240030f0045401c8141965141c1100030b08685540d90108a00c0380c0050300417a010042605802c0c6070000caa401040b481c2d001d82d00b21a4181d40e1044400100c5200d20318400209a80090400092501402000400303010380f40106844d030380c030a55140780120060300641410389801003804035a81c0148062039070401407524000c40d00b05514090700303610550058a04040d1030754000424000c80404503001940e2220460b0300610746803c0c80460070180f501d00f1204078003800b00000f200840000074074190b6000402030949522490100941e81c480e0800c11207080d0b800380421303030785541c41c410014031420307001c40d0000209035001c500c44450031051486409110b414828045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 671782589 1250 671781339 671781343
    0x807110f1506010509041b1b020306010b0a1707030c0e0619051812010c08090a05030307081302030a1202010c090e04020d02030a0803010306021309020405010c0303200a110c040905 79
    0x2200005007405910162a1000100c945220782801c068215061140d214441503805040010f2003400e652112107030320420075075051140c0c1d0104080d43c150f004a0040c024803101c080104110802d9092121907001403055480049400b1500383c2c0c0481d550b4101d4480d550341085a03440c0b1130707200315203c1c0d00e4107071942104001d41411341d445404022001c80e0070600d490b464201d5500454009010034451821900d025011704000c1c80c0380790002d0038900119600620000b2424002c66101c005075080d03544400d012140a6030050440c41c03100381c90701010006d40c4090161002450180142c18804d4100b5a0044d0955207000c1070704081050901e402c0240c0b15005035296003099049a201c00d00301c042d03000107444d1440401c40600010400800001000403e50007480303070b02e01c18004485419034540121040703000724070905004c10020114600003d100b0b0340100c03407904e00181d00c0122450f8280c200511a0440407511000c20b030b0583c41c20703000803400c1050b018510003c941c180f0110700540e403002c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 671783839 1250 671782589 671782603
    0x106060c0f0f14070806160912062a261017030408060c0310090203010b0307050318010c0302071406160507030306081614010806090115030605100807110f 68
    0x30b40b51192610030b0750704010b4001030041407010540b00b260b42c19034840301c0703061300d5290544005042001100300c00c0c851900400f20081200c100e0b200110203804a61140009801c04c62400c03241108407260142d40900f0300c0420110300007459646580300d0b100031441c04105401080f6401424800b0b50411401c164031303000740e80a03100d000b129501c0480300380c0c090310b2a50096401035070550066030700700031352040160060342c440c00d030070b24012203415a1200904124442030003070b08000345003040001e140500400045400400200000807a0132054032440d007103400a801c0000001e40000313000c070a00c040340d20142d0340c0280400250010341810340c0320400606007001d070324052040109684007411301079800343c2d000305000429201240c14508901d0800308080c00f0360440d00803a4080d000c080d52207140043d104035405440800a642081d00c030401d2104040d141104054480c1c101240a403180c1c95200c202a0860301e6039142814220780c007034807020b850200b07200c072588100510311100000241c51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 671785089 1250 671783839 671783843
    0x10f0903150e030f030106020d120603081204150f05010906140604090b1207060e10020303091b0307050a030b090712030806040504330b030c01050904050703090f050c030106060c0f 79
    0x80c04950341c1c070030039007140592840710913520404000012002e0b004991282e01044940d5040da48100710702401c02100c102d800003400d0b1640c2800407041c2008070b403d99075002070140c1000300120502c90100019500041c8103c005680c0318001042215514020b0102806080a840301440140780c0882c1c10390080e03105d10410551911280c00d0a42c031205500c442c1c0507030180a8075040398840070060200b003940b00310f83e07019510600b0030080c81032010044d0b034014601c0c01c003d007110a00000f00424916441c1c1d241560500600000280d5607a441d0304d02e01c0158801c0c00340500511341103000500b409000d600a1449406090f800c60010364415090f030362082d011140055143c55030f0400d010760b075410f1403c6000c0b032103108603520014a062180d9006101c1010317000c3c4040917072076040c552150042c403042c0e404a0020720a1101c50710b0701d81c200d00d030300114601e0000f5000010f0b448103920a00c0100040d241030304040d0714050070703007020301510f0050003244c2088180801c2c01e80d5001283c0d00e0b00200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 671786339 1250 671785089 671785091
    0xd052407110606090a1407080618060f0d0309170601050a0506040501020613330f060f12210512011e09021b1605030613050a080c2a010f090315 63
    0x285030b4417440d40c8000b031a08448220054649810840a03007103c1c400c1d20043e10030207c110410800216006400e032051001900700600c1c5103509042c0701403860110402c41c1480407190300403c5000d9008190000d0040100042c111945424180001c1da4050780003203018180c204014402c6980005256070480351489948849001c6400c14100f02000c04c4104001c1c1c0d0003600841160400403407450b10401c5804104000e09070008030401c046814500c100c0e011070103115006c000710000341c00c41441c41c034001d1340240a5104503070f6016a400380f40300c0c0d100c4003041c8003191690040c144001c0081c00b40c4440c802d8007503a20b201c440d04240c00c020702d1080e0004c0640010304100140707207154503900c100c1041c008071504006010560501a0001e0046902a02c200c0300054101140690f110103050340000c09040560720a40b18402113511944a1014620424a011803c09401c010903c491042c1006440d07180c582d00000408404844440307204200c00c0f4141440803030701a07410352048685c4254 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 671787589 1250 671786339 671786341
    0x203030c1606060b09040b0d151112270c03100e1f021b0712020118080a06290f10030b190303080c030c1204020d05240711060609 57
    0x20300321032414005840201200c3c202100007480b40703402e80241030303a05401c8405104018008081c4001e050010101502c05034080a641c00d070416603070b0000c05d05006490403245040103c000d844401c0100717503280740030203e00300741200d4810300d84c0300c3c003e404841c1400030b0301a064200300007036038a01c1401005c41174036684490f611100c1e1005c01c40064108054014141200e880103100720080d004200000c07040d01c40254424210302d00420914140c512440181112152a0300115800c82ea0561000001000c030300001c12204010464030403868801c0101050302803200020b01600141c80d00143d062000880784030926a840c0041c2d41038507141030310007a42c8606110021000703086040c96968008443d108600060b01c001005070040d02d001c0c0c0ca584031036888561041ca0140706c211403424401c0b10038031500030742d40c4952440da500580001d2141c8110b900c01c0e224182013150b000e03110130f890414124440401e0019001c4140d200c1441d044c2108100c50710603107580c807080000c10440c440c0101d03130 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 671788839 1250 671787589 671787607
    0x7090e1504020715050910020715022209091a0103020f10140a03020d0c0804230102040b0c0f0f070b180307170f06060a030206122e0303090e070203030c 67
    0x541030b9424184c2103542410064401d140c2070b0010031040c0c900303015900416424450700c40300d074022528040c2d07200180d03da1a80c817400c9444000d40100d07009840c0d40c0d441f0860000b0708004405140c02411b1441e00c0094408080c0c5000700440340f02000900d5061400d10040001d80d44d038032950802c83d10143c5120380050800c1100b1620703640c04500d407580140d0045400e825460745035000d0007200c00f210a04000405507100203a170300340340841d001020048036404802080c143c001700c100102007501c0000d4101929000e03612000d400c510040c14050b485401142c0284204000d160300c0d050480020f410101d061142015091068111580740115104180950742e1001c002e01c500516001203c402d203505a05100d648800d021145807030b0511403c0d011440a190944698040b2907009200034540ba8003280d81d4640e4110042400601c00319012103d1840344508500700c1300e907aa80b1001500e80c50440c6030280820702d0030381001c2c0e4188900400c0001807034001007140d411144942016031140c80305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 671790089 1250 671788839 671788841
    0x60f0c0c030601060c050f160b2217010b090c090f0118060c03140a1e17090c24070222140a1d0a1712010e09010507090e1504 55
    0x15592038042c4100c01c0000f07040c5500450760003046201304250360b4007010300000b03980d98841886480c104a800b101c0c00b00304070340700ea0340217105400c0315a03100b089048030f203a00d02e4894840741c2e114007105c4e10364000f0007050b44400c0c0301e403080c80001180d241c011402d050030071000300d000d1444003600a10504521111580c02088c03d001e1644145214808550300c0720401440ca082d00d240450128144000791240c0c0c88444e82500c2940d01182d4070085490200c0311034040c0d2060b2841a40c050085052031407141a41a0340c801e07100e100c1d42c80c0100034040310182840344034288070300141450314002d03e1a2041d50f058030300312000190101c9000c180814403169019a021900d01203912040ca0035030104202d003096040700740304889582c4100591902001c0e006800600740d10b8080d00c1c1c0d00840364000010f40b03651003802212843d440da4505000c680c0100b118607030000c0c0c02142d10024908104030295200340200c65000c1c2c400d141113903019103440309104410f40e002e00b00401c406c0c0305034664042629a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 671791339 1250 671790089 671790103
    0x2060d0609020409150503150a0531051603020d020609010e190603050106050304030c06110408010e01020c19020603040b07141602010e03031809130f0318050f060f0c 73
    0x90441d43c0c0c960f10801c1c0c0c4010325a09104c0b8200940715a0001118a800302d40c24010b006152507104840d40c81043c008014000240300e88a06528040719404007603122100d141c0c0360b820406000440419401c02500c1c01414a0700301c2c3c031039100a0010710040c0c0388c2d41c1e406002e50754103565542d103403071600d001a01e2542901822682251442c41c0540e0076886003101c002c00c45074191020002640c841038100e56521007210054003140643d0102c1d00050a260b0044040c86410611241000d4480940c142035540310040d180305a90041100790300c1080070b20504410044502911690078a59400305500303000041000e4050309101001aa503140100040003600018060300b82d5500b001c1804030411442c0c0c1c3c80305a0005040e5009144503060001c1250103003181c80c1105c1034018280b404014030990000c009400954800c21030000154203990581d084500c66180d00c181002c0b51a5401e007a4111a031000b03110300c182c01c0c040c075401d440e9441101e030310421a0041139a00c0c4010711034a498244 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 671792589 1250 671791339 671791349
    0xb1306200d08250e011211041205010b0f0d15060f091b08190e150702060118061217070c2705010e0609060a0305010606050904060b1602060d06 63
    0x41d1408200c1d909a000d0009481a10320556003500764400c0d41e020100448445040c0021611084100c01035601034010340850700211040455058414090615a904290b0200302d0b030060b0814602c040010a0040261001e03003900c019a0a0420306c0c0010040210580090075a022208802110700c1c1107400100c090982c0800360400d4540d1030710712030000e00801710030400e005102c1c2c2032841110311170901d540c06200c103082c04240806420304c0381001080d10344400b0201d4484c0c0c10307080310546009100c040c481c0e6503d030041c061a40c5043d0852143e041d00c0351030301003441d00d03000381441010403d12001601a400402c41100c040d801011500944036100000d0095500c041c80024200c01030201d810381181b1000140020003d500741e00c9082c2d41080c01056920744c43c5d80001000350405582c4668040c2c8020032160340e850780e94031101d003103460541203000004e45c0000c9204003403c3c6400351400a103a820203203880c101240051030828181228007e118401c0091035240321820f0303400c980c010706 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 671793839 1250 671792589 671792593
    0x1905060106140c030c0307020a05030312150609330a05040e0c2a0d090b041202040230180c100e13090204051e010608130f030203070b010b130620 64
    0x8500544031b50702d0f0003a080492146602c0080400c26090101c19541e00901714120200c0c00c1d200d04401c138a180340f062707803800d0700400700348865051a40c4031030384900c600301da1207007a000c00344042e240404500700980c00303031110440401c00000103540c400c00300c0b4221145044600003079154100400038a01c00d801006c2000701400000503407520a03100081da1060002d01114032059603014141c85170749007442040358400c0280010420101c81541d11011148010001460300054038101c9c0c450107a801c03801c1c00c45003164040c10029505000c4010341000c2c6014402803400300c9110441e41e82c901c80c014140c09a070862080310051801880d100740880001031481d4503034040b19580c40004d102001c82a4465810040490702e51000316020351180e1005281600440e800c1c80c030265004000a0241c9600d0308410b000140410540142120b010384030b03601842d5540d02d203080c50f8248520681005508900c10410100710541c240d200e00229020750030000c0388a1540c008104000c4041e0005031024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 671795089 1250 671793839 671793847
    0xb150a08060f010801050606070204110409020f0a02010c050306060a0f0c050d12151a13030602070c060809011b11011506031509150504050402030f1e1905060106140c03 74
    0x22600441e030070340728480341c4600c2880c513a6900b01d0b0301d00303841e02a81e0450700110100100e0005d0b05103608122203080c4808101840c090b030b24442c4400b02da12140010307022820116140800580c20300030003070902103900c1e1807402c40c1401c0b00040c2c0355200b81212003080c00000c2c1175142926000c1c07644081401d82150596030000320044001d0a0640c54011002415142800c0c0ca400301050129100585141c0c4c0b02480ca01e003c032a0310000c0b41d50120020381310705154890000006007460000702151882170541d262441c0c501503026216500c094440c0e6500d0b4100b8404000030b000200c000d1003090700c907191003401030490040c034600400352813110078010b45400002145068168202510b0084a80001d07211540d440001d034045440544088189101e941c4040040f40780c19000550007070300040c01c1e90171540c06d10b4a607610b44070a0302c2400d4080c902c40890030101041c01e02000112001c5d040342d070b072039020325035407043c0d12a001402050240551183c1002c0040f02c5d000c19106120a2381e000c407684c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 671796339 1250 671795089 671795099
    0xa0f0c02060a0e06010b030c090d050703261207030f09291305070b0a2a0b010504090308060d26030906011d070f180308030105030106120b040b150a 65
    0x2107103400c982d00601107052140e09080308034001030807412100c4030821a4156250245a003441d68084078499600c41180011800480c2c400d011b004011803180303840c0c00e030200950040c24a001d06007480c080c030b80c1da4203000c1a03c051120907400b070361207401842e000400400d0121103c0080c060f1840180100d2080c000d40d0340060809401b05e040e2005035800056190340b01c4c0c1d070350152403d501400900d00c1d0840a410012030509a010b866100701c9414203403082618070075000c0d007a101d000704400c0121298107004090048615102d0302420b0191024440da46031a100904001400340a81d03002e184034a060344140996100d24805c1501169610b050342c03015403190502d1034005581e040b1072030144000000344030f002103030700101c108605040703c0748a07070381c0b4001555a0000c40c1008030038054110705006945280d40821000fa5228901e11a02ca5040c40c050508407070243d0014040c8458400350180071801544000b41d1003036001d40079400e0342d62070904a000588031148a250441c5400c100421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 671797589 1250 671796339 671796343
    0x102210103060b090610030903090b0703020c09090309030a0b0a021b0601140f0d030503040c0b0f07060e0109050a080d0605130e0f160501050a020f073b0a050a0f0c02 73
    0x20480740540e038107003c0303900060104910a201520640d5011b185030007800072140c020340010750418000c0c20903480300340c0d13a040d080020b07a00540f012801a0410f4907940010301c0c006803155000001030005504040303042012036660703a807034040600280c8112000a031029006c0d011070b0103220811403a59540256a08407960b40d01c03003801200c10141842c0800401820980c50300d00c1c0490004100003810610390b107058038a540042c0043da1105403242d030102d03180c3d00410003072903605014900c9680d90640d81c282802141c035043d9012502c1d9042c00d800b00c000c00c900041c108540c07900314124543d2800e2240f80c4400510260307020070b400110941d0300c01490341d132540c80810002187d00a031407180c2485916142c41d4485031840d6031105655000a0085500c0360003e4000d501083c01121036142c10303891840e203040c0c82680240fa40f6040400030200307401c0d001d0303050890854996141606a4001862503440d03100062941d11003550741c10016228003c2c43c1c22140c840300603508c00f044505003000e030081d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 671798839 1250 671797589 671797591
    0x18110a0807080106031104030b04060b040606270f090209010507060501090b0a120203070b0a090812090a06022a0a2112051608071a010f09050f010602031b010221 71
    0x1e0003048070740000050680c001d0148214103582101e07802e141500710b5441c0411400090400e91f15150f907504a6186c030f03250340c0701c0c03840075050355102d407448102c00039000002980503c1804d546110070740c2003000700c002e40803ca101550311608015031120f034a10300480f0b01e802100d40181999091500000300d100495110710351f02c00e001c1e2800c2c1c03d201d445442c0e203241c1d01c112410013509a88078250412508003050080e10200c000b919080e01e00030b5985052915040300703610749810244001070b0f0110305103006044900104107500187c4201d4150030348003605094060408440206003030f144509940d2070644003805001c044220744944400c41d5045c0d60b1030400c02c2c108460354044a0700707201147d4080c8080d5403d40182840111008166944614868200c503100b125003e02801c6404104180075844034040c050700c14018180d185001000c0007078440207085441d0790800c030b50046c804a0b50100032503514006072090002c15500c55105240248191485000180c41c0c040b009441c0f888001d0101d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 671800089 1250 671798839 671798851
    0x703050307180608070810080a060b19080d11070e130615300807080a080a0c0f0503100e0a0b010e032b0903060212060315010602030418110a08 63
    0xc0e01d60a40c011a84900b040c07581d003c0c0b8008500c440002500c181d03c6502c5140e03105003000310b10280180da0341d5013549002c84d10302003281c8543e100d04002c0600d0400c070060503910020391141c09495860110603540b6003007000748902c200311a1160083c64020b0030131114004240410b160000c80c68100c00280b00004402803c0f01c1c01420200c60300d040340010200c0c1420f6420441d021499040d0041000510386080d0341f07820060310501000d03002181e007820140c0122750240042e566200b9a1030741c018030b9070300c00030001c910751761406601c0d80341c9030781c04041c0210888080c01c1140da6915840c00c90030303000d03442da44071651011052040210710002a002044505000e80710300914401820405455410041801c0c1d110240c07005095141031031005070f02a9030070542042000c05840381c4880041c0e030f0042049403210280c003070601025003003c00442140e00700384d1244040303650400d4002034480c441c07449a4031080c00c03d03d0405416521070350050910750788803020342e81e03a91044400981000070071206 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 671801339 1250 671800089 671800097
    0x140c1005091501031e02030a0203010e030a170112110409020927071a090114180a061d01050a021504060c08060105160609032006091c0e0d0203030903030703050307 72
    0x70840c03a404850681c641030341d44c0b00c1082081c1000000b802405464805c90903689813203849503520140c2c4003845041d0100e81c401003d50350310b0309616009055150200400491000d600c001002080059001700845650200180d0039044140300000c2c090a03c840c03010b503000b0740f0142803045d6414221003e9402500302c100c08003842140d48100c0791501950311504805c0203c0161602c4c0e25800310008214100c4141407030b41e95a140c008101c00036410008201d05603924180c9a07100034603058030010003e018515220390a00000c1d0000740c94080300030b4140d414007401080c0c43c003600c0c0c0207015040120101000320441450700d410100041d0241c5c0007090040350038400070030b0955105108591040c0201c0c600c01404050700e9a4000003000814000e80c1000300400c01031200087c00701420741d000c1c0181004010500388220594140384046191489500d001610850f07400c1e0000f18000a0983c1120b180c0300000586c00481d00318414100319070380c5400300044040805801c4000b031030180816540f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 671802589 1250 671801339 671801353
    0x40b0f19230a0b03090708070e07230901080411040c0201021902070e0f10050402030a0e0c0406181802091303020f0316060c11011505040b09010b0307140c100509 71
    0x290040320030a507500503070815954403051214030080d20041da0000f07030041c1202c41c002d645100c40c3e4103000480e0004400d843d0300006200d03007158801d0031101071011413079030001c2143e06106881c0061090680d158107106007400001d081c80700040038107844410140007442110b001000c001e000b0340c004104442862020040845641c1c40000c1d040e00340c2d14103031904d2071180c0315030b622130890b680c0040c00d1a449200949003c038440d11180081d5003d4014403001264000501070701c2402c107014100042e01403481c0c0482003002c0700b80c82c0201c40d94940248400120b0701000040e000490740040310294114428000744214085500903210101d4001e90036505200d0780b5000841e00d0388618000c100b032031905110300d003010507201c0d070014210320101c1c108840d182110118007420b481d000c009420381814505810029404d041c022420382c0c1500311032101c4503604210100845c0d000150204040080031800701c40c1441c4403000b2140220401c2d011100811805e44180303014080440f0322045a005980c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 671803839 1250 671802589 671802629
    0x90a0b030f0d140406022d1b040f0c081812040323011407030c0c0b040602030108100b0a12020d1703011a070c0603110f03040b070206071805040b0f19 66
    0x1c4244c41c00e6070a1507002e010181c503d03440401301506052100841480c94071000c2514010411003583c11b81d40340001c0d0007680d045101000300301c0d035a004803044001d09004000c050558060b1100e5404001d204640d0340031020346005070300c0c144022f109019207000c005030120902510003001501340b404c09000c8404245044421400e0701c40400d1652a400c9a610100700b4180c0240c211051652052503d40c4403008152260301010742c040d039095400715800001030007041c5c030510102c9900456040144000d00c103502c04500a0420380c8079820402c00c0c10400f010856440b002c8041390307250451007900c000c441d407a21700d40b9140c4c0280b00d1240100000184034040911020964015a402c1a1109040c07894041c00b034001c3c008000080c0840310082001c00020001d2708080d602480c090b160003480c614000c00c0103894410082c080c4800e02c80340c0c18040fa03586690284a00c1034840984020540b001c0341008603580601c24007607140d200300714242c0540d26007810b41008084554002c81e100c0b082d0085 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 671805089 1250 671803839 671803877
    0xd140f042d03031b06090b19060501030e06040b0a1107060605030607090506180307080a050120030f041b050a1e05120c0d05100207260f0405090a0b030f0d 68
    0x24403009000ca9072003403501091a110300404d0b84000d02036030740880c40305500e9540c0c4406030340481d801650811841c0b500042c0c4910b03885a10040c190070709007003044181408803655100c0b8001d10061003105280300241040070b580d0080c40813819030030f50003a29420649410350241c00702d4020039020748241800035892521400f40f420890750054415850315400c0d15002c000500d080501d140c15104101001400360b40c1001510034050207140005040441d4400c04e0342c40d401c03120045140c42c4014000c1c000500007440116800580c8623240c0513580c03506502c04526008540d220301d0344005400800a21240340140d40031100c00130031444c41d040f6031980c0c00c10840701581005001c0e182d01a1401c0201c504003407029001e0340380542e0407200c0c00074100303c291082ea40810411a4038162030100c050329891a1a900103c0402c08041c060402d000740c407a0b030105010758401c0501c40d9800d40042a14484107502500007484003078207032100403032410f01140d41c0d91440c400400001d0300304101d0054140310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 671806339 1250 671805089 671805179
    0xe030703230910170a020c01050c210a060e18150705090607050a0204050406090b0f0c030a05071b0305031008010212070309170c060a1a030d140f04 65
    0x660040355003800607440511900082c145911420b00c0000e004c9545800c49042e5814030501e500180541d55820984186081d50401351844482e0107092208450000b14580d8240ba00c03045469820f0303107541e40c080ca860180400c0d40c4007140c810145014040350b02c401001d001c61508181d8101e4540307116444aa04140038100c481d080080c2042c44200351601e0121f0007070800c1e030b000f50300700c035508071098001238105c8000f40c80445c2c5035a41c40310300318200a070760f58045500070002884200c1c035203401e105e0040c07544030051124078520354610008004034021a10b9201100400442804401d031510303000d0300b0b80e80252500b09001106880015141105008540228281040034061511010820740c050000c4280803241e00c5070b0007114030301c0030443c103016001340007915009244074280b00207600126144584402c8001d141e0010030781042c0c1700055803900c1040103281c0310b824004400d10000f09170051034811401d80c2c0c00000c0000314400400413403051084031401d030010700c45c0d180c6c10111061032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 671807589 1250 671806339 671806397
    0xb07060b0f0d0b07030f020c010e0c0a180b0112291507080306010c05121804060b03060d150e010506031015140406090c0c0b0108011802061b010e030703 67
    0xc070780030b200780011000c1044940000e201c1c1000702d0b00c0403844144031b060b03801211200c60340783e655031705000c289403040004221148054034110105803d11000d030201d018000046c550060b120038007005264030902c903588030346000e900200281d103d0061135400005d556401e00301040c030780c20b102e89a94905189103801058040c00c1652801e0000e43d103050542d00014001c80c14080c03a103001401065040c00b1018501c204019a640d90340042c1c1c40c24100ca5050031441c074010b5183c40014444166410116500100210f8802c8a8a119440d069842e480c3c812002003c00b810b01c01007400043d015000203000d90400c40a8910800002d034112040322682c9800042201da011800c0002c821707000d041c14029580039001080035030b03c400024090f2a0f83c0c1c1c41a0700040c86181e0b541091100004290703000d03143c0d4400034001c000c040201d82904490900000e8410440011090801c040c10400900c0c030b241c10700000d00c00c003024188a5030303e81d04140c9044c0e004c40e01c020141a803104400c0100481a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 671808839 1250 671807589 671807599
    0x4111203030c1b16030506040b1b040302040e010603150c0305090c09012c310c060e0d060516120509150a0915060515030c07060e03070c0b07060b0f 65
    0x15024803e01001c0d1100404248980c0c007039104a00018180415008042c500802c0105003908151a0031060390f03200070a0410425040d4150146d466111000c1750201c078ac0455003c6040001210214010902d03503000a116a0000034200a40105ca03000b068500310701d034404004075501c1510890f181d12031924015400004003005101054500b00420b01d41a2806141c0b454480e58030820440c8481c20b903064101c241f40d80b460010aa0f60b248015011100010080f0071100316130303900c0710180b19140c0120810302004a070000c0d10f603195010340314803841d0070100c1404242424019203210750b10030410000011115428180d0340318250144500806030000249200d10b01141000803a480c0a45010021901e40c0340c004081000007000d008901041200001d0551404040104171070074007480920680042c070401c00c2d25403c200070746000d103400210200e035260320b2200003400e5206080c030007032000c036400c1004110b4116800c00b900615101d0311017040b41013046410000f9141e0032000c1c241c0c3c48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 671810089 1250 671808839 671808847
    0x70f0b04090e030f0f1306020c09010605090d02040f1b1e0e011709010b0a171903020118030305070905040902130c180b540904111203030c 61
    0x60805503200403400080c030302c1500c2c1884803400300c4105682c0140c2950100c4480410450b09000610444c4001001180010020305509002241819805102d99420f01101080110703940d21107406e1020302c56802070007040108800c101000080c0070341c40325400300224030007540c01c000c0d002c0e003201c21101d81030540b40c0e44211084c00040b2000c8610641a0703042140340c1040001141101a02d01e00800b030304c20002c035441d8401024041c0000603030384413049800c0105405481d9030804290309500307043c03883d070885903800141010717170142410b40d8400080c08449804041490350650205015a032070366107a0320120360b6001040b01f981c8800c0300103540010b091031100c5c41640c4a62050300500301c2410030700d00f00d14882101c060703a000c59911181f050b180008029100c0300c0611a4406020500e819103a1459003050207041420300c0342891a03410ba1008070902808480101e007607541d104024a0b4030050310303280c034200312100c0c1110200c50003002d10401d100c13445007000c4281c1c1d103d8000741e06043e0034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 671811339 1250 671810089 671810099
    0x1005190207150b06070b0115111f09080f070804170309011202090f040609140a0c080613023a0519021c05010321020a03080105090a020d06080c03070f0b04 68
    0x3403d080103290341c0800200158000540030064042c000c00e4a8410201c5940314a0400307001c038003103510442000c0e0070200d0354001c05522088202d403c406031f00d00018800314203140041c150300c58081e80c0041444042440b4040040f0032000f4070940d0301c5140c4182403e80061031683e80e80c0030300c0d1354070360104e05c104450b0b81703442e551070340074007400d02c5d00510481802c040394011408460700d54101968440d141d1406030a00d030344c468250754100501b09010402003003102070007130a049026001e54495041201c1c401041c1e6a150140d4058104501148414114000690680c8041180001d2048140c100380225140701071040c1c920172100d080341031600c022441c10321b200942c0070290500e8030b04200316446a00c0001d40c400c550117144104029080300a01c0210081203100c01070360340d400c550045080400290344810228111401581c03522500d40302d000381d12002c0d0003038030704aa0f03007545840d1380098940f50006584424200a500707442180d6181c8910101c0c060082c09602e401800030402005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 671812589 1250 671811339 671811341
    0xe0603030417010b0a0f210b040b0402130f1a12100f0905011401090605060c0a0f140604030c06110f090f040e070308070203010c09051e12100519020715 67
    0x32244180702c00004010120000042141445401c0840c0d100e559060500c10301c0381c00122020940f01409102c0d03440d580e942c2d01c00740310543c010700003825122000e01203421510b40c041a0f007086280d42d001444040d00c8143c640e40200703440d280d60030328040f00e0a10070070141040765110000c81094400782840343c1c00180c0782c0c00940060034820740904d030b0314200d41d0041034080c803815044102c10343c425080c1c0e51410a800080e0b40554011038402d41040240305182d180c00202c0ad40705540c0b010001c0b000841504040988445296044c040d03400340c203003040109584480c200c404207208040400002a007119110701a004000c2c20308018407003009400a149054003443d1441c21000700081082c16400b162607003820460392086444450200f401011894280100715524800b8035002c000d0b6032405000822040c410014060380c1c02c01c1000300c00b520744034401a01504065103044076402011190220000c4c5812100b00715001d5031103001801c11010743c001c591400b5045554880d20001e2034148070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 671813839 1250 671812589 671812619
    0x60d0f0f0222060f080d02070e0a11030106170f100b07060608030a2105040213020c072313090302060c18130e0c1008010b0703030f240e06030304 64
    0x1030780c4001003000c10b0041c0006403210741140d290a10002c030307a59180c8089007440d07144641003030130b464001c8035100001c280e000820300100c5016110004140d214514410010180042c07100404075000002095407034004c0003034030f00545040e10082c0c1d982c0d00c5112842c0c002806030b446038000c2c2c0300e01408206010060001d800d141d4020480000c3c65503440090a2544c0d02c41e0706204045944e50b401540040150a00d160344076a0165041c80140780550010b10300c0300c001d50401e905d80d54041041c1c040044104410005080020030180364204108110b00c0350028004445104018100700f410502e25503000c0d01d0511941900140b009403203100303004216800c440d80d440b031030112100c50700c1d219135240000c80c00709142205000a4040c521000641001c04a8027107600901f014007540d080242e00c41c25290442c0d000c1124651a61090303d0700300c000d07250360159560500d040500e800e1040c003000111860100c1100c8040102d070744d0f50f0640500101003164055416041400708101581d2140204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 671815089 1250 671813839 671813843
    0xf0c030c0304080a0c0e070f030207080915090406080c06070f1b120204140f041101050c2a27070905311a04020702030a02090c0909060d0f0f 62
    0x2490624603154103031851030700a980a8949584669212014000100c0c0e884000e44401403092109242400303002c0c050040c0405424100350b400034082082c4072036041550001c1344010210300c0e0380810650002e0141d001038512078413851801e1000101c0100c0060498540c3c035000d8140d609140860312061100111580c090b60110014055102c0b0380113046608001780504000610005015005000403104c200341c8017168221010b081c490641c2d0400e43d4a58041d0740030034001988000d5078012a028010000c078602980b03d000c00050004040c400118506040c04103e1203d0b1a114001c208029101000c041c0031034039003e80600b03a01181c444c0031036000100c2d0804143c0e2a5807040440d6a0704440e6100949040114000f040000c1c1c0c0ba0113028030408144500f80702c469a8a11302180448000f4910f521803540001c608045440c1809680089030700140302c10050700d01448140d10552020345164810709e130101c0007801515100f0b4101b41c003550406801d50100490340c3d1100000c081007941 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 671816339 1250 671815089 671815093
    0x605090a0518060f04172a030d02040f170102030105090c160206070f0309090614130e0d0f0e01050304081602030a05010c020c09132f041d0615060f0c 66
    0x1100e4000300700041d030700800c0c00038808101450a0f0800c0d403a0702d0100404e86d201301c541000b1041e03010304800d07034849628141c0174007a420420810105031540c4100d0180e081024000728002440d00690344595040751442c04a03c2c180ca5001c2c030080c1d00300d00c024062141d0150030341020404103145400900032000300490309411a130782c641c00060507a080b11808440c0102000c0c1c44c00c0415501c460031500800b0840c505001280c20101d140102d451585170362406045800f000c0c21044565802c100784c04060401692010326108200900303024102c101079000c104070b0040480302d9441502180d10494004d601141000306a00e1004581003601c8010703a41840741030029030105000b8801d04007107409640080000c140c02c102400400c180090105071440c5c050f00c0e180c00451607560100174564225500c0d41e164030307114101d01a1640d41d010314280c01910384a0768620f0743c80022011211542e9a200b00e4100b0f565046200540c0b2085030304040e000788051000c001c1c500c10a4014010720790301d000c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 671817589 1250 671816339 671816371
    0x1213020406090507110105090d1115011401090807050a030201032d051f1508091906022503140307021908030a11070f030f17070806030f010605090a05 66
    0x60305941442d0402400c9980c3c0310140114a50070100343c1c00112984c43c020701051505000e031701e0319050003902481c02d0012900290030600d001b406060307030518100d09121001d5842b00368100080400c11308590104c2d030f071502e0208551400050840403902d004104d0420035080d17a004401421103c1807180400b1700c40304030b0b9281c450f01d2400e0080d41c0595250005254076000b03501c00304408141400a00840f80c2c107000744a8002c0803650460030064508003001552102e80e40e9904c1c00d9000082032000050607000002040007640040a65207224881d4030b07000d0303540341ea0740080c001310082c005012031840311014070301c0030038103014560182c11401690b101c145c500c0786d160f403d1001d2031011984200c0004c00c01403503811074810103401c02c9000e21a0390402c0c0712a038606000f40c0d540c0c000a414009204842c8400a2080140507112400c40d4160001424150b901521310711050b20241c1c4280500c0e003810060340301c1441441e04460008240c41815101ca44d45800181f601809488072160500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 671818839 1250 671817589 671817593
    0xa02060d06090e0a29040602070f140139080403030b04060308070510060605160602091002100b010216090209060d060617010e04020a030822080c01021002040b1213 72
    0x44249101e21480b40c0103019840c0191a20601300b1303005d030340e100e4040360207500382810302c2034048455039000b60702880042ea03950403410714800c24043e5040c010803900e40e292580603a03100c1904015100e00800c40c0728028410001c04403002220400b0b00d200c0e00c1441c820118140c54030038403915812a000e800c0024000f0a400007003010b40380190401e0310b24040000c0e0745800c101d410030104250b840c0a4104001c07660a2900050442c401c201820640c000b103041040e00f0b102155040318806000100b00030305d03402e40401e020307441c3c2c900200354403141072914911700000c3d4002700740b04c910404181c440b404220709060074113000303403c1400300c03d40010040c030440030710170410320456014142a4407001254580d40c01e00100e04d11050b041120010465014000142c035440b030101d0582c0d512012440d181c4600540c51500c209112480740035551001800144000c8080b48426065130300380d0075030f00708481080a0409903c1180305518081c2000c20114a0940e528410580c00c410703284031004d4000159 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 671820089 1250 671818839 671818841
    0x1103070b340509031c0504050d110d06060510030603050c01030c17100305070b1606050a0216060b04231b040902190e01022a0a030f050a0201080c0c0a02060d0609 71
    0x40840700080703400051611268a000c1003103201141c110b2000780c080c0d01c0c00b03100050450240340b00c0c06006240d8030520b01d0030811103600b00c80310b141016180445082042c1010409040329101b61405050210b0784414200e121b03003e6141629000402440040c014500440007880f06004010270402054044404407800110340d41c019819810845411825800c0040c144081c5510151a1382d800700315002480701b039103551103070840d04114001501d0761864103c81c040e204003070682514040a001610400c54030b5800041c461a0940c0c04010414500b0a040c101d40340102c200c0d0480c401d20800649481a0152a004900101c0381107a003081e545980440c113980106a140046000d415032468036940e000500d030345407070024402010101d040c4c01910781607002900184682c280c000b040e040440d26101c1200c1d008591015400440c80040e003892600d500c0501d41c1240000c03a40360100c0e80000301041503032800000070b0080c0010440c5035080003d00e61041d400a10304c3c0d03403140c80c001350761051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 671821339 1250 671820089 671820181
    0xb090a05100209010206070c0c030605070e040e0a0302011506050304060b03070b0d0b0103150e070806031603030203040f06081e06010e040c27060e060304061104080d1103070b 77
    0x149a41c0561290542d00002e402c14000402090070422803445d0280032039101800b03401100c0c1c106000180d40c1c6c84d00c96086551102c9070b10316540150034138004000280d07002420702e40d001d00990003009650441007070117082003028071400700028001c0c000701e0040344080c0c4c4102c01c0610010100c41c4d9070f5995150b041c005030010140a0015561100041c000303580500400404650f00b2040c0c19420342003546c03104020785d01a01110810600200041103510b0030880e010300d0300400039400508aa0f06d2a00a503a540913015038807d01300440e0000a4050148110034052801e0390154403080f81580407002c0000d0300240458100604101410999107035407003030451465041c1e0b02c10030b048000d109041c0705420422200540e00425070001c001031a4403a910b401c80030401c5440700d0fa40d0310b56040c19000b400b81440c40c4481044001070000b0804000151180303401115103a88030080d00c40c280391512070180e0340000e0202400600090005249030300031814032100c2c02507001440208821207a41018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 671822589 1250 671821339 671821363
    0xb0d05060f04051002071a04050a021908070b09031903020a150f050603150a1518020a14090102190213050c09041a0d02150f030a020711030a030801030b090a05 70
    0x81d065081c0002e100c1c0c01d00030055030f070355880015440c00086584d00180202c01c2500039010100c400d000c1010894280a004031a03078000b069100944642140d01c5c1400b00c0c603100c0e1054070310400100050a2000c80165420410010060320f400e49907101e07007544000c0552011030443c018bc4c0d03c02e0340014415000034080303018485c00014050b10068003c01290005008580f203540715045070ba24442d40041480da11000d00607000c0380c2d4406110908400d000c03e500450342c24002010502d41400165005c2c0000350882e5442032029130f04100c0700010340c804e03400d4490058021400b9800300805605c0f00b400001d101901d00d0010009003580c000031200c0681e207560a42c54000360b001958a0117000726035071507840d00080760156142070300081281c1c2c02c042000740a0b00034810b6241a41c94010207940803501020031a1703549203021102c000095001a20031110808400403044090a00040341005507a06440b0b0754060303421900c400007031f2200288003540d58810101c1403400541c3c20f00008022071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 671823839 1250 671822589 671822611
    0x302150403020138061c020f18010c05031e070501020c07060e0f0a0e040f020603011401080106090b03070305040212030d0b1203130614190804030207090e0a02040b0d0506 75
    0x4694900a424001c3c109004002201080441d0030a4850406100c1413000341103500503600c0d00c2c003510550103a4804001c49001c188042040302481c0e0000c002003480d58400c3d0701a000f56450540151401074034444050300c541c2c828072803440b4914188445480e007494410f0190700381409540da15080e80e000d0910f00d0011740002c1800c000c05074201700000701c02c5000700d41e912032281040c004240121038521440e010304150704085400d200003241082038080c2c01401c4035035a0b43c0c42e9100035003900c40003040240014444800022454400c080d030000340d6114a15551641d00c4000301200a024054000e9902c030101d54040040e602c4100010240080201000300742ca508000402c248400900c2d950102608100038500f80d807050100b040e42510204d051810010a580b00c009190340204044003414051165951441395001401188554030039401c5507401c50b00d400c0814241c801c6e44010b5011030f030020b4400401850143c2100b0fa200310080e00505104c86540c6030a490100b00340ca2404040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 671825089 1250 671823839 671823851
    0x1031407110f0601051e0409020a0b1e0f0a081e010602072102030a021c0b0703091407030c060e0102100203010e010f080a020109090203060f100503060f15120403021504030201 77
    0x2241c00d20480c202890507102802c050b6141c400815880004181c250000b4800700303103510b0701962198490181c154001e000000450348900c005802548015504441c00700030900b050502942c0300210740350780d141010714034280340341b6240507240c865028045038111400055001e6952a04448150081019074014042540782c290f00390b1b80400c00f02501740c0b00719080024900940c03000645c0130a82030f816100000f0819185d1f0300013000081007800146980c40c00700902c01d203a9455001100920f01039400001e040c50300d07a42166480c1102e00c8014070186a620080103190300804a040b0300c514103005851883c0c404061890481e4800d03041110020080d1006010118203800000c014000000090101c3c00740364001034000803440c42034512858002000600360748405210100c020710180100301588803918002e0041e0b0401c0300e0440c0a00007000c0d100341c4a01c0c081058200c500001900903260215a184000480341c00030416030a61080150380215417801c0380346148624001c0d0700000301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 671826339 1250 671825089 671825117
    0x1401090608030403020303040e061f050909131a0a020706090507080d0503071b081c060302090c07210309050a1a150f010f02010612060605120f0d0c0201031407 70
    0x11500c080d000814039900030b0100344010380b000400c40f070551311a1010f89005a40b0718000440d5104001180c44039142e00d9040f5a4440d078010000d80b01c044411110b13600daa42e1103c0108000d007983c0c643c05407080200014013480313488102e01454103d40446009450501c035078450400f694a01e54003202c65502c04801000040d8062041214a80301c034a08145541040703440100a14170f000141001168140250400c0214010403680182e80c1c0071402c1c80c05032030202044c0c0052a02d8401a030003800307020006240122903104956490740d0000c4100c00312648450342d200c2d000e9800342440c003810360769012a00480c50400034400c0892003401040f00c0c1400c031030803010360703610058810b0300c030a0400101851550340300d11014104501c2840e107a010144407000480c09000c42d60711a0514030070640c00c00040c00002e4000f8401d442d8103070740c0c4a01d071b10142c00b119640c03140340d40305070429500292180c0038070a20600c0c40c12030300d0340140750101e500524800500350301c6600780e0b08074000c00e24003101c2c0d883d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 671827589 1250 671826339 671826341
    0xc09090b0907050d0224130306150b04051e190308070623010b070c090c02030c070515030c220b07031b12030917160b090106030c03080705010f140109 66
    0x740005880c0304ca408070342503002c500c1d10b40d1010280320b000821082c14400050481c0e00b5100c0e10171440c2d10314181940c1c0c906200c00204103422182d12860b44284000c160360344400100d070101c6601400c901d848010042c1c41030388004080b40480d5004035282001c00030f0006000751031000e9401116a0b81ea500f856141050464101000900700c071510f0030704486040784c90385603d0f41100c8080c100c284d516280da180c000049146600001e80c41d9190404103c40340f58000080c04e0f0000c2440201c1d50b540c2e803140c04001e10b03909804000c0010101c00c000244100018201511503510f401c0a4074940b5508040c40c507401d40c20341c1e0045607411310089a40c000b4194001c041124031411a088050300301501d840d0300d140b20440881e107100303154440b01c6c5041005004120144002100c5a145403200b02c400b417804008203001c0e00a869080350780c00820b200034810300c502022260b100e031783c2c5102d0303510b5031f905ca5030290445002601d55560b180c0c0040c1c026129802142c0c611102c442d1485a503604200f102c3d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 671828839 1250 671827589 671827603
    0xc0809061e01140d05060708061206012907140a031b1110021005040506071e05030403180306020d050105030d050a17060a030f0503131517040c09090b09 67
    0x10007000d40c0c0d114020078507051500168155000074035180c50140380c01021030f07960128114024010312a100c10003400552003c4420300400c0708903039540e0041141040b490b41d0303060038080c41c10191032030a6000c08414402c40119554003181c8034860802c14942c58030108411401d100c140180c01902c1070a040580c000d62181c40300b03040194507903421a10f07441d0100c0d812001c8004a000d104400c42c8110064002c004141c920807004000307020f0382c0b50500e45142c030380744d05881c6400404c0c414840424035200404a4000e11200d540d661821503450741c400311050160303409490000d00c5524000b2010410500041c401c90a801002040c5945042c0030300d440d0184c060400001c0020901003070b224a640251408100c510700c0f550f48600d42c4840001072030700c0106900051a08040001e42c104010010024016100c80781c884000c0165540034400351049407110030303100140c1c061018a0380e0191402e0400e0b085130081c540b26014a407503c09242c1110346243d01607403002015010007040e184100081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 671830089 1250 671828839 671828851
    0x100e0f1b040b1c060902040204151d010801081906021b03071203061203080c090603090a03031410030305030a0605060a030b040e12030402060318030d06091406150903100c080906 78
    0x20030030390b03601c00006828580b4011001003201e9105c4ca4003100395980c60701a90050550036210141c94101d110001c0c244c403414600e03a020403051000d0440c40c0750b0098480f03904030381d40e08010f0040da4440004034840c008092004554241c1d0038490400b401a90010318030a22050074005c550b60328060425240c440300c0d444a803001c0505008040c0140c508090501c1c0c109681070401d01000d460f915034090042c0074a2152a800820110130041d542d0b00000b03101d1901800307a1010403402c0d011030308440306111b00b1a0708005078504000b0810000c2c2c0300e5001182e001b44030850002d2519107900c00900507505c00001c0c0b40c0025110400a41c02c1c1c03919108030b150f04d5080000401c207444804a40306180c0c00020f00107445170711b000c40000ca0f0b80c0902c030700c410308403a07114050300e607600000e658100082401e070241507600c80c07410b08400c0040c40040501401800c0c010900088003617298040811548012110354042c056030f18010f0300280a40640101e0150b56103a07901d40c0e180450425140c00e03402400303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 671831339 1250 671830089 671830099
    0x380114030d0906030f021210050a0b0703050406080c071703011a0301081c02120f03040b0a0c02060604020d0b030703050a1b0315020703200604050c010c05100e0f1b040b 74
    0x9194500750b0040d141c00e0450b003a508010030a025049004802409502201c0031419901c02c01c000c5a002003d80020a035181200c161052176100d0304100306a000f506801004964100418041c081c0a826a940e1103080380318040e15021303040d9145000e22229124200c14a1030110042c8a40260002e6521a444071010310500b99850501e25513501c003c2154990004869480484c19452007400054800640c00110035566550003200d1025580308039020754030101e4960100340c00007140c0c02501119491b990007812940c0703481041100035404000440d101a0b0b986040e110b0640b400c0c0100b40c011800b813800381c1072088403404c040c440001007440031488801409428400104107070a00c4199001e40200180c85400a180641d00041c1c41d03021810a403030b039a002c540d03031450002001803156110b0710541d051050f052005580401c3d00010040503508540e011081e013945651104c0000403050084460340d100c03030b5249504129400803d00819a01d0381120320950a00e8080c02d04124000d42d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 671832589 1250 671831339 671831353
    0xa0b0d060e2a090411030f060f010503280f0903051215060a050708270132090d06050403050301080c0d0c060305090a08130905060d020d38011403 64
    0x2400c00e000328a20790656142c070030007080c110b2840d19540c0c0001c02001a401410b541d0713007006120810410000c40740e051080c0072200c1d01d48155440380342070340d01600c0e115003400d002803080c0d90003448081181c250b5850041d91100304000140c120300448200500036140c903030f0348800710700002c2e02854004144180c415045688500c1c0d84d141c0c079089840b401410310b80b01c0d44981c501e203407606042c0303e51440e4180c0300c01da4448071406000004190401c43c00246c076000c490f000c0303151040444c0081c0701c0c031401c91440711812407000c40100c4401401e000c0d0000780307034040d02c02e0b66582e0f41d03040798400d0b5002e80c000340011006100c0b42200b041014844203048034010750f421460f64a0404802c1e0600425040540303440100b01e00c0c1c1030802c541c54056900106c0503444000f0201404c22001081c0b141100250810000c00c94509280c80e41d001544e8014001503100b42c3e00341c40b40b041c115804510200c40d02d12880700365001c014010203080001020440548943d45003003c0b070001200c800b034480f071103030308441 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 671833839 1250 671832589 671832631
    0x62703040b1b070509010b04061d0108010501030f091a100e0103050a030309031b050f160308090906030703150605040b0306070c060c0c080714190c0308090a0b0d060e 73
    0x5000ea403030b00003011011141c0d8800c10440c0300d0500c141544034581180d04030001182030592072000c0c0043d2221650340708140740100948804111103a00d485010441280062285521a400c80e50900c85500f80110340e584040e502c0308071410a0f001c601505448980a108100b0441c946007001400c400c0c0807020b40c0e50450b01d031161180b0b44400014180751b5500c002400300340c041e1010031f50380000d0901c1248009414100543c40e582c0005502ca0b0300d00a02d10b548110014801c902c00a5a80007400141030020400500a1754140900b040740e00d032289500000c00100c0b0b86060006e01e006048000c140f140c41d000c140026075918550803440303a04100e0420103a107074407040c8841036540041e030204070070310001000d4501d10074000010348082e03c0092444180803882401d01030710701718002103801400c40081c1c3c8d1003107568118002008407a40c55810000311349220081c0c4010f5070020113002e040e42c0c1d681040110381e40403125080f400c03500c0d0361081048400102816038070621803d20000707060f0401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 671835089 1250 671833839 671833859
    0x200301030204200322050a050c010909091104020d060e0405010f0b100815010905180f0f070504181503051f0b131a09070206090705040908032706270304 67
    0x615034100083c00080003020030b0391921294000710b80001c15541c001e4481d0230719a407035404044000e8045810b108000600a80a10407064029004007828841e003913000c007000003941c80b10003100e841c2c0b500c0390008100d0b41c140881c0c170307070045114800000b020070500541e0b6084da079407c84494428241c002c290068240c00403103803a031110045003104440000400103032003001c25604803c3c0c02400c030b803078025105070407544101e00406211490054035a2503501641020740200d5000002880910080101003800344004003000c210780004500803601e51249000a15140e20036106540320100c0c213a684c54071441601420070f114941440b0030404000800c85e6003202c0010681c0301daa4528503501c40365522854440201c200519003280c5050041c3d0089da641000d456002c00340c082c0803c001424a400d11a17050641d60003242103065a5a044c0b213600140f40610104d0002ca011080721502148280710341d9105004109040100043d070b404050300107424504456000d500800080c001c000003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 671836339 1250 671835089 671835091
    0x50a1d0a0209011b150f0f1a030c090702010e2a0108060f0d020f09040b01032d0201080402030307060e030d151d070c150f0b01051e0309012003010302042003 69
    0x13160915810044940c035182c028800e40700d4082c1c0245141000300006002c554202c1e072482100b00c0c00902a0f00c00300e0342a2250300000c12a41c3d176256108414008150034040b0110368004914000010042101c503017860406d500c056403c2e008280340180040c41840c04044101c0100080c6820401d03841c0403800b10311010340e0151824410521010030a0440d502d00d5142d002e580c43c05406801d03d41410f150642008900303020884081002c0710300d46100860740407080d03c1101103150500c1b4240080e0b001514480006001640c25000c2006031a002c40d0190091101100040006650b1400303041d407010100e4241c503820f00c0d0709002c5d84e8001c002030018410348091442005268004c0c03919041d0f4240c030081f1105100500c00c00c9000c84d03110034016160311214103415601c005029a89010004540500c85c4401056804e442c003060080d0404c006000b81d03602c1a40c1d03c00014240300c02804400d0400403080003800000c1e4001300510071400c00d03008120034284540116401e401d048100080b02d400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 671837589 1250 671836339 671836367
    0x61d0606010f110f16060e031506060310120b1807030f08090607020a180c0305090a14011d0a020a05030109170703020c0d050a1106040807030605060406050a1d0a020901 74
    0x142050543c0086901030011000c3c0860020845060078001c000b803074900782c1a849240045400140f04c0d04041c20080b40322018440007880c18941030f9a14001c000281d000581b1030aa5100e0000300030450b0641001500300860184a00303400610f0640000b8cc94006003903200d5016422030070040000030164280b010040e0f078091003040d00c54210700040b03441c0c0e015048010758001220341001540d082200c5034002501d4400c0310501c014413004805405494054440e1015031740040070600200d0003240150225540c60300010a40500440c082141540e00c8031001115400000520b41140742c001c3c03840004100940083c0b001a074151249102d1a030000c1c0c200287c1003000a828040510034003c0411303121006004014020180c02d09a5a0300310701c1e0001c42c0c04172544007801d6903030710b003480a0700e08a504100060030310f0790850f80d0300400740c81c000d84840c1d00715448050101c1c00d642d400c06000050950520201c81410305034010030040c007005842c50600c03a10420a00ea410f99100c0406101c400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 671838839 1250 671837589 671837597
    0xa080c3306060c34120c09020a05090108060a0905092a0306040b130204020f09041d030a030c0306032337020d050105090309030f0303090601121e061d0606010f 70
    0x41c1c6141840340030300c8803560001500e22a03582c1d000c50480b04a00c0700072045e5000300d00d0005490f4070b803145a4201d1041c144030401140d000d00025000d980300c1c413a02e5601c200c01902c00c01c8425524008071068030415600314541e600715014103001004507220038504018400c5250408805a0300440d0325000c01500290003040e00e0700025203542090600745282590140003155506110703441c0a485400c00f02041e84100e042401c0112421814070241c00e4240e8400040c619003101c0d04801c0d00105030401103a001e0603128140007000c141c02c1d8410a18010702846001e00d1a0742081601e03060400c10300201d60350407860304c100e1001c0c000740c2d0036030415450180040380c00c4000d1070001841800303466100510b6982000100300f181103002c80600744850040c4c0c12a04000c910b1030165459000441d4400744d2a4401001000108061204200030901906041030a09608181803448114082003611126113442c0444e0100c100103c0031110000c07050098105c0d410200300003801556901400d100304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 671840089 1250 671838839 671838883
    0x60d06020304020102031902060103061a130b010207050d0803161404090209120a0f0b0723181503010f0b0301121104020d0614030f030301080a080c3306060c 69
    0x40e4000c00c105c0320020503001c4d144807d80b8007850020740d00d5600b400125401c1c0e086c00c0c50b104c1c514000f0550556036180082180d50907643e54207420380240390402e0200e04501c124840012240c803200400e54009000b0340c5001e56a20306040110b82a40184100c801000f21514a2800041000c0c0558007034a100850150741c80302a20b00103030721070700300c001e100b800c500445202100300905000024a003038400c10490751140e176141c905690000d45005203100c899020b5006522500c45000100405e41401da211621044076201040e41c58081641924889a0003c010b0028030882c2100f00c1c010003012140d1481c641c10111641c04c02c0100304001840c0c00303285410102d4607910f80c1c043e04c5080010f054100001c550300c0d0103008424116104c46402402100d90f001203458012084034180c8540000034101c0c140710f50742e011680c1c1c0c8003411340360060050b00b01c84454440c9465503075005400800c107040340b88000c20030100340076602400c2c00384569030807c040040140040382c03140e410f42220310110a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 671841339 1250 671840089 671840093
    0xa091806031403031801020f09210111121302060a03020d0902040f0b120616050a09031205040305010c03050103030e01140f280323070210060f080c010206060d06020304 74
    0x506025000201810201030382200c1c2450300002540c4145c50b05044582c2868941000d1400c074030a1446254034803000300305001450600c0074450010b081c000031201d81c220351210600b0f0840d800d5008c03511451400180801041203910b26554004080d604030003011050356000540c240b08150601c4181500410401701e00059940040580340e0003600a2128080c11103444e0020100b200350b00b441150030110441c95000000380d140d1003100c0c14240c81030f845a001c041a551600800300c4402000389040700440020801e00c0142c0d010203054880c41c0c3c030380d410b500e060790035143c0400c11841014034100c0104080307544410f030b01c1803007882070904070281c0120036096800d621030303519000a807400c00191280128842301d405a000710241c403994000a031035450480a540c01c0490241110004211071414642e00d040b0070342d0001454011100c03090039503841601518001e5000c3c4105d0296000100070508080c040c1c6041e04400344007500382e40c540500041c0300103000d0034020380469130210010701 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 671842589 1250 671841339 671841341
    0x103031b0f0302100f020711012109060911060a020601151b11011107270e01050709180e070b090a030b0a1b0e060a0e210a0b06060a0918 60
    0x40032a4000310400c0c1c40c1d5049040103550b0f01c40c2480c440e844103180000602c00000d85d4400c0c0c584465001c820150340381c00c014011121009080d07541d01403211150200d0300260718520602c10154824140400c40001034241010644100e1010a0250b4404c101841d1419400315020741540c18016081060410000b012600044c0c400c0d1030181d8003107640e00340410b0111280140d880320f2402d076202ca880b411465400342e1510001e2145160500740c42179000c204815005040f500c1402c44d000000d0300c00c41031240030307080d52416200b1801155860032709000d004158405440c000f0001e150622600c94008031440d906d4240d84170750800c000000c200210380e5a50380e0074400096420480552441c1000302c0c0301d4000380907618251203030b00c2d90f03001c070510322a00841b1004c1e20b2120040c2407c3c1405601e01c010340d515501015044e6026960360051b0b5007030107015100318485614000203000301d410515142000200c040d11042c072548041c860b5104040d0710021190584000d14400306100d00c4400e1014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 671843839 1250 671842589 671842637
    0x14031507021c031514030a060f180b19180b04020a0f06120605011b031d0604140f0d230f0601092703050313110d0f020109060f0206010303 61
    0xa42032811010414019410b401c007140020040c00b9104c2907031340d00d0040b804140c25101c0550f4264101c1e84646002c2805a4400c454030f00c00013034089207000d81e0842c0343c1c0c00041c682030121842e80d04101845403803140164125240c80d002c0904200b0403444142265007400300310b0000b049411108009411501ca441c500001400d400030403901440d21042c0180140821401a20645151010005840d803041842d841e41d80e414008540301c2c0b980984080760311400c006008111600d88441907001074491000400051500510322603aa1201d001000100e0101100c2c85104d0b656071007019011406140759503014500c110710307640c46051700928050030020500c10142c041e000d000000180111190840000c003a0b0750488154071034818050030810822008014001400c1030001458450440d0660843d450040e40114491080e940002c0c1440508800c00c90341c01558400b05411941c114040102916660900a41605aa00009550792014800a801c2010845a408002d00119030316 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 671845089 1250 671843839 671843863
    0x60e01120303090b07020d0f080c0f0a17010b04090b03010203090303061c0507061e03380303040f0905060a03030e01030c0c05160e0705070206300a090c1403150702 72
    0x1841d1385107408000651505c080c58400c4010030f060781d051505a0344500500d07480b41840400c103900300700c04050107040b030340c1110000c0c000384403180581e00f010410885480b40281800d4000b0707075480b4206500c0070152168070300000d01030382c0117000b402540000407040c3c035401402501c0042c4c084c0e0804d41e030b200c0ba8468140d80a446802009004200c10740c2c001a6090208040c28450845104007035084040b2799681c01d10801c406d584040c42920210301d05504083d8028400c036001e0300d042d000c0000780c199801984942004003001c9820800360206010b06580100c00f04d0701480454690b460203842c505041c140c3e181010340e03910741089240d00030140308103100d802504807240403101d810303402500304071400f034620001140d5001400e0306210302e003111503255000c2c112506216004560144650a1200f5504550113544c4407150941c14810914850319070700d1400720b00350800341071035041000b064014250b0680002811400f54500185000c41003040d503040d15850f68480400301d04200801e406 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 671846339 1250 671845089 671845103
    0x2040b041e05162a050f0f2107080304030c08070f05010c0e0a0f0302120f0631081602040e0d09031a2e0810140703060e0112030309 58
    0x1020316012581e122510910006003000c041280440007550003032a2005030990b5911303150340110021028a0860012030f00c5042114071011051080905000d056020812194000341075441c00c3e020102140700180c0b03600b050f1501e40319585d118501584801800541030100c21081c1c001000b01c40401c5400e4142c11010b040030401c3c040c034285020745205040840000c0115945902d546070444d0b03030f0b070b00720b400107000815810301e55400c0c44101c40d100030a0002130b020f8510001541102400b2940c403810f10b1108184000039884010365404052400075980740c401d40401c0800900140c04546510350712740d40701d020318a0f052000a019041121038403506001c0d00c0c1d462041c0b1500441d401c010340b4400c240303e604205405803000a00701c81190041c0c0e07040e005444415a251358025455001d1080d04d9160350fa44d071716090218a0100181c3d0344011242d6100c010150000d42c40142c0c0780c20400303034074040c0901442e001011460150602918a01000074002c0a007014001c0e130140c0941580045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 671847589 1250 671846339 671846381
    0x1a07020f16051e0a091503020a1412010c08010b0f1926040206070f021503040b0403140711040b06090405130209010518010603051504020309010608010f11030402040b04 74
    0x1112210100c20b2040038000e0200b03403989202c00d001c5241d045603042d000303416840d51925006588019080c20101c20040c902680b0011001d80c948040400250003000001d60540c1007072000d02981c40e03600340ca106d4a80c0d140070b440e0045c840c0d10a522a0460b4842e41d10541c44a5040c981c1d420075100b0702d4944c030791000f18031800e26600f5411a08184440c8401c0b40c0d0101c1c40212008284511181120000e52090041245200240e031100c84617a0050008c1e0129107944045001d0010540c010b540070303203d03003040c2820081015400419008080800e1216900b012100c0d614120716242b403e2400344600e407100000140c644901c0b0942c1c5405000034010f12007400c10080c160104440d42c0802d038000d041c2e1000100c2d103404d056040d120907095021036203007240c0c45d01c0e00440040038064410308448558808010280e5581d0000d103008141142c00025141d2416039140d086540e00c0708090744032820680360900c60060b1030b095030303441901034070041504401400050010f003030408641041e220503c13 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 671848839 1250 671847589 671847613
    0x90b03070206071209030504030f2f0406050a0b1911031c0c0305060928020f030708010509010b07110a03170a18050d080a0c0501020a0f1206031a07020f 67
    0xc0c0306800703074401d5124100a0714401d00900d045e1040e10001074003040b4200300c1000041c103402e0080400c00e01568403d14441003820307040031110031b600140c40003070480344501101d918051003010020300d0110b450a00052030300320155464041c03102d50304044139401c498862843e0203120440e01001c03611041d261b44504021407119400942d103d24440c6510301604824101c3c001d100b454003540c8d005101c520a42d4036880e4001800a4000c40e500030b14442c04406000f1044500180100e000c0e950481c3c0d445e880c00d10002000910140d11851260200000410001c0e031041c040b00d1603107401444018072120303218042400401e030b82e070000388041106260a00c00c2031142c03001e464200c840303642d020304101c4204500a1402ca050290715031000c4c000181500144825000b8410b050b407504202c01d0301740c0203441e440e0882e084141c100022840c42c030b0a00d00c80d07075841006c2c0d05220b80281c1041001e1820f60b11008110b440200e0140e010007080004030741102e008120f11804400c0c520700301d401d508840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 671850089 1250 671848839 671848843
    0x31e0f020301051611010204210303021314030d02010c0f0507050a32010b01020c04240f0609080f03041703040e01090606120e10020a03060f09090516210201090b030702 74
    0xf02c602c1030b0014800e517600a601030418001c03035088440390342c014130b8000129049065401e01c0721104405140d400c1056011144101c03000d040188888000322504002410a150804100c9071201d802c44e4501103c0901c125007094042020040d280381c481d03116801ea00d0301c10f2a0060885e00039004059400300d1500510100813141c4080280715003800340311142c0490607007650082c05c2c1440c05a004825641580e0a02d41c0c00501030070140040d12460b07908082c240c00d01c0e4016500200c41a18601c04107210a07070300b04400b030000b085058000d1103d90490010240c0300d004a0041c40050841640c1c6910805002c2054501034511030310a10495651444203030300500040c4200f00c00314000b4403d5442101c204c0c4248002c0c030bc918005410755581002c9507000940c80903d008040c10358842010940148164a82c40540840e85001a80d040d003030402516100060718000b900e410488414080c03026441200d4001c800c403036003500e49982c240d10069891004580220200d000c007c82040161540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 671851339 1250 671850089 671850121
    0x130918021206101e03020d061803170903160f14060c040801140112031404180b090604020f0d090614150114030106020d0503090304050d08040906080304031e0f02030105 74
    0x1102000b54a0b02daa616258602002d0a000e84e0841c0110322600300054104880c1513240c4600c641000980c100400460407203110000c0d5040c4c00280700032654002440e4402404d5801c600c081009508094842e41880208004031074000d09030f0144030100da081000c10b0031300c071140341d045906860f0703589840c0c40700c0c01490f0001d2041026560a1209900020022040380c4d27050b075600800f60740070f0120301d813002c0d140e030100d07403003203240f0044200300000b603005050543d401005441e01001c51440720a004014040c040a00b401d0300c42c52040003240b45140d02071007101d4044034030000114079801a070619100a100c1081c1310200f0181c04d40c09c001500311000c0d2038030a8000d090702c9214140d626514590850f0009001c0d103c0540c0c02100d030111090301810145034800d039036404491400d5200c0c1d002c102101c0e44504201c0e01c800d8041802d01030008140500005041c0e104011801c06255440700104200341402d220240040c1000b6a0140007012200030b0503a41c01400a12050400d000d0110749006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 671852589 1250 671851339 671851351
    0x2102041e060603020a0e040213080319080a050c1909050a180c0804260702030307030f020706050a080c0333010f170c0c0f010e070f0506130918021206 66
    0x101d400d0001c60142d010340f0070f48a0994060780c50626421110007070000035030117585607128607552500300189004042000b440c051000070059800810340380e04c00351a1417405454031040f142844200022940c0d0700c800e54540341a10707240b8086c401e945400c01d03220300f400d41c1c02054001c40d1040c0c0200c0c0e03540e65a42200b2104404103000c002c20000c2000449165005070350081c0041076608007020304443c5008480e505440300d624240c980070955002901c1d56120b03d00842c003007921078881c5000300341c05001040007800c1500b080ca00d0458903250051003c48028014000c000d00030000c140754038411800380c0380d1880060600e1440c0e040c07400c4010011184501414001642149403500452080520b04100700d540d4594505540f145904040603030130003001003840c2d10601c070070f00040a409000e80100090b01001508420381400f122840075481c1da00703c0d81c047ca03070402c811000032856031202030480d0317a410ba0000e929800c0c40c810b01302000002002a40c008200342100344030031008642140038503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 671853839 1250 671852589 671852591
    0x40305030a0e0d020a0311061239030703180213060302040c030624050c160312140d0e0304090608060a0e07060f05220e04030206010e0c042102041e 65
    0x2c0c1d800c1c400c002d15000c000c0c3d002500b05420041c00c1001950045015410904c01040b250402c020000c002c0300040044545c2e0654140214a41d050021480a4985d084002100d0030001284041c0705c801c00f444060803040c2003607941c00b209a004040c1c9240002000e40c000c22021103109a81400c201910080c0005d074440c514041210031103500030b10481048405400d0f00c102d14000034400c0c03007070100c9103441c40001d2003405c2005c880705020512a1094010685641a003d1400c60a001107071582c4c5148030001e00c107092020300382c000e140d00107464a0250b80b00f40401c403040d80403441425401103500001a090800c50003152540d80860001c4c03040070607007401c01c0342011003180c040d40c4000ba84030302c0300480c084000504810f445803009060802c0c0803803001d4008070601c1d01d4459418910351000c0b682861210a00042541c180050ba00424911014400b5400c002c0e810404910407403184002d55209200194251942072a031008040e80080c0700308500a4034030220320f0b0300302642c0400f803032207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 671855089 1250 671853839 671853857
    0x15020a03050a0e07060c15020c030d05090c0901091a04152111010c140601150305090624010c140c03101a0f031c051803010b060d11040902040305030a 66
    0x644600e41c54540c3c1c0750000c2c0f5075540b40203019901c15a0420054483c129400c03990011811030303000030140b203a90803004640e00c04141c6505170850b8009420398103030360001e10030001c00b9520114040d06544459100040d0101c010030309102100d614003140d42c1150030403001c00012404501c0a008807072205601c10340c0b41098600f040000550940002e05d0007a0100f9241105c0d449500c042c084940300300c44803410210b51131042450140709900c01003c0303c2480d008001c2c030a03850301500d600040d0b03190082609040010b03091500c0000a51141b0100c01100a0360b510781c1c0c030170394020a40c03d4002900220710562104030710344a851030340d0164000d1003800082d1411814500c1080542801040c441010f818603100300b001040058001e1780e030502c030f90a02c0c1014030790360b01403011320050192034060303403a002c0c42049c21401100910f014407a926144c11107410b602d82100b250020445e220f00098010f14012560410303010303a1700014131003031000ca80401085030002c010039604801d07031201e90103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 671856339 1250 671855089 671855101
    0x2e11090907031a062a010c020c150d020f04030f061a0d0b1816080c01140f0306100c0614040c1505180a080d020606010201110c0c0d05010b04240815071b15020a0305 72
    0x10320550307500c00514000100311506080380680e01a080371440e024605203001d030340307803940051003042400c151203c1d9514401740c10043c600c070602d441601c100380c45e90303000c0c841c5d503849018108100030b1055146054100d60400030030401d0000c0c01d0801a03c00c106002c00b41c641d11015503c40d1042c0007140441c4121a01454803d886802e403000350080022051442d51024103004600c44113003016010300c030104100e0000201075025081e6450311000700c11075149014100007905031402c3d4016080c80814840f44401203a2000032200741301d4034040d044403203440c10380c0411a15150b1358020380b5a030107a02d00c1c2140341680422024060f0302e090307009000d02c3c0341094402d8481d11507121f49440583c03180203003d0060501240c0c1da444940600c0c000104c0c2280117010400399005c0241c03505060440701902900b4a40d040400d00141040b03400912220550700c440541110001d0000760600c400e501520700000301140c1e20b40c46c515881404406010343c10440314020350010a00c2ca00404e040c0400501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 671857589 1250 671856339 671856349
    0x3110913032a12080601090f0e04110a08030403140313032a0902040503190308240a120212010507022e11090907031a062a010c020c 58
    0x102034410300c0888035648100e55000c0d1605051120700c0d42ea1000c40c84841c0480220006040140c640120802d003940503400000034603650000700041d05010f0401014000c0b00c40e6004268151001001201d50540300c0d82420210201801c04042c0d1215401502080d035002c04005401100c5c8203040d02440c03484001c680d5038890180314620050509803040030004100c4014142c0700c0308421420088000044161000400106411215910342c00003020080307801c6c200501041300e4004244880403801c5a94020700190b00505010b60754000610f00324200c1c034002080d43c0300300c10018844000d203917030b90810044400742410305038410348014001c0480c00f4010b0080c0e5110f0995a405005201d0860020411903030382c1101600031039180020a000075055882002c1513082c217140710341d881b00c03104001c2041c80003000b0b00f180c04050810001d030b1071603101000400442c1108454003900c4003841c0e500500c04143d4581200c02c07031071080344140034205040d031100200248984c00c2d1000c05440405003c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 671858839 1250 671857589 671857591
    0x1090204080a06020a1b06051603091121030a02060109050a021206090a2003060910080705010c02010509130e0d022b02011e1b1d0909030f040906031109 67
    0x107030321908002807220004032254000c0005c40307075a040040d011070b13841c000c00e00c1d80d240c500401c880d82c944d03034014003250240b03101810b40c0a144a02c2c2c1408040d00300d58a00c00414460010395003c0c5441501002d204581e02c201c40302400b41d140200e07030f140c42210310300a50f07426083c881e50001a16020200e0014451402124009010030b0381c60003580d11140103101501d0401080080c099545030034000290005415501ca0344103000c02658603801c04a080200005001e0300c07490408510390b40410400350041121000c8803400d0a09861003082400182c41071b10680c050254800c01030505a801c002e441c0e17204001d110b454404031a104494042c0c00d0307a50b5a00e44159000c2c92900c84a00c0c0441c0006068900c64003005100208800d044012a13102c01003500581c0300020342c940c0c00481d003a9510004544130a0018508400003104483c2c90002c2e465050280c14003c00d241000148031000800440b07070903207155068295601c5d6661890350050249000444034112034403020221071070445151 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 671860089 1250 671858839 671858849
    0xb070f08130f03080703020d14090f06060102253201080606120402030102070b091e0a080f07050106180b090f10180f110306030f0a05210904090f0b01090204 69
    0x28084402c42c94a06035040c650080903042055020400340300f030501c040c058500e101c40c09040d01c050600302034030f413141001d20030410300d000b42c0d101c1401c00040b80c1c0e00040103450280720703400009828005c11180f031442c15254104042200100c0c1c0c554010801000f42c41381801030f005c104008002120004448800c026a2135a500240a10a10600410610005800500c010001860445541d40c1d1184565044804809582100411040000c54008685481400b00d0b018050b03010450352070400a000e9150440e0032001c0102d2410100035095010b48043d0441c001030320740001021ba2280c0160071a103110380c0c02010b070000800c0d0404174200c0d82030300178050b80041c50040d074148149004c9405001650789031490300c2d1210071085c01c540d441101700403000302c409150382e480c001c41414070380080c07506d4490a6034030180d15030b07010480200305880080d0700d6151001c044445840d1003003403406075611859100380303000000010011003001c0c1d074085501c140e014a400740e0781c1d103007120b0480c0607500c90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 671861339 1250 671860089 671860103
    0x4061d12060105060a0e03120310080703020d0b0405010f051501031514041e1e062310141605060106020706020304140a1d0105010201050603010c0504051c0b070f0813 73
    0x500c4145003c4001e030510680901c0c0014603010b1b50700c002032410700307a0001c0340101c00c00081808004034410684002801114000340801495603011507522800400003810640303040b00401c08200c42034000e000520744000042c0300e142004c0000c4802d03210b000c507006001c286071402c58091001d0341c4001504540644020741c0c0c1d02c00303401081c040508507a035801d0321000180450a8407000180c42180c84900e10050b00c0021522000c904c4800c41d00340707811080c201c3c00341c038104003044142c060031040106426154400b00b450490015a020b210403180309076085070104070032400325008105554464000c5007100d02590341d0350340c1070340c4801041c06180011713001000709004207000c1e12251800098041c00c0040320719a148082500e804031681e81d01104030584004100541e07090060f00d40102c422802000b1360035100f44054814442c034425036014621a010b40d5200d1410240b0441c9619041010900d89240409000301402e01c2031b0001008103600e40003054075442011145c0241542c0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 671862589 1250 671861339 671861341
    0xc0201090b0d02270102010c031a010c08040801060b03040204051602030d11041701021206060a0e09040503040b1308070819110d020406080703060f020f0a08071404061d1206 76
    0x15420105900041c0004507242d000c1001040410a440c1001104c07541d81c07000c1c60822102d00002801e442c1d02800b14800c250600d1250f07001b6000400da070b140742ca0001d003810880149a4944a80c180c025070340170b03044035440c3c00c1001403e1107440c401588142d02c200c0341000346070343d190145840328001540807401a4414489042c500c5210344c4503650484400701c072a8281aa070b444180c107070070010040d411842e500820032038140e8903c0394840d0b800070400c40b006401d049008074000c1107a0741071641c3d680301d4107220700443d0603c03030f050049a000e0201ca81007070b9a1500d010000c02c00a000da4460680e451095041c0062074000124515400041c1c9425070110b2003060307203c81e00001c244130702280d800340c455690030700140e650344a400028144034024204091075410f00808881c0d1180320101a140100a6440c0202ea90b40855007500500e051040d0340c0d03110f41600329811400d241c0c8600d0320780030000b008034805411035a101881051142c00080800ca01028020004060000e000155201300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 671863839 1250 671862589 671862599
    0x1c060501141207120b04050709051302010f1425050a030801081905060604020c0115092405030717070e0a02030105040c0c030c1e020915040e0a0309030210050d0c02010f0b010c020109 80
    0x16031440e01b02e4082e808031a0b0441e02c98800004031b42080c3c0da1075500c0c0801000c8101196045009202e43c0078050070206036100c00614810601e20803011401c40100301504040410040c07080c550031015046412540f41000c68640a804441d080c080d0444034401e503c0c00502c0610118070000010354030401416681d01d6817010302c0047d4020b0010150a9500c500603a2402c03400c10800d84000d0144000c0800d41860321403000d020055001180309200401007810b000d0780d00c000841d00304a03103842050b045070703968400800d820f1400a410108511401c0c0061014446003500594141e4504840400030802c0d0a1800d460190540b4401000303c2c1ea000e11401c003041c40d901220a2824406200b40181c040c154002094a00c003290a40195648a402c0d8801c9080c984074060408003050028941141e0343c0c1c4028004514510000f0711400410181d0181c0301e1080f811740711095645e250612030140f8001010f400303083c104c100107400918140c450800ca40c0700b105e048022503010784604020034240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 671865089 1250 671863839 671863853
    0x4080a03030921020a0c05010c030e060703021501030c15050327010b060c010f0b060306150d151d150a120204110406020f0706080c0301051c06050114120712 69
    0x151043d80e40b542600101040800443c0c41818144441d5024101c00ba6451a00101e0010301344c2110b4104a200e07141c480009800000c810b141910031100c403034507401d803403038101c0c6000341c50100410780079214000001000a42c07040842a103107035050b45c00b046010131764100c4090100700c401e00c0c905800e0501d9072030700aa8800500c10490745010002c130784204c14601240059010004480640c1e41d10500c03007140350070b68030510b140544201d407191b00e50305200b80020300948031001d1100d0351107000142207008019031b038400c02e52440c0d201c8000246c5a6900303c004560307a4248544c1c00743e2058800090205100b502248040d0340b0010074107282a82012004169041901422600541d880b0b0301c0c01c889070f542c54050f2006000036401001c84424001070181000f4a540c46a800c0c030031124203002d1007410303000076241501e20603204a822100f000d460300111806000018103840e01e803400200f80c41e05103042c041003a41c010b43d0305c01324820384135a015a80c0c55551140c10030910318100000009102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 671866339 1250 671865089 671865101
    0x319031e0c032009031209010f05030a0603120c1e02150a020c120319030209030303071d0406170705010c02061e0d020310050f01030219050c011e2004080a0303 70
    0x34602d00069580c440005418900c009100d00030544980483c411000b85810425480c00e20a0000034030f060040c4500007a058004045400703040c890084000381c80d40e50594450b100860700f01301994516000c03040c0160048822480940300142a690f01c5040c1d1800c0c061300045c52039000e00500b0060140125032601904501001c00c01c50281c00c1d0307104072544d520040c440c42c00354000c0145030388802600c4140802c000c0c0441c1c00041c1070040c01100c000d81e80200a4a0380040142002c0070966025922a081c1540c0c560800f60f000740f4080700072079050828101c0c03c0603c84a40c044401c80c58445005555109501c00001d5004c05d041003402040280780b40402640c011282084c0e08110700140c0180aa804c00c40e4402da02c03044804040120340b41002418800d0346081c00d00b1490082e400c0078421102c413141c202e520502800095210300c282c0c0035480b1500c424409100c0c02800403541c0c81c0c12002d0100c1520b6003d030181c544400c0142003d100c01103c08407900c6030018021001182e80980c09000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 671867589 1250 671866339 671866361
    0x30702150114010f080c030604020d2a0206090c1509030703080a0c03020c0109150305220302060103020a3011040606170108190b18070303020319031e 66
    0x1403409044004900c129198080d2039440381600700c030075006000418801c94a6140c00800038144240030108120030210398102c2d605442c0541d9074070030700244070b004d00910084000030450303a184100e440d500103401411004015802d0f40e141b0344400c1585a6104144c4400a42c048904841c5000d000c1c40c910007031150f43e00140c20345800c5640c0e91039200301c43d01b003800345d0404100d20b40056410980e050104045140090a091041d06e00b498210040b0704030070050542810754030400300340701d0481c0048140d6840c804020000181c5002d02c1c2c0252201c81c03c1c40100c0c061202c01e00041407401203207401c07010041c0d2400480300302c43e024036501032420001580685803100e40d11924081ca484600480d07015107071035140c8030b000082501008040010513401440349070003640b0080348010f80741011003c155000150100161142c01c05400d04800c3e01904200034411148004101f64020001d054150840395004440c05440c000070390580304408146055a1441261180720541c0c50b40b200340d806c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 671868839 1250 671867589 671867593
    0x80a111b06310807031502040f0e07030603140114250815030102040f17071503020f120103030f021b22140a020d2702040b150a03090606150e06030702 66
    0xc07100400c02103440b15034214100380d401081051051090038940ca0240c1e11141c03e04600d028a07180c0103640030300a85c01781e0609807c000c0b0200d21a80c5c4a604908041e5400000c0707040d0070944514468000c10075010782504085803100015003c0001c0c90500420111001640321000c456410032140d0741d900810210030103010b004c00114a44007440588082c0c0902c00c1c0d9440369500345010303d40214040318100300d070340c1c3c411901400b8694104d092280740c00c100341000340ccc075a01030503410380d140c0c02140c3c0d040a1940740640008241035000c040d05054603003a1b0252903032001801451810704a028a0254004005991002c4c0c200410142d030964503260a01c001802e0341d190380c001c0c056090540702c0240c95500480c0e44200c2c204140305010564144000303911845000c65070721912106030000181c49581e50340020222525a00c02c5041040d134222076165036000a0000603005003907211044e211246440c1000c503103a05500e00d01c040d81000760f282d00326101f80e0981040b4a540c0007e01100440c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 671870089 1250 671868839 671868907
    0x901020a0f260304030c060b010306080a3207051309020402160209090f19030c141b06040503061f05151b060c03180a080a111b06 57
    0x400c40c20659401c00500c1100114044542c0c0c210000c480c0c40c1c503040300d0b5554030b420414000060b801a805a1082d9405500450007803a4080142c0040c03c03035074030940d035a00490002204104681da0110507104001030b003086038032429105203403201509403500d50141e0160383c0a01451800c0031210f200b05482c404040340301801c0f54007003001d0707802040641035044c01107407200085252054003141d22040c00b800502ea02400e04032090f5880100124005044410601540505100306404101240c00040f14076103681c81c079803095a036060740059540841d4807000c0800481c6019011101160401401460961600b426141c502901207548441d644541c0c00c0009140d150840c14444105100b640e040d120303500b00340c80c030040ca40024043c03289908148201705070043c04d40e00750790b005511000252020030040c2c442503d03142070850013800300c102c04549010b404c1d901840c0149011203400a43c0c0c085016200310344401c441c0303c0b821581c891814058099021215a1810048041c5852100074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 671871339 1250 671870089 671870093
    0x7060b060708090315130204051e011701180309061b060501090c0e030f0706140c011103160c080904090c0e0c09030d0c0309030201030507020309040e1f020711060901020a 75
    0x140380d100440c1201c1c084404141d10143e03103020b1152807007000414803004081d141c101c00b20015444c11240092040b5a1500030131045507a41c2102010003140800295803540c42c1e03164400030344003504a881040d8200303ca6440c0220060010600d402d9164032070b01c0c1c91a0a00364192890460219806008880c1c1040100400c00341d002e440d0007424000800140042d001d0402045012100c00c0c580c0030b984403419425124800003882c1003107a030305207030502c081411120788030321900c200d00240e00c00d50309040003504101e0340c58005501034028030795812003114000f1410f81740503000d4200940b041c0301c03c0c01400c400d0f0900e41c00600015202d003400120007500c407030218008080a4030101c0e502400410b00103c181401c02c0030300d8803054282000014804142d0f0014261501c41c0402410075407500f0115445600800c261040e24100420611a1001c0c4098050782c8461085942c4a0318440481c0e0100382d1082c0e01c202e075070040e044032481324038461101c00d004a070b500181c1c00d40d04501c80c2a0b01030300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 671872589 1250 671871339 671871349
    0x150c16120b0c07060f0f0f02030c0a2109121e120e07080303040f0605011e120201030603020d0b071404050105040504020915070f02030c0a210203010e030c0a060501090c1407060b 78
    0x504505c468400045546060b06003004444003684045000c510401c20700c0100700040040c1c0e0442000d918124201c240c403c1c03030742c03004c09959002c1e94050505101c200010084404840910844907079100388600031449900e1a240080d90018400320704141903110f402c1056070050018a0f030b0b0311040f21b55081c0d42e1502e4a14561084409132aa07000c83c000823810444240200d500401c003140c0c00e4400d0810001c0350311a09002c510801088030710410740c00086901075040800216002031142030b00407020b0501c2090300c60100c8001e4001001280d03882010241042540c0640e001031b9190341c142801d007018400250320414a0561002d481030401c0d8402c11008001c10410b803103102d03410400c54181c810325103003a20129a95101c3c60b4011740c06c0c415807480143ca859081051140d40e51302e860700f800400d004040d15420b080090000007201c00326000c001600f250018881c9500704601c0c0c0e40c50031140115040d41d445100082c041510901070440510081d00201d4020003001a4544140f0000f403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 671873839 1250 671872589 671872601
    0x403090b0a02011b020706050301140409080307030207020f01022808071e060b060405060d0203130b010602030c0601050a08060c1803010f0b0f091b07050a02150c16120b0c0706 77
    0x1c010f0391101303030415144d0032400c8000b24402d528001410228185070b4040c220340014010042038641d240c8407003411744d0310754002942c0c0c0d0707411941a9980303003480140140a5408840c040e4014081c100b01a90154400600c401301019000c0d0326000b104c985001e5822080f415901c2683c000c0c00a01109003c1b600d02107403400441c2c0e10010501ca0942d0791728100b4281d60350b81c42141e108603001d01042000b44c4a050841d0010040c690700185d4139074890300102c499844d01c20015100040c26400424001d030004001c00303140c0c02d91422100b403a87c0c0c46042142118880c003d42c2e05035007112001c5840484140044c01a02e1805001581c0c05e1550741c01007803c40300c0441c0402c0f002902c0b450400503e09007100c0034450090140e5245034149040c005044020002050081c0c40317030400540c0805000041c0000c884c03040d802450840f07003100751805402c05070080c8c410b90345180929030030070020902d90300c1c110045800e140400c181803000341e268032000510081500807101c900f0000320340000d40318482c0c9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 671875089 1250 671873839 671873857
    0x30c020319031508012319060303050915040803070f02130504050601090f14010b0904020906040b130f18050601090e0a14060a050a050d1e050f0d0806090403080403090b 74
    0x140f21442400001c14003032080d03004c0007481e450003503007000101c0510070088014182141c2c0d9100c6480e0301c20200010400d260f000341d0520b2a000c00481010b5001004001c6540229031b2141c1c0c6081c0741d074038402030b4030480c4910042a801009400c0000d01c0040081010b80e00080161460380811908401aa01c0888017142c00da0010b40041c0304480c0103114402100210003c20085040b500d0f00f007011800c07043c01100b160410108010304140c5d1141c044a00a0030041e107156100d540c1e4800c0b0304890382040300c5c0c0100120700040003046000c1440081e00864142c4080b50008280c1c03200c0c071100410026002d03074100516154081081210142d01d540510030030240003421801b1603442040203100070b4000da11800b40c03042c040145d0383d9a280c010007618411a4814a40340d45480c21281286940f01400307810115030b082281070000c081031300100c6d4a031722000d0301d40c100da002100711003032401100c03100c1c0e20203119004180464841d8146079840740c441d040c104002074490f0001038194115050b5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 671876339 1250 671875089 671875091
    0x2103060f0302040f1b170f01030201080f06030f0114160507020d03050c010b0604150e010e0a0b280903030206070c020a09050934080628060f0b0d05060916030c02031903 74
    0x4140703018600307909154000103982250f140788d410760740000c01c00000681610020140c0f40040340081e40c081c40040c1c4044540070013000060721819034040807070001c031360070300501e140110000d13003041c001e03421208040c0d401400203460601d1035400b50303416080444015010344d03075018002199201c0100500c050040582038100c0b81c07076140c00040c88410342122840c10411a1100308406464801c04a07082c0c42c5610840c0e6100e081c042e00c602c580b1841010481408808003c0c1d0181240e00200010280c034069805e40703106070b5402c0001d460028480c0c1009411101c03406080006401981c08280c0020070001560b500c000780111942c225038204808100f40100190740000004000d000d410052602801801682c0f4245507607440b00c8950b005501c49507040302d04c01c1102e80784150310901c050442a0a403001180e1560140d5565421110408004901d0301c0040b81c285d00c1d00c07503881c500c2112100b480d910306200e90300046000d0030204c03414800303611050001d50300d0031640c2500d2090709615690 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 671877589 1250 671876339 671876357
    0x308041409060d0203060105040f090c0b030709150804080c0a170d140f041b080d0f09050409121101020d05090c0414041a071403042103060f0302040f1b 67
    0x800c01c1094000504554800d21903824440e0050300e0100c0e21b181107450440b400240440400400800b0789600c10004000000001c80440d01209142c00703580104a90350321501d42e01c0c2c60f24101864601580c0e1164003080c600c40c00540042c928a00038400d40810038103a0301704481c2076030b9040e5000d450001102c4404000b10300c0e0340010409200308048001c1408a10420303080802c4999102103012304041e000d5030015a440400c4007000c41034100a203403d03812107402e004590002001c2500316001100001d44a072000502464a03025214182d604154048894000c0310001d882003c560b016041702035400f4410941503ca03c0d200e0a8494076601d000340c203203520b5500803c0120f840c0190794000140c074400600020410100040340550b14030b407040909a1a00398081d201c18100125401c03000720004100300400c0580320042d10b0343c02d0390b01e1a0f500143c818000903410b0781d00501425041440096003040549401c2d04256000c514240c4001004140101062030303204650316a8008102416 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 671878839 1250 671877589 671877629
    0x70305011a04120f1e05030901020105010e0f06130609110c0105090105012102030c120307050c0a06050a050d0216081210050d02091b04080f100501030b010605030907030804 76
    0x310000c0422964910709240606008460340900d080c035201a0905050080c284100640031a81e0030340390102040d049078072000f516000d907483c1d20204601703006500302400002e28040a10119000301810005014566202c805003c1000d0a818126290940f02d21000850442c00c1c8121000000400301c2c44e0b40c2c4140c01c0030030345e00396100035000c0700b0709070702d40001040940000224991240c03000320340070780e0340b0101d40002440d040d0400704541d4030030510340300c81c00c0d4240004000c01904d0311600031349401c108540100410210540308603004901c0400041e03a8051103000284481c490041c030041c10052020410038100b50f07419000c860762039000403017140c0e40c19800340e5140d100c680f040441c00358904180c08512101400580203018501c0340c0c0100340100355140000c2e0200868a80480c0c8856640f803c880c2ea95651194840850058000c0303201000400d0145e039061b690061b1401c0c6207a4601a011551548010101070a50043d07400c040005104a00103100170070b040307011385014590b10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 671880089 1250 671878839 671878859
    0x90702013b06011505180901170c0102010506011e1b0311060a05091e030d1a040b0102010b030604142a0a0503010c23090415032102071a040e07030501 66
    0x106054050b40800010000100005000300b6a604a403800c01d443d014004a80c5042008240c1820340c010400000070640244000307540245020038411180e036404d0890040e4220761080e608c6d240040c011200c0e21542d03184035608103002020600d030103100810303e2000c140c08c03078095290441c0040c0c1e02c1200049181d1080001d01d070407956640040020f800c0c85a4200d40d514501e1031380070f40c80040050401d10080b010305c2503800300300c0800c900340200d88801901d188801014442e4a2160345410241c140c59441403092080451020300144041c1c3ca41c0d80310f4108140040c90705081611400240043e011184941107403500c50f0020044d0f2130210650130031500e000541c000601a030314000020210581c4000b8031307003440101500000d810004101003055510a065210741c0140c10494034228041c8045d9001c03003124040c0410301c1c544da01810b07107085802078040e10000141d0203241c041c803283c40e111000c00030780094040345929107540d0b03500c41d12129104a03404408640c2d5400100500ca80c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 671881339 1250 671880089 671880191
    0xd0203150a0f0f030f060209061c060b040b16050a02120106091802060a0e0406050d0b15060f030c030a0902040905060417130b03090a0606032d030c0209070201 70
    0x80340c105400310600f0b229010b280402c06200242169501d204a2001e10000d58102c40b15004003902c0140d40b20602400104010b08103021204490f10b8080d0000c0c03070004500684080e200e00780d070058078120090302d000c02c440d40c01f20001da0f80303406600d1003000141d4030f12001a403031a802000214400d46010b902c201110003030303824011181030018513140160f603200c00f25040c00c1c5150401248200030030340030500600d40e80d00074940100d8150f4842c000c2c4180210003520030000c640200c0d45e82442001840054014049086205001840862500000d28024550044c1d070000000b0b005400c82d00000c068a2a1030000c0c2c509822601c1448188107064204405040800b03200911704109146900d804283c14428000c51280100105000140a001007840642c02c07500c140111502c07410101303103000c1b40c0606c18aa00c6100810030004841d0282c00b9060203070140c54842010301140c0034070070700c2c100080c154011556508429480d548401d66940e10b82d0000d9041c820f54007808000c5106a402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 671882589 1250 671881339 671881349
    0x12030708240d1b0803031f0f0f060833090912031506160b0906010f0f06201006060e010215040f0f081c0c05090306010504050c0d0203150a 61
    0x320008441c18644440e418040c0e0240d0100003c0a0400c01c1c00c8007207120146030300811040c0c000001806401c0e10055a500181e01a0701d03180134800c1e0369000719904510052140003d03048410700200113103400755640036884800045c1c4080c00c03480c5200a448120a00118003140707580c0720b103880901c0d0030000d80842d800260300e00200b40c0641c41526500c0c43d400000d010102c0d802c0640c901c0304058031000c044d506400085030864070591002d14003050b07131a030100d401e039100303101d4030000058400d8010044801c444440c85e44c00199418502d0403245075801e208045031103006c0384622400d003031041005000d201070241001901d00c1c1018801400c4030080c00082c3d04640c444030240092010510b40560410760200818038000b80030320b8883c1c0300030340703250740900000004a481e034000c10f0f401d43e10405404650354200040c40040805131002c1c050303d00140c2d01035201030010310140c1400c0d072056810072090b004040c01c1808100110f0181c2c2d00840e1084078200034801402e0590500c10445c4007d48 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 671883839 1250 671882589 671882641
    0x1509022a122a1606170a0c090b0f04030b1303050414040603120903060f06030b01090506030a1b1809200102011b0c0c1a0a030b0a050a03050604020909030a2012030708 73
    0xc1c2401502d0201400c0504541c0c40a552550a0302644d802404030b52300402e040d04004e5110140c0180440c625002840165080040c0318000348400040b440d4552071298507031100c904090030f00c101d5060304c194003480c054015607030709004800300d840591404460007803542d40d07098007420361a01c14140c2d10f40c906074114181c1411400d0002508543c500b505488030080001503603641c042c0000e18042d040f0402501c20b482c01c00e415184601381050240a0b41c0b52404240b0300e01500c000800100c0d003501a0241404d5014568007402c000d80721100c890f144e40520000ca44190031505034000c820540c0b403200c000c02c1086040e40c3c200040605500700800c03000507400710f070210391401c40c60240b25581000c01010340c1da10044a40d03a5943c041c1c00701814015208101c140e441c3d103401a03131210140d40c05e0b8480c000c6807000078000c1c03070001b04454032503416694030504101c1c98010780e018442503e82d0702001d405020900c281801112000d10b115213881c0c0d54456960900e0b445007042d58080c03210305000b070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 671885089 1250 671883839 671883857
    0xc0f0e1b0f0d230c040312020c010e090601121118100e01140f0a03060503011404121209120804030f11150a1509022a122a1606 56
    0x100c54800a480b0312041d00c000101d101100000c90341d03510b1520380300202e007851680c020b20007114403107006030081e68491010b5940c1c10b980004283d0f511084600650f0001d22403410100442c2800c0f05450b4020308103041041c0655924100641511152060002e0b031600100d0484660100d4081c1442d107402c0c15107180443c6105400002d084018508440f81880884014008211400812a00c51000c0116429141c1a50a0006010700001e10605101e9801c00c1422440098441c1c51640100d83c051410050b030000780d10191002c0e1414050030250302d580316580408190484103d011031203032960340800c2c0b484d003890b0107411002c02c5100b0104209201e444120f08403000107054a100104070654415a82c80f03800400c06082101c1102c0ca0140c402000000e001e5419006000c1401c0e032503441d14203407884100901c0c80c87c040c110031440305500150200d035078540d420380184000014140c40310f01c00d900c14464441c9503030008101500b994003a8180d0540c2340264213181e0b0140403145014206 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 671886339 1250 671885089 671885107
    0x3010c0e06070b091f020405040f0e0715050c07080606120a03080601080a110703030b010e03010b1c1b080f16261014060f030102040e0f040c0f0e1b 65
    0x7807401180c070b000b0f1407520040049910340d0820070840c840101c0c0c680d0f43c50301140711601c500010350014840d480c011410001d40e840040c809000e4107401ca1002d03002400510714061018009800045028007440f9080104041d03140c1c0a03c21800a0000347c00246a10305014050080c0d81c0074165000391140c0090800d040000c1c0d000c09001e40002c13007441c00141d0340d01c6800662008282401500c4030003003000950314100741c0c05400c8161000c070243c07a0700702124904814142070354480c00003680d00040503801c13901e203580e4400002c90028040c02c002c0d9441d40300c0250035100c10560346c10074401540880e1135100e1214041000b0b1602000314901e158202d07180800c020710024401070724103032004955050707650301c50081050003c10210a03c0900c4141c0781440c44998002050320400c3c083c4044421120050030140200c9003100d410603d541e84640e20100d80182508010303104454035034420900180f011101c000d2030001c0e100c0d03000041d80b40e05081400700444411583d140b0fa482c0014006c0e048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 671887589 1250 671886339 671886349
    0x30c0e160c08040e01031a0903041206020708070503040b28080403050d1407052104020102060f0910050f060f0306091f020405130207150510090209060712080603010c0e 74
    0x1241400d1401c1240680c05246005203141c0110341200d416020071070000410f01c8682921020030204002e40340c80e80b82c840f12490f83d01e80c4a0f60040850820300d003410300c400208254000d0140c00e0046c00d20b60305112659461908541c0254029071008001290103140d540c14040f03041c05030f890364000c1051200740b03801c018091420040c03000e01070240100340110003042ca40c1040014484140e040c02480c83c0504019296805c100c402c002c0c90b4120f22031032038035090840c2c440343c01540c058008103181d03941e41121411028004010b656280214200d0f050f180c1014085c450040c03285440e001c0c0e1510b8000203028008403c54001d5110f544007005001000e0008036520195646165200e00c0b40070b0120000c101034420f603800076400268680604a0b9405603034050b06034140305203000700380310f4150300244007500c1c1d0075140780032041e44112007001000003640c014405003c2c05000141402c10a0f00c0c0c0031030b440e600546650108400504202c254070b0203100b07000d08083c10707081000c0c0c2451150b0100f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 671888839 1250 671887589 671887621
    0x103031d1516120207080d0201060b091210020c0303062805040f06030c1d1024090b120a1b023703030c02101e0c030f1104030c0e 57
    0x16040c00400965402142d0015100ba40a40d40222500903d000c440704000d564621604c1010054080d05e03950600d2184103010764811106601c0e502c0f8280081d2104000a8003651140048248501d24980d9012202400584200001f4001840d20f9150101c180141d144100721006540d1100c440120313500c2100080800036a08241c80004604a080300760400074111904007803c0c4070105040056544103944120700d1084007002c0c070107415280d2a0340078a04d140103011385e54950306642d046110113450850004480b00151400b03400035036483d030070130300c99901c2000c4003405c020203082003050401490081d120310320010300302d031151650a00c60094551003640540c2e80b4100a8404440d03d0b009a0301007c2c001c1c0140c0c0c07808011441e1a8603016004110410100300507004880021080c03400510480310980702c80201c400e40c100407900220028201212105c0c01d05544400d240145504c0d4842c803000b414400900c584d9403829810580c6414465500c4182c01d5101340003041081c0c00c02041076 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 671890089 1250 671888839 671888869
    0x13060602030a180f030b06040e010213170a150504051b0a050607020301020903030c0f06060f09060405090f070602070906090203062b080d0203040b07020745050103031d 74
    0x541e0003114800040b400c0501e030761344402c076840b0803039601100b80481c0c8600240108800ca4040000f00701c030040c102e0a0703002e61124030880e0300704517600300160170042c90b801503040803180594694211594070349000f0100460080c1445607540100000c001c07081100883d032a08000950711441025800036007140b20a014140c06404041040411914250156083d81c50024140c07502c4003240813045a9425180b0b0300b09165100301008a60715060110b58010804030140c0000a01d540d0b00c0700b480301500024003c00b0b454851480345107080403090050402030485540540400c03840d00440409039080740d0440c41c2d100d4030400a00c0403d50340e14500104c00280801c25003183c0145541c6c5904c80600c80e04060b1408d8000903a04299001c01e80c001e51107a80315640203129511141d00880c1c2ea8030007030203114091944d0000d0a0485050074650800c486440c13190001d0201e411401c0780c0c9080301005151f10401c0e243c000620425030095a01300c5e01c150011403804031109141c0010307140360b8000e110f07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 671891339 1250 671890089 671890097
    0x30206060103111e090307081f0608070608150301140a14012102120a06050105041d100f200408010507020a0302070509060a030f15061a0d0509070810020913060602030a 74
    0x101a00018013041651030079407006040d90361150b60f40491380d17110141400442442d0440c2790844040440a100e05015201a0b000922515081038400e83e1003240c064004000340400000c400400d070340900a0a905c207601100b0202141401c44011003a80d0820401200d000e56485c0103001c09000c076031150200090074105003444d41201e00205800c800e01c01240c00b02d80c002c1c2800442805040c1d000a4101d55058900708042e031540d000403213003107410000c0d040003a04410001c5442000c2604004105180c105000483c400c0840600490301c4c1c620701c0844d0810004602085040d0080c4681ba031300c000b00e400139204000c0d041d40e0094440503540a007510814080000ca840ba4852030425000f4503803007400c00c402000c0e03504205000c40780002e41048041d041c0700010919a6401d0303102e801c0b410f8502003103410245444006809040d008000c40715a1103000000150b50b2703003c1000a40040e0100001681e5623618801e1105804680801d005c01074140102004215070010448107000d9081c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 671892589 1250 671891339 671891377
    0x80a0b101a09030d090602030901080c04050d0303050411030c060403060e0114042a120f0609021c1703010b0d0218100302040f14100c1e0f03020606010311 68
    0xa44040c05684540064101c6000d008140450900c15401004201c500700d0840d00008100c40040b24140031038094100187c00c144290082035000764000c0303801c5105c01008600b055100c1e4041010340101200c15030001c1d444800f80418001122034000c03081d070084d00a452034035610703400326919204074880242440d903548003684800d0400e60100c00da0070081c400c45065401c103030030003440008642004420070003413002e0042c42c640340e542014080719200c0c0c400016030300580c5c03070781c1c009925045002d941c510788445047c40180d0303412040c101d81d45942002c41c1e0300745009041c0101e43d0824824503c06002040005120060054066600094240402598030100600135160756640c0800e000e0704800210f16131890a034142d0042c1c4180d85800901c6404117540d00c0e02d1440300141c980d00c054200304c40d000c0c030110f0b651140300180e800900400c8502d07442d000480f42e1015124140c0c0003aa128540b075919401015414403000e500003400740ba0500c01c085e2003958603001c3d8802e4001001038a82848 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 671893839 1250 671892589 671892601
    0x50a0b0607140f0a080901081005011b02040e06180607080903071101020c180712061a0309150a0903090b030907061b140c030705030a0b070815060a1215080a0b 70
    0x89014070307011003e000e66605490502c0d2400d2039402050ba0140421a084000f410000380754401c0000c5500594a181c40746c0312110408414822081c001da0b005503c90381e99054581d42003040074043c00c10070704c903030400e80c040c00303800c42c10880042c1c4040d04001252052000c0c0060000c251250076410028100c000550301c80141e01d01810320010a4000360100b408010f8040e280300c00381d00c24940d41c0c4541112082030711140d0202d40042c040d8136410994045002811000e0401650f405044002164043c440c21000c03a04400c0e000c403080c0c80603a4036103a001c010554000310640041200e503030752505504022380441d84031911400381d40204040d4032036800d800e00c9089640240307503030041c00010500c141011410744607240c02d80944c0c003d118034040080c00e802d0000c0d02c150002c1d040b01c40b40d0213940b55140c048442003009000464403d0708050010131682d65100103054200b09900e400b84150001a00003064408145c81074501c00f25048041090450105081c401c107035114020480030364400b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 671895089 1250 671893839 671893843
    0xa0905060711010b0a050105070b0408041206061802040324061a0403110609220209060c03030703060603060f260102120709080115090b01020a150c03050a0b060714 72
    0x1514060094890032050001c40303074100300151002c2c50440024005180a6070a01c4a01c4400780304460009100304141c0004c0740602c440306800030b2081c90318614142c0d5880c40310280c001506810703a60184e88110070060301080d00415110a90f041009506040c0f540e25607003150120419800d0764808035042510801c041588a40041c0c803000542e140e015240981e200d006801c01d010840391900030100e031422526220f41521074000c0d00070000610007188000d00114682c40c4002c10710415000e000000310b5943d01005095441080402540c1360b141c800710040c1070300c42e0b03544110309052a001b014003031405101d03e4071041d1054510002d66000e0800f0840100c0703600d503059020b2a500c042080d1265600c40d03403015004500c150740303d21200d5106d8062900305c1d0107040c0e0019400761220810005503841b50064040080c050069440d20300e40d5444544850031884101d804095a50602c0ca030019014424150480100f1104111800031040800d6241c402d2043c040c0842e9441100085a0744003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 671896339 1250 671895089 671895101
    0x50a031214042607030f030c1410050f0708040302070506092704030f0f081501110f060709120203060408070804150806150304020108011403070b04350d080a 69
    0x1040040720795966407100c3d14120348041e11550f007040e143d10b4101081901c4006048010340350804091a160307582d030f40e01610f490311b02d0350303013140d50340c40403481c50b1400707402400300c0e10a20366016000700c2c031850100040c1c160707644000c200d98140311002091002190780010108207985003650b00d03541d200501c2c0e00140070a810784150180381c80803641141140a00307820054001c0c1e10030b403604c5103680380c0d411050314901046841000001c243c0c4000a0b12800d0750b0051900c074581c113050001d0301d090100340c1181089454441b01056921100c01e21541c164000c1c0c801e0001d14103521400d401284c6603001a0700d83c0c001400280003260089454014481d004080310028512a1303180b02400784648006007602800700c0d0350304c0c03041e208204240312806046040741d100b151705035103a00c1c1e02e80c00d241c042c42500e0140c6080315010701c0758840210b40401114000c0001d424800010000342c259004060400240454900c10f44140301c2075240c080c0c0380016402d1450611810010025035a801c050001000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 671897589 1250 671896339 671896367
    0x90302070326030c090f18040f020105160606030b1b1b0304051c0302010605090f0a0c03020d0c0306080c01111f020d020409050a0b060414090c1e040816050a0312 71
    0x300001070010442c0ca604c000c0100c04019640d2101290402c2e04200c0032805582d10758030810181000180000c0c404803960090302d205060580c1400003154182c1c844001000080b58800c1e90750005206010007102d015612620152403007605d83d40061030b0454502a1281148034140a0904014000350a105844c0907050152100382c0a43c481800c007100601341a2098015510b4000041142c0c00e0140c0900d1182081c40460451030301e07030707600082c000d0482d460304030101a070900020b09250546d00030301501c80c0c040e07a00401c5407801d08129605066010954505000e2a958041c03007042000c20601c0c0c4070f2403c5895840d081800e4945103001c1d2043c1034440c84940d2000a010482035042c2e40064020341c0c802314204801d4540300b0500101d032007a40034244080700b003e43c1c0d0030317076034134040b040f542c0d2142d0300c0c1120354109999441c6000b400014008180c2400c03d011809212168040040c080c501c5c2d41408552140ba2506020500c44401804081d00c1c138130707182c5000381d0340c5400340745c1c5e40c01c1d440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 671898839 1250 671897589 671897663
    0xa030804110306092103250315290a020c1009030b040b011806050609060d0905010501080604211b1a09060709050d0c0501051b030a03051501030903020703 68
    0x480d10f404d40d20380300d10030820b4221040c10901c0280480903110301c2030302e20410400b0705902c511040207000411500105000d0001c05071210408080030440c2c054410003000020380e00032910403408030103101c0c49001c00d2012603111080c007981c1032a65000681c031042c04810b44840d1070b4241c2141c01101c4c805080c0c0c00103000b200a0400f031200b0008952001da04851444000d00650a4502d07507800664003140700381079000a05010001707251810400400e8104a40c020019441c2c40c0385d030b1030a0954909034440e0055030848000c01c030500c03212102e2802000000340361a0910400c8072805005c0020842800e807100e4100c194410422002c038100072441c1c00403c91042007450540f50b0b80d69980e01c110b0384900014484400000d0900f4481007440c0d6a507440342600c03542a042000440701c0da0480003a5a03121180d03660030300d0300c480e020300041605040d80d40d008121440c0960582010fa103021548a04041c50080c1801c0440d0703010864209903030b4803111140c114480307400b94881c41d0b065124111559 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 671900089 1250 671898839 671898841
    0x1b010908120f060901140103090507080a0c060503011203050a4506080f0c040e07020a0c0510080f07050c0d0e1206090d0e010201020d05130c05040e0a030804110306 72
    0x11098080c00303850300d1800004000959694107003205000c100a494141d0070142c008014460041400c50407a51801c0c1850001a004001c0d140d03146810072680c08400141c0200d40a101401005e1026601904c2c180c14024599458005071140154420002504000020503d41d00c814418810020700491404030070303c4900c0641907002000c002842d00a031801a8207003009a010030020402c02240c0c4181c4611032981e441c200c003141441e00c018183c20319840c04000216440e824200442d0280845034014842500300b882c0c0070b84d81020f19000b4510a000d107a9812034070a41c45006182c1c489200c0c614401c00da21000c6040d1211f01030400085000d0007603101182d003c2c0e900901302c140114089401240d02024842c5ea13988582d0203070b900c910282c012001c81d44440d80510a4812501c40610005190450b0364034900c2c225034041c3c0c1e0b1804140da0203a401b10601c4240980100508030466007044100450340040380d6071544030318020700340302440c0d00050501618419201072807501406803015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 671901339 1250 671900089 671900093
    0x305250602030a020d0f1a091b030c0a182d0e07050901181212090f060903050d0f050a0e0a050a030b040c0806060d060222090b0102150f0c1b0109 64
    0x20303400003900d00c0200ca240031005c0703141ba4183d00803045119800c0c54203580030420340c01400003490000b0040780320445900d541c071a0240503640258854468400301039210300c000c001c01410030141004d909000640c88000303010030041c01e81c100011001007410004024107504140310301940380d90000316150041000c0200e690380010007054480b10036683c005642d07011079a4040c140c030240c00398000c3d800a82c041c040006d100410540e2a40b801401c101510b1541d0795954000c0f16056009800001e840d00020020010200300c07400786401c8a0034080c0000192240080c268020103c1143c1000076000c513002060b101c1425044c09003001230160b16400341c490a0415001206803808c40e84417084030b00002d0203010105007640941001402d0311604c100d1a2540d002a400c58906d0034440c0c8100e6080300c507000500690100207048182010851209100029082c4010305d80c4140641410004200c00d0340f90140300c080d40003034000c100036200c0c100f01c2840040801e518000000755881c02c10326000f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 671902589 1250 671901339 671901341
    0xf030b15031e0415180b0103030207051c03080c13030501050112020108010f0806011208271002010b060301170a02060a170a0204150c020f03070b04090c05070305250602030a 76
    0x31050314115680b010381050070095242c2008110303030142c24591544d001a4640050b5007002558a035502100c081d50768841c1c0f80c0c0c0e0740340403082c1d1003180503a0000c0c4041065090440118403542070900c03645092036055140500140d20081c400020a240061904100d030114000400603580000003040700d983c40f1580e07030398a030580c480c09902003030400d000011f000a200003a80d003500c42c00c2d0064200703039180105590403504801000c80318110148058021482071217150100300c1c100711681c00d144441c0078180080c10704070585881c07c59041050010300c6480340c0c1c00f00d0781118042201d0240c4c4203110500182420310034000203500680005584040c10351202d0254020b1503840d0401c00c04d5207850740401304a114500c2000f45451190903868910740c081c080c8184020300181025181240303980029007802485d4026421580c80403400b4845501e4a204603070710001903041852030080c1545001d4028003403c5501140e0407400c1c0f8070428010383c00390003a006103500a40c04c1d502d0342170101c0c41d80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 671903839 1250 671902589 671902591
    0x8090d0c0c080f0f07080304052d130218040c0e060304050a05030a02030c1c0912050a05010f1d060601141323010f140322152901020d0f030b1503 64
    0x90920440a02245160010048034100c500049c45040011444042c444060020ac554011020ba02c0010400c56171140f0155404c1e100c0e64100c01070351002c040051605040e110b4482c039004a01d016007000150750417240440c00c41900311080c9071241d03121715000d864070074096001822030001190720070320705800101600c4028400c02c10b49504100094074110b0b002d1100400000040c203040c8104003c804102901000e54020816038641c16042e80b5124250f0307500da0b44040d1003c0e950741507610100d4080107100143c0c1e500501070440c500701840001c101600700301900d0724542c00001e0007103880401c0c051134801045088000da181e882c2c88401890541102450680401c14208031002080d1150614095102c1c1d20050345045440b41c107555014030002081108207002200e43c034074003287c03011300c2c3c690a842d070481020441e0315070380b0300040000707500c00c120051007508003c213045940c2c2c01080010410526181c14200074814401c00c030013518812440303a40008055a81c40b1000040cc4019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 671905089 1250 671903839 671903863
    0x90d0b071101050c0412030c0c06020303070905030c091609090516110303090d0f021f0209040c050a141810030f2414030106030c0b030702070608090d0c0c080f 70
    0xc03490422181c400301d8240e80c0304440750511503004000030300c007402903841d0701c0c5403860003480c01081400c0c41350380c0c01b5000f00e1590032060142c0c1c408410031410319800b1486402402d41a005001e405600d540491404070014161184140780903248080702c62082c1500b1004010502d024400c1d400c001d205545400007561155001404032419981441d0300042145e02a81c1c00c14014100440c1c2180125490b42d43e805c04030b0118010302039100c400f544d2034190500013810003c00103075101086410002210308605421042c08414080107125940043c44640d006400518060b9030b10508100d078000c90304241011540013011020543c0749583c542d00103540801c05180800250321552030858110303c41880c0f000309001103000600a98401400c8403140300c6003c1d0000c07854940f030396a2032100031990b42007210241000310400010a90400c1134500500c642e0a00303255030f04110380700c99160241641340ca01403009000e558010060348004180091040303d060741d140301e400380b01c0341da240d104034410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 671906339 1250 671905089 671905097
    0x72d0521090613120c02040e07090608010b04090803151f03020d050714070212120403210309110d0f1b031109070f1416030e10080105030607030f02090d0b07 69
    0x6031000b80c142d06041d82444d082210800045040310089640801d035402c12a0084c0c3c1700c0c03420540b0480c04014030006002c60000c0481d841c1d06048a85084802040b06980700e5030500540201144e880d0084903084600f05014030b061040d803202150041d840c00036020141c0c2900d10044004d1503040d805080b00d00e6005000307214980301c0034070489520580711550348403100101310550061802a480d001683c1801044d40c0d403280c0a50000b901c0b980003940107580c40b4034006401e9180d1090203000b800d0140d81428100000c1c0c2d425280c42001c0401143d100b8007503151107030010103010b18099010b9015510040306007036920307141c0d20340064036586c1c1f108803010402512160701601d40008001e02ca00711940d11b004289003801d804980d1030b4540c50f24050101d8003000000481f44440182458a0b03001c1d0b00d0744040d0315440d006001c41032034140e0600080200e81c40062045603404214141c002940d0319004c0b0315040041e05d82c0000307114000030107038025080540042041100ca401601ca0306c082e4079 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 671907589 1250 671906339 671906341
    0x120908190e0405100501030f060e04030203070b01060512010302280303050c16150c020a0305070905010f0801054011090603030304080403320106080105072d05210906 73
    0x1c02d10007a03410540380040c5000e294101803000d5442603200010010380624049501c0381d803448461815402a80c0a0700140c1001515a00f882400c282c801e0040c080c0740b60181ca04415a4650805074006010003480f81107903000f4102004d8100300c240b00c00c5015044005104c40d5030f4500546154006912181035019811803d01349508480010045400701e40301100c1c0d00403002c07400c139807501d90140101c0c2e10a25088007c0086101080024007074002503030000b440b541000c038200b0a91110758407030403a5038100030030408840c41031130041039020481100301004480a411483d001c2d0420401820100c40903800d003c18032503100040600d00c24141c5100c100c80d2161004d040e220301c000c49016010a204100c20000038810348894000c1e9450f08800c0c40e0102e143d11076400501d01403a103585000e079100c00d0300340019142031040d103400034841d041c14003400d034100f80c3c88401c4241a0b05a000e60254010320300c2c80c01c2c1c1c0240104e500084960b1421512415400400140c030907090780d0006076445200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 671908839 1250 671907589 671907617
    0x1511011805030d15170a2102030a0c030509030d1713200f10020c090705031902030c07060221060f130c2705180f0712090819 55
    0x40180c0c0380d550440082c501d001c00981812000d88420907902a03141049400000c624040e0700a207442c0710400405004c44000900b800d0040480380040c0c264600c0b100200b401d801c0390000f04070380c0600782900b8114402d1040341002d4509020340070f0130603050b000b509801c1c44525441403110b0780c60b000c0d00003a4020b1b41c6030b0340c802201c5280c0d0b919005001203106c001c04d41a5900d591500502c03108014041482c03141d401021410030104c2c0082d031400750f44004e86414040c50b00c0c1c68102c2c0d01c042c13285019400c6180000c004c00d080e5028480a2a034a903001011615490301328003150410f9030000401c0d591006200d9200c1c0b0401901c000d01900c100150004c959076140070100c1c406400c2000340b40e051846460059800200711381d03a110b03c01e0005c15084a0006141d00d2040c0c6403000ca0608868481480c01050000c41008000001280500070b820840c4180b02001541c0d0845030f1450092049c00310003021000419203007a02500c038031400714681c01c0b6034180740e5400c04c0290707080d0346c1e08620803512 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 671910089 1250 671908839 671908871
    0x31608030702130b0f190306090803060909060601050a0302070501090f030c1b031716020406080313120c0e071704080307110d1707031e05060f0108092104151101 71
    0x142404651144484002582c10700d0251211131070381440c495105005940c80d0b23075042c01c540480100f10742046000c02001260700d000820a9880a80ca0025011901d09480000c082d0301c0382421601c14540e01245020511000350b001050f04d50f40459071686a1034241405450102c002e071003201c00704007201d078503000e901c840072140d0222070380803481c610380702800c001d00c01c150740024400d80c02500e800300c03e071800342c1d4845c000e4030300034081c40000e9983e46441060140560186800424130305030800c1d0b9040000c0c801d44240c600302c7e0310911103c8495220710100300c031000207100c2e500041d001e01c0c0007400244a0b010303004500a80f002d8540e50700c1c3c45504030350107031a50280f03031040380492400c0e01d08220b03000c0d6400c404c503805005464005066480c540c000014001d00d800c001510680e140c0c01c21400b0304201080810310442420140c403035140190307080d941c4441c2c40701140305100500d80300c44408509081510f003c0c0c4190500ca0340030300300004000b23181282c2140700c91459801d00f0742c20760042c050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 671911339 1250 671910089 671910101
    0x9170d2a050c100c0c090504061803030f0501090b1507060e0d050d061517070212040314071a030403030902030c0d0623070203160206090409030804060f0203061008040203160803070213 81
    0x1700c200d5a011103854000c00c80028000104150713102c0352903d6408030721107c02038800c2001403098500041100d4000050021501d050b009800c4d046d18000402405650b0920b40000048150210031713a40c014618007103001d08442c500940b01c510480202009154008001e000d00e201c0701c400c204101565541d0820342c5108007052600802c900b1640c052041c840c10003240e50000960044544140003410300d400243e1140c0c0c000d9940042c0c0c1205030000317801c1400510000e244481400c1e0190680088240b17180c4806480142410341e904089030031500d060081458581c40113040d04107041d001d0410b074000d44403c030303014080c800500042c070400003c00105c0e24010081030b80154240302d1036241940740c0407122507090340d00034810310402c60140d869001d031689061081da07030003070315090600e400400e8500701c014030444103006000b00041a11000c0c001243d980552030103002c140c5460011a003000081d54503000c03030300d0b5035200200d81540000000c12602d88242c65609a08141401540071111 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 671912589 1250 671911339 671911343
    0x2070b0a050a020708030a1d030c2b06020403061b03090305030112140105010906060908190b070e03010c030501140901080a0206210a090309170d2a050c100c 69
    0x442800540c64161281014019442030b0b401200c116a88035441c0928503005096081d000a5070750008000c00c07042c507020107030982000d070001c2c8030200c00c110001c1d141c5044210f1006009000100c0380c942508110042081260801011507849482e8100f21025080c100038401c4145840441b84c4402c5100e0f00c1111001c540554555066900303061405002041c1e03072000b6109144900242589400288100c9000f402941301c00102103203402e034040c0c207841c50366029540f40d400c03034420b041c0c04440c02c078500030103181c2c09030814400d6034400d034068a0040420380190340640c0f9240319030116940590080d41a40c0000e0441120842c1ca44c04010216509015198082d000b11a1250050030808050010615168a003000d106c0c1d419071110643d140458041004c2500c404804060540002e0340b0b4014201c128944006c2c0701580090990b1941e800140004101c000015881e01900d030300b005094011031104841c840481d107003000b43e500d01840500510942d04c034200329020600404200421a03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 671913839 1250 671912589 671912609
    0x816091404110309030c070510021002030c04120303151205031209120a080f1e0601120e0a0606090f0902030604120e18070809060105010e04090204020403080417010c0207 75
    0x281405030690400185088058006071203050700d440c0c841c0400040c52180030701314000c580300d844080001d480d12089a01c200d004140300001c0590f56a400b1031044201e0250200140c1e4a842d040b800b545540b04540c42596039a0403041814101a4503411602490035130444a0759603035202c01d04000c645080709001001980100303d03041d100c5d80c1980740c040d071020240341603031418060140c90480e01d074407a00112000803005000c001041c443c00d030b400c0d44c0009188095207500c1440e8002c107035000c00040c060714103028050b03403031070603c03107054019400c0c507034014040d01c201020300d1501c2800343c109030040c00c02e01811309a03410241d4409114005005400034002c1900d921350f0745a01d0159400859a40c00704140c4180008054807040441a902d1003405890462807620350001401e001000e402d40380c650f0441c10041090340c2e44030504220b40700f011035000030881d495100290092150f603100810039080401d000480294021212680702d510070028030010500c0d0504980750742d0640201d0b510701c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 671915089 1250 671913839 671913857
    0x7020319030b040204050604030c150f0c030309050a0804090b0102010e0d050f0a0e09040c1d0f010515070b010f1805061c06090c1401030f0e06011a1201030809010816 73
    0xa4072075044845480400b6000601d071075210008035100e80d100760410350302404081e40401c0f80b69180d005001e410702407440c00c142242031940005085540401026040644503d0210300780002409510034140d0300078601350352181c1e520705000190020b00c00d524050751a0070001003038820041800c1401e55056a901441c08000500210b103c0e0040c01e904e00c20882c940114141d01e4990102a502941c045c0c10340403102460300d05140e0310103003ca00b0500c820013200041c850702100c03040701c85054400c100c801c1002138908000314101ea004225003c4c103c8600900006040c009140c3d4503000d84403804032107030380f240c071030b42960b02922021b8030429002041142501032030b140200291280910aa00209440ca002d884404c041e419640040790284d00449860103a50703014400c8948100045030706100c09201c0044141e1255014480d07004402210750b03d1940040440c401c40308280780311092160b0658507420300e2000741e0460841d0b030340890420b1020039502a80c81c061000209426074a01c010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 671916339 1250 671915089 671915137
    0x905012403020307350c1e0a0e07030902030312011509060e0d08070209091b03010e030f07020301140f040b0a0e0307030f02030c01020f090306010614030f0603190317070203 76
    0x4000300c2c100c4407060b10066284010810308103101110041c0c010900141580003164080112046828007c0701d103e5806040e42d0102c2e444080d0700f00b0803910000c141541d65540c60750140d0140c40d0000c002945400000341c9807401840c440c803000d058411505440709940141e09040d10403a88038055100401c0c1c01e203000d1074052a05180407040144180740c02414518103502044014800356210390301504285100c00701c82d034a4842096410300210f0081c400e060315074140c203403a88564402c0100503040014020103648094020070142465509082c9903842c3c510f080c0d0160085c180c504076400e900c0c1c00049440c4c0303065801014004200301024500c0c2103441d5809032003903030418842c01c0c10f5000c1880025640c541c20701c090850741d84440202036076004030704101810010140c12600c240300445034407007440ca05440582e41c3c0800c0c2200307400c25a46506002a103850381c80b0303d11903039511504a00004051b482502038002c48108020392020b03444081c1d00340e03186d00412000c0c0049510084d80464 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 671917589 1250 671916339 671916359
    0x7080d0905031c0c031506172205060103060f090b0c031b030c0406170c1c0905030406050903010f050106021f020f0a02010b030f150f04020111010905012403020307 72
    0x300188200c0c02c07640742a261800d034503078290f49041c3c000095541c4003400390b82c20741c06004142800c406200380864841c201a40501414210482600313038500050003d00802914124048010b0340018100000030562400a51320002400101c0e030650070301c0c14103030401d40d80e03000f41c010703c50340040f0729070056444031141d06403a0802020a40082c2052040c0c5ca1400c540b04000c6006610050400c0c0c1c1d540d0400300040d102000441040c00681300540c1008060310025040c1c0d4001c0c141c01050600d071101c80c03400d51000d0a1408400713041c83c080040e0000d08240c02500030000440700364001c1c000c0762041c1070903d003211030910550001d604000b910100c8100c0400c0c1011404521010040c1040d80f0281003440980000e500326015070f664215400a5150801024001807100c1c4000c3c48550a4120020700401c8080e10840e910040d480218045a01449844562030401030080060380c1c428242980601070b1202e04015220001e01403e20000721580c80409a80d0050b0040c00d0309413401c90826 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 671918839 1250 671917589 671917601
    0x22107021209130b030c131508070b03011a1207030b1201140f060d05120405090108030a090302011d0622050f01020606060703020a15051f03030c060b0f131506030207080d 75
    0x3682c1802012091b00f1290382c6c11680d528001c40c019000a582a0864040341c0082503507001494150710008040003205042c404580c10364844201601241c004518a41032a008250304030f0940340169040041403a4035a0000d418000225850102069000300d118201d8240a010060310440e45000444015613422441d402050107001104075444a89895003080c540d000012801040050b00700320910b0298161805400000055071404a9100010704110143d11000b03040c0025040c1110090a48030b00a400000e80a80001da43d4040d84407144181c8034a92100d86035a400c0f504046503d00b403c030741d03104030300606800074084c54488908000d070b5900280301c1182144182600780000410301d10401c80040154030008c1000d04156401260f01c811601903143c400340c41400800c04241d2058404c41030541100d0001751082e0b004010540207012103540a4000c01005050520110310364000410359501d01100510f2540f03c5400b00c00780d00c1101005040e0382018003240c994001640e00030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 671920089 1250 671918839 671918861
    0x6010c0309050604170127120507060203070f18180e071a03070f0f0804020909010e12070b010801060b03060639060f2802210702120913 60
    0x1030554640c0e030702c0040c80a9000d908090010309843c0c2d81c110f140da001740070f00c20b0405400c4c80d26180840303403d00c5542c01300f50160f03c00703002c2c0d5410f1181e45401034041c60465100a03007005080d9641d2030110005842c00580c26643d4002818409180c403c20700803615243c1940c2520081c0421010301c1003030b60004d809414591070441c0200ca100041f50f003000641000c0a10745500711f1522841c141e80b0140410342803503034003070520424840800c00c59030710651050740a54122405040c41e165440f00c1d80c0144003c00c01094984a15031051a1914910000d000440c1c840c8440c0402070ba2a020a2303400c0e901c980c807030f540b43c1c690b081c00480c106240c1180030701690701c0215188887c08204104505041191b4509204c0c0d2030380c81904a4034426007444419807000d0040012009070403c282003600300e074034080000520080071000003903d50541d4049580f03810811941c40400c05001490901011042d00c81c00b015101c0c5a00d42c20faa462084183d4000e42001044050403804034218100600b010802c0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 671921339 1250 671920089 671920097
    0x1e010e100912031209050105010608100605030402010507050a020d05073f08120109050a05061f0807031d01050708160905010e040b060c07030b0c090a1e15030b100c02060306010c03 79
    0x38130203a43c085200e1420300138000c400229195150007005445600090280b001e01a00b40009000d80d0781c0100450b81c0180d82840c2031540c900103070410038104045010001d50103515105051300b40b1900103064000c0d282c3c103003000c0066402a202c905200400c03a8266810b419003d80c002304150000113801146500070100d0a281100031044040300c3e1202348c00c0305161a954405015403001a07201d15640500709542d990a1100b00480c20303400140c41860315000c110403940020034852290300315091401440c1030011080d1a800d913082c0c0139040844180c0d0010748280300040d072404103001100c2320444035448a26106091100445840446854081d003068850b4100da215440d140021300c00303040142d002e090744c00d081d4907255a0b2103a0203040d008010342c1c184807c20040e5903001c4a40211200302600301d464900754018640c01c1505030b03000d55500d9641010740e407049030b05a0810580c0389001c4035480d140080003003007601d00f0800d1040280d0012070900019110354000c21004034042c3c005e0030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 671922589 1250 671921339 671921357
    0x307140105222c150a120303020706050f1009050702120c1507030b0f0f0315160801060f1d030c0312041a180108040807021e010e10091203 61
    0x40307035899035804800c16111242c0300108440145040c1e019101e092101070750703502c86480c03c5241c1401c0800707403a140d2503d4000e000c0760181d990f400040030041802d00840c007061100d03801d01900035000990140c074078900300b200081206642048051046003607000c141d00c1c10717050066600c01024001c1500f0294816140c10045640d204805041506107440c0104820341d0300080c40b2800c072101030940010305040c1100058245d590f02004002028181c0d101c03210358800700d00003480c0188200300c0b401e40e141c0b51005c1c08204140000e20b4000308005440d03003e4180d9892600301d583c1c00b401900e42001517510700a0440e8200c2284034440754030001002c40340314682c043c000a0800c0307c0e0600341d803080040003404100602202d4004507404c3d034910140d600f09003400d088103107507008400b011410041000009020408910250b80071542c0250054249074618010154a0501da10410303003c0b440081c01c80d80700349040140700b20460000c0d5607a9006610b003101500c89481404030450900002c42 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 671923839 1250 671922589 671922607
    0x90708190e120408010c080c0a051c020a0e2403040b06041409070f0806060f0d031b15050a05040f03030b010903020d1209122a150801170307020307140105 68
    0x820000071040d6030b00079959481c04c0301031400c46034844000824030003070074100590303142c5400039102e150040b8202141d40ba0350b00229040b20450440f0260700c07462010504a651f203900004800000c842a11410b4140082c12645000b002a810140313060a104100160000b56601191504102d0280c004980c2d082c0300e40341a2035450049954194035030010004214402c4a40107070002029000050400d6051072004207158905095005026002580e0760750105403240e5038443d031321003071203000c006044031514000d4881c40100b2880b40d021420b1601054429896200703590142e540101e4030fa00801e500d42e000c2e8080d001c0408203a050003554403000000d45c6031780e00210585031140c01c510b0070000b21a00d019004802980041035803078004403c0c640011001450548003070292925891060607007010004240440c0e001911022681d801031003503242c000001e43e068420410400071030720403040300c0d699680520040130f075050307102d0074040191800d42c01e80c12208160605d000f61805001d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 671925089 1250 671923839 671923843
    0x40f080f101109120a2904021009180e070e011d060303090d0506010911070f08030a020403140c09073f02040806041b030b0601030c02010b030105090304030b06090708190e 75
    0x818480695401148102c010002441c0701b0060030312a10f150400000c46554441400d000c000700004c1c0604161070b020161940901a05070080120800b03051f0802c0f0701c0c0420902406400307410402c180b01d1100701060102e0b0b03c2d500c00f4103851905942c2064018440380044c0d5591029103941d8040c081000642c00d0350722140501c407600d6005a0080c09a549800003120072038000440003000c00b102400840001400c11212240007500024619280e44950312017100034840d941c4024102c510180702c0c0300c140d040201d01c14004400486504ca150340d10342030181c80e40d6000c8603c040d4a0119400e9801c1809400350341000e20050035100414856140e10103882268010b40001e001a4080001c100c2044000000415108080c00d21500000d10b0741e61004864400a44814181030710350702c9150b503443c800d50154a000c070000b402408641403a0300c0242c0c5030340c85070000b91a42e000400016502d402c03c0d10009028080980c0d0320a0181c0d1080d0710300d074141007020462008961951025151f85d841 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 671926339 1250 671925089 671925109
    0x160828020d062f12072a0c080d02010b0a06030e010b0406030f0b0c0f16020d05060a050907050301020906030c130b0f0d05071b11060c01020d02040f080f101109 70
    0x100da41d01d07141c0304441c01100500c240000d090f440003408001500110050040caa40c00c00b196040a540040c1944a00c540b20b07240b450b0802d90b8181000c01d03a005000c441100c000885410344e081e10b0821641303410807801d8529045a898116116440411144d840b0703038018180c42d01601e000050098541c4001b80503541d0b0b541c000d03104028441c0422044c014848000d81e08030301301511041c41c10030f403e00306101c207000314064104d0200d41b44d4107000c01e41d168150880b40141c0d11105075481460450300303410041406481010301031141610204680c101442114185140103003400d00b10740d20017034544425130140c802c41900340b555200001c1c1202180c40070300001020703005540c0d11420700c2c8241e0700c00c9510082c000c0c410418281140340d003c0c1d4001c1e85114800c0e4000c210141c8174541440421000e220b0200014815840001c220301c007400a03a018109071080041c80c036900680d1142c003256a00d40c003507600c0b1016001407000076200081948803e6042c40456901818a40c0500024200800e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 671927589 1250 671926339 671926361
    0x90d0818062509060905063009120a090312090f06030203060f0405060d021021090227070f020a02060c0a03090503030a12090203010209090405160828020d06 69
    0x403040041c29003140181440c0c40c040302c1035150078000d2501d890001400744116100702800350f400050010682c4000304030512040c40441c440c00c1d05001c00d4000c0810f1a0000c5030702400c240180301d11600452010022a0020710aa503202d841003801c5440340407403841c20b0600c8905010641c2000250140f0f04040c5000402c0355440045e02c130319221060245051804231881d20961a203404c20170340b582c070383d0050100d0a40586001000e1100c6007070540e4901e0400200440d000414515501489c5840c0c01c42c2102031b01c01d4a040740f0341ba01e07112000350b041c2003850500c1c008803482400154038912820076426214020310403a48002242d402003481903110210000030382e04482090b030241500101d018008103000d80055140c46080c6000401000e441c002807140ba0f6100c003450000d46d40c00f50180d810312140248054454182450f01c0d969903145109001e010095501c030000390040c010540285103c0311440740d81851106085481c000403105800320ba005031800380f14000700e001e502c0b864030012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 671928839 1250 671927589 671927611
    0x9130e2a0316210f06021c0e07050a08011503020114040510080f180c0402280e090a0203040c0509060423071103040f03140708011a1206090d081806 65
    0x41d040840d001c640c4000c845041c500000c1c08080c5000113100040068007494006130010388540c0409602d02c444c00c0390452040c821403c0028981e150600031036104201e07001214084115561031440c070b401c1c0c681c130048400003406004000c002550049a042c8103424075580f0003850652900001900c400d056400800010210010000540f811903031203074101c07205c0564000c0039200100380f1640d502c040c8100360302503034001c600c824242228090000d4403000b281071075505484540e2000304006080e2030484c1c841c0e00c800002ca92a010b1030b03c00c603402207030030204461140741070070705100b8104070181410750010750f03030b41001c0d84800034036401e0400301c0000c2c1416101c0381000000200422081c01007032210790400c0004015076000103e0490490768006029610301401ca51461705200d5280d200c82c080c0e508054220544254100c2100702003041103640f01d6600e241012640e580d84800ca0b0b500715982d0191003807485803030148055a0384000d50250311640e03840b5040c5254101041510f0f444000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 671930089 1250 671928839 671928883
    0x60c1505180f0109112409030307021305040c0e010b070f030c05030a0c110301020c03120604140709050a09060e151f02150f0907030f0804030c060509130e2a03 70
    0x41d01034413136104040803240061500c3e00320050a41c00440111b032615a81c00c002000900303620240299600250024401045070400380b40780000380a00312000c0328100c3d41040c01250302004410514141c590b41541b03030341400950f98030182c2c1302840420540034800f4040290000039010401008801216a5072400e030324914545100180581002688264010300c02c003000c0590000030344208040150178000c00741c036101e0104004042007035118078003210244c10419800c0c0c109a01c1800c41d43c1c10f443c580d0f01c0c1c640d078071400000c40765280906501002c030500811691040110000350002c0c000b003200c504040020014012024041a200056003104401608280c290b41c841c40e4044c2019051080a14100501c07646600103030000428009a928000003400303020016100a1580005a40000d40c0c035030740050003603008003180070300c11041c04000225001080c019040e0390a40e99000702104186a00c07901544c0014113951101c180d10320714040103c2c1d80820500c0042da088000791100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 671931339 1250 671930089 671930093
    0x30203060d170912010b0f0904020f030f16240e19090606140406170403021515030c040e2a03011b02070e07090501030c03181b060c1505180f0109 64
    0x10200d021110030060391400001d140c0940b500d1f1528040100104d40d0030b45140d40d03a1000603000080c0083c4180c1500c0b5056441900f5180040c24240c0da480741d0b681e00841c81d90722116220340d12041d01810045d41014440414400e019035032403120560002c00800191408199491821340e05500400140351600300c200a401d0700480b03140030000290810038503180c00c090014120a20b00d0f481503852800c0d600c0058241882030181080311540713161110000e0600d600c11000d40c070700c21a000c034800d00841d011000986894460611400c1542019160741c54040621440418151049403001c2e51007010807803403650280b052003060841c0c10010601c680c0a010020300c3c01045400c0319241c3e200f0303d810301c540c02d5080f10701e40017100c0f42440e001c01c400c03440032000c0340582222210201280c5d42440310f1000c2000082540814440c0100304900d41c0741c4d110030450b1454101070018100446642c91289004042d0700859400f10418044104079078201d03854900d062a00281c080041e5556403500003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 671932589 1250 671931339 671931349
    0x1c02040914162006010801090c230103240e0f060d0c0b0310080d11061b0412050304030c060903061d100b15070c08010b01050a0f030203060d1709 64
    0x44603a50501003502146040b0b00700301c03100601c00900c60184044181d40c00d4220515108a295060688083e103205503910148640a0011a02c0032034010b100007001107454161600202c998402120200d40880b20550040d001040d0a030040703101701c01c900b407684030503035041105130f001401c109507420313410701d80100310008070b042c06807a00d0310501100607a07102050311449050b007075641504826a8a4541103164001081e081c0d000d0411405000a2081910380046581408052210995100f03030380d400c88644522024100280c5880400d000034040c400214054040703040c81036045070303d00fa489483c1c01d090111990b0105d800240111410b10401860340074029554201c401340e030fa0140c0900441c2a1180c401155140006503501c00a228030303504c5090003180c1420f0030b813100d0380d1409281000a181071041c00b40f030705150300306030550036030f548250100d40707804010360380303a40d8040003502c0110301940c0b0241ca281e5100048040c4000412108007900d8403d414000d500d50b55030b001041800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 671933839 1250 671932589 671932601
    0xe06030607020c06030a020f090a030b06010f030506031f020705010203010f090608030a08040b060f060309032203110111010e1e01050a050c0301090209180f01050109080a02061e1c020409 82
    0x1c400c54202030144981a01c40105483c0c000c1440c010241c2c80e44000c0380503008900440c41c0890b4417400c1a4400414404960003403030080e50280d880f510b030314084a500343c041c4e4009841207030b0142d001070000b0b91324099903560103814040c101e6016140800071340742d027820b9800a03000032140b440c0091007000f20191070700c14100100f900704040d43c1032541c8040081d1107100000c002601d01d49403000003c0f150780d9041404441c0700001400141c076402c10340b11142e41d80c2c02a60803040d00c2140141c407618a800a43c1d29402203903031103600071300d080d01c00340e00441d02000e00b070ba8007206540d00c400060844110a20020500d20b41e01480d1001d891150500c1c6800d403100504081e070007600d00b03400d0050401c603c908032810344054a030b0143c0d07525010004620703e84900c020010040090070188492513800c1c52590f030499000f61b80e110507540e2150b0b40b0513114821220000d40c409010000c0311034910800064206850307141220b10b00308624003051141881c01c0440d40307904158001401c0c8a5449144942 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 671935089 1250 671933839 671933851
    0x1401060810061d03010f050f0105011d0d0f05190f02130b0306041101141b1516081005130e06070311070b0c0f0423040c050a1d0a0e060306 61
    0x30796511842c20740302411002ca41d488188056204102038106034600350048000034a0402041185140181d640350050400380100d034005000d101215200002c80e01803c0e94000c4018043d101d0030703885544032a030388844000110b565014401012100c400060b05070300b00e5034022030176000c03c0f6070588100650180640b00c5a1003443c50000e04c81141d0f18001055030b031181d44800054480710310040142c80c920403248803580103001c002650548000301c0c4e0b040015606001045500c40c0020f4040c0844090084404640c424440e40f5001c0000e031182a103190070448144c160300410f6203503408280c081d2281c2140001d9141c9413131802206850070004039521464901e030820284098a808444034421044054415000c043c0480c905485d01c0d0304503007a0411811103155556520042c8441c040310240301c4185c540c0301190404c0072400c19000e441c84002d0550364480c0f4128521200f914112002003840f100c07025000d1401743c503901c41443e0003002c1c111030b080060003031030014101031410000404c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 671936339 1250 671935089 671935111
    0x1120201030e03120f22030e060f0a0309021201090f17091201050403020f0705030a060203310611040b0306100c02030f0a110a060915051303030509030c121207051014010608 76
    0x11b102c8051070711054049096803500c0d01800d4424204001241070285035040d1814600006e041d068841d0160301801e801c41c0309440e405421183c25504e60b0803a001020b0181010008400d964000341c070084841080e05c1c00088464200741c8024041b0701c080748030110b8401c01f41c2d525000e100a240d0100402c1016100e0b20340103044260902011030380303e5501003801440c140c1c021004c0740c00d2207070309060042182d4044803113075a40502e00020702000038031002d0075a800351910060032802c180d03074421a029140c0100d102031a540b5804140550300d02c11a4403141040841c4c0c41d035a005a82c1444592600d12500d4000c0ca184003a03801d200604584c0038002a10420102d48100416030b0004200004c59031904c0c020102c90440b40d9082c4d901384a60100e8140b400e428000200030036030040c2c00780031741d0030040e01120f015642c83c07424020a03024580069090b035011465041408002c01c009040c005c7c803507800d44100f000314450030425103104030440d8007110300240041c0030b4158445603c0303902c040c941d15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 671937589 1250 671936339 671936371
    0x803040b011e06020309010c050a1e1203050105010e0d03020a0b24010306030210200f1005010b0c1507050904110309010b15031506040b0a320301120201030e03120f 72
    0x43c060744d640b0030000114184a0355282d900180101400309440742d41e0451134a641841f42d003100c0d058402c407160b004844500c00e200100300b1040c804d20131281aa101a115400d1003510714040060300241c1c01000c50451061070f0fa02c2c2e0000da8401c0440d40142e12103646070400248480c00c0301100419000751030704040c0391980420251351031401c4142c1c1400142000b070072581020541901d00f801064602150f8454400c104480080000749000b64051b0301104101990300e501c075500e00d62045160405880e032004022200141c01d1043c115040441c83c00c006142041c0c150120f001e941600030302c40400c28002c02001140d00707080c040c0c564180801c0314200900110400c40070034500011f8003451100c070900001c480142c0700e510449001e409015840c2e61105c041c203000504d10012603082c4011503a03030b19402108100c5810b000902798400203601c904580c04d00030070a02001000030709034101a00c0f44900001c80d0401c3c8010002d265281c00d0003501032801040241c4840344c040c03c0040020100a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 671938839 1250 671937589 671937599
    0xa230f0d0201140c0a0b01080606131e0c110a0302070f0812041a04030b0f0a0c18031b0306091506240c03020109050601080d02070e1b160803040b011e 66
    0x14943c216600020151551100d42e9640085d142c410000c00c0144060b00c1c0c44000716441c000062250300c2000704482c0400340d0702014813403d0680c0d441c00e985040800c61100039000383c3e60a030701b010301c24043c00c0c0340610711170400544461401064a0095015070841c1c2824400d03680442851406001c0490050442d04040f500d0f07540c80d4415486030003102c244c40c032841c44542480354229802181c204100000701d0030041d500da01d0701c038420b03501d90560720320300652566424090300300341281692048290096519544420804044175100085c4450030070304040b0001d130a510030420500d000e030a0848145d008081404202d0303081d500000821104000000304402503e003140b0510340403031411a90140c01481c00340d01400e44040c004240b0b0080c0170011541c4c3c1000034039900503201540c01c55100715a43c2628800ba01c03010349162555507110070089403140302180041c1182c14a10100020341c03015a11220300e242c0081c1c404540b03205a003001007114503c1100881c10000c00c401c0050b4101f842d003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 671940089 1250 671938839 671938847
    0xd0c06170c1612020309060301030309140d02010f111203010902071b05130905101103090c0108090a06091506150305150a051c060908031e0f010b090a230f0d0201 71
    0xb1080081100c03180c04070440c84503100784240c8070a044090003007a100e503180e28000c1c0209080d406148040042d00441805038a000b0891065071501a118a55a2207404204441da01c10090210219105844140d900410440011402440025801a22080a0315012400400b00031104403446810001404160b8405120408142d0a08000078030001e45240c80350421f036441d892203820618205134408030203081001503114808080c19210600305d600010b44da505000e6035081020f500884101000070307100c4d480300c500c0a000d144502080c402107851070050b01c55640040744000500c442c1c44900c55018060180c01900c4900049501054400070903550541c034480c0d148900069841c0410716040781101d0300f607183c0c21403418440c180107130520500c1a4410341ea0306403030f03800b01c42c24200d500a40480b0180030780121031507450039034600055449181c00a10509521024840000030b06c2c84880c091541007581498071030340001510410001e004040c444c0c040e008071702440710030707005070b0348 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 671941339 1250 671940089 671940127
    0x90a03080f0f0a0519090507050a1203081609120312060f0b1c020c010f14060913030e030c130c1101060f05090c0403051518030403110405060d0c06170c 67
    0x3d101c00001c00350781e407021300b0b91907451843e40c0016040c6000a0401405800710b442d10913554180c0303100e0b03086541c0f600c00700c0e4120103814001c1d0000c1c10140209101130740b0302040925a203c00d241001c2e54035120b410385805c800c40b0a0046000c54501c0c080d80c21078042034050b2000070600c4050304c02c010392600011a030a07209045105a004030304805075000408a035040d90b5418110130000c000c045007003030030040140881401c0e00072005255001030b00b14908040a644280408807024044002550f81620400b000c1c000056141c09020640303d4503443d5103401c201c00f2070180001181c500ca00c59030142440600800009003a414041c0c18803a840300f5100300d00c21220190380c1a07200781d450402050f010b002d5600b00400b140500a09101800e0346149414001c1042c48040c3c01d03030140c0f00c070502d80c0e40c0c422484001c0c01d103c1a20491246441c2c40d5010560007000948415403001070341d6584440b250040e008213010501c220032807030304d208107d044980c4c4200b9609a04d40703085504800c0100010b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 671942446 1107 671941339 671941351
    0x90a0e07031418031c02070f06020301030618082a1b010216080718090c0611010b01030203100302060702131406150307090315090506090a03080f0f 65
    0xa01050000c03a100020f94021840c00039a00c4215504850703059040345055824003a0707002196160751f40400039407088000580c2da41c1549000000c071410140ca040094040001000026200e801210740300e0b4900400070340751400307203d113042c4000d4000241d0321990107000400c0d1221000c0c0c1c440001310400903000e40c0c91014a0550406e22070740c05100303814007135000c01d40401030340105030b2000c2004840700101007641070b215140d140540304c45501081c00145242588403883c0800c1c49031514000c400d2070103500e1814101002e134103400c035900019204607000200c02045587d0070585a800c402c2c00d030018002281c40b0000d0300c0d0601411640b20b801071448075981c89045001030122446041544c56070300c011810340d02c5000100d0040c000000307485944900010224000b00040d0344103040e030742e008000c4483c030343c03400900000000c0d0502c40d148615006100600000382c5c1060f0b4001 = true := by decide +kernel

theorem cover : BRFrame.Cov 671762589 671942446 := by
  have h0 := BRFrame.cov_init 671762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 671762589 ≤ n) (h2 : n < 671942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
