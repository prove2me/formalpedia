-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0418
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:42:38.28213+00:00
-- url     : https://prove2.me/submissions/17bb2a54-28a0-489b-87c8-b2f43a39f3c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 75000002 ≤ n < 75179858 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 75001252 1250 75000002 75000007
    0x70f060f0905060601030c03060806040807030f05030907050103090501150609090e0601030503090d050a0b090a0b24010806030a0f2108240105070206030702060708070f050301030206070f050307060c080705 90
    0x411400f01c0c070164030500900c1e0000d1076908114050340204040e4111054034440c880800081080d40001015218041e40321001541e802c158101d84a1008445105040c2c00c003510410031940250440441c49201780008220340c1030760030041758512619400b1500107400448108001d81840c810003040c200b00402400c443e60641d240d50340d8038403e2010407405807010013081c00078130000b4071008072003e81c451742114081c200b0310202580d03601c108209803103208000001c5803080d100a40f41402e802110242070f882c5144410040d50040703001028950036005003216140007401080501d02951b100d0128160300c0c5030420003078200b22120900036010301c02c034a01807150f01d01c0d14000c032441115907820b0003507e0141000040714940140700c0001d410840200500500d1134000c19542d00c100d00325502d0143da81d8403450106d0f595050440d82c640801c40800c0140b0142c1459002040501e0040100c4040421075903115440c6074003152064403002d075524540702546501860300d94001007903103445030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 75002502 1250 75001252 75001271
    0x30b090f1e0708060102070603090f0209090309150c0601090204051e0303070f0302010c0f0503280603080705031206010804080322020a0906061403040c1203050c03070f060f 76
    0x618016018215a0510198000003622418120811101c000140401074940d04000c6000303014038400307858050241c001c2c0f1102044541c071034031860024507000f074601d05038031000c0c0c0c090007507090003c0d140e108580230803c10018144ca65407110000b0036101e0038850790340d12000d410b43d420b040042c0c1005201500400080110341e42c0d4003802411a40c0500840400848060029156220748040100b608d52074448020500d9019444200c6240054a80400c0c1d00300102d0102c031280320803148000022082c503d8440d400b104020070100c010030424000440f030f900e9484219081e00700d1103040310240c1c40003a8031640300741c4111440c2e80124080c20102a2070605d40d50f0010a40001040043c8505826840c0301e080d90f45208403900490f0090308100c00c180c0c07104900409050300d40561004130722003541c1040e000d0b00c1501141e1240782c2140904c440d01e41000020a08410301c90002d804018003400302002400050008210303240c481c052007070011b001071520700180c43c0600a4803140030f20b041e00c0b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 75003752 1250 75002502 75002509
    0x10509070303050a0e09100315090302030d020702120304030c150224040302010207020a0f0609050303070c0e13080406030b09070302120a0b13050a0204030b0609090d300c030c030b 79
    0x1903041e254141030040e110503d2910446101342810112588480b13820b0911406400d0000c42100f81ca0060300300b403000399a0400400d0a94107005002001a8420440b010100e03c4940c06413032355034401002c0344c014a91020415180d034019410036102c8200030b480412510503036580301c22a242d031900180010321284175400131140d86101d4060402203680c0001001c15100b94100c0d0310080e030007402484041e40301d000700c40440c04103000c0c05001c519035400200e9540303000801d4410540d4000e00c1e5088013400c16205044000740949513500b07030850710721800300180300c43d0040c1c0b000c1c04446e68002841c031100010800c0305c0c18080c00010506104000e42003071803000301c5c0120740c458030380000410100100c00102c0e04002410310345180031403501003440416207068004200700ca000d80c02d2503101e031711008100076624000b0f40c1d084006070b2007507440c3c1c02120300942b4081036881d00e581c0e410103000025a001c03c154150586500d941a513980b051308219a0144101d00101a451400304443c82058012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 75005002 1250 75003752 75003763
    0x60d051e040c0e042a0509102103050405090c03070905060408030304170d060b0d0b12031905070204020c010b090c0f0f07080412151406060f030709030b15030f010509 73
    0x54030700e000703d8207001405011360300f030038500c0190f24a44851004c5262801d0188406000d0052a1107200e103803002c1005030704a2000c1d082940d203540001880c42060070031081c89002c400343c085042c40820b100c0081c149d641e02202e01d100d10005c0b15007da0744c0c030340039200030f0a406031908003922401c000c0c01309016080000080c2d0303500940c0007000c00070311540c000e42d40415000c0c0741250b246039420900e020480c41940c2c40605800e2448484c2403114204000401c01400f40400c1e0b02c542552081c403082180e4101c1d030126130840c82e05802e02d28a04500740e004103040ea4010260b0000e0342e9111425868a0b00b82105010392100029144c035042000d410281c0d00d1601c990641149003032000b103000d1080c081c42c0c004a4000340f85619090744400400c2c504980d464047e01129609140b8054a0101d07000404050303a1260000405203032400d900090441550b4001802c020304119114402200162440c011140501c28000110b9100e825010401d031401d0001c0c040c54100d039040000344807645600048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 75006252 1250 75005002 75005009
    0x2160215030f25081315020a020601080724030204090609021209060402011e050405030d020f060c04030c060c080702030a060e010e0c03060103020f01110105150f040203042f060d051e040c 82
    0x10401655110035210824288007008090415011401906c2c9010403d5009101003800740d02550b00a031f903100b000307603206d100d0740c403441103030070b41c003100c545000b0381c06898001540d03080d8103005007815150302c0482c0443d8125000005403030750014a1603000c10203ca2020381c4900c140c40240700e907251540c0000d185411041d4444018100c690391408410b00071010b640142c14042c0440320803810319500259600c00900d8028094050440801c1082a2074812130b0203498100084100080c548681204c80240155003596030400511a40f00181c2e800c0c050a141c803406207101140f0440c503c1e14003070071511055080342c4598007004d560921600c0100380141100c1e01220780140c0c40e102d400042e43c034014802000d401c1540f80c101001540603455040d446168400d50388520001b00410510040b448103480c007400e00c0307049003a52151004520000c2070030101c03181e01a07900c7c116060218003039420503001900301030340342d90400241c41c1a8001c20b1781240280201074107603040580700d540e00c0c55018013 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 75007502 1250 75006252 75006257
    0x1306080c131502030403240c230a03020d090b010501030510030215090105090a0306050702060c03040b0f15030106030507050915010813051e060610050c0c0402160215030f25 76
    0x409904903d0090090700c00854220403817011805020f0444529642000c009014007490054200c40d91441640710700ea07038804000c1e209008102103083d8042d16000020120209602044138142030000c50003607002c00c40c82a0314002055040034009015034a00030008003c040602d017041000d41c0e21104040391010649501c00d41d5094070000480300d5101d1180340c2900a018000008100034450340454812031042c1d0030f8030100d07141c4501030207032848250340c06815100d01801003805420043d4501e0340000b4121009860000c800002c0f07420b4a800c0d910995042e08080c404201c1d41c100710f020030354801c0d640784142c40d0005440c2c1c00641034900c0503003e0310410b0b9030980076108002c400c000d10a0303c280b40e05400161526100003055444000300c0304d09003c1c00742086120a00d41c06030050320003150b2040050001102d495043c880250081402203c0412440c0c84080150301c51040642d104c0c008000e03940d540b0b151200b12100c60680c050301100c031064419a001c90101240c80d4062000300300c52 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 75008752 1250 75007502 75007529
    0x60408063723010e01080c0108040b071b060501180605060a1e030b0a0909060e060f01050f03030706020301120c060c030804030809240a0b180103030f090801021306080c13 75
    0x2e40282d49003458a8080c078064010b00c500200d03202a40402c524102e82110007102c521151030001160750050645000b442010b8a1010030107890007080c20b58000300c61303400411041c2800341c0f51401916800e0b807003182c00703010b5039800300e0004a082c0141c80260606071070702c0386001100d010050890f4040c101054031603c9043c20715030310602c40e403c01110283d004211140140d1117a01d500004e02003444210b0785249420000080b4290214015104401920712640581c0c07a10302441502005244401e42c580030401030840003900602c05940070b016400d40e49490008545001000810250400750038441181000c4c2e0009078061081a4050350500d40b481c201c0d00e4545403a8a084070145041c01401862110f1303803601903520360100e2180710401c2080c001121900d09009801e00e5051202d01c03895a590014804030740919030890480710076280c09038046655480310781c00c907007020308508800343c04448104201640100c40d1508030541d041c00034540419001d0b6071820307020707901c2660b45280c201c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 75010002 1250 75008752 75008771
    0xf0d050c1303050102091323150405040605040332091f0e0108010f060516020d02030f060415140a09060b0613050a060305091506040b0604080637 64
    0xd2205644140d121040010742090300c0e89407031030103500304110301c038002c1d10403014070310810390035019041e45112030b0020800c4000e0800c404407001040185880d80750404210f241c003240d1181d10499214a0083d140000d0340e08043c5170052041103180116419000f0341c1d50b40200903a5000441d10f1305070281249540e0364082540444c000482c6100240241c4d02c4050b2071034a2240c0004846c40c01c80b0090362505001ea80b9440d800f03055440b24018800000c90501060b40d414001101e60380d019400144680030444d101d5000910300003014501d00d41c140c110106000c104060040f610f0320292207201e081c00311010b100c0c032680759074800078000a0084d4943c0010814004554081000c10740302800c0c040d81c81c50391200380d02500410b482030502a0358807401c0005c07064480c3c81050b008140b11006896807002600e8542d0360140d02800e081e9005a942c1001046a902d5500900c0180381c407002a18151400c0c0465a40260b0306810f01c040e020300f00d00209a0032500c10060440d1003146150024203800c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 75011252 1250 75010002 75010021
    0x150c040e07121e06080102191428034a0106060f090f05010906140d050103060b010e01022b110304060e120a0305090402070f1703010603060b0f0d05 65
    0x4a030702c0c00d4a44145010400341c140c46503180d00f9080440d0740780c0140103081c0d59001032802c0b8420502281c0c90b00c1c2c2030003100c049052051102c80c14510003410700078180705a50146190301d0b2400500d0380280400b00030510881034250107800a00c4001035084d1a458070a0403460511200c2c4107100428001d03428000c04056508802d0801092108002040400d44400d0084c010812810486003c1920388200194a46000d80303904103940040c0d43c3c0150080c039000e000d40d102941138100c8043e001c1c0602089852060358406c0d00d0003036003d0b08010034107440d50380000d002c5020080005046410640d9250003101103144110039000b1b2100d04036002000b014801c40700b001588009403520302000500181081c0e0004510701020741c112041c038801a0304841c0d16a07246071003c401000b16000303104110303851420b5405020b07514003820104006100302d5813400007072018458088000480840140542549803043e90b02601400e030100745441d100b000400309031b005084118500b107031500001641c182e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 75012502 1250 75011252 75011267
    0x30403050a020a0b0a0b030c1909181b03030e090f010e0a0605300d080402040207020d0203030313151e090309030b0708010806060a050d0312020f070b09150c040e07 72
    0x150000201c151508100102a01030446c2c81d04a0f4841c2c40340180f1300034246070008210b08408804082c6814162038000c0c0304002d0a400d00c44144050104c03000c0740301092a030041904804c04601c0e83d84030550661401405104030280b1050064008101300000740d55000803483c190350218034040c10719130307804500201070170b9503803c03403500300400d048030701d00805550740c6484000c08005044000c0144000403266a0342c21441d50307a000422050108001d03080550040c2141030000e0f00380318680c12141c0110345554010ba410fa07020060444441c1f050000c0b001400c040440e045074144001100c440d141b000c00c0382540030b0321a21741c1d6540b404104050059601c2402140c0c08270180d40750707140401c2c0103405060244604565802488000380c518504014100c040d204000d105021564050320122401d60304942e040842c241c0c204202000c0e15504006050894443d40301c001c80c030304c1d2144190382401108201102101350303140a002c1a580b252083d942960810004015203603550007007224244d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 75013752 1250 75012502 75012523
    0x302010f0e060f07030507150c09060522080a0302010e0606010c0b1512060703050a0603020d06151e1403070b070b040c05150301031a04030203030a0e0a0602040b0c0607050c03030403050a02 83
    0x160001084c0e010950410090030496003ea0915a49504150303040c605a4200d590034000041c0c0412003880414010406400b40040d4003200f0a03400003174503102000d894540c3c01c540160383c0201910802c16609014603100300300b89601030803650408500103048002840740c010844040c0c100064010180c909405800d010001e0503c09442c0c0400c0e54152109001d0302d411000a0401c400100040b00300d005601c1240c0d40504150310408a584451005164a2005000d600e08514000034214a8285000c00111900c81c011025516042e031081c00000c80c1c150340c0340240c0003a4000c0160000520640d9140380d0420502c2003950340383c2c94004000c0600b60406544140003400154540005e600070318140c0b44926981c001124420007034202030081201c0c028010780c0204001074183da295040f0910410b1001704031800c0c4507455413800c050fa01305400110358110046200c0ea5026810043d09030001080c2c14218a4902d058015549034800204042d09002c00000d2252091b8820014007460 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 75015002 1250 75013752 75013777
    0x120c060f050705040e0f0402060f0714010c090f1d070c08040803040e0a0f1802040b150706021e040602070b0f040b180f031b1215090f160302010f0e06 66
    0xc0e403034040c0010303100d0313080b43c051807400a0a90000410540d0650325590040b0740041242e42083c4960b0021031150b0300211045401c2c0c01c4500410341002000d0242ca001071926460380c0c80f6003418145040050000e551001c0c413141803880a0045040003c40c03443d420a0301c4d442c0001c00c82c48181030080c61480740703620048551000041c001600038070b26465500480c601c282c10320a00410013094400c0d42e1403c0c3e03552050320f0b04403c43c000145002d612101742c046019006200040540d50240c00035080b101b800d036245500010303030001c0018a111030000e0881c4910701c481c14a401c0002c02590b40c070b404d01454081d100c000a0a50544060f4000c1e1801428009000d0703a840300d001c81d440403880e42130201c00e401850b1100c0b40f8819880d0200b54064081050b20884d00300042c0c0c1d604105404d45101c1c1030710445d006402100100700c8050b4203662081100c03100a00c0181040341c0c0b000d2030309082048000690169810610050f80d1081c4640000f8040780f810b03020030409400010040d2068076070f60000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 75016252 1250 75015002 75015011
    0x304030b07030c1202030106080f040204060909080309070611060c071506030807110f13091e0c06080f04080a0806010201060f080a0c0e01030503030402130902040f1e09120c060f 78
    0x841680c19000b50807a881c05981c4c0100412070080c240c000c0e80001e008a4011604e60030000b140c2850300d042c0e40d5031103800208041a199034030390848081341d401c0f28007910002d40000c1008280c6100304a800e005002c90300e80703c40d102c0c04d0203802c00c1e12140c018143e202441c00010301501441058000300208000e030b01d40420840d6a2450000783d56030101108440c058600341644003c0c2c600385601040400300905918004415225502c0050031151011541ca0440709019a000c7c18030441c0c00040522400c559030350503090031400343c6485d800411241040c0e83c68004c020010f5400c00a8034110481030415a540340c98640060317002d000581c001c601d085960726000030b4044800181030081c2130140541c0c5900c41e444100308041c0710310900000e015079000300041001414880c0030305034064011100000c4800c0070743c4c0050140c034070000c0c540342c3c4203854000d6016141403442002c004101040d0003080301101c00e0707031603400b200c0030302151006100b84801100c045c8040d54106284004060b00c0411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 75017502 1250 75016252 75016261
    0x309010209031e0f06010e01090b030307050115180e2a1008160302032707170303040c083403060905030c0c0a0e061009090203070305010e0c040518090304030b 70
    0x220040c885201c620444c8909000610210070114446050701ea584a00031040e030f003032851400140262810701500b42c40104a510003089080c410202c1544919021300d81081c03614914440711601100a5440c003807404000c0c148100c000640d02d0702d4480c0c0071032144903101c424189036040f00003889926400c1340c100d4034007050156100c0403142c0705481104018500544400c2e045040303010881c1d0300c03540140059074900c0d00354504c10346c0524983c3d14000719600c9640300c0f810340c102d00b030306208010030980c00481800204a0701f0740415000d024050700901c035020381d4100403156485150342e207414221420350b0712808032100a400303801450b00003c0c2848251054070b44195a984202c0242d2403a000d4041e0107000c0d4900780c5c84c40d200311790711600040310a8076007100704511030309000522414420030320382c0003410000038009148100d0342500c0004440d032400140f40d4000400a054607010082048284419a22484104d030b010409845000c4a42d6a8524032891072080740c00103490340e5090810007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 75018752 1250 75017502 75017533
    0xb030f0406150311040e010b15251a06040b10020c030f0f100b01020a020a030605040c06031506050708070209040b090f070612050403170108010204210203070308030901020903 77
    0x94000c5104800400a0882c4a96450010140c5000003009a038120040c0c1d00c0314030b01074200c800c410101d00d0001460244140000381e102d05940d00d0070f12002808600b0032010410b001203100200c101d40510101c91a182d60390302ca50a81035250311896810110216199403140e0740720001c4504050b004544040e07a07d4006540e030070360803010078800e20601c1d03c2d6905441010802a9164040d0704c0203041c06005146135602601034170344164114410002d1450260303a48002d0a03005600070800000c080c206420404011490303600440c007803600f0f0812903480601c80c100442e04890107880c0076512000707140b034110f8170b902c0b0f2003c2c043e50049648060105128445080707a02a080c141d0417201d82c0300280403a59240e880070320403507000c16501035452066108036080030b98031500c06c2c03600c02c41d24807000d544c20f48002001e070030844d200c0e0740c0030606100307960001507484c80c000d1b0a03c40b04401c52a29600281d03685043e07000c000c004102c0440401d9010600750140c0e2110b400042c181c40041c140035050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 75020002 1250 75018752 75018781
    0x603060306050c0f030f040f150c110c060a050a02100f0b090a0e06010302220903120b0102010605130c05040909080306011b0f0201050307090308191e020a110a0b03 72
    0x181c411038074100200d482e00a03c00c1c11100803082002c522404d540e034950315980c054100400030344000340035440240c002a07c0c108042c2da1040704500000300840c03c914002c1003000e010b10070010399406030f600601e084d500d11056500e84411807404030f82d16000040100d041400c0a00c420301403a081207400707080d20415400240780080103594a6180e903032085414020388209505289440c0c01040c014409800c188080010341c600c0b20000c060024400ca03440000c45034034460940004130041c050701008803a0b80039440f44d030310091000b400241c1c14080014985520b40c190110101d5440c48210000750143c002d9600400e19104100400c03456030612202580c000c45403503000a0a400c1e1480a02c1e15603111145069003041c14141000d510342e0056901e0303030014101d9030502030058000400a00c020005260159070b1801c80c2e26810914200500b02001841500511088050300441503d900262500760326401c4520514240d0300c081c0850720f4450540c03c01c0711024170020400099000d14943d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 75021252 1250 75020002 75020009
    0x90a020117340305060d11040c0e060307020c010305060f150912030409050a050711060601080c19111006031e0c0b040902180319080c1603030903030206090c06071202100501060306 79
    0xc05000955514042296000f06c1d100024031010b61508088031034200340e4018440202d070b078240340080d8002600014041e400803191140140d0007844081039559140c0034850700705c44e00b641c01c0510341c0c0000c0700190a0300b02c650a610388084020481d0501951807880c0d41038410b81c00d0068980c0d682d2940c056102606084a061030160f0521f03000c03030402842003590600c0000c0a401900c680d88400d001110ba03c480540b0700304848005000410400c2301c69800844101c206071a20300d01813203031012080c180350401a101408500d0301104102044102001d00c80c3c404a0164155801c502c0380381c441c1c9030720340c550441003484070045404558401c0300c0d130041100050410390510954031840815964940001140354106100301410300010505400341217408280005e0350807000198454540450540d40103400040d1070110400c20b064050207220780149418020304440e41002000c24203501c40c82030000d21a980a5043e10b1585200740010380c00917110640c180980d5a40f5107004029214500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 75022502 1250 75021252 75021257
    0x70b01030b0c070206191716080c03070503160c05060412030f0e10110904050c07021003060f0b09120d0201052409010311060c1c08090a02011734 64
    0x1c01048100c0c0002e030a40d640780b0790081016180c004035900c0d2141103942c904e00c400500040740204d80701480c500782c0e150f10403d16540c2011100002c0c16004010071400b51002c074081d074040080c4540ca036030007000c80b80d00000c6802040041111000d049071400760a440c0500305020b9501441708126280c41d0780f24103107949076410b00c03001c80741810b402e0444d01c2c5101c203841203034012030410200c2045500701c000b01004c0e0810160170108540041070076200d0071614079882c1d40c5d0000e0304a04624110380c5154a482c2586000c0102c01d007848044071014510303010712480c46c10042668001e69039240000300c8020f02440580780001503c400c00b034064003080c0c031a5504441c90071980c150390084200e0030342d150306006104010302c0e40307162034030b489034200d04000700e4208004000030001e0280030042401c1141d555101c0007001000c120000341150806414494a508000708010250382d0020046480924603110740500f51a2410303a092020b002c2c5034100540c0c40100c2119004008000182007101002d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 75023752 1250 75022502 75022523
    0x7081005090906190605030a060207060c0507080a03090f050307110a092003070c021e0a090504150f06050307031412040806130c03170c010e030a0210020d11070b0103 73
    0x440800c031282000b00d58414003940400c0004a00000d000035062013001c021000044c01610303280482e042050805080d200540c0000b2584104000c0d03100c0c01440c021103141c0300742404c1d4641c5d00d829242c031407000608100342d01c90741454140201402c5806480380c0c4001143d40c0c0f030910f0300e8100083c25103c80000d114035401e020004901d4030600445200038a03144000031030078100c0c2101d024540014003a03504000b8251103440c0161910081000c91060890590411b582c80c40200444a4082d8102089545c203050078407002075000c80d195045c1504854000c105400d00308420001081140d02c0b442e810706c5114400010320800c42c1c0c220200100c8041030317402500011018000520035072060b0141a4083d9002400403010341d111003140921501c581081265203899401941e914220b40810000d00007400013400c030070911441e58034400c048013a40c113250207100042c1d02c6614100001c01c1094002034503644101c12075004890102c83e0240d419122401800d0880281000740411038280100313 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 75025002 1250 75023752 75023759
    0x305060102030c0c2e0206090105131518020406121b0e0402010f21020d1b020304060509030703020a090e0f0a020303092206090e01061217030709030506070810 70
    0x1000b00d07003420750103038001e000c511000d2080c8941c030020740283c02d61540b000081c4024072400d1955260311725009500a00e11401c100d502d4508482d4003030800c07020040d60300d01000000d400f200c0c9201501c0320031000020700840c0150b407604100031040f00258007a00d480c00208010f110311268801700da005602c3c19900d151540750703c9400203101d004c0c403c0d03040c0c42d0381d00180c0190b12440300c3c0c8601c50483e25000310015204485811603858075a0800075254011402d1281c42d0380c54412401c00030006480510280c100c0c65019407684554003906007041800a5a5580c0e902d04001c16401954054814101640d5960400c1c5c000e1990404c0c05400d0302030f5940d1540701e42800500010f400740c008014600d899020010407000d8501c01c40c5001642c0451880307018001c0007881200b008101800c4041240342040b00c4042c00c4a40300d82202d101102c0460096012441d040c0702c91010a43c03510a00b41c2d00d88820600380da51941c90b42c00180188680d10030003c000d03501030b5030b6500421800c554200507585 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 75026252 1250 75025002 75025007
    0x30902030d05030106230d050603031b0a020f010309111201020c1005070e0603010e011e170708160b0d0f0b060414090703020901021009061e05040b060301050702190309051f03050601 80
    0x201c241c5e2484030303000070311004859141503841640c09c200002c049030310302107107000411801001c4c0580b42c081a0000140c1e00c095007070655103d00214400d103030030003141085940380310501c1d035004802c6000740070451b054082c550342541100c2042100504598840c2c460802417009040300303e840c80b000600b451204107960402209903416036141c030000100e0382e03080c0305404503660800c401c01348240001250015200a00c1e00002c545000414043c000042c2040003080c030f0400c80007103103d04c0140e001401c01088501c5c0c0252010042c0f1013001045a050701d41d0303110054855030a0700d507404180080c0009018481503841014650182c0b000e950b5a074418100368200d000b500710050140c4c202c51440b0010100691202e0b402c0c0344120320003d03014500f0060600904110001780c1085039a0702c0901091180034144a0381c0250214000e002a00c0c1c4520001c3d12503868a6880c01c401d42000d131417208250050501001070030010301520400c843c10940710400d03004502c0010042032800010404030751 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 75027502 1250 75026252 75026297
    0x605060a050403080f0706050f0f0609070e0607060e151b0a0c030c0c091a120115060503070221071505061e0a05030118050715080a0c030902030d05030106 68
    0x42058031518201407031038a94035115809505030302c644010400c146c41c0001c446105281c0a0141c14011281d50f14201039942141c90018103998465150201085045a4089060500400c003540c50540301e003014078040300a0305401403c01034601848110380104140410300c2445981c0c103960389070f0341c0c40c2181d4a50035a0f00c1520220000551024400c0010a000c0c14100400920500c018444141c0d0790048404541881c507142030702c4803000340c0350758052170241f00d40c80306480904005c1110b96213156145402268602c0341074103004000c00060030480c028002403a518001c1092011a03000640c442a403640c060301e01210010300c505c00310035101615204881c40340001030400b03144083c1100c042c00c600b680c035024040e44500300740c1e8082030a0700c0a00800164000b14600c1b40c0c0f002405140c12800c00003260440d20f8240c650314550b0740240d80c001c100c0f5420812042e000950594600000c90240c03c100d04069014494060751603203107640070000b14121442d0b641d5400d00b012514a1125040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 75028752 1250 75027502 75027517
    0x60311030c0703021009060b0411040b040501080408120c12070206090a140a0501090b093009010e030f07080c06040f030210020a02090c1c0b0303070b06150c10060506 73
    0x115000c0c400a900ca4142000401c401c9010b401201c0d44894020549000e07200e002008580341e94945c00c42c0e40c0f03207061501070400070401002c40c407401c1500f8450700d82c80a000718443d050401203102c01040c1030090b018121494412105201c00aa00d40400c0c3d00450354000790f61a01d03d90b5011002131485031000c00d01d01c1c090f503040e00142c81e54001035154a400d48850401780b5406001e0700818100151091040040b401c1c4604125920f81c44c0602d40e5608065100908421458a104e400641008200516201d0790b54000ba070700e0716010b8000040b1031001c0c664110540504c920b00e040006101c0008108046684a204031449110140b0600031035001e20702c1755048200c080391090005241900c680c0d072442469104440d40d500c0181c00091140200b81e45c44801e28000288003c004640c03446002d907500604a8107000d825440004a6030f2449081c2014025010b004081034440e510850f44000000a085046440d004440c1c0001d860300819040c4c28161860a800083d01d41060000e44091 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 75030002 1250 75028752 75028781
    0x4080a0e0607260d060e060a081903110a080d020304020a0812090423010609080607020102040e06092a0901030e070803040b030703020708040f14010306180f0b09070e0102070603 78
    0x41183c480007024903030304a01194452180912221240d90b1081c4200c1000300070243c840344550501e40c09102918126802c000c00680011b0a85c2c0100042c07084100e041543c14a0f110380040650f846c4503003055090b400007013140e4070004130350520a560360007030360045000b00d80400d44030303503641c040940c0e0384842681c10b5401982840215000d182c10361024290380c030300b0340c04a140001114042400002c00f41c1040d008108458002d2101c1d81e400c020042c0d001c0700314002145044e00300858081c03560070082101d4450712084001903d80d0040c00f00e0f914101003c40403060140302d02d00742d405555000186030030b0009241c14088500781200061410484042201940ca09414041c0d402d005070b0006140350f042c11340802400000410720002000146250328401000030b0a19010001411019061b01d04150030040b0500683d40c4401c2c104480c1e80003c000020340c4054248218081c020802c0e585074400201004c0201c51a0090152000700000b42d0a454109841d50019421500341c051003200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 75031252 1250 75030002 75030023
    0x30c1507081302090a0e01150608012303060a0e16030305090f0a030b0c03071110020409060506031b0c0c04020c10061d060120010f1508120f030703060b0304080a0e0607 74
    0x420950550121031b80d05042000824960105081d500c5804102e910520008280f40010090b40044405c40e6803ca0030741c003110000c0d4003202d4000781d614807000d016810300942d0340d0314040500c031040041642800580940805c056620704001d04070b0740100f003400d80501d6201c032040005182c900d0060013566400300840869480e400d40000f20b40d0401031180303003131144083c3c201002032400c02420129a250300340141c0e46a050910a03c00c3c0d0700598030071800b13202d06000340f24442504016841441042c0421581c80c2c5004640b540d18210404146542103480061003034410761010400c40940e80002100384001d035030311800704601015142040c811000340d8400b0849542c451070002c45101030342c001f90fa0500085d400218211500c0141c9004910b58880d000c44c06e424445103d80c0080880c031010b0f0201074400c0030f54205501c50b403900748030303525400000070b81e0590203a84510040c2080104a5899140a1a01003480d034084e4069078081140c412032010b43d454424101c0d1180382d0f10503034884 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 75032502 1250 75031252 75031261
    0x1101060515030f060a1d06100e010e090a110403060b1203030403051207020c04020f070506060102070609090b0301111209070e01050d02010804020102100c0309030801120803010e040302030c150708130209 89
    0x1d68108050304c815804a64000000f401d401c0080c1c80c01e08000184c0300c0302c061801d0450070081c0c0026000c0700c600904c035030101d50845582c1c2041c40240b902c5c03015a03001c100c0740d9460382c8500042103100c1180c041020045008400d000056014212501040e078000401110400c0150350720702007124020000303901005404d030929000b245a90700034501e4011504030f05124400601642c00c1940e913110314020104030401400001c0014607007241003800035014940c1030000080c460002070066001c3c50340c0350410702206d518254886001841e0040503a900e620300706c00810758021083e20395210511130301c400451821146c216081c12a18010520500c15076075a005680c04e40004105906501803000a00443e90709401101c50007407940d07400003045c660790b00d80030f811300006801031940340341150031910009924000f101c2c150351848400401c96030755894101c4ca103101e0811041d28a00072500c421000131a42482c0d28040d07901a00d80076050b989000e6003a4403032444a070043d5200c43c0303600200c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 75033752 1250 75032502 75032521
    0xe040e1603170403020904240b09060d1403030403050408060106030b010e0114091203090109081b01270b040f090b1e040603020411040306151212050403060507110106051503 76
    0x20708541d0803403070384641400c0c1e41740c00044030300400321810f651034040d14500f200950301e0744444105424440c10100800f01a420105c1d034558030003000740b07015001481064052080704505084c0041705d90003201d0307403803420b454024581d030890303c119242417041300e00118407207000e0700803061000410396401028440c4c00004680c80545032002101c0900100300803241512007402c0040c47d0083c6a006554801408000421000c1240d1200405130400c01c803e1140500c204545035031101c00740707084103100c04241c10080c1d1616611042c5501610b9491001401c00700c480050803c840d07c09100c2c011903940c0e06031000907683e804101d5035208210381c003404003510183c1d402d0401440003030000104261254007140c111181c1810951b040480071508200f0002d2a000c2c20a843c0b82e8010403c40f464907001079030305e5a00ba0000000d0159501d24221360141c0d110340300750f0340110b801803018842d0f0704002902030407030308a69114640c2d6500701240841c990501401e0035038043c072041019442c554030205107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 75035002 1250 75033752 75033773
    0x20a080a050405030a12080c0a0c080304050319020601030b06060403020123040807060305040b060f03060a050c16030c0c06050f0405040e0106030503030f0f15060f0a02070e070e040e1603 82
    0x40105204042c4804501d944003008400301d0383e4407502d1852200202044007820070740c00285455580302c41045020085603201b0b0000c604a40e115a159440e62140c0c40c045082d80510301980d2000303a045048100c51944c0001c0150407640202680032803034560005119072803140d4000a8040f6400d007007641c40a0342c08441200d640d004040e4818109516200c0030780c24485181d0080c000640c445040c00b003070001c1c440b14281c006d103040314072401c10617121001c01c0d240d10000700024040ba07074500001c1c010300000c00c221a0200400c0c14401001d034800d03e0094014500850140d4078035000b24404030340c56001c1c1044800300071070b130008581001c0c0382400300000762520750458130095484241c0000001c03000c10156002e00e001014584a92130004031404450b00010705580400b94a04910300044c0c40398400c0b60840709450308130300e40c2d43c0740042c0207034a8070120380d0000c540b83d20800200300c9502d90000344542444c0b001c482c00d00c1030441074a001681c410b01b40c1071a64021080c880c04000183d5082d0340e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 75036252 1250 75035002 75035017
    0x20106050d0210090b0406110c270406110304060507030b0f030304140102030d0f0204061112070305090f0907030b0f060403020f060702030a060608030901030623040f0e1212090d020a08 81
    0x44c1070082c03d490b1014140d00d86c01c264032403030110700b490407038030000038003840500702c4e602e02038400300003034219003a4000400b000c071400c22001c3c65a84000c1014408284c01c40c100081c240180300382d5034101480c0100091200b01c9900d00080d2030114009200d1074003840c101d200c03920040c000c40c2002d0070420a6104401601c590605620040201c100c0d007445a000e00c40c3d184d001564010785031407410102404601104001c03441d40d4105e41c250b14003003a003440544140c281c00d46001c581300c1503130901295448020140107a4080c10b00d1040140c0ca55150f00300550f88503087d54103078408180c0000303000d0300b8007503400029840010158a01468140131001d4100140003d0403100e800c010760329034000716180e0b82c124a4064100103462030071560140aa0700040140c0c820b4030305c462001310350b0354040c14503402800744529114505100108000d41010051250281c1130320350007600c6600544e05940700300400e10803140540006503011501107403000b102203141d0058101d00e0300d140ea07a441580d00106 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 75037502 1250 75036252 75036257
    0xf020a020f130b03190c050d051c0c061406010e0a050306010905070302091c02090f01080d0305060402220306050a0b091b0d05070c0312050c0a200a080301090606020106050d0210 78
    0xf0040b00300d6030b40410208a450a0041110045903094188401a4040c503040540038410b07400e01c4030b001413400540c868480c1588030b1144008081208100d40710000d900000d0652030811100e0070721902d0b5003540c0c900549013603e1320b050008905c01807000d81401c510482e94181c01120041012800c0e031341095a1205040c500180f0b03042c641400600c46010f03910300d200481c0c690111802c114281840600d41000c2074555091066140000c00c0d0740e103507240d03442c0c40105901ca5010590584030340d0150b075400a940c0120310007010100c4030030000944503101c00d503000c07801d20002c14012040d078030464242481c0038108041e203698841c000c102a02c520345180900c1401081010020300b128841d8a010b10318607a1080c041c00300500b0028803a04214100b102068909024440340300c412608039001174485040c4051140030030100c2801c40b01003940030345024002c141d001c1d01000045801981603550070340c41002225100c03003080b4200d030300d1070061030703040070156400720094500415440041821403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 75038752 1250 75037502 75037511
    0x190603090503071704060306080307081911070b0a02190201080c070c031209090c0e1e0310050a2a05030c0c010e010e010e0d031a01110f0a120f020a020f13 68
    0x284e0380c1d046003000b484115450254041010b1003100c0c0d242c001c101c010b0881800550805c203040e00d03001041e109204002d00c80c040c40b20110305140b4014040c000074218000151a0102d40d01c0885503810390100039414014080c1a40001c0031400e981005070995806a607403200550740d0f0304100e22280d205034800d450b2044440c40003c001440c50b1601c9801211a0391484251498110074506840001c0d00302810300024580022542c0c403103034131940c42d10060a04034031201e0810000301e8246000e4641055182d4140820000e107034145401040140591001c0070b2208034420521640300d08403c00f441000800c10004159042880d1000d00514018880000350284488408a003107881c1031000240a0f5103d01b40810b10176010700040105c42e00303d0900744145242c448190b41401041642141071028030388546041001c00c1107580c20480d0014100c0721265260704240740c8074401c8004501c0001c1002120154080c4042040440035501604000100d5401010069004880c50050600c10341d103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 75040002 1250 75038752 75038767
    0x3b030d0b010507050d0c0b0609090a08030c0c0303090109020f09010609090b0a080d08010603110c030301120f050703080301030209070e030318041127060a0f050309010b060a051206190603090503 85
    0x600c040030b00030341d584d05c0721b00004016241000000310020200d0b486000460104a5100310100d030580009900044142c0d4076920140000c81c5405881c1c0003d10700e01c804801c01c50500b20541c00810118022100041c019448100300b180c4242c09010f40e40000e000400200300a6849402910300e8a500402d12040643c0b0f83c3d8140345042c09540000d00002d85400041000c950035116881c1e039561041030607840e01000301c140b140c0c0da00c410321a40401d0400c40f2801020b00100d80e0b05041165030000541d01e4095603030500c00750a4000780401e0707114000c0ea001244405004000410700c0c404060044e500b4904410140f05107602a90450798001d0f884407241c0c0800c1403200010030881409200c641011100882c4113411200e800440134040d40c0c0400800490715000503007095404070038a480760382c80e640c1d0b070722803400350102d1804103400c10000310700c51086d907030048040c0142041000090017150f44410407c845913104500944000c1500720b0140004c9119401c80e801850140d41101e10b400107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 75041252 1250 75040002 75040013
    0x20901171e1212060103060b0a05121503070303020303070f020a020d080703090305010507020d0e09040201140c030f0304030509010210050f060d06020f0409202b09063b030d0b010507 80
    0x11400e0b1502c811043d03401005425a01440b9280282000094441c100350b55118068a41d200d21034805185810100004200c41c0300840303100508d20f0042e040d180b0050303491801170340c0c0f50420340d50000420b0104030f0f030031070142c400140c0d02c0401f034000b440c4080b50301301c0c0c3e11604e80302e0b80411019001c00c2281140032010482c00d020f00c602412081e8014138104814800052460180705d080520400c00c0c030781440050b1b030b8884504035000c1034051040c0d036208460f00001f031843c030804004e40700d151408410403080c1130301318010705581602a000c0d02d03000d00328107a40c0d40443d0320490f950313401c078410600030070054104100701840e01807240750014a0000b100380a02102d0304203500140c1d021f030f22001000f0101d4601c52030b00030a03c00000b44241449040091040c0081c0001d0518a10300d0036021101c4a40300290000700310359420030020056142c032080104003600c04420794448141894180c04036054110a240750800e81c444040d50504410790080c80103005442d140d94104102405003501050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 75042502 1250 75041252 75041257
    0x2100201020903010c0e0a0b030f07051c0606170115022503020a0806010515040e01140d06050a0b1009050d060b0a0803030f01060f0815010e060d020705010603020901171e12 76
    0x311030700d81c0c0d440201c00604002211f00c080c1c0000740541401e2052003100700d43e6a091b16001143c03814141c3e110310451844007082c44100d43c0c01c1c010326040840019010f0342140110a503103a010502c1c0b104c981e200c0450f085203a6400c0f1b240b40059000c00403038a00c0120001e1002c0c41e030031103c01c510002d42c0d603907000110358500303681004c0610741004004008501d00301c40d540d41c0c15030b01d6503112428030303150484040700004148150129840040200401c0f640d44820b80900103500c8081001030382006240300e0004c002100f6400e004c1e0f500080c4500445000e140c451003100e2000b007c1c580d4841e4035954200140540101c0680c103da5a00d0021070703c0901440514810b000ca01010021507150100041078000c44045203010300c6034034800d12610122009116100303e0080c200b40100005d0f16020881d40e1054107541c2c11607510110b000401c111041d04180216402110340800c076903207800404d800b4014034005c2d601154050102d082ca981d40c140003000076054104145d80400c00c0e01520603c0c1c0e80e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 75043752 1250 75042502 75042521
    0xc0503070e09010b010e092212020a0201230403030e04090605091023040b10052d0402280e030d050a020d02060c040902091504030f0203280210020102090301 69
    0x50400390802c40800e40c2449011242c910901c1c2c0241040f040d42c020802c03143d405002c0181030f07890110000f111340c0c106240c1c5000d00c2d074020340d0496000d07c4a036000351a402c1c13000c4200d0004052001318005440390310041c4e0b00224101521a14040ca95a07040e9040c5603021281ca4000e51183c9200b40404d10034400c49100c1c5000c0400380c100c100207801c4a0040714003100351607210b03802d40f0005079060399608583c684c4c02030380010400e0132926018018901582030f0b91002e41d200161051440d4282c0354004407042211162900c1004821110201b01c20781c00727040041140d01c131124603c0082c00d03000600c3c000316940142070140f2000c07540c00c0032900301a20329840001007240000e4690603507a0400003a144402180b010709614100074052452500c5207220702d81c121900821045c44d5542d40d40c2d444810410039004c481e83d84ca030f581c0303440c4c111058100804d82c807038000c2200001440070010701410b80030f0702d400d1381d000e070f03200c0d842c0e00f00080701654031a5001190341c02d102c4d44c24261801d11640024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 75045002 1250 75043752 75043769
    0xa030906030e0106170312010f0e0601050a03020c0610180513080915070308040b0a14190b0d0b01031103160932090c01050708030f130f06020307030507050a1b0c050307 74
    0x487d6004400100f072480103134448004021020402c204641b001021150007407400d00e1300b9a40e0b6110110701310040d0154a8002d44240109001d20142c1e80320351209000b200e080103209402003500c10300391000c40d40100e41c407698030b4003200d88240c0004c07a140020200030034002c00c2c184d5a06410074052503207401c000b40c01c0740807808401c240021f11110400340344d409001c046080c84031101c43c56a0344840c80c00a8007010000001e40103455080f03200382c001010503880034115946181060800601c0c1350002c4c0301c15109050144030401c020f0401080810f92101e024241119080c6030000c0035009100703110f1009180c02c91045801c0c5c14805040c1c8600c500e02c120360008081d4108240c240d400d001c0c890024034144201000035500048103001078a5120424187d0055166039070900c40c441e0340129403006246c5090504143c3c1080095800b46014104955081266659200c0b0a840398032610070440d011800c02903284500c55001480c84003c10720416400000b65521008640f50000d203800002c1c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 75046252 1250 75045002 75045007
    0xe060c0a0201110a0c0b09010b030a0614011203140703031b020102120109051003020f18040506090d0c02150c0703150609050604140601202d0a030906030e01061703 72
    0x380380d424010004031400403e4264905400414081c3c04c03085103420040404443e1400111150b0080d8032501081c1c0016040d02c007030001d10303d0080300418002e81e4000c55110f42c10004038002c4100300c54012981d41c161547c88655406203203038092600021401c504140d25040008210586e0310242c070182402d580025881c1e980441d158240c03130105070000d00f815840c200400c0f090769801c5100e1800c40e42c042e034041400b44108000320f10b046400040d5032034042d6a520521040000014021744100040000c0e9651950900c000f10768442610201943c0086003414504510200c400240b0b2a01d00310070840382034568a07a10640202d080c5c404202c2c1e210340e00c3c2030030810703010f9038000d280c3d200c6812242009449030360480c041c81c010340588014100a0b10032003c2414000c030b0711b9014007a60041003141e840301410380d0300d0440103d500782200070390121000fa03c1100e6100183d036004080e815140ca04045d03003402c408030014034088030034031403664076044009040c244481d81d2909580000d03000d141e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 75047502 1250 75046252 75046267
    0x120040e0f09070510020304080d09080601060509010e040507020a0f06020d0609150b0304050a0615090e06070206010e0c120414011803050301091d01020a0914040b0a03020f01030e060c 81
    0x420910004020040100c0128200244042c01081e18025984110703508401c09448480032880d602894000d21018811030b6424910a03030001202c004880d0b503002250810307a21100200ca00d8080c490100340810340d40310f950500340c40c1640141d075003d80d6a204507500302215884030300044a500703409992480c0d000942d00c4004286000d40005401502001c1c4842040411580d1401f0a580b0680d20641000320128041100a0000310a140e030053300500a1000000e654458401c1500c15003002a01c1c0c400e501d20306410101e06a807203150113030060310080e880c14035284200300004003a813007444010803503400301d80004e80409000f0b90046c6a1054040b01c01c101c0e4a00316203c1c10a40b031101d2a000c1044000640d203c030440b81036a82c45480402c0241940d40c0744103681d0000c081e040d105500101e201442c044d030084589003140c2c10f07055201840c503500b9050008842d9030b00d030b0061704110500700078005424400031001e0400c0d4180750020301c00000301aa1360906005440f01e0b00019000a01803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 75048752 1250 75047502 75047519
    0x2030609010902030c10030b0d080405030706030c080f0601110a0318080c0607030e01090302041a01080a020c030f0304080f0c070609050102150703090609020306090d140a020a03080405012004 84
    0x2a03a005181000810444000e900041d94030300810140c1449044200c184060003842500b00c801d61540c0134021070106401c9140c0008683c2240c01032a00070300c11501c0001d0280e100c1c0c0601100b111058640000c2c135102e0340e64039004021b0090440f4180f090307800000c50702d01810040049140d00a65602c00060f0740e103507070030880440700d40c840203207580041a2040907540c0d81c01240c00581e40341c00d02c0322a5403800c00041e14612019403010b54410f141c030002c42802032068840740040d804c01daa81c418666a40d203140400c074015101c15240d9075209021256070099a040155002409521141d040c06000620f4283c1c41c0c0c000c0c1c54601c2d942c1c10495081280a412601060180070240050107900000169488001000034800307000c242e224030030348084c040e2941c0203140301034001d03040d034180f4034201c48429515040610300d80c00183c1ca94071803440340340e24a000c0d175103100e450344e024110443c4d05071411143d02c40090401da4680d50784d2801030040750003030000350b0a080b00c40346100e07494034640003e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 75050002 1250 75048752 75048763
    0x211c0e12070c08010615260f04110907090b0901030902060d0b010206090d08061c05160510090b0a140c06070c020f03060702060601081003080d0518070b040306020d0207050102030703090203 83
    0xf807820303a8105401030120008520021490680c2c07440e0007400c00300361000d4000f20000c600180840b40110005000481c1c10002c46244038034001d0b4807000380000b02500780403000384110b60400002c0e240800910100070f0301c40003401060f80c1413602245501071500019040d50200780d0340100c2c190703180c1c44504556010f00801d9440745420780a800300b214100400f402c00c460082682c4d00c61602175102013400c84400724415080b507084400c0303807010320070001c3d11b0020b154a4094607101c3d0010314040c1e601c0721312444ec0300307042c2c8440303095003400c0c0004d10300203942074000f102410741a01c9045c081c0d1102500e04000f401e12030750040c0d540051003802401409501107943c0c8059000e80c00090411944640010b0150f070080c000b0300c2c019406542e10380c42c80f980c03aa5140c00c0100000c0001850414045171074214500a900300b011000200c00c60002c8240d48400c03038850000f1000003484204003090280d8080e003060a044080540f4000c80750382c52900320791084070f6220100b585c541c80b800542c1020080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 75051252 1250 75050002 75050009
    0x1030f0204171c08012d121a06061303110d080a0503010e06090405030315010e03030c06010f050607051902190303030903110c010c150902091305211c0e12070c 70
    0x203052200754108090086410943c5200d4500441b1200b0006507a12841d01c140c030092010b4107016041c400d107450480383d061003803041c0525150b01800844c5d2186804822102d00741c0a406110014a2079a035403010304ca106c10064036072224080352241e0114004c0301c010440e2351350a0f5506a40c81d81031003490841a803001c3d2516000b141d940042000091001013240d420600130201c0c903130b001e9101e0f80121500c50300c00504a070107001c04540f41c07a5101001071081d058403c580a9807160644420500070180152400988180e10048060b4400c01860001c01c480500107005610789190070003205a08101d60380c0101c001907603039080742041c164050602e4464990340030151000d10ba004000074801060b120020b020b44034810070781d5440321601d80c07101d51000d501421084042c6080360091040d001f03400800e0701c0a0040070b5800702c21076502e1460070b80036001a0501782c100700c604c580500128400d90003811405642e88005071b40610104001e403c1400900000e0303a640e1800c0c641352558854591 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 75052502 1250 75051252 75051257
    0x102040b070209090106030c09060e06030f031e040e0f0609130b010504020a18080105011508160c1b080c040b0105030609010905040c0314030d0c0e010e01030f0204171c 74
    0x402400042010011601c09a40440340c0c0241621552941401440c8a50008103c1c0d0250b40000400e05003d801000480d1100841c420440d83d4680074143c4a107030b44250341041d500100003100034000f09609000c6505003600c000c600b886d80f01c0d403407029803c2090310134004c90b030007000400c0400d18203082c40c168040e0b840f00c948800c4002a985860520340306000d403030720868021a40c045140e1180b02d045c001c40410802c1c0b28003455a83c0300310f42c0200401c0c01502d0110004818081165006095460240b84655001c101c0030840100864203885c010360100c55004015001039407041d00d1024070005403024001905441018404100c2141c1c90010000d05014040c8100055a034908826a045441041d00820706a07a0341c901308131800f000d0342005241c010074102c030049000c0000007400694000c65000c1048260381002a5010206d04210900084060190080952103a082011022100b800241c100f603280e04100031132031005404500b02d64131041c0014a42d901d143c18404c1c80300982d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 75053752 1250 75052502 75052507
    0x30911030307030f0f020115090606021207120c1401090c0806161706150708070b010b0403080a1206051203090306010b03191a090c030f090601050f280303050712020102 74
    0x10f50703024160740c401e61000401e009858a040c0e0940b4000c0d0400b403501c0d00501000004035844021140040c0024050040148140e241e41402003860008a43c00703560440240412016440b004440850743e0040840d01d03403692010a40d4100b100740281d11007a031041c4180000703141882c00c3c042c41c1190080c072a003c541548100061001d4120041e05051401c0369030300d0503250f8400b0040f07600c001403616024030b1541d00103100e100b03100a1f00007400d07009200301c040301e5090f40d07560b00011042c007450001030030703484003004030704000da0050401100c6a204110007054050f81c460014820720782030942c030102030300300041200b41e0389001e20138640900a10b1540e503040d130802115240e0140480c417000c5e07a00f9641c80d0011031401d0070b0541400b01c0c1e0303a4010045209442c0007500018160001c8c1c4442004122090104074401c40c00b184140c10786c1c0d4007034882c800f281c3d000e404124041ca0180d820130944071000c540c2001c0b0344543c1c504040614004d031212981c074445850081d0140c410b03034240b01c0c112b9205 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 75055002 1250 75053752 75053767
    0xf0f021903020a1205040f0203070f08011505010f05071103060a090209060306040b010b0708041509080c030d0203030a0b04062310030504080f03071101050412020106060203040b040e07020703050a030309110303 92
    0x130400f070750003c082c0200d002036655600d217008407030032041707001c065414454240c0c0010502c0c2c5006000c801c0c0c807040c20007440341810b0700b40c03002000f0301c1078000d45011850440c546075070948944083c24550740904103130012406014042424120107641030241c094441a90300c0035401c000240a4005405400415041c41d05840d5800382001c180100745030400005000300601003884150380150010342443d42c2a000e45c41d1740540082c240e44a0070845000760386501807945030200d0420755030780e0142c020314510780c0c0c3c014200000b040d845000c04d80c8641c0e00c2d14086601e40e044581d06142e12543c810301c5045d000d80c2820000d02d4212046c001d001c01d400d010030040055099029500383c40d056030061900c0392503403002640d094028a040281c01d41c0792004010500c44008050848603109030005c100d03454448004a88074400c2d030196a4030868100f00400000000b6216240c0c041c10310700c140e03450580c9983c3c4107800c15028107010350010361030b00d21a02c00d0220803150700004c12011001503142101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 75056252 1250 75055002 75055007
    0x50f0d0c03260c01050103021302072312040b03040318030c03020103051312020601180243030809010c0801050907230408060907050901030c0e0402040f0f021903020a 73
    0x100c901004050100310341c0240c40e00c50242001240518001c0140c684440b501e4074500c0c0280b0003417009a1064441c03110780546c6107410b01c202c0d030015404ca4420080311410010b0500345400c022050b440910894440400d8855203801a0000c1c160309002e5035543e04040c20000c1c512240c5890a00140c024a40100001800079500380c040300d84c282008201662814855100005448000351840c231404031203242c0d0710b6000c40c810f416a10134011044244141002400403402104009400032034050b0b01101c110020226800c4003002c1c0034034582c120080e8042c0d01c040b4910300207044021881c0002440140d2100b8000ca0000b111a454103010301d615220000d030400c0d1025104000348184000d4088840140001c0c8c0c1c00301c18150b224407652a5503844a05658480447e0303800020f01451030080750500d4290080d90403640c020074080003c90400400c01f03031322a03010380100c0e800b0360390f509550701c00c50791800350302c0c0000c2d01c1c080010f8441c0107013800c1900842c2504a020101481000991003154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 75057502 1250 75056252 75056273
    0x70b09030a1106190c0506090c030c010e03030d061211010e060a110f03160506010806040b011a091504030203010509010501030305160303020d02070605160f1e0c02040f020301050f0d 80
    0x260414550400e40b800c900200b0780e280303d11500c190801c400d16415044007a0000c4c0d070519900e02c00c10840342982e42e0b01c0001503d03020709011060345a040043d884016620039117842d400038a004090300d15203192070b03c24008807201d130340c8110811035100341d5400c08c0c4400189200400ca500f82050354200012000040f05445154038072402e2050104013502c890700d0402c000c1d0070902e204000c5035034482c103502d200c800e65540e2041c1100c1c0c40c410200007068450b0017042450007943d01009101d1f007039080c039086407401d4541400c030f25450710050012142503503e86290400d80c0e41038490302c070703511415401031500303503403004106001c0786c0e0604004000007503102040f940d84406101c02c1c0c203401d0840c3d103400c60282c0b01c0e0141c0005618004036079502400495807001d800b03600c82e400c0250403010012429102744c0500c240504c080307190130754881c3d103801c5403201c07405507a005c6180030340b00c9c1000e503070009003110061502040050b034040010300040c100184210f03641760701103904c85481c0e412580c1e07519404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 75058752 1250 75057502 75057523
    0x60203030a09240b0a0f050f0402070302030d090305040302010305090d0c030f1202031f0608011203050a0905090a060905010b040b1c20030f0601031a040903111e070b0903 75
    0xa03903545414014001d00c0d4683d03a0f0119501c0d0100485844003801c9000909030707480700b00d441003220780c400007043c40000c0e11010844001400851030181c8a0341008025007080805900358007080003d00d8031964688910072a01e0b100b40c890039100d40c00e50000400300e0b000282507031070303d0380309454103426140c010110f842c055034140b070402d412085400044825060700c1e19000d100c0c03400802486200f0702c00103454401c50029400d1002415500c0c0c40c11582d02100384900074100d01070f4001440441d1244005045650450804c80401940c2e400420f0910208850489140790f481f002440240c01c6c90091600400404c004107041604240d02d211191150045082c0e00301180b07010965221269008081c003a00104030080c981100740046007090380c0308551405041e034885002072082d60091040c1c03080c106c1d04d18024000781d4811402e1000401c4143c0050341130000440c100c02c40c45908200c004202040e440c112144106210007a074541b81c002d40100e0300200c1c0611820307480e42c50008415414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 75060002 1250 75058752 75058771
    0x3010815060a080d0c110303070206030c0d02090603010e0403030c0e10111002070507060807090f0506090d080307050c07050d1a0c13031202060f010305120a020c0d03030c080a020406020303 83
    0x90300c424000884041090f40018128062810003228858001d0584500f80340600d003018481800d2004250301da1280550095120340144045240d000301c82c4007910701150020f1f4010f142c6455036000a040342c00907848141c010001d01c0410041542c0360050440c900144d0a01040d040140400640110299400768003000b101480c50310b901e950402c41040c00c038002d0802150b40d40d2013802c0803503d54465019003408200030300c0126080a01c19a8148103c441c0044520041410072042101940c00081d10a51200312401510301241c90007004500540e00c9459803560740c004440c4031400c0c6181680001d10481c20707000b019001c248500c10202c072414461840c0c4c441680c440c1d0001c4514042d010012070001c081d08000b00c200885c424410000030110b80031103c00b43d0719003007101c210343c00c00d000017044e0b42c104c40705180001a162000c0c02d402c10340c5006480c000c26110000c01c041d0f0100c2c6106800082e11307000e01058954100d10309641003010744005500c0c1c542081d50103581d80c40081d0a07200c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 75061252 1250 75060002 75060043
    0x14070c030c06150e0705040503061b2205030c0d05060604020306180a05010f091a1012240b0a170c0f070606080c03010903121109130603030f0302030108 67
    0x101071064021400055100004100003901074401d031040000c940120801152244041005240a40180d40c11250020000d0803666110207000030304c1d101103204030301110f0701400950000644002c040c1c6022800143c4d400980c0e1900341054a048070703a558140c02000e100813540c0c0416400700f00e03240c0c081d6081c0c80242c0e40b52980c0011903105040d0b440300800341c00c814030038016400300700c0d0440c504a030419200460704545070340080c0c08540c03510350410300c1c01c0511201a521401c1100d1030712070170720450038402c850f5161504050300380e070180c1c021103c80010488041441101c007554000c09480c041e5019030514100d858041c0410345151400a1201d0f26407001400500c0d80f18212102820340810240c5c99500e280b80000160100e4040c00c00140601d50345040282014400c510a0035010b94407151444840c07622000103150841052244100030032440080c2d403105030301d001c0c00e00303648030000901900d58100100342c108108116010140100b00401405030002012580c5114050032101c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 75062502 1250 75061252 75061277
    0x9020909151c06090201080601080705031f0f090b040e03030c030c070c091107050c060f0d021303050f16090b06030a020d091509050c100801062001020f041403011407 73
    0x480c41184610960324200c0405290002c00c043c40d00311800b8540300303032a00040c2d9101c0c2c10040d42c1140c0c04881c0100010000e100088501c2c4001a0501005103054403c0c030302c441c4c443e450414109110b4220220103501d5102036052810188583c21800e20764101942c2541011070144c00540f101a100020a01011881409010079052014010038910900700f05007822103c5c00e084aea0840c0c501580c96019401c0a040103050800c00c4604007440107201a15040700c401002000b5000104030204a0500e005c01000240c1c0420100e5108a0a20300411030705c40d8070005072003000030381e41103035203107074248141807203a6100c04081d2608104032240150b1a03d5407481c00350000c00e16a40701505003005140c040e04a10460b0780400542070154003601c0504442c030007400301c100c65824054000440311401000503620458003401d0200d0443d20780b000400030102c602d400d80c0c20503c0c0d580300c0c0b043d0004003040310a81125200e10001810760091011000c0e10741d0a040180008200c403040c40300303131441704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 75063752 1250 75062502 75062509
    0x3615030a0b03160f412110050c0a050703020f060c0301030b070906021f090c150906030221060604080a03051201050102010b01020a030e04020403080f03041e0f0f0309080607030f060902090915 84
    0x400001e90090700640f02040c0c031101c100300f400c500c00c40050301d0340920f5081e18040f101f28003c8503c2044500c0ca1545441c218003000c4606501440094045000f80180a444c0c1c001c2441040c1c002c0c4080d9885a0b100c1d4150f04141642c1035010303141c8002d20100c46000c12a264000c9010112850100b00c0300f4824003440700f0101c042c02281c0e1004240700c0f400c41005c180156040302c42c128207800f50b540d9551081d103910050b001c03407098402d818100304100145281c0c81000c0040a940a000680341c0c5042075640c0349118a400043d4204401007400454103000c49a021881c140c01410248001c0c081c3c1c2c000040085d44900d103d0f000a01041100d000c00c0007161513076011280255400070303455a60b12120301d041c1e9903c0c0c10940c0c0c1280c081d08040ea030030305400b581390f66092805400007045440c1d81c1555907640d1080028003000ca0500000c10130003c0e40c2e007001c1c803141d1701c45e40c0b81e41c50201b00c0b03c481009a40c01c46102d604044101481030040d074000351115150164041680e4960030980307030751803000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 75065002 1250 75063752 75063869
    0x12110d030519030603110a0e060f06070503030a061d0610032004080601030210081006051e03012d06090504110f3615030a0b03160f 58
    0x1c018500d00c2e5140030030542c0740c0c075a20480c11603015215a1145040070b10400c80c04d03a0b102e01c1140d2018034080003059061801390001c45003031030000c01d45480c3c2810303680d4003401e50304221028048565104800c00095201803190055592094464200b0780f514074006040300e04000051000c2540d11841201a2221880059145495040304645035981c943d030303459a40800b404201d00405940e0b0500042c00d000d009060701405070310140e80082402c02004036400d40160408441c0360084d0541054180040b0300150f0180c4a01248401110440c5c210760806000d05416400301c410042401c128440d03000321048142c420032034012880a5400d4203ca0a600032504101003c40c00042c00101d60311000740800001c000106860044185072900c0b1006c1001c10b009190304102500d481c80454400e1000441d401404a000040c1e0b4180c8074001c2481d1a54550134102d50002405091012000d04044a40105190302e451019505040c00c000c000103145041044005500e10b007011000c100c0241 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 75066252 1250 75065002 75065017
    0xc07030e0103061e08150601020309010f0c020d11040b031b0d08090901140310020f030601050a050705060403080105011701080c0d050f011e0b030307020109050f040b0301060909030912110d0305 85
    0x100c80800000441c3c10b4091100d9485040175500c070300c03a034a5103e00122040d4600c5010141c019505080385040150395105c2503440341c0007000000108100140c1d1814002d4407414001c0c2001184d00540000344401c9900d480607a600c654000c03070403541d0070395600380301900c85002076076018000400e501c7c0a803403600401d443c940c1e100345408000300b40110303200b10118108408500312001100d03c07100040072417289a100246282d420000100a540144018070100f80b4500d801d92078034103e0303140d05040c60000c4d20120700150641c40100820740e072200b0801814039030041c0f0a4015450285402c2d40d502e85400b401d030040081001201c00d000b030501ca0307800c41d8030b219402401040001c4800400d0b01540da814002101d1a240100420303003000010384920b2a41030712241c00c2356007007104001120203c092000c0e44103442d00082140c2ea1000c0c0541d10003808100c2c03001c909429076141c05011280c0700d411415120501e0b1100001142c1c0038982e1040181c4141c58040034030902c4d0600310350b944513016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 75067502 1250 75066252 75066269
    0x1110105090303040507051c0816080c06040209010504060b040311010e0d0c0e07091508040224070213020702010203030403050307180b030711060115030b0402160c090609050c07030e010306 83
    0x103040041102000c40154460392042081c4e5101c6900c41c42080700c60300610b0030160780c19841c40500c2c000034407500000c048010341e0b80c107000000c81003a078500005500c840c10121082d00144d06000850600000d000e014050488060280c1c038100000700b20940610310010300721404005d07003902240d0246920415444020b0700150390171809041c1016250740070722800242c603201d100000e5409225910410940382e0240d6961006045160111280c04c40504141c0c0d0101300c00d4207440c5081c07200c0403070070705c5070841b0344101c1c1e1100220b0040180703441c5803d1020f43c20a00402c00900180c5c4c4c040212507100d075060402c0f9407280c40d0366800b101c081c405c112110321030801881010802d8004034010758421542c0d507a0b51408411003418075601c6e10802e02c40d40300c002080403003810015009410040031744c84042c3c40141040949449134102c003000c1c00056410b01d240410601031284c407801410003800d00e4a00a104031700380540f46c0070043c0300311000641004440c0d034488005278402c4e00030100501015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 75068752 1250 75067502 75067511
    0x41a010e0409060219090501030c0806091015020106061214190207170c06090f1209180106030501080d030c081801091205030702070515040909031202030405010c09050303090a03060b011101 83
    0xd494050940300060f134500420800d51001038036622a001c5d114050030303555140070280e143d41302404de100201800c00b40f030203410136102180c00c02e958443e500304030207158001f00740c42d881c00710050185482c0309010640e207800d0510078000440000b507100d400041c0c202d21840c40c0386d40140d900009000c0c02c00e004090f42c2c0820441014200d6503000781a145d02c04000f500d0680d03d8903190695101101003145100d074102c95080700468103000040c000700c90307001d410301031403908114030404031220036000031020903980d40040c021000700b00300703086400c101c60034100144180c0b410702604041e80246810124180344103a070005150a40101c0d001c0d540c480c0e0b00c0c200e102281400a06190022205540184144007000443d4a05601404018102680e0b628034181c01c1200d281c000e0b00d0040019014040c0b110300c0c50b45110300c5c62004500c9030f0300a83c000111003000d0400207088801c9031707200038420b601c1884545805d945a0b40702e40d080301e40c0050009550300c11200181c420944401580c1025482c1c0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 75070002 1250 75068752 75068767
    0x50307060204150507020306010603050c0d09050d0807050f0301180f0e150a02040315020f090907020a030215090d0c060e01140a050108060103080703180302062106041a010e04090602 80
    0x1290003a000340d4000086002081883d2201200c1da8001c1c160040d50650000c0010007102e80650b1010750400f0000458078a080342426100081e100a01402caa41d580103840804050350b220400981205451900a01e800d0038980207114070b010600901e884440910724501c0c0e003a0b010f07480f14100c071320454011302110b80d0314441e00c1c0d11a0010003181c10000400000500da002c0c1500c2182d081c1c903403040c1190b801c4c8000b080004025008a041140d100348100703d0001c6d19500d33100101e00c18681c9900411112080b490000d04102c004280102c40b10070800030700c400350754085029003031070318903240072542c45405040403030190005000c0382d082e651805c165500c9602d1980d419610820003088180041c0e42e85071070b45503448100340b0016001d00010300c40400002d209603a0301101d4424030361000e021684075000103603280c0c8814034401c414408074130403500d603c8200d4030007680301d0f50440d001c2090000280d448001610703003130b402c0341c100301c0d8004144030a59115440b81d0549030308541c0464880d102c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 75071252 1250 75070002 75070013
    0x2070f0308090103050106090609030602180d12022a0906030718090c0e01260708060c030702061003030203040603090501021603020c120c0a0b09010302070b161d060f090a03050307 79
    0x1040c20030b00d00090405001207605802401400d084134443e55a00400c9450368072114020b4110340100790440307a400e00c4014250b034646407604a1a0b0155000c1e5211310020380f00030745085114120500241e003a0100701e50b0f43c0c1c0c403026115a8950080e00c5828041d510080028107082498015032440d0f0030882c280e0140201c203502407400140308410002c1003980301c0000100544d42442003a040c0703d922041301d103c0d0b0b03086050000380d50f11700d10101c076002c035194114103041c09000c4034240c5c0916404000c0190041d4100417040c0c02101040300300b0502811910003d45030b1145c0c0c0142c00600d40c41c2d006c0300d4200070007503048035445076014000240e00041403400035100d0341c0c800c0905114644146440c040d81e40c000c00c5908504100500d0480440d2400018280c580c00a01540703050650920400000c211400003492047c00c291056500e40d00090a02a142180311550500703d101240c41d6801692540740459585907000304040b510360030710704002101e2501c19080100103000101c3c00e0000c202 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 75072502 1250 75071252 75071257
    0x12010b010e03030403120e031c030213140d03081305060f06100810030210030209060d090c0807080a06050907050604080105011401050a050909040c0b181c08070b060102070f0308 78
    0xa009030703a1080ca81440303908240d52809140009005480250380f040b08550042139000e0260038041c0540701c030280b010009802d000e5071646000b0110303070001070b000d805c003180407008800742041031a81642000c1341e1011a120f102020070080034800350348045032081102401588480e50302c0422103856281450707000340307100c40582d0750320301980140e0400c0b440540103105a610546102c0e00c0c01d00307024030710340802c1900c481c05100070381415806c01016030390761940002070452044956001c00c400800f40b811007030801c0300340d0100e07035550051542400305003c0841c22500040d003010001c0386a4644071400d074103180c00c682c0000c1c0d00200c00140081d4202064000b6412604039025450911410302c0065502d48280c2c410072001440070412500303240f43c000c4c1c101c0d4015005648030b080007611800e2210310355206100d09207070f11404041d0300100e4a0800122141804a00343c98079007070019650b031201d24001c0440040c50f903032021000503146c0c1d108000001c010074129070b0300320303020f0342d2418510400d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 75073752 1250 75072502 75072521
    0xa0e0a0f0209060a1d0604020d020a081603111c1419060614031611010507030f0e15010b03220b04051509300c07050102100509030703030b040b1201 65
    0x82e0034141c005411072a042450400b120a80b42c01c00011401103078a0a030100001030030190b20503424001c03e450090320b8400381100a51030b48607007026040000308018803603c2c0745401000c15092901ea070a00480c908260b410a0181150303486200340702da80031030702828180c0c0c046081c1262000402c6194510040c00880100020342c080143c42d40301d00080380c41c0c60302058000c201e02d40420200764211350400d025001c19000b03140105003407003050200d0b820340d081a1801400241ca0701014144c10301d1611134a100120014014594605081c25882620300e051080742110540440003420314802c2038603c0444480540d0720050755501031400c5410340b00d0540c1d0035200c520400480520501c640d120550060314404010000044442801c0403401240649000c2441c050030516503194013001c01707040707042e120720054400d01e41004002440c141c40404031076411420002441480400031046403400d68040c074006c42d060005130049409000b14030302c4140c000c40502401403070948107610000c2d08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75075002 1250 75073752 75073759
    0x1b01020a0503060910080c10020c030604030e03070f05101b080307050318060402150c19080307110a1106131206090b16020303010e04022202040e01090c050a03050a0e0a0f02 76
    0xb1a11452401c041405050040840e946e02c501051f542914000a030649030045610417562001d5440700460300f003e0042c0e40c00c4020403240c500124071850140300d00c1014060414a40340703080e20b00800500450400074096040c0903800360030742d040c0c407c0022041141c5400a46007039480c14048001070195004403a11300b103041104d101890b0100c0d0200b01030303005540090449040034040501404168015494000c040c441c03e030f46290340200140c0da10b4001402129603903224a40014050b04c0d6004003c03510903d43c100100c1c800c0090890817108900341c4040d00c180351162003403465125030807403d03046000c8650b10482c03440100680384d00b2840040d44924980304094440a41013001c0c04c0f203801c020000b5800520040c00001640c40300c1035030081c0014059010341c021038110030340d600900b882000400e03070006414400c100c0711041007801400c252500b00720305075a8490051542c05000248810151a08040b456405a9810503c44212020181c48403440d45162040d40361032241d808900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 75076252 1250 75075002 75075019
    0x102310909050c01080907080a05060f090109050706030c030f0608030c01060605091c02030309100801090b0105030f01030305090a08011104050103060e06060703110312010f170604171b01020a050306 87
    0x18480d88501420441c250310a008001c4082c1080065074002402003503c00244135850002415240402c102c0103010f01500142080c1d04004021259a100041c0b1800440c0c1c100743c8c1c29800903400296840c01c03a056481c0c001580160804100c0c0179140520800404a0900384c0218030001e0110041201046107402001040c0d40c914050350304d809402c18041c0e1180a1116681060f402c541c0d03010a407600c01400d5a21b04103000001421016004d40b0690005103d0001400817102c42e10500d040010242400ba0841c0340075141603d1852050200070200080880d0f101c0b1151100c0c0070040203130845c50001d1142600a600350655034110340b0420340001c0c1440340000f50000c018044502403040a845a444c0c82a2501c00b65610710304081000b03810320041004540d500c1c046000c4601030003588040300b0b03403140b80041600c1c0d41d9602c50b0082410b608080d050000140040e004101520321845165884426190b0a581e19408214840f5443c0d400000c1d0040d045030b20070004c500c1074800711207588 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 75077502 1250 75076252 75076259
    0x504121101060e15040e0d1e080f070e010e0901090203190b06040510020304030803010b04090c020313060e0f130507030513150504020a0302130606020d2a05010231 72
    0x14281d480b24800c1c140840641004078140500d10842641c000d44060b101081c50440ca0076100e00d89120400d40710001040b02d0840d8810348a40707006600310b8803003442c1000c86402d08014104001310041e010105100398420061140d034000c07290f034403011100401c141307051341e5124440400f9510842c1c03102c8546108802c0d0040d002c10340d204000c0b49040c05083e503801c02c0d080c43c040c0804000443c244109500c0280000000508900011400b80030720640741500c9078501030700303281612490501181990001e100c400109052920101c0c00c840c018503003200003920000c0400c0c8074120b00c0d482c0640012411012201e03085894010030300440c860364040065540398207400506454482004104985070410300c00799030125007110350014001010002c1880c0d5941c0007540741d03410091843ca0854641100700507541d0140072050341c44040340ac00480503022a18100260002e07005c2c01c01d00101801c0701d820900c542503042d50181c5941d89600310003600013400700c2011400c007071440b0700b050342400c0007c0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 75078752 1250 75077502 75077537
    0x20f1008040c05120303180c030709021c0203010b180103020c010e0c0a0806091002030606091c0501050a02030610050d021605071a040e0705220b0a030b030109030906050c010f050412 80
    0x3008038a20f22001780d03066403250500200c0c0f009103a0f8529000348960910000c003590240401002010103c000503980c00080006680d01d026070204922074030304c184010030015440f881141d068401150110f00d001c00c8041c01038000303010320040c3d000307550310f0269044240b03c2d000030095002d01e402c41d110101031f0f03601e5000c0ca6540f04102c40400290300140c1c0c0c100601d001c5a0059034204000421071070410000c2004a08541001d04414104811246141051010030700c94250861401003055140d80707044000300760b03604107950074441003110010355800f10014950640c1e00310048a64001440e22032810071550b034444501640c0307082c04080d1028003030340b0311560481e4115403a1103005901690313051000d0311150042d0500d410b01440c1386d0cc0362a2041044024103014050740c0d000c0c1510f80040c0c1c2001812070b8060310400d0b02903850600c002020940019100048961500e4655510759205031a2800740c40e2244829080906203000d12003009030412441c50100b40d183e540300c203100c0580012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 75080002 1250 75078752 75078769
    0x903060c0c1109070e01050304030309050a0c0e060f010f0e0604030605010308070c08011e0903020f101e02040302030c0d03050c160e0601020114041b0305070f050102010b0102060106020d0c020f1008040c05 90
    0x41c01300e405d403044803140e035000e40c1c055948180681400640108951503160030030050030b004545400503aa0f086c0601c071440080140c0040302500c1c02c0c4007843c0300400180403903001c07001417814044001c0008980d503581d035003194061640818140655603403494a81c0d91500320311806c5514a5190602141c40f4105202e0007035101c12205d5180d841e480b0385407458000700021107059046000c0d10191030000d500400c1140c8000130780070400510304902d00079865407030440701d14403041a4010001003000d0390300040c540d44401d008450340a409a100d145c1911715103c4c8440c011a280078111a41090034006107070001110b80c0007014042580d15180120300329015141d041950041c1d04003c10301041c010840c100345e0344490641d920708a40c0707a88940d468482035034441c1d401c0035041c1c1c0050009527828040c201c528a0207000810391941000400f0b034560404000000801c40c110010784150b540b41e44840742c140a01801128500e4840321005061900c2220b0582e855070031210001070f5400d06420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 75081252 1250 75080002 75080011
    0xc030a08040e060d061401030201110312180f0a060203042310090201030e0118050d080f0703050901060902040806101a07080c010605121014060a050609010903060c0c1109 75
    0x5068545400d1400c049200304001c0c0c15160004c151000200c001410f52140074190707070512041d03956070340c5107100040805030132000202540d0000c3c40528000201d54040710740003103004108240746007441c49180d1400100c0c0002420300d100c0c0b100f403841403292640c02180a140202d0000d41c4840d1190714542d002c1c8030382d20084035070b940413118111828602e6072050303488030b1051401040d44030340f500413282541c44404020118683e50b100b60303030400c24200302d045c8410f41c003800c2454151506e41c610040c007200040c901803e150702c59001910170342c000e50041e030207480d50031411916079032150306290755144102c42c0c22040c1e9001c540b011803402d009443d4107038008410f8442c146440c41c00d5441141640000c40c02080079922200041380c81d80d6403100281303910010400418220b030042c008901503850500c0b03a04a0710903400c0070310aa50700c1d01010726043e44d0741a01d0b00e540d50121440101c0d0b840403a5400a02024a88942294001c1e0300090000d10b00340100c4100c0c0d50140c040c020084280400e5a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 75082502 1250 75081252 75081263
    0x2060609010b0406050717180a0504050603150c070213020a03050a060513110f041403190b01050121050903030601110613060504050a05010e1f140c03091906060303020c030a 76
    0x1049000e20a030000c08a95100d9a541c404c02102031807c01c4c41c1e1f81010ba01c1d0307924840914401c1034507061440b4414000c2504031414016424424003207030b1174003503500000842103131250001e40d40ca8211001c85030840c0d40641104131910301c0504c0c400c004d420004001c400642010040354000c42c5c82d024903820303201e009020250000078511039000a102c43e150301a07140750188032103100425020060001040002c40f60313030710860340004250030040f410311402480c1c0100c1042001185020500038150380c42800e00000c0030204030504074540c1c03024600404003038100000c110b029072000c005140514800e0721407000310100303848402c0c0c9606084481850102c130f580d0000c00800d50f1790f0000b540141c0a0004c1e6400d000c2980c072001d0a42e030202c41258903590080e622100c07400c48003068150421101c40d02040908140400c0303030302c803640184c80c0111002000c008542d03004000e1242e504205842c02c04e42c10100e005141c071f01d02400030740c8415000750044848020340c4e8203012078615040c1f0b6004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 75083752 1250 75082502 75082507
    0xa020108010b130503010e03090a061d090711030a1107090903140f0f070b0714070807020d030207080718110c0d0309061404030309050c01110d0305090c09070f02060609010b 76
    0x2d103503420315002040c4211100c0300303407840000c16407420311413400005220000307180d990718100140042241e861348000d007007110b25141035004040c440036102d029442100e40401e1a00c034032108444803440583d45910364040043ca60a603d90442c0d105030b07091902c502519006c80da9428004101c5071007590203400301d070250000c4900300d50220014000c90150f107a803107041c0071800195415a4014403811142041080d0034804c017282c0200c00340454105448000d8a0036205a0b18503106005008000b405814140241d2040600a102200c05801e82500300c8441d5903844030b00b40c480c0c1030a02d680700069842c10301c2403180c540e143d0007242c41890070035005006039200000114000c2104040c186c0303800d0fa45112010f100d520b908010b41c060381c0aaa808190214a41020360500c9200d1902c5030510515114240040e100403d500c00c103150785040006165480100140c2081f81060381560b205644404014009402210a5400800c2030b82110b0032030340c44c0f00a01907040d07003c1c0190007554409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 75085002 1250 75083752 75083759
    0x1e050c04091104080d1d03010209100305130209151e0907050a0201021e0a12090c06050c070b0301030501140a09030504030213021329070b0103020907091208030f090a02010801 77
    0x41e8010403202c07441c01c51810f140940c1c2d408060708081064200e80c001481c03003030b942c104903001c05416901034403045008518025003900042e07078003102e40e00760034107141d2178000054002c0107404443c0416900608204141d2604400c141c00e06429041c10500c91049480c0760110045042c0740e81e04a0340d40078117603440c3e54503120340a85880e00500d07a40d03c11076400300300074a8250100210481c03540e03007000440f9140c0d4010f4002501610090ba901d00e120741c6802c13010004100c40b1035440701118a42d051887c1e454040e0300c5200d08014058022150b4103000000000401005501c604801041000c1841681c0c40f40546041903482462014000a801384401d00251074107185e4510700b18941800180781614117031140390030311010790021301054551841c499a00000480001840e40f0811070301d460000b240d60ac40c403032240c040c0006401907000000140080b40603000c90805403404d440c240000841515240305254011a030524802070325101064010b900020071203031042e030507111340c00d0580c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 75086252 1250 75085002 75085019
    0x30f0606031807030303140f0709170106030b040b01030b01080d120507090306090b040c0b040b070f020102010204050303031003020307050607030c02010c1b0303021501050d150509100f1e050c04 85
    0x8060804240401144000031080b2801c0142c1402507100e0b48021402c40491005002d1107030008107a20600700801c001c00200e9540003101c003003039528600100b4407940c1d40221113401001590402080038074454103000c14020700d100c02c0c50490303200d03080045050380c031440c1180d00d035211252502d02107469000b20038060300c4290010303580711140d440d1448009070760392551000d031440b0f22401e0b113a0382990b0b4280810710036040031500280210b0204540380c04c2c0b511021640600c614600540620345484881c03045a101b0b404840c005c2600134212620303401c0c0031984014110043c4000c0f4460f2044a000250303600b0124160364425802d500d41c0c40400309070b42c0041d030b800c8491100c211003001449080303072541d18101c000480518020f5008000d0082110f510f20451003068011a00c81c441110144000940214201030307249039182000c545506e5211031039150007805a14290958100b40002c42c41100c5c9074007219810980900451502c2c41480c01c05040b070781d0030f803215901208100302c02d00c138001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 75087502 1250 75086252 75086257
    0x90a0b18040504030507030f0e0a0315060306050702030a02010b090c2a030f090a050409050a02130212150913170901090806130506100e010303120216030302041505030f0606 76
    0x1008400110981121040001d04440d0200c900700d012450110340303d01803540c4202c8911041c240c904000103030320340e004002014110302d40310042a005040c000d00c6021003454101c0c0300110707030005003400f190601400c00b94032034026071150401136113003103445c66440c0390810f401401691a8000c0900e0410380c001005124a290044801c03140e038001e1004c0040d5404100605107600000619603c8044c1002000302081c1c0c560301c224400d074100514040030810111f441304000742d0454040c0c0424620a2540380680100801104042a401c0400803c080c441d4071400d0503c1040b60040c081c0d83c0c6060031407011440019010709400c1d20709070b207540c4509511000388818101410180007140e614118540f07071a100f110001d101c00118251042080002c000d00354028001d9041510214100102c0d03004c0000c0502c40602000802000b5407808031899041b10440305080b44039406c1c5602504019001c0d40c018803a008500304d1b070442401440e071048040d20700071a20301c2c8128449880d11800c004064 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 75088752 1250 75087502 75087517
    0x1150507022101020306010e0a0b0306090603071205031b060f040314040302040f06030203010b15191e09060e030c0307050409030203042714040b060d050c06040305061b090a0b 77
    0x903080d4005503800c03084002e100310040302d00009a502e18025000404c01c1045010b5503002d00d29a5005000506101c010b980e882902981c5200d0715980d80c400083c0342181541c0159416002c448105050182c044002c0c400c218107001c82000382c50900e01119a685070882e00d04a0f00d0014101040010f4440c4a612401704104c04009042c0758894001504864030411203803032071a80c0320070820031800d084c040c0d0034105004903418ac0c408000c000400141d403107001d00380c00e251900496800105405441c4100312000407080e110b084c41600d88002e40150202d025210100d02c031a001c7c80c0251800140c0c103030000d000600034042540c03a03c010301c0003410118200324294001440049841a40155020320182c40d00e80026004490304010b241101c21414800e88d0031020f2200304008030f8200c140c2107030480400d407840c1d5000e007041d00b800ca08000600c0d2000d03521840009000050010000b0320342e0184210100c2100c0b03004051070626050710648400540003a510f500c104a0140050b02a0244 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 75090002 1250 75088752 75088759
    0x2709130503040b1204060c0507020303040b030a02071509030806030705130f14161706010c0209090a0b0a0b010207050a0602070e09101119110601090903020f0303090619050115050702 80
    0x2c00c0d4031051041101e8101a10321300c0c903a05004104002c3c41500c0c043d03c65626180c3c20000e10303110301c58010a85a10981c01441d0400300004041540748803942e045955054006034070300c40180d0034074803040242c10003950580016001e030b00803619074500410001c0403520020141502c3d24001404100a4004800c0d43c100e120b58034070aa68407004106803092240b040038046181c020000703032000c1c00c680306400c8081b0145c1030b40020890b40380d800030b1544081c2d503011500f48100740c0c1c0f2052118540000100e00800c008015001c1c1701d0704103407540020320341040903000d68840c2034850052080c0316034140700c1c0c100160300000040000306610b1010b42e030400e4540d001e0b03030081200a008902a2842c4242c0c00340c2d0140c00042c1c00c240c0701d24800000000342c18520740040d11a0b608070420750b4440040c058051807a41d103156003c1018001c0011100802500341901c2e1030b458841145902c52200302c9102000803924840038003161110304c100d03410780c1c403142c0000d2981941800d048070590004001242c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 75091252 1250 75090002 75090007
    0xc050102070c0609060f0201060e0c18031b031915181b06030605040209150f040e040c0306180b04110f0303030405071a0c0a12030b152709130503 64
    0x410b1030300c0a00c0018060b16202c004d445031030080020078000e20001c060086902d40301d4140241d01001020700d0f00a46102070042c0c031080c48059540c20200149032450303042c4140340401899034402e4050b581140340482c180d840205820741c6001d01c0f415840c80040c40800e580c44404400d800d00e42c4407540c2c0148111250800100540c0c031002d842c2030392a18a501003c107010100481c40d41800340d640540025a000d6003002c0c103000215902c0c50802a0324094440d000c070310060307084555030030b4a0007003500c410303142c8080c20a0f08100c000c0385950702003554090304102a000000c90343c401c008a903d40d00c2031a0300305d955180d445642600f048145855405502102c150fa2680d50420180d4060307805540a0b0120901c1c00c8100e10b03c4050450042022000620245644001c0407828212864204200c10807201707000208500070b22000d50407640c03055446071f00c1361404074504050031100c0d850350042d075909802c404041c408003654241d010342c858082d0002446286500e1740d01d0461300c1c4101c0441b070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 75092502 1250 75091252 75091267
    0x3020f040f111809011d0402010c060e0102070c030b0a0c1205090a0209070f030e070501021209030c060412050106050a03080901030b010201092001090f0602060105060319021303061d0304060c050102 87
    0x2043c0e40007030f2001e411020700b01554015860501c20042c01050794840d0b5800d211407001600009080c0140040e042c400c02980d11010301c440c0f60007040c801d0901c4402159918000d180c00b000300007841c002603c1f242d000d1800a010110b640c1315154000055481d048400d1820300040b1004e86402000007e85000f03001540c00162a84000340d4047e0007281c8030b01c580c10b900e101c0010100c5180c081d4402c160f520078201001141d8020980c031a0700c03400c05c45103540c0c41c03400ca0302081c506843e0b404115088240064000382c040e00400c2d00040440c8540020310010390350f14104201080107000c0544601c000300103075052980250b103c0340d92180180004160000c4641310505a803885540b954000b80542c141081150391091981001d082e40e8100c600c0041e00304000203580318014021180552400800708951002500c2951031200f4a06e105550303400c204281c540e540c402c1440100c0d007045c01e0010b0040d04000444002d551550144011400d140c0b422000f101d006441560a547d80d550801004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 75093752 1250 75092502 75092531
    0xc0c070503011e0b01030902060316090503030d05070206090f07050103051306050103060605040b1c1403070c0f09050705072a03020604030c0303110a0c06051b0f06060a060903020f040f 81
    0x2180103141512841400c110b100b0f1804242c0d401c1540e8141058900f1810500607a20041501e030400f01c1c42a962000c40c4a85006441480c0c0d00c0d04500e5040c8804984504402d040750020b074030940141e429548143c8a0008003595140d0110310350741180c00909041c855944280e02035940500c58038012100207180d62115411100282c10658546440f09018070150a01f4000c031402c12809403000c241500748411201c0540028440040c40025010001c108481081007511041904080c0c1d01141d16070303e82080301000c1061240e804007509020008401d43e0080040c0c1d00c605400460058803d2003107250040c6c003d07040d004007841201c1721a0044056201c00d80684055840741d50340808440c103605019201c0381014021071081e50004823640001005020780c0d001311001e070300382140c07204040f04007946000000d405a214900c50b000b450741c08040e001540500aa009681a428041e100d10f400c4800548030301002c1c0d040f0328203a0300c025590500da40202c0030345082c0b04c000036051a152085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 75095002 1250 75093752 75093761
    0xf080405060d0605040b0a120f0602040b120604140105060a08100b070302030d0501090203090a060b0402091224090c06071505010602030301170102120c09010c0c080d03060801140c0c07050301 84
    0x60302d403065a0322014400350500348601410518204c540450480c5803504030544580503010082c12861581d14003004c0040b142c05440140c03002c002c0d0036842e00300c085615802c28500302d82c554400d50400714011840d40c06904460f060f035101401c0c16242500940042d030f01c44201500e1604040850310b800074140d11b8003009040410300c04e6028544e900e071504560000e82d9010b8206070389141c07040050060750300001030000c49a503800074002c00d01186c0c030303400600240a00c06007030b608644082c0141c001c40c130001c44c104580307282040301e420714910f850140303540b140030480e049034150388514080132003440d00c64041d00307040e40300741c1184491900444545042d2182170740010050383c0b010006205040c03c1d000c0e100d119490704402142404d0342d000c814045204050550304440b00e0000300309000303900c640e080c03a0b20581c22914001883c2e540d10241650380c0b102010180000e0714258006c507114006029012400c1c1241c0441441502c503001d9180e44c643c8507042000451141910004031520207004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 75096252 1250 75095002 75095017
    0xf06040909050105010b1908220606030614040305090103150801090302011515020304050405040219060f020f0c090601081e0a020904240306020f040807030803040c0e010b04030f08040506 82
    0x2804100c944030703458001d09440041c1c0150f0140002840902ca40b00d0015020f500e6034142440c03c00f10300c2e15100369420032040380443d000b510302c0350414480c0034010307181c0046045038420201000040d012415050200c1c03400d480040c00100e040202100c0b540c42a08203444107001900040c5105580b1a1003a00b141c14000301200980d4640c8000314202d15043c460200400d501c1d0030498440010840094a030710890051500c0b641e03641e40490155141c411500b182608407000e100070325a105c1001900c5000603c0304107005202c0c0c00c0f031031401d02501003004800928080e05049982d11044010345403100d005098810303085106109241040e0074101e400d000302d00121005a840e0700706024081564000c0034207540c00c14030311903405045602049130b942103e401103001a01c60441c601d25425030b02c283c1e0f00c01c08182c0315045010080c003000000540c0030303d01c55020a080d07a952240c181699108c03d2080500036902440100b02007680c000901d00e41d24482c1d91000e242548820011349140c01425 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 75097502 1250 75096252 75096269
    0xc010f0b0f060309070b0f0d1e05060103090203030d05070c02090a091a010b0d0e1c17100e1504090209070816030b0607110607020a060804110d17090f0604 68
    0x411409428480c1c000c04504006940040c6035152940d840c650303414a9102c3c0301048480003d00b25140701200042d5483c12501090920080782c020440d0010048201e00d034010713061911001c0340066000c0c0c17281d0000e841e03016000c1c1d81080524404440107120003409001840b0140c041c070720060380e07016809072081c03114001c0060080030a043c0241043c010368448088040d68000502c603400580c01a00e40c00c0546517000300d80b0303000c118a083d0404807a000c207140280c2c024461411000d400119001482c106211200b445581d100b15030501220688607014250039100c0c00f248004120303038840031402c0009000407510300060b81c045809554205d0b640c4000440800c01e0004110403807010002c8050180340074403102e040c00c2c1c005400c038404c03210010510490030511140300d40301e46e420344001640040c40c41501c299660381c09429030204403002c5031000220b9450102600d40840c02a807040c3e0884803000400c4c0e40c042c0c02d070040da401a82607a5001403004003554103542c0c1d42c0001c0c00500b5190 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 75098752 1250 75097502 75097511
    0xc0114210c072924040501090b1f0c080a050c0307110405091615030f05010801050612060f0609060402090a03061506090b0307030207031205070f0f051c110c010f 71
    0xa092403a6405080c60765007440f0f5404142e40c114040103000c085804c40d18009012054038511080c1e03000c540042d0192a4200e42840000a40050154044071080c082a200184041ca22099950307109116070f4644011075460103040002c40d0242c009005940e00038101585400801d1980c28a10f0308241d178202c500c20001040030741541441d000c1c0c42d82000081c002010340103a10782d4546099050b030f0144520400c403501d02c1a6040d40b094000442071a10054100040d50310303120901d0290500300c2d100350081c02c0d1014039031058500000c60a2040c50f013403045003055154a8100a110803018001f6648140c090060003001c0d564829003100440c1300b8400050f458070800740d440c1042d54150311000c10701481040421040bd6400d044030744c40011803500503611005841c06445480288480700100761602041240c5070750801020000ea031841c3c1c951400041030035074115200d110b030009034881c000034030841d02031855094100c2201e00c2e4003400c0841c11b00b02115101405c580300ca007000b02547d6120b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 75100002 1250 75098752 75098767
    0xc0102070b06210d03020309010b060301030c03170a0f0c020d020301021303030e0a0b0304020415030519020a150c02150409090308061003061d1b0703050c0706020c0114210c 76
    0x340403110565441c114000c1d03880f800f10b03450b44130581c000402c010305400000150600c0429072181e0080140109090384a507102d04181c0c4071205240800c0303941120342904c907800b03034620f4002e41d045120f0a039144058410381c100f048074403a40e004401c0340c1040c0904103200050b038007800600081c5000c6110700480a1440c20b000f400c070504c0d8a0b0180c01091900000d021803980035048a0b441a010b850220b00c15008191001c0220040c0d44082c103a80a107070150178050780035065140170640200c039030696258039182d202c000740c50200040e002040003030541d213006041007244819070344907094030541810340e9039101200f46d070304034403080b4001144d43d02084820b15200000e810f004986290400007641041c580e1020925070b8141c0c141c18255200000308808490201325145580e41500951240f0581c500507003075421104801c5070500981002003107192000640300e20300c00c0140e40d404c074502000c0369010b04030380c0a00710204c2c488502204040340f12241140790b502403420003454a81e146603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 75101252 1250 75100002 75100009
    0x12020318060f1204021903081902010b0f010f020a150903020708010501050f0d050304150512070e030c04151a070312020f03011a1209011506020309060f0f0c0102070b06 74
    0x54012a84610018080c00110b6541282074031404010006071400c2c0d92103900008450811640c13416444240b506000b004010082019201400c0c106c2034903415120308040580c02c0e200d23109941c80e0401c481c0e9020039243e62041201480c11038060054481042c005d46400401c005641442e4490540381c015000400da410003020009100d540000c2001c0d5040c000058060101042e11900c1040281e01c4002400340901c11140200240c4101c400d01c1c1c00455406042030304540091080f011103480010107440c095140900340c0c00d030040140c08401551002c20008104265941c1c0400041c00f0011483c110444c0301400240c8020034003603101c0d542840d00030115251041c00503041401444000c0c00084140156410b68691800d48100d560180320940708500828241441701c25010301800940710040d40071790030b02d203285210034210342c0d15800c0603039503841074182c1c694004504000c0503190283c000b004d003a001c2c0d1500d14803450000051222401d903008090152036050032081400f11618 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 75102502 1250 75101252 75101287
    0x23070906020c0a0f060e0307090e0a020109090504020a06080705160b0a050705040e01050d02010c050615040501090905031c09140f0d030915050601120609020c0c011713050703120203 80
    0x9003c40e2a43c8038941400c4100900d080f40384200740511641e008400501c0d40d00344028001782140c14000c0140c0115840e0301030751081e0082c4264007098002001060320002d9008840c0f1a40e00540008480c5203030200455400d100200401c1c2001000d210b075152120308080c6010000d4003d0300941d000c2e040001c81901200c3d0b020b00310b40140030b01040104500c0c00f618035000d044600848104412004a0005903159201410010f000b409240c0c01c00c04403000b11280058400c406860810850381c0741c0415130112169548050240ea006210070403002100c00083e50760004644004222401160ba8200c2c10942c420203414030380d00018118092081e080111030503504030b92a05100c40c01048e1600e50005054036004120039442d03500003080744c0d004000c06c0f16940760140003000a1603171520b00304001d4102e9980e52045014088035120603600c191017560380424411400704603a10380801580e00c008400b034007150b070380c05644400008940d5031180004040d000360007460780c44021070100400003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 75103752 1250 75102502 75102523
    0x90e0f060609120f06130506010b0a0507150e010b010219080315030a0305190c030807032406090602060c040620010f0213050102010510061d220c1202070b0403032307090602 76
    0x481800c15a01d01081c0005003250441303038aca050281c0e4a00f40d042c41181e013841030101c003a010202c445450041880540d0061006c55050002080412041401240c8030944640f055005005d4400700d03402003907850008540107038a140003803c0350803050020034108800d2003019008120045095982400e9034540401400d44034a000d03180032001d56005807260401600d0841050343e1015508100010f5003885283c0344441001d0003500d40d92080001d00482e86406000e00500510010613240071401055400740c0f01d4645401c0546c000c68030562000031a64510403042e99200c41c4c20300030709005407000b41641102c14643c0c840303507414040060b007990b0000d40f492020b4030544008002296115116410b545202e14851981d00c1158002030840c000342c0301d4a00e11140038204000318000f2981c0002010700d00e9444080742c03040c5824511040b4051940c015062003144400200020b01c01d9004901c1c03081241e848504407200b40d0b140d10302c945000c484050101d0f854050600400c6d0301009441c054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 75105002 1250 75103752 75103771
    0x30a0804053604030c0b040b01180b030604020f03030f0d0b040501120201021c020106031509060605030a0302190204060b070b150d050307110a05030d1e090e0f060609120f06 76
    0xa0320b40111400000210144a1114190000c0200f01014410604c5040d115007082000c00c15051504200060f01421320586103000150303840007072140c840340108080c07004020003520356503450341c0a20903142040c0c0b4210360301d40006c2020707007134201e1400080d10b9111040500041c5003445002800101c40040c0c110016400050750000010703a40001d403e20044a000c5000003900c4941d01d007607015200e15080104641045040c900b4604120742c41100603034001c8005010240d500d0051640711404000068010303001a10800310400c5034020000343c10b40b0103080001c89554400c0801d00581200c102150129070b82c20030301551090701c10302c2104001c801c8604c40010b010783c0d51002d0750b910034400020708000040c426000140c0c0d9002425004120180540740c01c400720034802402c040c902107004006200c40c940e070001c00f13803240c18600140c41c4055030555013606c499145a2446000800c0217901080c10070031a003082d11001034540d40809480010880e51440340d058a04002c0018090883e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 75106252 1250 75105002 75105049
    0x10e04090803190f0212040501050a0603020a030b10090e0f060106030b010e04090c03050a03050316050306010801090e0109080a03060815041707060b04020a0c0209090703030e040b040b030a080405 86
    0x42500341c01102c1e006103401c8031441c03c0381c010340608000b600b0f0030045100c005102107460204c00e001c414199100f10f20400003000f150381e0380769107a000c660450102940000034120240300145d8480402c642050701c0c4806c9408141e645c20081040c0c80d110011908180c1042100510b0b6250411205000d0700280c02c040c000d100e2844002031051401d110f00900c555210164001481040c0756804050b6404c5020750b041c0c0e014a08015249520035220a00d07440044c0ea14a00c0c42441501942c0c081d850507500d64209910786200e04c2c000c1d1166104241442d5070720340030b580c00503083c40014080f40c00305403000705a0501e02a54242003515150894011a216108000008001180000740c48480c00da0b540d4a0309078505011005065140506405c00d00c00a0f4034040c03281c0040080280034402c40755200c0d9661150700103a00da0320a4400140441c00304c0709804001d250a800c880c040c034002500004001c080072001929095030302e1000d0703032964000135042c0720710300f042e00702400f074209080c2d42d091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 75107502 1250 75106252 75106271
    0x30501050114040c0e09130c0e041109160f0302030901180c1406030402030a060203040312060306050a0b031b010e0105121501090506040612050c04080a050c09090109030207050f06040f0806010302010e04 89
    0x102d030103000802000380380b41003d0320b4000308a00c100908022705000183d0b941c5618042c90503128180c168410036115485a400080c07c042c03124040525282c110355803548004030b407030001e40181d00043c0c0750841c55500c40211580512190500c84900c50280310152049440e02e050302d03010382c180e42110360082c1e008104100144c1c03000603480005691101c0016034a90716070400322030100c13450404011050a14200105208031600118000c100000d81000840403da0416580d01d00c49900010320080707001e1100c0c0298041c8400c0510010103052041c500b55040c211455002000c881c114a041694000c128040d6805030307420014101c281c900c907152606100020b803c8001078028101420780b00c0001031230010aa1054030020041b440440c1d1080e00d01c1c3c07030310580b43c0b03602e2900c560044242600184804c1c81c14002c0149240d010380142640038204400e004024113070b4410350ba0018800c12001610f150240d90500c000c200c404c001e05695411031000400922424000c1e0b4803490804c0d6030704 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 75108752 1250 75107502 75107509
    0xb01020f1c030e060a0b0109060c2307090c11071205060c030702100218040f02040b0904110c030a0206070e0315060d020a03021003381009030501050114040c0e 70
    0xc0341c0750300700e2a0441150300d106208034003805000703800452901900c0240400d090550300032140c0c42100340c91308809261070b000c0c111201e004080d4060021f00c0c01100c0f010401c0440b81401240002145c00c0d02c41c8a80c40d143c1c09000d5072001080b01000544042c0d0450341c80c4d60901c6620054003c040c00079440911a48895030f40300000f908402510708000007048400e4020809a11040d981c640299106e40c200c00901450300d1070391400b14001c1d82000150031511001d4800c58064821880010742450512402d200060540000185410004020071843c03000b04001408803203d20354000c00c50751400040080400a1003140e19000768803803084107503d146188441507000b102a0f0340122805070071700000300d4848081d44080c0d040008650350154181c0d154011545905000d1036000300c1c145c0c0621a030285104407040c200985800c1440c0001614092024020803c1c8501c2c2c0410035644030348505007161000c0c0e2258004075141d004042e00e41c01c1900421800001e00c0c208484a0503110011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 75110002 1250 75108752 75108763
    0x61806080a050309091305120c010c020d120b0d06060308070c06020d050d0e10110a022104060c0f050706120b09040f03080915150a0b0a02070e100305060a09060b01020f 74
    0x20148501c0d00c0c0c0000620710300d19840c4c3c0d621b52036005400c4907038044080c14100d44540c01644090015424407050181c00340c00042c00c009215210b50744c4101c04828003617240000c1a00300d6180350b01c1010016030f0800300700d25000e081d0281d805103040c0c950716071503841d1071000c81d0000d50012055411809015140c40d400006492a0082e5010040340f10a840c0441c1410b14002ca1035444407a4548510f51020981900c05020602419000c0381e00040b80f15a101255086e50f00607a0f906030000c01c41404298402c407482c4240e180f045100300c0320340007d0707620079003480059046a00041e12100c4d1400d44e18440703004400345440c00780e5110141c1e04042e12500f1200c041105d01030140003845011035030310b4074104407203030510780988400e84050409100d280e044004408007907214041713400c8003003680500d050448540300f80070380051085030710305507003011008c0d80103010302c0d240d034a00e0400001140c02400f04a00ca98000704000031551031a26000d01181d520303005241c110740c8031269010001800161 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 75111252 1250 75110002 75110017
    0xf01030f02041805030307020a0b070534050a060f11090f09090316060e151608040312020409050609090f0a23010c05031008060c040b130801061806080a0503 69
    0x501107495004541202a80900f40f00300501d01d110000030041c403258041901a04984203006400d115218400d088900b0f02414030125980c0303081e45120045012002e808101600000c0c206080510b11030304c0e92401e00310040d206889254559550b05410101c522410100c9603e005003d4200400d10b00404c0b03450240000700fa006402180200d04461000c1003503655140c1d04041094400f10030385090300141c07480c01054100c91085503d43c40d072440407520203a105016a440a4800401d00101100c2000c0d000d130042d02480440c20114252030b13203900080010b40300b141c03800b041d14280a000e1009019004000741400d4200c8424060b40d0380001c42c2010314136400040c1520781e031071451510341c1c1c800228008a0701310b61030941860107031500074015612591800c101200d4450380c4c4d40180c2d03100d400490319813110000c20002449109149800b40601d03500c5080c503031385c49540b164a91800c60f0226000748a4490000c901841d507072901c0c1c0601c1000c0c1c46000043c00601016596240d52402501c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 75112502 1250 75111252 75111259
    0x20f0d02210c0a02060f0a11010c020303040f080705030304080306120727020c060124050307020606090a15082104050a031103160605071202010e0a120e03010f020c060f01030f02 78
    0x2c1c5010416204002102450350020403565403580c0d4403000000c203078865209100070800c00c0d4284000c4810601ca00513aa00b41e41c0c014502d5070366203589960852031040c0c5c0844a120040c05880042881000510b219a100e81003040e5a03003030007400c100b4078203040d422030907081e448480140480c480c2e9940440c41c04050025810150030101e5030700c000384c051100c0f100c0141c420940004ad807034078411032259034000761401031540017422800480c6c140c4800c5401d64056400800866a242072007954207500841c174005c0019458030f4850007102d026000e030710240385035001e010004c02081241800ba6171040c8560000d80c0360600d41004203002c4c0740c403840013407c21241c441104120743c4050100241d0001941c1c410320444c5e440e0600900503800c003070000d0319201d280601d00c0c0240e40c014415403005000a00080c0600c0034107036540880b0040c01500300c400c2040c42011b400403510240201c0264103552540561103806040c013203403030306800401d202d1004c0d01100040000c0780d20200d1090006405a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 75113752 1250 75112502 75112507
    0x9060e01020a020d120e010513030b040f050105040c03030f030614060702030705060304051506041109040b0111010c050306190b030c0c01020403020a063c050d0902060307020f0d0221 80
    0x1100142d0402030800320181d00301125043d49410013918850204080d0003507181c041102e980c046c0110b80900500c5100620302d207410724107201050324440c0240d44070f485080d41101c01903407a500c150075920181c0b001c4541031180c800500405801c8007682e21040003910f001c01207145403101c4034400b40113810a040c001e2a00040d0301007035444c14131032070000d800301034031441c3d03282170605e04903070b070703280840940c0a055403003401181141c6020300690985401c900115801c3c0101712003000001c0141514103414068820b20140e29400c0030300034a4007046103901c5480c2c82e80741c650140104080000030300c400e40051442c061280c01c100805881d0454508a10306464601e4140014024030440c2c10183d1300c8888200b0000700c4541c0111003d42c0f41d542d000c4440b0300d03851446005690800152601d030340003d6140b129001080c4280d020301082100d42d400072504008513004a0082e03031050b5107900c01604291140d0082501c00c01c80c03020300401c54801007024031400c00110210680d03e560588600800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 75115002 1250 75113752 75113777
    0x90c0402030c0414060d0e0714010903150213180603050f010203010e01031e1b140301050402060d020705011407080603190213022a031306020c0a03020607081e0304020906030d0906 79
    0x1d840a48168040310340c03081000c0c00021503070ba40d070303008c1600c5441d5200c55030014440c00340d4800d00c0101c0449601c43d030703003e01c2600d1000320305020350007074024584e0310b441d40000010f12006125400302400445e0500113050750841c20814240704075003010750210b03801080100041140010000d0441b9000441015880340a64400301c0400d0f45c02000741c0701c240e40d090300040e890000d078005070445076210b90408811584005060907038004440295210300280a028051001c0e50000e1507003900c600000151201110400404903009031010000034040000f008100d08080140000f01c000360300070b41e220f603001781d800100e06104141100b143c05401140c1403040c028107050700340c8403000e00010700441000c559605a505e401039403c1040240103084005902d42c008a900080398001030b08442c115819038081c071801d0303031103800111a01c039410090242c00fa603205049500c840b5524084c0c030b0343d030300301801009203940024000d548a074000d00c0015600c260030210410442d20107040955a1040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 75116252 1250 75115002 75115009
    0x6060d080c01050702070f080f1c090f0e0a0b09010e06041e0e0a12090b040510020321040c0608010501020303040209060103060810050a1d0307030e04021b06090c0402030c0414 77
    0x20781448040d140d802c0000b401101d540118084003500e415a0300c489400ba5141c50440e031b5500341c0b001c0c02c1c02d00c2e000280590f80d60140900811055800d506242038469566000780c404004254040041c10030000180310000540780220b0894000407500b00100e03505020307082c00107003001352500d1700c9140d56081c80e02c07640009104002040d50a01d000f0060655030202d06625110b880c3c43c2200d4032000d01c03448024060080340302c0000d03141c40c0309209007010b04010501110380c0c0600849001c3d0b00c8144403404c0e40c0e5100c03483e456a08152908018800d040905d0080c02e600300300c0c0c0105040c020074400500c00f42e680001a6a400b580480b102e9206071140030042c4d00800c16a004401c142c002c0b00309920b945581500550300031034004c1c000304800041d0180007202c40340342c03901d0050745400070030018000c248250781c42c00d01840014001454040200c14022014020500100094024500b0086042400d0200100c0450140c4080d891840d001902000911403805440d00540041204140c01d45 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 75117502 1250 75116252 75116257
    0x80a0f0b04020a020c120102040f120501060305010204060f0207050103050708040609020f150a120605010504030206030c090d1a060109050609060f0c1006030224030406020a02010b0a230a030506060d08 88
    0x601601c11550354a042c0002511240c400c1540c40c0150b90b625084d815002d814400c9078201d40040b00620119803c0c1164944003c0a4503025503c0d5901d400000c070125500307100500082140d500c0f46415003c031001e0203420800c0f10707480305040c18a824104158242c00c8aa4998030580c08080010706c500d85100041c94005540410342c1c01912000b0440010a06c680040c141102e4503100c0360351035070400480d40141c0d0240c1c051240001d8040c0810801800c0507000785401010b180c440c1c0e81445400c0c00440d410203000d00041d500400c244641c2114070100b0203d0603003100c0b0a01c1d220500504210120300240304108141d405000005410310402c903001c1c0945410f0300c581030a484041810709a00806002c20380800e900c210388881090840ea1420f0001c58500c1100036030043c11555162a070390f00035080704508409554880d20010303940d540c1c414425014003d0440312070301c5000f0036029401c0e2000846035040c043d5001c200140007140c40081d0307407070313000c070040743e00001756521840c007501d290 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 75118752 1250 75117502 75117521
    0x9110f03030717042904120f06050702030904050a05060a06141e0702040501050108130b15061908070e0a0302040906021e0309010b010e13050705041802030603010e030703080a0f 78
    0x603441190281140011000420868440b250000d010384481a1384080022051180c45c50240b4100001c01840c0d20740100720208501170114a5500401912014140c4404a0303101c40140c20002e80100a45894410b1640102012900b0480e902e02500460582031080c0281010f2242c2030b00d000782491641021100315101081003e0514400904080b425401c210012072056003008004252540f1414840b80f10311a1894030304003400454845e420242070280040d0a0030105291400207516458002c0603003000c290740c0c5c49482d0384200c400418084d03014080008020341400c0c0f042d029944c4c2c010403000d03681c040301d0003d9401c0070352428200a20801e112841000e11842e030b5005a1500400650311030a400e80c028000c0822000045814140b500e4000b6030128004c2a1010f0001d03056201940c00181820f00500d0903455624104250380120118662a07800004001c0f60741800e01544900d652003200030750404103165070282c00903200034101c00314680d441031100c180110365001280407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 75120002 1250 75118752 75118763
    0x3010e0304060903060c08040525050907050c010c020c03070b0c010e07120c090c0c0807060b06030a23040c0b030a060b0708091009030215070305070206040906170109110f030307 78
    0x54903a10701c1d01500103c0b403440113030b071607600d4005440811400742c0400c0d03101d40c0c6e010001c1c1441c44000010743c613404421450030b9032000700800d000304003a1184e06115020718075607251103881750803402e03c441c20742d00c1401c00f070700c00c5400070454146a0745001410b0402d031480c40d00256100d50041000c2e07401024041036070782e1180308080700050362003481403000a00c58055100c1248490310340d907180081e2441640142c000844051440700410000030151032140d200f00d80104000401100082e03551308141d4001103001d41c0c1e203134940c004c03030403040421082c07a60036044038601f4501500c40740d40e84142e520030f05030301e880000001243c4249540c0010040d0000c20381c00380d00c1701d2b42414001500d800401c5402d000305d01680503d14000c3c0620340d2002220b80c002c10040030000e8503407010340203401140b011401c2c440e0a10400700141c2c0c0d804054005083e0a1500113102c6207082c160944841c84512031000f940d00d0403008401062083c01d6510760403905640d80c0f015482440b020a14502c40e04002811707 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 75121252 1250 75120002 75120007
    0x5121b0601150206010608060a03030c11090a020904141e1b0a09090609360204110a03051b0717070210020c04060b12010e0618010305010506130911090603010e03 71
    0x103440031012000036507682d140e4200c4181c0d81e01c0c0c0c5029141c01c44103030f40c0c180e0701018042e000c2000030b11951890140c1ca04c9807980d0040e1207008004903c1010f8103480e01042c5a4005c1000000341c00c1911a13045025085240c020190070720f100d40d00c182c0200700e00c0300030151480c0400034075040c14410030100c81041c280e021a030380f54406c3d080101034040500822103014209000015403443d24040d410003114130719280307440c40d196102c09200c0745c500b4900d440c00b600c6100d040000035940d01d100c3c0d080d0081001d8082030750707501d01d07840060031540005d0510b144144540e400800011080050719001a400101030041c10b5a4a88400c039500413640000c2d48040d0f80402d0503245a030110390740103001c0d0207413021701c04140c6400700400c40d1702071401078a00c0045807100400101244220321504154081c0410211403816024451107040980003907030b0980d10340080c8060703030401809100360011003400402c102d03c0103070303506000c10419070aa58030991016021810595017903010700010000f0204495 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 75122502 1250 75121252 75121259
    0xb1b0408060406050609040302030904090309080d0c0605070311160c210302010608060108030a0e040b1203270901060309061b030b03070e150105130504060902030f100305121b0601 79
    0x107994000444084445034140008076146080c003009960050760f054002c2c1d03040036040d005020041201220907010041c00d90000240034034184440f015044260755900311a5901e41040010b9601c050122020035103002010901031043c9030594172040a1010b0088403103446043c20404a0b2860b04072518610418084e01d07040240e0f0105888068840d400174440c0b195101c0701c4544070042407013454044d420401c0300300c5526200e20381e001c484107002000080e01e030384408007281c80e0860544451034260320000c0c80c0c0040001054110b00c01506049a04500c00d940c034000c101450018410001130540300c0c800a400c00a845c0c0004813044c002c0c5201e07985001440070014040d01d80c0d240b20b0b50190184840105500500200451180454103508080c0e415114011036865201010345404412180808115561240616801003840d034101503201d05151114080d0402e02614118104031007001c00c000090011030070761000d00b0b11342080780d221b003040741ca500052510b00d00d402880c0d01800d00040b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 75123752 1250 75122502 75122519
    0xa020a06150806100b0a18030c09051e01080319020c0d0605071d06030105011803080c06060a080a02030a060f0b0d060c020f06070e090a0e190302010e0c0d0b1b04 71
    0x808a80000b0300700c0c0c1454079900580309040186000c0d19141030300821650300c00ca80038a00030003680b00b0707042904c1c0354185d0780e490b00146030265400401405446900740540280500803c008880d948003c16009515115040740c0da403080d85101a4480400403101c18000d009200300b809800c0c0c064800c482600c42e51034288000e01d000c44031407010601d600900c80680703200554654090202605003451079003000d00544051800c1007148600d50768000c00071001442c80b60180c521110b04c0401480c850400b00c1c2006000d04440e04041b4682e4000359040c000741c0d0707000511034035160b0030150000300500c080c8054405048030b03401c05900244020440b80c10051194480d0722242d6080d070030350380d18840e09420a5255041510103a00040c0d0640c0d80700305502d00f603c08590461515040096100040d44006040c001120300000506409524150a041d0280104041070030003001600e01070521a0006000d1680300b000603001135400400114000501488020089c240800803130311156501000e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 75125002 1250 75123752 75123791
    0x1404030c0b0109090201090e180d0c0b0c2802120f040302090f190c02030d060905090609030a0207140d060612060f02031b0d060509011203031a03030307050a020a06 72
    0x2203801c18084400041c441d800e41c8101c0b039081e03030f05948a134002c0f4649203121041c0d2401904c400700070f0088001070100b030703039041240100504482c1c0350348a0410582c200000664002000b00039010020030a23010114084210038000e910401c08849214442c031408901c0c181c4002d1100448810020f501c0c541d6106040c00360084920071101c80b1403990360080780c4050698140c8507140ba49900740c1c500c080305412500401e029201c41e104483c00e162082d440c86042e160168410f603400c995a0050003000c0300b0610034690711401100041d4644401c41e50b0003940c4280c10721075502046183c5683c2d52050b542c03000303080e0034140c1061043c440652280d000c4541c041001703808507030080c03400062040c604c1960007500d1103281c04004081000a11720b8015660740d01466001e40b01d95074946011911303941d0700c001140070309845030140144810510b005001c83c0c24121084081400d000020741c60fa503000000c8940c4007000e842c02988a004886003a450b00042e0180180154100f250904428542070350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 75126252 1250 75125002 75125027
    0x105071406190e0309180403050906070602030105011b030e040b03120d0c1b02010519230306031501051e061201230103020307090e09070e19060501020d05120a140403 73
    0xc0101c06400103840d130b60791080700784294104001c9404074041d00000290755520038024107040b8a00b40100e40080c400ba03102c92022114035601200601895905c804207001103441040109090181624060400344103004401e100355122401c080a0340c4040c0b10401c104441d43c0f5600d510340300158103100140c20441001c03c00211050060000368040a00c1103100707075010b0b1180d0346800d00022281d6030389041d9640c40c0080c00b150200404014103400e0052510b0000075500c40c1d00c03420907404150609102c09a90480d030801c540040c006a99102500d0025003403170b2000048102030355001c83c9060003540c1c1404948969140001210640b4803040d5410440e43c030300d10100503804c40b0055080f0700003030b40d050000854405083c00755001404460350084001012205990399134030800c10390020440c3d4415000241003c440d2661b0014081e0038040c00c2c00b400079000c0c0c1c40701204000c0c9280105011001303c0f8101802007290145594814240801e190300078290601e881e0074040e041819004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 75127502 1250 75126252 75126301
    0x20921060103030239040608030c160909020f06072f030c101d04020c030705011e022503090306090b091605060729040b090c040501060e0105071406 65
    0x1480003413002c0c04044074040c9800620840000c440000705503600c6005c100070700c0b603003042d0fa41d5400300300648200301a102102c100002001c00168001c060700b4403141030ba002121450078200703990010303503072100121034005017562155205d01c0e079810020f1120707070303040c0702070445080300d40d00c0c5400b043c09031894030146d003819011075800301c444070240401515080e900c800081d840409240440d4814800c4c3c29040c2c5004001604210180c0701745170440e402100121400d039074400141591a43c0454880984c0614010860400c05200040044000c400301c0c40e503400c00207015800c08040c01110300e44040d5030802c20800021000340b0b001e2100b90015900c0610740e200380c0038a402000c21038042282038800152129091000590b51550310b15600c03076241039802c2561001c02c45450b602141144a1400703002c80c2407040c01c04d4082241400c2c40456200d020300e00386401480201c0e0040c1c0300d6030712040c1c00c3c42c1a5550388c4050401101108508040020303500500040c842c0c0b052580003044c6101a07010f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 75128752 1250 75127502 75127513
    0x181207080d020a0c03060504110406060302090306060307080307020607150606170603060106090b0a050d0c03051e01050609060d0902040c02011a01090f030b040320100c0509090402040209210601030302 88
    0x15030107070780e40c03400040300034092401143c4c140006081900669001392080c1c0030078044c01710000009050340c01070b4000ba400641e01240c0c402c164a420420300d900080e050380541002420075064584a1003400c102900884000901030304108012101089094104c00208119620382c8001040b0554070580b54090391510710214406180114980f4101ca42c0d640f40d16920901e440d408415507004900322030f040c01000d000e106001a00d038090610307001d400703a80000300c51811000c0c1c80c004045035485035082d0202080144541d0319050700f12140003600b120196101d51440d42490040c10305800c00a4209040001e088407544d01500305c500701c1505007200003440700707150004494059461280051003607000d8020408503103000c41203a0068082d14041c011983c590b40000b01c0030000f1444000203a0004d40400c18a13221445000d00308151440e000c0e25281d10300002a0f00c040000d080a803007035074000303011441c513590000d440e21100d52000c003800a00305103a0102c1c0c0c880030240b00950160185 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 75130002 1250 75128752 75128773
    0x207060c0518150d05091612080307031107240e030711040903020312070215010603140402120106090f020405090702030405030604030305090c0904120905060406120218120708 77
    0x1640984400c601200200e00030501103500300185100300488010200c5804c0282e107081450034004ea0b44554000001001c20001424001f1240422588040c2c0c11100c4c015000c0300081c80300040300d80081031481c02040303c4004500001441c42001e0004040782000c032481030700002280c41500540401210030440020020412a140e02c1004e50040010384400c010480302e192540c051409240284100c038100412030b00030045561041d02c0300d1006da0b00ca5801c00ca40005c82c45d0b04580540010b240a203c3e01d000100b11000c5d0145c06000284101c51540c01c108124a09510032001403903410011700110180ca110b0900a500c0703809024081c0c00c141000841080c000000c4070102c0d04050700401a076a1952003c500038007003e003003242903024023480040076a0390745a415008078014014401c10b00c02604000d0404003082c0e01540c0a8035041c401045240d4128224910a85090b40301503580d85030308469242d207494042c1c0d8568091102240319001d40700c0020907600380c641540855511443c0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 75131252 1250 75130002 75130007
    0xf09180d0f0c0f08040b130317040f0302130f020f0405010207080703050c09150310050610030507082701060815010e040c0311011106180c06070503030114060c100207060c 75
    0x3001c006900c0851480001d160004809410b458191030040001ca418a525a124915207038806200f441441a00c840140b00740300800400035850100207070000c3c030380b0303140c88504484104544000b034441d4044040070001c2040b00d8019100c6c060400e4001c554850300304803480c1c550303003140c0551801817040c0480411340c0840028142c0507640c00100a105840074031007000301000d070050001c0b01c59641c0399081d01d00383d2000c121610013a800c0b120302050303d1500005000f8034048100140c030415042c84107002c60250030500544d00011000302e0325513410488100300e0740d640c142c4c2c421815036601e031080c00101e12401260540c00c50394001007501460b66030303d407041b110a1059902811781104080c04000041c10425100d030101c6060502d403039000944018641446000c441c05c0b040c030302ca006000942c248050148030b001c16800c40d2014108030a54680640c1d902050007000d541000d87c00c1000790642c2c0b0001030744c036400c000c0c500326107030321203000b50100194010000459005040a003000e90490 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 75132502 1250 75131252 75131267
    0xc070f080f010621020613080c0f270601091a07050708030a050a030b01111b0405090316060c0c050f010221060d17160507080d0521060f09180d 63
    0x21000c5000350031480f020f00011080c4c43c071418080340c1c8800e042001311024804418208000d1080c1d1014022206522051000c01044001c4d00da12440100c0b101d99000041d4400c01031210084600c00e9900d640d0720001a10388880f1a00055032100e4401e01e00404104408001c020640c821001d9582a0740d0b2401c540b07071b4038000d800e40c40c0085501440011107580c03099011000c041f00501d00400b200790280a05030500e242d4021034844403903880038500e01428580079881d000700b0300100542c50004035100031940c1c2c1f05181002007072141c0792150300412910801c0410f151940180940b070384800c1c0151030354001c4d0700c40302402850fa00e001602d610207415102c0d43e244030780c03405011468200c1c120740e141d10642c6c1641d072501204090a2040800f00310b202c1c81040130052003440284042c0d0b007000c0d182c9147ca071000680004101c403c111519558a441080c6000025a41c101c6405521000006120841c600d60f000e03811010710000c1242840c21400c0c907080c0d00403145c0584040c00304204d011910384 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 75133752 1250 75132502 75132509
    0x230a0b01030b030613020604030b07030203090f06010b0409020f0403080c0303090c180604050406060b030a200a050403150902060d0603140d1e050f0a0206040507060e13110c070f080f0106 82
    0x10b0b0440c400041821760a12803480c0e0241c8010b204e5840c260312640da410a680d4241c2d100c00c002075000c0100820b400e402c2100c9080c41c4010350040c0165131410115251a200c0c5010341800c054001c1089540744521200b03550165500c4965941c0350444c01840a030f6a8004660003001c0b4800c3c41d180b1210350500e9002242e1080400380c8200c50f69a03a20203100c0030f028094401c4440c1359503072800184a000010146018000c440b102003800c0143c3c0340d04906004011f07030107252005c420041c442c892a000030483d0100c99009812010b00451044400b005019000c0040d40008001030702e030852031074035071200054138420f21409045401003040c0590310300504280d0008144440c110080300c10441c844030569404500d8040e240900811f40708030750f07410400c0d100b000340c2d00040074002000720a00485021303164a00e001c211030050743c1c1c00103e0302c214141001e140240e640c9401c1c540c0300b000500303c5040301407640880f0390381507941c4101405d1502c0c611039400381e40111650200704102c18002c400c200d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 75135002 1250 75133752 75133759
    0x40303050a2c0d0203030c0d020303091005010e07030b180408070b0c0909040602160804080105042d06020702010e28150e041805070305150a06030305120604230a0b01030b 75
    0x2c060b22030521040021a440980c0e141c8410300c4085086902000f1604007002503a010310b8072403d060710410300e0012028a0004e0740340c1020018070104403c000c0d030a80c0104c1a15012404107210ba010070f0790f220304010316044003000740d17040000380084c80340244800740c414524500ca83e030715451000200e008401d480c036440054200410301140e0140c010b8503650f801c101010005115683d20b6021a40c0250321248050f51908100800d0007080d07004060640119082200801042100b003c803109040000801c05540030843c80d0135a44190f182002d202400740c60811a1000c5a010a11969848031031446106100c800403925103014007600544441545540d00c0341e03190032082002400e81e40800000080c548a00c88010071401c20012009601410240c5058148402000302000b00201050249400c14408100095103c0c08552800701c40e990340b50101e440e548005809031000003210119160300b450407a9200032201d03143c50003103002010400180300b401d80154103440c5104c9805a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 75136252 1250 75135002 75135077
    0x50405130612140f0106090905060a0b030304230a0303020a060c020d0e061602030d050a030501080703020a090b03070504020408240f06010f030b03060a050106121e0908040902040303050a 82
    0x25407402403a51124555005503055002035442d4642184e15030350141c1f038181d4496050300d0501400f4040940c200c1800981444031030a010301096480c4034600c91468688520f400c0a0202015000c00c0346200400a06858215590f4100203580d40140c400549507903280441540126000090120707500c6030940b500d40c0921035400c20008241c02034080c00030300b41900c196000050360107224280c0c8180c0e85481c2e02c0e03151400f04500408480f816040701a0641c444a414405aa074a042400480f1807001003c2151208100420700749005540101d0300940081000b041c2144041801e0080c5150000c0da81c0b1000c1c7c081c26442c40b2400c003a0340c0c10200200010201d51f20754421080c070030400c000340c05c0105280c00460042031900404942d40d50180c0d40e07a00040c00440d41c0710340519070000300b17450244041c410842c02d680c0300d019012101040c8660340d080315410050440300381c0d4000c15218008540b165603e0801030b08d15480380d0140c80009808080d00035040e401401d1300701450006080c6c801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 75137502 1250 75136252 75136289
    0x71d010c020310020f030f0106080103080f030a091203020d0e060408090904172d0306010f0f020c03060f01050a050d0c0b090a03060f09060b0307030b04020d03140a0504051306 77
    0x1100c003400310300142d8040c020300c83c0b0300e10600024001015054010082c607982c0340f4000213000307103128060300401d00708900c080040001c96000d030140c400c1f540c0d142c0c4090f962910703158025801813420460003414280291000c0c81525019409040c0d4003c0140042c03144044180391592164001c940081c0154000d10201401d4180f0648141e44288501c1c42c066001d81110241c400e42d803c00c0748001c0e10f40508040c0c00402005540340820907280e11741ea50360550a00b107001070040c4240300e1201e400c00c007200d0311a0440074400c201000c0d0f152000f8080c0d030313002e040600524154080c00d000f60b60040e452550001810308080d900081019042240304000d43c0c18165110143d61103a031180f0740c00f6846400200121342103118082546102480c0059192107628001058aa4030100c40d4421780215104001046d2156401076000307504031800340c50141e107403400b96243c000003512003400d0000441d44400d0990403100920541c0d070101c03404260800c1000481060f1040307809034034000050550900d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 75138752 1250 75137502 75137507
    0xb160b2d2d010b0a020111130f210605060307091a0f03192a080102070302070618060302030615040f030b010905010303090b0a030905060903120a02090609120307050109080901020105071d01 83
    0x2820f91301e040344000b260700c80401074004c0039900035001404102d088451b040081010300c0001c1c10042c28818000c6050391400c1103020700c1152400d00242c400303522280003c20954080c4180005000043c804110500c40c1840c0d1201001100e604d6034026114400c4081052070000354080740320074000b00a0a0460803692000c0d000d8200d8000444020106400d440c640003484182c40090003c20703000607190003441c01c0013494203041d41d01241c00e02882d660403508420403c0880d0041e1241801c0160752a1030b04408a007214560b402400020346010801184d1040350380c1c0340710708a90103040407001c541d881e2101001107480a02c40200802c01740c0c04104800c5442201405184159040005030640b45449483c14000300f01c0e0100000d130800103c200c00400715144a50301b03d29826030842c100701600020840301d10036103a101c0c0c400c10310082c6034437040c0c0c800c01c22107902c0c5138410001c1c400d0b040507113400c1815820108005003d9420000058406442a4003034020880070342c0d41c1050161058005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 75140002 1250 75138752 75138757
    0x1112a09160f022b030f0908220b0c010e1b100309110a0303120c031a1c0503070c030201030b0904020a06120204090219090b160b2d2d010b 61
    0x104065014014044c1c41103181103200e030048035100820036480c800c90150050440c0c015240030303101d0300e1601d05602c000c12102c0701035601404118408400c841c0300384685010031415a80603040d0100c0020700054401810b400000f681340707445085030f00915038100510700380324102c0700454105032280384000d1a94440c0d0480c110342406503150380080c0001d600860522140c0380c10a60205400d00a501040c5016104070309400e40540740400c507464044403840c5629840781e06083c0f10302d80384800044080030105980300c21540c440c0481e030703035200f003442e00103500c0c1118401a40800d02c1e0013095442401c0903242c41e1303ca207500401d001d40f050b02702001500d100070b4a490608a6941c00d10000c9491b080a200030b0541c418654212501c0301c0c51100020031078021070304110901e250521078510090b41588107030030aa5800074450350b03140d0740c0e4143c0850305001c41088030002001d00c5a0322400041d03c0206902a580714561f5000012081410811195032828252880a03040c0c0040003201d000001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 75141252 1250 75140002 75140027
    0x702060f12091e030f030f0a1509090303060e0903070620040602060402030c0105040b0a0c030203071e060b0306010b0f0715060b031008070b09010c0201112a0916 71
    0x300d420100d07600c109180c100412100c01e0165072000c0341000c483d140c5881e82c40c0d040c81c0007400843c5000d2082c0c8404205000c0505000c076800c842001007980c0000540200300d108030220300704454181da810002001d40080c40301a000304c1e24000b8041006a1201c1c4010710410903040118645007a42c3e039400c004212610210005045103a0812030403084000180014487c0368001c04850400d0300415041c03104042c0308905201341080100900d940181c16101d00c501c4508048441c542c03036040603401e61087e00c100500c0303190940441c1e1001017003c1214841180a0041003140d400040281641c6482c28041e81d2110301c020302c000b01c07280c800c801c014070081d40310b0f00c9100c20210311601c41c2c07070a40c1c040d80c12003542004040200080810b1100d6038500400c01e0000510b810352030510800361a20610264604115044a01c4002d42e4020101d802a01803400c045640a1004c1040c2c45580744404c1d41520101003650b2003543e0038078000c2e440070300898400e07014442107503449109403030424440700c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 75142502 1250 75141252 75141277
    0x40c0602391203040e06040c090614090409140c030d0504050f01050d0c02060106020607301409010507020106080705062b0614010e030d12050c0c01060909021503010605070206 77
    0x481d03045850316140c91032000a8500030046807140c0c20850455031691000340864002d07460421140c8155500010a03000c03035042d401c0146610504400259007481940d0140d600300b401c0110100c1045070343e860740c40c13040390074005440c0c480440d4010151140c40a001500000340c05003c02d00440ca00a454510400070504200b4540059008a801980c08144100e4050380001c0d0040013101c0e018441c1c964000018500030b070b0100c3c50b500e511003004035203000c00c29040b071070005680c0200b0602d40c0802601d07101e02c0341d02c000510b040300800340601000c584603030065080c03510001e0703040f4000802000392140180000d0070207100c40c41c0040480391103c0740041c00c1205030031003006040c2c180b00d15030192800301c40c03901d001d018103c0050604400c07040300c14040d501c10008100b0a0368090310382401510880004038241d2201c0503241c440e80a440000122075190036400208641070358030107580c1ca071003903441d400511420107881303540380404d02c16400030880800a550041c40d000000300004180803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 75143752 1250 75142502 75142603
    0xb0a0509030f0706020d110703060504030c050307110f030106080309190e0a06050f0906130b0316180e150c070203030409020d0203190c0e0423040b040c0602 69
    0x300001e00e0306418056031075807038100e600e05002c482d50501c0002105980d60801342e0030f41e5100b146169584005220181030a9038a10100b802c140c800c0300407098050b00901102d0710348202c1c3c1003c0d01207259119603180b040d070300346202c20040e0a060161034200c0d00031601440c1042840d50078002c0350010700c0010000076076941c1011814103400c03c1d0b41170217560440310000e4407034144014007098001c0600814400c850490403c403051341c40c00c07a801004002d040020a51400200c003091504a080f155009046600c07500490592003a500707819003040203940a01514045040f40c5482d191341104e0b410148078400002040c2454030130003032a60b00c0c4080c00322403801361382d0402c03081203030404148000758a400206001c005443c1528008485482c5c002c10000c40840c181d001c0c2040740c0700c04920340031b1034032600c084490b100c03139a081da55005001095081c01d4a0646003540315100e04503422a00105a480d001c1540c034400100001381610714000314135494699020b0b100c0b4010030f41ca4000002081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 75145002 1250 75143752 75143767
    0x140a03140c060a121a060d2003181501080705010f090e0a020306190b0313060237090609060c05030c07140f03010506150901050c03131508060a0b0a05 66
    0x5080c010200810035945480c5000038141c400b400351170703010b4401a000100c0d038150103c0799507030030300711009400210b81c0014011000140005460190056122040d8004c01040891710750898900180138044040d03e640507200115602222000c0c0924442c0380d00c1380c2130600040d4002c0410418840c41820224000b5603034031035481005900311080c0d80101d03000f0091001340c0c1032000003010804101000400680e003010070702005804020480c089584050348d520313040c40b05940c1161040601c0e5200701111000ea1018002c200120701c0c40084500081600711030039034400c015120603200c165030b402d4101440c020040f2440c0e40101020fa07a03e0008102e103101003141041880010700b00070a0742440e1030112403c1101c1002d000182a020780d04240810490b550740e40c11801d48025404421034440d040711004a540380a109135040c0184400204480c1d601d0480000d142103820307800300075850380c82c00581203d4600c0103654181d0824038103181448139101240160500f2541c03884e2280c1040741 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 75146252 1250 75145002 75145009
    0x609051005070306150f080604020307030902030106030501052d04020f0604080a110103060b0406120207031b06050a0b0103021204020d06180804030c09020a020304060e0301090b09011401140a03140c 87
    0x41c240c80040120340c1c1d441007001039282c64510101c00030161300344014038a00380d46010f440040010141485541c1c0040058013a60182c1c2c495914160090b0007044002e4403407600c03500a1a0039a8108005003e82c007194080142601c034107072280c66502d160350519101c950031310000d07198800c0c04540c400c40c280070209400d581081070240190150790074580d90013000e0005001c4913206d81005d2011003041101340b00d01900104d500110311390060005a83d1121410100c41e4407403498540b80c41d00a0b5010752405105154121034014203400304200800c0c0d0740000107500b05d220300c01c100602415500001405454580b60723241d0500e00079500424444030080c440c4a00700344503801115005404a000d1040c060b003440b041c0d018001c03010045240c2503400c5006541c900852007807030100700c8032020601441c0c4003900804449540174902068506001304401e0203442010350b0340742000c14a100029505004100c807500c1e020003d040d50078144e0840c0c84401d14130b100011440860b20482c07215110301d4a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 75147502 1250 75146252 75146261
    0xa0504051302010f02030c12070203011d060403030c050304120804020a15020d031410170c03030703030b01020d020c011407020f0607060506090f0c040918020310020a0e04150306090510 81
    0x445007058038511080b44000340000703500f452280d08541c0300f40242400d5810008131a082040d4201c40281c640000340700082c00b4020242a5a0130315031f1000001d2a082800544c56014900c80d4806110950514074121840d0108a0300030b0100c0c0c0aa20740402560301038078503aa000303400500f0240b51503454481e108821083d05214400607440b07800380b403c0c6940e051107141080c0c0a01c09080c031040c20000390340b4001030514002c2c1070307459141165603c0c0002c8100500d0841c800080d084e661182c00c6410050020703d2040800b901600407802c0e01c021062021650100f6598161640c00b06021100c0e0001c1032a005940e040f600108070070350345145a82c0300805020403c4c8a180081500c0ca0003c0c05d01542c0f88018001e003101d1400c01003845040c41c11074065405032880014000b07402e6810307480d00c0c982180010406500f6010b40d810f030741100040c54000740025801078940003140219403052204a44a0b5040002c83c51041081400004c08a0300b140d401c2d50f02500c2100e941074100b1450200b200c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 75148752 1250 75147502 75147511
    0x60d02070f1b0504140403050310081219031b051606020301090e07080303090312060406260607020a030507020603070e0a090b180403020d081906030b0f010b0717090a050405 76
    0xc44110034080d410002c1c2e80d401e07102418040d1403e001e0300302c511a66403070110000d00010207006011000950166000c0002c20090064004940391040c4070a0200400d6100d44206c0100d03800c8180c0d161000e0303020303001e03000405441d0401e1030380031080c0300011220303a04241040804284a4081d90000c100a40080c42c0a0010749000180341960000c10a01d030403038030340c400e40e02d40c0c1060040100325503012003518000c800d04427103600325a460400080003011140c0003107041e11303040007590741503086400c4050800c80c40c5101312074181e2101c0d4426687c80804200c01400030300d0400802005003000c40246411524a09002c1c003132801d039100140701e441040d04503199444d07940440032420329149498080c0690300c2c03054a0a00d040c1a02e0081d217600d0340d200e0407000d0240300b40100c3c904613401085148484601d44040001c0c0b9140d04c0d200c000014140d41444040003900004a1012041c004446000da03000440d48120620b21501a146030003103480e041d1300400c0c1c1705000030aa2503e02615109 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 75150002 1250 75148752 75148763
    0xf0423150109060602010b0d03030902040b06040e040203010c0e03070501050f09030a0503070302060a0903050d022a1509032a07030c1508070c0203030d0b06070c030f02011b030e060d02070f 83
    0xd0350305118103441100c105030b020b80c046a0502c50b55049a03282c1e40d030018000c0350180360100d0010841d0000c640907009416002e5005580082c001502841c00d440283c0168400c40080c00304003034000046415480c40e0525503816003020408100c00e42c055001808000208030050b4203100303040d00081d08284260380d00b41c60540000600d0420154140441580103103001c0c1d080140760b040e41c07802040c500449030b0084103d1303400100301a0306030510410007903001d4040c007240007641050f00c00c01d4a0300c1c20300502111003130071600407a55542c004420303210484410740030055a0601c111500029054240c01c04d4814020f41102002044120035980041e0880c4001400060f16010004140e540000d10708020091002c1d10700340142e402004176101d4110040010548002010000d01d15100d0008000c1c2003445641d800420018040201444107000743ca40c4a00030700034a10a1000c2e141340503000303000405000524083e8500f66002d820044410100182000c865a8443c40c2070241d050061b0b03503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 75151252 1250 75150002 75150043
    0x702070501200609070305060f09030f0708073201090b0a020a0903080a090f06020303060a0312020c060d050412110d0813020301020c070f090c09031709130608150f0423 74
    0x7c0c804100401d542020380d41d003442c10249000d0180c0c81d12030054102c0c2c10b5800800141200c10720600380142c40405420042d8024840c0c212900d000300c135400303100222210900440880211441071045444142c0c201a0701e19040e41e51401400c0254000b40b80c003010311902c41e0010010800107130241c80c03190740907150118074504061520318603c11030303440b1310110741c42002040455203c0c0712587c1c0881c0c1e481b19005070940311018040e8203281c003900905400040c041044441c149030f581029004038080c0700b4100307103141f81c030804841e005042d84240400b40d00440388040e005200340601540a030900e400ca9000812590000382a81c1c00004090400d03489090203200c45498101000010842c082e03040101c01640180078201d1802c0c1c0c4005400310301c250f401c001e20f5076002021220340200080910000b49d400180010040880c0d0040d00058484d00700c402c3c1028075030742c903258040c18001408050b607659030f80c2c1c1e031030440840c01030030a2600d8846c050859488010481c592300119281128031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 75152502 1250 75151252 75151259
    0x12080601030b0a030302030702010f03180303020912070605070b10051c050c06030915190c120f060b0301030f06090803010602150903030106080105060703030207020319020117070207050120060907 86
    0x1002e40e0380300d4241a124844690342000000d03000800c4849190703081c00e1842c10f81d440c00c1c1007640205241480303a0456160b04605604066169000f04450041107502c004012070b0881c1c074681e41c2016000f0100424003c00102d40869604500d16520080c10f1600c82c082c1c980f11000310702d505101628084825184000c160b0800206002c82c00602d68207a50850551500269490741c407031550003811a0a440e21002c1800e4040b140348603200340740b207990107000c1081342c0d8000130038000c011645441c1080c589000d00265032040d0080307004032500700e0701c858156400c50700d402c1c14030001482e0807100b969844070408002401e14010b54001d09081e0090008524401c06ca81501c11008001e06c46a40041005102c1d03142c200b51868152030094070116151701d0b26160940091142802c082d5151051010180c1c4900040424000d0745100383e070b6580c030b1103120000d44800c554043c0c0700d080140c0c00402080c0031717a51242d8851515442010495054a4841c0100a040841c1a5601f0b40f10350070410051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 75153752 1250 75152502 75152507
    0xc05071206090b070e0907030902030f0a120801060804020109060e01170103051b090603060a0504081c020406091d040210180e04030315031208070903140703170c1f0912080601 77
    0x60351042c02e6042c0b1245105c0410000385550000421400a1590f190072844c15900d003003007050305034a40d0380201e500e008414200302d1070f402c18006544c800620340200105030a4442c0c0ba9a6000b55410303181c0c1c034051401c04005842610600f60b01d641006085842d20b01003144c040c18140c000c4d0301810142610b0f003000c90802e0702540310008220301686030081070010340d440005900d03a001c0c42c003000003d1f041d00c5500c0e00d448148100000904005805401c601c804465079004100301c40b01d40c1c80d94446140c0d14194008003603810004024190038090000d005801d0413802c0907072281081c0303000743e1408580d94a0303a0340b210064000402d24031000d000c08c010142c040c0304601e0032501c11011600e04515558984050400021a1804010743d0f44080346504d0f0050400001455200c01e02d8413040b01e1905505617140b5040c401a5840c0c00c4030350038190407601d2041114400e400010280c1049074000740405200000d040020f241d0f1076440c41c0701e4011500310020a000c5032b54a03034904c072180c01d140000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 75155002 1250 75153752 75153773
    0x19020c01020307020a05100203070f08040602070611100b01020102041e0504060b030f040f0f060606030c140c07050f0f03010203090d120b09060d06060504060f0513020c0d0c0507120609 81
    0x980303040d54010032048025030340e241010313000c41d1070440303481240d03001d034600890843c09401070080900c130348014100c04110a09014100392240c940c00c6170f58055450900b11108500c9080111344c64224400d105a545111b0300140d2260006000142c030305959201a81054041020744206414484900744100c2c40d1500884004000c040076a9083d410b0803c2c030551401d40190004005480c030710400420800180580c07403000b0b801800800105a880402402501c5042c2c20100026140c10801c414561142d007a14a441203000c024003040b4100b0081c094142580342055031f00c044000408405a5000d00055100700702e5100640820313131404c0c101030aa003100c04c02141c40300d070410095140588031280e174980c1c4200121442c04212405003407000c002d00f6950003080e0801e0600d0f00101c0e807d4240000e88040b6071007a10314690041d940c0e4003001c224061542c4036001504001080c80740340c0d115030a0210120300903000d4840c15030751400405048840c401044910310340b504900d206004000c0340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 75156252 1250 75155002 75155023
    0x7090519090e0a051e011509060305010f0e0309100516050c090a0c02030901120902030709051617070e06040b130513020c0c060315030307050102070204050714040902030403050d021902 81
    0x30300d45111990764090b100e14202035549404500c00032407080100d001d4126007401c001c1000c1d404d071000c0d00e42d1400230207000c03503010594080d803d20206070080e182a00c00c035000580c2307010256040c90054010000e12441e081d5031070040000074880c890520702c13400240c0c06040d104000800040600105003c4045002801d2940c0c5501d8625a058031a80100466a21032000d113004008101e43e103000c00010508600701a4040c070070b149001c6880d2280303500c1240100d2583d4808140b8100400c0c044a650540d01350200d00790301c103040072402140c002c0f441c004e85000021f11260401d03854000400c056088050400708820200000700010b0403c04214a0500b035240070079490903030038420191f51110003000c030a002c0c0000100140240c2c03456a071501e840a0000e082e40d03030b49c482904005001c0e403c1201d05906c11464500030804007405843c412030001600204903040500d488540310003500024429418800200010401200f0901c010300c07092030f800e00340f0359544004900003480c0915140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 75157502 1250 75156252 75156281
    0xa0e1906060602060c190504080d080906010504092411030703090b0705071e030201020d060f0306060f03020d0816020d080a080a060f0b0d02040b041211030a030f080709051909 77
    0x4d041c0403800c40d0340c034111b8400b00d0b441860a21035a900300d03001c032280e102e2a84030300301314003c010381f00e1303084e9500040060041c01c10108413401642c0700c208000444090000041150709040c00c0c895070301000d42401c2d61070b00031400c0c1c00690210345001040e4140d00880d40800000da44902d804100042c08485031f401c44041e1418904004003030f51111000414080d1a40600004204110805200350121a12060254000d0080560780c0c0040e00704c0c40c0c403034003044405608007100411914031140d400d10490341c0040c42c000301c82c1c0b02c40d110b02c0c0e055444842c1000c60000301400a0015841c2c0030140c056143c854500b1a540308212034000300f40c6200546409511410020108118411015141d0035104c006c02d009070b44d0f28221104a00034401c40d070101110364000315002513038600e00d00709401e840d4015407699240c194000105920b079100344e100100480c000514100d410340c413038650160f0210783d5080022425485030002841c1a610b42e42e10280c030710040d08103100411a6000780d503010402c41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 75158752 1250 75157502 75157513
    0x3070f44070b0402091803130f0801020c060c07110d03050703120603051c02010e010f0c1706030303041106070b01090e07090b0307170709050c09040b1e090a0e1906060602 75
    0x7540c88124001010b4000303441100c101020604209030220300741003042812040b20303a14403030141900034803230705441002841643d242c40040c9a040600032180c45c40c07840400340145650300c04640701e054002850071f46142600442e0280c9940b1248916180240030f40c59a0f91510003500c0c0040040048000300f001d55820040c1c01c20025000042440d1980c0c0c000c04011500402c000342240107102c10441074000750f00342b200510300702c006613100503003480c17181c0ea0b6807034640c200ea0280444800e06640082d00f56004000150106d04007401012a0b600b00030416032801c0712075211034242e01e4003a00030b40c007042e2303903140c01346a24003007040082c005008407202032041c4007013480042d88a698621507240042d0603035181c0d903c5102c0500c18400070b8000d141d0100b0813428907941551144d08940803050180c0c1c900303112803451786081c406013844500e0042000c020b135004581408031450003e0018681aa2100100f803c101d01c24003260001c080c840035092103005060a1007015140164004810354001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 75160002 1250 75158752 75158767
    0x70f030b070c0f020f030c040501030b061005030c0a030b06091206010905090c010210050601110d260903030a1e020714060105060301050108041b030b180105010b03070203070f44 78
    0x2c50640c0c00c5010780482c3c00c5c051041803000482d0802107421449030307105e80b03400004010011b40085490142c14150707120140042d01e804166440d1000713035201d9409800911426014a201c0c0d00040120800a0481c0d070501d008032021900d103c00005d10f13485079030440310044c00940302070310549034446000c1000f8001d1100c00c10003c3e40b1821010440814036480310001509640502240c07146000004100c1d0a51000018003e02d031403d114200c245015075101003e002d88188a8900c0c05600104041c2d03255488521040c401080f44c54106d00c80c3e40d62808046030441007502c05008080d018000c43c0314005911825241050b0058010764482c500500062000e0399001c6012980183c0c0110702404000486c41c4c00d41340e614040d44002c19200e004405c0041c086499400281c1e181e2002c0c00a100b181d07222801014940421902d000040e8414040440864682c3c500c4000c3e8074004c445944c00b0181240a0039088a150051015490b200301c00c18049001d81c2d40c0d295400500e0810034a050044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 75161252 1250 75160002 75160013
    0x303090a0605090d020306190509061014031510050f12070303110106031709010201050f010311010c06110d020a1b21032903010b030303011a0c030c070f030b070c 71
    0x30500440701003200220f0203407901e80719205609041c43d0010125406840e081c1c24142c2c058111048400342d1a05190100703d0a0b100040c0113801407403003001011489013000c1240c4142815641c1d40d5a0522540141502c4c1d2064a130b12140905d40a00d00603641d5411303c0300b48083c10b904044c900f0300880451001d00f04020b008100c20040d258180b038004141211020068094101904050302d103c0e90f1043d002203034120b070300003003e00c2c050030b8000740115035600c0c8004400a00c00d2002502000d12511002400e6109141000486200e0240000ca8184902140d00640c03c200012407000d6400501c0354036150b0860300c581e002d420079001b048459101940c1e90380903400c0300c520841c0c8803140800c2120915009410842e07081e02e40142e407180002c8076498400c0c1c1d10211000050003940f800104801c1030402004580c1030380e4104500da070710103c3c0b414915441e5440303407a0002c1c890205000c1251080e00502c201402455081401e00011b410740c03c0c05048036002403c1c400a0104c4078004800180707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 75162502 1250 75161252 75161269
    0x5030d090f060e0102070f060e01030501171f06080105090601081c0f2d0801050405090304031a09010b06070602040e0711190501270c05030303040b010905041a040818030309 76
    0x2c01a181c100e284046500060b03240c13004a0b0060312038500000b00203e8090b40c02081b040d42c0f020242c3c0c0a21050740d0310049100300c07800d41c400d50036642d000403042030f04c0034000300b001003500c012600d0001240c950f0f07100c030039085800544505034181c019a004120520f401c00c41ca07904001001d03a0030388040d00402c0040c0c8500310808402d400e1001108403022010f03407801a0011840322895100c0e0703c0d504d41c0ba0010401d400c240601d0b40700d6440c02003c02c50440c00001642d00b580c7d8000201c61048641d2122130180340d0000348610074642d22468680507a84650340501000f51041c0000b43c3c445080010240603124018040e1040295801a0311041c20300021003ca1900380300e90200790460003410640e0140042c91a4814004c1000b07840e00144040b091080c043c1900902004801c1c0b0b44030010551244003d8030040c00c0a1003502c0140040140c5070302150b013151241400b80520b1108014048401c44200d60a0700c9008002c2030035010100c52140300f0b0b4a4807022009540b40c1011200090240e070f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 75163752 1250 75162502 75162509
    0x30c01080114010504090e01090302010c050309030a0e0f120a03020f1203060112060b130504050a0b0604030b0c07060c0507020f0306010509010b0c030408030d0e0d0309020a0b07060902100905030d090f 88
    0x1290441040c04584d010304116809803000d543c2c2400814189402580070745a4400c0c1100150300c0c104054000364410416280280c11880c05146410709408007107484240300d501040c1e00260114034141c079992803001260340090440b001e001030607a1800d0207810400ca4900c07140954100c0154040c0c184111400c40f41c0c00202420004910031600300c11100410841d008a03800d031900081c0464500404840681102c1c0d0480f42804181d03918220f080a0703c842c28102c0390496424402400021501c4910715801816591014200241600d80000f900d1001c8551030110b5800101c3d0f1055007810103500072002d605500414541d4500808150354000501c50309580200109000c10f00d840144101e80c000c003283d000f22500c1c0c040c800075010040803100c582ca80350340b01d0780caa040c403414040e0080c0c9880c00c0c0c0050900811903d032000300300310350b0720500e0210f500303076543c0b00c0032001a81c1d0b00075140d840d05150f94401c0c40282c2000c0901d454020840c46000034007030003000070814085d85140c1803055 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 75165002 1250 75163752 75163769
    0xb0403030f020c0105040302071a13150c08040f0905060909100203070201090c1e0501020613150204030605040b06010f0c081608120901050f15030a0303110c07170c030c010801 77
    0x70400040c1400030b0255140c803200301c0d420312040c0b00505900003070b1007040e1120380e900d90b00701c80f0001066050b40d01c0b9a8018145045504404105c0c00400c03054507411003c0e00d04101c07020780c0c159540c2e401c980c0d00c5a0050880b00204200501c030004403841510b42c052000d541a100720f0810b4910941e03583c85074148000302d02c0d0000009246c65200b9000050655480305504600e5a12490501c1e40b50441481412080c0b501d03c00001d06588009101405250400070170380012130903454001020700c1d402e1848800503001c02c00040060110f01c41d06200c0c0f40110100c031002c2c1882000146030012a550036030400044421800100f80c17450115141600d0000c1c40700442c2c000c520b40310b03030755000b0310318111603059540d0100301154406402c560701c5040c010342c059541c0e9540704c901c4061050701c540400d030541d00044d00c1c100001d0081e48064880401200f00318200540c038180c0700d25189003608a1702001c414400205101380003007140c4810303030b60100d015040301c20342000001c0064005205130441c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 75166252 1250 75165002 75165011
    0x2030d0b04020912010506040e01050c160317070c0302100606120f06030206030c0c07060203040e010608100906080f12070b0402060a030b0402071208070201090c051e0603090106030b0c070b040303 86
    0x259141e90466183c480c000d00803180800c040403e9500801c0101c501c60b0095040204c03414502a061040c1423082d080c1c0c0c6085401d0000940100341c2c0080380b5501101030180d80c480220900c1c1c1d0035900148107001680c0c90b0881d400103894002e040c030582505500141d418034109204c03030341c0c10070305c7c03507c0c01e051403480051088040c1600070041c0060b544042c3d0410000002d10020585600041181070000d008440a5a6888c41c0813039503031146d842044420708020b00144901c41c85441c0c0e0a80103111420010072803078442150780221505a071040301d0540c807407000035403a02400e0003403a1019011010320b60800c00d640d1a0411032900017000280310781000916010601c0c0654428100c07403c0280045444400780e141000d180b0594100400104000000084c01c1038814083d0340440c1e036022514081d110f28042c1071140c0c41a20900a0034001089030184540d070301c88901561180b18800000300c1d01c01d1071800d211040403070280500010032010080c0c03001003200380140940050307040c40d0004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 75167502 1250 75166252 75166271
    0xf12080108070b220b090a08031206010302090f131e020304110f0a1e09112a0a1403040f050105041d131a070e01030606200703050601080106030611070302030d 70
    0x1429864041484a014140400030455109a05c040e003103a101c04d40b90760441944032405245e8a0050480ba408280303284000158254441d07006008101c00c00b8140581d1000c134000000c035100ca608041448a603580c010802117108000100a4600c0d880ad2085240d810716403520100000c050b4070f514006e20201050310500d480e084036800090031040c460000400c1c03e101a1100c001407840303201c1016043c01d41c41595048450104c8000790142025900200000107a81c940100103640b0341c1598060303400280b01240600c0d010140d5144140003a40e075076410801ca407019501d0729000701c1e04206050100340301c040c0507940c02c900201181d4031045a56174070303590001c10304041d80074020b1035180e00e640d40c0b0385094004106e043c0200d01d540c841e0544c03002e194004500301c1e070035440348100054100c81451468401104011304030302410381524003103501c0e9100c540c90300c031080e030100350b2aa41d03800c0c040003406603c1c07040ca2242c0d000c501290703141040715140217507a400345121072041f081d610807a50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 75168752 1250 75167502 75167527
    0x402040e0c03060c0d0506091302041a061c0501080f0a0b100f08030d0605010302190507050f030a021506010201050c0a0e03070f0906060e0306090a0b10120f12080108070b 75
    0x4040120014200d50043c80e00312480c6200d6088800c0c0c52017040d09010101d01c5e18a400401070748500f911580c0b0002800450702048081d040c2d0340a440218600100802d0040d119540104070f4181034803498a440c40c411114142102d105134040c1d1302e5500180b201c8100444049507809540e9000300128445455040e051402c99030264002c400c02c684152000030710600c0480501203103c511442041859a00c0d001135041e8800e14100710300030b02406001d00d410034054006003d170b031405913086400112152515a1a6601504512015074440080d80c020280c3c001110350348007000788001e01081c00c11300c10841044c0242d00001c410320100464100300c5032801c006850040c4084500b00405c036644041c0c190050900d4018100003a40e502947c441d81d00340002c03414040c0a200c80204100c3d00b01303844084c048100540b804079003c040160000d407441d1004544900e060052440503811035251a140303543c1c003801000c7d141800901001005a0800880c18400f15251140120b0303aa90389a503c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 75170002 1250 75168752 75168763
    0x1020316110303040e0a05070e01050f0a030603020603090c120111030f0402030f10150803160b06010903060204091a09040b0601050c010f020c0c01141606090807050a05061015080402040e 82
    0x751905840041400141031413174a0b80b00b40511500700c410822a100c0c180102c03005040004c00301e01155080280d40314035a141c00080c040302c010743c580019455126400540780303a00581d910341c11684a280c1d90019490000c020000c184007000081021110003074148140c1c0c00003e100710540b4040000080075502c05122241800c1001c50030f48000041c1c0091981c000c0c0110424030380c1845201401060840703000085070311803082d1400144407119160b0302e100d86844010141410011107402c0040000c4060010300007910030080c3c0860201032104484035542d001c3c046007485081d60b0018040841e16030018241c119a00380f820340d580e031400d02d0300240900324038040c642c0030314800580840103410124010034580d000742d81c2c036107640000501001d058050b10b01050002a00c2e00c1e0280300254040d4442600c140c81010064100a0305032220b50030103400410503102034020780200a290341d6003036030740406400407201304d100c0804000001480000c00070b0009000b036a480400c481c4183c2d04100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 75171252 1250 75170002 75170033
    0x306040b060a020105040516030201141b070605090f1806040c020c030d110d050403050706030903021006060c110909030f03040c03021f1d06030610170a0e070e040201020316 76
    0x101652618420b500a0082c50203c8080d50103018990a04050101b9000f403030b401c59405a443d103095950080b5401c640b94000346a4407400011a508400c00070340902c200c8000341007546820b51100301ea44280107810b84003009031480791100c42031080d001c20880156640011090302d0004500200c034070180d1400107241b90f4181e0511403034484a402d107502035503000e402e04904e0192100114699020b5880d40207900000302144c10040003440214480e902000d9101c1c040c0c4111b40582106000c60801c0b80d00c2c40e0001c0380010b8a8103410014000f20142810907a00d01340d41402107450050b090640364050781c3c070490025030b000404182800610021280a10380040c51369444004200e0170700210001d002e50768000c5003400c80c1c8844110b00e06104100c1c0300201520395491a034030041040100c0140007019024000028a120308980d8103941042c40307115002c00003da80c02440348990b03d000010740c403281c05540d8400401005036404000d842a8038551440605c801080b46004c2502d03000012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 75172502 1250 75171252 75171259
    0x30507020111040b0403140a02010f0c050c0405010b04140a08250302030d0e33091305090c190f030803250206040b0915060910090f090309050603011202060306040b 72
    0x20f0049200315034100140110b0b03101e445418910240703014140c0d210304a0150103800719062003410056a03005801020002d03200d1000d6038481a10701d0005800c465003a084440c4005011405014400761301c0720100e40c1d0b80c0100c0750403840380d180040c55030380c3e4000703111060610740340401030009101c400a1003601455005058500d0b2080e09400103000c10082d800092142403111020031b41840e6248588140c0320b001c40140600c0ba10103681c107005030744001c101e150460a84041c080340201c441c4240c5020f90032010107040d0406041042142403000c901c00d000c8141c41c1e10381c00708104036039400080b0480f648007030704a03140d9403400040790715086608400c0c02503011014003002c445a0104066206a2040160100f80e883c0d03e040c075540c4031410202d00b5a00307050a00403400e5441c012450981c00701e0f910b4100c1c0031b0251164140e8050301e1064030101e07051600c0314100c0c0209a0444050b0024142c10388000e4115894280032011500c402800a80140c10010108600fa26590007a821128019 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 75173752 1250 75172502 75172507
    0x60e0102040f0305030306100908030d020f1207170a0c0813020307050303070503090a151d241902011521060603031d040c021002030901090506131202060105060a030507020111 77
    0x20705000307171250b0044803d03c0c0f0580500125522032400f41503c042582c001800a41c14032171040036401c000e44c001c005034100c0000500403400d421200340f000c240300d1009640d5003519102301d026080c00c0850081c5c80354100b01d0400c0c1c0b040e50390984c09001c880d4001d00e103030306481ca201010f0000c039042904030741119400d0300000802d481441800801402d07070302d0040e204492844d503155101801440521140d500140b80308481404002c4186940c090714580182b051080c0040f82480030040d0b1049060203076001c0e40420600c0e502083e40c4048040c1c07421500081c02802d0f00510a01410a4980542c005c60071181c40045c0701364030201035803080b50307500090400c0704a4807820043c01d042a03480d401003440c40b040c8550000703800c05000d40c521601715a001400c3c02d41c801d80b40c02010350401421491299a80c044480203c0c0341040401d0299014800598007041141041c2d04500c035100240e206560055004000301d840f000100c403000010380ca4005019142e80710308a009d0f103004c008450062001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 75175002 1250 75173752 75173759
    0x1205090a06051f0e090d020102160f0c08160512030c060609070203070506010e0402030c0f13020c0a0c0b0a0909051302010c081603390209131406060901120f060e0102040f 75
    0x44513036010303011002c201c5d01001070240c4101d003030348980803060861014401c180b0000070504a924001c1e00d1042072003130300140d01d030301240e403401300400c030002c480d848850010001030502807486000d0442d4000036600d41031030850b6a540c0d80e000603180602514a04d00000e600a00c2842501e1100c0d80c00782c160b1718103503501c2032030b00c4040c0c0c420b441c2648a8012a08800054075002000102c0003002622110207103000411240081d040000c0c03c000500031f0303801c49000140c0c01b012080103400d4801507a07407112101d20009007011800e420104440d40f43c0070901403001414020520001d60910704181c4000702417505030400d00821915002e08090030741c102c410160408050502004034080c1000003c1b00354001803103189004890000c03905120b1100e60260424040c1e01d648440ba00845c80050b5099913500c85028580f8004104d0a4100c0002d100c11031403d640b80745d0051101803482200e0001580b070300031107606500380040c000c50340ca17030082010600c290155801460b80302052507034143d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 75176252 1250 75175002 75175019
    0x1403010e061f02120a020304030606030602031e0705040b0901030b120708100b01080406090809030a060e0c0904050c010c0203070512010e010b060309100c09051c031205090a06051f 79
    0x1007a900035200d060149465203078490307644850080710100c0d5005064031140b540c284e000550000c480e0b501180810880031000c61180c0c051200198800d48006aa9251001c0b8517a20a10080c030004c1c0c2040c0ca110030300c407160f075108059070255146013101c90703580c060f40700040e001400005441c541101c1d000c040c05400950208a0314120b88007072050300d250701450308100080702c41c042da01c41c0c08922104085004500158400702c84a803040c20203501e40369030100081d240c0325400c00c04482064440c0b003400810b28003841f40722000a0b09a40b02e10040c01c20756602c940b0b5071414103040d4100510090174406541e4100002002004094600c0c0c1200d1035076011035028049000720b20420b5030a2a0540c03085080c03c2044900c5004c0403806001c4100c0218403c20142c0503c0d44410200514500003003025920f801544120328079141890b4800d0b602da18002d0143e507401250358003807900d4a8104007482802244000e145a842440051582c3c3d0300d031100c1c10001c61500e584e951720343c21200041303420300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 75177502 1250 75176252 75176279
    0x130303030f0b0402090a2702040e041103060403090506030402031c1107051207060804080904060f090507020109112e0203070c0b0705150a1b02010f0c080108030307050a140301 77
    0x722481080c090501d0a8090006030b2103081251a04040e40d14010001041240e04140d82000500151600410302a2501081e42c0241d0000c2908060200501040145000d6008094642640079080601c3e058401a246181c4c51103103d010340d80c0000014119541406212040345000c01c8020559a440a00612044140707000c1882d07403061000c081900d180c0f21901440b1031104000500d1400e00b42041140c001c00042c20850b4128400d10405105079214021b41024081480c1c1d01d00e49280703840400d40a41e02c02501c44401d59141045c0750012510610b40c440c030404054500121845400d807420a80141c8800034108000940c01650b101550100c01440058050f8588600c0303d511a00311611611400b04003d101703030b00c0b400c520340f44042c0104110341c0c8048050400182c0003107000d02003000c010950a0440180d41d50394204080010130710038195100700b81c1c034048680f03606100b548e60f92840040c0c43c0d44d0034418046000140d0500c281c490005d000744881c3c0003512035a49944414200f13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 75178752 1250 75177502 75177521
    0x31309150801090b16020f0118030f081603020c0309061314120c041a091008060a0c14070c050604090204050301061a030402010809160b090415030203030409050c13030303 75
    0x2820300d6100064600414050590102d0304000740369590f4403003100000d56010080020015806520600d032445c92083c400c21254015490010360410280e150003000d580b4031000920600a4682c1403042813081100c1405a4038850b0070300682d5610800b2b4075601d14025500712542c81100001d0400701400707002c0c0c4100480d0481ca01c2082491640004c004114083d445e881869a00c1010507501501d001d0300300841050b0000d2107940d62003000780209407440c40440b00c40c25280a413600c00c2040300d20070000142d10845210742003040f188003a10007000c8440700201402c40354004250350007848a10600c007401000020642c82c0d0715a41d507051000603400901c90303540710b54030b0310318001a04140f0301e03540d205090303003001c1d480e02d1542c0b580c1c019a03007014041c0000203035110702400080001f6082001d400a403c122041c02d8035406194100702c141d0355a40780d01d08151142c001c080005860000c19103040e0303860040c02150035514003100000a0080c60200d100500065200106064141c0e024000c41c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 75179858 1106 75178752 75178781
    0xc1012060f15081618030807051c14070303090503040b160c050108040308010504020a02010e0f010e0106080c0607031b0618110a050312070314040312082a0309031309 73
    0x3e0f41c0002340115034a9100800781c42c444409500314034003130840c2d4030b00880c0c0702e601c2c140e1032441ca004000005082c90340341c0083c501004400d00c15a400713400c00303901c400d1f00e402e0015071848940e284408260340c0c500c04080c000c519948a0103450388280c1d010b8980700080d92030182884000d40c468205074085540e114149042c1d074105100182c481c02202d0004110780c81c240f403113682110000c2d0721084681c2d1003809420300544440c402c0d41d1a943d01410f103044000d03410403071400d000702602801009186804180c10320b4561b81401c50780042d01804001c0009a451828001c0c60005409569856800740c2c17603070f50601d0b407107200400c8840c3c800d141c500d0300920010242040c9402640045800910384c500e0b214005078002506940240d407004000e0142c0022012181e10200c5101054000080040001c0703007a00200700300e4400c9403403c02d9540d82d8556510180e4020410f000c2c01c03164 = true := by decide +kernel

theorem cover : BRFrame.Cov 75000002 75179858 := by
  have h0 := BRFrame.cov_init 75000002
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75000002 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 75000002 ≤ n) (h2 : n < 75179858) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
