-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4751
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:50.827697+00:00
-- url     : https://prove2.me/submissions/8d914b22-3805-4851-a6a1-95baa8940bcd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 854316546 ≤ n < 854496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 854317796 1250 854316546 854316553
    0xa1a0609280306050121061a04020d291c050111070318063609050408070312140f0907030803010f09110906030f0a15060f020c0f010f0507060e0d020c0102 68
    0x2221000e652850f900d103040211b50107544485100840c42c16404800f40e071060401501c48812480003007010703608226142160b01d541e0301442c000020b241c3d0120041e0305010724220311000019800a00d04400c120034403d0003180110044041240940c03144a0034990f6404041c0c5660203450010b014442803800c00314042d240302000601d02e801003600344003906d0001070043e2072074860b0307036900407000300c450a80308151b115101c0000c0d1401c80707110300d83c0030314000c814040d070303e2445040c06484000c0f041c0c0f0303040300b161a140100c1e44003044143c020340c000d071100703107000c201d42c80d10709000b460a83ca03500040c142d02000000021100c9090390504211840b548007400301c010700035454140346c011204020303008402000040d03445580d03104102d40c4003402c000c0005134425030001034020b03451260400c81c049485580203204068041100400300042198081d4241881e800003c04c0020792400001c1403000114916042003500d0704000030151141045601013201450025907551112401c1805800b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 854319046 1250 854317796 854317799
    0xd020d020403230c01050d09081b0a0b0f220201051b07050307080708030301150c080c0309090f1e0703230610080907300b0703050a1a06092803060501 66
    0x50004c81e580c130602a050715403a050010b01410350740a481020012112841c04001c50f01e41a0740f4401e0b10340b07950500300001c00c0c070740c1400c3c40e03c0617a54801404400c5150601030030030040960380360441c07403a1014101d50413040c00d0345c1d20058079280100d94100803130429044c4621014200050303079400b12101102121003c0755614411500c0d11410702030464160400c10042c05004028904c80c91403074a1890113031840e072090349406031103400001820f00143c20006020301c4520b00710740020b82001c040459501d0030b0910280140c0c41c201210060800300500100107140d6501a40c84005a0404980403641507041d44d08605000003044551600c540a21240894040e2144044902c200c5c80500100b412600380079996107512120001c070b0f002402c4090b042c1049501c3c414110001501c1198940f645091401001c0e0540d08003c02c43c4e641c1d2864520381c000b012000310b1b0400d0408406035102d81e6140c0080d40400c4001e0010310f8241013071441002d26880e01002001108201c90180e802000b482c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 854320296 1250 854319046 854319113
    0x330301051510050a0203090904020118080a03080121141905061e0402131e020a02030c060610050703140405091306050a0515010509030a0605070306170c030703080d020d020403 77
    0xc4c0102900f00380141c0c8140600c003e41e050034095941c01500504021000c0c41c1c8443c80c1a40d2200140c0081400f9009400c1240400d074200e4141400340a5a41a150120300e03c03050240d4050f245000180c2051a007020501c1215010300415241850009244001d0081c3d400c1040e66908143d6075845145612050300c0542c250740d402c000e000d29030040609025102d000400e201804068140c0c2c1c2846940c0781c0c2d03412100795103200030201401a9005103455900c0c2038030560804000408071800748000f03d20b2000790540c80f904031103030b003541400c10710030100103841c0024250066412058200c0101c9050111035441e110014030003e11501c01801180d440b0000c11040e2601074502c602c0b500004503461030258003803c00f03000d0307054000e41111400c00284e00d460041d12010f5a0035008a81d42d094140306003d40b40604d40c51160040008107003403140480402d584e2401440042c0084a010a03080c0400640d5011280e0070103d030b44055442c0e0b0740b2030416650303900000810340800001203201a002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 854321546 1250 854320296 854320307
    0x12080f1804063209060607050708010216061d0627030a030501030b0106050705030304060e24161e140d0509010b0103050f13120306050a15090e330301051510 69
    0x10403c007a02000b115100c002c00d00c01c490b000440200d0b02e42c01400c00103d001c0c142480038200c140b841c0d8160562210346030070441d0860705101a0200928041503545032401c00020700c190308683c14003032901c0c04e807140b44001140300720704040c450414000000e41e00181c5516030040342c10f0328003a002a40d07050340d80f410181c41e503120301710005010750000d10004010441075072040d135a0600341d40a650340e00d0205010011100c00082080142c08203030341c184517601140807041e23510300e5141c1c03c0070803545061038222540c0310004800301041200489201101e288000c1c2911010000740710240418100b07440410301800303000000c2030002f4130308000a04449040045240518890b00845035031405546451b1080301604007141c09254807158005190b4441c81d0340c003001091080800d10703105502c03e400a000c002550710030404440304109001d10384021b189410003c0180e094910f003e510a0102d0b0100e8840a046080d40742d441c000400881c491195002000b0740c100300c844409200c0d0f001000d848 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 854322796 1250 854321546 854321639
    0xd113006090105090f0d03110f03094207090302030a0503030f100608060f0402041e05150405010212030402030a0c06030c020f0304140607020f0901030f060612080f180406 75
    0x5c2d10790004140d1280507000c1e911144201314050343c200d20308907441e81c410b6020340c8140c0308503046521542d0741a4001348180c0700408540c1c800c0c042d10035550500d1f034002c01006440344d04a034800070b40e07001140c0a00c0c01703a00703c64002c59011b415103070642c03a039040c1251650001c880d00401c5600004c0041c4001d81030021100239a241600e520756643c42d20014888020030740c1c000940c0040d420440401e42010021083c0100f9282c80d080c520041e00b801700740045c82c1080d0a29950110f4180010300603a80c020860103803202501c034140d9203c0e0345600000f1b2406040070005071203681c016402080c85581a0465111405c098084803005e511403186580c0e00e100d10b01c02d040c203488021342039080b90310f4040d0060010078001441e00c001b000343c85001801005080c2c1c0200c03141403000703103040200002400ba04004103072030300342d5500c0c0340d04545035904980f0404420036211030002031500101074804091031940c281c090000c1101c4e0340c4410030000203060b424400003866480454ee15003000c0911078441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 854324046 1250 854322796 854322823
    0x1210061508010b0c0133170705120102120a05070f0207141c06140403081609060503070513030803100801110405060c070905190b0d11300609010509 65
    0x8009a292107501a07084c2c102440710040c554075112903003001e0310591265003d04034141000552204060000744100c04550b100e03240c0b00d40c141400c08040364001c2135200440d1425941d40d400d0002700c50000c0e00a11802820050072183e90003449035088056100071b10440d10343c0c03036450984044e0300c0f0599550361684210712404200d010344d0840341c20152541603182d07000741f01240e100c540c2650342c0003d0701d20b010803003032407481e252003004140340d402600141c02013541403d110704440322210003440e1110a0043c3c600b884800400b10360386a105c0c4040300c00e2101410580340d411034a901d0003815641c4159074030803444003040f00100d044c1c44180300f6607400359200741100345410300c3c00d018001c00d500056002900f030300a4240008800b00c09009081c418404401c441410540d00315046084540c81c112140c014800340040f00c00103030030190700d03122041048035100c1c41e4003c3c442840301044440030030030005a10760000e0305261140010501c0c02006000300078000baa823614080e50380c41d0b4003940300340d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 854325296 1250 854324046 854324057
    0x10e011d041a03010603050d0f11060c0a200c0108070201060530060106021011040e0703050415020c06090c040b06070312060b0f0c0d0905010c0b0c0912100615 70
    0x168860314003a40000403944400808405019480000901710342e00d81e40f0596485d00b01c0c1744121400da62014800b6924400ea040c20b0705001601d844241e82c0d02c400034140000a040000e0400000e40103030302402d000441c0e0342105001c0c0302107101541d11b07020307261991070105000e4030208000c2c0d030040c02120241c1d00b01901445030f41d5840c410000d0701140d8003070041300f08566034440441481d01172001d98040c1c0710302c0c0c00070700717505c118103004904442c003050075600101c80610003803006217480c02c41250000c4a916002c55a911142402c043c40040c404411807014400100388024030404aa2144074000ea0000d0320313a01414801031005403210400160341c403034000c20050000900448100103024200c500c00141c291300e6810030007a03940040b04200c070300d000109103210564000c001e02c1c4107041051401503621490702c00080d20301b1104e120001c04104102c00083c8c2c0c1c0c0071942c4280c48082030000d1031285000d1020300c3d02030b2a1000c92441040c0a804d205000c01d4880114145111000c00c3c1d0352013 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 854326546 1250 854325296 854325347
    0x31202031621022b110f031f0807030b0f0606030f040501021342050d11040603020306030d0504030f0b090c120303191a0d021809010902010e01 63
    0x882d000000c000c03403100b00c403401c1080d40003500041d202500455141203a141196034040c800110ba401c01034580340046410550703540480c5042c1802e4a034000034511500792a910f0f000d819521000c10384800c0d10130b2171701c0b1203c0062600e10014030342080740d0081c1e101000680700c260305c426001508460583c1c0048081020a05042c140d603102e42d170141c01040014100410000c1e034500030f00b0f0b5a031041d403101c0300e040380101000c1e0f0590b030025119400240b04580202807a0b04000315061907400a005103c40070890101d01e9049810139594201d042182541d516181c01000d0000d400c20b4400030b00902c02c05030944411406402200c0980360071030820030350b040055889940c0d00760000d0043c0c685008145005640f40c03118102c80c0c3c000404030015580302e02e8825804008454105502c4000034103148100d0f490032a5100c808160f1780080d54000d0f102da2180c0081021a254000b101d800e54810104101c182d00c07040d0b0207206114400d9035100c00005000c801184c180842d803090704403401010700c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 854327796 1250 854326546 854326591
    0x51902011803180e0a0615030911120123090c0604060c0222291e090a0b061306081006052b0f02120f0403022a0a1203120203 55
    0x11907800001031420780d950706075102c1200e00340080c001e4651170380f40c5031030304014407040a841c2d01c20711201030180390807c055003032500d034001652081103210340240111404000300103070a421804900401110b604007282498440102001044a0381d01450080958910702803604100b241e0403640107680709070701c40030036400300021010342c61911f01303070b80000c81c054a0007c18a4011048049d1040c1e8400620901c195000840310700c0c00901188555a201700001c040302d0410440702c5421401c0d1781000c4950b9400c201c017001044150380f1181d1152000c81e40011000c000351090303041c0d9405940b0310480340c84900c0061040302c00c034011900415014040b050039402100002c0440c01c0140100f03852404034169200e08843e4012488c011250300026030384c901510408002c0d82005901034a42c1c0740e484d0948001b51100e600b140512034078841002400d004441420300c000f00d8000050400f400e086e5599a81c07010034030501d0049000c00c1c0c0280600200707038034610907284100100b100d21050304a0581 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 854329046 1250 854327796 854327807
    0x106050d36060b10140d020405030f030c100b0d0f051f14060906012001090b0c0a030e0a114501080309060a110c10051902011803 57
    0x8040e41c540c1004448120001c90008054101104641d418841c00340d44030b003000d400352040c107810940142c1240891000d441c0c0d20040c04170309417551000094541d2013202441019100b1070740110361502c51021428150003012000300034856606c03080343d442c0030341038141c40140c0d080481c80c10341c0b1007007642c4c818010814502d003401d2800e2240b002d072a460348506900408074108980f04003980341c2d0b43c4040f151480011a17003541c01010490340c4412514003500001d101c5260089840114496070803a841c2c40102500b01600060344000c0914440c54400d04600464200f4014017000030304045c0c100307102400125403c40c080343c1040e50315010303c0b00b1405200314000446140081002866141e2681801030303000031f4808541e0034a861030b034000b514094001c002c8103800081c1540c008001282e200e0340d81030121101000705040c4045c1c0a401c030503d1500301000818000d4100c4030020780d080a80da80600102580041050200c1141850410407422107a0320300c480c0440400850321400840d0040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 854330296 1250 854329046 854329061
    0xd05030c010501061d0303070f0f080f0706050a05011d01050613090504110a0522050c0720031c051e09120706020d030203132004090b040c0e0106050d 66
    0x1502124544400030680e1400c54034242e0001c0009070305170980444245030b02040c0d05514000301e00540c01c0040d551509052100c80450040c003080b460202c94082000c124240e0324150800720000c1e440d048541441c0e030203031a04954001d8041d280c1070002c20103607140c1003840c1c09100100c80500e400e83c00d020a01c001a0301c10088445065824900081c0b10340042c01928812403141902c44107420340c07071040c049580c0701c80d005540308101720108603080d40a03403003810030840309000e000702c2c6030784031a01d090b0980e02c2a420082e01600f102c0c001c1c0e0018510f21181500120402e40449816204800c0f4030384040e0401e070008000103004010700e800300900301c09000c00d04242000e6444c500603014000600320303045254480036a0f000400c2c100803843d01401684000b1604c1c1c00d040d86940307000452425100040b1800500035140304054840c074080c3e9100f154400d20b4054400c03c8a1640350400d2085c8a4040340d044400701d02c00340b800b003405803070505124100d4406842d21810100310b00c1074a0082c1155 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 854331546 1250 854330296 854330303
    0x70c020f180708091c02030c1c050a0f03150306140603060601050d0e280b0903090a0605032a040801230f1506120106020c180109020d09050a03110d0309030206060d 72
    0x1e00e500d03400d400c000c1c17017200f10303607044290010350b81d03140c494801500b02031141d10010101d02909403605401d58012003202e001444070729141c8003282c0c0c00c1000781d00400c0c2c40c8084403600c2181500c040204902688004107140507411841c031540d4540b820142c5c5da120444185000841c244040e0940b100290001c8401116110a4840c00c030590070200d0b50070780b41021032180881d401c2503c1c000b80b084404080d500b2690920140d4070307112488001c40d0701c10f800c903c944401c000c0e002001605a50b407928012084040e80280a919682d09004001c0c003504140241c1003554606165036100716507a40e001c522402031348100300e405039506201c200480ae001805c20190110311880c88505076115001480301d03c0c50168a50095414050000c0c6411102024140030340e019801029448080c103441c58112580035101584d200300c2501c0401c05880540001000c0b8800e8182480c01c054020710aa4455055501150b00e5030342d41d090202c09860090780d02602503003141000c10098140301e401820311030b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 854332796 1250 854331546 854331553
    0xa0e0a05071e03140a0b0a05040321020d060b09030f21070534060806030a1e14030304021c110d0609050d171803040509040204090803070c020f18070809 67
    0x260790b1654032034084d84410f080480e070000c01ca410104400c40d0a15600500c003070f00100150f18050f0f801408038040e01a0300c4101d6121003803020040f8135548c0444048a459820a0110300e60300c44080d000740c1c0041c1c810b18424081c82224403800c0200084840101425074051400d044912070310301c8040d40a10002d0300e90780118500c507500c403928000c1c4140c0030009040c06140600c0820b013001100480c0f0307000141003010074401e200c4103580c0003441050702900f14200d009a06052000220880e128840c02050001015154a451000030021b144518000d44482c00005102042c03058402c05000c0e00414220b102e18100191b400c4c1315814800043c42220006850141ca4507040d1501800100e0b440000e0083d01078050350003041640d00750008000d40a51041d03d1007000c2403502c0380990301406000311180000070b0195903440c1c002a030003e810200ca03990f01e080c800300040030315510746004c2c1c1c020000c00701900034500b407503034065499028004004460b900e40c01021101c490010f0440c800034031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 854334046 1250 854332796 854332799
    0xa1502071d0604060b1903151802030405010b04090203120c0307170c0c150d110f030c1918060f12020408030705010f06030f031b1502030a0e0a05071e 66
    0x4aa419080c00084414071250079180c408108000d030303a503d0700200c203100707410b0000a0f90200034915640d4560700303d040205020311105c51840c41001507610101100c8249058841c810b1040d900075402180603800a1021605403000e00042c0c0c1c00a07900250941d2007410a6081550f03030b00054444004c498040e130b0702e06800d54491040005020001d006000d43c0059070040c00304041140d880e040500b581d0010315405010746030340441c01100b1441600c40e40b10342e0810516515034049454522076610890f4903400c003540080c029030004a240307084111003e054940301402050001101469000004241c0e030070704c4400c070f440030920780140c01401000c1c80360003034450031400a803020300801300c002c6441d098103007406400e4445240b5074400365458040248082929181c1d42420180c1500f084c2d180d4180004000c440942d4003100645450000903960788010142d800442c00341d070000c24248003108812880d1520760032864030003449584032840401000e80b4144649508071303940000301366081d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 854335296 1250 854334046 854334059
    0x20d0311010c030f140c091519030902030f0c092212030f0b091003062d091a090706080a180f2d06020d0e01090b1902090a150207 57
    0x441e41c04402d0360100751140c006900101061244050a841c2d101ca0100282001c440011280c0b190f52006d03405503407840c1580c075485003ea401c64001e0303200780862701041c803001c0d14014000c1c886070030100e119002c0c280d15801c2c080f100041c14102c4a50040c624911a11041009415180400d400000c01100f0b07400030404a0790004400b001041a61004607080d81021040300403222058102032082c1c00040901098845910000c0306407544500c002503000010144150f6400e80031080c0d400c5051009000007102c4150341259525620606035007501c8032015041030b03443d030011174540500d0350150030b04000c09031059804ca0741000c14604000303004100b408003a0894a40444165444d00020040301c041000032a0612200c400c1e0f0704003112003003e00e1851948800003c840a0710f069004254130048004651144400c0303200e40300204000d441500d0312030100b080c200d8044904251108000504114500849003080d00c0102040c5001e41410f1502000480541c011001c501c102070021441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 854336546 1250 854335296 854335301
    0x40203070e210f07121b170a03030c0c03020606090417040e060f0102030906030c03100f150f02010e15040f0b24010905010c02010e0310020a0c0b0603010c050403020d031101 76
    0x50300c802001400c1d512000b00c00c01881c281504112049540c01514100f007500e05000f100503032582d1081c0c041c051654612021122044c0341d42100b40d0550380020417540f2524000b43c0e04030010320a4030f080c0f12881c94684140ca00200342440507015030484000511286405150706601a2052500040c1c01400045a0556821540045c50400b4548091110500d00109100c1121100348000c618090f000c4000c01e900c3d010140c2200060a808004503885802010b50103014144556100400e070307039540e03101d0002402c01010070002c2616428410310292041c0200d12240c150040101820008200d21f40e042c03403802041514004165221000002d004502c842d005409101030828660038040c640726050700c0d130020290601c1180d020401040e42c0128127040e40a4090820a51028484012a040920304002c0300e000500c0040d0901c0040d0f04143c2c4440b00c00e0140a1200013540c82d0302c2031500b02e41281500102141d0705102c10001441c0c1402440e003114403a1804042e48044040740c03d00703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 854337796 1250 854336546 854336569
    0x1e02040912170f01060c0b1503120304021c050601260a111c0b0c030a090b010305010507180e011413110405130c0807030c030207020306011d06010801030b06040203070e 74
    0x5665002940b1a40010381d080d64208251030000c06107940b6282d000340282407003c000411070301c03003000004c1503040d48040b0241c1c41000a01600c0c8500c81c40544007099078401c5404900c204101407001d281094a5030340054404c2d0302200500990b42070640d030000e4844040d00b440c60000b000c0b1a4800c0790081400600605440341010503d1084060100a424070070500d01c44202009403604201051b00740710303000c0e00040403c8080b5507036291521503101401e03c80402805000c1550000820001c0540c0040c0c030561031075071905010002d001195482da0540d02c1440c0700b044018005102c41000240040003d042c006c2c10080c075800c0081040e000d8030300d8006001d60181012034100228200b440302e80c00810741c2c1d540100614150980c0c040d141d400c024002c0410140c1e10540c1c080c80c607020780c1c100d85220b90010200c40359507940320b4201c540003401d9205410005803110114981d54007903540c01d8141e0354817641100305952080e040c40000d4000500840821121144411080d20f80c13191110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 854339046 1250 854337796 854337833
    0x31b090504050c0f300c010804030504060f120507080106020601120b060907030213080f16050916030e03130906050d030206070810031a060108010515040b130504060f08060606071e020409 82
    0x1e41103441700c5038950810f08410502814007644504000001c0d034044122800d031031050500001581d035500d402c482c0840805040030781c172480c010602100b650443c420034102d4107650708403040d036038076081c0c3c00109180c0c03800010080c40441c808a003075450f0036200c05601040d6458018100300c040c0020140394016031384030003c00d03081000020321210741489840c0004e80c1a8040b0a056072503c00400d40280c0020304e0b081e9070300803a0381403005a5200b030700701c1c80440380d6801c11240c80320050001540141950f12600341c3c1207140410004040c10f000d00040708180d0150040c00d610f5a4400090b20880b200521821b0404003002e0040300240c1d00400c0c0894030083e261f4080e445240c0a40003511100e010f0308818814222742e00140c0300d0b07803502412202550420304030b4548a45026800620b101010b80243d0f510a0908101154402e07400c1079040445005100f150103030740701c4d0010300009208100018041208200394024000000348080c41e04034405040015500c405442d0040e02415904024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 854340296 1250 854339046 854339119
    0xd081302031204030b0106090f05090405010b030319121116030c080403030c060b12060105060906130806190506090c0c1c120e07120308100e01031b090504050c0f 71
    0x5205105e5040451070142150307003800800682071525501e1b000c0000d00c1424030400190700000c04000c004c0d0801d0025400150450380c5a0801d180c2c042442042a81d00d0380000d0104161610050b215014582e01821b0454485190080c0b013400b0707149040003004150244808e4040203400208042c0007000254000d0381c070404401760b146420f030280c0d4881100c3c0791086401d94006d005416010640c2411100d040304d24070365440403030b408556a0f0045403010064100c06e0800050f030f0060114241e44115521002c00030b440420a81c0c0034100c8800351000d90300141810009149924408002c102440703503d000c45606c1e04601c00f4414454006482031800980141c80800c91100300f4013990602c80d4102c00600445414410b00c80c00d1244070340000382c00c0040c0000424070100048000c0000350080429441c083d40c1c681c01c108803016003054000c0380001c0030303002c0011079084030b104483c050f41d07221003d400218000c1e02002180015040c2c416400558102c0041c0c404801240311900030407000d042 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 854341546 1250 854340296 854340299
    0xb0a0302090a150e2202030c030a0b2b030917070f06020318040b0f0d0f03020c01030605061b0c0d050f010b030d091a0f0703170709080d081302031204 66
    0x280030050b20240c2c04003600c00002c0144510309030704103d80b62480c00c0256482c0e01541202c0307030071043c40f88070448012103541c4008148541d00764001d000b14032400200e041404540380c088140021a2500034101c961120750300d11503001407c41c01190b628440c000c0c030b0613220035600c4004500d802001c9180d550304952008034200003c0222080c540020b102a0010310b0524624064068028500f0108948295903540c60301d030701035072100c03c8840501c5018009200d0fc160341c6c50306101541542c01305401611400700031102549c1b0078018501501d40140800f800c01000c41900031a5040c400061140c40c003d00701f102c0d03a07031380714800000a064003d0000f41200c40c42e1440300c42c21681110341c521300a4001c0f8644240d482e41042c104e03002c4820340c64071084405a00c9414103414010b10f400314002100c00101c850516a100043c1100c288241e0f400c00304a44030302400f03890200c494890a4415000382e0302c101c2c3c019000f40340c0203601191000c0d40300e080e4601603002034200403d644c000c2070b000f00049030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 854342796 1250 854341546 854341549
    0x506060d061514030702030a030e0a05030a080a1a0f0118051f2a24050c210f1807050a0618060c020310050408070b0c0a2d14040b0a030209 61
    0x140401c083e4145442a140d4101503800035224420780316290245529052040449071003084148030554200c0c2c142c039260058044024000b850986207140c00d1400d00684650390360b4524014007050320001d00b0600d0308409a0015034070000356001c00900404100b80005258031200e000e03020080d4400d4052a0104200c14043c1500060003003012004c2004c4141d1070304010304aa00c1e00c04140c0001443c244c5400e40451511000182600240d0b800c0c202010f000450070b24202030710a8888400f10103495600c04200d00b003001204403403035440e0410180c04202e4020940002040c801c1500d025641d505840d0001b095141000d64403540001d507646c02c1408007401c14503414000b400030b41c0740504c1c5c4500b003900080d0f80c9015402183c00c51554070f4004c40e080100800c00c07601c1ca15070044074078140d450b02c0d013804110ba8010700075000214491042d81c0c41d003050021100c0d000500083c031b2002c0e17964500c00046444040c910300407030801e4030412011074401b4408010b821441c00b0b580d0b0269445a0200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 854344046 1250 854342796 854342807
    0x9050106060f02060603070b07050f10020310090905100b0d0203010e0c01081308033402010b0306010503010207210c0b041419080a03051f0303090801050f01050d060506060d0615 78
    0x149403000f150096028030003143c0d8049500d000301e030500c0c0500c9403074000c1410890b08141e11200200c02038403c40280940043c4540c01031442001e400150b00c1c0001e5581c62070200b51101105e00a045803c11140d10030f01d246298040588000c0c003424004203100c030350b80071908480c90110420600e511400d44920150303403251a859121b405004035000310341042d84c2d90002c0d400040d003200b42d486401d000c000401c078405000c49421383c8042c00b81601c6c0081c0087c019000707201440819000340101d900110322403c05000702d408555100b0125106407503102040080c041201d0103110030040b050800d803021074081d404840c005c90040e1002c00c3d40300141c52b00c9500e02044d00708540200300900e8410341c040307824502524031004850401081710340c1c40f090148c0d490800c10702c0e03002064140311030110a0680c0507030018261419100201310710703110b80c0c0384403071060001d201d0103078421007482c1c0320790002c1d40941001d90810400381400d8245450700030700ca010340b001c5030010301c1040000c0210f0b414865000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 854345296 1250 854344046 854344067
    0xd02040f08030a05120c16080703170907030227100e0a090209190e07080a14010501030c1a13121a09030405040e0316030e0306070e01080a18060905010606 68
    0x107900852a01d4100c410280084c02500d04845003507544c000020b02090f00b042c1100c2c50310364a0782c078000300700c0c10310700d8040e8003a00088416000941a040da648091441007046409141d100c402401c6207840e41e802c0209400503d004101e41041e0500501107080f400341ea124020340e00000c2440000d41410110716040b00000c051030116410690050056164441d100750030081d100c0c0c000143e0544c1c0034031840a001c41c0c2007844102d129801002900b2140032880360f2a1500c01c01d0528019000010080d007a2442800064882d072000c01003001030074161211f6000d591100c051050601c56091350820140081da4060843e5042d00e0b06000c04000c45045d06007501819500150401d0600c0d00d072050340c0740124003c0c070340100e613500e10700802503c01708150b0303c00300e108844c4842c140c1c00c00d1400800344100321381400d0192003000046480355003d40c0c0050300c05501a5074124450b17035200c901e04040c212103c181e012260001c83d0660101c1c103a03025180340caa00a1001040413880e0843c01403c802d030300d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 854346546 1250 854345296 854345309
    0x2710031401110a11010b2206050f030601060302070c0807080304180903080115020307080d140c070506150607080a0903030905010e0604030b040515160e040203091f110d02040f 77
    0x51204002d00c0c6900402075580f903101c1c918020b032000301c541e6551401011052078555010032600e600d4003050150005041d00001200741c00c0c001d1aa0701c0007031229001c009620a98140c01032070051001c0c0d807103680074103a01c070f0040c40b443c00025a15130407075080c030ba641d810092058000207818080c070590a0445185040b490700104000c1c131464600408110701070158528085000031003c1d0b45510802c00e4540300794108115030f03668039035064800003c0c08108a100851001000054028013406040c0d402c1c480e0440d0141c50180e407400316082a52940100c8564012428801e18001c9400103000d0112010b4540724510440d0031030501070300071202c90748064108a5181100e610a884500a9504a81d031102c00070b8003545a03850454104240447e00d203480c19004002c20000c00d12003034041d4031407011a181c0c2c0a600d440982804141e01c03080703404410319880302082165031400001d030725050791060500080c0c580441500c00805034000e600700d45030386802040901071980707009807580c02400c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 854347796 1250 854346546 854346551
    0xc0903070b0412060c030f060914060306010605160512030c12060a0614070c0b030910051b090f0f030609010e060c0a171302150c1b0108062710031401 66
    0x18060f0002074040300b44000418960f1100092680140207070000854158202000d2041d5602c584a400007402001c07090f07642c40c881000443d03094100071401c203050314000d075607035480c01c0100e01c8885020544940101d46c0791150340e607440e55201b0000044d40c000e800030502c5998443c0000c104200c1c040c03000d4843c5201d43e101010800010350410480403d101070f458115071070f074000e410032041000303490340076480d03040c0300000300040c0130780c00314034604444c1c400c10003003100e40c541d0010f2040c4050082c07041001d4100400540c949481e0600010000c03200042182c0240ca00341404242060002c1e200401070769143d55480d54a16002d000030b43d400300324102100d0502c0180c0000800ca00320b212464011682d08002040d2466218641e04c001c1030f40141c0800b9020300c15010309103059000720740e0080240504803050201c0c5c41a0008210b001005a4400f801500d1700f0f810050b040e800c5096007100200c0703501944400c0c00c01508020b200f982421001d6401900d9414141e480803a500100c150b582d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 854349046 1250 854347796 854347799
    0x120506060d0903050c1b0901080a0c091a04090302030309010b0d021e1203040602060105091e0705092e11030c03030a0c050d0e0d0315180f140c0903070b04 68
    0x1256041600c010403000d0307034041404080780c207041d5503510518107004041c1c007600344821000c000c41000e1010a0b4400d44481105070303a01d0300c04503107480c41340030020801b82022000f0045404903411010394070041140e1181d030f401d4540300050480c0c020340382c2100540c00200400c05600402c0c440c1680c80d6005488d907031481003060f40010440c03050801003c00c5030550000c0281a9105d6030140828000702d003044940d502e4484070043d50b60b20091203030b10b1040d860200001c0030140e00e42c0c102030301e00e81c0300000242d5907100d4880542d02a000790025982201203a07c0ca0300c01ca101a4481d4000714030f400311280c036160440c0e04001d03c08601a51140c80c0c950003044a0800c484001080300e60256041400081d91807060300c04403241e1149200014064bc00c2001c030120400c00030502115aa8441e01d04105a947c0f40d101d00c1075500d410b218000003c1c50020847c001164a504038580c002c8000d8000540d9010175100d40c08404070a440c1c03541c0c1200042000e1209045c1005003a002e004007640840c10036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 854350296 1250 854349046 854349049
    0x10b0f01020c04050714040b07050607050a0c020f010e2d010305160c030203070b0106080a06060207050d0605040212030f04080f0303010f05100917030c0c04050c0403080f04032001120506 82
    0xa01c0381c80380e003d0003140c1c1c0f080091070b824030500c0702500c80303403010041c240e8880d540c1c000a40c898102010584030750046101151446000310304a4211201d41d407213560001610f0307020000300404407942c2606002c005050201559640b1a000041c90320000c10801510f00101498400e411905011414103250109001d0840780d00709003071011006d1468008900d1140746000c17030460007080703001801285074200108103550860440da125094107101044160398070308041b41e07192000d00c5240c1c0c101210385030360300200b001504201d51250001e0041210314250526a628662098100170050340e0080703030600c20380e00240400d00e2103170b101c400290b095504001c10541000e09910a981c0f00fa085812000141ea00481448000340a130081c0620700790701e9407034129101d912010303850425001e41140654145494400c0d01e00511103946c1060030b0038151380c0e808440741c1c003031140340c0c0305000d00780000000540102400d50303500110300d581100314560400050075403080c40080e032003201e09003810412176 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 854351546 1250 854350296 854350303
    0x1120b090c01080c131a090907093f05160e010b1b2508190803010b0304050a050f03210402030c010f1b0f030906090b0304150612060b03010b0f0102 65
    0x761913804140ea95040400071000004d500798048104024103102828840403444007406c03500c2c10550f43ca444030f69808004441d821800d0141071a60a00d040d10204d1060500034002038002e00744241124078030382c0844800c020100d0010448403540f155026501000c0c0702030070a8010400215110220350401580d14030078040c90702c00d483e46440d400e4000320009410803840990840c0440784c1d00c400c1c0c0d4040c500c58046002400381c0000751045501d500c0382406084007224600790448202800c50342410021a01c0e5400607009031802e00c21943c123500812018885050a0710180008658400e281c0003810141003500070362140900c100d038100000340e100845c80200341102482c3c0141c02809042c2c054407115507030b1066050007103041e4401c00402c2000c104189210780291a020081d03540d401003100c000c04180a1800720079001c0c03002ca000113480a20240100c0d000400c080781701c40d1941d0910405440e40315046c0e0311310b41c0380d1040500a080038440c00190300c2058a40014412071040043d40c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 854352796 1250 854351546 854351551
    0x8011d07140607150507031a0a090b1f03020309060601030204062129180405072106020a02030901110102040f0513021b030a0906091a13090501120b090c0108 69
    0x81d088000c0ca00340030035503030384048800380c651190203650500b0040840e900107000444481020a20b400d0340d042990000c0500150104001049049858100346044002d40340352618140c001d003261b6a401c00c88072071780f02e4000181d41d55540040c1c513460700c00519880c0000c058490b60600d8810001031041c50743c01a42c128a0700c481400c54403403050601c0d681801016034516412404202c8901b2642588001d41c000c80c0d5500110342411741d01021904800121009482c004c1c52070b07010080401c100d042c80c51990b80540001102e02c4450717011521400141c0c1e2180d85464010b0f00000740365205580c01040c0c090703c90807144000c5080c40c1c00c1503000c00442c210f9008151003141d40c82220040e1207030b43c1d01220700d200082c0c042e010441c08518451030303982c0c008900c003501040c03107048003103a000d10559042c0210f071141850030304c01d00008e00010815030b121440700b5000c81010180800c88000c01d0150a008042c070b143c4840d501c102c01c0c246441270312006028000a5004146511340e641e074010040ca4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 854354046 1250 854352796 854352809
    0x3130509060d0803060d0c080d120e19030309061406011704200a1208070201090b0f07080c011409030c07061b112412131515080703060608011d07 64
    0x213503a44c40b244005091017589980c007c0c401581c8100208911030040340e41444002c140c5c4800d482d050340d441c903050544400c4401790310300d0b6002a03440700c1c1807480c0c554000b40c500c0c024240064203400300e0b204c41050f24204c0b903400780b80314054414082d4a581c0580f40c00e00c40790440755a88100e0416a5544800e03030a620424192900031600c5070100c1c0d0b03111494107000348280042a5040c2e0303414a070003200b0343c100850a034041750320208001040c4281208807070034118502d0b2400c3c94202299209030880d04441d41c030444940da100143c1d2015071002c401d41d030007049214011521400714a20141c901001074000d030b0100704070720320740410346254400840c580076803041490410098000128104400341898002c02e82190100404100e441500030446151103000300006580c503044c01ca8030303400d2140d80081140c040c08070300540c0900325034052003000a030030344e0300b94050341e8a00b0240d1410805400a0f81c0b80c03aa41c60042100240912600d03c003c49004055030145261100f09500e0344c070140b0451 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 854355296 1250 854354046 854354063
    0x8090d0f05040e180c03030f0a03050c0706020c101d0616110d05040f050907050a08150607060b0a060906020304030318090207030f02070e0c2203060504030203130509060d 75
    0xc04031280148252406460305059202c2c1502e0005910302c1c00d107081c0704100c0414000e40072458418180030040f101c80035038051146143c00c0c01020218010400201189036510040c840d840008419000400208660000034001c0300c010000340012262440407429400000310011482c030000405d01541c407030010750880c01c0400088005607090441c1c40e00c0102d840c007501c2c00c1c851a040e040340c007a105940040720304142050f10f0b00e05005116400703890302c0c40405c405100802c7c115201c3c1101c16030010f568091040d03101b100da000700d0115041070004552660301e624690a050921010081c0240030614000790550302c2e101c00a034581c4140c1c000070703042140541c5030501580d210b022a6000748000c080455980d405410018880540c1c4002c400c01400744034400200400c4d1010040d014100320140680382021000f003084108401103582005d480000c00c0000111f03440340701c0c66210740e00030f0300a0360359403d26031546081e001c0a5048544034520b10700c10701170310307403070b0b50b85404070032503105418 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 854356546 1250 854355296 854355317
    0x6050c0118031d060f0f0d09080310030b0f060a21021c06051807091a090705030f0f13031d030d0f09080604080901030908040906140f0108090d 63
    0x528050060314150604107400e41d8100030402d0780c044565004015684081050902c80000b0020380348508001880c00500901c04d115070f0b12500001001028000c40340041e455503070307030384014042d042200e2a0b094001d6420b01001400b0408100e2a0b000307184042c0c404851602d000060700090060150361490889280c046810105032002000003d40003085500d14200c05201d00d080800205812102e170740c20980469022040704600c404503191400c080c1c0355031750074005854000d100d5040503c0034101c40320752082d00781d201c007002c1c14000c044ad6901d095403464500503411101e20f025000c0e03082e00d03007208100070800300a000c080503c1e69051400491050b00c45c4814085e040590f09440c1e27040c0a03c15248450941168205e07064100035156101540e680c0c41c0803d4440320704480240040c507040099076070f10341c480e84c06001c09a2082d151981026180c00c6014119a026080440c58103602041f80980b80303824024006509402d02e00f500640c83e1038090281c48002c07500c3c00f00e0a214980b0300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 854357796 1250 854356546 854356567
    0x70c020109090204030b04060b0324060a18020d140103031407060b041406090a09051009060e1209130b0105071709060c0102070b010605040302013011090306150a0605 73
    0x44800400b9803860640d00c8035203d0611020861060307904403803035850040d00c2415424080f400c260aa541c86510300500c0742c8035204007665000090a070f0340d10005441001c519413080010320041000d4917180140c07501d610383c4402c02111040c3c000180b00014a000400001c0c0d4490325010350710740d00003ca15242d100c14a041c00203001883e030541d50190500400041d40c1600a43d030790300c900001c640242c0e030350b02d0300fa070390404840ca10180070b081074001812088019055030030189440348601c20015140c8041107034542807003c2402510580b28002800c6d0820340340880722080542c6404204102c11150000068510302c2492001008408d40b1030445107d103802506480c08030b40084c01c800d83d911400e58800d8000c0d413224008642907005000080b6400344510162015250b06840e840c40b610b460074ec17042031070b16034120064851120000743c901d05080b00c0c01a068040d40c0c0048490701c55200404140c20007800802e50394a08044000e280415034031540407208540d02d6052a83d902c441c0d600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 854359046 1250 854357796 854357807
    0x70f0605090a03060e0604020f0a06050702090c040e46090507180213080102041a160f0602071244091f0e07030b13020a0602060a0c030e06070c0201 65
    0x1800035140c140380817041c3c80101720201d1854171a501c02c0301e446074500388400801c40d01d80c03824003842000480910010300141404141c03607800903066905241096500d010102d10301c0001c841c0154161403411000d03107150110140072255038085000303902034242c0b0181110024200280b0581d9007921a14031006020040c40038002400c21500c0c081c0d030a010802010000e948903000384510310025020010f030744c180c18800d4400380e0f0305001c0c0d033383c500309074002e100d00007a009030308105a0584004008400211913100300c0c410b07148528409611110345042c446a00d402500482050241c8501c3c101d0500b41e040d544031204403030040b0920f030b040003045c03d076004a0030303440503244c8955400e0090000d502d8000a14a004400050020112000000c5440b058841c00560b001150344005020320002d03000e01c0305d06a01504017400b24420885070380004603003400660010002d6000b0303400740608d82080f030050044101c0282814002c40d48443e944650f92030009054008210b114500301003168480d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 854360296 1250 854359046 854359049
    0x70302100c06140c0901020c1509010e03150106030b10020d2001020f1303122a24050a05070c150f1803020f01054503120117070f0605090a 61
    0x2400e0343c070120700e4040440361840d0302c0141031300d015100c5c0c0554100b05180040078440e03184076500c5c800d41004201c50041d50b110000d00023083c1c7c540102c1065802d0090400c52a50003010540c1d80400c0c1c90145205111000410f58261700c00c54001040d1104c0594008001058502c03001000d800c05182c440d41c3d160080c00742e0f14610803081c80003e81c4003003501066906809403401202082c040219111007551031010f900000142002c1014004185600320042841200d009400d103080c0f060b400c5007070000c0010400d40c055120f5541e01c0600c100801c40b8400c180d404107150401420600c29911075542c410502c039040b080041d161040003280d24071642200720780055030001325140c1182d40c41c1c040d445181c40c14003140719618020015001c1700c80c2c03003401c40c0070009400c40364514540048100256110684507150f1282d0007400ca169100c01c200014811050031042041d42135041508442c85024015421003040e48001000d00c074079a560703002a01103484178240a59690403050100b4400e01d1203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 854361546 1250 854360296 854360321
    0x601120908090405160f210c1107050f0105180a050303040806090d03020301060f050a14130807090c05091903061407080604060f0b09180a0c11070302100c06 69
    0x826900c001048030850181801050840e403d200030b958a22000550032021086000050010100d030805d8502031804800c101d04101500c84098415003681000d41d22400f03401000501d454400304542e4100348219800b811013101c0210405a401d0b000030700c64000c00d051000c000c012070b00802119a078640c400401800090140ca031501e0303a0f90300054940c0c8003250301d500c85029040c1e4008805109100301d80c16555640c03a510000c02c56244100e030541c01c584621014030042035244085000040302500d0802c00c004511618903081801c03060414a09502000059040000e010b0f41d080e0014155000d080381910015001c100708010303e280c40086a201400c9545003454003040c9003802c0d09814070400d2191100c035440e0300d40303c6c01e010490311688145115000e00c1c645c04d1000c001d41d200284902140142005404009444c0420b00c515094070801d00c01541c8403800c1050a070010254032000f400704000d000000e11719008150200201c060400c100300903400400e00b044001e41c418001003a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 854362796 1250 854361546 854361551
    0x15060c010e010207051b22180c08070506040b030c0304020319030201060905060117040b0c040b16120c0c03081e0d0b090109060f09090807020607260a0512060112 71
    0x5a100c810303000f5404144242c81034042c4016000c150441042c011a0305c88000d0f041c00c7d10036030000f03000805007000101c138040c0c00d5110421005582618040d00c05000c0c0035401c4000210300d004000c619201166002d1405070380140020440c2030041d100ba03a51214440451595a42e584e00c001b078204400c00300145950300248038210245681507003d20207480740708000b004262141d100550704101d80059003603d4442150000703000039060700c00035400600495005040c1915003c45030301c076400503122008040c405503500340c1809444407044c034914100d82055401c040264440000e540010300000d4551303000080e901c08070700d20074089090902214181261500d400d00f41c00000f074070042c0c4500744240034071400401c0b00700443c85107004403100c0d000c41400c40d91a1413005070240c0050f0300203031010481070101ba40035840d85002810021f00c0380f541c2c0800c94240d178401101408062000c0c1400080602803010400d801900305c800d07420030101190507960781c80300100e51807040c0302d50805a060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 854364046 1250 854362796 854362811
    0x130c02030717070b10081c091a1309020327030403140f060106020f0312060f1915030c0e0f0a09180b090a32070f15080f15060c01 57
    0x2c100000d040804d22580c228181074503141c80f148142807150050720041d800c084d07a084060b00341e514610720a1812401c080c5161a43c031200501c401c3c48510312588511800602a0200d64064101700c0240c11700d25021400c50910003c058071f00700c40c4481ea400342c82c425000303840303555a00b0010340d40203546c040c21400480240784169512880c02242801052042e54004280d1900100d06a1821401d600045043c001820070254540f40003505468002041c1540720a060301e940040e480e0003d01000c200035400d00d09109035085400c3c0318450401c040c940300b8546985540203101c0f8000d075408445c288042040e00c1e002845820b41d5030b000214851801110281c040c80c1507004501072400351f0b0940900b6074032400d55544544904100901520001100b440d540c412120040b1303003286101012a5940350030388040e0301d428003a17000000c0346007054108001c0400110603001001e101d52030b2405150415681c01d1100c810301134a21346c20003540c400041003a4403a20140c4840081c070304000e11814 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 854365296 1250 854364046 854364083
    0x171c090807030f0203010b041a310c0f08130b060121050a0b01030603050304270606030504021002150105100210051f0503030f0d0b060c01050907090507020c130c020307 74
    0x303100f90104074000d50900028004070310301f40c0316900c0d20144940042038540902c4040040d040b03207681024049840c40e9030502c84076070295116030a0310f070801d900060301003024803001d40503008190b000b90401c07504604015042003181050300890b40e0003802542c19840386001030700c0070103807a41d1170110380384204859401c00380d25800c150b01544000304204170240b04030b0011800c0d01c00c03501001d070007075101b0002000913131741d04908940343c1c05002d00c404000500c0500c4290603580103500074000607481d10240070035803514a04020804507d400100f503800c1c14804010340d491014842c0034800c40d400007440442034024007422155201c0c0c400200021302c4c118000700360307518040ca442c0110111b494804541410000201d503070320244c84800608140020621a0241022024040d0410420720a40396880c0e801d0040c0390052103a00b0103084070600384007080040784d030007e20700001c540c0b00007000b1915480d88401900700ca86900000700eaa1800460140d155105001000b0110210f42c1c030000d408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 854366546 1250 854365296 854365313
    0x30a0f0e220c020f07032d0804031502030403080402092a030f07020106030c0902090a030f030f03050601020606010903020603090a0b07050c010e0109020105040e100b0c16171c09080703 81
    0x8110703a84003004001404034007281d40d1380e0325120401c00355008100906c082028052540c0d040354100c0c0c0e01468203034141410114400200d1001c403282800440c00380100003140c40700c994482c252007801c6085103407903180242200d0f0041c002a018122101c04940c0850b05c1c1079400911001844172018801c100c004046801d50041b05d40c0007440c00c0b840c0108400318418003d40e012281c214034800d92003030916080c900294881c0c10001e42c05420b0500c0040020845581480028000d0301c0701d40200000080103415a440104071a0441d0410003c10038142c0e0008141c07410760b81c040d48c51944030fa5483e80d11500d4811b80982c0501454076680401001d50b46c050010321000a1040084c01550700908506083c3c0d041c14000a0200b01d00b40300602405031039080840e804094400d804100643d1a03865003032582c040c403ea4106508070850a0701c15469210303003080207017000f030180400c4060940ca103d441e40c500b19800c9529407035044010b040144903105120140070307000c0070b80d440780d0764a140c203294 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 854367796 1250 854366546 854366599
    0x241b1703090d11060c0703110102071b0806070905030615040f1d15010324181b0b03060d230f0601090f02160204020c01020409020d1d030309030a0f0e 66
    0x158503015001e1050030f0120304203000705100848281000041d43d01038490340c0001c0b01c1c0c204190f50a0040e8004600c2c081140c00340020804880c0d08150b08000c046410f0441c020442000e00a00700c0003007200e602c000038620707804a800780f080182c00580784000b5014248041c440605107042c012074043d00d803282d048006c1c010552600f00c1d4008a03a2074040340c40303a45c00744800381080340c0d03048820401c00007c20031b0000b00c421003036001a4000c0050380f03142d9030800c00c81055401c103c2800c3c54418801c0d0022010b009800544250341c110b01c1c00354000b4802d08074000c0024800001c1d04094900d1040f842c400c5295910204240e420301e11410664540d105424446d4010950034002c807840103038102d100f144c6050250509820000d4056000d04c406980407440c1401299800c00c0f00154401c030b10f10140c030340d0341c5591501180c60807a403621076004c54a01d000351401a0010424069809000001c8030303101e1581e03007070007040460011300548103565040303030b0b05da0407052048035a02069240c102a58 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 854369046 1250 854367796 854367823
    0x324090509211204080c060f0a0b04060b180f030d080f0a020a0c020111070801020408010209030c0907020a0f020402040b03010b070c09060f0e1504020a0207241b170309 74
    0x9516410030030b0b0121944005030810b6007611020070003003540c0030303020042550150044149525008412602620300306013110a41c0d40003100c007050001c0458103028840100c0804c0303401344142c90420705a07000f40e10490100c0300d10b0100110060501ba200d290081105000003005e854003400d40a0000d0000901100c5103c1118111400500050003a100781c03005200590b480f9040b0303415030f50055400c403030480c040d40c50910071404c1c0080e0740c010034001403001c0e20030400050b85034500c02003030501d050700d207000142c810040e4030200520194001801e030226a00310b84880c080d8602d6002080c020f2046411403504018000004075065680f5801401524400d03011802019500c0c0302ea041141c02c40c3c0240c90744240c90741410421000820341c3c098008910030b2b4601d082007500300004d012640088222005038000d958200114942400020110843c00200c0c14110501f00c40043c44a0f0450405c081658803501148040c00011505141a48984903001c1e41c2d0341810072401d071780ca9180c0090721 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 854370296 1250 854369046 854369053
    0x1050a0302161205130918080703031d0a02011412060d030507020a090c0e0405150f01030b030d0e0907090e070309080c1f0f0626150f04030905040b100324090509 71
    0x83c000c446e0b13104004241a406841ca10b103503909590302100ca81c880402a0101900e603c20b428408201040c40040d03010120014001c095540c4000f52495180101150913914107002c0e917101015000c81d40d03a48002c00312552422083c0070301d41900d5a0058480294000000001c041041101c44c0e1045280d100701c1d071614005941079034100700c2074510403188010032142031200001c543c14480e507075a2000e03c05040110b0032810740c4c404070740b42c640880b0b01840081e20105502c58941046954150401c0043c034042c82d07543e007005036144000502401c08000c141d903d54a41c001e0280c0030096404042c07904066a0800350090002d000301942c8961083c4841e1404800c010041c030140320341c00440710892000c0c1d0843e03802c0b45a54840e04030321080001d090150b08131207013807268203a00081c03003800d410b81482c50500702418018090141604850b010380c0c5001c00c8020299504656851001031516000c0f5051446d0035144600310103070700f00011030b6904103001040b5040c035900b02d82d20400001c000c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 854371546 1250 854370296 854370299
    0x20408030909013312051608180c13020c011e0f0b180a020702030d020a03080f0903030a15080708100e0706082212020f0f030901050a030216120513 65
    0x2041ea500e1214041c00100c00d80284220381004c640c180c02460100504008030b403000b03240b0360344094400484003c0c410299900f46001c056030040c8000742c215000c01c0034260000380d440c2c00180d68800c100d00b068410900b480065100c42e086804444070030350140c000340001c8504101d1194801c0402c5000c1c001c1ca81402d00c512001c1000d4401d4514201000b4070081c08101e280440c000c2580b00680081000707902085890301689003002940f0020b21b965000300605120303401d008155050180c03100010a01c1d88040c840d03001800010b407500a03001100c005841e048003042d0008800f81640015918080c00200140309200400c80380e1075080d01800500c489640c000e01683c03500762601a210210700708402141300c840c8141e0415252500d820b0350954014419100e94406410648240340164400311b105409031209011029243c0c0340e143c021400c0070134910003c1c1550042c12000402c1550201e10480b6521056a01a40c01e03a00000100d100080f50070000341315500c010100c5540d000030580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 854372796 1250 854371546 854371559
    0x9060d090b0106050a050f0c030d0c2a08030f090a021e0306010e0714070503070606181b08060d050114040303091707022b0b0f0912070203060a0e1002040803090901 72
    0x300c910310441950361030310746101d00b2001010b5422a55000e01c6070300c014040380d02b400c01113228010559140382c032016100c2c42181c1c00c0b584980640c1d2240c2c0a80340300805120000b505400a403904055000c207802410f54800101900d00040b140000c5d511000016510139224030700304040041000690584000ea030322240008a1007409850900c0003490307540e02048031507a5540a0200315109005403854098aa00c80c407040d90b03000d8200d061100680c0059191402c142d105000184007003070135018003550602d1300a00780c01e000814503406001e080700b80800b0001d080d408071141d08401c2c140310009007000d0800a0040001c031034100c0c0c80c0c1d048000c41680781410701d000c0d242610390050580b0b24030038901044016408011103460450504a00100009014103121600c01c00e000274408606241203403006262901c0034070340304518001000381da80507807400302d1b05075801041101c022400e60604122146840d2a014940000718130215011071010408002040f11450444404a103640c0303455 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 854374046 1250 854372796 854372807
    0xc06081b03130807080d06060905040f0c0906080a14040f051e0a0f030e130e010605060f030c07050c101e1e031d0a05030301030215031909020609060d090b0106 70
    0x101c0c2d048003801c22508040c0003402020041c400207101701c03011410400703032041d0a000d07291290070035001b15042d01c2c0d0074480c6003000e200c0e5050010200c40140100400070724058050301c0503010700c400b08030804002444c1074000e40c22500840060340c460400341d183c06c1c1490702500701110b408513001d0241c0c4556014980000010900300d441c2c540c0900385903400c0b50b403180e161000e884000c50034800450712810007955882801441c0300c2c00c1c514046041752080080a0031141e403900107500c41c44052041c074004040c0101070340d03440300d0070140c250b41d14060741c00d103546000380c50b03030005a101c14105a1004030340d0784070015586100642c01d610840e0902d4203029219002001c0390321190014032105070003800c0c4a80c200d50014002e084d9801c0d07424450006040c1040b008040a0350f03194000001041141440c0d624042c00c03841c0345141c00c0c294186401c0d2441c0c0001940060f50303029449a103a0425551008200d40b503c501c02060555204e07101a480005030445c07030000e0740c0c0e0b41c50700e500000d00d02c0d0144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 854375296 1250 854374046 854374051
    0x315100503070f0e041e0507020f1e030c0313090509190618120f1d011704170d0501060e01140d15180b031c0f0509010c0c06081b03 58
    0x585406007555150742044a006000382c0003501081a1500c481c01c06803a076101c1d0004907407200900100d13444100b0541020344002420302403c40d84000c02502031028085000d40081c498100c50150042c2d0f4000e456146004264121030700c1d0100041c01442c000d1528000c40c110360f102403051059035901d002b0940c03941c076070004c12081060803c3c10f10002408581c440818030021030210184851241c0714102003440d202c10400200d1051900c038040140c00801807015100c5024100101e200c00c0030008020042070035003030030040ca0800c0810201700c0c405049001010f420f04406840710f025685c103001401d802e00c54a80440c0c000068905107521540101e00454075400486240603855080c52005083c1040d8480c2c105420b4400490468610084c9500c0803107000300100d0301c5101c04007003608201c20b030305190746003400340043e561800c3c2c2c101003841c0200b00c2905000b9107600c40307103006a65070195464001d01d5410b070b20602040140c0c01040c0b0703034010344141e41318061802d41d0f5a001201031009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 854376546 1250 854375296 854375329
    0x120201020d050a0c030e1906020607020c0a080d08180303041b050d0c15030b060f07060506090106080109020d0605061209060c09030a080901030b09150f0904112b06020315 75
    0x1044c01040840d01598000300380c0000541030054480300c13402078400a0742d03560842c00058200f10144182036604020102e150001201c0061469280646565035004080545401c1c082c400c40061a00440343c45d60503010791485c0282c1e40e4919242c43c28140520500700c080410706250500400e190402508400d0440e51118540032201c1c1003500c0d07080130094803c000420141c507085175032070b03640710b0078007400d02c8510b500c4101c0e440f448189031000664100901990040403003000402c01958881981411984502401a0b17240074505500c0302034005500700d1600603070006001040d02642d880543d02c501e007400b068650584410301048142d20071107480681c1940039004250108007050001c00500b90141000103c0c11103181c00700742c01c11004c9400d141000030852280341341d4206811007401d80f20003114031103030700c0c605544c44d203a0302c0c50a030301c2d030300d00403a0303010a00d00ca10081c900c012800a5114640882c240e02e0343d00d03100010758400c898903045003860603a03440950070801c2d204152041d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 854377796 1250 854376546 854376557
    0xb030609150301020c030424030e0303040f03181511061308090f091003060506010216060e2d040e0319081003240513211206120201020d050a 62
    0x60300c41100d64a030706000d5429a0556082044c1d502c50041000108020301c01c07000e0400300141d6000d110301c00000034080110034141403407140c05615a0100482e5401b50b403040103a1070494a505088541102c00c00604881a02c00c050102d0b070207180c0c41c1c020780c919443c0e0b0354038003400080480f90ba40700c9006031404c40301a00c0d092000c000140685000d408c030701c4400351644140c00308010008450503010781d6403c83e000b40d0b060092050001501aa55114400b03000801d41c9804990080300c0042e610300c00c88080000000d40c03070040c1d03a91700d665456103290100000010f07c04039450301c006041d038191440c1c0308501c0c0200e6020904000300580e01404445080014048016101654150b0004000280c0c102d014240840000c021844a048541c4007055003062070350401100c004540c07002d8001c1e200403e403500c0c840c0c0003c050202000f400140040600600c1421140030303201c0100d003101404186091080215404034040080c0281038000d03070880e90100c0018a0130740d55172140c1c91102c000180c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 854379046 1250 854377796 854377801
    0x1909080c10140406090617071e05070f0302060a0b0306010b0706150b07060204090f0209092208030f0f06060f03071404090e0a0b0907080705040e0a050d05040801060b030609 76
    0x15190680c0e00501c070140c105400b0107180007401c071665030b01540084010404899003030141c503500a00c031564012486641c83c1e19401c200e900035221003401d01c240d00d85a0b40c020f100d000440d01c50016144040c0c0c0c00b002c0350440041501c0c010f52603180403203902580d58a070104803543c500d03000942e07a048890b80d00550749807110315125840070b00354002400d08407aaa0f8100018214203542c002d081c098010f440042e150360420074024260f030681449511110300601604003a80e54810b030316a000300100900004c8649458922034145c181244040e1054401004004800400300b40991260503041440700442e40c56104000389400307042c41c10184400d0500020361890301030b00001d980187c441801e036080690312003401040d0341010f9a410703125040303080780b0010410018441c40e0025800c1d40541211400c04000a035a0310051147c10700c0703242c64a500c210600414054010701c0d03500700c0190740248101000143c0942c0c014804c0c00900e43c0b0744031000407054040002d072170107150001c00f020040d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 854380296 1250 854379046 854379049
    0x70f020f03070b0d051302100915090b27041a09060607030909230c120a11071502040e1311040615120f24090204031208090109060c051909080c 63
    0x1000300400c40e0520b0303103289440c6c00140c1e0320034800c0780c0a04042d82d039902e009400e00c0001e0b0102d10007010f6120034018a0202800180ca00909803400c7c1414600b01140c05003040076080f408100340c501041d0020304d0030701d81c481c03500603182009e68000c00603680c003039507504c5030300500080384503103000500000c4c014071081c010303c0704a07040b012040c90702800c550124440064422000d4030b00fa1140800c500000607105041c2004240c0b6903840840300000f00b0244072102c2c03004034a4410144010401c00302c60040008605140d41038030060103e621004402d0301c3d00d0b01000c103d41c4e45400c0155880328151491400f2840d05008941c250307070a100391101c41c0d514040c4143c0310000080c50309000b603900e03408050f052013100e20500c22071440240c3c042c0b21010344c08091342d8000075523800c0104e07035030f0040100340040b400d440883c074800c44440c84c11800d1653b81e446594010701004100426544c1407000d212001079000000d0300001161041c1030410076080b4100f42d6542c10ba500c20042250020041710415 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 854381546 1250 854380296 854380301
    0xf010e0408070602160524070f02070f0e01030218060f060f0d09060c1b080901050a050c030415030b0f220f05010e04030201060e0f0c07020114070f020f03070b0d 71
    0xc1403003500e645090418669482081e40c01c90003201c984114200098010300004200b8400344403a464421025410f0000943d404098001c1c050320074000500c8a43c00101d01c01c001c034000a20030400c2402119403210a4255211400c0c0300c241e01c10380701111754903004541038042134012240140304514181402090045035006562511080041400300009450841c022848410300c1201c00059400340c1100181c590f200c0d2084209811107004032490000c1e081208403401807009007003041c0c0301c80049004946a100e0500da4014a0001040c009194402c0d414170903c144845d80341807201580c004140300c2c00c08250300d90f0581c003d042c11459104040007a111500d900005600822951041c41c410000c2e98020f0b0b000c0400d0310300b501d0412060681c20b215841c0034124692002070241018445510058805081e500b80f83c000000c114045a010b050327913144114105601c00c1c1c8a401c14200906000001350040c0d0186281c1d480c0220b0700e240c041554000c0da00e200c003d072401c0440e0030840400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 854382796 1250 854381546 854381551
    0xf01270b0607060c081b07021c171305041b0c061107030503010e0703020705060f0c070c290405010c06020c0106170d18051c030905130b0a0e0f010e 65
    0x4415500d10400005840300c80042404500998000c14003010484000740038080003022107602c680308195010004030400110360400b6012900103d003e81585100c00a0303d0920b40c0c000c2851004103030103803075105031402038580c1444200b05e041c10a0340c0c400500c0151400030300c9044058403042c2074012058011400c0d400294046c4200107030100d00180b00d6502940806c100345c0c01310300080010061551a05403141d4058007a14042d030400441c0c0c0d076000c1e034840024225600c0842c4100000f01d40300d0144064030380c2c0542203182c02280d075560341c03183c9070308119004032802d05490440700c1700300741490310003203500310342c0180c0d41c0611b078003040d48030900250044690182d00395201d580010b004c0b11450f00005003500c1400141005400c0b0000282003482c0c103108020308078041d58800c00050380c1e0b20200c11200001061024403169143c0741c2140d4104a60f042940d00031242020051b4505c066448000a20002d58010941c0354079800a61415142102c11503110501000140900120000c5564 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 854384046 1250 854382796 854382869
    0x9030f0d181406071e06020f090901050604030c030209090316060501061107081b0a15080105120a150e1e06010503280807330606030902010f050903070e010f09050f01 73
    0x41142d1749540da00060340e001c4002070110320320106030882c4a150071040b460042904a588030b02d45840e607503031403a0403e840e10010f480740300c03000001502c0d40d07414800c841800b8136900d10000c420b401032a12200803e000c2c02054005a0727507602c07296081000041400c195082d0200a00c8490401c68028008002c01c480c80360300204991b20010782602c45403800340c00300c003032034032045a20340c103040900c80e000f10b1803c064021544041040c4001c2070074a8401803003040c4502010880740c881e1401981f91014946000040420140c91003943d00c03004a4018180c480c110107440c1c00b00001210302004184501c8110150581821220700080000006052243c400c0e400e100100c0302040c0154034030700b50b24071094040729138812022500c0c109403144901409031424104454185c5800080c080d1444828070000d000c40040c0100c07666030104869001008101c2603c0741e83c2d80c684200c3c0c800c0200510600c90032900f0030004c5103007041502d140c9410303240c522444159641c01014182c04a00302c2d585400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 854385296 1250 854384046 854384093
    0x20f15040509160e0d1a07090305060403020a0b07020f070e060a3204140601030e2a09011532180306100f03060209030f0d18140607 58
    0x90140ca500b161644110944051040c00c4404020058030301d200c0720704058402e04e81058010009868400340e216180240541c1d07540701d0b41c92075001e50320b40300c158001601601c00c4900b004105607000600c1c1c40c081e0b1050802c000e040d2584ca00603a0303104a10341c0e41010681000c501441080c000b580c050341d0041e00101a800ba4a07640e603002c61404000d00200002c25001202801526229070040606400141c0e02002400201ca4000506440281c0703054100b5840d0081c003019018208900e0074404910003111a0b40740c09900c05081061070088082d007e40c01c02c40c0009551143d0b42603074940c402441d218419920a421610300c40700340321540b00620020b050324046203124a02024140904106010404a06941040514090000b0f042c2014010307144818021801041d1b032600480b54080e002580350a00b00c00002c1c106130045100f40c80034800e116450035110b0b0701001100d440382d5038a500030b100980b1520508088a81c081d10a40c0000c010131820001411200048a02d0020012074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 854386546 1250 854385296 854385299
    0xa050402030a0b040c1e081005060904061802210403020c090a0e0618210904090c090c0e100309050d0c02010c1a1017070b0f130902120108030304020f1504 68
    0x4040703030f2451008400241d45004c026100f08041c0003c04002070490400c030f01d281c03400d42c0d02341c803000c141405281d0089001151642c41d13a103803900002c020f0300790b40310382147c0980320006140083d004107008030360205603120104203141ea20031000303000e00d80681c007500c0040812070038411109030103400d2044099075500d44203c0320609110481c00399208101c070b4107004d03075112441c80c80e04450140c0000b44d41104492108c4901e0704008807031440100796401700707042000c0d060003e0b821a8580c091b070403590502c1d40c1642c0c25030340190281040c60301203400b01056064107004408440300100d0041c503a6001c582d03203005c418055800324283c0e910515006400c101123603a01691034000d0403200484016000620200d4145204440050080c12041c3d144140d0b02c0b1404941e078185602c070380b51100c3c80c0080d0038065460340c0d8040b607070341d071001f1070b82c0c004d00f0742d0750b907101c0c0c00291b015841c2c034420388904200100d4a08004000c40723005903001041c407180c2c5540c0c841040a00303907441d00c0101410008000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 854387796 1250 854386546 854386549
    0x10110705101d0115031e0c140a2c040f0212010902100f0203070f1a0705070204050601140d2c07080609070f1e050d200604050a050402030a0b 62
    0x200e0036078040c1d80040031445480c0c1c80c500c2101da8050780781403111a41484c1e0140440107803103154000302c03070700040d50f04102c030342070040031074801e86d0724a0113869200c48480202d20080c2200106001a1043e18103082441d50348540900d4550904036220002142e607000e403505403000d8441907000b034000c2d021606062100d50009800c68138204490407182d440f680400150310740b40303600c2100b103001400c3c107003007103410540002d48030312035480b00400000000c4504c009000c04034070304102c400700c20140c0100509007410060b140341c00810040348074908000005e1102e5204441d2481c3d00a45000760a003094402882c1001a068880d603201480b24200c21841c3d48000c010340300781052841d80f000e81800e034145071015040017401403e10a00b503100311801c00c030a01c41c82036a1400c6440c107100035044402c2548a0030400059130b8890341d4400c840c50047d4051050140c56081440155903c41010010440038000d0b05e000e14402c0e554028100030b001c2006003040d0f0000e43e482a403189000581d01036610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 854389046 1250 854387796 854387803
    0x40c080a021c050f1b04050a120503070204150e090c1e01030f0f0b03150105010c120c020d0c061e0e130207020d0f0c0812042c0a0c09051210110705 65
    0x303405003160384908041c000c02d1071000c5e01024000c861740c49002e00d810308002c0400c0000e8114800d1040301b100d080e01540512074148169103815a00510500642403518100c4c03c1884e41809501c00321018000840e0980c50002940444107034050001007500115192003003103403002c401003074145511102da1201000e110f1281100100050030700044419600741030514011004030110000210f80006000907030f003000c07003120401d0f4840101c00e91404141000c9076094000b0780000e4004180380250303801c20503074680080c02d0316402e0342c0c1c00c8002a500800a10802c0c039000040c0c001c18901c081000c110704100004a0f070000506c5d07005850b00000e41d02140201020ba081910100d0054910f042000f041d44413500080250000810440c0a00c1c0c03900605071096201c0c801000c0703800141103150b114851f05588044041100c104020b2410f0131100c809840380e00348550009000030740114880c07800c040705084102c140001030821560540e241e0b0002c210303401d140b001c004401c1c0480c078002078041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 854390296 1250 854389046 854389051
    0x501090b0f0a1112010b0903030705030f0a17070905240c0d020609030310050405130206070c03020411071a0c040b0a0c060b0a03020f012003070c050f040c080a021c05 73
    0x7188000d01c5440c100050200302c5107a00030a508052082000030004050850400d0550383d148200a0740d50542000003480c61040c103400400500012410701000c2507400081d102009a40d03c903900200300c22500c880d400d4500f140c1e4040401c1c400c0300c090016040c101d60b160f40f00000b5004002e0044240c100006854020718100f418981c05010507030301c0982d05010054200a46000850450030503556040324640103025540c06a980c03140001e040c0d4282e1104580b4154001c0c154075a582e8042c00c1001401c00140004d074001d50a09420784a0000c1003000ca914890300104405010b5a00107116045081c000c6e00080d00c0340018040400d64980c0c202c02068080703500c3e191246042014034105c0160341d02c02003410303c1008203003001c00168451000b4103003035071000d281c240403082280c5800a1800000c4182103400d10000c121001084900072060040d138070121039414814200100700015108600d0b0f240b80041c08401c04506040c4180e00940400e901c10a10038145600c0448401b040351001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 854391546 1250 854390296 854390311
    0x60a09061e1d161704110f0603130308041b060c060510030f0b0601022503050c0d0f26120f1b0306060a18080102190320070501090b 58
    0x50954140c40c15000c01c14450050411200c401e5584101d40d444500e01c0c24010030b10400b00050107550070109102d40452502003411800e008114102402c02d40d11100c0700860450042c4e07542ca03240040c1d890400150f034840c411315456404950300641c0d0896200001520856002450450302d0350b035120100d0450002d41003964414040a035542414800d5a401801c030030031505401c1030038404680f510b0b4041100729044140304c60b880d115000100e00e00001d4170000461400c4402c5020b800c01c02c07800c0329000b2a402241101c4c0340c0d00044d400c2101d142d81310140100b11511041c11071001814040390110408080b0044420400c0030855141044d444841990302e021800c0003048a45040403505c590403c0300f0302c13031100c00d0320b00f0040c407003c0d184405040e2611880010454010440c400d10110315030512854124090300d585101d00d60203500007810700c5001d040907400360f91065101e0320646500803000606000c42c2d68424243c0c0d81e1560099805940319500c4c0d0342550f01248005c250325000b41403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 854392796 1250 854391546 854391569
    0x50f06011209020d052505060a0507150608100606090e130807060c0305010510080603120309030c12120105180f040f02100c0c08150a02031810050109200a08060a0906 73
    0x70800c01131b42e40d610640300083c04084005405000d40c1e12040180c0c0c3e0018510309246030381d00c0c0c041c20b00610800b440c0f00000003071400c000c0042035000000c10701020124501c1010f1001d5a140c410580340c6100c980503c100c1d1200001c00154003062059905810360300a004071490b0400c03985a6905494a841039503022903110f800400c110300305015802c49210141c50200900e0400c4d00c0081d45400b00500040100240440801d04000342801160f040c2094801160680d07040f402e403161a41d0040ca0507426000e0441000040c541000c24440c8134100d040a11044165141c0e0403050447e1000b80042c1d42078444020300000607101e40c803400d415808151500d000384030513032504500c05410b5422140c0c0a0b00140e81920114542d03c10080e0051180040585c40356902600c142c004600c00165950610408034198007852599010074181c0c0c132414028482e200241c40084044000c1e44c1c410300c4174400410541075000d00c24003d07590002030003060072092075960208181a1515500321120050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 854394046 1250 854392796 854392813
    0x408060403051206041109041d070306050a0f1b0f0207030c0e191b1b02030105010e070201060b0418021e1b0f1c0f11030406090303030e01050f06011209020d05 70
    0x3003a120344551100d001c490511005018a01b03070a41d60051101d800d00454407054800035440c03070a603103107032200c15120844050079074a040c02e0010b0003040d600507110600d02504407010b21003900809008000528910300307020701c601c2c0c04540d0354100469903c04c40c01000000310001f1004850f090090001d01b50b030084a09040c00141000b0f14914400c00e40130385031400b1004040c55002c0324a0702e0070342506040048000b00c48000e40103800b2814003c0d4154603000000c02c400000621050140c0007550080000d01c0d00c0340300b20113040c850703402161a0644007401000661000390004d20110b41e1030406010501c43d54494105070790030401001440e003807440c2c042440102c04010310303030740c19545100614200c01c140c04001c80c0015044807100c02c00201c1c10403405d21902503d10410b08040040c04c80341d0301c0b590703524001e0081425000490019090911003107484c107050081c18003030b000e14040380c0b4041d100c0300015901404800b80006106803035400b040056654600c40315a02400b0710081c201b0075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 854395296 1250 854394046 854394067
    0xf0b04140f3c0604051b0c0106080a030314091f020a020102070203070603060504180809040b031212040314120106050a020703051603170a020d1b061d120a23040806040305 75
    0xba5008280c240210310380010000b0140c1c54074205080e4102e02c50401d56034961a4203080e001d0022504114481d01c142c0b4020020164150f014902a2406451400c11030710389064440d01c442d0105040d41c01180b0318150348500d5802503004142c06c0c49140001450841c0b1940880d08000041c0e100e280400e5849108000a041600604045041b001c11840c9548030301d64a44019004900c4d43e42c1c0510341e1484c01c841561001c203c002500317802c10680300d486100520f03000724603120480b0220700080500c20079850000c01c0070300396034a001100c1100406a800c1420803612600043d201c4811032086440020108a05003c5240c201c440d04260325040740c19030400c08a00d00000d01c081c50b203807804201120405a0215038040c04003420714040f2202901192511080c141381c8001800c414038014030355007040c1815200b41c0c135400e40c0e0019a010b000c5001840d00141c0035186504001c14283d81d0281400300c40701c3d2881030403044a80b111803d00da1a0005249030003400c5500300d000c01e50004003005078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 854396546 1250 854395296 854395411
    0x308060301060303210b0603010305010b0f010e03062e0f0807060f09150c12050d0e0c030c09090109050601291603051608030a0f0b04140f 61
    0x220400350001e00440c0d1850ba0001c01284e45024100a020b801103200d808505140c2c2080900c031200030140ca4480d611703400c10134020808545114030816190828504035401150340040003200280039080c03d680d900542c1c90304c080101c00074400180c0c200e2800341d010040300040c40140c06070b6101201c0b1075044c40995860919560030070028450720760301d00290709501802c520f05440e080300c0c00000340031134408242c1c3d641c0c1011000820350180c55110010141d0f002001e083d00d021710940038424000824034480d15494040203032034054220081500c4617041c1100c4058014550b00000074807805140c59441c00c1c89001c0e003000d08110072010501c3d018411100507150714403100c0741c42526060401b88600d074080078400f0001c05006021809400041d0101030755503441d900400c041d0768901d00660748200a0000303501c0e0407106440d081c1e081c500360070507209010112031101c2c1814080c0c0c440540d140b0b0f89038001080042c0c00d081d070350300001d0314941c00c00f06030601c2000c0d110744c0440ca800461101d0070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 854397796 1250 854396546 854396551
    0xe0705030f03130335090310090c060309050c13090c0e0903181f03050a1a06040b0319060e06010906110a1209050306270334140a0308 59
    0x115030052001803c920400d41e4658110b940c48007802214013814110800760044800c80e600080c1c2e615281072031305581380d000400d0305540c100c1c141c0740c00740e03540c0398040111540e44001030440701c11070f002403101501a50150360064000e000310f590800481d000941a49001640812482d07200c0d0004420050055017440107080451008140c1e4074000c50040c0e907900880000004160144254200e6a16484182c0080000ca04851180035610007400f40c0580070507030303101c09917a00d000c80c24004071150111a018031040180603900e8a4a0080c03045400d03000503040c1110b509500f00c90b4204481e9620806004080701d1091800b945400740c0050252a41607020300288015007450001d44003020609038805507012500101c0e202059004464659080c0c1040c0c1e0980700c0c10050004840c403041c0101c1d410502890038004956040340265264091b09a031464140028000307442404020141c940e584200100104071309840c94854800f6041d01c40510049608043c400c002810703800203210f42d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 854399046 1250 854397796 854397823
    0x70e1c020a060c151d0d03140705133b0a1404050a0212011d0109140c0108070507061b0c0203070e0702030706050907090e0f01050609010302010905040207060f0e070503 74
    0x2104403c407511040a0380d030110716851500360791800410110600702445590a019440480b02c07050809a0061f000b822000705500500700c44c100001c1d005072154003150003202d0700690f0700d40e441d45401c1240b0304035003225001081c0d036042807035036044040c0b490141e100c2061803400380e44070710305080d9409411296202c501845030f10b984020003020500000d140003c035981030b52054920145082c1076801890700280c00c0d10000326601802c04548415006280038078080d1404850403080f400701d090780c81c0310030000c00d40400d821b44001841d95000b203003e072140c3d6005d484082841e683c140c1680703801c03215040c083d10200e1040030860b8190b00b004c0208502820320044131407c1401d21050195481c01140401810b2903250800070300c0e540010b0186000520104005020303998041c541c031512024241d45084442d0729140000300545840004a81200e03010303105d0100e01c0c0c2c01d100900c4042c0d4030411050303c0094450036004140d4190740f0861806149400c050041d00c3d0605081504150000c003400f03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 854400296 1250 854399046 854399057
    0x212061009050402370602070501021c08161106010306061404050601020705190333060b030403030b3015150d02280608010b160b070e1c020a06 63
    0x7000585a81c10107035218a0a11040c0b40c0840580c00c403942c42d849240f55958440e083c909000030780d80d80012301d8078281d6009070251a05210300150140d00312012820350030000d101d000c00f041e240c241c1018500c00142d0343c0d01d0701c0d1510094042146161407400e90045404581e2a076040005110b0b860703203418214400c43e0144120304100f00002d50310001c0d40201031203036141c44084000780203003032020b00080d41d00540c001448038006120340c1075407800c076502c02410b0740e0003200f84280440301d2040d5400d5420002d417041c00d545494078120000c10b001503040b600b1605480c01245095014403200142e601f856055681c06401300f180700b800c000802c0502c1c0d80d1065850b06200c21100c103002d0000d0241001c1d03909503440c102600001e4a0411107205824546a108070b41c0101d107210840801d0650322251100a00380c4d907200001d1259105e11801400900084103001d000141c0e00305207280c109603903141c420003501d601000504ea2901c0050075003101f500f210a040118288404080010012030600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 854401546 1250 854400296 854400301
    0x902010513030812070221340b130b1b0d0e010504110f1806060403080d02120f09061602010f0e03300c030601020709091515052b021206100905 63
    0x31f0314804010000c00440902003540031200c0b51010528015681d00e9840e10003031001d50050f1064241074900a5400c1410440003480ca03500082c4030407403442d070150710a2156038994030041d40c05000c41c61528a010740400c07034815289003a00a00c071404a0325400041e032800c1910b40402000c4404402600403040c03c81d212007680d8030b50300362050080071016450819a1070600265643c8142e40000f49144070100701c1e401040034a034068410040440c0410050b070711400010324030490101c0314007095a20500018121704900601014900716500010a041f0f2032014080143c40c803100c85d55035150f0005c951240d001c24040d2020b41c030005510110301110b828107001c40c0703402200170405c5041130760001c0800e8950b4030030071804008145181c410410b01070a850700c0425880c001c04400d041c581400d840306410b80c4a11105400c80d0002059460211a8001c5440d45a416241d1201c170410791940d03004096141d140851000960721400b030850f518041003440800c0c419a0400e00c0c00302e1a0408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 854402796 1250 854401546 854401573
    0x7030f02061f0b0c01021b0604030908190f030e0915043603090510110610050f0409022704031202030c12150409050303220507060309020105130308120702 68
    0x115541503c24010300681d45034031042600f03019102e0001600e1400d502e0441131a400c1d1f80100304180554803030b41d1078a1015507a4117000380e680e80c1c008000c4c800481400024400541d00b000041905482400c290022420510008040c5d41c4222108041c65481c540d460315645000c0c45801d120541c41c0c1d070f030441186502d40c01000c1c2d8460f200365030415100e0300d15030001810300401201b401010000c2c20503201324800c02c8010302d4015001c104000b148540346c04180341c090082c1e803071402d4400150a81c25a26252010007001d464012000e903000300c80001c010b41d80036001600c83d8400590402e40000900b042c0c80c00a01c20b01d54241100d103404c0c814018404e508204d0022110101d00c100860140d80e00d070000654130b2000e000e01142d60091629080b10f042060100c081d5110704200320507030740b00c01d210f4070f01c20302c45407440b0400070902c5e0058a4180010303030107a072000b031141c0c0c010b1400364146150f045c50b0600001242e082600c23180000705008101448040d1b009522540d01d1002d418403408009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 854404046 1250 854402796 854402851
    0x301050405071a0d0204080c01260a050a060305060c130807030f0b15120a020a061409040905070e09100b0d030f08071b03110105060603010b040306050a0b040207030f0206 75
    0x14201c40c100310503d1420000f0108802c4d5040c805200108554036582c40174595629900500110301265a0400746544902000c42c120b04100b00c004401e0f01e180e40d04c0c95801e0080000405042c0700355501c80c00400403810810200f0b102d1b82865001650341c240320441020201903d90006809038040e0304141700060030581c2e541c61184e0302c020401166140c6820707283ca60010000b4483e0445151070304c0801c015800541002d403240241c400f00b20781515041c0441e00c40601c03240380c8200c00c00030001c001c12800d0660100c424140240c00365000651200841d600e40102aa9605810380c006181d00f90082034034460f07000c101c07604a40e15808401c40c3d64005e45000c00c036411140c04c0c4020400042e524a0040c80c3ca0003034080b01240c1440c0404061902400001e0300c3d4072465030701c0d031034000010980e051036001c69058a44091000c0d083c10714580e42e813030203400001d005071082d0362500401c5100303440e94000340034401d1107511100184290014003d00c1d000004002c41c0d81c039a001a1440c50344550b02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 854405296 1250 854404046 854404049
    0xb0a050c03090d1404091a0916020c0609040902091f080a120305060111063405090909100612020301050f060901050d0807051b10020a020f0d0213090302010c030b030105040507 77
    0x3d0504040748150821328682e03902950348070800e0b01e0f007805942c0070340403c10312118220000c00c560864454407103c4501030312407440f003000c4016910070f4640030b40600d008405080b00780d034020400b107411225035010a02d0400181e5000c0303000004007682c0541c81080801d034101400da401c00402240381c00d0340328032401c8220307500d00001f4141d0303d401190490f4407820325640d2024060040b242c15003000d0388544c0000302c400002140e4140c03072480c00e2050381d0004103000b103406400e0303980031b003842c1c9d401c0c0c00c00c44c0050303000e44a901d0783d2251400c150480241805a031004003608490508841c94a0052509446001b00602d20b108141410005195500c040242c1541c00544220520241500d0801c07040d10507814042e010703101b005070051070220201e00180070b0107400c1e55075010f100208201681e44040c8a01c0c000d41c04409010081194107080b8154a0751341d0000303042c0c0c00010114081001110725400040e0011b035110030540e15000e4260040044051058000300504e2406449183c0c840455 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 854406546 1250 854405296 854405323
    0x405120f07150b0d05030c160b04061107170c0a0b120c030a090b1005030c0109060c1101090b0a03051b070b010302100e0618011e120e0709090b0a050c0309 68
    0x48002c07688403600e41e60302007403100341d0203001c1c00300825031404d215689030048074101f0400e200700f450000550200c1903098044803030400041e030401d814124143ea03030300c02000c0e907691981310300c1c0000220f10b015040740b2041d082c2118003030800d60320004140725850000b80c0000041007002c100c0209480365842006034803109072118203403641c0320b2520100c042c1904400241015030b0a800380420b49510401280c22580200d003211091b00b850b03401580e03440028440c090111301c2810a42000c6a181c45074a184007034145003803410030b0b071a41ba042c1441d800030070040c40026520700c1000b01280c40000f002c0e41c0500200c1440f420029a541c4503041c803c01408000c4c080c08181c00038551550245110440240d8014911502c9041d041e0210b4054502072001600180a200070103440b41e44c00042013001429a545540d80840085090006009400c100e0300c00c900c00c0ba00c1c0040c0c92941441503c014a10131041048141088941c600a840000d003010745036500800c1400100000042c840091181 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 854407796 1250 854406546 854406563
    0x30c010c0303150e09010b0d0816020a0e0108010f0e1f090c2d0e07050a0c0309051203040e180d1d0405070906120515010e06040803120405120f07 64
    0x115454102c01a120050909500341801c030b50101d080e4040c82c50680c45003c50302c000b001003c0300c0b042000350414106030043c00d0004200312600c90b46e00c1b04101000c8140c0064901c2000e95135a0252401255090b40310340800c2c0d55820300800341c54018001c02607001d1400c402491420340d8006100004062403031074001d130b107a552140d1303400c00003070908c1d1000174182000d0140d51403d0b0640d140031b81c0c200007948515030820f04000859000b0b10894814000c0350300f41d49075400c10000c0700040d954501c066406030705120360070340001182d40d58203800466016501c00996125440c10b002c01e0104d4030054080941c90344005501340c0007040002d2686892801490540017002800d00c4c0c924003408400c0000d60005d00b02070030030445176004000741007119a42d035a41c11552104281850480d141036440c90901400b1512150841d880707882c200349510030060910340751503600c0740700525592003148440810403a840402040c040d0512294401c1c0717110484041c0340040c07503c03141c40244140c45c0024000740 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 854409046 1250 854407796 854407817
    0x603061005060703090b0f0a14040f03020d030e040911010e031f021315030b0108010902120601140f040906060f0822060f0f0f0b151206030f060132030c01 68
    0x1072242425070020104030b12415629903140c0302402c2148d100d40d8542c030100741510500c101012100048031b044900c0c1410088865080d0743c01c004011080000070340811a120440c900555180e200d1030050500c50950350329000c402e14005818140e40100b140d1094010181441760200c05200c017007421004080016035400d01a281d0001400107904030700700400c4211740380c01c1ea5581503480686c2c806004d0301c0d101c55036a60741419000340d110b10801c402c019911980801c800d0b5005151600f20220501019810800d1035406022903800c55030040408546a5608000307450f002000c1d000c0804081c5010405440c0522003401e01707401c0403560500b41c8240c100c0c98410321155501401143c0f0280740203002c81d000c1618a44094507041090510041c80c090102d0014a481351a4081071130346828454102040d00c80c40402d4410b0042c991901404ad0003074012030581d00740003042c0a82075088020a0311781049090707500c4400e5860003d641800d003021038611079500010b0b41d00c2040424a892218070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 854410296 1250 854409046 854409053
    0x11070605280c0e0f180f010f09060302061c0f180b0a050c190c20010306091a010c060905031308010c08011a0306120303240603012912130b06030610050607 68
    0x2480d0701c04003090180c0c5c15000f070119101c80d1040c168100e9143c2e103014040e0303648a05000c4215100d03484000c0d84450100001c05050303404824608814005000010b501c40208001c0350658070340d0b540041480b01d86a04c0f40080001d41c0c0e0903544c00950542c0d04204501e0004580c0102d84038a40d41f9881031043c500300c02a1243c0b142e88170707a400035401000c0b4004031403419140c0102c1c2034030b102d0701404681041004a0100514850384001500112505015046210055038081d0808005076070030b0f5102d01081001c550b0820040051141c1c82424030b11a51600039143e085401448240003041a080010030124040018603250864803500c6980c0d0303900d400000665140345410010401d0001004200d14514041400c084016488030913000d0002c031070301000310305e203c240590031047e64600610052000c0702207600d0001207494003a0783c9441e007801c038901c090079011540200015128200c81d010048843d07201d580081c030940007441e0f0743c1020311030419a206540240ca01a19000c00c510091 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 854411546 1250 854410296 854410309
    0x1030b0406020c01021810020d200709020a050c0d08010806061c0c060201050115090b0d180b0103050601091b0c0210020304030611070c060504150311070605280c0e0f 73
    0x5007103102c0300071546d903010918140780c82c03040304407402e1080d400141107500850001c41c11240807026a030b5024210b07100025a444804a00500098213101c2c00c000800c2150180c4010040b00031251655911500d030300b24010315124645085004000b44040100b204110000724103822200484d0300f08100041c103600c0d00200031002c00c0103400103049000009100b40c06611550503580d44d100c00030701e40e0140080540f0011144e10035000d25920401c135080101520382e04c400f060003041103449409543e00e80f0344410b402020b03007060341d00d81c102c41c004000c06041407042d003203845105080815545401c00c4090407113410345501901440d0b4110130490b500d442841101d0141d540000704000e204a0140058855000300d54111044c074030503030b00811801e0150302558200c1e4442c80410341580f00c1440c00714007421600f1140981c58006200340000224940240d910400071741031070455200e0001c0c0c500545000030300303849141030300d454400d41e10725a200d400c4d03050041c0180c03040c2c5588031414000c0b420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 854412796 1250 854411546 854411557
    0x3030209010c1a010503100c1215080a0302010c0e010918110c0a1416030b040f081201060309151817071a1608131407050a08030d110403080301030b040602 68
    0x40c04002400f03c42d00d40010300009050300c10542c111903034030741110117a00880e009191a4408100800c101482c41d4905400011458445901c0e2640345a80c400f9241d01d030411198003100542d4481d5080c03814264020304440c2540c03024038180244a241085050741c58a8551341c005519890781c00001607120f022046620100042040f200703003d0035800c0c102640c0c203484941c3c1c81140168401d104400c66103402d910242c0390070450561241e1110b40d110024181400c030121102c0f0018010400482c8040828500900454902142200c9a40b82000e0b140c0c00c0f400c035000b607541c641748120200450b10090a441c0340da01c40c80d001c0c885178854114580a0150900040020030f1041c10140380c10101c08580340140040e5450301e0710200782c2c610940300020104c0d200902c120300c0b2007a080125100c2c50369203812400c801c05a414064171080826041881c54200c0d285a6100281c9504c001c900c2d88104500240c01a001c58201405c1d0f5499041700d01c07062101030240780b12203020805220640c2d04031203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 854414046 1250 854412796 854412803
    0x338011802090a0f120303050f09070e090109230606220207020102070b0d02133f0b0f0601020f01021c0207031206060c150e0a0813050a090509060c07050a03030209010c 74
    0x1c02d0135507101c4458100c1e166600044000a044c8004512a0b00340c0c110818014446007001d8480141441b0300e08018810061a0725942c0d074903040140301242104110a00072032840e0f450341041c41c2c10055580c5002009007100c1d000704006603000c2c503020000c010020900c9144280541d594805000403880c000903508002c1c1654070008420710006e031158010014400d000c0c480000d500d81c2c0e000d125a1104905100c3c10b11100303101c0011001c600300358002085400344407018405142c0c9a00e0381f0ac1010740c100c405a0713010110609010f02580c04100071400c1c054514025072406410301032100f2150701060a000140d500070645104140c080c0d1100d02114141c503d0420049944850003000c00300e41d21819548060560514130f034068003030181808412260000b841c3c011034580d14144280d0200b0400c03a41408001d50119055644100b064018030400402143c242800c2c09100d0611a016058501403001085101c0c00100045030000c0e45640505006072140050310050340c3c4002d5008004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 854415296 1250 854414046 854414069
    0x306050108060a110f0f1308030c0106080f010c1d0d0515041704051806040b03030406050c0705010c051005091507050a09050103050606180a0338011802090a 69
    0xc11009800a8694424103080ba02407203042604204e00000c0d108450003019050003c004800415003030380000c2214001d4289000c1c0c0465030340c5801030642e00142c01103600c07651100c100b00964103042290b0b82500c0c1c0c1c1c0714003c000c1c036001401d0180105000c80f4900001c1c1c940401e1109955482c0307010500d409412800f610a44506040100810f45084404a4a10609003007070325440122000b07582c15030b0000740c601c40c5045c00150440c20400b20003044983d0042c1c0b50307035143c4202d44042c0080c20040c0081c1d00c91a444000098050341400c3c03594000a0400074400c196001080300007444131002490454000b40740e8480320030039401e02005042d00070040d40c0d21070a01020300e511070000d12002e0307000e036500b0914070744610046081d500306030b80241d03000340140104c1440c2c2d051a4114500c0b40c01c018190308045a90355035800404260646c2c0024207642446400c40d86490783c0841340d09182140004a03407581032102440d800c000078941e0200941e40411b100d4110348495150710040c01c5a034010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 854416546 1250 854415296 854415299
    0x5090f28150807050a08010509090c0a0801090b0a33093306200c030a062f12090a210f0203090a0506031e090a020a0e0601080601110703060501 63
    0x1041c0314081c200c580310000c0c507007600082c1036501c80d00540d0314034011035541e1500c50340380c0700400951041c0030f4005c2619005010f1152010f41e110105040101010340010641031071300c2c28100c4c25104001d08040c6c6207414034825525004000383d078401c06071310b0078051050484100081010318895508051000fa15003242c42c000c1000c030160290002040c00340144400f00e181c14a40416611031007541c0c04203071107040d600e039144410070001903550b010104451810103d140040d2400014450950350180d540b1003003034403000c0c50b900a0440200b9182c03248410a40720403a409503120301c0360240310340349001c80032178943e2409010010441d500300585015035900740401171000c40c8032050001c040344904000c00040c0c2d002005075190000002d008080c014900410312600344d0004201c1c00d00282c3c4224408484406a00e10b0790050000d00d001b469642d010344144031500249030400d03811004901c0800089070790000d49907a1290702803074181021a07c60b010149841d80a400080003642080300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 854417796 1250 854416546 854416559
    0x1090807080a1103390c150f040e2203050403240e150105150706090c0e0c04080c011b060b01030216030201090b070813031b021c05060705090f28 64
    0x114142c0071440c40041514070280b100e2102d440145e0b0410070b1420750800700410600b0b10700130015070a00101d0700707480352510030382c0d00c1e8505143d03201c1d800a230900466003060001c020303104901305500e8000f082b100941c9141940300034010740520300c80208100c030907c0d60710140281216030111980090b02c003e000310350106c2122501c6410a41d07034610000c07010f40c0002468982462603400c0c0a41d060b10301454107200e600d40340c002c0c140d00e1000369610200d45034001030548800c01228400e04038400c980780c89a081c4501c0d14108031a0301041390401c008241c1d0300c1954403201c2518030050390300850014030100301000580c0a80560b4420b40240f031202042e6406140e010b402c14008540704140e110882d80d07407420b055801001c180c2d054100041c00100010000c0c0c022915948851f0b049255a50403203002e0703000400c002c1300c007540200e2060300000303080c0800030704110b46a041505810f103942401500340c003152416980e210050301c43e1562b080510009401010041c0c0610342d4240100384140d290103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 854419046 1250 854417796 854417827
    0x1030c0545130c0f030b0f0d0b0103120f140903120f040f0e01031112010e03030106030903030b0a0501020316020d06090b010303020d05030402010207260d020c1201090807080a1103 79
    0x16001c90081c28101d031550881c2d10b4612030070110108903122090300700e5415400f02c0091140e082e1280c0c01019000da100a07964a503100292514400c00c54074060750304614000b5143c0300b41c05811024001054400d0104942110420001c00403a14a80b5101c0d818140024500503c0050540000c27500103003031800040750000070015030310f60105210301305540d0031014030f0580d0244000b811610494910481c2e03440e25603507400c60785040301d002140b511402c40600303066034400ea001b200880c0e9950f00348010140c0500030008000e40c00c40303441da0074607e0100081d44904c0b9010722100c0422411201c202103642d000501c1c500990002c0c404c11002541349808103100c5405e01084d8058403c40c41101c0a17a417040084078811a03069000e450301516103500c9507070700c0341e0064070740c0740c003804004441c420507400308008050162154000d00c0001071071010f122440c0b04281c0e0b4009140d0500c0d04e0080410300302d404650100e0f03403214955503501c4018004031180d1008280300d6415004c0003411051040307800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 854420296 1250 854419046 854419177
    0x13031412011517010e0912040b0702010c0203030c1b040c0e0a17011509020403020f0d0f230a0303150602190b101502030d1406030d030902060d09060608060601030c05 73
    0x4110b94010030110580d1f44907020794801c440342104200000401944124080b015680c8041c0449003440ba2103032016080200c030103106000d02c1082004501c1600e01409003004508030303402c1015245c83d4840c042004510140075000c00141c0752550641a00380962014004805841c80b150213140c8a528040c042e5000c3e1000360b01c143d1201c1071540c001d1815040c0c2c000d5a5502801c01983c000c00c1c0e54645401d001c01510a040c000038210908143d40c8081c019850032a100c1e0340c00140d104100459880b001c8000d8003d85c3c1103500c421002000030004c2d200300340c81990014502e6031a03503a20001400c030100c154002a101440301086580f0880c0c001004e450b011480c0541441007101c405da220350048001c880c6a5419480314003078620490207544441405c0e0b0000d01424505902c100344107090b188070400440e181c590303401040119a5060004a401c01000d2030240f00003030300a00c00030501c2c01040018110300001c0402c2211007580c110100041c02203011040d103070000c91206111111030304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 854421546 1250 854420296 854420311
    0x21c05091c1401020306010f0c1109040b1902030c09040f0b03120301080d1d0108270a020102100902060a140c340806240913031412011517010e 63
    0x102d010009403035010300036240304802c10794910b58103031542c1204071070000383c0c4002519882d90940000d50581c0724506a42e20840c00303081d6180860518408050f104036840c8840741c8461702c14001c1c0486150b0741c008603407038000110350118003803a144004400078154180400c0d4035116078161100413442c00c034042c5d4100e40f07a0009545440d45e4450041c1d0f0302003130010a40b01910381c0d0704105122503001d16035054006280320010f20980c10070454031004000040c40c82c0000e584020100002c41d80c0c108503244140650207014060390301c0640c0820704500070259600103001e003e0803101e0400300c100041d500e0b040112022030b00b5070300014450a200c07128072900211121880b103040d030000511490603004032100c00c0000d0042e580e03815000450801c000c83e40f003045410b110b07001081036540c807400364000c034039480281b103090540d840e0192500f450f540400c0d80380c0b0340a21040c850304600d020360302c0c115082e20a0034880c44005490440c0c60f081c81e844000040c030a80400483c8801d55240300f14801c512 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 854422796 1250 854421546 854421563
    0x230d06170d02010903050d020a02100c110d1704060b1201091b0b03070804060c0c05030c070501080f01030b070507020d050d1106010501110c0d0c030807060507030f0b01021c05091c 79
    0x7840100b01d0907144516800340102c0d004200a00140100340d0007448d024940b40b0549566000041b10740c4c9c01e0303c906001c950000f95100542d00740e9100305100c0000d4002e000e090444a07030050300620007403400c1c001e00290510380d0740c29180f13400b0b8070b9442c1c0c404200ca0302c1200810002c8014036000200d542008160f4030b81103455880400c0008010088902401140d12000155501c995514002c0c02524a0b12002c00088400000002d442040a0104000d284000d0030080e03003440001000c54000402e042d4115031141c0040004c21805c0b0f092a0f002080303460043d90b114000d0012401da8100500300400c10701c02c15141130140d540c4856020010001c02d41a00c081c0e9a0b62001103407605070001410010341c0005190114514140800318000c40c880c00151b50802c0d982d4550307203c01e8000c40c900741d4041d51108104800d6540c0351081001e005a460380801c090003810000079640c00b5110660421140040710390150700d4001c0c400d486015a008049020381d1200c41c2000c0740d0901c2481d02143c0284 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 854424046 1250 854422796 854422813
    0x80c0405040827030312010312091503110405060c03270a061b0215130f0b03040308190e03070314070302061609080d0503010312020d230d0617 63
    0x901405541d02807904010b1240c10003100030300d40200261002c21040341407075040148001c0d600d0034030142c10450185c2003046901e40c550f0908581d44410703100b45004009a03030b2020b011010310101100c180342c00742c0c0783c00203542c07c0d044041e01c0b00d0f100b150052948038002045606003c40c000004000456000888604500c3c1d6000413121a03080c8800c6140d000c0100c0d00c042c0403040c401c0340c80046041300c508100078844840d40100c0d40300009609001c40c0c41d80002014040c800b00c926410000385490424400d20380d2400c0941411404040d200904105008010640c1c2c007000b04410342008480703442c20044500e14075940d9540ea400400c0c11404030700d686130481c000340701c0c00d01a070b003405400d034001d09011b54505481180d0446403402a100b801007a06010805400c00c0100345110a0303107844155036941103050140101d00903807807100071036000745410921150b2082c0c0808a11743c0c002d1071a01c20703981c2c00c1554030080c000c50b02144101c1c1d282c0040007032855201a00b0031042100075081c1c0d02c064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 854425296 1250 854424046 854424049
    0x509041b020f0d0905040903120504141203130314070c0e0a0614060301051203071b0e010503011514040e010e0a03080f0c07021e0301090f151806090206041e080c 71
    0x101c3d28003102c000421501c203001c100a0030103400480354036100c0e01d8603044090280512a085850a071400d41c0e0241500f000d288400c0c0d400c120400180020344809030841c50805d400c0c440003004440c00408020744250300810050185095480b950b5000b0340c002122500c40b221034204450845903800001d003030400c0088c8582d2488015501d952028002e00d1841c0c0c00e0009001015094010b004100d00c0704110b51000720742e05010380c640030700001c00745410140c6041402032002c101a0400e074400c1e4901000780030020305000202c022a1908107050b0030800f180c000050003048452034412882d400c002c0c40a80c1c41901059000d4100c2c400e40300c95809880e8031020010302a01150101e14241c410404c0d4400740c64400c0c4800d16441404e41c1d009291003250300800c3c00d4842100f01250701c502c802c01c1d40001c01402e020a12040c0e000b441c030410000c40001214240741d429070740c002d003405a890003d003056407240c50445016100a60b4034085c440741c2e00e4411a4004d540f413042005502030201401000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 854426546 1250 854425296 854425303
    0x10c08040807060c4a1302030915040803060103060510120b13020c0f25060e040908070b06040b0f0109120f1406070f080601080f10240806040905070b0a0509041b020f 73
    0x70382c101130911496006c8803440b02000354800307401486076109041d0f0290aa0308000e42e440c0c0700354402c0c0560384e283c2c10150700140c161940e41d04882d12a82c080c07000d81038107a80c804940d0030f6028801101080340700d00e480104444403940143e10680a000181c2c51641c00c0c0c1c001180b4140500e0030044880c8084240310b050007124030900700c2c1c44043c20303400782040054499600740c1d400030001040010050001c0c0d445520355400f80a04036030030070341201007101a103071500c150320314084c00350741c11030395541c5000000340b4203000c900a501c0418040c0e450013051000c00300c054080c00d5841070303200302b0364035900c860941d80f21300846c1c00c1e1001685616401c54054400c05025015103810f84495213162194001a076413414024145183c11071034482c002503070301024103c1111504c1160032000a104000c80080400c0802003195024509141c0c00d04001080021038004441c3c40e00c00c0b05440b031005060840d214403803110019800b45c103164030712951040c00700e1090b040036156000c84003601c0c00481c88644 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 854427796 1250 854426546 854426687
    0xd021306030c0b131503150612050609040203190807060c0306031203060305030f0f0d06031101110316020111030c0f03030a0501350102090301020d0b03010c08040807060c 75
    0x50165101e88101700c200012182404181c560f8140418010f000d500000146c000a030311085c0010f100c45028140010b440c070074035802c00420f07100001c2500d029000b0035981d044000f10072100e000c03907454540c1400a14420f81d4800c0354080800c1c41205d80e01d00c0010b01600f1103000a4441c00c02110030350f1400c5000c0e12418045030303400006182885c1036595625040d0304020b01d050040102040200d00340f0190384904009544900b0700352032405480e9000404513950381a10035841d40c42002500c016109060103005016030919102c071030003038030f0b0140f5800e40c00342c0008012148210b4019062072180440550321136038481c0000c2280741c0c0d84100e001d0703001480c007000300400c1d040070841c1c2c154504080116107118000100141c45d004025022a089900080000040b02c1d502e003403048103403a080c001e9512050703113840c2c07020b01810a41c0315041c3c18414450010400c941d14034858070300d1070080321403181c00200a03c03018103801c244104815200c4104045203041084c035161035250501d500c12041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 854429046 1250 854427796 854427817
    0x60308030a0e0d080103061e0f0c02122104081303080711041a010e01050c0f03070c0906030209011e030602030a02120105152a0f0706030f050f150d021306030c0b 71
    0x44c0c1d503440e648a01006002c0c07a031440400c0064405141c0da405402d0041c01d0300610302ea030000802c81e004a9000303040445007860324441900030000c44001035001c1d0000b4004c0c260070f0b071180300180c9462510582e00d22540690000300c062001d000014000004003502945000e240340c00083e0000c03104010481e64a0959446601e002c160014a694464080b8141013001030400b01d01e0510031031403041c1b40160040c10b5a11690002403d842000340704e13880c1a004000c00b5070144030440c19540050b2803084c05005044e80300314414521850000e03861070003001103812200455071f80c1000300b8000065070280c00203240480e140400021141049014030141d000700350032303280c02c2c104190003000203684400b0310703550140501c15038580e410b40203004d0300b011a070301c1c1e40081c40450310b030400c00b50685941e801c500e26040d2a05080102031602c2010040d4002c100b08014110340e040180010360300346400c0c0300031303401c040d03200c82d076802c3d0148130750102003513902402c1c1c0724440399a80c081d4461107100d00c600703d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 854430296 1250 854429046 854429057
    0x27020c120304032604240e0c1c0809060706140c04061e08061306150e03060106020601050901031e0f0809040b1519020f0a031205150102070302130b04060308030a0e0d 73
    0x15004c502640042c0c2a04207a6a4001c2c1b0340e00c1005440c001991040c05046803d5004100c0c2c030b10311490305040c0c3c5801e4025500456140c582035407500541400b40c0020f60340510b000081050070002940c2c011841c0705141440405a0b0404489280c0981c1081c00756a000c141d900001c0700c1402c01d800030441c00484103503070707040c05c540e10441400b18042c1000c22610f000c90f1615404520310030340511040340c05401c1e903200c0c1c0031007006808041c138000741a070210080d5008500144a40d4841450a90640750408512034880701c0080d024621481440750142040c0c0120240004120b10384000b0510b84400311414800451a0410070049000c016038a801e8038004202d81041c184e0a07620101080c07181c0e0040d035107118440c01074582403070140e0104070005422200030303284c40d031034a10540703400c8000600d00c00c4100040f0300c00031355501c4a07404003a12400050100c84814a0300d50411009038101410030300015559103440c000540094800380645410010500034882e0000360015014080d50303141d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 854431546 1250 854430296 854430301
    0x11e0207050628020f0901020d0f02060c07081b010b01030e030a08191503110a14060702090a0204050406090608011a1302030a0207060e03070c0e0127020c1203040326 73
    0x1510401c0f803008004149010035944400f80900e020300c05012111420210242e481403078a00080c20710541c8140802441880e0004a800c150f00041140e84402c10403102ca40d244601d08103c074040c001da080e5400f8001900c12103808400040d003002607040002c2c0c07010f00c003140441944a03280e02848030369000040342c0c04001146080d807040080e00341c80d45c40301e00240001031540c10012445890b007080d600c0d9008000c18803607505005548000030b00ca1604403140c280140d030001851440740d80d80281c4603c2c20380f40441c6801c00158112002880014800c10001c0e656841540190185106100c999442d004402040620007081007030039405c01040c0c0019a0741c05040d1400a400151582640070350901ca03480024003944a84500f0003ca500155140c3c40949003042c200710154100800131155100100004044522005107000382543c0242002c88050a424002d000f243e0080c803072441000201c6400c400b1050087d401a80260780710304003d561003e20010300d240070801c0c10341c03070074001c0300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 854432796 1250 854431546 854431561
    0x1203150b03070512130b1608060315010b0304030306080d02160e0c041701150303080412020a11010507020d020d06061d0603030d110702090c1308010902030304030605090f0d02011e02070506 83
    0x840130703485040c01703c924403004120380f54640301610848002c0d08442c0400419103030286c0207445a948610200d000306204e20541c40725040d1108184a00c0710b81c00f0002c40414101070103904000d010701202c100f03d54407002c42c504000d40e41e8400d10003100d581c0302102c00c042502d44100401c9449500c404600f0780c6014a05403040d06940d0703d294000b4029541c0d03540d81c100741c0303141c1c3e070100e0000e5020782d554095a007400c0c10300400081c0c12400c5101554481c041e100d001407024480c50328046803d00704039031245098004038680e60b191400095003c0d60880c074010411140d50301c40300949043c0501010040c084501c066484401a218170358554014400c01c40c1e00c07017050700020443c41d0f00d00000e60401c03207140d0100d0307800c0d001501c1740510200042244081440c039046818000d0104c48003e0005401a8001c03e8507845030b4040500034584600c000383c03954034200844064085950120340000541c190028000c11841c5000d90b1407000010990b24580140e0099a003001d8200c0040c110703945a005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 854434046 1250 854432796 854432827
    0x311090d0803131b060f051608180d0b070e0307060207030b151c02030f01060513051806100e1528050d060902101103070f0f1203150b030705 62
    0xf81201d00d0094049a10700000e8562405118002d4100800601e01c41c01c00f407010300300740700c444040f50412809110100c0c4a8040317000045446030450f60050342c66000c00800c0429210b1100d203e50004460600300c0300704046c20440e14810300c5c407039440ca151001c02608050300c680d503510a10006a01110050001c6580d0004440d000003503192a07d28229061011071528804000203001038015020440e0a43c101882044990f00c1842c2c0204103150801c800503a0049080368404560340d514800210310803043c03010841e02d000104110307000d92611922a40c148903003400340280507074250300030038118110040087c0c041c1c48014480580c100e0440004801c181c030503230800ca950a8203590008845d100d040042040314001d10002c0390303203d1140144441045094070785c40400002c5000f115007a000030007a191f01d03552000c8040c11504140c00e00062070711004d40c01604100c074640e045503500e9011b51119003030403c48240340c0500355a40b4000c0b101801f048905c0307804960204404142d045425 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 854435296 1250 854434046 854434051
    0x70f1403060a1503240c05041208071109100807090b1023030106020d03051807030803341b0309062109081e130e0a09050604030509010311090d0803 65
    0xd08216218035034035280d100c1702086419800da00b40b10390103240c620515803070055611440583c14014a42460400c00740810300400202410b0a080031584404202c0701a07820091140001c000d0303501c03803c026208010600d42881072280500c16040b00154049850107100500040200000c180b95240c4205130783c4115610015441c0b81c0140182d07089258485000c1d5000e012194000c01c08070369a00300240448001401d08410400003100501460350009150400d6941c0070b01115103903200c0c4020343c1c1241030050190341e1541b0100155034160f01707482c0a1102c003c103540c0e54012584000000e10700e0b2120341d03120042c0014040304014080e0b00c1c066010340721404880800c00f2840b0500c0009202100d02e03c084c12250114002610040f58070484021050080d8018006140000b00d05040c0010403252190b0708110140c8000100100116071200c481d5a82000c142d80031407815282c01040c1e43c2c0a650361501080ca040701c0001c01c585c000081d1400076401512140071010107860b24055038100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 854436546 1250 854435296 854435321
    0x2030109060606020303160810260a1b090b0f060f1209010c03060e010b03070f0e0303180a0906082d030706140a2901030e03040602070f1403060a 64
    0xc8100c0140007074020b00c80c0d840104800e03800b454490414079441000c106907098014100301c010802e1043c0f007586092620100c0302d5000c1c0e1782c10070402007136840e020000715001c11001400790840300010f0040100c00802d5020030055807280898032004040100d45a000401750049006c2d40c3c0749009092031001840b0010461000e0343c00c1007030b980c00d01c0c00d00000455040d08540d450300c2c0601c0d2400d8141c051407000d4482100d03010030030342c10140c0c607071020b0000400900400040c0061600014080c00d8504601080501926039902d0019183c0487e00141000c0c24000e07411100f00150a505a1040c1025121454058044180304010540303007d190a4175101c00214100015a4000000c01c02400d41358803c91002c41c040148881d050403404004190089081c105030001411044410000603d00e422164200c05091040012001000d07030300e075041598803000501040301d9400113181c5003210030450018003280d0700c5500b107501c00d1001e02a001e42562040d40032a01c01c006c2c41d040491803219 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 854437796 1250 854436546 854436551
    0xa0212030c0a08040801050a05160c020a211505091908220314010209093412110702010203040e0a09061103011508010608060f190f0f1a0d0504020301 66
    0x15031400c1c150034908503a100301e40030000000d04008a00007130048660160204030104000d191a07404417941a0b45400207008024180030030208550b80d0200c480c000d012030f644c1a204400030706284103d003000c0305205442c894400103e400c0124001d0058602c22008400946840381d0301003414144809101f008440b8040c0078090030321007003541081c103101c00440c6401c020001e45142085510440d001100a000b0b9004211450450b112412071b141c01c4548444c507902122718441248821082c96203d2038541e0040000400216500c002090014000342c1010000760a00981c1404d0383c1c0f085c484020301680081c402008a115174401141c0c1c4842c151a02080230f203c1c554400c0202c6203444580c0e0f850a102200611a8003403902204600700c1023818180c2c610f5044c150050803880c0010714a0303200d212901b00760300281c0c0b0380b0180781c0c1040e40e02072100203005855107000c0c4215400b034028a03026003009800051980101e25240d0800b00c0011403c1c0c0c54040c1d2410900701910300240141d0b015034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 854439046 1250 854437796 854437807
    0xa0e0d0f0e0301150f0905060d140307020405040606060f050c06040803060102160f09050c0c06011818050a1103060c04050d290f012907331104080a021203 68
    0x442c00e0041d02c6461001d0114900201d08041010014030200d03000343e40d4041c507050403c01c190f10f40780700c01c0d00b803950050181d07044c0040307415420b447c510460b00e000350090f050200348420001607420001c140c0c2c03451f480754003003418200703c21281400348000b4006103074804030100f4040780818005641014040c03040d5007070f2400a000e0400b2109581d405000b42100318142000014038512400d078003c0300e40210903241101503800d25503904030600942c040e4070802e00148000716003e501c40012144401070802e020160785c10050b8840340e012400f0355850007640c5400003e8034007c0f07599841900d444441074140340c04c11b018095600c0e070141c01124100512000341075804039200d0898445003291545031a14504084100404141a80414034000a44030007407844103503022440c21002c08010665101c000c0303030410803511a480e506101c0d4109581001012a07180c01042c09003c0d00c46200c24026071403840c4514146105a1180f20310a03000410294018034004074030184d00701191049a0034070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 854440296 1250 854439046 854439049
    0xb010903020907020f060714072019150c0f11010210090b070306060e010e0613031e12020c0f06161e05010b09010302030a02060f040306050f0f0a0e0d0f0e 68
    0x41038600802592001780ca01001c02c2d000c01c03080c0d0348076269140000030007075440c407958294003070094010141c2280d125818a600c00000034a403c6640003003c407103404060800640c958107030340c003600600c03003200b5946100c1b090043c000d404009070311400020408045881c0d60303070401002207199046014078051942041a580a21171665004001d00f910f60705081c240038040700c00d6a070112092140d0720403206c0340b0f41e030040556901c074101070b83e200380d641c0301002112102c0282c80c0c000800d0400c034003855140c40000a1182c021403886607060740c1d541000c4607000e0b6074448040d12201c3e800854100c101066042c940050035007542c9448403041c07400340d241d494000d04017800e10f40300c5804051000c00e81c103001c07090244108140b4140c038408042d50441d0046611502000d41c045d001c0d680014519810410800803075000b5030704514108010308141e4009041303880250740a0000910000210720349000b940301c8d04110810301c100400d034a07c0c2210b400d441c1e582c02004d058080c4180b01c2842a205d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 854441546 1250 854440296 854440309
    0x10c0f030e100302030619030201020706030b01020c040609020310120803010510020c181b03150103020a11100c20060601030b04060302090f0604050c04060e0f36090d0804060b01090302 81
    0xd0b4546920007503200d141420a00061030200304841da0485020030007080541d030007041c0071064900c0c0340b50110343d4110b0040140c0c40c10b0806c03840c00740c000b450b2010009240c00154051402811140803502d1000e40e10700c2045101030311120050074844007080101304514060040c0c00d0b40c0c9401b03005548294034941c3c0003804020281000404000d581ca0070889101414255610300190f410280d5045042c01c14000083c0103110030024141540064200e01150145801c0207a004075041101e0f0016804040c0c080a09604c10b41c400101d030b070080440300d5a081104280e01c25080d00320041c420765403610011030207005290a056046513992001102580710103842a1248121500d8400e4034201101440300b100e0000700000d00c145818001030154551007819000303d04009c44000c110980ea400014110016010f200f01044500c1240d00000c0c040c0f078660000e1113151707001034145c0d945e142c1041070b450308140701c079110009040c40c00003400104594410003500c0e0301817400075601500c0c1d030b0110f4517 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 854442796 1250 854441546 854441569
    0x14060901171302040f020f09042409060609050a06080703050604180b06030c0117041209170d1e0f03050408120403081909020f040e39030309010c0f030e 67
    0xb1030030b0003160000a41c1003500803e1350801d0314074811860814102501416800b895a207a4495078548200001e20804c6d8a099840c2c1240d40c0b15112030300e0b655586020042a00d07124100100e802e4210000f0341d80b50040f1201c0c00c480250701e4585441d603404404400a0600400b45603202ea03442c0110004813003203c09080145102c4c0e408148030341000750400d8609800d51710824104070b0b109501419005804107a80d1700960b014081840c5616071250544104150350090700098643c0c0c81158070240380010b038009041c485885180303031107081c44030980c01c100c610406a00410039910340d05450070b00c66440150f0050048820318103064103440074001100302541d00f64002400704c024003542c0c1080d4080070190340b01d00c000230409014140d012540d0080e800050a00c02c5607101403403210b030700041c00340b0520aa95003405141103030303c042c03050845072a1107020704242c04402e0200400c03818004112009894143c485003038820043d6244042544000e1049041000c030f05003680494803081401d51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 854444046 1250 854442796 854442811
    0x30e0d0c1413150302010818010c0c020f0904050309011107030b07170901051003110d050105090f011401051309080403061404111e012f030d151406090117 68
    0x226100c0c207003080280c203194a0440000051800d2803c021100c42c100050301241c2c0e080c200000c4541d21034200540c1c010340c5494241c0c60b9428001940e20482e448400100c40740c3c42110781c1404101c08109204425030111030041c8107620030099402158043c155801040044404031042d550700d95440f064600d40984405000c6850031290035110500381d084d1079442a02c0000030440b501c1d02021101e0000c6c240e200181690344490362030799031911460f003500d0515420038024402410b00040807030f13a5080a00115403154a42002c5500015030016818103c410081c50040540384520055000f0848448211920340003000000006003441c01030700c0c80080b502d101180c0c10b1405040a08052042d0365005208000b80f0107450a030450308220b08805034020710344940c407003e500e018401c3d0f0003201501a210a490500400600c020000003041d10441810050000041040f07226500710654094400441c24000c0f038001c050400340046c0c2418441450f1802c0310040308082508000d500f03a034000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 854445296 1250 854444046 854444069
    0x30403020402071b05060a0906050703260f070c020102120a050705150a110901080f040c0b070605060a090e0303070c08040e0108011a09010b0418060e07050a1d01050403030e0d0c 78
    0x30500382d0043c1c0c40c04c0005100c240c0b565403629084c3d850091400c0e6160142c1d82c180480807600e0814140701c0c00340001801c1130351783e4040010300740c02805140d400044415805040741e0304000341c2c520b886410000030f9150706800402072524070480c4e501da69003022404d5820400203001c42c4010507402c01c156803450380e803030320401e1080c2001c4e040c02066410070780e54130424a200708900c400e039903405015107a0220f50244a110151a180f806440d41c0e901d90b801507442c00804900801800087d42c4400d019032000c44c1d45c42c10095640c10490f050350405001e1200c581c10030f00018111a005400303003c040c42c440c100c081d150035201e004d121400d81d82030700403944607176556821000740c159180340b10303481410803140b009813503140035510740079880350b8082c541001c01c282c4441c80c1001c0c0560045c201420454400810625120703030000c00c250443d0140c140019070790410300c101e41c808228001c00c452810f075074a80c9058115203064408066400e501d6800c903402c0c0e444c1501059896000d003001c2c10b1880d124 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 854446546 1250 854445296 854445323
    0x5190c08071b030c1508070c05150901020414040b060f13050411030106022b0e0a030f0b100e01050d0f390501020105091e03071e0204050915010603050903040302040207 74
    0x2450280300303590499004020b50840c41c01c2034035080044980d1085407440c04c15010321003442d01c20300380744c1d01818900400c141c0c6422f02544d840190080c0040d1400c480d2000f225041407010442941c2c0903d52258100400f00660013040c10407030020000601000d000d05042039481c0c0124045402890303100c281c0c0301c07001c40140074a40d41400040606081c1800c0702048c0a8940f030b4080c0305012490300d41090000d50074405609866080380d42d002580c0004061200c4001401c1100e0100402c07607411140507000703900403035801164080c013816184060b207100101c03100795031506180300d1161800d541002c4098010401003540428500741c2c61b0181c00351006078000c030101107034403031856001581075904280410000c0781e030009401c0d03082c07000e6804046081441d00d120a06522501001516580d40c8941d2004c0300c0352207800c543e00c0c00d032003a1000c01ca241d0360440113585034450503403008041403404004102c2035110703030400c07504102200e040c1d92a280c0d590f0b00090032030f808041d04039900f000050f1b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 854447796 1250 854446546 854446553
    0x150105150f07030e01080c0a0806100306030b1311031c03091a090f24130c05090a021201150e09150d0614010803040f1a09041d0d05190c08071b03 64
    0x1c44a03041f40340c5505c500e0900813081c0e0054090440105034030301074441c09544141c00c2d40310340c01800046030040298281400c003514050800100601c05a2304420300f1400d40c1a58140054101d58004100c0130002510710313603500850240c002c00405448a562040700301018449203851113000b0f003520b100030a110301060f0340441c18101810305404042c0c0e420940407580050601145034041682e9090422099481c90305036003040300c9800075a0082c0c3c03034900f000111101c46c0d005000740e442001c544141a170345c6a013040041c91842070040c001402000003112103007040d00d00b0a4015130f166141042d000c00d03000100b0251500c202003601e1f25601c80c640320080692018601d805020090060351806040140307851810002e8410b82c4146125820061020907034503041d50f1068400034000d12110f40c4c00c941900041c031030100498a60b01850301c540402c51b00550403146a8184a001442e07098004c042c150307003d0740381e18001e45810008001010002c0d130021088142030000d0700107180707100c0c114103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 854449046 1250 854447796 854447807
    0xb030a0c02122b2306060c0610030605010f051e13020f090f0d022b0b040b0906090109030905060a120f020408070e13200306040503040501020c03150105150f07030e01 73
    0x480c183c4600c2d103000a0465508031003c140341c6180032020b0b0134105901c034075020a0051060f101c0300c0e040d034020802400300c610311218440c000c0742e002e00300c24001742e40c8450520988000900c103c80e0722007009541141c2580d1055400400290010019051051a003170720034240e80c880080156281c0c00001e07105018a00481b010346c0f90306082d5598101442d442c1e01062000d003001540101406076900d441e907012000968021483e07501905945407820246020003095000780d603000054007a450000d82c041d001445080d0115030107944103a07040d860103003403082a500865a00c070400c280e0b03c000d03442d1018140075109803101c0c0b020005a650785480080c40c2000d920780c224585a00d506028003078040c9074074400503501500065441c1d0210041f020400d034a0341e03a5100300c0d0f014019402000140040440a0700880d80c00fa029034500c1141c03003003011f403110980d600d20191041c0e40c8005001034102805400e00c690f030a02489890070b4140c4851081c69005003404800207035500e84444055680407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 854450296 1250 854449046 854449117
    0xe0303060406081209241c05010509040209060411040f0b040302040b0607080d1a18010801060611211c0e0d09120308150a0f050306100b030a0c0212 65
    0x5040c0c0302ca49202415024400c20b50018450386e80c0d8491036901d0000b6181d84038060041130000c0b9560a124000c0c1c0408001c03511011681903c1c01000052074103082e00c503e8451079000f091006a60342e58000c0000070608044d00c01086d840078480442d44102345071300a0058180382e4042ca4413689580f0400c01903907001040217001e02030900c050740015400c0819564851034125002c00c2989165420420701e1000d0000c90b68040c92400001c014108140d00c501c2c140d0708400000e100c66603c902d01a140368155491004bc030360b2081c0080c0d90300045140802a025000b51911031402e015040c0e480a01c15040440715100c9540395140c1100400412850140444908160b41001d02c4c049510350782500040000e8244451000042d072101d01c15102a0803110b0b00910f405e581a4485142d03120039902d0f4010a4024803500c40402c0640b608410024212410041c00c14503550b25488840090b0a241155000b50320a04c4244c100c8450340c0c01c00341003000c0940c2c190300c00b2000e85070f000c0b11244c843d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854451546 1250 854450296 854450309
    0x4030f111204051002070807090915020d09050708010c020d08060301061a0301080d090f2315070215090d120c08030708061003060e01050f0a030c2619120507060e0303060406 76
    0x641b810001c004020880c2c0040701c169410010b0125041c0c101302c0000c10301644103552891001503500f8401c0340d164055070040d405001103c41d1951a032090508032000d0002010142c0d11001000f01c4181c4034400203a4410b1020b8004103a0595403c0086050130300c0103e8560b041d00c000c0018420f81e0300c10449203551030081d141c140c1c4082d1400c0c02140072030386c20340907449126440c82018116400700440f425440d200140c001c180c0000c8403030100c8000e07009048200d224400e0b00c0e0b213420500b1713240d10030380700150002003494841f0302c615034880490a0740321070020107100d040001000401c0440002c0e40c8a2405915039a62030301d040000c21001c58984006074046c1868a101440300352116240c21741544e0040d100350700318403410400228030402540c00107090408500000c00e12804185004103140c42154401100004000c00e83c0d458240141e2400300100a003490f45000c00da9144042d030b414000b60500c285090481e84905003039071400c516190456000001f40000c0d4101031080500900a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 854452796 1250 854451546 854451553
    0x702010501050d082215230f0c070305010f02090a06020a23031612020d091206020304060b09090705090a020711090406022502010e04060e04030f111204051002 70
    0x4140003e03030010540c0c0000380050901042681d185090b1704001d892054240340307800141a56010355200c82a641910030380000c91400c070210501541c9400c9100b088900c01525040800d0008001c0146e00700d03060b0400a807056400010100b031080c411200c03840d22491001d03a0761107054083c080039102c0c41c0e0080f011135000c0c9911b4004600208454110280d0141460a08000c60141303a8518050b01890700268072000c1ea5440c2000310007100004d501410703409850146551101c1a55803d80e24818608815580780e02400003612507030040d5406445100d000070804c4d661408564010740c202c03107044440e032064401388803614140f42825404503908805514045840d0703a030311400e100701c140c10750180d040000458108550f98054940074102110041c1c0c1c40c5182000055102c024610160301184101c0140255030034140605030030b5440c200550002e85d1941d540c21031754441034100950421035441c04d000243c00c403d001c4ca1303092150b038a800584540c01c180401c51ba00d11a01d101c10155070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 854454046 1250 854452796 854452799
    0x5210c010c0203030d0525210501180519060b0c2b0e0303040801050408030a0513031d211506090f1305010e100603030f030e031819031a0702010501 65
    0xf074001080f05e0311680a40030105203501c41c103416543e8401c0090706a10318504201d004040e450f4010b549a445100c0c200d000c1c07045a224215003422a603080c003503101d8100300d030012100d802c2c0070341d044560000c207104140181081c44242240c21102107411002c610000040d035510b016600300300d680b0a4014200d40807103a011514100c2844641120031030060203000c944880307090b41c0070310540b0700900c4408002e200c0c40c0b44c6841c0031551944100c5410225510344804910300d401c040030307500c0030036a164444804015019000d01e081104103440190300c4416540c0090030710100c01c00340103880c40800c00601904100700090341e04c990004003842e000d107a5810070010194200b043c1b941d00a0026042000d024140e81005800b40c08080c2a8444511559018045074070107640003400303c80c0a555440418450480d0032410b483c0c542c641c44400d58000d2004102a00c5c040140f44402100200140a0042d100c526107100c0310285d801030b80d034112038100401c2018941d02185902c102c09100801141d0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 854455296 1250 854454046 854454049
    0x121104050c0d1119030c020f0a0b010605180d030207080c010c17160b10031406090601090b01020102070507082103010614161b06030609021312050705210c010c02 71
    0x20701400d039001071043e032a400f507031040b00c0000046a0300c1d0100c01c04c00b00c0001c60a141c000d80605882030194005205100c81900010700108054404580c0244441e601d6413814104903425001710b040410840c110343d400306043d03601ca18240d80c07503a2103500604003070340c6048000c80c10046035040d403c5c18044c004042e0000105090404500f0501491855498150b40304412510071030021b0010f0141e04140d040c4500452922444801c90b0310030206042103c090099054881c441514440001e0348081d005110007405031704142d61091043c40010309040b000d841b414076003040c0394031034a82070b08024100141c030881da01c240c2418140c03070000e0794519490803400800e04500d41c50008038a440c0400c550400c07a0450065400d180d400c20b40390b0136000d40c40c2003c0001d69955101d04030201e0f1502e40001140d0b051781c000e40e144a0a81010b10300803918010065400c0440314008454502505501003250303940e411803044a0a2401e4180c0381c00ca0403000000d182042020b5054184403400740a100103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 854456546 1250 854455296 854455321
    0x2a14070305070e0a021219061a0a0c170403030e1c0203030f070807080a0f021506220e070f0306140411210f03090108150d0b040c0504020412110405 65
    0x1c40718030b99050b071943d075108504c040080c094011341d29180ca0b02d07a02401a041200c2c103001d0a0b00c45044000c000c120b550703043d120440710070710f031291143c1c40050210400150013a41072020303003070252130505208001c002c0480125802504100c010440b007070050446c42c00c0160044012500302d04805605914580002c0c0c0e81780541e001003c108400010f0440030400000b0a842000d03910541304e0b0303180c0e0603010018007240f89842d0194018440e13580c282d1440c4030450802405010050000e010b0364202c0c4400000303071406d080c409802a51103120795240d40340c0800000c0014200c29001c1c0c02c002d8194508002501c1485111040d01500c013000c1c8004100454120440c41d0802c40303e1010300c0103616002e50301800781c024481d195000e22000116046008401080380c507400340d903a8041961520b924070744022001a0464124041841804c0061030b00805e040d0000e015a8810026680d9000000c060303030302c213401141713914040380304807002c010103a803006000d500205d03000e001c940380c00b40e40c0051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 854457796 1250 854456546 854456549
    0x10b040b07140c030d080925090b0418030309020a0b071e030c020a0f05040b09010b0304240519050a0b01020c100903060204120c08070e070806012a1407030507 70
    0x2003070b401d40c1ca00070b40d030100701d410708598014082d00c1102c180d031600500100412240100c1501400443c1941d0007005400c00300704402c128002c05600b810402e00d90003c01e80310841a03001991100c46000c420104840489924403a58010410800600c14406e500140e6882880245810300044002440e040c220035440750007130359001c4d98620141411100c85207415001b94200104120124044c40c01813690002d842c001d807000e102c032404090078000d07420801d01c2500c0042200b8008a4009080101030103002000545c0c80540c069154407400c00301c2c0c1040d00d00f00c0300c1240041d07481a1443c164052160301c6500c81c001040302d4112500040e441c1c280c01010f05114a03010b04200d200c00d809244000069500410115140c1d130f12881e20681c0c1007200d0708207031004000000005800640002c00b54150340410340d5511950b103510105071035079000901503d06110b4600f0314281c2c0c0d410312508009280c6600f00c0700c0b1020052038240010181c2c40b03803000d90b840340c020700d030248046200040c40781c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 854459046 1250 854457796 854457803
    0xd1e1406220f12020106050301180503120c0903060702010c03050a06081e03040f0e10080309060f032211120705030705010c1505180d0305040209011701060923010b040b07 75
    0x244040c240ca4440c005040c58100207100a015000c040c3d4983d07415481003068030b105030001c02056401030140c1049800b048001482d13948100000305070340000d01850b5811003400b104c002c0c00c20b20f410001a003000c41c121100c50040c0e66503101c1c07100d41a03241c002c0b41d80220584200b0085d0f6410030404030703203a21b07040c0d03040d010258079a04500038030601041210021b10510742d0081c01310740c071041a0b504150050744d803561030380c1d48018045181d50f408411288000001031909240541d0301000702e000303401c000c001c43d2489001a202d1464060700320541460703140320b84101010b0210303070030401c0115110343c000e0441990202c0300034801614000740d2001501c00900307045e030890255103001104e10b00c17107a2190460341d0070441030007411a0f1013103080d17161100303c00540b404007503040011070803900c08a502a42c08108200100101e1364000768021600000d02c0002c80d480d0b4541c02e07103906a98103200e14441d413080d504040e20b1b00c074484540e403501403c4840107003460189408007003c3c06000780c49005c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 854460296 1250 854459046 854459101
    0xf090c0e0403181d060325080c06040e01210c12021f05041206090c060e10020d020c01050703052703010b032109120f06070f0f0f030b0d1e1406 63
    0x260541e030200142c0011401124404003545065031031f028410940b40310f035012501c61080210154a014402c8c0d03016905c41d01c182190036880e001319020071004810a40441d0b04011984102007040001d040e00070300f5a07011016000d640754814840c0004440b404044002c03802c040c1c10303040541c020101c4045460b0020110a840d803513040490082c5502c800c02800514032450010f00e298002105000000045409202c00240360100b0380e202d105040b102c400503004500020169030281d4082c0c20118041d103801420200704048406040d00440034400b600307404103103070b00b60600d001d0042492004046c0d000d000e20301074108611554100341c030342c4c2e061003110203d065422038444a951211401c02c4000701e40c94414003440154444500380c5021001610a8a0421800e4000c51403038140c20030a6403070924845901000300c00816081050039480f5a000b4181c1001c00c55121a24441504200511110145a2070f060040950101c01c66107190080000c01410000c10000c2051520100c0c004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 854461546 1250 854460296 854460301
    0xd030b011b14060c03160f09080303090f0c0d0506041112100207151413110607140708070608040f0507031a060a080705130f090c0e0403181d 62
    0x16105440314032403072801e90146020000a0100b10500b030030b45840c1075000d0b180c460710f500702e01c51510310044401c040b103500304011580400e8801d00144488804a10789134000c140c840b000242160300035240c9070410f034414001100001428007007140e9440080f02da461b00000300740d840b6619500000d02c0030340444040c80c9281c0e034a490319610700f4840342c100d400f270b9800a98411907a10003504006401c0cad801c3d101620210102c078180384155080c0c800700720384100e2140e42c1e2010550200791402c400702d4258000500100b610b84401000c0c246051048801005e80c0782d00403491860300c819503110a200394815001040815040b0441d2038020303070080d01a04c40826a400d100d850b0104a92000b4403540c0c01c0414003092000d005c02181c000d9400b1151000c0d0315640b2000e0b16070300d08042c00790386ea001c1c6c1106a60f00803031211743e00040c80050320a0340031460b000d40391500444040c2d15807203886551061010003042560040c0e0b0030303d0a400e0503421341c01040c10101404c03050004c190310b801c115940c5002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 854462796 1250 854461546 854461549
    0x10504180f020d1b031103010b1207020a12020717070b03180c0a0e24211f0207170c0c040e03160c05031b1c150c0e130e0d030b 56
    0x1102c0c00f54107a00b0090160f0540650f0100c02c2d407070800c0d400c1303000034a0710440c440405a51021a81202c0300b03d010303181010302c0c080034040343d6000505240305510401c0804000580f00b40822500181c203900540f44440c94190041087c07a440c0500002641150109008240c4003030b090f1780e04100074682c008006030602203002d1801c1130b00f402195108101c22400581c001c002d200540c8200200180342e11010b222141e141e00607400b08003141e9004a08031480e40c00140c07070740062200c0c0c00d070b4a0304403041d07190481a84003d400c8103000c0d842006400143c040c007030001c0c070704622043e4000c46201070719001d20040e0045d1260038101505204603116464240e4a800c10415205840c55899541014818034a0240d0354145180706040c02801840c04411030b0654441c0c100007003035005019100c2d9086540003843d40c18240040032692400911303201d40c0300d0201c81c4140c0b03020200d80d803541207100c8003603020444260780030210f02d070b400c9050006030445400c01207014040b81c7c1050902141503a403400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 854464046 1250 854462796 854462801
    0x80a111c0c3e0a1e0c090b0f0909030708030c070c170303060105070303291005160b07020304030b0a0501061b050d030b060f0d050f010b0c0a0b04060f0e1506010504180f 74
    0x24400f070044981c402444c440701000e100b0019000c4d1081941010b07113941c40c3c4004c8190b528031341c242ea90100c1c0c41c01000140d81040c56139258020050310541e80390520550b900303c40b0f1340065501ca42d4060001c583c1c07904014516900e08003a00b0240e034440f6084190260310351b900c0c440100824100807002c6107450416020703030080046140214141da54083c03150110002901c501c1007898810000c3c00084070007140a40110340c49131a250701c1c21740c90300c00c90b5280c0c4040102d0180994045110400c0000080741307043c81010b0048500b104003103101e500d07040d40204120881444580c2c2e62510802d0f40300000e000040c120000011420041401a416800105c13140594012560040e40c00103007d0b9849005030310140c820920404070070071076600c480c1081c207103002d8009081c1d501e51003d06002d0208501c44040d5501901c42c00000c110741500c03503e103800b920301c003000540c1640d02c90305540c00300032450781a0907400030080c0383c41c41c01d091403c8100058000c211030b2800d443c0d03983d070115841080094 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 854465296 1250 854464046 854464063
    0x5040603080a0f12050702030d1d03040501030e031905030a05010b120f06190b0a02060136090c0e07020c01020c03060711070509040b0709090606080a111c0c3e 70
    0x702d0f020421791500081c00782d16540003813422030380345150a009192440d6100d0f901407480e189440114100390411005500030403441003007880504c018040042001c8a020902d41d07004029555640c880c2001c224080a4940680081030490004d1003103d06098801d4025541712005d02c90381415600d61030003085408500c80e0849000c2082c2500208244404000501c840c0c1d0040c0d003110348580c0c4c0c40c0450101981d10480d001c1d04a10140c0b01100d100349102c86126058090717500004046003640e407030800c0b52488c0d6116440c2510200304001c800c503011301134403440c40380a00141c2400c54942c400281c0f01c4100408000500c0700c4021200806501004008040c0c5005400300c2d03898102030600d943d50440483e001000a0000d41000c19080701b2030140004680d2542c584400b15110194448050040051998007000c400d005414020354000554500d10391003500010f06900060710050240003409811b82c90045c607500080351201410028a0742804110f6082c407080c41c10300700d043e0504403130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 854466546 1250 854465296 854465327
    0x201140f0702013203100e04050a06111603020a020a15080a0c27050a120302030426010c0804051b06030408031512070e0a060e0a05090f0d051305040603080a0f 70
    0x1404201e1007041c1510003540a0324a403401c15010030707650f1031203847c1e801e004c540047c4250000b10a40c0c00103035003500050f9815810203445400d0800d0440c580020815091040d4010b9000300f402d241542020001ca00c09080011031a039240882c40e04090b10444000e013921031401d5890980034003107446a110b402c540306681400540d54040c9410f48980780103140503d1b03104902284001401d1485007030314100e4541e05401a60403d440e0074842032000300d007101c6221200b56214130b00200c4071790a10a0342d55032162034503503440070b007400e040051801a40d06401d074000180351072406116591003046e40e9100e5405504903507a03544144500c00c0b02c400b41040c031500012642241c02c204800860070700103a5079071850103142075030f55000362070580306144038a0442c8102c10780416801d21f07464100a900c100709004841d00030200903038080c6031020b80103801c0001107010600301c40c404034408010004040842c1c05001e02425500d4847c498401d4040c00344c1030044a2007030580581c01104160b44102c0b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 854467796 1250 854466546 854466617
    0x90d080c0a0b010e010e06011e030b1210050c0c1e01020912060103031209021815060a090602010501050a0e0f130203030307030501080d02010e1b0303040806070c0201140f070201 78
    0x100c510784502c50400078007440703a01103e03400000c40d80e10b0300c0d420400d04c0303040c05a507041c200c07801240ea05078058008541280c101a01c40302c0070882519840c494000559110004004090040100000305e6401604107555078a0402007034461800004181c801e0300103d040f4a00341c80ca6a1162500a10440034199000240075210b407101020210340141202c0c000d44032079003c0004200b544003102c6005600942c0203144400050600402e80135603a80129a00c1a00790703c40c070000c000400302c2e0880340c240301c00122401801c0c0b000035428041d40c0d004203c2500e509420a04041c50900b107108020445a440b00c25030000800300c0041403110a656178014007520b03664104590010081c2c07900340196003051160003c0320130191300c1485080c00780103605024000d45640030740410180d5500715540b641c184018080400c20a03428024540500400d803224a980c250a01c00500106110284c94001000610550a00804c6141120102e40c0e0910300881490019180c03072120f00c80000d00c120b01e45a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 854469046 1250 854467796 854467813
    0x2160302030c07150804080901031d010f14090714132301120b010b090f0310051609031104020304080706090308040311010603020609060d0917090a0614090d080c 71
    0x40d0048000c0181c04440019507010544904802e000c0004141851000a41e10703400200440e07501c4025107280c10301490f000c550b0f451645601d09080344601c00410140e55900c2d01171056090503c030351a401104080003040c28034000c45169240d0000b40316060210380c10318440d0586a41c0c80a44a061034054041003080540b04e030803a15038000c03000c92440759202d60100100300310520010042100f54440030082190b800e000d1401c80a81000b40340c0c981025060110000e10f6406002c103402e24124004001200c1c50041200140068403942c1c8030140b14a80d102400400c3d11100f41c3d000c075080664015076030b51240e1401114034401c600000e0301403840c0800ca14101f5034007090340d601990003030ba1407100075041e034441203080315410300c4002d60003e001c0141281c24203065025080c8401d600340b00250042c019281c10291440111020b1410070740010b500d01c01e0b00d02500100060040c03481c01c02c10081c000c02d41c5a00700d01c5008402c62060140740b12100410a95008030740700c040d982000d903408007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 854470296 1250 854469046 854469053
    0x30327060d0501090c080c09310e060c03090601032402070b060a050411070b13050708150a020a08010b07020d2f0909071e05060301030b0919020a1502010216 69
    0x108002c0c010890081e08080003125001e02c5401b0007030003590a21505132504501c10100603091540342580500c0483c1e440e2119a101e00740803a121004007180004a001d82903020703240d052040050412402e58800c0c800d0210b20080001c415056070b520102c00c40c00504800380d24016041d45480d080510342c00081c1d02030030080000700840c040c0800703582c640b4405441e2801c00c026520111243c1e0030038001880404081071240305d90030f0b0802038069400b620055503880c1c5505016140c0c0102800381e00940c14469070000720540c50350321131036601c411401c2402842000f0705000041c4942200120040703410015552901c80e0780715200d90002d6441c0503030641e603540319030409220804010780402c122401105040600066105089060140c0100d07800c20300c840d402109030825070083c525181c0404a2581c852400943c06107005201e14a00384c541080020324141907600307004452814101550016107901e1701c4401612040d540b124540e0000141c200c1c02401507402d401c0403074950b40102c1003407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 854471546 1250 854470296 854470301
    0xd080f0f0d0b09060915060d181b030206070f020f04060602071d01031101140409110d050105190608090f2d0303090d0e06040b03041b1202030327060d 66
    0x507110008060100340052420030169070402c90b02d5680001c0d10100060002408441c13220680c50020076103401c003034100200404a8003080689404d070030b5400381400601c4100c403001c010707c007404154040101e08545c041140e40c007a55400070540590794180340b0440d0340c2c10308640e8072000007400c104505596980b0096590282e846980000c0182850b4601c90190086101d07050f203800c91400c13000c5081030001198407200a01708a280030600f40400310341c0503014003a01c005601356008035502c80c00c41c0b144c540112030b41079112511620b09103807030807848560b80005104035501810100c44950385c0d80d880c0390401c480b2044d458014051103000d082280001c92080e005840c0464082c03806440990230f866417880300303603040440c5a000340280359003035101d1502c40340b0760000507042038107082ea220981001170b0403c2e90b04071800001003407400300390303071031900b1610083c10000c5410300c2107562600826120b104910405040600e404c2011400c2100c602c080c46004001030112356499000d040c08200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 854472796 1250 854471546 854471557
    0x7150903080109020702061e131d0709030b0a05060406150329011403040314180117010501050f0d0e0a050f0c0109050609040f1d0106090f0c09050d080f0f 68
    0x7140c040400440c500846100b0b90326003543c01392001d4607012005180c5800d0040c1141d4505c0c00c0a020845092100c503224125401806100b04070401c15180c0f02c40302522000c0100000200000705000f0400f180c40b0b250300f650812034008000641c4c1d1200300c0480c000d011240c0003004401c079031600403584550b06600c07503c50594124410840140c20094001c01a012000d1a40c00a16840000c1c40500030441c01190024400c2c1080070581c1e4020300d00c0041e51f00b01411248491490414200c240d503001601c01001001c0d14851460030340c10640060a140201445003c203400301192100d0036070b070180d02550074410790700103d89045115180ca180e40c0d884c4240207100500644490510950190f0752070780588034028075040c240304001c810b01008189510b140d0380c5103921041046a040030168507984200c0d401d40002c500795041c003552405640000300034030b490f20f20341240600083d0344096540281e40c0c0031202141e181000d070408100d58082c10404000d103000009942001030f2501c8010003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 854474046 1250 854472796 854472803
    0x10f050a032c0a021503090c121c08091603150209030705030f06010501180e06060f0d15290d02090307030804140f0d0308151210051e0709061202071509 67
    0x2108176021002c26400143c400d04410350004801e0f04091510000b081c02e40c90407201218440c4150184140c03144a002c200800452140d8041c421540000c0c0500118a21000c203000a11450356594164890180301c5101d00c00382d0211702020076079404d00401d00244001403c8a40b450010a40951140f00a1003101e012400091141e4504000a1000d1044a0004140c0a4542e5658003807040300d0f4405000021044020021b81240f0b051920039003200e104040400c00440b42032400448032908600303072a0340c0681d40e43c5105c840c130221480071104001c2405402580300d2181c44080783ca8081a90401050035401180200d00300d4000c4002e40e103613440880e12003004150640034000043c2c0200c0001d000584a040000d034016182c3c1010300c0d00348405852400000d080d0710791681401c0d00745e06002601a12401130259040300e103000c015030038903040204041c1e07082480002d8081a801e1040d0000d0206040f05041001c540c3d60582d0240c0b07401c80707105040e01c220015020028500e010303045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 854475296 1250 854474046 854474059
    0x409020d0e0a1509060906020c0d0e04020c0a140f070905041101050c0307140c0a0e15011704060911220c05030c0d020d180f030e010f050a032c0a02 65
    0x1224900c5000a04900d8540c0040544500d5082c0e081c80c10f0292402010a0f68015241e035038000014000f0320041c1120300c00c100181614007000e40004050003102c0d031515110b03600500941c002000301042c910b5409900c4042c200821b200c0c421280e04105004186810a020303241c030004070044590071a52182d44101800d4003a0340740c902c0150358a001d0042a001250310030702c440c0f00060809601c01035465420003c461030404920009004071070141c100b401000c0801d0288001e5811030005071003200e42c2424003002980c8191140744448100400242001e61034010050602c01d421720705c48440030000d848464030003040c4000510700a201c2d440c80a0591400c071010841c1031080b07003a00e0054904441c1103161140303203902d00307001e074010042903e071180c5c0da81010ba0304035014100348410f0074443c1d8070007041c0c0c10090401424008404020505008110140d40e40c41640b100848911030340c1814001807900b80d444071010f144e602d1940300c50300d6811601456000910025411420034401c0780c0301c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 854476546 1250 854475296 854475311
    0x8090c010302030618090f1903080711070504050a1a0607030c150f1d0615030c01120e070609081507120c02010b151e0f09091b0403060b09010608060a14060405060409020d 75
    0xd2003480501c0c07880074001906100c0458bc1403446056072140c050181421920450f40f254001811100251449690a595a4a045500c0f4060181c0d184c0b20081107620508104a94034041c00d94503040c1c10080000115002581c1c0421480e48042c01003000301104029007010155001184031503a0202d903c1d0303104020000e0542004000c480700c094002401800318a00e50f10010348150640c1d00141300d80c0c40d02c81c1c00c4901036003c1040814020415556501c0e0010718087c1614203003800380c0304900d070000c002010004507540195000d402c00c1c0c04c103000018011031104c0124018144d00110381d030311202c0318030162054401e42d005094025140450b0b1603100e603542c801d540c040c0c4100351410005904c01c0c1b10b403000342e01c1c202186a602c40414410f420400789145540820f50340300e0f420803a138141e9a030810480745e0900f001d540d80541140d0510340c03818145800002c128121a110300030302c0203c1245a0f110035101c22040c1d030010140a440d144d1510b4503103a4a402a4200e8210f602c080c0b46030200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 854477796 1250 854476546 854476573
    0x8040b121602070b1e0c160b0c060106050711091501020601050102070f030b0c041205070906151209170a0504030506060607030f051810080a05010608090c010302030618090f 76
    0x40d1140c041242e800030705165152680780c460715000304141c0c081c0780a00c80c8003c844188804014081c6041000c050407000c4908041c0c00001803040d00140e15040003441503c9403800d0004455040d20001c0c1091611203846180c0030f128060f040405030f0304041540d040c4003011105103007031102c4090980035903919a0302c07107004a03a100002c1c818900103902c103070420404501e00b120b04580140030b1051062800740c03600b40d424441c4525010480305070380544001c0065000c00d01c02c41020f4600c900c0b80c180e00401c0071000401003080c40c540001050365035041b80c0d0810030000c02d016420400e02c1c01841c0c03900100c1c040901142c2141c80259943d00802002a00500d44042156032655242c0c842107040c91800307408031580e8210343c40c600b021a006a1040040d81d803039000d407040400069a8806191904111345402c1d10070607406041070201c90710512185020100d01003814000c03e1800588a54400c1e00080f03404608004504001c08a20103100d00d98401081c000302c50910801252201c404442c1e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 854479046 1250 854477796 854477821
    0x8010801021312020402041208030132041a09011202030f010c0206040b09010e0a06020d0e2d10021207110f0604060914010507020d091211010c0c0308040b12 69
    0x42e01d0005801c1c0a00050107910031a84404880394006000107090079240c1e101406070700c18010094510180100c0100240100c0c1c200d1a1a8035800340761005021503010303800749e17150b000380b0705061195440e4401d0f0650140912500550791000074145d00465a50b01c101c444c0b090b107071042c1070780039004421a50f100d5450500566114007000c0c0e0080c0501e50700c0d62a01026020080c1105805541300d0f9160380703054508010000340786000e0300d001a51081c16450140490f107000a0003000740d0429240c0303188101d07800c42d42c264800500c6880a0300f20103402c8030f00c0e042c0301058145030144c510100d0045a004205114284180300985504041041443c40d0381d030303961243c25a0703054590220000800244081d042035900610600208030074105d61128582507840494040006074040c4100c5400c1c103038800011001410000ea80405000e516200c11401d2040700400034140210280044104040805e0700b00081d50002c4c03910fa00ea58076501c40e020141e10000e2000700084110300420907004585 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 854480296 1250 854479046 854479057
    0xd2001090602031207030506060c06090c120a0b1801020d020301121103070f031707050a1a060a0503120a09030203121809010e04020103111306180f2102041512030801080102 76
    0x911425583c1c1d045d20490140c0b000900c0c03190000740c2800150401481000842d002d6603003c400b8265002c250424010b11000c10300076a600c6a1140c0b00c40390106400b60541134001d407580c1d1501240940c0e9110080c060701c964010401b800344000000524000c05001702d80d0300603c51201440d10845040415075100e0490007003060301d9041071000c10004981640c610145031038003c0490a110198445030b00701500302d8001c0d9240c0c40181a081901c560140035a0b41c8a2022107100d0201e034101800309581c0d0062241d8100b14000000704501441e0082c150390009690040440f481080c0b90490510720b03030422141009001c0b482da20401c1d080c6001c2141c00e0613120740c070b981240a07556030f0b00110060a03c0c070090406aa100700f01041c0b98600340d20030784000c0d00958403100817200c100c4240f200b1303504495000c09180010424140b0004604ca4081d915107800144500c5844040e400010700518003228440c810740711007680000e450301d0003003e441850780a5111941282c2e66060014280c0c072a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 854481546 1250 854480296 854480317
    0xa151104080601121106070f0203010c450602151501050d20040b09032a1e030714030d18051509030304030c0e100e0112020d200109060203 61
    0x18000510643d04c48240140e043c1d80990a519400000540070503115440000241d690426030790300d100c00e504090040050b594140d05d4000c54500c0c0070301d00c2520450882d0400d644240416900e940c0e0740d038250760b45d03000e400000600300b028240d40e020b0103580c03105c0164400a05100c01e100065140034005802c0c076502e03030180c48440c5842d0504038250000d2008401c94409015860000d541080d03513080600b000d421044801561070548604045c500140c03142d00c0e0603160059800244281034005480c11741d82e1003070f20641030450700402880300c640f400b801c11300c0c1c2504c10038000160100c44842684060401a4250703925215000800c40d481c80080340c3d401920000030004018504100c124400301c1c0c40300410007402e20311580002802c40e802135005841c03441c217001c4280088107001b062250001c0d0380c034812150440c5404e42c011540300051060740b0b0400000c40310101035485564201000660045c0c0c20318400100032580903240b81540c03280c0d400254503003004941c00c1d00000071184079940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 854482796 1250 854481546 854481553
    0x606091303050703050309153108070b07050f0703090306060b03070206070f020a080f041a04080a0204091712010f0f0812090303070503030112290f060109080a15110408 74
    0x4113510151803540c0060944074841c07040b08805001c115207000c0303160046a0040314203041e19112900414094a01007514020040300680d4000044121040b01c4000340c0c0581190990f0340e132140f058401e0300404a404412850000d07644080590254042080d640b00b040304002403070302d42c2c000c0b081501003216940d0140c1c0c01907001c280440c0c010403081101d01c400e4411280c0c0d0080307666138650f40b50402114400200300200d01401059210602021410980350783c85042a14041c2e40c541e03601c00c1d8400103030050b540c0e644031006005c002c1d50000d0315040c3c4210000d03a00c1c203509110000040c803d116450042101e1180803c1d03d129060224049400110040580e00342c940d10014195010303007200e507810310082000700f00040041c00035500030208000b0141c0c009015050401c90030030312551401c40d060b500d084001c415030109403440e4011504480380ca0aa0f61070340c0058800340d00d0347c0c00020700d5101c0d00602c401045201c44401c1c060091102043c0204200b420703e002c403074095801101c610380c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 854484046 1250 854482796 854482807
    0x1f140c12070c020f06070501150503010504120f0e04060e07030c03020a09170c0a06170601091a1b010f0c1d0108040b1911091f02060c0c0102070203010e060609130305 73
    0x40c0b1031000381105a0006000c0d9400b1070702840040e00640c02140203c40e141d44840031010100c40d4204000003c00007a03000340305034030b805d58840068a614060713101c00d108140110461581c4529007450701d08801800c01c000103030f110301d0840c0003000c045942000003410026151100c0b44071f070080e144403a1594036003100075400c18034416030621038500d10000f1403181891942840d50303121200001480c10b074440140c445181c034007030244818003d100707030b06014022000708100c1c0307644000c3e40354964911031b085813501c074090040e4003d100d0482015006600300b2402d030b410313991981e01006d903034001ea8682090000304d60355401e1028514030845c1c3d011858210000d0041200302145c03690181c03030501c030b200c0200300c02139602d01100c4150b0200115050080388011150034034150b203002e4900c00621b19015160349960095580c10b00810048525102280d04002d401d400d4066840e0154020024040151a80e500c90380e508800c4405521851252002c03520f5000380307040c10700c0c0e2903070103685403850036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 854485296 1250 854484046 854484061
    0x5060409150b03031c0603030206010807081b03010b1003020c21070803060d0b0f100b1c0c030f093f0507032f06010b1c090201021f140c12 61
    0x800d5004850760b0103004c20024a141da01c84006501600900090009600750460800170301e4800160003d8880d0392244005000e0f03540b0008003004043c1c607005403c00d90f524a0001300b0b0242c201780c181560002c124502c07030150745801d034010f08881d0320403c044130081e4038400c0c24503124800c0d402c40380390113500030060781c008107480000031644184080c0c00c03120b0302602c0380c5d80d248100104030741c514100c1d01000305125001381c2e40440100101188a0068240036031109400d01d02e0701250140300486070f484d80a16080c600a8002460084505800300000021410203000a108a49002c09100030003c21040b0008171406140ca46207403541d424000c2051601c0261026800200264140071740c4501400c22102c5500074003501c400e0724400701100425400280d45010410f810100d0449010720800c1c105da6100c0018102c00d0031106004612142d05000603814102401d03180c8001e03007840d02c4403501e071031060b40010040400c44804d42a80b680c0e6150003550a010b261152400581c1890202c0d040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 854486546 1250 854485296 854485301
    0x1111f0b0a050f041104030213140106111903020f120c0c060f03130201030f050c070302011505031213090204060c050d0509090a020306030c04240f050d1203020f04180506040915 78
    0x30116030b50007282c0307420b442c0c8e000240d10b035003182402e081580d15201d0400444050050403030040c602810400c0842901c08409a00d51400310001c0c00c101040748040c2d41818800c12283c06548080b400380c500c7d0032203489402115500051120403a842001220031290a010301290345811001d4820303403c40e2100b0f10756903100617801109074101034440c14840c408819610601d03000300d205008050341c54440b0700d0003a00351059480f514141d120015000c110644000c204140642400c0f0540ca550b002048800741c00613601e078101d03182161000c1008245903400c202c83e09165805182282c1c40d0800d085012182d92040d401c2640d0880e0300c1c6c4011480a684540181d60010310041c1030f01c04400655004c5011a01e1032481c16102200001111000c1903064140001502131802046401401c00000c6031603440342410051910384261303001c840e00c500c0f980c10f1b41c000d62040d4103507554640c0d503003080724031130b40c080f40e03d940a142c50b00c4082691490b05210300032000343c0c800707201000d0034981c010b02c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 854487796 1250 854486546 854486561
    0xa050715020f120703180e01060507080c07030605060114040f0509090307150b130e06040206032703280c110406180501030b10060c06020901111f0b0a050f04 69
    0xc1d4841e0302d94a8092050501c12070f0b042554402c081900c4400c02e040041174240f58820b020101c05010409001c41410200ca07603040d20440e041c043e5a0f800300d490f00600c14450742c030586000e4000d51001008100c070607001a40035038001d903500708040c80c1e0014040481c1c403e0381b0810075003812105003040682000c0722078540c44500081500e08084e030307903291410305400900f10510302c40c0d44c40550000520b480780c0280d0720948002030400c50500c161280b01d41e20f50020b00043c0c426800400050088011484186607089410380c000c01d99030f240f0b0b6107090b907a80084400800e44070707500000c010100012078582480940d183c0d9840c41111a40d00e8003188480400c2016030002c1e1140404600044200704a4225110302100094a90300d1804d12201c201c0c0c000d00b03a0200794070202c2c1e0801c09940d200f02c01910a44d0031110040e601c4c49540010f8484000320203d0218034080d50900c0c0c00d60311750614240d414410203000500001948004014012100e07003d46584211311038115009030500b94028074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 854489046 1250 854487796 854487839
    0x3070e010e030f0601170f030301030b0c040b0d05091b0d0f03020f0129030309030d0e0a120f05060f0606270405041b0609030804050d020a090203091501080a0507 71
    0x9000340012010a0400012000c2400f4981c0400d00400c10a1000c0c80c40582c848210000341a0001602d00005d441c0d100c1840301804c0c180645011402c03450300c001c115401001d04000c7d150b40c0e819000400405042e040300c0c10b808034091070120f40100e90035424154404200101400810f840d1540c2e45200c8142076541942144209004003100c884240715002a46603280c00d1125500442c60303d1351001d000c2849841c0c065042484a0705690320001001b00182010f41801c081079881c0d03c01060f50700600b5032042c000b60300050f075500207000b94221905051030140341607030810780e2080840010151b050303e00c43d070844001c01172551482081c6031144440d100429004402682050010b400d64105540c10b91b80c0b0a62400000d0b1980f0661540d071005190f0b80c14015401e03844d644800103280110301c169400b0340c040210801c115625541c0e40e20150944070300c1107450b401d00e100c206564440004500400c0c401200001c91180c40000d0f80302c1c0300e0b0b03900c000103200321414960258941c0d6100b483d0394 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 854490296 1250 854489046 854489057
    0xc06030c030e060a0e070b040e061221031f0e27071e0905060607020d06020c070906050a060507053703050a09060e3604050a1109070503070e01 63
    0x101286010302120b4002c070040d60010407102c0b811704551341000455032113000e400e20100710410500c60440c02203a0312400440c0c60b200c80c14805003045d4241180031200c5a00e4603840052803220000070f002560240f10081002110580b9100194242e603540e4012800181443e10001f0300814042c4004a440084250700c1641401d03050030142c9801300980025003901c14844654150398001114480200074040701441241000804100203214005019000714412100401449459011500c580c2586021500300d143d0310a42d41c2c00802850083c2132055003e200001030b407501c5101654446034114028280b8208400220012800b14011a4242004141d100704480c0060450031822900075100c00d17988814203100201500340c290484000d11107404501c03a2680c50324002c0c82e1000c080c442e2500030084c1008208da0442411403400d94103501c100c001c00041140c00703d40302900b079103c1c1d007485089440d0341c01040300480080f12903100180c418800140c0c0b0034862510342c8003814060402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 854491546 1250 854490296 854490311
    0x906020a260c070306020306030d26070c1407090614010e09220f05060f010b0304031103041a0702090903040b0708130b2106060a1d1302071208130c06030c03 69
    0x100343c02c101c0f20764820f0b241254080100107003401d0502050484142500e41a5424103002000300d010070350031500c00c4a400c51344030010742050700272807072070300c1c041d820500318160b8182a01103260b84940c0ca000b03080006040030b50001c0c844228408a69106030140c40342e540e00b40b00201448580d600061248400d0441c1080c80500c140185031a0817165001c0c1141280c01410703814000d00e0f00c3c102601c0c112803034080000403c4100c0e0803a0070780b900705605140c90610f4040c060601c91460041c1e0b0441d034111001420900e0100540e580101181ba2003564610400e50b41d404400751240250b2081c1c8880c0031003041140c0c001000c5070020425075002c41e021100c0180c070741031140303040d800a4414031850401c2d036078007925208581560a034130413400c40d00301d440e10903210340040ca10300003240d08480f042c403558803403152560b40002c05107210014150842d01c0382160304010b048180391010b40000300e0103800100317980000c409002211076410104100000c1e01d000320842c01852000c8103d410565501d0703e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 854492796 1250 854491546 854491567
    0x10e03091e0603010e2e060e0a051504171617070e04150b041e020d0902060a020102070c0b09031908160c0602010c080f0721090b01060906020a26 64
    0xa94040c10707002c3c42417821442c0c41d00c0c41145c804c1128644075441600d0340c64865076000407a4803201a21401d14080d00e403003240d10301096220310b054010641c4404600d84044540c4c50390009403003202c0d1403907040d030821044083d2450315a4140b2549000110072040b06000c400c5401a803101540c800b04201d8860941d242004200f101c000c5c1c4048030400f489406000e0f451206002d8503040d08402c55013000540888001a0312140000740c0c03402e2043d4010658105081e1154005003c1b0368002c0c01030781e5125881c1300c0c028002c3d40980c0c0e04542680040c0008241e00040b001a10030140d00a001041004541ea03040702002c84031900c116020710303042084249124002034070696040c03041510400c403605040000c3d00b5100340d03103100010400c850082080e151400c0481e5504000d0342d040074880c5c0201c1c4851703134500c50f08007805100c04600300417004041044c03900b50f45040790180c0d0748010302191202001c0341c80e5030680a01410395903070404c070320035507007850b90148515003481e031407503440d0151880307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 854494046 1250 854492796 854492809
    0x1b081c0e01020a1d032806050910050714070204050c09130605091317090429030d0e09042301060303020f0c040504020321130806090708010e03091e 65
    0x1690008107035004900d20b2807040d000352041c00b444400080c00700c40c6a0f40b2001080d51001000c0040019071070080d640310020142000418449030042d070248143d00e403070000680c0d110803104140c080980741c040010700c8940b2546151071003400003881186445583c0d000c0102401c070103040f07111503000804c17640d1400c1c2ea4401e40c03095403eaa402002c501e00b45090104200c01d10014900200b80700710344600c0c00000d00c0e41d941410b6000e401031045071110050340105004041c010001d00a1065988210b03400e40b20098040302504421401c960136000c40484c116031980241c01040d402c068130102250014600303001001c85022030a489654081c0c41d002007a00790b503060352090340581c2040300c100304c89070020f10031240c204000340c805000c14141640465901d001d4680d803041101c1a1071403030008118040122043c003c40004035050b025120806541c40d00000d40d0703c052180f055000c00902000180113000d404441140550b003000d180c3e605128200d0401c2100440c0319851000055050344d070703034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 854495296 1250 854494046 854494061
    0x1050d0c1a0405180a050f0c0a1d0405010308040e060a1212021f090c0b030408040302060c0a2906031c0f02070f080f0f0a05061b0d090605161b081c 65
    0x1540313203641c5003032100300d8a080328005024800c86001c10340c1045440c400300422100c40d4072907898050030701d408c02401c4140542071001c0c2542d01a082200000c2032000d4200640183c40401c2403036001502d4040801803180103d10481c100e01c2100360009001ca0140402400c654146005035605520b140040c84110312284071342700c0e032442d0b0700d680b00b406200004148501400031060310030b1440c1040d40318a00315020794070000384a5100000c10071ba690030309002c0c03c80e03450f81c09005080701065511254101c05001030a218080c000100028200d18001646005214880184000d020361140040b078481d071404440e1815441106000a40d00020307251090080206001910035540d4000c112030600c07280045084065006003080b001040b00811859007100d01107589540b0310307000d242e0800e034900884408a0078a8039100f01130092141e1600698498110411802c8001001e48070950b860800c144618124030302c0c08075000001060700d4000c0108900503400c03100115003c0e81403100347c1c2d10702c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 854496402 1106 854495296 854495329
    0x30803072606090919081905031009020a020a0b090304080705061c050a0905010c0201060905100b0403021314091b0a0b0d09030905030a1a01050d0c1a0405 68
    0x40240c2c6041d0305d06851032440100440c1000303c4d207074101152101c09040c0340240b07903414501c5882120302c1041d0718403100c290389044c40848002504004408000d6208000da100c012405050b050744c49080303628001c41d991418480e0b81030418002d0ba000a004160030b214200c03107912512000c081c0b0f100142d000040d207a40c0c8018510142420321406860740d460400c01d10340059040d0001c806452450381d042c8071585441c640000900c10b10703c02d12410640a01c424401440d06c81c1c5035241c40384040c580403540304510304500c260390400351400e10090340008134200500081250006802c44100d8803144100d1a01ca07541003941325110b0784000301651341070444105401040060082c02018007101d21115913458468044d00d459038403030003071214002c0009014984440080ca80503803215030444d6161034001280c40174a0403039021039040e04107000101d416241c000e40c0340b00c204103 = true := by decide +kernel

theorem cover : BRFrame.Cov 854316546 854496402 := by
  have h0 := BRFrame.cov_init 854316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 854316546 ≤ n) (h2 : n < 854496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
