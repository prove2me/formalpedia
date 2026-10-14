-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:18:19.769231+00:00
-- url     : https://prove2.me/submissions/36ac4de2-0e9e-462e-b4de-5bdd27ee104a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 200359712 ≤ n < 200539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 200360962 1250 200359712 200359717
    0x1d0c0105090a030b04020a0815010303021209100509030a051006050103060902040b2a191101080906130311070605041d0106120e19050d1116090b03030408060703140c 73
    0x190b01040c86942440051103503144141c01c030380301410b4050740c2074842a03601d007424214114049031803c403800410606034108401c3c07840f0b6140449540c03414040001046035400505e00701001d214000491103400d0318208035040000790003a0035104c400e101c003d00040503001c50320940d8006401d103500814005c0191003210308440881c11402e1030324910400c80443d0401c00503640b1140c3c0042d209801160005000d049080e409126000618805600d400c1150150008803c0d0401944c5e41c2040400d00b400158603030070016030b041d600b10409451900311a08940006941302c203008820000600c150400003410030b07999000e82d42019108420502080c138402403055000107860a8400c1d044001198001910f460b640340a440c0f00809180c02d500c0291700740582190686d001c194030011007940070300307402c0200718820040c15280f2510124650b2481042c040c07500069030700c140c406201d80e401c200b141e0080c4840816120b8910304000090020046980d40445007400480080c2040022004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 200362212 1250 200360962 200360977
    0x50d0216080c0d1b0b030421030b0108010501030509030d021201090b0d030f0c020111151b0c0a021002070e1003060b09090307030305090f01110309010b01020a08031602030d1d0c0105 80
    0x43d540500900d0f0300c40500d1861910b1004002a03441640411602000d0300154456401500707102000b00110907444104110790500a00301171501c4031600c20f6a034400341c0da83c1103880c2441d0220b90358407600807072800d40c8103008469030b0f424800034400205918000c4140c0c100d032b60500b003c200c008046400e124080031880c2000b000140501001060b21303009040e140c1c401c0e4010b16000850300d40340400e0b5482d100c5c0d490045920007a90f801001596604200490703858040141c0c03183c200501c001c82c0e65030344c003405d0320024861059200d56a03035461003000004004c02e0410f075000c0480c01d0210800380b21807118001524098101442c0074214180801c3e483c1c081e00440e0003e61408000751000c400400e40070b842c00c2e0440c0925030011143c12424041c81d03510b11001c2200d55a241000610a4210b8080307000840c1950001004040868501d000781e075480030b0050b84203d8126103d0204030b0552098400300d01c6480e14054046030407a84140200b00345030f21b01c804079030501c9042e000640380f0340544034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 200363462 1250 200362212 200362219
    0x1006080406020309160b070b0c0f0d0504051204060915050a1416140706110118030c14010c050415031418101a0a0909030503060616050d0216080c 64
    0x201280014400c0c1d4029a0b011240300203650400100c40700e821109443d83d80800d4031700c3c002240caa010721403149101900050a032038000d1401c4404040702e9061302031300c0d601001880e07940c80040c2c20f1007400e10118510841811000740c1d5542c8421001d040781805001c0e03005441740d44441031010500030780454907401140d45422101090003000140c1c1a8001c40f00311450700241c01084000038030b010440c0000500001c082e002c6142000402002400b4020440c05268145503500d010150f028000c0c0d55071582610308424104090708004880c1c143ca178103c1025503103445000c2142a9101e809030007034400f400c24140603028038010440c1901d2510304110b05018150000c1248000c0740e9a0140c00031003070109850310b1004070840c0504a540c80d6020000311100f815100d400c43c038000c03040401a04800c40304100500352a18014410700005000c00c0c0161000206480250000701c244940f070340d400021982203103041c0b48002c1d1280f0412925003484030001c00c020a6507080410401100c10f0080c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 200364712 1250 200363462 200363477
    0x6090d121202070c090b01021e01020405131404030c170c0a02100e03070509060103090506010e040302190f020d151e2d050717070302070b13020d020405060a170c03061006 75
    0x11921030091450214640c1984109c101d403544444c0405280240d4481c03010005840341d2810040c8200f1076014074440504030716110794084000c0c1c6944d1006c1e00940c141c6050012820700f481c066506400014520807004d00100e248484080005542c0040b00d02c00c3da40019540d407983c205642d4584850201c0b40e00d030300604024440d03420035400e03056020b1f8051601040742e81c2c0c0c0740c5070705003010383c00c0e0010a4004220402c00c41415010444162035110003214001c82000c00d803078083e804402848001d11800703c028903441801a1150041110902004100141d82c01c40e079540b1001440ea10390b8591650925003403010320791050003801c15400c580003c541912808800c0d440c000c10000301304070140980e0311203008845650103e080c2c8244500c0d18011b1f603824590a10980501000b0510042c10310110b00d00001a2946010381c0c6802d0382c10389010031107807903009c00030f840903540c3d030010146290340e1500d038001818002a803401c01d0700c090f0706031002600ca07002040d4074007050f8028040071482c0d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 200365962 1250 200364712 200364719
    0x606032a09040314120f071103030127020a030b130605030d050d1805030a031b1202131e05090105041404300801060f03062306090d121202070c 63
    0x31212140c1c041c0c80f0385050b030040d44070821645255001207000503d20b642c14010011601e00b03016a698215810b4145080480440f84a8507900d01c014003c1064010881810085820440c81c01000c002c0704041d007591254402c0f60024001c000d00d640d1a40715207480e82554420511030f2103190203490000d0050950540140d00503503540d84820800d003c026620317501c0700d40803028001ca80f0030991254002d503543d6010940024140d4886004074a21466152801c1c16007a8000c800542c40700e41c0520003503102c001e4035401e011150706c150302c1150103200c110030400c15244101340e0342040d51411503484c41141d80302c0c020700c4103e03680b007040f18040d03894101c0800c0c0450150f64481e0034408a50f5101401e0b004521280098042806850004211288014420b094100080001c0d1884034070341001308901c0d001c004c1040c1d84522040c11a070035817500c01c4443d152140e408480b1644006032145507060540d14105d00040e4400c00070500059080c1c4051042c503602d8001c5850107508203c5c0c20b803000c0e08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 200367212 1250 200365962 200365969
    0xd0f0b0907032409050718060813031701091d0a0210030203060a03080a0e040606030b090402060a051314010908070605070206030c040302040e0105060301111c0b0f060c0606032a 78
    0x1008120b10405202004003961002d000540c443c02038006854082a43c3c03d1007640680312003c00c0b29189584c4c015043c0500609034401001a840540d5120100c841000d500f42078503014415003803451100b40f0203001090382c11540d08409948074800d180400b4010301000d0b01510340c01c40800096100c941c20000b0403540b48250051a0010300080c6506080c5a580e40c8224035944009201e40106800302501081c0b403038030f40300c0d0b04018081414240607401c4c071000025a01792000300000d01c41c0c000858182d211520507411307911280005210014520307290300348503c4808103600040d000412000001c5007019010500c5d0f4101c508907180c190501800360708021003030b00010492088200b0078003000000d030f07841d4007038901061451350001826040070001e25007541c10f400c1151992003010051081a40001d220040b89004481c8002416603001c2000070021909003e1460703008901040d07420800748007246650190b081141200c640e103110041001d149039101c845d04503120a5883d01500300d04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 200368462 1250 200367212 200367221
    0x608070b0f041208250201080105090402030d0f030b0406030c08010c0315060c02040908180f1002030d0506040603230d0903030f050306040f020f0c06130c060c110603010b0d0f0b090703 81
    0x5100359680703818811320351013001d6550100b41000003580c40070404175040d035030880c1c8100e02500b000d4480f981180b81c5900801d5907064045403000812604c0b030310004c00c040c032940c0100b0780c4010080041c00300325900c0c00c10304a032060700c0c050000d040d480c1481507103c00303004c0c0c41031604421107042800003036031402800380c031650b17080034041c0d0b0840d855400003000a00e4a2004014410410f0b0300341e407080d04400148012582460005070285c0d1410508804040d0008203a03040030300d00000109940d074440380840e0150074a540700404014074459600e10401800c1225018000160101d0740e14140d01d4008a40003c42d621014006c41d00d00300c5800078040c400c1004561081c0080c0011601c1c0030560b07001d40482c1e00658111b000c2c8000480d007500c964105000450f000704030b41003103054042c899111501d6040f018441c510901002d2500d440402c0510507146081d0440105a940c9940c0c1d59150941e140d802040b403005210b151050503001908103203d0b001c0c503801c01400307042141e9201d94042c0c0080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 200369712 1250 200368462 200368499
    0x702010e150c0d111e0c0d0c030210030203040317070903060207080c070602340b0c070308220501020d0c03030c03090c0b0a180e04030509060c0607030608070b0f04 72
    0x1071010800b0b04807101080100036990708007075403200c4c0c0060881ca40e2508100b54000e4541840c2980429450300b81400500c0da00752600480c1e072211110300303914108000f0f8405074402904040300400711190990183e0240d403041c2c0c002d440e001000248e4841c11801e1003801c035072900119451090900110742c3d81c0d4090a40309124914141c03030554400e10040c6403810b96480b900042c1d01c100400301c0c4030300280c140a0144039400304c18101d03201a02440f0001c1407154040c13200310306008101a9070f107000401c842d000450308a24102d680300e07081400e45901c183c24561018800c0c86080e00014254800503140c0c00300581a5220148081e041c0c5e0101d006d06a0814020205a1180c03010030108100c003071004007c000c81038075031b0340d2003001d1b440280c0310113903601120621101c04402040381230384a100e0154070550500e046940d846019001405030700440315400c526118100c10800c50381e40590080c01a18445012242200da031003d0780c08613071103180d10220220105003c10085810781d41c100700c80d01e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 200370962 1250 200369712 200369749
    0xa03030f080408070519050f0c0622030c060804120f0c0b06010e120f011503120809031204140f010b01050403020f0a0b0c0d0f0e010c0b0a0f0c0207030b0c0702010e 72
    0x130483c050b2034141c505810b07200c3d2050100340602c070702001c204040248151007820744014080b483e403d0300000300725019040d0704034003204280d01d00c42402c50280f50305002565002e000d10003815102d40c00107064007402c46003164141000c0d03e00e52a2240268000c20701101b40d0b6032a00003e1255072b4900010000c0500b2490601c045900c50030b01030707a2406490072a07100f01c0401884404c05a4040c182541c00045001a0034082c00d041440464440030180c42003102c10b007440e50540d165084400e207107201ea643c004c10000c103058248001c11480c003030f00d01040b01551044031080202071001c1c0d400c95103440c0003540032460070003040006040030300ea003025200009051201e51541c8214218442d031110050b40869044251164803880e013009078502034007118500340d400e1450100000e040c2d508802006415881035400081440240780c01503136850022480a1260724901172001e55120313014081164668886400541908022401d4540e002e405a450400c0d285561050019404000701c0243c1c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 200372212 1250 200370962 200370967
    0x6070809180705210c04050d1403130303030c02070b1804020903010e010e150c03070806030f0a140c0904080304030309150510030c1e05040519290a03030f080408 71
    0x103880120791800340c4500403070b4959598911040b001400e06040811400209202104c240100455200143d0381901c0d020384074521542498181404028002e0007000318620001400c1465140d2100390310703013142d2080d1000d01c403414140d1001c0c0d8407064035016030702400fa81070103c903043d200c0342c2c008940300d0b001c06080107203840c540e840443d00b9154411075030741c140e1b0b441300c10440440004200713800e11005032510b203055909192900710b0244c030018054004220180000c1552540c09005003090800c1d400d080300d000c2c03a05481c02c81c2444525000a01b0180501d181090343d03400c01c07c03183e51145078803c9001c1d246599555065005220020041c1ca00707100b020b16510450806200c3d19024440e1210b07229001469450f025070502c03110780100d80050200700c120802c01c0e900555200c20b03031b03400316404961690381070b210300314030020b152070041e41606051f07a00c21954074548007010031100000b0900c0401510100340326960544d407000400042c3c14602841c1c10074441c180b22508648540394151 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 200373462 1250 200372212 200372239
    0xc0a0c02040515100c030806040203040606080a1214070519050a0f05100c17040209060111031c060f0815070c140d08060319080d060e0115030b030c06070809 69
    0x1400c42c2c074221441c200d40300e00310107007440500d44410b074201c40c1c1c8a1441c00d0022040c290b94010b00c00080a82001d00458010012a04001c0c0d603130000000b82c1040d004036040410141042d4290b12100e612180c04219a0015941c0703504090003101c04980c0c0107030040440f02929003941e10121465003040e0380e40c1c058014440c00107548612007203d001e004600074500c00d4500c1020380100c810b250030310be046c0310206c010303a5641165100460b5200f601201c0c1c101107039884500503156400070424918081c0400241010000302d502c07400400141c40c8241001032035112501d00e580319182d802404250b5111040350785074101594009a0f100d10b95150105460000380c1d0380d1281521005c02d031005507080814520141584480d10b10751165044004003034000c00740400c101c5c110383c242c0015000e440d0000345500c01d4001908080000c141c6e00c4000c1d0342541c5d6407031000200c4406c0c0028400044c1c02d16071003200070701d000240d41132852402414103103450455500c40d9040e50000200680008485c081034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 200374712 1250 200373462 200373469
    0xb07060615050d060e011809171606050906010b030c0d021c050a05071805060f071a0402030f0304031208090a06150911040b042705010605040510170c0a0c02 69
    0x72030991503101c0c56114500050420242c6040da00901101071070b400c0100084c0b2003245107040f400310030b03c000098603010f81c00c0c00200009800591000d0f614002040c40a0000340d0192090042c0144000c00c0fa81e121300d1050350301d0308800c0c0324160700414240041b0b0050810b120041013103000d0041c0052510040a16459034024401001d8003800d9503101040f200300380c41e0040c103034000da103403500c0da50901a04034100340d1103646014032030041902240c5583c5c404907850445100c40d4000413800380b200d40004481d82030100c02c07034089000b409886440d010168000081e90140c1f0ba20590485140c0381030300c000c43c0d005400801030f014501c00c980240e000b01d80184200d0f03404184140c2198132460500a440c01540e4800d00c031b278407008504010402044034101c0595095802100626541d1600405103211119001601810041c581000090b03582d8024004100700c800607034104540707a0b45058140c5108865a85603140129804c001403000c00300000184050a4103040041e4001c0e2a034011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 200375962 1250 200374712 200374739
    0x10c020708030f030919060504140307051c0309061b090b131514030405011b02030408060c091f0302041805071b030201150e0123030d08042103021308160b070606 71
    0x10341e0030707940d50014027040c4400110070286c0401c3d88401985406c5145c2c2d074490391018070301d6012500048035090140e45500c650406040301e0b802c81c40510001052661100740c40d003541d02c2100202d0b42442000400c1c038103c8040e110b11001030511002a1032401190006240d1103a028804000c80074800900022500c40514015405000006070700b542001c6900140c40314041c088095610501080005000020b061548800400c2d0b4040c0c0722000c9101192401045100500340d62040003c5640d515900d80d0142013292545000250840c1d903484500045440c195030780000204060018450b68480041c00f1850328480d01c00051401c0c00c0001da100e8a2060743c005180014010004202d10364060400c0100e160082e114510107800d13100000c2e603150783d5071010500b401041b0300002c2c20301c0f40b0314803026040900200c400d1151601d400c9d0050095014244085504c54101c1c0f01191001c5d000402a1010000303404111a03d410b0218144154101040891b01580c13121700c0400d042c1c4041d40c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 200377212 1250 200375962 200376013
    0xc080d180308040c211103070f0303050c06010506180f030f01021305120d0215100b030126060c2208010c022a0a06053603010c020708030f0309 63
    0x2650519801c0c2403400d50b564a6085d0b0046170b2103800e100b610780714070004e00c41c07080256900405510000300f1002c0440c0c28003030140c0c8503070700f200e0601c0000410701d078011008141d591007020564030b140c0e0701d030000c1140c540612042400800f0406040a680341800d0701154040300c4010111102c62005041041c01c0ea800603104c01411504080100400d04007009404240303604080900610580d424000395910001e03006554218440e5002c68103a000c014010000341c039031181d40603600d40e100c181910440704402c0d100400d4010700d05420900c0383c00410824000c00341035000c24a008031001803550455000c8202c4c51812000707240003c0c041c44248030710503403540303940c002d0200220240307540444100340304103c00c89249003c01d03591507a59842903440070384150f030a0091700e501200d0040082c2205a014404121400110000449201003003c00440f00300b20000d2103000c050442c22600d891341481001c010360b0007800700f90011816100070310f074041200c01c100c91961140000000c0300121004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 200378462 1250 200377212 200377217
    0x20c0406030c060f030207050312180303090303061f0c030503060f0303070f110d0c0b1303060e210a02070b0912100902130c1b211812030c080d1803 65
    0x10454203802a826904d0202141803c600701140380c1c4600d600c0c0c2c490383c00f400c8005038003413000900c031ba03280c082030300308070780c1d80008032a00e0345000710515030389600680d8000c0c45014501184507030512040c040c410040070b1943c2c0e0017a212404d650a45c0c107600080c014560100c0c803da0150100e03202000500b00d01c6025044920b0101c00d2070070004440b050610b803140c0a0590174070380d200440c00301514103040b03a01f0501d8899480703812110752943d0007540d802c0102400d04020508944201c0091020340701c0505200c410f0200c200001c105501d889003c5000b0301580214034100492030842010300f060307800c06440c0006030540d8882850800006170004030086585240d8541541010350415849048040040040500044000d8080311404007a00f410b01c00590b00c1004122480030f10290b505c450003080f804014541d1006484404912004540b50010384800582d001002911403a002d405841d0524401c0e0680c0355a0352a40c00780f145465001c1d1074034104d1700300343c4800c00c821801d6402903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 200379712 1250 200378462 200378483
    0x90e0303040204061208030708090a060501030b04030e040e0d030e010e061315020909131a2d13031b05070b040503010c0201050123120d11060a050c0a03020307020c040603 75
    0xc0c41000104c4a06401800c25400c0000c06035000903141e00842e074004c07207103050440c499030f1220480751034038111040c014076150814000104204010018601481c03094480895075001e0380103100c2110280d41c07469200d07074000342019035118080d0b8003201d500a035000000c5501032078603440501e07060065400d0100550f03c0d0301e074042405640c410150b1682039003034003546800c004c1c80001e034982c0000b0b0018480c1c070343c18425440800c140c551074003202d41c0c0c10701d103601030f2440c10f5100700d600740c0c2d10810080700112701451003409000044480741d101d0b0a09403a8540c00080e00d450803203000403a441c60703901070501d40c40107a002c154100031281c014200d103002541ea80f420901403509507016a02c1a1041d6810035005100070101809800c00c50289801c2d00340c0090120b100062014052101202042c00740710260f0407000e07031140803d00d822001030111402525824603a07000c40b081115040c50702182400317040801440b030f400071500504c0718030490321200303000b0000404a81d1694422138408044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 200380962 1250 200379712 200379721
    0x3031b0a0c060f022a010509060d05010f05120a0b010b1c05090a06061502071802090a08010b0405011203020a08030a1b0c200105090402030403140309060601020c101e09090e0303 78
    0x41040205c101d010342200100800c050b00708062001c400101141070090100d1031100d6a219030050b0f40380501001c1061200d543d45e00300c07220030f08400c0d00981f80980c00d25040602c25040008226001d55805884211640c1c6003055242107078028810101c0c8040362410290304000e1381c0c3c00340da40190122005440d40c000d05261100481c0d003550b010300d1101c42452610f46a89401182e040300711400020850114000990760f00000d01c06d00809942c4840c0150000c00c158030158000305034248252400c00140c2d0322991025103011100d03200500581c0000014400950040003950301320407400404600d94100791450400c01c24403150741c0d4002014074108106000d01d0b04403003070402078000d81031400c2201c2000000c0003480b07480c401c0340c000c0c2e400002103810103105138890340307000d05039000070750b128149076409903110f11050b41d10b0b50040c40380000a050394602000360580c035002d65211440010300d504a0041115082200d5105012114000289550442c000c01c281203c40c1406165203240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 200382212 1250 200380962 200380967
    0x9091008100504030e01180513200310060c03021905030a021b1c02120d05030117070605070609020f060a180e0702030a08100306060b0406110a0203031b0a0c060f 71
    0x142011001075007010280008240c021380803480b044030a1030404102d41c407004c032655664001d0b0313208680002d45c02850001050710750344284000c0e010109060a450503000000c803042c0426520314000f404601d00400159018000d1203000e588240140d8644505103202d181c0c2400d40280151400e400001c1c004e650158188810405820b601c80b0841001c1d40d0040030407208080754011001060304401d0b44420b6540300c908031091403615500300d0758114134000004150f07400038411154012400582c80701450008900002500e540307035565802c5c0f03052501e03030780c01501d4080f8080e604100036580c6100070344c4404008140c8881503841c0c1c01404010402403031508480341e800f0101c2110340310f09005440c1da0100480310000f24614102071181c035215080c3e0b483c80941c0d4801030015241920015110701c003600034000300e40303039034496400d1003c40000d21a12500d14080080d45500308100c513950710743c8200100c0900b016460111b8012112943c0c1d20061f81445801003c0450540c0c60000462503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 200383462 1250 200382212 200382223
    0xa0209010e10090b0c0102070503040b0403051009020303030402090a0b0405041b0641130e01061b02090c041e030c27050601141b10270302010209091008 67
    0x36070b240c800c500650403000302200741c00e008180141c0f10001c3c10b001122001d4040d22141c40e040002d6958135550790100311429849803000f1a034900800c0c07400801150640300d140c0f002da401038091450756507158200428440000c00c9005001e94840c24245941c031240300e40c0b44503610450f4106101341d500404070f80202c086502c003808010000f0429462024402c00ca048007861400d02403514501041e202d0001c20544800c8444000002c01c40302c510551480d000c1d4121800c030f5801c48216601c41d40704a80100e01c0c3c05081e40c5103511500e41d0320040c1001c0c82034a0748854440140c0d401c00703032280016519480c84a010900b80a1040707004e1080c803170040c07040d100429400d401e404c0d803692803d9445600c5080b80e011080c0866a0f0300000e02c60f41d000e83c00110001c100400700070355802d907603200c24030100701c0318144079424400c600c2c0c50080741220348034a032804050550840007004108045620140d9003650460840d50280105203441e00c507000f00d640110118030f2561500703418400d00e649840c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 200384712 1250 200383462 200383487
    0x60d0f06050703200414060415170c2b021e13120209150a0b0403030302130e0601051204050a0b010b030901050c090f0d030c120203130506280903020301050a020901 72
    0x10480440389803002200981202e0884141942c5064002c0340d646c00603000e801030b94402d607209000003c10302c1c04a98000c000700044c240e10600078086031100650b00f010ad0103528220315182d800102c0b01070350490b20281c00720000311922805442c00540d0343d20b2032040c84515500054100c0c000c10207074480340104c0b54042c0036010003040401c0100142d000144203040240035001c080c0c13200c10b007181441c1c4540c401d0710050400c0641896a560356440d0080080d4800241c0017202119884046900704e400306505008150585d1624280000c03911049820b82e07010700200c0352031141401c0400011041c01402c2d0007411007410240c1c5074503014981c2400d40c0c2c4003c006511121082124420a030344143c1e1030998004161000100b141852406071080003881401515510040741c041002035070010080c001e0045030903504612075650700a2002e5401a0307403680c8c81c1c501030040340c180800d40b10703280d460f8840258a00300010359602d0700440c0c212801640c440b0440b0f60000b03001c40342c40d600100c0c5001c92 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 200385962 1250 200384712 200384741
    0x60415090b03010b101b1e030f08131203150f03060902010207140a030f03111203092407050a05190509090105060304020906122506020c09071403060d0f06050703 71
    0x8504a800020603907068452124a45c3e104000d4480512501c802a20740c0300e64030942e80e6900c2403090501400d00c031002c0c081c62002460502c005a030003142c1d00bc0c00e0010b203a101e030000d5a001d607403007411303005801100200e007040450710000286c0314840c1040140214051200001d10b080c20340002401e0101035004044500f88501d042c54254440300d05d0b1500b2650803200d2694140034600d0b085502e500040a500a84d21a1200403000e1071032100040d03004030140c90458029900b006031103030100ca601d0401000c10726020002901d110300941c0200750b102d4861815600d44820440810740a05c1d00040001c000b4401080503005418803120791800b402084814900f545419800110018001442d280c011442d12440000c0e0b05410084001000602400701d9420644001c0d44040b040803403049000610600c503a069842c01e0003610540035002590b1340c012100c60b21058000e05502c060501604445e0355250071000c11041e07050000424820300f030228403420708000090695403030803860300740c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 200387212 1250 200385962 200385979
    0x108070b0324030a030e040b010c0b0a020a0c0203070b04030302010605043c0e15010e040f030309080f21011e060e040e0a0f1202061e060415090b03010b 67
    0xc5500c1005a0341c1c0408242c80d1000c0700d071460144540c41c000907400554151003410364034010136070082142111030906850802c90340300710300c0045646960709480030305007035800804503020940d1030b00280169655801d05039100c02c1c0a80c0801c0c40c150f1b1580c4403055204001c2400d00400d903085c040c0c0001880c04407810b00c9109403180b801510a500f0703485151a0380303030b41c1c0038107110300c40001161540c0b000109001c0280b600200301094880c0200c02c2d44120701c450503c004289403440982c0700d800b850300960700303000040060380d00350002d044212007940c04210078440400045054801030440c1c010083c03200d800200186c005450148040c0c01c45107906503050f030070501c1c0342030101c403031411103d443c9444258881c440d0007103002009508405000340c09036001c01d505000d0080b13142c5c05d02d42e20490445004580d1100102e8072101e0540d9114106510401907007000002c041c84c003500b240700100b0000718400402e4080003001c0065100004640d100c4500213850710f020310a205039a03605a4441d074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 200388462 1250 200387212 200387219
    0x30607090b0714070f061403070806130605061605010510060807030c0309050f0307020108010f080d030506040b0d030201150608010f0902070c09050126030a0c0201211112010807 78
    0x200500c0c06800360707440303103040418000c0034070080c900300118404480c0240d40c0080c0c1c84012568540d020b0b80189004580440c01d61348031105c001d402c60f880741026584400d90768030b031181002007084008005d41c0011381c0b18200802d590391810020070760798403259042c840301c07002d03441d1440c29120f00419032130305070060040421010382c114058542c859401c0c9000280040312001c00d40081800c940041d009206454000c044090000024101c0034001d0706c5d00141e682e40c1380c071210446040e81c09285419040002012141c0c2d020380c0005800440060000c41e20a446202048030340c0d01c98442900143e442e0100002d061510303001100241115140050782c03581090070140d0000458070419288950000e450820301007000c0c038003805041100300600031543c1d00c000610001514481d02c140c541156014000b254100004540c10750340c00c1d0325001d034034030340d280c0043d2a402c0c0144200051690b00300c0c601c401e00c8042d40b240d803090892500d203154035010300c02c3c2c7c01c2e48a080140c001418070743c420b25060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 200389712 1250 200388462 200388467
    0xb0702030604020415030f05010e25090b04090b0906070801050d050303040b040f050715090b0a020c0f010e0a03030314070906021209060d020f09010210051003030804050a14060411030607 82
    0x1603a10a4061394046410b180061280b100d0010603440607142c080000180b10811a042d000036411350f0804044034020300410004040c0f1508001054500da0300f00c00d4200071041441d08850380b900e10051002909444503103820b40c500300110b940001c1500a14104401c85802c801100d001d0720064032840c200d00c40e16900d859883c480540050902070b020740003c0d04204030704440d001c15a80c060300303030380d0748680c5d42001c0450751041c1d140032404903030403520108a43d0364150540b200508507a009000c2014502d00388502c0203515210a41040110031502c445611000d080e01c004500c00e50380041c1b1508000102400660050141010408400c8080011550000740000007010f2000c684d40d45201000001e0811f01c900c1a80c1c90034207001003040001882c2c05405005e83c51400e800390303100c4841c0c41c03511208640084441c0b10030521404018400320303100741116a8000c3c441c1048440d06100c030f46481c601120440510181030303010408010410030740a007000c1e0161400d4004150500341036801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 200390962 1250 200389712 200389723
    0x10906060e060d1d03070c0e0f010311010c05160503191112031306080402090603011103070509040b06070b1f05030a11061207020609010c0905060a1b2405010b070203 73
    0x1c0c0d070301c0b0b80004140d5040d0b481c980d5115040c411420454151141c07005810039440390800b00d0300341c880411107000012000380280306a8840c50310214420120b0313007903548001050100c5085207040142d00700c0d1070000180c08108501010340c0c0c0ca200742c641c0d03625007001c251600c81d054110a1a2500395126440020382003444001082000c80741c0380c43d0006500391040c6140600b03048000d0801a90400041007074014080368000c078000c1d566484140c0c1c0743c00915007030758003682d14030210460810002e021248220003520505000800110b55440701100044403600444429219204e8140602450104000b080104014135404041c59a880e1600283d1503000c0b244001d0541300d80c152a40c40f0031780e1440102d400600a680381c40425080c81c1000a54607002102c2030101c0d07618100301032600d10b0080402a00300c90000b088030746000b44c1001c3c12603425003ca034520010100100c035060001d1f00c80340d03600024101c00d0b0b01442d102d00300040e82c03000b541c2e13040e80303c005407102c2008170b4009030310003040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 200392212 1250 200390962 200390987
    0xf080307081204170415090803120103030f17010f0905060102070e06060f070605330f060a031413120c0f0f020609040221070809072c0a1401090606 65
    0x244030b4aa407141000d56a250850b0a40c18200c00b0000f07022509200012030740c1c04440140c0d072200000da40fa2001607a4030b225003504989000b42207001000000d01c0380582c2070074001c0900e041510341514500d0010441c200780c001100b18001c0702802c1c09000304a10482d0f50064092005003590792038880c00c10300c80c801c0504160b0040c90005444c008120809007141e045a40c0841c0402c114504408804162805c44954820031710394070511101103900e03003c11100139803004001401e000b0412040103c59409101114203240e11046a0781c0960510020300307114152080c031401d0400c0c0d492611074a00350703450032000b0900c9840c06d10f00010586d00c110b204562688079100c0701050000740001915406024900303a849400001e026809104850001c1a601c20144628080d5140d0300000d0790402d90481c1c1c03580040c1d12805c010409812451441404094181c889600d8020010840f0001c144100c4105000c1602d40608c1d01610704d1400000780113160344203040240c1800c11100030070314100d102d07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 200393462 1250 200392212 200392237
    0x60503010e1302061810030204150c020d1221020f0301120c150906080609090c0907090f140117090d0c03050904020d061d07120f180303060f08030708 66
    0x10010303401c003200a0b02c0b40700080e00105055104c40c50f1041c108075005800740c1c1e0b42e00608601c05189040c134040d000751070a64080c68840c0c5220102680219080e0901e04400e07640851014048408100d0703281c1032010002490340e590300541900200c4112585641c40f40c42d04040c03041014044c1221510241ca054440c0d01c42c00f0b0482c0b0400c1c0c10603607000059500800100e030071110030702c0311154001a00300212822911000084d6031007008010301e0b000205c42100c030941100d28807040601d04420703001d43c401024148500e40948a480c81c48130610150812081daa26802d0718880d9036030001c115002400a40341b10031014070780105041d44401151107050207000d40f00110348109406442034581c120f03c0613104540310413034200c00002810f1a0700c40c200f042800d144c1c50082049261003001d20856580d2102c10143c40013110500041c9800b0f824a05000c0c0d4038940000e8000c0880500c4c002035000740e40108526041520700b03000040e441c1d1181401354804c210460008402038103a071041148075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 200394712 1250 200393462 200393489
    0x40b0c07050616021005010e2a07020126010803120a0504051506060f030a090c24050d06030812090d0c0201020616020c0a150e09010b0715020d0e030c0c01080106050301 74
    0x118113038036010b005210380742500e0030200007050785800100c1103032284030200410b41c04041044110703400202201c440d011504030030001100554000c14036185041d610122001d940000d15800f1481e2000a070407130026900b00160b441c10391900400c00e103820000e02d6800300030340e043c507660f4699a4040c0040c030380c080454000c00070b2050750b5404d003940e203051080b80c0d04940c1c0703103003805040340113228000d0b040b1003110f1080d1000c0b03808400511542041d05440110f003442ea880342c1384c00d89068000d28004058692681c1d00403000070b1040003c0e164584030360090440c1410000030250800b000900e00c83d040110b030725600c0e80940c0c6c5c0018007a070000030001a090921403078070022404c0400c200c4200c1d030081c141c4200010044001c20b80b416980c071803656040031080286041002e200780c28450741800380014442400400d00302c528154103526612401171825004500b8003065a140f109180c00d180c0000c0303103030b85090800748000e05a145003403a01008660412070068680d00040c0030300701110001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 200395962 1250 200394712 200394751
    0x336060b03010f05060a0911160503040f18050906071709100608030307021006050105041e030b0709090501080703050307140a0b0a05041b0602030904020a0903020d0506040b0c070506 80
    0x250340024512800034000b40040030000807054094541030311014007410100c58000303600e000760301c104154690440c0c00c3c0d0745441034181000c102d0508500041e64980400c008c00100248420128001400c1e028015680e18048040580403600b0017400c800d819040740c02000310880d885858803803081451004283c0640390b00fa885803500980c0020041030700d00c7c01d030001c60244d0001001e18400c06581c1e084a001954000c60b10064500310f1040f50f0200b241880305001c141c40740c030454a01d6400300090684e4955407511072240c03920090b0b44840c0812a400800d00c03040e8500c1c01000c1c00b414882001300001407566444644e284585034000c0c020840c203c0410684500501480740142d40014081840307041c40b089540082200b40e07001c403002d460501600d44102c141e5000c0c0022118250051824041160300b031102a602202060040095000c0040010f90340c607060300300a1400307034004020354901072400c2c60200d1800b90202c00d140c2c100b403005d08001580058003070340c0011a000c810246440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 200397212 1250 200395962 200395973
    0x1404060c0f0515010e0a0605010912022205060307060810030303110403121205060102010e0a060e030c03040807171209040902040b030d0309021005070312050c0f0d05070336 76
    0x140c070042880c0140800301030100306030080c450603140d001c000d40f00746882d0320190740211034a03403042602003a5050b0007080b2441c1440140d040c043d002500003001181c0045140400b904240114441c562b40c400522195040c1006940050b101500300301c5c405007004440e013100c00c07440303201c0241007584681e4188101c08041c01650011503000080c4007002e8050b0b0701c003504808902c492010300ba03141c8000140c0c0c1c0e43c030501490089044c10400342c0b103140300c6502c850740034042004946140c1d110800031401c110342e04000400042c140303040a014410f003000c91100c508071140c600d5002c1c81e446110300c0942d29403440b0480e4510082101c0004682c840d51006c01d025040c240c2050b54103015128020900a03095082410800e1080311144c100d6083d803c8107582c0d9020306030014001503000080f00c80a103440b5480903410102c0d901d841410150025110040703613001ea201c504542c0c0c3c4510910035000e4150040741d00b401014200780540010301c02ca0108542c020a9030030f0400207049000c0400d120 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 200398462 1250 200397212 200397233
    0x504050a0b0a0204090b0603010608071d0d1a011505041418010311040b030f030f0d090f0c08160b250c080a0507050f03030a08040c081b040b011404060c 67
    0x741d01961000e000d180200e2120000d4000d07100d40d1002a0402c3d104081c01d24205085906030340307843d140c0ca2041c2e11001021070300494091340d5200c10842511014909960746c50442290900c40d1542d13030503415444403209010801a44105548507100e1240d44d07134980c224003942c00707540720b03020030031604000d000000e0703c44118614950f040c88452000801400101040545881820340e41070186540b81c0040c1950380038040b11300c0c00d56800512203406150640d0000304400074601d03a012a2544007a119000301040e0108110b1301c040c4040b00400010342c01703205400c43c0c602c450340d02105442c60110300c5a100c1c81699040e204005076140c0003c1c0300002107140c0c1c554250030000c45014075031500b00c4c89035585d10119041e9168400c01c2d50004103450300c401c00190300040540a50308025000c1025103d204019008442d002c0301001e01196030318080001240c0b02071914546d2032840c4000060008403081798004a0401c10010a440c0507010f902c0100c804990181c0f800380074a440d24144664500e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 200399712 1250 200398462 200398483
    0xc1b1c05101409151504090213050906060a140105040501050c0102130803090301140c1b030c0d0314070807080106051305060f040905130f11130c03050f060a080c04050405 75
    0x140d1800b030007210380d90302c01d10700da5124619440c2207440240d0b500b5000d18210b60121002d03001500d0701c041102050410350415500e041c4060140221248203460803000e41e002240c0002c01030f8020400c10840c3e10b0f01c1540140203090382843c501011070b180700020201c0c03045000f242d044c4003000030300702c56204d800d41c1162205507145150200c2161640082910f039400710480c039110b50f0800b03045407048500143c509020b0050450080d15009207102000c400001e40720300354003640414000021440d00a1042c001e07442030a5400084103404000005548103001d0440d4040058113003c01c0090b03900302d95914107480c1c1c5400d015458140004004802c0304503a00050307009440444c03034010503e04a405401039070400c8401b48101c0d9152082002900d040f1100546103940b5284e108010a01501c2c1e070b512039a0018100b80b1142c62a4907128003078a42c0c400b40d01c00043d030f0b18020032500442700c0c03010301c0d042802159581c044030310700b20201e645c6000c1500d11510607590344000c40d0410034100318520340d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 200400962 1250 200399712 200399743
    0x15120c090414150612010c1b0c08070b070b01090b06070308090c190305012d0207020102160305030904110309030403030305181c020d03020a05040b0306010903170c1b1c05 75
    0x1c10b20f412258107190a030955040d40180014000f0040100c818051800d01810681e0390305550115064400328400c0d00c8141a284100624400b142d41c0d0390038130249002d402c03d002003603038944883c0b50000c0603a0051b803198000d103162203c0d040007030745d03104c04503a1340d95090710740328085484084505042088144243c1c0e4003594514545a4091a005809040b240038500030480c0c603450b1040040b416030000080d60231005041440c100101c0d06a02a240c03440c0180304a6900e14414408105250210780040c0e825900100e08182c0c149801d00a02c10100301c0c091542c1c0c25810320511550783d9016501004040c152070b4000900c00421100c80e0004612810040f21030940d400248103040d500250350b214014040e8440a2446901a000715140940196038140c074141c40d11204a081d50800f0344503604005507020000003050803d065801d20718a00c0801c1035455110704030461504000744a40782c2514206a00000d00c1c1c1d0b101d0780d07110340c0101c0d845c03400d581441140c0f6200d41808442d0400080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 200402212 1250 200400962 200400973
    0x402060d0e030a0201140609070203040b031503031314190b1605030d06081902010f0f0e030714040f05090a0206091512010311010c111c06090b15120c090414 69
    0x44036505406c130718400c1352a042d0002141d2070300c41c2888543c0d40b08480f1340340940c2c400c100410011184000450b4043c000321001850300ba003070b00000e401d5078052500b100e0800e554207014802c040c180c0d541c0c2c0740c1d28001155080d00f01c5000110322514941c840c07140e030075001c0e4045400036681d01d220b13a90b00c0d80c80d80c0c06029a81c2e02c1011815200041031305000c3c0f891540302e642d822400c02e42d0107149130b8403025016140c80940325040c01086480c0b4000301c01107010800003108509080e14100181ca028189030114602030030007042c10300007110080c09020a106051509000307043c41c0205030308044507019585541d45007d02c80102e0604002d4443c0c940356014001104000310b004641c0da42e040e00d100d41d0040d4800c112000046072146401c00010300a071207114214901c618104501640d208502c6a070b88500c03881684403041290522182075139190b03030203001c000c0e0b24140300480360301464003100d8010b00100900035513075984807080b4101c1c0c011500b2401203020b1016180c143c1c2c0b41d50000c0c9007203a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 200403462 1250 200402212 200402227
    0x100210090602070b0c0304031205180316050c0a14040f15090204031502090f0409050c1003060e07110d140403060e0c01030c09060e06160804060206190c080402060d0e03 74
    0x80d8003401d01643d0303411328000400d001036007000440303005507090341e60f604800c03519401c088001c10b0080c000740002a01010250034501c0103101030242e0f00c5160f0705a644904a40c207005042076110f19269204503104c041c01d1058000c00203000c0d518280c191000503e01c103443c80d010004040f800c025903410b11450400180680171900200103682c13003050101e200701608007110059001c1c8a10940e03000d0099050510541800c3d070051501c28010407c42d0f094807270480c04144001c0c400c0c0d5034600002e842d540b0a000043c2090360301604008030b0325101121030b504504080e240d0412003072503000c01c10415484000c404c058002e0720095508a84200700c02d02c4a2203100b0350300d00c01d003e461400300c2d042004070043c2e00d0050148504490454851680c1e108001041104961050341c0030714812904405103000b1888400142002d4240d54008042300e0402c450501240c6072010005104142004800a02d903984003424a821580c140e4109031074180e0f10b9500b0018024150719a40c6502c408981d60 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 200404712 1250 200403462 200403473
    0x1062309030307140c0d0b040605070e15070201180b0703110c03030a12050a0b2209060203161404080d0c0807140706110f06181615032910021009 64
    0x854800c88400200d501a903d48018420791032280c541c0a010301e00d1f00f00025021031030341e4020705d92210891400c070f5403144240d4000f800505490980003851540404c8a60031540c00240714020324031404c90b0403008a1908542d800a449114001020041c514103180440401000702a00098006042d25280c0c02000402004001d882d07459400042c00c04000c100b040e030303841c800c0c0038080382c010f00620107611144800682e20680e0390711041b402070780d8102000102c1c0c0b1a1026500603001d4201b54215020709140c0100300e4078002d01079000c0102e00700410003d448002401e40b08040c1f072070424035503402c030500b0404a14001d549000e8020140e0241481889002094040a48107d178940c161500c880f8511269500d18140320700341c2d02da00190100d002c160644485034404000b40085940c07000f802c0425400b0f40c56140d001c020250b5041c0603080105030035001d00b0469a48483c0030700f070040d007200c50398882c54245103801c0d4050300c0190155238800740b00340300c0c050181e0340d0120300740407003111b03450322 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 200405962 1250 200404712 200404733
    0xa0e0a090308070f0e01030c0216090204080d140a0305060f0301020a08010801060b0c0303240d0503212e150806030f0a0f06020d0f0e0303100503010501062309030307 73
    0x12400110b40000040e280c6004844500c07110585685810840700c0c2c5c100194010545240b4141c10b51040c000d0700d4211055078000e040140007584000358446103031400862034000098140d40503c106110078250b074140000544030811072900d0040303940d468001c0412940e4000011440d015400013811840017504150098101d5034408020801c2c565280c0341c001041c0200481c0880301d030420408a0b0314200c98600d43c2c40c101d0208812051218010400904200d0750078030115a1a00049043c0c00c0701d40440c0344005005c1d0341164000780f18038001e52007442030340940c40c010301d4800f844940054501c54500d20b0750090260001d400c2c0440e0303400e90010b130244904403500b41c428801e60640c8021002c021800a4003154840d10207841c1c0c0d03d00f40d032941c0203504401039030b0080c5940d07000e810081024602813428042c101402641c0e07641030541070390342805680c0d000a4000ea060200401c80b2130b50281040000c8040d500d8640d4071342c8003800200c003441c826080382680c5440041008424000030944 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 200407212 1250 200405962 200405981
    0x4091e03020d021c0e0301020c010c1e0507021008070e09100302031218060c0a050105010905071d011209060b10080711120414010203090406090e010c030911040b0a0e0a 74
    0x2110030201d40600100c1e1384000c401038030407400d02140300c081c128038003884588502000050008d0700386071509854074210303440034078201e000401810119940110700d140d102c1c100c50381850200c0c5000e0803038001c241c46e4070030040f804e410820b441001a024030f00c100e04100760b400004204520f1410100400d00041d003c0d0f0000786c2c42802040b104900c0c3c0d1040104590502c4080032021202a038410100b18554004400001e1940107121010001500038440d060103010040c0d00058281402c1a00410104e000074050b1281407031906045031030381c2c01400e5080000810321000c9540d01c828980078000d07015644190341c000700d081c22500b0210750820446442203055030b45008035210f400700c00369541c640e0f000f0002c2c04a0b4041009020441c0404001c284e00b21040c011030345032143d90801700e0210b415561140702107640c0ca41544408080038090841401d08510341803000080b40e031112504140510a101d125980e598103401c1d403031715950314900041042d8555042207203000501d0130040d10980c00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 200408462 1250 200407212 200407217
    0x3080702012c0103110909061504170601090605010c030e2103030903250b060d0825050c01020114010905060a080f0d0206132f100203210c120604091e03 67
    0x100890302002205c001c0d941c43c0300000302424142d4689406103c925000c0c40405001041e0420010800700d0944a031060020701c081c00030f04066144c55071400450300c07030b038020364100040785e40c0030000b0992000304070302d58680c01c03200411240340d03d04040e200300720004a000404e01001c810802c1c418008009001d0100c0122220400e0030020325070f14040380d10b0180010030304018107022803c1c2e81000c1c120780441921880082d464902c1c6080310007100d407000d07070300c0300541e08106151a0410500f804180c001c04000c1c0002d00051303100e1229082d1030501400fa6083d00c0d9030f01c0300011000c2c1c2c0d4043d0050000d100d0360054884406004c01582d0f1910044021007015200e1100841d078403150005003800090340101601081c80c0300c4e0150754030b0b4a400008030200c0840002003451083d500c160301d0300c1e5003525940045580d00d0520700c000c2480b2450f005c20b558004034007410000300420003812600400011081c1003000d42da2000028010011440007a203160450025940e5000301901070701c4900c1e000340c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 200409712 1250 200408462 200408471
    0x605070509030601060c0515011203110d2012030705040608150105031504141504050a02090a181803050d0e07051c1703040320010b0102030403080702012c0103 70
    0x49805480511038004069010b9009a00400c109031146002d0211b503803189068030b401146450a01c07007214000e0700203403030b1001415004010150844000d0000e5425603000d40300440c0030407406040820270101d00c941451440f410001260300c180005508541c150003282e40724241100c0040c13054025000e480301040800c40880e00d40c100409040b900240140d50706c0345103a9030150f0300080c034115020800e8102e615028080e00c01140b042c0481c1c0b059600e0f040384008800c98a04010580c6c0000d041c20304824410804500291295820038065907444080047d0360025009040300a12007042c072103610010a80501017019030100c0200002c250710034080c040280d4040c96140c5607142446182d074060b0804004400b084072980d40c69800074020040c00400c1c00c000f20102c0c039203a10807a4100c0c0080e078142265040c0040544004c0c1c8801002c40080106080720b0b80084d50380d100341d00019010310700c0858101d04681c0f103400c00c00d00d41100d041140180d1102c80a10b10315580d1138848140c0800e040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 200410962 1250 200409712 200409721
    0x5011b02271e0604091a07230408120d1b02060603010c030e0703031b060213090b040506010e0f0303090d0501090c0e130b190f06030c120f140f0a050703210c060b06040f0308070605 79
    0x2c100589d803d81e0300e50005010f05d0725000020100d1540642540003c4584500e541c00c045603012841c0040c1c0510354018020500d4071030105401c4441c5c07034140f841850310381210183c010b440021207400390307a03060808241c448102510701c0b00c40c654002c4020643c03400082c3d000b098110a113101b40032a0f2828000b8070030389852808110640340e00300e03034980c00100020044043c81c0307400004d41c1d024510243c2580c0c90811280d000c04e81460074030000303485c1f136074646c0c400c2000c00a00c94030005c0108038a0f17400442c0da040400d03071460340d03085c05207000c0c1000c0f9051000c40d4954030340c8100f59440309401072040141c1d01410320808041e1170248001e460581c0c14002c005030f80c1d10034a0b844030b0599808111010303840c1071655100c04000600c3e00e4002030380300d60a680410407508116980304280104000c1805030f10350300e448541103803a0b084801f04603200d40d031460003560f0004040440181d1040c008160f0051180c003282980c0629071042d02d002000d428000300340840b0318018600c040c003c3c04203120940c1c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 200412212 1250 200410962 200411027
    0x602010e100203090312040201031b020303100807050112020a05090a1403010629070f0204060e0f0109020f0703030207020d080f04030b010503010b0a05011b02271e0604091a07 77
    0x70899213940244c004018110800900040c101c0c2e0240c41410000303a121182e035000f0810380050046400564400000e0250503c10424140300a042e0a402480d0481c00c10f0002800b0680300d0482615054000c1034003003425001d01d0079144800c0000d0f00c0e14407865036810b00544483c80d1007001c00d01039482d0210115076844140b28000102c2c9040c403d020082d8803030400e0f101d281d8400282034a070082101d80b40001a0f0b10750040c0402054003450414140c18107c100b24220003040c2d025000b81441045401c070350695400c01e4899881d0182401a10354803140045400c003016042c00802c900c8001414400c100c080c200500160b80c01890160110780e290341c2410700f03c4026100d078646c05480326408010546c8180d212030704062040010811008280d40810b400d024811604800d0410541119800c20580c1419a5000840303800b0340381190104828034481c500080c124a0150f81c86000310030520003400744210403c0e000f44517441103441d0642d0000d041c8101002e282205c11403030b07c5018050003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 200413462 1250 200412212 200412217
    0x2f060a05031f06090b0c0709141605090d1401090c03080d0e0c06030105041e15150c0b22021905030706090b030f220606080712050307080a0e06040602010e1002 70
    0x2001c0b61118000c00d4100844943d003a0803502101b1010310031000c0101d0b121440340030b04071807014403038104c0583d810210000c1d030040354049201000c00c50b09010f1249695030b03d0410b4015103030010303500c0000e0105440c03800e000d00306824016042c200f400d0400010030121800503d00102c1d950410410000c4517081703d44c607000a100501d5200d0014030050095180542c49103003c03078141160403202401559200c801e4890340600741049004801d8100580784200001e0381041110b86030102d031010295071110320540010300261002c1d01803000f0720b0504581000b02402681d0000c040c100000c11049640074400c4060040328041c3c0a652400210b40e4042c6207400700303666a240310641169141c008440a100004004107504000c06500018907000405440c501714040e880100704141000e0307001d454441f01d0752040c0300102c0340c40e4803403000c070fa404426614003d500c40506d41d5a1200c0c08821a4020880c45195901140c00200007520680551003442240900781c20740b800e04080c1c568080490 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 200414712 1250 200413462 200413469
    0x10f03051f0204050a120317160309020a0f090501030c0504140c0702150703080901050106050c070b09030102040f1205060601020a1e1406011518032f060a05031f 71
    0x641c0110a03045800050341da000744241c0e02820018181980c0e040001c201881640c40032910701c0d12140201d080c0355104140440c50700c00554000f24509044030980040d621141d0084100340c0c3c2c441f110003c40da034040862000f0048100b000341080d4407a40c40000a0400307110484002e005218001800e0401c0d020f0405e4250325070000d007900e0f035281801c03c10703558070010b0101c1c0c1c800301c600c1c48403000c13a60040c00740254900030341d2540c41600e05141402d08640701a0010418440e0500100190950004140d000d40d402840300c5500c410315980801e019004942110402820f400400301c1c6286924240380c4040b4004c2080329201d0320707044016a199544141e018240704480310030303a000344000c2c42a910710144642312056403045039141442c01c24a00f80c02c400340c50719885003e207201550041d0002c1c1e9800302c5041281d0010300d19a10009142c0c0010b41003542081d441040c48035401221130300110000001c0d1000b5503030b002800005005d5401141e1050002da0a070400040e4002d0103500402503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 200415962 1250 200414712 200414723
    0x60602030703081306060306020711010c02092404060b0702131406060a020c150a0f21110706020d1407030e0703021e030114070f0f020c0103051003080a02070e010f03 73
    0x10007900c1d88040f100508020644c3d410824140c1845001070601d109060045006132001a212015131514448a030b02d0480c00e1030411031550074020142ea10165580d0f001180e1002060a88840380c9000718480046000070794000c0c0f51810010f10720104000134101240300701c80030140300704d500c3c00542c1141c0291451207001d406190004041d400c1c424000e0030341102600403951840b0440e0001030300500d51101c1c070400020003107100007101d07401003403458070700001d402e0501d905d144140111048081c11102510455140e00701c1150b07010080c02218826504890f09569401000d0511405012a155a4240c500841000413000b51080c4500400c03290904082c080e9a807541d001c015010400d445a42c1e84040207a0003020680e07801d10038104800c1100040880501d0709490143c02035001180a00502c912007544100065012903200e4500000f420002856210380401c131100c9038044e0401400c0d03c0001a603069526000560003040742c9240d003104000340e0325400980c80460b42807000409 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 200417212 1250 200415962 200415967
    0x60b040f051c06181b0b1602010c020a1d0f04030c1506091d0c060a05031f0905040605060f0307050102030405060702150301121703060a1214060c09120106060203 71
    0x12510b800d802010003005a44800d0440303401d1a12448211004480a00381082c14241c04030200308007407a10821070004802180a8240342803001d122510560080d40c92a26041034890116805102c0092946402400f9103150303988410414503141c0d122000700801210110004026103162074005114a605a840d200310003465901c1951a114045802c400755403540000700300070f892489411008984425800c600414640c80c00b4101110003c10a0003034904011105410b03810408a0313401000b04411140d200d00c3c00441c0b03290b440f0f100d4210108150800f07040c001444140c2d0004c03406800211048000c0d4000081010343d41c0280e03120b034a01503007060100300220328102028041c0d250000d0a00003000b141d91a02c1401035009810440303c1b402940d41440070300035100c90000103200d030800d40b5407860401c00300054040015200b00701e082c00c01030b0301040c20802108414003050310000300b19082800d14040b00d60303054100e006800d0040c4501b615814824005005078400c45d0400d4000d9803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 200418462 1250 200417212 200417219
    0x7090605060a0305070201110a030603020a09182d030c1b0f0611070b0c011b03090b0103020d1406070815010206010308040905040317041101030b030303091203090a0b0405060604060b040f 82
    0x2800303410300034401002d5559a01448c02800490720050a0100155400145040c00d501c100048480305030000484540750004d00500c3d25801c003000010250000c4814000b140030088050f144100c16298460460403884a80101504064401b102511a240003120907007210030b81400d02209114100f41c182c040402080030a020b141d1003020500c0c104150340501e51504c9904490780c1c4400c640c0401d580d5100030700515140040b041c0c0b00785002c0d41c5000d0010300304549a10f02c00101c10700004e440b6141d0806084108a1062444600240342d1000d44030300e4a02114003400c2a84100d540c04c4402080c0021401c8961011500605a0317a10072451810541407182120003442c2c0100110203100a50300341c1c0081c0a1210880c0d4403075031041c1c080c0800c544514000406581f2840883d5009600c24414030040c030300c3c0480c0205100c104024019100e6a4842c90300380b0380203030440f0143c640040041031105000003c00c0c881c1c4211002d80b01407280c90340d143c2c2c0401480c8158030601e14900e08180c0c060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 200419712 1250 200418462 200418467
    0x6170c0103050a0e150a0c05040b071101090e090a0302060a0e06150d0c08030d0c0507120c080904020a02030301050f09040b041403040f0b07030327170f03090307030207090605060a 79
    0x940050510f000042c072550702c031000314a0441441d500c443c0c500700641c01c000f0460210300503c2c1c444095850401d04151a08030072084500411000401a41d800c40000d141d0780d104013020401004072807840b0b126818420b0209444414019040c0e0060040400140110f00c0070b0088044804109004240542d00d03070008280d900c0d0701d204d005500800c1c1c2d0700309001058145034110050801c20028642d01c2c0e04250140088840540c142d000380031040c0b0042000c1080703521800c40b1030703841e07081840000d980d40c079091000d8480c1454031a031003480481e0801e80903a0000155050302d40944000011444080802113400022500280405202d0303000400180b021215030740c1001c0c248045905141d1220040418080c0541050200c5030004c91280300b85941030050030301c01c511000580f2422150204040d10030281c03a4405400020213245010300c038180e0400311203100442c07046640e12070500c07002694903540850070540c014403031540c000c903104034288034000403598001c290ba40b90100030341c800e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 200420962 1250 200419712 200419721
    0x21c0c0f0c170705120c0106140a031b0b0f0909101203050c0a020306070e01080a150501111501030b0f1e0714070b0c030105031b030604030e0d0c03080403020406170c0103 75
    0x3200b08103051240400180c4d08100c4088801d0300102002c1e00c8aa02600c1542100c030300e58081d040c049480c2095903410380311141c041c0107898100140007120017581400c60301e0699281c2c0940101c000000b680085190101d0207401034003800c840c030045e01d84604a00000100342d902800781003030b4403518540700080c05a0700400400003080282c030104451900080d081100495580700443d019280030740441da030108070303130ba8411064081007012481c1155400c40c405564001e1905101410401e804020b100f00800700c0c0036100780ca0b9580c1e65603141d207007400d520340083e03415019018120003c20030010507221300c1c100003458640c0707000c0d603951024021165041c089410500010042100d8000705003036510f0381c0d100b034003402d0304a035495140400389403a20500140740c03100a410741c0c051a00c90b580129101d50802d0701441c280c06010080d100080c210040a03400130480001d00b9400810032121201030003c0302c2c0200c90401c0b446582d104284841ba06c114206070240e0819641c414456020703074003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 200422212 1250 200420962 200420993
    0x80f0a02070b03090105100909030e04150302060c0d030506010207030f0b040303020f0d0920090c0f0c100f1a09040b042402121005010507060c02030d021c0c0f0c 71
    0x100c50801e079542c507140505500507519401143d449104000d02003041e072030040001c0c450080100402521610002c0c81d8800070110948210b0711003461442c940c014180440c0039540040503d0313501e4088103001c941e02c915010504e004a828500090170540c0086501022203030419031126243c0401c0ea20310310034140040048050550901031880d41100385000307000c4c114146d24000807005554140780007042c01d400c01400c1060211101000691200040c241d0030814403214141c480e0700c2103114075624054a200340181f84650756401e50820126001040840b032800ca040144040b11460a4110448501102d401981c01c101040c001220780341c0e20f036403142c01007020340c459030f100c240d0090000d607400311b400b11890b0b0081803218204104208550300202e0300c03420501040d14110010380f80740100c28002d0300081d03607041c01403040c80c002c2c02180e0b50b40c0d106144c115542c0c1400c0500200a610341c944030040c682c07400d50b4891003030b4001c0700340c031040280716200c042c8084080d9035184c014815218 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 200423462 1250 200422212 200422217
    0x503070308071e0c091e02090303090105030a110a170a090b012705010915090606090b25031e09080c1201060504020a080103120c02010c02100e0a030c0f06030504080f0a 74
    0x407000c07022601d001c1c44600178014000c008140d42446030706002c00c10004650030b24403248100034464450340c000049070440704081c200305c4c3d129a03d1803d000c00610041c15841c20210000520085255016403284080044c4605000b51a190200da40007260528100141400e0722900180001841e0071080526620b03c1e17013a40350505040641d58040c0c0e41e00f80d104500c0325451302610701080c4c02c850842401350038000c2c01000001c7c640480104404100d10400e0340340040010100c0408684800c0003002c0000d082e4814007680706450020800607030422181c0401480b0025161041e115619070803c68940100030941019034070208810200c110180d00e0466588040008090320b07240082d1203441e22945852400758918182004003520005004e020019030102150060380c202e0500703418107030161242c4500020746001902c030100d80407801644101c1c941c10000c00c00c064122520700f601c0415101e00070f60ba54070704040d4160f8500795002021628140f1049405001000140c0010722061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 200424712 1250 200423462 200423513
    0x10050411041b0e031507050304151b030f0209090438040c06020f0303040305090a0801050925030302060109050903040e0901090c050a03110f061b16050307030807 71
    0x100050111000c0c1800340440d02c02c03201d89026642d4110001e0800e50710b056025004420708501500c80309500180300344281700e0040007207020311002c135a112030100b152031010800300380d003072526200c00c4140c4041c00000a00300000344204485034001d690444101805640003500c07682d46030f0070f450500401a8038124005200040a00c44991410051520340c00310800e007400c0500b0503c4520440741c2019003994407070300300341060817800801c80b580960189862601c0c0c08450340043d02030805d541c000a40d643c00c10050041c616004204225940b45c10740081302004484036442d5a02a1544805009078005800402c4204c120340c1009a000380c5c040c00341c0703192581f25420001416005d40364420560340d0f8179807810400600252404c0a070400b00c982900701450340c1c1e60112a40e4105400340d006034003012101c01d41c0c2d00c40d02d060320780509071340881c103901c84416072016035621a20501c9008103480c18400141d170f420f02164020989400007482d900e4848951030340d0b0080c60168240c5040312228 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 200425962 1250 200424712 200424743
    0xf040c030b04151409010308030a090305040b04180b09010b0403170702040e0703050f0c0f0607060605030d0c0501060f0e070f1106040c060f030b011b061e05010e1602100504 76
    0x8621071640d00303d40c0550161006814158500c80300420400428000d420030001400800d1000b000d0b2a0311885910380850400c502c0c1c907040300c10380599400291307591000714003c1206054401c02c503000d0022200d04110030b011030010421401c1c428400c116422000b08010320100315502545c1450082e011522458420b0f2580410b080750100b40c4107030440e400054041c400c0000c14001c040604800900038290010030300c00050344070b280705004500c1400002100030410031580c01400c01070070010b05881058601810242440c110054112900d5103030001c041740b181d41495110055031201d840000141e514240240c4000b4071003211007060000142c0c150080710400c01100c5d114502c02d184141a1380e14090003d8038180a204090050504120ba81052030764481c0401125103141545100428034a08010000780218016141c02100c44502c2204d401055003000e4100e0b110040d03007074415605c91000066884041d12214010703045000c10910000140d00529001800303100b420010507030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 200427212 1250 200425962 200425969
    0xf01050d14040c0303021006081504020112150f09060806061c0803041a0a2d1127010212030604150e090106080f03130b0c030705030a0c06051003020f040c030b 70
    0x142110200c411002c186424000c146d414001071600701c403503400601c603403802c09030074036220a25020b5028010019000140940e8452042e01e007103075207080c04c100440d1044007800482c45802d40500e0000e400000c00010300b4050354414201111800c4e00605040e4455104100c6940a0151585100c15080301142c022600c1200214040c80c482e15800410022403445218040402000d03524200e1400414030004402c0260300003000c0b00e808030754540032041004a40090201d0030710740040c480e01047d1300000c014102d0b10000a074805d0722000790400001d0004a079191060300118641c4482800401c1450905800800e1981c100c40061341c072003511500301c85508501281c1440d140d079191602004050014410000c00c01c51000245180c14002c030102001f88805207d450900f2200040d0682480300034000d0b110410342c0003007501c6c2d88244a500092400e00e03001411749801d850034020500300b00910f408a41104d502501c0402c0450f00764042100a04458a00c40c003070544440380340c4031942d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 200428462 1250 200427212 200427251
    0xc0309070b040b070314190309150c120e030c1902011b032c010f081003080705060109050606040f090203070e040f0f14100e100e1503100b0f01050d 65
    0x1c4690364541c5030b07007080c05c2c000c02140401d090394450900810a91100b02c1d010f5040745a203020a05000c11216114600110400c40750f42101100c1c40c54010341d1314038203611000c801203994100c80c09006084040b561b0644034483c2c0742c04000213034001d245040c40104c55080d028804c9005050a00700d41500c502e03494403942101c101100040c503c0313807111a00e40000a02c00700c0d80000420789421425018001a080039600c40108050006400002d548403000d0500800a5503000001e182c55020924040350b4440082c0102900745042000194181c18007000b80c804030348211941c100e48a10303002004c0d00951020f4014030402110380c40700c070080e4845000300c20a1030f48240c80011a12100021741080701c03050a8203414036418001408001d0074403080c00400e5540070520321400740c8602c1c214513809038450340b214411240c07400402621048821000a81c10401d8065031003a0580441daa802caa0022410a40c0030500814980940d442400a41011074600a000610107003000c020045003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 200429712 1250 200428462 200428469
    0x150c0c0d051011070302150103030e01050c0a140604150b150a032a0306271104080607080601030b09040203120a03020f0712020c01091505090609090f041403070302060c0309070b04 79
    0x21240013405600305641000403012044401124805950441d94002d0400d2202c24010f4100300000c40c075811606020f001050a080d0720400c05c0141c4038418a003952100b20444059a00801001007582c110001d4006c5904002000702066000f00602a0300c0c0641e42102c940032041503070701e10f544a8031201c80d210340c00b840007080320680303840000c0000c01810b4402c150420901c044c05894844507103840c801c40c8000e1045152004100031444581c4801c440c016540005401d2003440300703010000344c00000c409e00480e400c3e0780520410014000b03011604100707035002509584805021000c0e4140d0303a014051100d41494054908144402d01d010f05030041181a9001c403150620202c565404201030005028203080040b181807500145440c644001968601800b01c00103c8020300d50f9108221404645d0003040201d0a043c203c81844055500302c408680111008910201c2090000709644100381e0660060141e40d075000f111207215080500901100e00c82c8510104280781150045c2016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 200430962 1250 200429712 200429741
    0x804020d06090b130224030a0c05120403050705060f0c03180f0d0504090b010f021b04060302130b01030c08090a1410050c0309060c07080405040b0a05030d0e150c0c0d0510 75
    0x10003030a0040003440f0f45c081b88a109145015070000700309101e06000e495001c60361880015410060280c1500c06101d0310f103445100f4500300701000105a000805007441b10f005804503009a951008006a803103002d50b08219000c10520016000fa00f00c400c03101180244082501d8440b04c0c0412550300c0c100c804030f1a0750114502040600c04070145102e019280c680074079000c1201032003e10043d450b01a481b207805405d05144803210410349031600180011079018060000b050a901602c00c01041000d800600290400e010624401d00c10185140a100c07074801400542032141d03a4184504074a02610b03401e030088090010303a800306486500e10a40340c066007669645441036800d8107080c40103080008002c03040c8000c03404113040809070b8040d0f500c00d94001540d8044000060346192072984201e906200301e040364940f159100c0c07040039104100b6101c1d40360480760884441801d014520217201c1607480035900c0c102d41e00c3d00982101e85140505c05542c001802205800203031110041518803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 200432212 1250 200430962 200430991
    0x218060319050a050f0403050a090803041701050709210312050406020301170d021507020f070605090102070b0405060a03020703050f0c070f0509040c050108191503021206070804020d06090b 83
    0x5401072640540d640c0040d0b0038204200c540b0342100c0ca10030050300904003404200021820104203800740c01d40002811086d81200c0e251035441c04200d8217200c4048401c04a5420a800305201a01070350780100cda6055080c0005032000018500b200140200e10960801401e101d81c1c01d42e081880c8605070003680900070243c0e9940c10b1030070030549a8401ca00c43e00c1d965018809100c0080d501041030391001030701d501542c4454460500480c03800c0c500409a440900031140005070a0f5000b40040458040a800752552140d8680107080a405284140340c0c000d24104000020f07507109600600e52188642403480c1000070405582006400c00c642600e00c1f94420791081c060609029181d4008100c1180c0100d549c0c549503940c00b40f00c0c81d942c070a803818420244080340206840480702005c1c5540d2000410242e00030a00f0310744110340070b100681c01242801a1114a2040460a144110310607211050b0545895091000140208205452241c0d8810a500000302c120040c980581d01a41e00510b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 200433462 1250 200432212 200432251
    0x4120605160206190207060b0612010303081003020f06090612100e011505191e03140718031e0204020a1706030c0a060c0f0624080c0d0602180603 64
    0x1c07000308a12028800b598850741c1001002c00c0c0e0841c503255000f81150002d40c90349030a15005000e4102c42c0e40d540d6000030081060399040a4107035442c1d04a034000c4e681d00f8400e8031a000d5111110049010203500f000c80403c8500107800d202000300b80031400641050701d440194440f001202d1429541047d0100c2d0740c4100b00035031505001d1042c05004004110203400181e42e6000d0034500c944c201b082e000c82009140900f0340c0e03000324100b10035517142d84207150100c80c0642d070080c02401510b1681e85100001c0c4041003070740384209048002e051880340c824680d40d00719143e218200905640c84801c5a110400307900044c0c8482c00500b0b041c598a031200b01c1503180c40c12a0340c0b104900100054040c1c1d025020a03105030b0f0b00e0100520866070217061031081c041007030603c4601c003601c0440261245090615044042105024216600b0008258000c0013500c070341000ea2a1419036090a40c004282042c0c2e10108030a030307005041c0b80c40e41d1541a8106080c400202d07946400448421854030521440c24 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 200434712 1250 200433462 200433481
    0xc040e07080a050f150c071407051c0311070b030708100306020f0a0f030504080316020c12060906160504090b0102010b03070f1e030c1401020703060504080703030e1506100504120605 80
    0x104017900c0c000c140c110300340380c4040c84030040d0007902400b52101400c4040c1040440040c0b007010058a00940300315200204280d018804804107001240020f011007920415078402081c5082660709070240b6501d16261030104840a9401610142c1c003800c1c070544c00000241d83c0d20040c0199110203220545600c0c4210010305600c150000c840d09150910040000040c9803000b200d5000303503009112440c041110404918018200c01c0d529004035100c107031078100041c00515035114101450480b032180d42c4036400303107901d404000c0d0601c01245043c0b100340480c05050700003944061040c400014040d170400b000902d010000e5002c584484500389041c0f1480004016038005468925041d5a603903185135184000b0300301030722641041181c03202000505070300c03e1040388000c41c0c1110081c4100d00f42403c1544190b0b0214400b00c0c0481c0c9450500390640c6008106102500d0003d070280c44183c1c1c0c1d08041c464604840c940d44410002c04110100c1c101c00d00000000c6007902134440002d00c0d142c4080304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 200435962 1250 200434712 200434723
    0x106090507030b03070306020a03150f030c1205030405040903050918090d03021309051506040305030a0e0a080a110301110f130902070f060e0307060222090e0c040e07080a050f 77
    0x1640415040003c000d80503100040c000007260f61002c0d0059660f001008201c00404d4186026181c4180008000030310701c0e40c0300c6111040e00d000720703500480150b5411205082c0c0c02c943c81300a00c0c030303001800b041100b0b150603030040c03a2850081c10a249050801000110480f1000501190f4107001d00240a6405000c00c01d106d10719110b41402c518101c1c0c500c68017880401d241c1b03e61580c0c503441f04002040b125031211580420704020303202d142c55035124a005916508034000803400905801c0304807400e03142c1100c0c0d40c42203c11006c080c0100000903210074a40d0369450154039003564842034441c5440c0000002420307060044a12280c03584640d402000c400102940151000c1d4010302c007020104420810b078002040e030000000030003283d281400c60560103191805013210380301044c400002e14064030340c9985e110003003031540c8900751180b910504071020100c4c00ca0841e400000161500d00706940500b00d14806902141c20742a552041c03180340211260302101c1b59000700c9140341d03211504101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 200437212 1250 200435962 200435971
    0x30531150c08010f2702130e07260a05180d0e0a0504090b060613090f1d0609030307050901020c0424150f030911031005010531090314030901060905 65
    0x840c204410300d842603030041000b0001c04011003d18440840740c40c2d0400f070b41107c0b505400d106002c451590790b04c00502c2c50704001c0f2035090200d241500c61004654540c6102402621904059001c80c3c0700d05621100520000b4200a585e148500300c070400301204001d0110160313059030340c1200350b007124414880e40480e2613000600890600041c43c0014450a11003980f200094030b00135107a1031030b12400f840500c02030b40070032141480c1c2038455010400c207400505204200d245034100c2e41a182148503030380d4404481c041b6850300305001203540c540c8190010115504144112070041304944c00280450714100d0240c84032032035070003a90f508580c0750715270103006003200c40c650000400000806040740d00080d130803c081503525004101080b60b5030403009010b0001a0440d44204c0600345a80c004210070b0095a1180441c0e0606076201c1216005c40c3e5103102450f0321744c68007040c0b4000c481014280780720b01103090081d5040d01100155900003d540b00741070040c00854403d01c0c0c0700e00f03002161005170 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 200438462 1250 200437212 200437229
    0x905010305040b040204091a040501050a0b0111150a020403060204080708010b0a081b010903050d02011a120705060c03070803090303040c05010e03030306130f06090b040c030531150c0801 82
    0x304010206000381c007051340c03103601070768081003404035442d2090002d442c41ca2008183c2002c48148000e001055000c01c0c4a49061328080024411034401036072074180040b008800d95200500d60101c1318404400e5942040c81c0d000b0250400f43c4039600d004c01da0700183c00001d89540580020001c1d80400d000c2d00c00445016940818458200700c0542e850742c41c0b0390040101c8001251000350030f64860380c5100300a541010969594034a03950000303000c1c02800c13581419002c42c2c202c05d44a60f00d40050a03d100002c000005c01280d0310700310522009030440e10000986000a0210ba40454800b000561080801c2005150f8a10346440c05120001c8160481410450603480303035801a180081125040301c012650b440c43c03074140645042c084c1c160360900408550070100000b60143c0c00350808400d128003100d041c03280c01c0450700c0840845000f00c80b41c1c904196007581c0c10015041484c06006414a000031545c503080440d01c031072084e4000c5035407880030aa520102100400d80c04566103014180b4407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 200439712 1250 200438462 200438471
    0x1e1e031609031707050a0b0411030f120a080901020903060702060106121b120603050d0f110606030d11030c06100302040c0e130e0c10020703031205190216060e010c09050103 76
    0x40c2c03100c00348442418050f490141c400191602401810410003000e40c3e0700002c0180d141ca0903140c08140a144c1d103086078001e220700c200c101000440442c0c080c1040620095007400c128000a04039040b81000d0401000c955003000020341c292001e0154030704c1003802e50002c103683d5141c550002d00d8104031940c0c0017981d6280c0700300d0108001c2c02240001e003080c514601400c94062a942100c0206006d5000900511032101103511441d0040d002070074004090300c68007209442601d2440d1141c400300c81441d4160010302c91107410b07501441d404240e0a01090440b07052104503590790345040c1c2d00b0307100e05600c1540141d080045180a0266801d40690383ca0031404c95038050b0045009203d1110402003100d4859506030003044080000c2e00c1c41210003060304002034010310303020391100c02600096000a0b44020b944103241c0c014041c0e1400b6000540d10030340450610403d0f04001d401506501d00c0c51203d100700d00300841c80d68000e880804825a000060342601d000c07001d0300255442d448507042c903051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 200440962 1250 200439712 200439719
    0x20c01020307120e040c02060a0c260705040f090203100b12010603201204051507080705070c0b0315040e0a0c05040b040207050f0d180b1e1e031609 65
    0x441610111640304a101d0500d21082c181544c51580c5804041d030002e18003100802103590001e104c50041e00c0e000380c10091005018802c03600304140011102da4020b2424a660780e103508403a02c10303070140091a005060079120b128001c01c0d81c54503800b201d402034006c003d00280b4800491100003c00b142d8200b1480c0400015100d250810305104d41000c1c1503854049200051000407a000b602d0382811085035241000902c0001048007507030107450070700c5501503900c00c51044103417081c0998107030345503001d0342e90358100c00700d82c980d1160350200c0d5050030180d40000c42c0c1c04a480a14050800c2d03104d20b4040041a20a103c212441e61065140d59030103030300d00801003510b5082c2c0c0ca00b91131060301d0206034a003400d400710300680f083d140001c05600c9501e0350342c140a10040340382840078101d596010296104002e404042e50f81c140102c040c02c800c20040c00c0d109151060904100c15a002c40080c20300d0600e5100840c800707840030700c500030400004100441c0058107400d9a032500940d08040c21014103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 200442212 1250 200440962 200440967
    0x3041b0506042103021c0903140102160803060d2306090102040510050906250b090a0803060603061801080a1112030712091224090b070309020d080a1e020c01 69
    0x84983d0420421980c00300c8079420b0600c00d00c0052201c000d0541505494452001c000b40107102901c0207440c001d20f03080042e0320425060003141e4402442030120300244103d41c9030303a400380e031015210b143e00414034060500003445000225402e4006000880403110305070401324103191005104200c00d03441000240401d954800f8500002041c1c0c1c680652100001c00100e00648695541c0141411400c6075022803d200007402008a6215452903074181c5c075100242c48d0f5075160450300802541080c00018000e0604002442c2e010000610150f0f804a0903060031040c0402a04911401d4024440600900c810312240d030302104029206041c0e54000620004d869014840c4018000340070b81c00c05080452281e0722030009440c5c0d01c00d08514802c030524010101402c1d080c800e540c007420260110016206600c14185010b0f04083c990300746aa480b0011402001548012644040c8100490004c41c2d4000c01a00c003502e141e8541c079120a1120003208400b0020404050031540700c19604001070341d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 200443462 1250 200442212 200442239
    0xd1b081509070f0e15030a020c190c120516090c020115050603012c01150305010605030601120e0102070503120402040605190603050a06080d080123030604020609010c020603041b050604 81
    0x1803841c00050b03000c41000040c00c101507000f03203170007600710110600c2070f584603640c0182101a110f07812500f005420100301d5000002580300602500720310b10b410408240d82c04101060203101d0000d90b4541429041070408495180e0007848132a5901d030b03103041840c0d07024402e00d0012182403a1301c5841c945004000344044c8070500512411030b58140c1402008000702034000d10b550f13681641950b40d980c50307050749076602651500e0f42001904001c00042e10700c2c011001c9a020b810180d4843c4594107110340444050701220600040c03a40d03003081850007041c0e042c8058040d80b08113003080180c5044c00c0c010001503401d1504014401c00142d8003054140507140076070812100b2074140840c059580010a10091645502c050114011480f10300c0b0b001d079001000318103031044030f0031398003d00e510803950300710805127446681d40540c0140d0118015282407405011408014035160210404650116860b5002540d045232000140b440f54048245105111809400700f03580e2103041500c2d003404040e0b9007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 200444712 1250 200443462 200443487
    0x50a050d02030613020a050a03030e03060c0306100c020109080102270603061c020a0e0f100b0a090e150d050f1903050306190503010e1605030a05030901050d1b08150907 74
    0x1213500e4030400315128038049000074000100250000d0b95a420040c14149080c00f0b114460b0148800244030188a00c003a60f0003800e0141620610a4004c40281c2d01003a8004050381884203c1200188400b4240005d1001001d144040c848190726000907219840d40707514014454101402082004c3d100d007804500c0c0c0c08100204024142414000700701c040b1552b40003001d0900a00040007003070607200100c58000d44a4913107a901c150764071078901449015000c010b8000411144040002c0703a4034000035508044030703160070900404c05400140e03003c9171140003190705030000707011606006424007061802d0003011140b2028110740755001001da21000341042e1280f90603800203086100400030980c0986000780082000f080c0b0040c90030743d0707902c100c030542c01d4252200001065a080106989110039030010081d41421801da00641d00c0d03030000320507010803079555684100c508028441017401c1e907185465102040c2054a4500310b040352a0105070702404000c0148403030151f010030301c044403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 200445962 1250 200444712 200444731
    0xe1207050708060402151c05130213090209060d030207080a060917040b0304080307170702030904111c05060d290109140109020c030f03040c0509070906020c040506040b030f0106050a050d020306 85
    0xb184031000d400c11913003140a006140c7c06103442d0400a840d24090142108030340200c6032001982050316a03903059903644080290000303121004200107080100401c80040d209006403010580c6078088107141c569a08403d03142c0d02e4549941209008074480fa860320540c040300918981030400035510300a100151000b4080c40000000600301c0f441021101c43e520301c00c890840a60502100080d40e940180c900c035172181e403402d5420681500106d08450701d0b40ea0801080c0c1c0c151001207051320043c0001001160403050000101001a01e00c5601000d000d403028a205002224844011141c08058101c400898602803100c8d100700380c0c00d1011411201101005030382da13030850f0741c000d06500811450b803060120200c2803004203c0c8505407035050307400c291480545c40d40d85004c202d6401115109400160b0802c54442c0300500300398010550144d000f500105240c0c011401003481d24003019040c10035a5074131242402070f444c1422101e0b0088c04121142d091502c0a500040c2c0c865030050800c151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 200447212 1250 200445962 200445967
    0x304060806060d0b032a030304030b13231b010c0f021207050d110420040317040b19020d0e1507020f0a0608040b06040204030c05130e120705070806040215 68
    0x34184140c0c0101341c2815024060b100000c00d07001c0c8405e42d194014102107880c01200c0040c03041400c002040d24200c0f07410590419443d00c0b04000746aa00d800c05a050f43d804103441091805102000c1d07802d1001c01c0d03168020120402110380c401041d050a8610b039041100305038419000c80c941c49180241160110f82d0f44c007002c02c403214003500d0441c095201c0c64101c001d5030754400a10035400152040305038103030350031701c00b0151011341c101030400a008044a030510500052021a880d0040e80c04051040c014840c80c01e900c508051405030018a60704c0c00400d20441030183c2a84e05005001c5144140e080007060310400f80b001070b4021351083c00751101c0e1070010130600150340d5010510b43c00400060000ba030a151039950042191000b00e0f004c0c1d400340403040114089040520803101100d800403800e0b00210f09020801865070f0581444000c071544408000c014018144101c41d28420030240d42690b51000d482c000b800c0c1034035540000c081e9040b0b0000c11015803203141071548601260705032141d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 200448462 1250 200447212 200447227
    0x30503150301110d050a0603081e0405061305010f0f0207301a010b03010506040902070602070b090d12060e34081504020a0f030b010c050a080912030406080606 70
    0xc54080e00034203a0640c200720303004000c2810500284081a500d41e401d01080c0d8401d040784080d03908a200041015408216140c0c2501158031210007a00102c1c0050b89010340e40c1c0c00041240d00030141e07000524070b405008012075a000103926815030800c0c1070110320b2540640307029451b082d4034440d15095541c804032182801c0381410460300003650b1644010103107086400c1100f40c285140c0e801d041800561000417620b0010b51050f00d0403500002e0441d407802d8101070015011390010700c0c0c00c072141c0343c0a006020000d51110a40d6210b15102c00082c294400103001c005c5c44507141050801c03035a0301e024014000301801306c00c02940301d15410031000249c4101c0c0660302c0c0305000b840c0e090980c1c4640031851105180d02c900301a0284240241e000d104001181c104022881041c18541c042001c4c074500b51a42ea000b03800440ea411814100784504400d191103090504031040c0301120210301c00201d0303080c40d25042504000c03012506006508160401401401e0044050101e038400e0b4000300c2e200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 200449712 1250 200448462 200448481
    0x3140c0705030f01050103030206010b030108070303030f09020405090c010221030a0509070b0c0d02120406020a0204090309080a032a0f0f06090c06020607111b01032f0304031b02010c030503 83
    0x5030024070015085840e01c0300c0b18208540240004e000171001070260130000945104150250307416550b029001d809810b180d5907042c0c1c01851044140c912054a0b01010400743e915031040c5441849003001420b00c4403503100009080101c05243c8241e1000710340324000d014100042030307a5005100b1180001e49807500320100780788c02019800034103240b6000564122031903000c03d08007800315040d0200d8080000c9690780e0b00c42c500441c001d00005034041c00001c0e01510300780d041241060301904002c40c410f43c03200c22003414804014801c0d000304502038103042407d4980c5500038020350640d0441583c0c015541e0707621030b41d11101c41d0301070302980340145128140100d90384299596940134128003000d40d40d034035020b5120082265504082100081011b80804011401001c81076030031001c4100000c1510040d0300400d080010009103182407684640200303401c40c1070130400c000c100315058691600e8600144800b41c002c0b01c103021100f0603000400182d80104001d0700480d85428041d0b1603680741c01a8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 200450962 1250 200449712 200449723
    0x204050603010f18030e030607050a052d0406020c04020c0a260d0b122e0b0405070504030b0a14040f0203010212010e100801110a20010501090614040903140c 69
    0x46506440c02c132460480040c00320840421a101e070301c03401081e10b5007008140c2c4850007101da050108508200c08011240300d007000781006d0243d2b040f042c220f0a03244800801800d134400340c10b51410000078044c81020307010400070098a004a800703601c0d029840c030074140c90fa110214020200c0070a0882c0c00504070b0111000381d502040c00c0e00245d00c0e1580291801c0103072503078a0b98140a60614003505401210100c0c0304100100314150321070100c44000300b40b41000500301101c0c140940e80d003000c1740269841d4084c03540501c14541e6160345650640c2004405140c005d000c00344c04c0b502d8071000c8030031000711030012a400b41d009030341040001c0b0f0070b0000c01c0c0648608844600f01016813400844d803182c0460001c0c2c0101e90708012001031580303e66615013200c078100b42a101d9a00c0621800304181d11034200c81d1490b0340f0403021212103d050b5000d89095400030f80120b1941d588070203092042e02c0d107003072904490440468040c0690b041c0c541340689503405100503085041c1c0001030464072030b4400c104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 200452212 1250 200450962 200450981
    0xf060509060d0f0203270606100504090f060509130b1b040b030f0a0c03020405091302180f0915060612061f02011524031a0a0b07030f0201020313020405060301 70
    0xa0501c4210303c10549540207500440b01210260a60004c400b61440c40006140c041200c080061199443e59400c000c00001f0384100c0ca010890304000102d41c0107075a000711016008480c001140e1a4240402c101005d000207100342c54004060503520045441140c083c1c0d041902641c50318120030440040e15403511854221400140c000400e1100c4060071440480c481c0e10301203410022000581d108500717038070840c03250300e520100d07030070104401c15074410548124600c01400c1d0300410140300d20780300e5031074000c0b5110006080c01c2030811041000c20f200b0b140e038507202e0b4141c248441c40c000c40065500d00032030384030550a1813a200010010b4031295a4070005e0b0501c142041001103030144000e018000f4035407841c0350040000c00001c1c2c0754070642c00070020b6281204074a400e081444108500800b07031503a6045a06c0b200c10500039080c0c40708284200540a030004c25540c07102d0030304000e80140c0035450f2900c1160301c104104035950b42010b044108041e0b04490224542e22a000003078050718580e00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 200453462 1250 200452212 200452237
    0x6090d050f040f06080603010b12150901140f070207060c0b01092c0a110604060504050904060b04090b0711060f0105151309020301081608030a05090d12030518070f06050906 76
    0x10905541040040313210b103034201e0089c024440c816050001091400c0a004005d52240e01005440317000f40c420b29901ca40d1040000500b044030031028110200140e8a010310140e80c0c20600280e1541480f00c03902414003401c4c0010a040c890b607440c0d4010405101da648101d98031482e10404480c0094080c0710341d800501a003240c0d4174241d114a07140c5100300c50032580c000101507140c40038103002e010350341150b8150310f907203042a00c5e00081c05500324004104440b81c6541d585140c02c01d944910400c1031a9004501024180c54000e1004d0300d001039455402c0c00640c02074080201014030740e100241034803000d80d291742e2050008030b00c0e680719006000352160840c900d520081100e0441e41c2c00380d41281c11701401c84100e1191217110554114440c00760005130742080009561060280004011314400a408004228400c0d01d45a4400d08081041f500103522541884030001c031080700759641c04801c03806025410b203030400b55030342282d5911581c0f00344240443d00160f04d5841a05403500c852420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 200454712 1250 200453462 200453489
    0x9040c0c0506330f0906060f0301120b060108040b041502070602030a0c03230112080c0f0a060b040e07030212190302070608070e0105033606010e0906090d050f04 71
    0x11000343c0503034083c5100c0d00c00f03070091420350f0750b903800381000381554400005080f45003121018400e0020b510340c014420750304604100449035550359404000e50080c890911100104404c0380f0b04058090000703450a0b0401026205000c0442c8ca01c2105a400c00d03807115402d001e445003540c1c00d1000c0d00906001814580c4044108010400316410420348800d8990701002000200701c9000528041d0004030640c80c07071404010310010060f00e02d0342080900030003d180c03d05c0586590b01d481e01c01415840c4080350004268203003000014000d07580880e808a80a001310400800002c0ea0340c1150700c03000e44201100c40d140300300c1c4c1c501400418080030601c0c2e00700d410a00300e400c0c0a540c8050911940d00010611000a04103510407284030124072416569945942ca0f03c090320004400d205140c0181c81c0103444c8441d042c8007414510604408910300500007542c98884c88001c030910003048548281c00c80e5040141400700824510b90349101401c00381e848982100701884180915006a00b070400324 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 200455962 1250 200454712 200454721
    0x1412191a0901082b0210020708070308090d2304030f2906010801030303021b071e1706060d1b0611011a0a050424090204031a0c09040c0c0506 62
    0x15544000c86160081d15000c9560740d82e801d0065454181c50b825065403e042c13000035900c80740010030340d007025005104554041200b0b103800c0b012640401310450301000001191802c15400a10075603002c070141001d00784001030030801521000100d80d24103160002086141d40540784103054078003035504410300d04200703030551a110b07a000301c038102210300c076240780c0504143c03d440e69a0321600c10f09041c5d6070301040e42d10b50764055010b0f400922412802c80480c1d03403400405201003084000030030051450340c00b80ca440f100030b088104441d40086001c4907103054116a448000a011508184140d90901c00d150b9941041041c0e1507030b00c060017054400130030000400640c8100004200010030b4004c020550f580e00d410048007140003241a04850b4102c401c105521f81a400705046441c5c0c07440720445000c0160909018a006070031000c4c94640c0031805100f440749003c0545091210340101a0007400d207943c41c0031460160008280c85a030300d500003106580c0c80b03a6000e22105501404543d02400d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 200457212 1250 200455962 200455991
    0xf06051e0c28020a0b0904140c09040605030109050c060f1c050a05090606010f03020d020d06090c09050303130e13050a05101b0c1716080c010507141219 67
    0x11800c146541000c400e51101c26030b0103100d82d041c8241d600900f00c000580c41c0c80c3e10400d1582100041e182d1007a500c1c03510604003203502c03444901c61035071184079550b036410000c20002295800d82115000c1da142c002044001400011440c1d02c20504460640d16084080319801107880b405c0c54099480313442e00e6800040c10415084540103100004084c007095a03250110360340c8000031108035000420a22041000e14040e41c01000310b04000100586445881980101965141c1d4030803110350340e03074a11865015502040607005004210051480c010b2005504a21803401d80030701290501640c020412020b002109403034003a074040241c5808682c6410034684500300034500061050500a038000c11042002444018820580f241c0911901d11b803900401098480346140c11a4800c2100801211390380c0100402c0c14030510041d643c0c0c2028004640c259407025044806100000038400c5c1111098000c0d1204c81c000f80003200320395641c2d16426002041b1000d80360010740c0c0780c00081483c2d0340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 200458462 1250 200457212 200457223
    0x60a021602060a0201021c2c01020405040c02070302120304151107030605010b03100e070507150905060f0403030f0c0e01111216030201112104050a020303031503010f060f06051e0c 79
    0xe0402c091012140b805c01109031123080e0403104001c1000510704c800c500402c050007078103024070750005040a072242c011078100c0c0e6070303500c0070005a400100200708510f040b01d106820340e0594006182442c2c40c1a5180c440784881c1010301c001d100010311007001055040103944000c540203a82849196074810340c0c88955031003542c00d110704900c031100c0825902038a84100f8000c4449a450916101a6458200c1c199204160503081c1c0c6071030f2150200462030030041e00703001d91068090b403225407c0501d00681120710004040644a00788118488103681102048080d00301c03c0c00d000c01a020f010641d281000110800c1901840c0702044000c8111508408488820300c250000c0000a01000152056000300f00b0303800300000da0b070003154400f20032810079a50090300c140100c42c0c403800e1030703800241580c0040703440401440103c801412689402d00602c4014128407200f04811030a001c400c003041002c0b401241c080c0240003071f2410f519016141c0c0f00184c030032440300e07980d00c0b0a440d90b207458481 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 200459712 1250 200458462 200458477
    0x120a050105010216030222020403021e03160509010b1b0a050706020f0610090b13022d070f030f180b0a140313151d0c030f0a05060a021602060a020102 66
    0x502c941c0b0241025044d4002c0c01205030303a001040200c409000943c10f5070402014000e03208219020300000005071200203c1191000d843e909000c070502d46d100070306241020050300e2901400c0410b108200c9034403851175460543d09a00021a80c0d800c100c016a07810581c1c1c150b40316058441e01611109201c008036070041034a0703c59083e601030000c004100b1795555400c0c3c0319021103079005042001040241c4c0c0c01800c04031405080344070720385024446a42260044c0710301e018040c40d40380503030864240c9003031009400d03d14514a281021590307103031075810030101240201840010340b501c040d0207000f0300313034551409005116801d1254440400d007081d900500c0941002c070b000e00840d0b821020200301680e02ca10907816040c0d0300084180c0b111112101e00d104001c0100355115050504183d1106140e440e6180c210300038170038502041c05246c41c0c05500100000d550308a1520340002900c0800e146400407050600540c03606291000480c642101c614020b50281002580c0d24000f6019000740464 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 200460962 1250 200459712 200459717
    0x40510230112061a070f02060d140606070510050406060b1303050d0912030c03170109050609180c0409050c060c07060801120c05040f2c1603030207030f08120a05010501 74
    0x40b04891011810f44010b802041d8032240c0308000005182c07000000360200c0c03801200804050101d640208508d58030060350200301c203403170b1aa99150011403855443d0000002d507082c0385031020503100e15480e031014502c00040b880d103500c046000e0088581101001d0080d21600c00c3d0703030b10140f680101440c0280e04c0200c4460284070411003190b40a01180c0f4201d030f00a5084036a2500190b03021602c4021444046050001e0300c040f005a0701e0000050030301801c400d80000416003001c02c10450748440040c040c0b10f0a00741160180c800e200c01091444040009480208000d125442d10b1414440c41107030f6540c210f000817540524000300081c3c6142100c815807108e610590720788400480e01e50104002030702015811104009a0409501080d00c103045c00c0000541102800240241e101c10300d1106e50045400d1804500440d5080c4400b0024200e07903c0745201007451698081d40b41c090b9480041d0110540a0105007485544400c5980b002d4040c5002c05180c41c1002d0740d000145800e0185500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 200462212 1250 200460962 200460977
    0x230904021807050d060515041a0f030103060905010f050402280305030c061605270103090c0305060114221d03030f18012c1002070804091113050405102301 68
    0x80c0c03410002518090600c0c1480c1d00c1f0320f481d0031f01c0c2440004000800499140c81c49c100802d08a980c40c00004d54007a600c544404600310959040c11400d6441440c0b03581c10861500c014080180d13510074a04d41800c000403400c12031500c07036803015400c2c000c1c0756102405074040024080144203000c02c0f00d43c03042d4402c1e65841c0b90300b180c959003259240129401941800c59060b001034420107000ca000c5040541450017083c00b0b0840c0d0f64000c0c1c4448650f204481c140e10040060240003a42c0b85202d0454005403101900ca400c1038600c052502c40304110008050743e911407802e0407082604500008050000c1141d5031303401c1c050a004654041180e80d80310303108480c845851080c406018403030385021044441c140200020342e001e80b00004151081405101d0358000405c00585c90000d4040700c0c0c00380d40c1d0a80c60b603190040c41d0081e00d1550100e504485802c0001950301c3d4664003114040c3c4000350f900048a80d144104801144c6054010301e071300600030041e03403034403602c1008014201031003a81c9001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 200463462 1250 200462212 200462219
    0x30105010e040b13230607110a0203030412050106050603100f0515030609091608070510030902030a0f030306030b2509120b0405030d05160306230904021807050d06 72
    0x5000a8054400503c1d030480b0304041407420000042101d449801500100034010110b00070b102c0340189500407810640040701000b4003141c01001c40401890030001514034003101d640003a40300e2166015007402844c420600318280304003584035a01824024204680e0b074140304284160820081c032541400401110000c2101e00f05000d91000c1405c280809904545400c0201300a444005110400c14822440900105800040054001d00d040070142c03541501306010b0242c000b00610030613050605050085d00162030000700c01d041e0540016170720980b800300d1720f000c6000e0036085c1c1c405420702c1c03055001c1c85600d40c08004040e281c840c10f4207005e031a4107180c50302070714108541c0c4100307034641380350b420080e0114003201642c0d82e220b8899015285031001c2d107110b000840f0340603501e05c01c135808071600000b241e94140c0300e00c0015001070084200306030b41d00074100580c5000c0321240360088113840d011800315103510001500d0903113000e200404501e485036004110760000328414804c5421b085001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 200464712 1250 200463462 200463479
    0x5061c05010801021201031212020f0c06010f05010c140a020a15020c04110a2a0b0103170c030409111903052e05010f021006080312091b040f0609060b0903010501 71
    0x50b80d05d0741d4844a42d035002ea1031522410481c40b9210051018071041100c40e1200c070400e44002d185100a1595290b1500488083c140c80c110050f0011300700004052002d11003603800901c91544240c2c080107500041440b501030608080070b115000390040000780c008286207201820300003034464254203c130008241101008140d42c0892080c0f1b03141001007044400040c0f1070301c2d18490300122454045400c4010f42d9119000d4040643e040c1c0b03a40c01c00300014001c20100c403080280d0481031a146500781580350800c141c42e44611312039903203110780d00e66800c40d41104050640741d504030b83c000310500c1070044a0000c0c001e80743c101c55140390105820300c0b415030b44201381102c440a54082045400090805005540c084041103a500952050007280d240b4180b540c00b85e0310160510b0f601840d20b0344d501307a90f82c0050b0752018003415202d0300407103489810000b16000c4090307407040440d804035884103451500c5000309040d070800070100d03052002c0400c0844d0190000c000703051041c1c0003045603070303a5511039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 200465962 1250 200464712 200464717
    0x5010e07021b190f030f05010b2b1113050a0605010c0b06090c090306131203020405030606130f0e06061503010e07050705070f080a110114040e1005061c0501080102 72
    0x3040c07940d81242c40400b141006409032002040706544032110b0b81e182e03056506003621962046445d40c0000441c0c2081207020700412219090035601d070000c91000d5502c42d81911440b100d108503948200c014542440449580d00201d010302a000c0181104007900c000040d00c000c81d0340c0c02c94182003140001c1d140d441086487e0440360420300141c440d45980041204110002e0401d00d800042400b412501303035000d1105d540a0840b2208126004400e0320b4948104140040d117075050500c14001045151004503020b030f03220204646e000704000c440f5580c00001c01c1d1402c0c01e908068504441003440c80800201d907405510100c94482410000d10043c4025200902886040342a0200403c2445001c0c0001d4444140719000ba68110380d140d00c0d800d445912a40e004503419880b6801450600092010540c11203201b131801125591801c07000c1d56183c42103215400d90f40c0c1203072000400c14117039031b5030401c050900180b181d60f88003400701c0c5242d4280302000300f810056140100000d03c0b514140708 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 200467212 1250 200465962 200465983
    0x10b0307050403060e120a0f02011404080d0b011101050106020d0809120a08040807080f0301030605100308031602011b020309030f0705030606060721110111160b070c0b01030605010e0702 82
    0x50303542c502400c50703481c403029002d1030407440d2035032281212070880c03004100d019000c02105596034442640d150040282540c2c0380b656035850004168082c0004925a070044860440301c0b42c00100e400c45a000040f80d29456440383c42141c1d518240001c5800d80e80480c100000b00388079514086940c651964240d03c40c003107030030154040b220801c041d422850027440400d40c814081c031921424844651248207480d80507400645100c80700100500400c019481050380000400000d075411504555031b044951001800e0150300486c01444803030701358800d40107103040d10410030300d00f1a25880d1000203592504104203075407180c02074421070100040c000034004120392006006008944500d410312007140e1200c3c50035200c0d500d290140c1410081a0030500d100c03060a9540e980d104005102c80f9403c442c2220600e01c26000100030300880d115180324003080140e0071417400c10180d15082800d42d014200388000401001c04200004280003460340428101c070114078203a49035035100401261074010443c1e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 200468462 1250 200467212 200467217
    0x1a090d050c06041212020c0610090b0d02040f02040902040b040603141e07140a09051201020a02030d0b0a081005070807031e09140106030809040c0801050d060203041104051608010b0307 81
    0x40005010130784845121000c0026810110303e0783d83d8002d010340036640070380d55a8540d540303c03a007401081d4410781c0003980180070305981081404100302c001031520003800d202034440c9495120140d0400d503a9411500109010841155a10394a8840c02c005400c240729080c0443c0c40c10748030002c1c80d01c403181c0c25446594008104e0204450710249001d4162003d00900c080014481031101c40c0d0340040024480040503482c1c0c0d01c0340c586000100724403241000030100703c83c0d0040c0241c40304c40e0b8001040c3da0f01c8140c4224045203212040c0003040c915806540000e140b4441e440180042000380d40c45030b405205140e6500203641e6504100354240c07401c180781200c80c50a0b08000015a00030b036030046905611450903102181032501c149820348030b00c0d4100340c1d030b1004000303284201890103100f2311002491364100140b20758982800511460b1803244098101c030340020000341004a819803600c8100d00080c1308004508000c51300403488010034041d10003185200c0004034080c10607405680c492903499 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 200469712 1250 200468462 200468473
    0xb010806060d02070501111209161409130f031805060414090402040902091008071403060c0c030c03040f08010c2c010c0f0b100b0403020307030f0206071a090d050c 72
    0x8a02c200c025070041d2400c5c1d55555886400e96040340110b4000c05085950507030110f01030030039212150a060300445190100060200c0402842d000d00a0390102000b00b198220001d940d02d00c860001044500c20041c10608021100c408154008000344041005c1e0440401d010751a24103002103131086014450364109540481101407500c6d283d0345501910103040030500341c805902143c0311741015110b50407031b080b10900610038100200040c4008060030200b50403407104c4c030000301e911100041d02caa200528000b50071280b0410801c100c8160140f640304491340c0b5030780c0708405024a061402105910350a2181190301c071403054079210340c9440002c003c00c1c1c10940c0101c261004c1903103c3d0380541481000e45140c0c000c60300800800342c07018010074441403149040b200c0b090746203103d03821034115900103110910150310001501c0050b25807119120307081c440c2c1d03800012400c0c0034001c0014081c1d0080c0d108204810311219010b0300800720003040b1481003c81020580d00d86c02103440041955016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 200470962 1250 200469712 200469727
    0x9080c0306041211060712110313031b0c08013207030b0f090f090c0a030510091509060603020f01020d0e060d0912050301150807020307060b01020f16090b01080606 72
    0x56400c03105500c034080c1804c071107203982c038800c260034000e044903100c001c114518464481040b0f980140801910300c1035100b451850030419411500d00d40c80c002030200700c040303090b001501120410108000da0414600c0c80d00c80d5540c2e0245001c0c041c080d545848000c800407552400c80d55102c0c403c0c1c0c00502c2a203c80c3e80f43d903105d040880c000c2003213405140e408041210705825036200c4c240310314041c1d000050b0100c228501541d140d0300d4007150704401da005060b1100100701141020610005143c0b8194003c15058101d060038400822860340720580c9610b4104481c00b002403d9000000310380c1300744c1d10103c4081c48130005a031104061085070000c100d49100444252400308010702540d0180840000c10101c20344900d801d0b60b002c01c0040c004a1800801402181450b034401e4040d0500c2d450903075441d141264000b500d81c02207400090200e600c80c400800c2d960f00038040400050044c030b040364110744002182c994548903610500c44980d02e030000c4003005510648200340b01d520050701061130602e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 200472212 1250 200470962 200470973
    0x604260301180905280b15100c0309050405090d02070b030108030714030d0204171c0f110a150911090403090317040506210601032f0f03040302010c09080c030604 71
    0x110b00340111241e005400d40541c1c0c030b803040d40c60502c480b21740415508481126140c0104c400354094405200300145410070525691a454030038402521480c141d0000600c0d450282c810014903080564001e0038041080000200003074506103240c52a407c950989594240e0891148020b0041d00e84503001000f0b00c9021800051918415160312012a0315041c0c00d0610f0b202241c1007070f0031850b1503400d03500c500c291200701003161556201c850f00301c51103410740000000c2c00000200c0b407101e0a206603601007101880303043c42801901038000e05200003580024400d00001c0c006650100c0e402060344006c1446030510944c114840d80d4940c603004615404c0da254900d421014150b0030b14001c1c0108400310341c03501d81801070f12250341180a8130107440c8401042c07204005008062504240c90020100610307038081d000700304d901c4400c8010800611240c6040d80503440f8465091034541c0d030000911040642c150b02071000004580e40752280f49490b000143c2d1641d1003400701d1030b45907124401144c041407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 200473462 1250 200472212 200472221
    0x9050102072c09160603050105090f040f020d0b0a0f060e01030209090f03040311041b090306050c0c01020f0408010b101e050d0c230408030315030f060426030118 71
    0x5080381504030500b52640022245200c11601031400c1e800510040321035520541503a40603000c1418188031a42c1031001048030030170000c08860121550102240500c4400031800580360b4015080b03661001050400c10181a015a180041341c0c3c03034111100024100d51140340c0c15a00c03c2c81e8101030a902e1602000750b40480641710b02c105004a20b0720100082c0100000d2004500c2180c002150031490300c1013000315180c40b8030040314030310b5174012442e5080e40b0076800c20607241d00500000d400c0d01c400c241c0e0f4129009000c51941e01c4d43c8000303040140d07d004140a40226140c0d40002d0101a01c4101400344808507504040302084002d40c03103014410131420f00c190720010b00d203486800c01d030011640c0310544400c04142004544201205015440282d005483c030300082000e03686000d140040c015034034440144440401c011140c080e5003960b400744002070ba2030904c00c0889683d418a404c010004055220040d201000ba404544840703007a004217886c1211884140d001c1c0002c81c00d1910005003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 200474712 1250 200473462 200473499
    0x80a090c0302040906060f03030c02010215090c130b100302030405190308071101090206120702150c090f06041a04240509040b150d0c0e040b090115210c020d0905010207 74
    0x1151038400104484e02c160b0340390310045008ad5501d5032080501c0c0006401e08624010040e2010804010030114100018230099015403d441a210312401a000075000740220780480f544126544682a034030f0b031b4160041c502450185c4240c5200c84c5600001c000c060309010002004240001c0002d103030075000d400c017015401c0c0c42034001b0450003165400100305a0022810b401040c031184244002a64100060548002c9801506130381d410103100340c0c0814000c04945910a10433200300500c20b886000503600141401056a003a00d0566000d03c4c135aa0003074010f1400b040042640c0c004504162421001e801e10b00362101440c001114040c04090000201c2091704044140d07044007460300c903680204041107003403000041c44c2920701c0307006001c0e101e25507406110300d0410290504503a1240d00540c1120012220344081031107010003a26282c600f1a214031402a00e503002100c00401c0c0e400c502d9544a503a800c4d1442d50003081e800b41c1c2e60402c240100750050744030407000c1c040881c6e50143d64401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 200475962 1250 200474712 200474723
    0x3070503030a0827010f02030406050f04031e05041a04030b0702070f120f050d030c090b09131d01180b0105091b030a141003050c010203120601030c2d080a090c03020409 74
    0x20510203005040c2034480c0104070410b25940042007005200709032080c143c000814330100d42007424180c44c0180041000d01280303074115030703030700c0442c040b280500300301d034010609840c1c03c1403d4103a051810145c0c0d009488203440ea5070401d00040d1480b44045030100581e0000d41d8200c0f8460700b0300760b13241a428120101200d074242c50000200101d84208080c3c180b00005507804030f000600484c0c01050b40340c06a01c2019440307014450000140d50341c441d140c0802c01494000244080001c1c81d5130503045100001005c254a1304840d07500380d44030112041c402074001c00b100700c03081c3d98030000c1c402921001c1b22407249458030300300002d210400b400025078109480550205042c0581041940104400d90340d86007004c403000002c10800c6401c0c8400a1182001d002035810054600030820001a000700300354101990740500c000040c1c01000d8440300039000d9100700c0c444c070b035400c104d0705c151441c440f1410011030900e034001010700d80c941c01550003160f800030f60204010300e907a0a201c081c0000c20300c01c403038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 200477212 1250 200475962 200476021
    0x5270d0b040c051e03030f070309120b04170c0c3114010603140103030e010207090204030303020307080105040216060207150207031d030109031b06060807080c03070503030a08 77
    0x4210a0900540218010440998410303c1c00040181103500b009032803000400d10803800354181d402006890002d500e8115899942041d85000c0322040c0d4207400000320f000c40b010301007042c0000f00321542d105520802145002d204481490007541c0a90b0a80622030340c00f00c02518101e040c00c01c2404035562070b00c0c0048001ca0346010703200013464040d07a506c034401030790740340d0110084c00815503050040c015402c08000c08d0f0070104007944c003400140405403d000e00ca8181c448980d101300041c2d0000c001c010411910785d6140d240c028003950013034030300710005010a000424207203007038401c44102c00c106900042683c0d032182d03500000f9400c41d01d002d8500b0038900f241c054034803409000608285100b903031010340c0130030302030500c0c030806d012110164041da140407035520010360014142c14021194903042143c172a0380c0d01d03000c1c0280081c0d40141a150003030382c20000711940e00050000c80f1003821415a030500b131301c4600349666030081b5490b0f840065203007008144a406e02c90200c17204a144200300c4d86c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 200478462 1250 200477212 200477239
    0x1503060421030f0513031b02010e0603070e1507020102010509070f14150a02071e0b040b030c07020301090308010501020f030711010503100305010908041d1e0c070b0f0702010c0527 79
    0x3c1214011100360852005d140184820103a00501a82c20380c01c00e410500300d410490340009107001c548420b182e001d0000080880c0e40d046c040d040720074000f80003c200051000616000344150f07004914100d0140d801c000c04a08406404a21607080e0344c40d22002540b0b103850b1096024034050821012500201d00d41000e038001c012860045c20110a41e40003010160300d4842009031121000f40c80390840c08009004ac401d40b000d060484040742da007041916180d07160782d0b5500001d0310801e00001d5056107040880c0742010b4004205e0b40c12540260252142d0314050188030b52a0b1040d244000d00010134918118140d600a1001e99004a0601101c006082d00c0c0e03943d007400c660098a0603108980007040410800c10001d995028440315101880154103080c05085a200030480c41003480700442000104410713445400c0d14040c0c1e810245200790750070606100d414550301904c009005509044180c1c8140b0b0080c0100e501e40c2c402e8802c00c0310284d0901c031040c202c106808a44135448145501d480307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 200479712 1250 200478462 200478491
    0x702131508060405030705061303020d030c0302090909060a0501090c09051c1203060f0f0602030703200a030903050c19140d08030c13050103060807030b09070302090f150306042103 79
    0x20784242e2140000356a140b00c1424074515029004003900307409c01c0e0f580c880b5000250f010a50080c90401824003280390140650b05070701a000b208041600081020100302108034002100b40c051165010100056625200c1000c199002c2400210104024a004020a080406902918145410004410f81019a10030300b44180707110342540020f446010900502032512000c00c02008101c60000e0400d01d4201c001c0d46130301a100d406018400701e000c500c0700454858079010102c280c81d40544422940615003d0024481d602003658103208440342140c8a08251842c048883c410080c1e251441c2e140040f061000a8510102034000d00c0220320100040d01000c0610702885480b594252111003640c095481c01c0c200394402c030704045c1001010001c0407008111581034a070091090300081d910b00b000c10f4a84640c2c6c0e8002500b00c1c0c4444104506c04048400b418024001540702c04424409034003016034804007074030042c2c03104141d010101843c0d0b0a40982024543d40c5090219040c440040c12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 200480962 1250 200479712 200479723
    0x1002030c070512090108150109090c0908070e0105030c0607050a050105280501290403080309061b030106052a070803090102120f0702040b12030406051e0702131508 72
    0x20303080440c804a40602000014058003014200605000741003440410008010f42c001401003a0300b00740c0b40082e031429910030b000031800351240c1c120038416400b500030002c18002d22840717960782c14085d103080400d00c403040d00c00e128101c1d0310040051030040041e408003c7d055103c1c42d03040311b00b440344401c1f032070010b80d082c0103507441107071204050008030b002d003140f600010304084030800e402490900180301c109943d80c004090307560108403071204500664440d51103441181c0004e46118408010088822000201030380300301c004442d0050914115000030102d80000c0c011040420390500603581c80d90042c4200802042030040c0d0311003c45c611502481c01c089032034100c0101500000340361203403540c040019180320507180a200e0710307040c0021a0040305018540000384990380790109402d8541c0d40c660740308040c0c8454800e2700ea80707607542e120160190b07208040000c0100c5041024094410001c0e0070b480280350054815413040c04003101450082841c124400d007900c03140e03000801c070082c08200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 200482212 1250 200480962 200480971
    0xf1833031e021302030708010311010504261e0703080d140901060303020606010c0b0f0a090803010e0a1401060c03081009021b0f06090304090c12090f0b060f010c0f05100203 76
    0x1094181c14649005100c121030741e50140d0008a0b00400c1400b1145520041c0603044a42005c02444005502030048039284160361100e50140400c110301100280c15082c0201843c8850b0116042e01b0228003807003034201c0e074402c00c2c42165080700800f0000301c0c0241000b4401c90302c0300350340081c5005840d4904000e9107815038004000341c1d501d0100744100350301041140e0b000542401c00408049807503039000f02d82c2400170401000c003182200840c8404045400140c9183d521100954807580c4440781c02040f004119134195003141080c966034803954030100880c0c10780b55903503605c0f01481c6194809917080e0001a051002e54409400006088070b2180702511518080c540c46660071314004050910780524039240309415080a0280b02440000000700c808458517594003003524225114160b6426541503613040e149421f110308001084400ca03001d01c0250b11802d0720355495220300c03007803165101454401c40d0204181512540108070300400054805d44030360110360580448181040981c1c0082d075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 200483462 1250 200482212 200482253
    0x50a0606090513020a0302040323010f0b0a0b0c0a06020304030f02190b0a15030c090b12070501020601030212011b0807030f06050a12060b030307030314090307050307020609030a0209010f183303 85
    0x490b01d280f160003030088200d40c402001c03007840200f00c00b50000e121442d550fc28030960385400900f212810800340822143c0e181c02050440d107914003410064034000007a9286401030003541c1c109210101074180d907001c0a6000401c4c50780690f2000c1c44e103001022942145d8054240544000000070000240d12010309407400d00802c000d8210000c0c407016032402028003199800c152400d00c0f15980c00180541102d03011034440d81000c6a0750042d0b4010040c210b0303001d00c05c0440444141c07289400c040c10710f01945050741c0800c5030043c0021903804640b158001c041c1c2c85041d0a070200459908180074003030440c0035520000f000c07148040024903541c84031701d0440200c1d480c0e40125030161810325140750302508030b2001d1450a01035681e0f0a03200d11907400b00911503c0e001c1074144035274600304108030781d20b40c0c0641003020740c0d61118200d040161540c411400004000c040462002ca85d6008020860714124002d0342402003442e00100a03005804121514000c071482c000007141600e000c0d03a00c81050720 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 200484712 1250 200483462 200483513
    0xc0d030b10020a02090408030408130902070308070c0201140c030c06010f0512070b03060114040506030415180f080a030e120c01060b070b04020d03030b03030706050a0606090513020a03020403 84
    0x4051000758241603401009540044038010050f03201c3c03040d002e038402e5002a00e00d9807075880385400c10407800780c041c49178000341c0c04080124404100740e0090041c035000c0d0f151460140e6400b502203600c0c1e00c030100c0c000c4c0000d10140220401260800160154a010300143d9040420040c142c5242c0842684101c1103003120745800c0080c0e0034103803031004c2841c2542c0c0140040c5814125a82098407010342046e0402c000304580c00c208080d9201920701402c401000195642000e0130420740702011014004059450f05c518440c1c0f003d0001e145520a503070005c01d12a031400f00b074551004a40002015a0626486400d0071000c9d010520a580211a88012503a11b688450809500f140c40c5500a005125020441c840104030340b5100c1170780c031503411501c50014654500d401c0b00078084507000309401d4840401c1140402500350000c500c01c5216041c03c026055840c501142c081586102e1540c000702c41d074003c905032212a80041204460508000d458a80d40342e90b4860001010740e0900761301c9100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 200485962 1250 200484712 200484731
    0x60913061805160e010905130b01031d0705040209040e01140117120904020a140d0207050c06041d09010b030312010305060f010501120f090f050c031e07050d080c0d03 73
    0x140785079810030008180304102501d08400345404140c48101d40106102101c000d200c2c0c60b0703104080180c040d24000c7c009022400550701c0c04805807085003200782c04682480040030882d1403d50705058502c185000400c0d08515080070f200080d400002c620303030416200c20881c800d5841c01d0240b0031030000014020112580b51200c5ca042038424016658256040381a00d09090180341c3c003030300c0f9981c0e011175005903a00801802580d0051744203003203050508010401d02c41d83c2c1d9041d405005500c0c0101c003642c3c000c0d0f1100d401c0040c14070130740c050402182a07e02400d44c08803d030303080880d8801000c100020f14100c4800009145401c40e00c41858044840d00050042082c01e001c520303007202c290400040329505140000c0c0425408414071286036950310030011100c0740c030ba000b20b4101d03504003031010701e4040c050074140e849116244200b8020310a049850380e040c014204044518014940601003050401d002c0107040c00f0044000d542d01401806640c849140506c90f400c1841304070746000408030301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 200487212 1250 200485962 200485979
    0x8040506070302090a141201050702010b01110a050706110a08030f07122f0f0d0207060b0102060114100504030204050a05010e06030d020a0b0703020427060905040503090f06091306 79
    0x9041c50201070041c04609803036103807900e504017500c1c40022403850202038107010030941c50f83c40c0315a440d02d6007040144a5040d4041d0310501d0007075001ea84281d0042081d01da04ca07901c00c5000c0c0c0c000c14a501008007001554032410f5064800b040c41c0ac1a1076010050342c90700d5031a50420b5607101c20203089402404241500310700780340c03010b0300408000c6c8074400d000d80d9600c8001010040004035104616502207003003400d102141d0990906820700d903101d1020141c014001d411a4408503036540c44c004002c042c2d9800018854102c0f0320b030000d48800c2d400503000340f01600c0301404a005c10b011080c8000700060fa0740e405018442c0c151554002841c1d81341c6050a2181c45c409008c01d40650400340300c68055541c04900005003c1e040001c1d0510b507161084120000d01c038a51044005040e84520041e14403084c586030810b480c1c034100140601d07521b491400e82194030981d0020302d1680b007044185020f0070400300c51442d1a070300515003800d001c2c400700410480040340540c0040195100424840f210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 200488462 1250 200487212 200487223
    0x1205340305130b0a05060a090e0a0623040602091801060302190311070303021b070e011d130303050703150b0702090c07110d0f0c03061d010c1e0306030501020a080405 73
    0x5207102c001020390100c1da1940c0d607061401404042c0740f141c4500000b072064503000c001c0b038010719200e1340800001c1d11942c40b0545541c16040101da55505041200075203400142c0e44182580100150704d14035191541d4040c003c1d4080202c0e9a0040c0b05030910003ca1111241614002c0140da10f000d03944110310190b0a00c8000c0ca041d901c81407518001c0000e942035000d009542e030300c642c90f0600598030441d01c0c0140c000340c041c4000204181c801c01c100421946084540075040700c020001556581c140e10380e000c804150122181113034192000410741c0400c1c42504040d403c1156801c000440400000d0f000c2d50120b034940000c1c034042c0f80001c2d800118101900e10907407060300d01c0c0f135490900600340e0b11703100016042c094142c8581c2c4554404420b004003c0814030075260300c0f40360300100a80c0c074034141e00a4204070104d490342c60368000410b000b08030180658103203401d040d40d0310203210500079503484050f03254004400070555a00400300003c1ca0902c000e288503540351700c52040300d01d42890141c0c0b402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 200489712 1250 200488462 200488471
    0xc0903020f0901080601090e0c09040303090507060e1c030318050d1103120c0a09120b06100c0507030311030f0705060a181a1302040c090609080307031205340305 71
    0x1850a84010002e0144c040f030602d05468001902040005400780b001d45000003041003203038410301c48000c0c0301c00c058255100c4120244200141c5242c9d550340c20040c0c0706c0120018580e034014450a107250f5861007128244910180f190400240000c5505034881c454a05a20f04440e554041d01204008641003046036032480c01c2c071401185865420304c1030b2107030000e01404000d042200881c9010603a4000c0ca942c50107043c1c2e2505520b203400301401c108540c86416100743c0e0013140d003244490491f510680500091301d03086801060140d01d15a8100c0d8100750040c00c036002400300744404083e030f25080c0001c205c01409071009103041e041224400f0101e41c074408125540070714907801940003510384989440809044000c0c1000b542d100c04500e180e94400f624020741c040c0c07404040341072441d08868404c0c143d81d0325a841d0300c603c0b5114038110341d03a0300c248100a404182c1101107440440c65a0704107540c4110303100b1020820a4091680000c1500c400140030117a158916100820551504c6015400b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 200490962 1250 200489712 200489719
    0x18061e16051803010905060a090b06040501060813030e1005070c050901050a0605070c09110c0f19020411041e17070b0a0c020d0209010b120c04260703060c0903020f 72
    0x2200d030911015159101d5104800c00409202c50038002c02e580079802081659000402d0f60f030030340780c840c56840080c0000c0ca0708541181d4500080340c52070420348241410b0b18540d4644129a031a0341080304d1488100210840402200f000700c2011130300d40c00318001c00404507488075900da11041ca0300c1034192100342c20240c0550b100740c004103d5692865031320001c480c454107265a072105541801c6200d40d410360800304510f414a030400403500f52120040c5601a0070209a0f046209501500c40e11090502c405000e000003055403400076141c04d0748003002501c00401200c0ca0982d0f9000400d11040702c000c086618042c545500300509140d4244151b5068905c8010700660360510047d41520301030141e429040169005480c0c0c21500c464800d000304a4008101c031603150b0b511989038103103500040c0b0741d143d0000000d0204604206450944080d503541c109410080094680c0c1c40601c88600b540706c102c58881d6640001c08504580705010504401e0fa48651440b0b0960060140d400004040c0d2800f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 200492212 1250 200490962 200490991
    0x20a0201051b0301050d06060906060908060703140a1a0d05060f1803030a27060b04110403050c0121060305010c090503150f060307030b131a01080d03020318061e 71
    0xb8442c484a0499064810454403002c1c0025142000c800410603600035a02c101e152030408039502e0381000641c0e00312801300303085480a42d140003085081d600103414821151030b03200301042e006200c0380c00c8003040d41601004001c5000d0140001031840a000c0c40984082c4c10034420300c4000b5000e042c40691045200482c0500ca5445c0c9000c1c680d20310004104100c15135496101d181903000384411020000951480c07218101e019050120061103000e070098810b41c0350040721840c219104040d201243d41140c060019404100015070703007030200184046030714011062100c01c0f58840d11070030018600402c00041c00004085015115041a42081d842075004886d000c3c8a041c074400001c0d8800c01d2243d54030001d4403a480800d143c20b10541005042c2c0c1c0d0903d04001c9010f48940280d00c01134024050b89559500050583d25082002c1c0140841500203d40d4000018000d800443d005001803000c0d00c10710705030718040f030706201c81510507403003440c1000c08112409000c08285500b00c6201c1c1e00505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 200493462 1250 200492212 200492251
    0x10b0403050606100e06030a1517030d020702030a021f120e0d18080307050f0c1c061503080415020606032d030c0706080103060c05040614031302040e01020a020105 72
    0x40c0c0c2c40b20024001c51041e0054805070071094890305c540035041c0700107400c280d1039043c0340340c911300075001c0340d9044002200f031010300007484d00450b8200e0041c0d42c6140c0185140070300d50500300c0007035445513138241d805101d1800c3c031400680f20032084d00c02c4091354484055a042e84541c005054004840c40300c0c1b40541000e0003441141000b003540e0b10513940da401c05100d10210a0301102500d1020b9002d41028000421505e0030300c04003049204001d420041542c070b803049408100008401c0c1211110340300c020103440500001d51641c40b01c540807000c1140000c189a503a41e0701101d81d0302c20b8200b52030082c0011400aa8141c04200c0c00f80c0203407049000d0401c140b451104a40b0a5050350706040360380d107008000312904141802103c1c00304511400365082d141d00d55174041c020305820f11040354040d1070012083c00d4280b00d00700351004e0722950341d510100161008a00b80c007035040a40fa4a40943c1e0345041c180042c1d66600c9a03080c080c1c1000700160701c60116850180c01c50f0760041c074041c3c101c1c0b1360b08000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 200494712 1250 200493462 200493473
    0x20306090c070c031704050a080303090303160306090204140102011d030d0902060d020403050703051006060509010c05030c010504200405010b0a14070507030b190e120c0309040203010f0e010b0403 86
    0x110307031141d2110610380c0c840400d801d025000304000d51018221405078401d04401388911001007090b54010780d04000c00350750303605080d42e481c030007120101e000350801e0010900d141c0c607002c0c904480302118070700481c0e01603d4a00300c80032640141c0c4000302d41c50f1040610a41540c0a00881001c800c502e00500306520401003810303103a00c01c2030140005956a1f044d1441156100d006952003801c40c3c1d581192070f65141d140040e40c54640380800c0d6514480c8079011113500320070b400381030140e86d039965171a41012240d10044d1031402c2c050b5400c0360603001c00d0000c451000001d10071a4400d40c010b04000850210200244401c0b000c99800c06000b10700700401030041e00480c1c0100c4404804600c2d00c200001c2414080c4d640c2d43c06100342c014284d0080101c000309100354030b0403250182100100e405546448041c8040844000000c62113082e0484e0700d9240411282d0000f0f0700c90074020307a081c6da141c1001200001d007264003d8010034112100c4400500421200ca4000c40c050848200520314050558495 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 200495962 1250 200494712 200494729
    0x1b10020301360b0d060f02041703160b071407060f050a0c091211090a0c0806010e100809030d021303050706030603030203180303040b160b091b04050a110a0c0b060103020306 76
    0x1081e4050f0f031038183c5000d003910380d07402c480c28480c0c200e0000c102c0c0c03801c0304600402a40c0b05200341c098a144080c0c2c2e07517031300c0400441102c0390850080404600003a00c0c0e99140d0401e01d005103500c1c244400000b05030103512a0100411185200351400034000c1d801504200841b1005805403c0d4640791a0180f01070035041003001c010741d031070541590700401d5680340560690034414246900704204134140040124160000c242500c1c03151a08403043e520440110362100825a4441e8000c0c00c0d1140e00081d60b002e49500c0d034010a81c0d9099030f00d011000c040c420260b910001c5003158013551820100103010050010f040070300070925060140c54959100250751b401102c40a803050008140350b085103a504000b100c0050290311a481d8445c078400d4034144500040c01030541d10b044c0a0360009945078000b2984515403a210405c1e040420302c1d10007848010100244000e4150741d0b24401080e0340ca291001420080099030740c0d20698500b42d00d400702c000780001c1c1150341070500600500070f180c3d840458 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 200497212 1250 200495962 200496059
    0x40303030e120a0c0605010914040605040201020a0b1303020c030105010e06060a030f060902520219170c130207031b0803270d051b10020301 62
    0xc01140e81c440c8001c1c540e003014101c0511810141d0002031000c40f05410200c400d07100d80c0103d008104681e0b8407080ca1054450000f1010500340503440000c001418561000e50801c0c01841181c1c0301d1801d59880ca000d2003810380f036a0140c2d00400d100281016810002510980c200350700910807549811000c000200380a405980304920102d00304224501c00d51005041d0360391503005100855960000200039844a00103210391101c000c038407025074206c084000041440191084211544c0e022403500740603030030342c00345200030440c2038a6004d40d4466107940203003404009415292860601c4485410f8540c01c5c11400a401c0b80304006000e503101c58810100c0080c0590141e61003045150031501d500e8589014014040d000c04501c0c1403100100c007035442680c5845809000c1005070303840920b1103900d12050403150b40104207880080f4802c2d80075046c6c006a9001c2119030000c4098240d0401ca04440018400380e80800108044202c0b0803012586410301d0606040c2c2074003840e8001003c1d04140b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 200498462 1250 200497212 200497217
    0x10110306010f1106191a2b020a0b0307020d020a03080609070306031e1401060b0d020d150905041e021c050304050a06050d0b0303040501170907120503130602070605040303 75
    0x402c104810b00840d40504800891015590381d89002c0b21458000f2181c0c1284c000c146180890b00c4800122010104000c504010030b00c01c0d41e40b246541d01002d581c3c2c01000c3d2801c8410203c1d81d00700589484c004070300a8028030454075101d203030600009107002d40c3c169904c0e04545c0704200950104ea0090b40c03940d003110b01640d51984640d5020800d40203000e1641c0001c00002c6100005d01c0c0140c1d100459a04241c4190042001c0b251540101c40c00da51850003010501081048051481a0598020800b4002c814404602c00c0b5110800c901c00c51541d61120100c10f490f4800c1004100c1c040c842d0084540703144482150781207654020036170621411885004a581840030fa4083c041c007001907074002e00009202442d01a02c0d442e0003445d41c0c10111100c41c403d400e010810f82e0f103103030100035101a41c106039640307180802090f10034660324101030800360284c028008c0c003060720f83d101a00f80f500940248001c6648002c17a41640a80f080e19500100841d0400303803082c000036501204030b404598052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 200499712 1250 200498462 200498477
    0x804030308040611040e152202091206091b0303120414010b120a05060f070c020d0c050d030e030d08010608310605010f0b04050f01030e03120108010e1011030601 71
    0xc0ca4508000c0c51680000c004c034a5020400103154002001c04901c100c0b42c102003003a0444070402401a0307103040081d00d400b4012806048580c50480750b000d808050402442c031212488548c4c0014142501070f00c500c03620707401884848106501081d8001c0d003848041d4019864034a140c001340008060140c8000c003c2500142410304899007508220032900000b400b881140ea00f05904640d81c91084d8011246030145000141e0305035900205681f0581d09500e0b00b6242c07030401d40c2000191100c2583c100d8a15084090124407174994264a0380c40f00c0c40ba40343e50302d10200800400d890f107040140344000704080b100040c01110f07849a08170390001c1d00e05071000389040d0707100008070303170319803040c07a0320310400791100e003d10a001407500721700d0488005030400c0d42840c0d204e80c01086a4402da01a02e60401e09104035075103a54865480490a42c601c07405a80c10b0601d0300115228060081e40100c64981d11b41074241600c260a0000704511080340d1410003100b0060030681400e0b020044c840307414000d12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 200500962 1250 200499712 200499721
    0x1e080f0c0a0203090f061e0a1202030f040210020f070906060e12070509060d06020d0207060501061103191209030207172a150c01090c120302060f060a05032b09030804030308 76
    0x10802901d0400788001c08000c02010001030101f105e0704094005400078080002c02561014203108603030080c55200c0c00442540e41d44c0d002e0240582a2010030001c600c100d902d02d01c20504280007881c00380200f0600420442d2416000800c40c584004186101e410094958445203e001410804a900a9408e6003460341c408002480e0504041c0016143c3d500010701c102e0480c603540c3c000c154852091604004590320307400120b641a0000761001c1d02d503441001351004600001140070b036980f000e454500052042c0065030360684140300011405070340508402c3c8951192881c125032010010b00c010100d60046d9003042d803040001048071182844100c445902c59102c2c0544240505000b45040c0d81d1401d802130030b2030003050004816600c142200c0d40210707690400d2143c2e100d1035900340d4024030840e22403211100707604201809141e03020081050016507520140103011080c842d00281000032880312122117086501210800100b00014105100203a810008ea43c03e0365094600070400350740c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 200502212 1250 200500962 200500969
    0x60103020d0c08190501080303040f0f12180605090f011103070b07120e071505090406051002010c0207051c080d09020406090203070f021501151e080f0c0a0203090f 72
    0x9035100d240c0c007050410b5003502c41541c00c050094000c00c1c85029800505040084040442d802805807088035001007000ca0040740c8820468400280650b09141d40f03a4480c2d60364504444030409840080760214500e8a000c1c81c0c0e1504900080840c0c0c00d0541ca010500c01c0040d44101400c1d00190502266074014124000104250b0704807691001c128406070901d040b02401c11084074210040c11402c116100340c07c0f01000c80c400086500b040c9841004041c49001501d0320340040c103603581c0290b0387d910002041d9403078403440b650841494000081898003820003e0600d052a00003078011006c0d943d02c010b040e105801000c40c1550442000ea45807001e1050703131805011007100196000342801c0700400e240c1d100760b0065005407070300e8960050002510805a0302c4103075241922002100240040204415000980b4440151490420014254001100c070019010240240010303105c804101d0f1800c500110243c00241e0700111038101030251800940d2446100c00032406115203010b58256501c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 200503462 1250 200502212 200502217
    0x308060f01021c17010608091209010c0303020d02090904030503060a0509011401050f0d0c020106210309170c0409210810350604020906010c150b0f060c0606010216061706010302 78
    0x4090350201307091944c1d0703100010310451042d15141500e00404503d60844503c440403990452410703101c1c07060541d00f90700c1c140e000750000c401d032a036229001c009044d1565201c00f4000e109a01c40e0b1100e6440742012030034081e820300c490708102d0080341c1a100501008058031002071802c2001d00e080c5941c2c00c413000701c281c002d004401e8440322150608d80380c0d603041134064105c0c00544044500c51020b40d1840840d07009519400304018000c10140d20041c4007138219040940291400901154032520028012030200e4201c206c0a880402615407400214141940100130f40382d110301d00b0040e0342c282000003002000c1280310b151100c400e400d030710700d0354a10506400c00d10346103d010307142d500080103e0595100d0508480c00c0344100900d600007036081d80652203052015401c02c08400d6560040c0342481c7c0200901400540e00c1040c1008426075682d803500107141210311900589650f051100019241c0601207002885e9114032000c180a49030340200b2000126407040100303034041c0c45410040c0c0080c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 200504712 1250 200503462 200503487
    0x141f090f03111005030105130c030e1014070203070201081501020c06040803031009050c0715020f0c16080a0b04030804021302030a0209130c08041713030c030308060f01021c 76
    0xd000c52100001030014490007042c0078441910100340407003910314100c52501c400d005499010b48515404020316038254080101d41000341400100d00340e2142c421842c00300c01c2c00710504c0d4240c87d44100001401002c0f1019000f0311540010b505141c3c056002078900000280380c503940500764254100d0b668400c01651210400c050989a42c0350b0325484c50548992040317483c180b290880043c000344c010b5540c0700386442042070700d1070a0300307043c52a0340e0060104940a81240300300d03000e000003014002c03104021314621044030000c02505003000011207007409907612550042d001400d03018046154120100d0380103501d031802d129a5038540c400109500c0608100e45485031004c0708000402d41e0035402441d000e84110342c507414002205080400b80d0300c10304050070005840780080f600061010680d00d503860f4841c2010341c00c0203003400c00c0f2160701e842c6910503901c4042c00e2008005040d0854400c2d43c000c002500d642202281040003c1e6498080c3c49142d0304008000f00c84081c8948149681341f401d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 200505962 1250 200504712 200504729
    0x30e030f06040201051305060711040e07030302030d0e01060806150117040201080a0b041803081e0603071a190216140307060e0f03031204050610060207090207020117040f0606141f09 80
    0x80b27101030b04010001240c0000014021868400030110340200021550101c0e0b0b45030707008500d010781094000c80981a580070380300c907541d03c4420106429070f00344240f070300c01c95000004228410413500014116981c0004107501e0344040002c2c4000750341d10050743d55101034180f501140010300c11021800600f4040c0c82400c170f15260b010b030ba104041e800120103015401112580421450b107044450310106c054900581c541e002103810885089410940c42808440d41001810401040410000d100c2c0300c0340402c0068100d4103c94607083c141d03200c24006068a010742000c585041004203945203100e0181300f0034080103c080c80c00a95800d07400111b040b4015066a4503840e1002c511480c02d50151011282030244000083d460007001041404640c035075030007400141d1911060200075800f080b81a0f042040009035407218505c85482c03940143c1c45050001002403040c18008111112504241250551084684141e41c1e421081c074100903400322031080b100c4110742c415610f60703246a101541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 200507212 1250 200505962 200505967
    0x60c0509062106040221041407150201060603020c0a03030e2107060612032a0803040308070305010b040b0f09062b0507020a17070c170307030e030f0604020105130506 73
    0x1a2400b070400d00003521400200e2031461030710341c042080164015001c000791020040d01490031000007822140b80c0007030103003190f000000709182e252400c0103281c0c0c0101e80801083c00344900010b5091181e100104000d01d011400d01d070031b102100d5121641c070303080a8100742e120a0901c411180622650407148001414000075441c182140380360780e00540fa00340c030700d02d03e400000034070013002c09920707045240d06640310001d084844426202d4186d0601040c0d4141c1840d02000000820401c02036000780d004e6207031240c881c5001800141501d01c140c10103441c41c1d0b0144000c1002040490540e1585000f001d401c984030050000412042c1c015100e0010319034030f0301c01801c403441d0744010000006c0d4014440030b100c2035031a10070070390b40d07940b0511006007140c0c030f64038a526042403654090108188150705d03810304190f031420a108004544102d9071025000001c85604160b0840303c0350032002005d40180010004402025846150041021341400000109011039801e0042203070090a0018107294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 200508462 1250 200507212 200507227
    0x3050f060405180601060906021b010912030e060f04050f030a031d0111010207061b080f04020f04020c0d0906021005010b0405240309160518061507020306132d060c050906 75
    0x2c2480740188078900243c05443cae9800484003240d4a083e49101c0180c44100d030952504101c1b0642119417a0180d08210341e129094420b40d9a01c401092200c510f810a10707201e5041c8410001a0000c0030603140c46984201143c60000380c00c424911382100d0520b54002065000303c005035032545929030a040b00b5440020b100d0700f01300b015400b00540d0b1403e18840d003001518040299a000b105480059400d46003900140051070240450a000d40000c0e0000d41080e0312030040034545001e601011012424800050080741d038104503000204001010a0040c0c0d45480061312031440740d0300a090040020844065914480314100001d1501c4195031580e0392a00780b281d2034942d416a0620703044000301d50030000710303031518185c070b5420050202a0300c4282d071181010088202c0207281078040f200303030a00841c009690140500303441104240b0f0070440885040c1b40c403070b501c000403039202c003c05002884550b1070f048a0704207402d0a00e5000c040000e500b841c0c80d1003510140540c50015034040320000c3d200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 200509712 1250 200508462 200508467
    0x7030507030b01080606090702070b030615030a0e0c030c090103020f030312040503090307090e100504170c0a05012a0e0409080a12060b092805040c05130603050f06040518060106 78
    0x541200c841d0005d80b0300c2501c480741000503000d01031341c890f00180e01c10101400104101c0e40107582100c0c0c01803400d16080c3d02c42d07004c2203881c0c100311340f03102c0d60558504460741c4a140910860402030411005807000c0d091400001c0c40c8800306010103800341074400746910082d12f0400845070480c3c0360700e860185500d05442d00700e949500c100d868500034010400000307140c0000c0d02420b44806903c0000c5c00c01c50024401e1100205001001681c08060f48400245503404000040206180d00300140002c0740003400c01c1d40c2550740d600300000d030706910004841d60581507070041010340005813408951002c0c0c80c0c0f0010380600641d04000c1c06100000910b85450368000d07400a140080e03480040c44925601c070300b4030406002d60b06a003a040b03000070b45c088196491810408028000b00030300b8a040645400c042000c81c0d80e600c04a202080001480b044044550000040205400d103428003252070003c901143c1c144001e07120300d008903211800f0034a0340f068026821020145041125060360390380500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 200510962 1250 200509712 200509733
    0x60b030105090f0f0705010c03030b22090209180d26010e0717010305030a031509050108030a09080601030f030305071b0c0501090f0b0a0c02060c030a030209040e0d02120307020703050703 82
    0x144842e10413440410100f8001103074000c21100d0503120170600300855103040d0b002c1e01d81d0441c620b50000030042080c52256007500b101916031001030f4005207010003132040c4040084040c080b400450501a42c95100d0300002a041203010035a140c0b0344000801490141d400740b800c640442c00c451081c81c00840c40246080344184190000da0350012500f008a49900c808074081c040501150400c121041d0040e00075007042c1011300280510b50705203a55159610200ca000b81c0100a246e0000100c1c0c0d105a030f8412589000313030101c0700203401a1b514598a100b45e40c400742d070b002020315841e14002100140541d16203840090b00f41c01c0001e04640602d0300d81115051030040030b0126540800200b541d0b940c0800d540280d0318100c01e2070346405d14181c030544030031700c0d003420491713019000300700b06410356600303001070040314103140c40250716134500c402084150b880d40d54a0300003585c003030441c000103d81d00191241d00c290b40031036000d59a0321030f54000c030f0521549800107015485404400000c21241401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 200512212 1250 200510962 200510983
    0x3050a030e0d02090402040c0e0a0b040639080f1206010f02030a080f1008100902100f050306040b040204090c080405070602070e010e0c0d1109010e090c070807060b03010509 76
    0x220350300108841d000700012a212035002940010701d0800090050070507522144002c1e156040035590f1650040003c3c0307040010350000b041c2440702142c2005155007100260f00c2c60314040901509007480c0c04550f840c800c2c005000340800b641c00100b080d003800045c4040f5410300f00f0545815039641809841e40703407150001d0725018002002d042120119902c080284d0301000390b680d40d024545d860300d0b6440d0401c0500501600c2e520710800a0001d031801e0b041020000800c4003d801050000d01401089101030b101452101402080d000420103203a000d4103ca82c03000041b01d00040348c16030600400c0013801030345c105e09d0300c0070304e410000c60425801050761032151f0b2003041200c84980e00c0b88003c07070311886240b00700314000d00100014090712108080095204030540d5603d400e11011366034a0040d525840110740e610300b400907801684d9640f20483c100040c005481240c1c0301c1c200011805c0300d51103800000340400320041080c00400c90280c0140c0c03030300d41d0000c000b0f0059013090080942c87e14030501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 200513462 1250 200512212 200512217
    0xa022104170315010503061305040b041b0e0c13030213240b0a0f120507090303110607080c09040f02040f0810060e0a0b011b0c0801140105060a260103050a03 69
    0x7100006019240c084901c2014442d4080501d10b95040040da0386410290140b0b91022881c881d01e04203a803a03129aa208601444545495003001d080c4803002d25440850760340381058480c410721a00c10201c2110b9044000c50084603035422081c0180b0500d4909c54100a5101ca240c841c0030201c0e03049608026440c1280c10b8512a459001ca0303006242c0c90114402c414010070203000d203442e413500407041010724a103a0b04101d0101846e841210301158412a1040c000c9150700e1000d000381079001c00990304411450340100224100b02d080a40080c034000c10b96200786030b00003041d051545454000c0180d08015020a54941f6100d288040ca0040c0b02e00891142c1e00c2200e140c8900100b103401000229060001c0103001038461030b440002501084028505010300400038003502c0071441e02400c0d542d802803112000c010b0501580e142540c0e80c100d0320206856104005001e6665024100c1d0b00d05074040c20f1144c1b400000700003500e580c000072500100c600c14414000000c0c40300200b24000c105103e903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 200514712 1250 200513462 200513483
    0x30c0105040c050f0301020405030601030b040c0806070c110405091203070309080c0123240a0b03040f020319030905061308060106180e01061d0f042903070302060a05030a022104 78
    0x904c203150807030050b84100345d07050303015030010800b0880c40e010300e079000f6028460000a040d240c400807450180181d0b444000984031585000070b2004007001300542440c00c480c1800541443c12400d540ca41c07040015800c03203440000440c40c4a4080e0340308014031035108078201c1e180c1d41e40e08100c40c0204044420001070f15140300143e0403441c54110600d1088109806015000755100c0c800b802045903245013039080460800c0201d85a1503c078042c40c4102c0c420101c1d5691145a48149810002480c100c0b103580c0c11184070b0303840001e402952a1003583c8083d00c00c10745544442c003032410066038590060341e0030701400c0004a1080d9008040e154182c0848524240b242e40d900c40d841c0301f10b1424850035000a0140750400c3c1541200c1d9002004400c000b8907034060b5401c500d00082c21140f2a07691041501c42040e000f20601282c008600c2c2c9600c0c0c2100540307202032a680100350940b00e41040c410400070004001041c0c26001e50682d241403100309815265100d000b216401c400c0002d0b02e05403158410b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 200515962 1250 200514712 200514739
    0x6020f100203040503030c07020d060e0a031403010605070803040219240e010909090f06050c0903010e03040303080c071410050403180303090b070809120102120109090506060d020102030c0105040c05 87
    0x503000302ca009562040083d80380d6580e010350046203410441c1d003280c0c891907241d080408a4064020034403015a140d0140104603201c9c42c0140c1004003401140345450414001000312030341040c1541d11160b009071650b80c0c0da40e07561000072600458480c0b80c0001d84140b8601080d03c8800082012400e03501a00103000b42507401c03803d641e21b040225090f400114070030024003884c4e2194120078911441740030b000180ea11107550b50410f4030342c102e1713140b14038a0000c142c008803031409006262015183d10003843c901803c0d614005d10482000345100400c0100150341c0e0104010311103106050103000d0306036410b22040d0500e08010780f5040d1003d81c001003261101404202e0009819022a40d05844040e03401346400b04071b01c62034104040540d9503c5044c000307211036896030b2601101401024000680d00c0101803a44603001c041038116941c103501d0550a88c00180c4006005500400c00b01d403034024043c0c3d6071004038079511500d00c580d0129404d1109210400c555481030700c055800450b0b000d400301c0360 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 200517212 1250 200515962 200515993
    0x110c06090a17181c150e120c12090a090507050a0e030c09040b09030d0204170d020a110420270114030a050c07050f03071502090d12031506020f 63
    0x40c2e10f40400c0c40c0b2510307000c1d964140c5002d580c031344540c00e451184411030880036100c0007007140e44541d0640c0500e80380c17482140b8410051003c01100322007002002c0c01c2c0903810034400e036160140d41c1d16a01c035940024541401d9076512000b90300900442205000c1da00c0c0c0100c1c01003454120362682030101d10000d008404c0c030b26010071003c2d00003101a0850085507140d03103520b46042d0b0040c1820910707000803c101581924079000a1004e000703402140f941d10b020f100304440c80e12005d4960718046400022003e00014a41c42000c010b505049901041e1011003c16803071006a00c0400b07001495000585a050421951030281502d180d0140810300d500511005480e600504c06030f90809800420002d00d0291f1b40c1c0d4442030308101204501400c00380c6540d82e051501c10219503d01c101d0b030010a001081014490301041c0c9071610f0002942400c5088000c103d6014211200800081c02e40210402951199104c0740e8581588103034000c80c1c1c0e5803000d01030340b10300b10b800141c61540200c0070f26460030136 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 200518462 1250 200517212 200517217
    0x60c110604080a03030c030605030f07030b0702151303030213140907020102031b0c07151808011a09131509051c050901180801060b0d0516020709110c06090a17 70
    0x100b000000c0d21101449a408500030071032440003c1c2450b5a421001c11203850030810130201800c10001000349a045040c000d0079500000d210720215803007c00101048411441138641141c8103001640c2124030a207801c0d0003a00070080c6d1201007a034000c1c03000852400009520a00d0441990031a10a488450040b4240c3c401100d201c0121140c9c0c941c070105019007100205203c90100081d02c04994850072240801b5000c56002d000084130120b6400c00d21031040184401482040000c10948401e1b00400c05680c1403001c0b21481003d070140007070907410480081354141603100c1031050360200c84450b0140142282d510940d05440b6420514452200c905c18003841c03490a070312010b00300314900004480c504295015488a104042c0b400110f00c0b80900454014008800419450f2510346071100c088820050800404400138106021880c2e0049111416038103020408601590300317000010036849518000203003886500100964403002150f450742442c82600900c0d03000400f02c50810315070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 200519712 1250 200518462 200518469
    0x50a140d020316090f1a120103061b0903020108010e041406070f030b0a0b04150903080705010203010512030702280f03150b060403240e010203040501140603121b030903030301060c110604 82
    0x81c001c40000b8440d42500034104840c840c800482c147c40d02d40e8840030301106071000e900484003192a405100c101283ca1000c80840c04105c2c43d05102c401d02c1c1d900003d00340d00040c4a0066200e18402c085400e05c00815103492010340210212245c40c00e040100818440d004503801000903e061160310312458084060800c03143c20f190b485081c07604000342100c84441c41c5451209002c1845400000586600007808902d40940c000584075031410301401408180507040424542040109100590f1854a188203020020035401e24008040109040080094024019940708520000100300060840e003829110000052060b50340c4a000c3c08082d02490000030a8111070b48191041101201c200c19081031a15001007542c680c10207900b42241e01c00d50307059505035166000c4168107003850b40c0446d080202500200301e03906810121a195010700740140c1a0752807000402000801c3c01c01c04d81d034004d000141541da6235651070303101901c1303240d000004583c1d99000d029030310080c1c54050300ba1000c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 200520962 1250 200519712 200519729
    0x2070320010903140307120806030111090904060f06080f100b0d0f0b070903020d140c030f0307241b030605060708040302040c030e060106030c0e091303050a140d02031609 75
    0x2e20300b9992460001140c404000d40329100510445d400b181c101040b404619805890308100c41c104001814292418080c0c000700d410340403c106a19502c4945440c0d50040d000f000000340754058000420240602d40d2013480c0364440c0031b01c21406110042188504040c46083c10440c4030301450a1101c1c0ca010b0440290081c0b29201211300030070242035905901800924000b0032040d01c0b680001c1403e820000143c50b900940310103c42d090004206402c0b442408600800c420507403005070f15540d01c51208002c140248110440303010b00040355036000d08085660050140c0044840c192116254074440d160000381400d40001d02414400d086500071508040118a494119002c0c00b010b0300c0701003112030406640d0034021b41410000c0c40864003030803450780d0120765480701c03d8009140c00824021a482451180280070450304c01ca40c081000d1076145c2015605c40780e2800e8292a4194a900740f014480800544452070211950041d40b14080c4070b0718803c10314292030300488001880e8002c8504 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 200522212 1250 200520962 200520977
    0x6020307020112060e1009050708040804050f01031d010504200a03241a040b0604080d0806180702070e0c0a09060509121015051c03081e070207032001 66
    0x5944100d600f040c00101182010820075a228103511503420100d40c2005040240300003801440400d00075240c02c4815440c10484d1420031f41c90700c000910561084078443d050105130302c4026402a000f10b5141100401800141d9808010b214044c0101311030840f442800380b036504601124071030152b056000c0152800c00221300b03540d0750761408003000c100c003140c24940c03848000700b14207a402545000c1d95800004250f1090710300a010540b02c03001e0034988241c4043c023080c050319900140d1400415001d01e440800d9803655070204111040c03142035440c000100d01c003080051900011070700202c5080c40d00560076a581c1020010190041a8403400000d40d0b0000401c801c91003500074150320107004000c01d40144040003c10f02c1c1c007001c0590003400e551101c042c034000e503001f41d03684001048152081c04e802d0b8201d000e108140e680145000b02400380d0500402c00940801071200d40b2444500c1110015051001029545025511088900d600e080d0350342c4c0c291441041544d000e03024180c6030040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 200523462 1250 200522212 200522227
    0x30906140105120f1b18090f0d03020f07020f010e06071a070309050a0b09070b0c1609141303030908030403030f0b030c010f112401060207080c180a1103090c1306060203 74
    0x12aa20303803100170543d000e03440c0d601c00240000907840d040e024801700d10003003510981d280b0701075041480b02d1551905241c8140700040015032044101c0340b00942c1110103103042c140400060f10304540100500e0703081040807904d0320400c0b0031000701300213508a03088200707400d41e00e010040b026506a601d0040c01c0b5004a070f0b501c000641121040340e007001c510b0b400d4400030341c1c07200a001416002044400c89c1d50740030500d04070184107810f5040020b800700390020310001506035560000b114014003c8165040c8010f6604203251081d8020410140c0c007822069880c10503040050282c4000d02c02030040b94030380744404d0031900c0c1c0081d10039100c10040c6c40b0380000742c8254038141c50b60003c0d41880b00240c09032000c401d214408100d1080c40b0b108011000b5280d6504002000f45006000d401150036030b48107000d0b000095840307a0340c02c000d4042d4904034154956880800501819500e03051072a82030002c418080d52420100e02c003825190251440c20100c0d400d1502c000a950b160b00c68400503800801c60340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 200524712 1250 200523462 200523493
    0x3080114010c060b1f02070e0609060109061409060403150f0b10030b0d050703030c03091e2303060c0307030e01021905090a12050c12010b0a15030906140105120f 71
    0x9031300f019401480702c0001036003d1188015003a1544031800180c000d0030301448501c544880540e080341013901d241c0c4291404500290204026005070b406000d04480c0b000180d651510032504920405004691115038a180070308401508482c142c1c181400c0825858504100e445032040344007009002c449020300c0c081e800d80c01425424000c6400ca09840000c902082c0d08002c2c82c402036103e903032018140c0b191810024001c52480c4c001c60030034500b80e000100b08211030400d80060b0741207102405c28142060030084445080174041a030540101c03020404c1c1300101e10b025610a81550710300348101100c061310f0900301d05c6120b6141c070340c031035100b104503107514421001741010400145c03040710305a441b0f00003e032518040d02c40494040e8807a03134100c0380b64100007124810900f080c038000c0c44041158000613020300c1e001d005500000881080b00008280f01b50841c900154011000b000708500842081c481c441c02401647d005072401c00c9890403008001454000c008692001b4012000003801c0d01c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 200525962 1250 200524712 200524721
    0x60206090a1106070212060109050c130918050f101503021c020109050909010509010b06090d140735030301051c1a0f160807090315020d05040f03080114010c06 70
    0x2030a0300202d0074051100140c0710529108444803449006011f1517140504000075110018400e0b01200313402e0020406a0a603130b28401c0540349030910110b8401c51398403444146406924000d01184202000300d110904041410300d09401007850900c040d0042e00c580d4051030240d84802174100032141540550304401c101424040c51052404040d2556110f002442400007503400e00c0c2e40f65918000d102250109100303400c0d1070701081d15028105070215000541140c032542010344804010f038003070488040c040c00860060400c001001661703949050b440e90b080707244d034042c00c991105480c580c8000d4483c0002030300d0403030341c006080c03400300b0080c0000341c001a2103c0310112440c142c5008000c0e43c402e61107240c940f18401206502c09185007944890031022a24100300d401e0000704024031000300d5100d02c6010540e170300442038a0510090b103100c0d6000344102000c00f4000b9290400f840304221000e1000340d0301e24041e0391015900c0e42c031002c000325034040e444a4903000c43c00c86824003000540c180c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 200527212 1250 200525962 200525993
    0x40b030603120f040f0608150603060d0605100302090c0301080303061c06020706141003080f1b07030812071b020f0d050105070e1c08030f04050a0f1a01060206090a 72
    0x1629000c10a030022410550080381c20780f900000c0c0418103001180540e1407032401450145811005401c00c10710b480f480302c41c03040c030860096100200180c029214600e5030305019502c40c0c010002e6240c400a104034500d0136000032485558a000401c3c5280f80e5803043c1c82c10303202d0900241d032440d1503440412498410000f4000c5200b6500c00601020505601c007520b807403070062201007034044490100b00e240c2070300140040f442050390302041c008500310000b0717105a0842c040354036603205c03171054035040f07401c1003030100390a03521800e180801000150350182000d10084640411103841e80041a40d6001d10a62901c58400005c10008054903080e0201c08801c18040c21440ca01c01070740d282c103800d40d10121070000108a1814224096040c14003580604904c40d401c0c110070822039680b000124880030b80300710302c1d007420000880c040c00700a02038019240c1d0301001166a4070807500e80700e00d4291014003001c030404903007000002e9103800070402d240704202c544054441c0046543d2000340d42d130440c84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 200528462 1250 200527212 200527219
    0xf05040b1f020f0322170d030b1203070c030515010806070e13020a0806011e0813061104060206100e0403050a030c021e0106030618080d0b060702090c0901080702030906040b0306 78
    0x5850f1503c04400344000c20000c20304000415080700d00c002092910030031a80080c140328140600808082d1000c04c9a80c0100000e20f40032a0400759940000c8400c445258001141d020014000f0104104040a841124483c006030f400305403010304804252282407090f5411381c0c0160000913142ea01c1511194901540100461201d00014100b002240c116001c20340c08580142e050210710768100d4109030120f01c98149070b040b1240c143e40c0041c51001e007d40540c102109500e04041002036580040d2030410030860f801707450f60f90f2800020340d90f080a82c0c03560a070100000340440c21810700b00c1e90b18411601900c6142c50310602c1c80045004117107411501007103024165800b094a40c580e00c01e01868501600040313000ca040d802c050040720154a031121201d00090311040000d0320740c030150b60700d40b040b01a0015038010b802003c070740d181c03150070002548507842c21304004840c10350170007034110608207030faa40c0f5191b50340c1081603a6a01c00c1020b100d501140520082102c003040100850780418040e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 200529712 1250 200528462 200528473
    0x4150210020423040c0e010311120906040c1a1b01060306051f140307051002010f050406051909050309100912140f0c0a0e040227010f05040b1f02 64
    0x2603040034200d81090300262020104a003d0440744000410041d24800e422582080040c45005d40a025088516100d030706050700c81c041d0600320030800d01a50001d582c840c09c104042d00d003411800392510000c031802c40c0c1d580d00c0349001142c4003d205089911217520b074000d142c0b41044ea0001d4500c190300c403000740b036215034855402200140260164a01420006002508418015518594008440c1c0069400c3c00c0c400d021440c05075000034140045610546420410348880c000c128007514841060340915070518050004004103540118418010801814804503503110501d040c2c1d242c0600107005584284103801c2c040c03602e90040324030381a142c14414070315a500c6d014892808001c0d48141c4640c3c07881d04d5940003890042c4a00d868410464028000c2c006105000605850403405a984a480c604d8000740031501c80320751080c21000c280600f407601210b642480c2454081c00d0040700c240d141c51a4001444c3d003041d000c0c2141001c1c0081c80800f201c0d5111031450100d5220880c00e40852148 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 200530962 1250 200529712 200529733
    0x21204031a041e03120f0e07050f06071208041103060405070302040f1d010504111903080304030e130b01230909060420090102070e0103032309040e010902030c01050708041502 77
    0x102942c00d0f030080d110741c41d40005000000c80060483d0050a07244c0841800c168051480d81404a407660036101e048400407880511600415014050148024801c41d966141e8801c0c01e83c21803240c0d440f8902c21190030f12035081c4242815103481e0281c60041c03c9511643c018001460680c204481c00c0c501d1a00018804110381c0400da079550b020445071840741d40d5402400207111503111002c9122505071401c80008500c201803100c40440d921028144540c080089410103210304a04801d002000701402013081260074200000e10a40da043c03800f01d90311aa508409250025010300351540702182603040061000a1080d140b00041ca800d03407140da10280f12000d03800110011002520003445207888840c11030001e85412003540118001e40780440040001903801200703401e80c14036403481c40340c240c2c4c25040740595074014440c134203500505004910400c4441584040301c1580220210b42d4007814810041d6518031400d2009006060304001c02d01c503141c64810301450000c190700c11100b182c040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 200532212 1250 200530962 200531003
    0x3070311161109090105060d14030d061401020d030e0703150b0a0f0305010c05070b04060b03010e03030115030b06070c0b03070207120b07030b030d1d01050705070b0406021204031a04 80
    0x3805108a82c000b403111200398060425001c03056006032840b0080150f4140f02c030000b0040144007800038802d06050303410000c0c08405001391a13101d903003c401801030030780f582c2504034000c140540003801481440042c5480364800e0103080740038020f0300c010b44071040c1103441c2c081c622100407400c40003041c3c40d20901403441d1107880c0b80c0c038010044a1074414103071f41546040f600307699040c056034003044000d1003140701140301d075603040303821582c861030000d04a040d080129000d0314200700503020a00000c000040c4c9102d5032046044100c245a8080184c04850707020400540210034000d401c101040c1c50511400d480c450045402010701d0044406403941d880c4803401261207100201c4451400000744010170f50503016280020000310003401485040c6e8500078422101021755070700030520380c01c0c1035030181d009a0490b0350250300102a030340155180c41c4030603a60340c071520811b00188908140c140303c01300d60704255010ba992265500c10b404e0340c141e1784441907074000381007550089a0440f41c1201d111 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 200533462 1250 200532212 200532247
    0xe030a050408120f0d1d0f0d02071a070227040c03110906010e04020a03140c0a140307050712030209030d0e041104080601090207050102090603040c03120f020303070311 74
    0x149503550950319810941014144440c200800780c9840060088141d10340030726007a1038102c0c41c8554009a141003082c81101d001001c07444079240c1c1e0041ca0185c181064011441103007141c3c0c035070201ca0340d5940c1c0717103403c24200d620701c682006500d000f44031000040c9411343d0503a280f18004240c0d44101010104550400360056404a4034107001e40010020450036000302c0d502010100d40d0448030385040e2001902c2801d21208084c070580e40000e1031141c0318082e91107500d8006141005401500c1c001541107465400307040e410300846c582c104441c0224401c40103c074400d00003076407442e05140043e42c030707215420320614444062580074000021252810041d1411131071050766040c80260800051200b20340c8071102c000d4195004002c00d110100c00054813a044079013090005948401c3c0c2c6c00d019009000b143c0a01d5031144001050000f4020300d0f01010003680c0c01103580b407503031404c40d140c15280d00c2040b041c90400742e04148009a0100d001e51300c038a62003024002d2042c40c000c4060184e00011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 200534712 1250 200533462 200533477
    0x19021608030405150f0a27090e01050a0624210203180601080c190302060f1201060305070c0b060a080d031d0304050d0b0a06030b181005070e0d060e03 66
    0x39400400c003000f541c03420004084151400b00b01a901d03122020141860910905115009021500d410302e1044441c0450b101064010031200104058030740c40400081c110344041c2005c15800c260104480c080c07a48100021a40c000001002105208c42144c080303035a0501ca4a00b0300100c130a50b0f58580500078071610030b00d6071494006980380b611410807004001c150084012581c015001403000b07600010f607107100d503441141e82c3e00301d0080d500c00070b095001107500000d41205010440390824081d0402074140210800e11044c201da8803048102d08840049520070002455014882c000c40d4040206070b42020340030300000c0c40a81c590038403510703085207800748600290340c525282c248a4040002ea294100400000d98601498080040c8000c01b8040b0301424040385840412140c227003540c0148004d50348102c00018614100250041c0b400b80b81120314035030b024400b0340c4c800c0c2945078441d8502c2180181c4807180c5800918080c4142c0168a0b0300031100b0a6984a01d00e09800c000c00242245 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 200535962 1250 200534712 200534729
    0xb030d11010f02030720060603100207060605100309120806090406110702041104060306050a08030d0209011e0f0e01180b0d1e06030212060403050f092d010908070803190216 76
    0x1060403103050554030b0f01206450b05034581282c400d008c01a90007155880d2401700680c009611250349042c584000e100b01d500443c1c1c4040505a08a50036030542c001c20b5041e0b00400400c5030215080c00300362403e600c221082030340024803500150024102c0c0c0d202903440c4952400c02c42c24600c00d81e01160855400d4680342401403008142040a560300d4012003024210944d40003045a180540e1280c0c0c9009903024904500d4010981103c3c0e644603040e1074010701104044994101100b010240200c1c14981c01c5500007800141e90000650140083c00c00e5404042e03280d0a20a151400380701d1250400d10504c09080c1c1c032601d0600c00d051125803140102c050a00000860038607501c1003007030f440c2c1710385541d00f0741c3c1e08603404200110340c11401341c51210340000c130f070142c2d9880c02c04000703080054074612100c40c071240a20a01401d0100700f54a121441c42a04c4482d5500c4c2c403540b820382e84501c240700340d04440e8000c0014204102c00b2541e009080c048600440701d00206c04101ca40011409410196a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 200537212 1250 200535962 200535977
    0xc0606010c1e0b06040c0f050304020d0201032d06050103020c1906020f210601022b02030d0e2508100b0d080a051c020301050108070c050709110a09090b030d11010f020307 75
    0x10140750038480c01c030301d04046c2c3c1001c040079048058003403c580001040640300e240e40c204031405590107a003000751046408005140c506148030f40e411000c114031a02c03030811529016011035039500034402c60f01c41d14036000007010b803e192040d5000d030000c1200c1d0101c032825001e00c5480d00c0c084020014161001d0f251402512504081c002c0b0700300d13048000c001c08d0440d817001a8080b16020801119a4101850b03154840c28915200c03042c0c0c5503101392807007100428503094092001c0080030503000c1080c005584003680360864056206042e020600401ca025040072051040040013584100000034014010000021240c1c0b81c40c03240b0f820244c503c202049000502024001c18512006090401d060301107040d07504000c0001c022800080505042c41050003118080c40303820840c0000030099010140031512210b0914402c035085a403071800030985103030011614000d14020103a4140d40039004000c49050b6103030850f1056400c90400115540c0d03203203515260301c2140000d600c1621300c1d44580c80e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 200538462 1250 200537212 200537221
    0x5010617030a0e0409170703020a0b13060b09062101060b0403030207030b010f030b04080d02070b090f0c030a050c090c3006040902030c060a031d060106090602030c0606010c1e0b 78
    0x903c0801c0c0c201d52180b1480ca403042a000040481c5170207480010000f209170340f00c0d00301c0c1c6016440c0590380c03000034008024210420441001036500391500c50b1140c0401d200514861091010902c1c041c2e541680c808025030101503800356402d291071030440c03958004100c941e83c4001025180c0d22541050b0010f0700b101c0303828014020303100c1d459401001400500207a083c596143c80d4020840900000c20300800010342514150840e010b4079051a007103500c14027107007000c01920f55070b4508611402a11300070149006114a408642500c0c91034000300509071100400c41044401000101001d08104c4240000c5501c40960364807140751300c10b54580c0c00402e001e826025494070000500c0c4c1407045003810407480068501140d0319000d10720070745e4102e468403400403050b0702070080e14074455510990894160006a40040d6440c100d5116480e154021500c50100f00e840c2d219200303411942e64030483c0458001d500c2158068200d03806250000c000c03d581d00342a4400c00d040200036500d458aa1080c00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 200539568 1106 200538462 200538467
    0x50904050f070f0b041208070816060b100215130c03030e1f0e2e09050f010f0221190e01021506030706030e010209030f1005090106030f020d05010617030a 68
    0x15403a01a00814039000c0d0120381d008bd1070250030f120450140d4141600020500c800d6503000d40f410294420403020000030240201708003120a54021011419818452000d03611981e40c1d240610a840e040104a004540c180d0141c44841001902c03850f4210303c0d180c40f604016130b0101408000300b41d10388900e0001d4130881115102050310005d485134044290016501c044910008510b0100d0045031642580ba4030040940d00241007041000440c1d0074611256010280c000d2916646419200640c40020032200120b2070a5850a0360381d0780500245040712280220905545001e0002a0f0b031150540714440070306560340703034a1074011001e40481b118401c001d0b0490b00e002c001e0f10b4106917a980b50f01c0b145040c052810001c606041418000c800031a50014142180c3e101d041e000c01259107400320f000c0340d640d0340c0c403180013800255403001c03083d15111210156896800307a2001 = true := by decide +kernel

theorem cover : BRFrame.Cov 200359712 200539568 := by
  have h0 := BRFrame.cov_init 200359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 200359712 ≤ n) (h2 : n < 200539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
