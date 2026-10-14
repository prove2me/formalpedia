-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0777
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:43:15.353922+00:00
-- url     : https://prove2.me/submissions/c84b8581-2d88-4acc-a93b-22fcdc23368c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 139568345 ≤ n < 139748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 139569595 1250 139568345 139568381
    0x70e090625021525031e180809041e0b030c01090315051009020a0504081203090616020118060e0d050c0c04050c040806040f0309091e091401 62
    0x910076880484801c00707181c01c0401240320100003407550005a80d0020060321908000c99110301c0b1526040c88064801080f8182404042032030031a05980a510006840d80140c10301c2028001c00004072401d60126168030751900c0c1002000c42c0310003000d00039000c4098000280d00e01d80c040c00441c002500300383d0341900c98840040c40c8550605004459081100382007092140c2e08603920040b09901e0240c1060303209a980000070000031034030301030500070108550115615403407a540148164804e00840840344680b10302c800e2802c0343d41e000c0b28421450f03c0c01405040d02d4421104100ca40c500d9000c0301190b40713882407420a01148166a00380c503215000016810585019a0341400c03524400c49040c01b1060100c07080602c1c1c00b0403d690044002c40c0d0008190b44d8024400e1210300071a0802c1c00103105100400003007141014070840300902940794080403e69035034580041ea2200301c1c4614881445090030b9540301100d40140c440307644030315440c54200140050326821030300043c17244d82080c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 139570845 1250 139569595 139569601
    0x120608071217071a010f150c02090a060f090e010608030c120c0312100905060d26071a010e0c090a050d031e02060105040c18030201050703120c030506100e150309070e0906 75
    0xa03842601e00b004000440007c000c40c0e00a4101501d003501814010380518031b6900041d60032510740d4000130260078031038006160039403589001001044201c000f10099885d003c0301080100001040da411007240c000104101e4024181d0240c064200c401d1110184c8028460400810000444144180b040d20001d6801502d440d20b294281e42d00070306100c0c0900f90070b810788004104540030440984001d8884101c0d4910b10f41440c0450f841554409030000003601d9034050b001065804035412104002180c0b8001e8135094840c0480d0300c100400c040e0301844260040203035080c441303040c071085402030505203484140e04003100c02142d40b80c50300a0050308410010710003882e05100381401e1400c94600018007076001e22a000307410800c0d01004e414800003042440030148142611078100603001c000f030000d00c4143e203028001d0081a590310748900c1c402483d06404038441d480e442ca032182c000348011000c10085040c07030000e90010b8000f11081c059050085820400720f60382a004501010080220345 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 139572095 1250 139570845 139570859
    0x1107030f060b04050714130e0405030703090503150a050604020c16060305070c021c020f0333070f0f03020f0a020601090b0d020603012d06120608071217071a01 70
    0x584140c1c00c043c03065142c00c003031102c403da2240c2c01d01064100c002030b69507104020162501d05e4022a400585890100790801040001c0880584a202e00c01e4481d01001d949420405499004405200e1110f6102d500098111401038100395084070015100500d40080300415a080c041c009a03040b80348816038100b00b14103070f454451254488654034141701e000c40c4650000301d000d04031a1240380c1d007040710362000055560700d40403800800801021070380c0c03000e04040141d07103c07040b40440004148900d611074484c01d80c0003203034a00ca1803140c1c0c1c2c3c14507184040041901c82c0780d0b40c00a9002010f80c00d0080c42c3d46459030000920036041507030010242c80d0314203203405007620500c120035801030740d45005204c0180c980c0425039040d1103011a440c030800345910b03481102813101824400e42d0081c03080000a04030f1304210a0450090610414010030345c41c0c3c05010356605c1c007031240f40f80c01100000c0840c049600c181c610910841d005186d00d14148880d04d42c603204d2060319140740000541032004100030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 139573345 1250 139572095 139572101
    0x7060c210c0206090c0a030809040204050402040f0317070b040b07090801060609050a0f050603010b18040612120c05070b28020d1713030e04090b15040c0216151107030f06 75
    0x1024070440101505d081450115040d2030142c0f200811281d00070502e6417481e5919010396018240281c011900c3da40c7d24100110400100e10054900054413142d040300010740c48202c582e0326411100e0b0600c5500c49540320f11101d24000c10050420840c2000030505060038055034000b0002c81d610b0000c0715003131004001840302580c0c0912a001c0d0600810413107500d41c41d082e0380c112042842900d443d461142108684000c81407c01940702d840d08101003005511001848603040c0102000c1c45006d4046070150341d2187e034000e0290030b46d40724440400071001c410005003199400721040003c100301280401c98407404090301e0700c0c0075030000b007403c40355144d00410510074000341c811015841d041440c0300e400750141c030300000303810460903100c541c117240c441c0e810001c07005901c4000c4d2500d5152a902d0803d550440f14003070341c403c03800c100003292001e100291096094000304900313050507240a201030100000001d00005104800340844220907050001500640c000c0415000300b003114580b440031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 139574595 1250 139573345 139573351
    0x180403020304051008190b01090f0603060306050604050f06060306010203070501050a0507020d0c260f030f04060b060a08010e0723030609010f0e06010f030608010924020307020307060c210c0206 85
    0x801002600f01b01840059410019a68280c604000341003181040125080c05598210520500f807900300007440c590715520600480340111003c12403a1124800c0205490b000e80798202c541904001013640752804400039904250140102e030724003d450ba84190035618215280d0820a030b60300c08000c10560140080da00c1c0300001e2a00e110680720310341d1902d28104c1c44841c03d81d0081121b1040801041d1094101e400000c080d10960307840f898465095410580112012240c1608041490085041100c10307511480703c3c58a4020450303003170500c915006030000380b07140104081061401c1d0f91604481056032400600c0403200c1e80c034035160003402040201a03002c0b42c51014290010050200e0609800e0781003002444c2c04909210b1071a0114083d20958101488551031f01c00c2c440d041200c03c840e102d401680c42c0001c20803040c0e00b0203060049020440d060b401503001004040700144080d403000000441600b03042440f10186003e45500100c0c0d8a1082a003039078a24030700006031380412849034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 139575845 1250 139574595 139574597
    0x10203150904050316080d02040801020a0e010306050105091e22050709210c030506100f0f0312050c0328110a030e01030f140c09010f17040206091804030203040510 72
    0x55428a543e40c40c0d52440307900400d45286000c884c040c0304000d4210b0840d10780e859014000d42d00c6503151081c0e64001d5001e4016000070410030102c1d800d465029004000c00c55070140c462a00382141c2c8400e2040d0140704030b101d40401a2517860b0719180c3d558031031440e0480c4504020090241d03d00741d1107074046542c003424150501211900c100144030511140c142200354043e03409450010510b4508013906098000905078090041040184e46566054404a403880000420502d035140a0980804003900003d003044d00035a00200300640244020030311000118112031825182402c7e001d040f850307021001e041100c814807400c0d1425484140d25400d00a040d01400002e10690341c0604901841410302d8141a01ca0025000780c030b0303603a84418402403e558030301c44145400c21007050154064290107002c1071310441e54032038aa210703100c0000c641408840d151441d458580030440380d070700420040c543c403060b00b40044488400b03050b0401d0045210b0707002161554189010841049822a180f47c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 139577095 1250 139575845 139575859
    0xd060902130e01030b010b0a0203070606091a0402190c0203120307050a092c0705120c0301030c0617150a030501150302030c0105120a0203040606030b01031a071d0112061701020315 79
    0x813001c10a6210001d0449030101880c6994141688040c0c0c218043c0c0c1c0c2014007254a00b4000250181c116089040b030304a414050b2489164507030104401c074051548111455000e0184179940c05d8090604280c1a034001011030300034588078404030202d54000c4504500045000c19100e82d1a90090520400b8211000c41381c0324884107100034880d40d8000d104683d0100c403654012450080c090f01c03c40300382021404c0d050705030340b80c81900ca00595000b803008a03500c00700701350b000440c0340c4100d00500c403c1f0b904000b84d10541c0c039409550582c40c1c9030ad0b4521584110780c2080000012402d200e00f20100700c000c0f42c45206a40f0710300401d800e00000000c201d061210410403610f840e0302240b140c59101c88090001605d03034503203040c40c200800150b08018910005070001109110f14114031000080c280003034200185c1d40c51208950420100084c0030800907149010a0558000c0c442100b55190036000001c1311a0303144000008225071003c0041165800424030115540510240c508580299204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 139578345 1250 139577095 139577099
    0xc150306081b0a0503010603080c0c03030405010f0c0204020f1204111504090203040f1703090118110402071401020f0702180708130f020301091103010506101e0201020d060902130e01 80
    0x4281c035100502c5000c08a0000022a2507456541900c4103000c0c1001030000c02c81140c9a1034502204d600141c5402c4007445843c2e107083d250b19000088030141c0d01c0694802d000d01c04111825919000c1e00d540803641f160f000c0c429400c8000c1c10711f01400007108802d143c808030b8106424140404c88031350450030300442e1151241040a00000121002c58440e80801680ca0742c4a04041e01c4030348099400414050a46001c0714414030b003880514065841d08000b040110000314400d003810042d031100802a5100b28500290751406502421440d0301410940e000000c030b030200759003245d100c080340c10305852004c9520740950034200c04082220307002440c2018070b8144442c0c042c000e41c50082c8031403000414101d0000800420b00e00c40d02c02c0c0b5034040c0c000d008c191171524101d00800d0420061038042d40c64640090014648000d98070070b02c8130303076490300000c02060003815003040c4509043c0106564081100134003004d02c0e8402c2c40001c12003210016250350003100359800203051036100344c0d0120019801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 139579595 1250 139578345 139578359
    0x80d0b01180b181207030614011d04061805070e0a14060a05060a09030602040b1908040f060507170a140f0c0405010f170901050405120f09100e06070c150306 69
    0x441d06000c898124140d2034541c1800003c45141640140f13080d82c3c00340c0034000003080801c3d004070400240b00c440a0040380c1e02e9072071559401d5006034010000181000c04034010038850ba02c4841050b01403180a4484802d548070a1310b000d00542c001101d024000781000301c2c03914540314140a106070b9001c2540181880750004040300b1241c05402c0c4552000102845598010080e0000440d40014190b417075135a90000000f064101815a0000c011441901038020380701e180c516104030352020b2000c0110406495910081030010249800e0101416400354401d0030900b109109099040d80400c40308500c542030076180b03102400300b0300030070192000e20925140c0f880a8409446082c03a1031580104090710440e00c4030b500c42d003100c140e610b00c14203010107200190806031146000380112908511800889004d62180356000341c81208184141c40b26440c055110008050781850141e030744403001d030000b501562105100320780780843c551082001555405803c1e00c481c20742e042c2004800d03c1c0c03038170b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 139580845 1250 139579595 139579597
    0xc09010e0609010320040501120203040f06050c0c010908030415050615030c121303020120090405060d050d0c0c06020c180601020f0d020102070c0f1a0c0a080d0b01180b 74
    0x403205104060205002c40164880e501403107822580700c104680c1c0c03074083c01e407035001030380903024090025410402900000e01d55008403402160b00400e03e4501c0300054461400514018204900c841420040100c40d075000b4043c641000d0f0203440d48566905041c905080c28008160900b0b09040c10315007008016545e20a04480c14201012481d5499488202c2d01701c0501c6020004144030403410103001c01324201a1905000c0351090b0020401c41d01103e41d50040c0c0445844010390885d0200219080703400d05400c10ae801400213801864551002e030f6460303090202c0641c2c4440080e0351490160309210300c1303840c403000404007400601048415000400c0940301d0026140c210700d006d140206405904c2001214400e0f1b50080c192307001c070940e0840c0203004c1d50140805903900e00700c074900801c3d200390700412401110541321004460920205c181d2105410400c481e4841c0c0c0204200c900c04243c850000b03241a00400c00000b60b101c44000c005004103018200300d00c00388201c0c440c1808500d05041c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 139582095 1250 139580845 139580867
    0xa09051203091306030615051905060d02070303320106030b090705030916030b15030613020913150c08070518091504091406061008072607090801050c0901 68
    0x500e106240000c08203c50000d88190f0f44004c2c0010f250403640721910300341e070f01c201040d60030442c1c0d0000004890304000004000c5070141c0d40d03101604100003807142c2500c1e401081c0c0140310742030204294150022014541c0c400b070f822000401c07030381e0f25100301140300d0306142c078054600b03030600f00842c0f80c0782d2000c00c80080000700607005002001010421400c1c1c10416a07040601540e56000041c1d241d2404500405099074a020118441c00d9490214600421024451101031034a0b403050b43c8a5000c12000c0300002d00303100f0b1030f13003040d01980021851030f42103080d107000351101c0403900501a10004101c050001d000b1400c101042c015601c0c8404601b60b20003620408841076501f130303184c030281080d0b103c4c05546010b51242c42c003855a02041890814100140b00c3c0500380c0f030195460506015600b5800400350340001c1b81240002d08550094001c03210328605029030201c010380018a01700c0c900300644011002c00d0781b0341c0040018030300901520f81c0c0100c85c0c4800500f08012940040c3c4111446 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 139583345 1250 139582095 139582099
    0xf0506030f010618030b0702010e060714031f0e01080c0108060a0509040215041203030e0d0203070b0c0307020c1002030c100204080a0201140f040e04031103130504020a02160b0a0905120309 83
    0x13280b541d0415612502c1802a41c0c0000c3d045090b030500e551f000c0d009042c41c01c8000c0007070080307100141040d402030b40d1a40c411204100e40b14616070303842c0310815001d10b05a01ca881c50260000005c0303205d418450646010f03001c04030082c6460404031740050302e044001410070b8070441e801d1500f0701a544600081c943c001e541598001500895040c04107080d02441d00301120110b804c0d54000281039240d0000d60440c01001c007076034400c0741840350480e1644603a0a001c4c110361000e001003905103001c4001950310000354810b540e030360200400081c412651807064000103070b1022409215801c010701c0fa00e000200c81c107004520306481d00000c5900c58144410180c18451408201c0d031114010710119991101041171265031030b501c42c40c54458000301034800790009919214203400da421300000319075042c0c580f40619400340d032601040001941c07041000c01708500411481d1003d440342d0603020005003041107002916880038810091200219502092180c2038000b0610365905000c03088540c40501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 139584595 1250 139583345 139583357
    0x201051609120201030e1b1206042d020a09051501020f0c0f06070c0308121518040f14071505040b030604020f040308030a1a0306040b0601080a1d01060f0506030f0106 73
    0x1c41c00164020706c1c1303a4001092038001e14603680726075014144c03100c000d550704903401d01d4174100c4072161568a80c002c980c0109484c14140310b11007035040034148e9182e104040392881780885000d5012522081455010351034298640c0103210390121740d40c05844003a0f10a200034018540d030351160a42d03c84510f003182d40113200c5040c000342c06448103002c8606190300064807010480d680e02e404005a88941c204840030700c00c143c007180c0076010181c0d030f58010840090111000d24403040081e403c104000c0c0084034080301c1041e80e040002e400d620001c051136000380160507190701d409400d601500c03400450310f003007010400040c01403081c00b60580f500001e051f03070010380f5084488900303200b03481103420240102c50084200221010360390000d6841140e84090b070032030050040d00b8103560316820b8130000c003144d030b10100040040d481120385075409143c00c40d02240040058031804004070000c041c0038080c1e511010188034101c0890071074002030ac400d07141240b4510b1b1609410070040b01c180105420401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 139585845 1250 139584595 139584629
    0x1003031101060e130b011a120711160501020c0f060301090b0103110408100b1f1d06040f03020306010b0307050f07030203040e0c21070e010e042304030201051609 71
    0xd030950010740500403c0b034038034040d820000702e003030310054100000715420080302c00041912a041c0d071818100c00c045d0310300f550031716401300008411444c00506c0401005400540308001000400410340210f018802c040001400c0c04002030502400203441c9010303069440a1b176005440b0001240d04403103c1f0080003603180b1600c0e0048000c0c000200300307819220000706000c0390040000c1250006d6180300705003045225100024414984014500c0c540a1901c858106403000d0140c00c501c04001c02c40403c01c3d1000c0d40000025501b80c1140d080080c100f2001c40e814411400c04125090240001c20794090852500d100c1c008c0462043e00541110a1b40101f40c460406d4020420b64015000208010080c0e01d010003529403282c0140020800c881031030100c03511444c00c4803031014065490b50b5203079983c0308404030041d501c04400c1e904458004e80c0c0c50a4000c1c090304c02c4400122005044030042a080c00c044c10024292100580002510516100382d03201854205207404100e40b034003044414510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 139587095 1250 139585845 139585877
    0x170c0d0203011409030408010b04061203120605061803010f110a0c14030f1207090f090b18090718020c15070c050106060210110c0a1b0305070308030717100303 70
    0x464449105064140d580f4113201100401001800c1918500b0000300024000e9800b0002030340c001d4403a55102c0c1c00100d10007000309100303186c0341450003442c0c171011401030743c0e41e0301150b4164401e820000014028104070345161500f07006085200403803900901000b416000000714501c50348d12130304284014401e0351802c214410300e414000000030003c0c0d81e01c40044424001c01680012442e1302d00d145418005203e0600070204c00040d1000300b209140100d040151034001408420703042540320307103400c4c801100d49074003031208d620400e0f80e14050042c141c5032000b030000070301c5d00310b540d16225401403203515403524001600a900081e070020042050f1214902668141107110000e4a82e5082800101d03149400040d0500b20b805121420810000c81e00000021382c0119482d84000d904030341c0c0c2290102e05400003000c01a0070605001328010340e240d40d00c80c6040c0060b4001c81d04e00b5408010403840a81200c0942e070110100d2003075080c10b240008041d49400784500004062080346080c0d8030b101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 139588345 1250 139587095 139587101
    0x60204050a0f0f050f0a1806090605060a09180b0d1a2203120209030109060501060206010609030b1f0510020a03031b0507060e03090d0c050a09020c030301170111180a170c0d020301 79
    0x4061204640c41f10060707a602e8100980141d02810410900f804000599400d0003021507520765441c0e983d25007001e003862281c88170001c0d0204030301c070103980399a4508000d5a4600c00380d030b1803078459a901e54416150300d41100b01c2505c020901c1240c1e03104840e05000c940c128035030740003025900d4a80a190a074031800324000030700448049a40540c81e00404104005107a40402d042e60381503000c640c881c0c0c0c2d07501400c82e10f4203454000200390169042c082a80c0440d00070b81c4450303034541d4010f0031000c140c80d400800c0100c0200e441d140300590003c01c5120a0503014401c0601d46103074601820095001450040d04a21845400402c1c107a950095000c1c1c08a09100b0b43c0c00c51007000300290605801800d040d21220300c1805124400c01c1e4003100000c0402ea54800c4400d800300c0314000e5801c580c640703c480c0010074580401d600155403100c2012807030401280c0100f0305180003602d5561182c00c05020b0010721b494642009030901030315031182012500004198040b40400c0342c1701c80e504109031000c0ad000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 139589595 1250 139588345 139588349
    0x50d0f031b05100605040e0a02120703080c030d0b0d0f031b02131d0309100c0510020f07050f010605031002090f09010303080612010504020f0607110d060204050a0f0f050f0a 76
    0x80307058640044020000d01150303c200c403180c1d0280a206094440d0100400c49444411040d199071001c1404001800c10340140c070220011a0161000655a521139610b240d0000305000e00c3c0e60400114040b800300c81e4440d41c44948400d84103050905125503403d000442c80f450050180401e565100801040d1000301024055002c2c041040c02103c1070320503400340c0880c202d0512018812003040640603000029140a910003c00b00040d2030807000d0103035109510703450180da041c041c501000070005418002000c500d0400d1700c52954640044c2091400c1181410489042c0d0741001d0003000203607400a0a18640440140010394a002c40c0000494024101407900e420808110001061540040c0c1c141e2082078259041641c00880322101803c880d021680254044041c904c180054100341c0080c0900d544120701100e41c0d1165000042c001c80850340c0d003100c0003031300002c4c18046400c2c100210002012541034640e007950a11402207400c003103902800d809040b04508110031070b0703141d0703440c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 139590845 1250 139589595 139589627
    0x20c1903080a050903131509050409050303070c022b0231020307030e01060e0601030e0d09030f03090503010519060803090919020906030c220612090302010605030f030d0b0109050d0f03 81
    0x200965520a02c1c0a01247c864000c001c9986408006a2800e05000d00010152f108001e946950380b1858166215903488000303a82180301e410a6043c1c461001012950a80c5139034551982114a80304100748000ba0082503113943c0d0f2300c403081f910800f000410105020540b50300c09626907030b84d074004800509628a84007169820f0800026800781c89a5840e80612420303601408590340c0701f007504d50303141080ca2001000071070b60300c010800714100e8003107040c4c068440d18105226a699400081c00d50b10203861080302c1140d0041f01203202150342c450b072402030034204055030401c00d00c0c00000d80f80f21801080302c62940103001008075014144c0c0d048404082005021544a041c40240071105030004003c9664804102e01103d07505d0b01000c0b20501199103e5032143d400801c0030030084043e080c0d0090440a41d034842d0f4000c15a60b50a02000640103142c0c0d0080d0340b00c1c02040c3c10702c8152a081c0d4511814001100780031f02481d218040ea20109a40005107206044010321303040742d600403414582d1f1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 139592095 1250 139590845 139590877
    0x9090c0903012306010203190c03090e0a020a1106100e1b0c07180203040206030403030902030a080f0d05010e070f050310050d030903020f0a0e0117010b040e01020c1903080a050903 79
    0x7a0098684010b0440400840c603681d000d2aa44d90006a03500d20a81e0240454070100360ba01da000130b4490b0203d90841d81c442c6c6000d880040d034924a030b000e401000e0b503510340c403d60045041d100036513002160320704610010004200c0e41c14440c001d004818a14010071141c03c2c00e40002580c4000041e20808410031217101c640d60701c01c4035080d40e644a52440c041e04400c49038888014039840694002e03a4001c40d00204243c1c40c545072550f09500074454680101e8142c00f4511a100c08038032501c02034000200c0d400091540c0e001b40710720349011034005820001c5424003180c140010342d980689030303207100461800c0656881d120310021043c40c0703005900c51f5500402d001e026034201684881301004403882500c182c00c49030702800c10005e02c0d4070103020720300e00c03400b1b00c80041007a40200420f80d4000c0040400004100c060781001c242980d008180e030303100c5690001a000300e40340e0304215410300a0325000c87d40d0740d42d41140c0d034000c00c4c1c078a01400c0c1e494030342c4e10b80c40850000324050048406100b01d09000c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 139593345 1250 139592095 139592111
    0x15040b1e040324090308060f010323071404030f060b030f01110403170a020c040b0411031003120203030411040b01030605030d0216080102040501120c02010207020a0806040506070507030509090c090301 88
    0x150003901da43c86080b03400c4445140f820141e180c0d650282040041d0b041d218003e46586800c20700c854000000b04990415484511110000513174440c11203141d0072003441110a45000c050240240444056824650400f000104049032180d09a036850310b6000c5800300d58490800d00180c902601520329000e19460b0205902d540b2900a00034000c4911812440b0309210441c11610441d0191162120142e08904200da1251904d580b02c10031020740100000786e0842c2008040000e0b40003103610703410080710b120062040c040849044240140d80d413008524500d041d586c0d4000010003501940e005a40380d09158005a019070494005840c0c0903080301d105d0044000c00940c0d604100c2c2003d01283c041c410302251014040c02228151501031311481c2c114805441c550004281d041b2440c0c0c115517081c040c0000503521259041c000f0132441c4001c141c02c1c2841e08103241003113400740034070b001d02c181005003000082d040030984201e54401c444003245542d50201421040c0706403022aa4994606012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 139594595 1250 139593345 139593353
    0x90f0a0b04030203010c090305151f080a051b0a0b07050111030a050a0c0801050303120415050103030504180c0c0803042d0b160206040b0c04080d080105040b15040b1e0403 75
    0x90011a40201c00074042c01c01086c0007903072001c4060001078110741003041180503031085041c00c40c2d040450b241c8511004046c250705c880e03c5140075000580b9540140c0c07511400c4c80800c02980500321800e8981d1700c84410480c0004010300143d200328008640081482400d0100a5200c40c818102100b00c42d40d4030325000c5002c5006040445508d8001d500d460800580c251155000c58142d4001800846c40c000c0406900200040000e2007100ca12688450328030400c1d41901401c1e00851003a11381703e85035414840c440410004450004070302500e010b0716262680e038407600700741500c0d810010003541c9407190300b02032030440101d41d400f91108644c2c600046a901d0000081c1404500803c1b185801d40c0f90000f8042c0780001c0c403100e0b400140d01c0310b0301080c00305890bc2c40d0f9a40004480700020314103070f9140090350502c0074802c456030116000350700402c4542003502450000910071916840628001c2c20b814600f0300690060384a0030300045154005020000e04180403c00750541c040d0b01d880d40d03850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 139595845 1250 139594595 139594597
    0xd05010302120c06030a09050f011a011d030a020f01020316080306120a05100216170301061202031b0a09030606090f0c0c080717040302090a05160215040206090f0a0b 73
    0xc0308030b0244906160100c2d8642e40452000e910307030001064503146855600200001d0300b00c6c00010796542c0550b503900c3d284c2840074420a02004040000951a80b0152001510340740d0410045a12108441110740c0306940c00705a100200d079049078207800401817072300102d2441c004c05014202030440035031808244800740c00074502c42d100c21510303217041c8581e6004441d124140311900034526802810b01003040c00f00c6801420507040100c11660011120361604021803400040c01f00c0410310000040c02885d07409404201c6410300f88105614509000381681c1c44230b0030300680002d1a000104420062030722950f040401560000d00500079951507a140340001d01c60344021400071031814403203030744c4103004028403071215411003101410440c90740c030b41c5209980312003004160f40300208000300043e540d800c1d1041c0a0f041c4c2c03040005075460b16580ea0a02c0b07100d246c10090540d4469041c0201480c03078020041d42c45941624010340740c0c6400f00104c1c407400c884240c2c0c0c503030260030b17034902007480c6005034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 139597095 1250 139595845 139595849
    0x19050f04060c0c17031e0f07020106090905030306121e0c240d0b0109150201090b0c031303120209031903020c0d0803130f02040507030b01081b120703020702060d0501 73
    0x30304208202c4880b1641a241d0b01041e00c40107041e80490a512262400301e44050f50b4031009007440444442d1000b200c070754132154100d6403000c420883c2028485050360912455001c0c000d104002c01210109444113552400001e000e10b21444200c8445008210140710048100300c040d4001c48401d9001450070384c6030341d0f003252403074010550030700c1541501c0c950380c001c101203000c04150240350600e801402c0018220b01c840e0f15044c17000c21040095501c504d5070078a05400e8660b800020f100403540b500d500c0021000c0c1948080c44414814000300c00100c038104464154103080007000302c8a0320b203100d006800303440300072641409130840b401030300c1c00100b0780a446584a80d00341d94100c034486003084231110b0b01b00c02c09407114105100103403651101c2540304040d07034029000042d0300310b038541c00207003902c03400c440490009032115a07420351941c00c5014980c0021543c60b0f2103251440001a40e1546d0144c07168501208888401140f641e0303001741d040b908602d4000c0c4c1040d07518002070701c151010f41428 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 139598345 1250 139597095 139597103
    0xb0d2307020f15010605160606030206070b01081606140901030608030301090c021e070308210411040b040902030a02040b060403060c02061803120c1e12090622080319050f04 76
    0x88220301c03c8201014051416560740380c5a0604009000c07284403070207030030102d04448081d5507680c08809603564034041c1c803401d403080c4a1204070351b06103c040c0f0b040405055100b04080c44d143d80520030766411104251985c80e900140e03e4840040400480190019a005018500000001242c40100c070b40001d42d880b65203401300c40101205006855050a0384a6440401e4000c803609100144c040d400406e0748024400f010ba0300c804804e80080d40003c410384040701c61001d00d80040d0707076504060003000316901c1c0c03c40d000c2003044500d0300880d07101e400408000344075039600d00b0b00076035640d01c01c0180d80180d42c01540c1000302c6d2404c098080d640c0c00c0142d4030346080024220986002d0180001202d140d920a05480c0486031112640340d2041c1c0c2101c00c1554410342e21140c1c1408c0300f410000609201c02c5100e070303daa203904006c01e0702418004050071111038401e13400a1071001c51480041c45600c0740c0c1c04a103443c0d90382d80b0200e408180340e038034040e40c00c403441c01d0800b032019100c03031250864040c40c05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 139599595 1250 139598345 139598353
    0x20601050a080706030c11061906050102030f09061308030a0305040b0c032412010c120b0d0209220206030103060504030207050406140f0a08010e061503070b0d2307020f 74
    0x2668100001607060344a45030540e0f105801c2449076503c01d80002c3c5607004941444030b90741c080c2c010502d050100132035224520419000c280c000300c140b140030f148001e20080c0003862a04204d41c1c1000c0e80c40c07007000780c96405558002505038200ca030501542004061441c1a00c0d1908070001b80100581300a503410f503044c4041c1360210317000301500401c0324003400c641643c01ea4004041c5194440c2c08050b1225254000300c03c6151807184c081c02c0c001d6907501829690f075020308034005561101180c0d02c803440c060141c02848002001600c60001e01600038000301c001000404005001c0c903101c000703e00001350050800700002041018136044140118030940944492079141d02c1448100d840c680714000c0d9076101029205020305040c1142e10f103c8a02601e80510b043e02d90410900b540c040701080c12072548010704000e0364529205c409441076100710042d1074000c0c944410003640e8024540480c02c21a43c0c4c0007003004503585000b5801405070424110443d6140071703180a500c905044101540380d0003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 139600845 1250 139599595 139599599
    0x70c050c0603010b2d03010906030c0b0306010207050d0807060219110f0c041d01141801020703050a030c050c01110c0c2706062520090114130912020601 67
    0xe040010360341a260960700d141d0501c08040051600715107a000c810a04c5c551100b81003690080f6003006501819102c00b01080651a40c0ba24400d107881c10f9002900704402401840700c240ea000c1812000c4900840e48511902550708001c1c0d1288144400202054400079031112901100c9014030101c00386034070340020b000360312540503844410700f59072421b030741d001814680e03424079088d485144410200030103014206510144182100d01c20380780e03a107100078a80200600d880b0361703014240340012803000a5061022542d805802c81c040c900104003810744070580d51206522800545112203041e0002340018440a8084103042d4010a00416a03000e280d440160074101b91303a0500c2c1c41c0c0180c08048a074541198900c580f884006824564002d900b085200b803001c001c2070010199a070f18000c1c072004003c1500e8451185000041024498100812141e4190303035814081c0d411034030120494625214043c0010b0316440b210b0090310714440c41d048000d01807040101e802c426494050302242e50f107036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 139602095 1250 139600845 139600849
    0x8070603060b13150e0904140f030406020312130f030e030601050105090307031412030702070e0a050121030201110f040f1d07030906020405090106080f01090c09030f0c030b070c050c 80
    0x4401c11628140c120001c038010010b48190f20240030321070544e80b0344505c50032417460000f2802c24055074141c4400c21014240c0e907403e00c0034000c0141300d0a000d070007540b03410300d010300c06900d1f40201c0d0100740c0c96098060000c5c048004104074001511b80c840300c1003400000c2468041c09031407869444c1801392054070004035031035006900303c640b4910002c3c000c001151a40e551040301c2c04805004017168080c41c141c0030b64520200d0040c40c0610080c1d0040d242c2c00303050904925020304020030344d07101281401d0041020390402d0340003116981414032121602880b81c01e050b409004003500800740f12900042c0700ca651070281d8090410f4800610000c0d504035503131500024520b541e522101c441c54a203402141416001c1e500004006105100241c00c01e5503450000313001160903405400480c810504105605850240d40c60151162104c108110749101030010854061030000811003a40380d07001ea4103000031140850000c61b8880300151041c580348000901c50503402000325114031640c3c00c041428 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 139603345 1250 139602095 139602097
    0xa03060602030322060204052211160b10170c010306120203120307030b10090314060412050703180f031209080c040216051b19050d030309080d0608070603060b 70
    0x503100c034031189000c0307014103241c020180e0b401003405c440c00c640c00c12000a007900d070440111090410502c00f5811206e0890b10201620700e0b41d41c07420600d40d170400600c8414501a00303182c62603a00700011086503910140010010f001940011122403041c034082d52020034005118105c005080e601880007907610060098001d00c0c003d4000d40c160081069100d4000c0c0741c40165074840c0003441c010410540d01000320b108002c0c1820000009400a1000e00c24010310015403000d55646000a1005140c580ca42200f1100b000c10440d081010000c5c011003414883e030801c0c0507103208000c184080554411080310f400086110072214401281c031000c01d10b502a2001c002103030f2614020300902651a81004029440070200d0001c80c07180340307404004550708014050380c180310b84e8202c078600c03131401c810407580300c1081d13651000c15101e61400340465200e840c8154030003985810080b40008043c61b020405014991031001c07418900314000518160000300354085419640b020028262208041c03011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 139604595 1250 139603345 139603351
    0x60804050312100f09050f0c03190506061b071a0406080c0703050403051c1107050114030406320a060b03190e10140108030a020a0605070309170a030606020303 70
    0x80ca03041404032a001c410703002e4200758440070584007000119150302044c1d240c0300c41034219071980e5a4441c100130400303110303081241d00124a10703d201c0c20351800400b050000c0c108030000b030804903210404221103450b4101519641d150158110804001c444003a60b40c81386a41b28011409501540c1440e98180c04000c8038240d82456480c11844c0d96000025402070384a0345c0c044007007003401c2100002044007448400d0542601400b030a50340320026100914644515480c119142c1109008000c123a03005564120038000c0707441041d440360fa80e414640020408000a503641c0100300303801c01008812401d000c0000040701c41941c049460300700c0558202c0b000d0340103400300a1420004114404806a17952080c005a00408900b4021200b5400d08000d0807004561a41b6100d00c0b8400350403526490090261040304025070909801700d000039914541a000a0f103050741c0e07a0081110702e40701c0c0d0041c0e04615004904c4491860302809402c3e0340d03510a0010100003850300c000401d84900c00310440340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 139605845 1250 139604595 139604603
    0x60a0e0f071d0d050c0102010c09061b0c1e06031107030c14012405130e06010b0d2901080610020706050f0c070303020102130b1e0a031409010c09060804 67
    0x65190344008041c1d54401c0e84640412204100b00303103410540e0f5030514198000f6100d1009000300082c10000642504e8080f090f09042c0144840b06000d05c50b446240300d01c1e108030485081c40031300311a090400b0302c0449500040c0030ba5a107002d08140c070805451035141141c105a07402c008281004002e080782d40280c8074000c0008a10641c4040410102401c412654a003400000340c0010605003004038551a00a81070f861054088200540e141403c00c1d242003000c1d0303000907c483c400c091404e9031551014010190707a0700d0302050030307104039a00b984100c10140d40049624a4100711403002c50403d0300c45002503001483c400c000502a08081002c401056901d0b00200b4240e82001d00c15100d030f030401404950400424881000340600c108100c500540c000c1e000140c0d42e03021007041345001c0e00b01303410005220034200300b1b00201a074490404004102502102a11648000411406005041106030800d900035050041008041d800040125200d80750f00c03904542e1010143c5181c0c4041354090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 139607095 1250 139605845 139605871
    0x41203080c0702030312090319030b030706030e030a030507050d02030403030b09181203090f160509011505041404020d02130503100603020102033001080a05060105120a03030b010e0d0b060a0e 84
    0x241401c2402c6d41054000100000340c0b0304101884118050702d9152051010001c0d840c1c441400081c02e0602005010f00b10230328007032249500c01d09200355a441090280400c05d075039100020600c51044080e10800c5040c01410346d039070300346410010040c2c8080e00e000b80c4100e4550000c0b605500c40c84c07054010b15000350003d0940690313100a9503e050708010840c1c41c2c5801907607000040800140a44090325542c2c59101860701e08100500a0703810050b00180e130034000d1008800c40709034000042da0f08807003c0c1c0813860040d4006801040c042c0c09035107501c5807464004210001595103810a401c140c0303105038112030030f112440d18081c060302d40307900c0b0103030141c0c00400141c14049255480714400681603410000c155a0080c15842d1480090740316800b69004100500d00f0010244620341c01408111080d0741c40b001c00c1031241d502c804000300c00030145903903580804e016901605000381400c1c0003c0040201c050030741070a80510104480c968426085c0c070300b02260f440ac46200c00d0340103011900381e42d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 139608345 1250 139607095 139607107
    0xa050c0403020d1b090e1f0b15092103031605041206020d09050d0f0e0a030c06180b031302030f060411120f1c0e0108010e190b0303041203080c07020303 67
    0x4c0940d0301040040d6030300f1080000089040211401842d00c030039410801070102c1c800c009122820b003c441c000c000b03075060600c01d00e0f00440e0303124800a01903810f030f9440242e07180480e40c0000e0400c1104c10407181c1d11070b102c1031a01160352000c0051807080010030381007120302c07a4400f001c0b05c0d14403480c02072140c000785c0c0ca0031210201ba030701d5010f0944800070010003d03091f903942d101c075031420001e2048036000920307038450048416072250003040109025604051224215500c1c1042c40705140101e00400160200e64038224040000ca40700400ca0581001d0340c83c24040002800303200203034030a034003a200e8100b00b00d01059001581074403c42d007100c2508407506408040141001e00c1e40c20309116882620380420000d1005d2042c4070640c5045845443ea0714641000500711498200c851070500400c1d800400074010100c8920341d01c441c80e1020780e1460300c2c0700300550303004001c515100382d014400841d02040800710369400e1502903000e42c913003a200c0e6803038207280c0b58030748522040290560010700c15 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 139609595 1250 139608345 139608353
    0x909020d1103090703031409240706060806010f0806010e0a0e0a05010f020d0e01140406200f04030c08030a020a0201050a05040924050f030c090705040510020102030a050c0403020d 79
    0x60401100c122402090040c48140d800d149a00180e641c401240c20403181003007056000404544001100c42101d418480340a0025244242e60318030441ca818003242d062280e900d00310100c0c3d000a50002c4100440c6845140007950361109005070040100a0000030030044400a50301d4100c0e4206104050aa581c8855820280c074500360300c40c00a103c3c0341074200c0095800c1c001c200941840180040c0c8403c881c04000e410398046480000ea82d91520450f00c0c0016000381c4d48540c080d40040004c40e40c00c1c2c0e0010181c001080342d20380e2848054010030b40380e03450f0841400038000c8a018144003030601e521041a1522442075100c00c0002d41d00c44020400154002c0000d44034103013260801608055031110000191001c0c00207034805d0740c001450300203070300304040001e4028040640300b147d180214080404d41d141a840c1225114180c2000080c0c1600c0c811001c0303801519000c0d08032852590040c4c1c0190103500241d4880354a5800e010028030402004001e44080326002005042036081c8ca8907 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 139610845 1250 139609595 139609597
    0x605070c0f020621010b07050706050a0503041b0503010207030201020d0e0105011d0702010b0d030c03080703050105130e030708070f0b07021603030509030f0d0e03070b030c0703050c0c0d03080f07080106090902 92
    0x2c0280415601003088110070740207032404e107001701040680c86540301c150b803800b40d0400001c1d401030030606c5005c0c4901c05040341d1100c04e0329032140c0d000d0110408286c540c50f0242004200342c2c88140d1543c00040c0034810141c0c1900a03050040c203004080c002c640c4034004841c03c1e07c0c0b09004070200c00705007030500384214004070245070304141d80d03000005150380010b011a00811720802c00707801141d5650042402c16900008a45d4025442c3c60b003040b041d41070070001142d0484222203c0031032502d50f40f040a86800520445418230344c8500f00c41d0365a4002d180c17441596042c0481958a20030110020344082e002248800c00070307900b02d8420a0381819940d0a4a603a0451048a6018801c550840046180c100b20394021180e45854000140281c482058500309981c1c00003003040c8418000d01441c04408000d440c4402e51508001d900c800d060050145085000510382d940615049071000c02d05400c05105805035048416941007595141c0c02916809802e100d1000040d40f00310042058a140368 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 139612095 1250 139610845 139610857
    0x3170a02040302090f060910060503070e1f2601030b071209020a03150b030a020a09090305070804030c060908060603060a0e0f0a050304060207230103090c1d040605070c0f0206 77
    0x1580182095169004505109000c40f000900034520805205c1c1c1e038a0502d00c6075900040d2188100405802e15034000c3c000d00020340140184140919035100320740c0da9800c461640700c41081041c00c1d40700500e200618207400d01c02140070f111040c0c040307640c5914100b81c203d41030740c1d00304008a403d0348614400705c40500c0ca000f00a01c100e60740340300400059542d115210700031409044400c070740582c2a4041c070222081c0d20301c218800d80c050421140142c4444401c182203905194001038081040d0409a4051041c0d140081810314005008420400d05403844c0d001d58030550390b0a15859100e1905640c0c400c3d098500700e9242d84804c0000d5212a801e81000030301d8100d0a0684911804a840040c548003501404864540021405119041c3d04020b001c00418036441000c1002900b0b041c3e14000500c44030506041546032401c1809004a4102c018001d21039032003024002d40c10040307050003120b01507404079440c9003030a011484503880340080c000d41607005107080c8a1001c01d6403c200c2d59900c51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 139613345 1250 139612095 139612111
    0x30a0c150b060d0f05070c0302060609180a03030e060c0405090a1122030203010b03060103080301032a080a0203060a1a0f040f020304030915050415030c090f0b070308130317 76
    0x1e401c1c0324106844a201030100109405008201064840030140a4400c01411101003105880e58031000c0395000038000d8101d181580e0700790942d02d0f6215030009414038016500840e1280701d400004042d89540542d0b003060413007007550380d192141420212903100b203101d000e80c00351001c008035000318030660051420090194256140918030040240410f81200144110440f00903040040d428207004190a01e03404038050314003503041d907480c8601030106001c0038281d070500d06103004240c07403410900078001b02e90006501c44c581d620080b181d6140e484240c224080e005d1700f0041a442102030045140440745c4800c00d140c009481420300c00303401552a01c480d44203449081150800703009100440c0201c1c0295a40341640d8140003150625916000301082040010807040100d808102014070440c4818600070400c00c0c11000e0403035514549810141c200726440c0c60000f0f140343c031000200406c900c00d80701e0b1005a501d0300d50303101c0d05152600300580403d140118110201a84101042c0d00c40c0c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 139614595 1250 139613345 139613351
    0x3020d02071406131a0d060e07140a0e03031b0c0904020307050f01030f02030c03040309080a0c050f030f16080c010323040c1206050106031805070b0c102408030a0c15 73
    0x103290003518450b10301840222440e4000500c5980707030352260087c2806004400e0303000885041c00b0340010803240c01c4080d80003c840d00401d0740610301d4410712100303a031000d00030202c81d00c44c1410b010743e800c13184141100311110310400b01d4510441c2002d20b861403041c1e03001000351182c00c0c50601030004a128014206041583e2565000040f03d010320145004403082c95502e1380b07906e01441d0241c007000240e08600041c2d40202c16040001c0c0704051410107842044d1510b84248607040b0120b40703442220001400d01c1d02a08002c0c1d042e07503045040346c4040352411000c0318090092100154211410444003903038408041d03490206051a400c0c0d255040b0380315061800d440c55440c2c0c2444841c11084000700c4425486100410045505000d070280b81c4100980080e020724281d61140c2d0340d0728045c8181e031491740300482d00c2e89003800c0c01c0c41006e810750810311080c4004c000b504980001c1e00e80300b4185080b01607251002081282002054401e460700c0d90b26004c040340016110928060402d145080100e52 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 139615845 1250 139614595 139614599
    0x201090308011802250201111207021c0807050a0209010f08071a160b0613180f031e020a02090f09100218040606030f0f1a06030a090b01060c03020d0207140613 70
    0xc2c8100354002292171741104588141c9200050139210f465480c2c2da40c0381e0052802c0001c00346400b0440d096194100c4000c0c000c4200d14204400c501160400500680c03001b0504200788035021030305009c0c1600c22509101c440c1e807606849002c0d00220b00a000c16940540300511101980c074076625007120030886054140203070340d01001c0c000d40c2040802c0303440d0384014060007440c0c00d14850102c00107062902c10700101001c141c8029100c45240c2024180d01c131400d800d03409260291980f0381c01c003d10041d0f8a2020104d07044046c0d9903142d600812405050481c00040180d0412560580030310b00c850050011202c261075200003a42113a060b504194140e0440d94143e036480b4031444000f4034aa4070301090040c080307281e100450311001c1840d40500d08200d00c03071440204403280c0b2001000c04644580d200d4130380d1070201d030050180c3c10008001e0300c0b000c000800c1c0b40b6000b401c9411142e103c0e50884901a04004007283c40d0402c3e0320950022030005201c40701c00b032814001a14001d00890385082c0c16035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 139617095 1250 139615845 139615867
    0xc03030304140106050103111801090f0815010e04050a021216030b180a030504090f1808030414190b040203160e180304080c01051c0c020c09070201090308011802 71
    0x948156021601d0320307030b031655903401050280950402010242401c1060134502d52100c80d8622400c02015051368600c05d00d25502da00a01d0410090150305418502c0503031204440c1c0e664200351402c4000100015000140da0100c04150f24030440d4000090064480d050f401c0c4400300084c50301108040c050203030420400203081116800460080e003188840341060f00e0b680302081e00080c1f489003503130042003202c0e000c00e42240071101100d48102000402c1d0410720038140c010310444c413600080d2100480014188090341002d1030242e80211a0210881911403070f0700e0f81d82991300c4005590348400284500450000a0100d41c4140003405603030031025900e8100c805803000390000d100c8100c454041c0040d03004c40460340c0180c410200c000754a400c1c00c0202c060743d03444403405443d04000300021039106078500600c440041032400304040c0441c5072113140194840c149518160302400b400d10018111503c1405408403140d010303101c4005690030000400061001042250112502042000512 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 139618345 1250 139617095 139617097
    0x18011419080a03080106030c080f0711120c060103060b1905040f020c0f060115020111040905090a0b0411011b08030a0c1b140106060207050a0b070c050d03120605060c1902030c0303 79
    0x15101340c0c0c0d0380000b5814600040c04a03050040e0742805c001c1d05004020312445607081454104819081464503101c101d8200c81c505407248440a040c100003050301140307a2400030b13100e810389225540602143c08641c060007020417102580011200901808100360305144d8004000c90f04090307005841e105450480c0741ca41625500048195030085004200c40095450b80d000c68101d00d200070300001c00d18094120690045000c0c041c02c031951030000c16500c440070803091031000e510400101136440e05013813615109100d49662400708441228a16805140100310041c40e03131301a014605607295080e91100034446885440309116060b030a42001040020082200302c0c401d10002035000744c81400b03282134503031650088042d035100c40e0040c091948c4062241c02558010413645840b4603190074010b0807a030881d4005900002c2d2151001c00b07040e8001c000e8207007034903400d00074401079030380d1414001a4031413519041e9040d0840302440b1001c140400310440018001022a4203060704040007d080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 139619595 1250 139618345 139618363
    0x2030a0609020c0313080309010905090613090302060f0604150306050a090b01080703060f0608070b0c0a1a0703150501050306190b120f0702070608040206070303021c0b1801141908 79
    0x86600104018003418402242c5c2c80140182c00051807e02d866080043c00c40741c45401840c0c4211818800144952605602d50803861007851051090503070354100030b0344800d400c1c0c5d410110020b1520001d825030030907000300c44c018080c09100800e605c0c03650301d418004207409017144510365218003803400440c202031905400791a141003d440520314625002d0115402c0c10b41e4048224204801000184004240b510842e801f0140150355541d43c100c0c0e2a0601d03043c05ca000300a10070251126108030008040720f40718003030a490400c600044e8400c1044005a1403081900043c0200000b4440d070400100341d0822003002c1304000d6085447d2000054a038000c080c642e080c0340c50160402074500402030b8816000400c90003e05141c50901000170034902000340064002d601c005029410140712381e046070078284109101841c0320880c042100c0161215207039562113481c032000900c84c00f01491076140d0403241a200401c0d12040b0b160140407400041c21081d816045549200080c00c100138005c01c0b00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 139620845 1250 139619595 139619617
    0xb0a0c020d0507051804050307030c03120f05010303080934050405090d14030708010b09010e041a01180e0109091e11090c070f2d03080f07020604050d0302030a060902 73
    0x41840c04d1034240454200110321440f41106490240800708401100710341000b6054a8042c0782803640b4101601c2d94000f508904a64520b4281090f60317541c055409941038038400e583d407000c5515180c0e0655562178803403c12520046035202c6211401c0000552007200700403500500c40d41540c2c070000a01250022030703940d007050304001c46200b60294403c1420a0fa84003c40e503160550a0405c401440a00c0500174003d0041c00080c005a080c0c0c0140784d0b000884400402c1405590031100000018080701c602da240454003408149900e5003142c03c150080d0b9156032040629a840d01c100341010340480c2c102900c0c0607000120000d0341c0d1000c4500c80d41c155000d1103010080e070200030280120003000611002d0f8202083c0200e00001d001160780c003501c2500300c5040000403100b12032008000c86c008403200340700d00c0302070704010030590041c000034482d84811700d529001d0b41c3d605d041a81c03600e000729002402500320510704694140a58091608a03200d410005000c544030f48800080f40e1056403d41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 139622095 1250 139620845 139620853
    0x1404030303060807060903080316050904061401020115080a0f02040f02030f1605030c030c0c011104080f0f0109030c0b0403090b0d06050f030a0c09020c0a170a0f08070503010b0a0c020d05 82
    0x1c0940c1c6002c00c44030b030080591b031804444c0e051854035191004c1c00083c050b080c00003041807410310050310400664016803001001005400d54503c490582c6548514a0078099401c1c0000518585d8a48041c801200d40b510042c0c40e1400c0555a03c10701014511400c0341e016513a41c00c5210000041d2003c0d611488085049101c0c0f0f0030024500400c0100c0e030201e410030003804100300860004040c080d41d03007040180c0c00054451003040e1007140500803480b6104080341b0041800030b51100b00250803040da101c03c2c401d4884c44008142c2407401da490005000e004102403104a400147c88080740c20b500c18000d20785040c5250300c0700c114031055401052103014990700d54030309000b80d18084000e164223100490061040c00b1070740c0d842005000c072520842c40c00903804108011440c10034003050b100c0e2030f0b1041e201c859006200e40c040c0059000042c489001411108480e101c10780680c24581c05030986031603407425a860200c5401d02580800c000d8070400280e501d8040060700c034580090201481400a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 139623345 1250 139622095 139622099
    0x911040b03162d0b090405130f030513080c060403020108060303190e131b030b0a050603190501120506061011030a0207182009040902060309010e120702061207140403030306 76
    0x1182500801000c03440d00f980d4410020400e003403240045654143d01540c0101d1141d69104004910b0000c00501401a1200b840e100c0201f644c0400100341c102005c1085010303403619a0701d065030311400300d0240d41e0032503c00c10003803025601880c54141c0c4528014122032600b100108001007a486195000001c59060380d120022480c12901402c01109100c02c2004459491115101b5510700f100c05801810342d0b40506024541715a83d1220241001030201a5203051820810704000240c2c24552022468030b0000300d2405540c0d40035440c0650000000d000303540781c100801009944400d110301c18404141c0521000c020288043c10640000d500600412807a000b000f8081840e00910003440300e1425042c07181c00d00d00381c090707032564a6000492903128803610012600602480078080e60142c000b000304203074920b05400080c0886100b1050365055003c4101c068101e0003400d000950058041c03141d800c0b2103d00c1418141e0000da40c2c40d01d5a0105016070200140d58480e80050b4002a103071103003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 139624595 1250 139623345 139623389
    0x212070f0510030b1c0804150207090606080c30040605070f1806050d0e0f030c0c0a030201090e090109060c050903060105030d05040323010c090312030911040b0316 72
    0x540c2e010495080030312102030640c2c00550040c602d001c000d88002c1d4180301d9007003846120010760700134109461800e107240c0400c08000c1e603605158461400114100341d40819940e1003000101c2c0a868030030034031030501250306106c0d0042c00c9070210b00344814981c0250380306040341c048251070086000d42000206402c003400c00400840c2c5c1149014203104410000d45540c0381609040710071a80703503141058503003000c80b50300701c0a44900e0401c44001c0c4960314204c05004070100080039640c00400407903240661400910084088921000c4d0108240c00c50800c0000c40800c001d075444140d80c400000c944900e80d0711201120300c141b000d68002440414200400c3c10104205030141c0011401400c0d2390700200c81c018014403413404020302e038040c514a00c14020081c01030044000004000130b100c044207032040204140098031040ea0030f4026071030940c03e801d0091288013441a0489a10a80318081000344805007180d00070054140c4101e44c440c1022841d600c030810003510f0b032515850705180c40420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 139625845 1250 139624595 139624609
    0x4050618100521091c090302040504080919080c0402070312050117010b010201021606020a020f03210106030c0905060a05040b130303090602060c0d0c090902070b19020408190212070f05 81
    0x100342c3c00b9848283c1c003408203d510026030380501d000100b2162091880c958000c507403545640d84000d405c40e041000b40802c2048076009003002000a985442d007400e140b210707485079582c1d0351045100d1a00001c0c6104464240354000303145c0e55000341410a80d07942c0309040c1c101141c20991220a5501e403140080082e401c0a0003240e5441c0b030244025070034038101008410001c1310340e62009000c0e81d4000b4103051301c01d0090041748014001402a203807541e0001600308030711140e40c9142c611941c400c4002040d028020b1103400c42264856640c0d00c0b00358101800c0c442c1a5001e41510f81c00e020341400001400b0410703000800310507080c004000300d801e255140c041d03d9010103411440941d00250204410340d10280240c1d070410301c007403c000c918612a4102603590390309039042662102c0c00090014244043c1c01106802140d140070041078942945030341008a00a41c064030f14550400220f1441c0410b042c41510707a820b0000701040d038003141005840d823425040b9405180c0000040e0810410362600b51 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 139627095 1250 139625845 139625887
    0xc020106030809040504050a05060f0402010201150b0307080406020405060d0905061303080f07030603141b030c0d031d03030a0207080115140603040317070207081c05040506181005 79
    0x40000d020203400c540e1051680d001d08805140602e507114001800d102c1c1c10010540c40d1a041002d848044c00e092005950002c011142a40903600b031040301141e21303816110324802c50700741d03603c01420364440c40011541084003030300c03e840880e003c0c000403410340c0d20b060040c12050b0040800017a044034501e4180c2c24948010500081e04006d08002c101003a001141594811b50b030400454280e0740b10b42c1d00394020402c9410142501d041482c1c48141700100060f0703807005144043c03911030303294282001c06a480c07680410340c40e00044441550380009001f07112000c58008164000840290440c2c0460f1440e08024030840059009130341c00c20114800780f0400c910031030109102c1c07594a052405c40301c1d01e20744407420140034910000000382450b01c41c0710404880181c0e41c1ea00027081c200820025581d83e00c500500444d8000c2c64448814095900020801c3c0c980035211182030902d070000b004650340041c42c0a07041c10104400760000c584c0d071882c84904011031031301c510380c0303506040010020759040a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 139628345 1250 139627095 139627097
    0xc070c0f080a1410020403080403110f031009060b0d050607080a0504020607020105030402010c1718030c18060316060504090c050a09180f0e011a0603010608010303200d02100c 77
    0x1100c050000000c003040c0d2440b101c0d0080001c0745242d40d022905480d080c05030714100100c030701c013003004010403030410b001704201e03406610071015500c0c2050411403450500c2c20700d540e15501c81203804500200d03079001280850302418001804a00110100ba100441e0041c00c64442d0081002c20004a8200508a81101440c80d08001c946000d6020a055100d810f81c068140000807000404581c800c01c0303035240260344804074030014441e2500c030741c01c81d4110406000d0101d025080e0340360a4200050107400340500104280b054000d03110343c5901411000d0245505400b5149200d441700b2600c100d40c800819031079840c2c9580c1c62a0162500032a050505903c0c20071100f0810448016400560071050702c2c848000054400d805c4520b480041181e4038003d2603039414014815403040065100051801245039061803104c1c0c28410046141f009009201c040381155005101103445524105190503080420214443c2c588030041d1904404515000040c0d100c101c4580c125a224020704042c5901c0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 139629595 1250 139628345 139628369
    0x50c090907090807180e1b040513030507020603060409050307031206050109031a251106180a06050c16051e0601060905040b150a02070609050d030f0c0213050c070c 72
    0x2000074184e100d40300e03440703803030404400500c041d50550003681c0202452040e420403100d41c040b0028a20660040c24144588514074210000768002001b16140705540e500d6a1280d140a04680c02c005e60b80d00090030454201d0780c1d5400c040d0014804000070400309010b0346400307540b2181000c00400340e9115810540c100a80c00c802000040d100d141d00c0b0f58140e000b0403107559281d03940c2c04550b8003100079040303041d44400c071034954200070303078220300300b0b40c50300a204050303c102c1d40d00c1a00c3c041e03518034132507888440ea61268000700d021a03810703406141c02580c00c1210070b16180c5140f031080280c1c180f460099800b038100c0c0c0304410000320011320009031141c40c0c0d00034202075850520003030182f0040d8455180520b40758132030552150385035808000034542c01d0421944420860710000d644e0140741c011140071544904000c2075900c0c00050b03440c0301d15850b5841d101d0a804c1000e04a81403010b4540407a00a03940c508046444403090089a01c6204034400d21500d03429541007031646c59003298031910001e21 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 139630845 1250 139629595 139629599
    0x1701060503120f070f021302040303030e0304080d08040f15020c010e0c030d031104030b04030206190207080a03110d05010e07020c09010302030c0d0f080f031605030609012601050c09090709 83
    0xa098010342d40f03e4000c030034800307441d41d4040c03c00d8030b040412194000e5010340704000030903400290b07501a2007920700035541040420742c015180c0e0317507038071490207050590362142d14620162442074042d254041e101d420741080c3c4c408183c2e52056284559180c0055040d004201010201c1007440750071200c8540c003008050b510a164042622410304900400030540c42c0c2c01d0703210060300508200d400560344451700700365a00e80ba003402911014141c803d000355404080d0007004006160003620444c40c0c00483c80ca18041206a054008005811070700c401f03c0700a000c011104d00701e0380b01c3d4074024280a001104180741c540402400d003440c12b003a80e445205010014400344e01d00181d000482d190540e0304800c0245141420b000002c0055002060762900254464003144440d000c0d40c0038841450400b1804c104d0a0b10903034a80c0812038250360480c030a1001003008005480c05921911032000486204200c5854407601390f82c0200c4030703503105000c0042d03201c00504000c0e03111540300300c4502c3c1c2010b80724 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 139632095 1250 139630845 139630873
    0x408150c070317070302071509021801030b0c032809020a0618140607050d020a0c050607081c0f230c0403020109060305041e0b09060709080a080f12011701060503 71
    0x90f040490960a00c0c00f003000510079038080d07030488250b140c001403000d44030f050085030000030385540c0004038001c140c000c4d410030329181e0124500c0c0c141c03580980c40c520f030b03a40d4041d0465500c1d003004090405c900c81b0707001011031000070912200d030340311440b135800b10300d440c52030050200030700460f8030000800c000e1181005c241c91400d40948203442c00700200114032142040054420300500c040500907006c7c0801c4ae099107500054000141440398008503025907031001005900d008058010346191000c0040741c040401c0400380194642c0305440014070b10030403d03542d10440b0340c1403000c100c3d00b1804060700b191841001c0b2040354440d050041c11407515013580e000906140072841000185610341001c0382c1046400000b407a000c02c0c0c0d00041d40310740ca45034108061081400d030740b16881c6028030408162980d2040031981d0681380d60030014403015076943e4401c0210740c012290340c500746000f840304010320340c444800c4070b0003050380802403580d41c500003030601d0031583c45901c228820341c001c25903400b6503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 139633345 1250 139632095 139632107
    0x601110c0d0f0204020c070e01061b020d03120c1206080d05160c03020301020703030b01271205030f0a021c300b03010e0303070306080105010302030303040210050f0408150c0703 78
    0x40401651007101000007031400e00c031108400c8000075071260000c2005205031000181d51401c032042c0c003140c0c00c5941d03a40c190a8a00d48800206103241c0080c5084080150a0008031280307054860f190595411348418510b2040701c0c55202100300064a01e04048658402d502034180034080c440c000d4a100c910350103001e082481082d112140102d10801c014007800105401c0100071070f0007070001d542e01e030203d15005000344280c449141c08220410f125982209a40c6050b500c6201000c0d1041c188074103010a410400025200031615484200035409001000102038101003099400038190701040041c004040c01e000074a502c100214203036940403480c484103001e0360341845500d04000c00311300d068802c1d01502c030407110903406601b480c80610400500000551055801c0ea030108081d83e16807035481d09a81c0d00f848007a60562040c4041005440e02e402a81182019400c040d4a40420341c040b404a41d0002d510405054002da40407158904d40c08520940c402280c2d844946060700f6a034015001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 139634595 1250 139633345 139633363
    0x60f01060807050d020f03040605130c0509060609180105100f050a08100914070318020102101a0d0803011a091e01030e0111030907090905031206150f030a05060111 72
    0x4205003140801d10542c0030f00200c0744040c9401c0c80540d5507002804e00b200c1c0e190710a440c1102c6203442d10000500c001e0100e80d01803584d036442020070101d0b0b841e0008020b6044c9000d065036901030704c2001000707407540d1401c0700c0c20200c45040000c552958035100800c010303201c014807240244050780c080d0800b441d51110449001c0003813170070142c000c1c0c4c803658584100d03d2100e400c850382c41841c0c03001031080b01c1420f2703850a00c00d5915540921558680041004274482030300c0b40240580c1c8964210303e4450f28581000840b03500c90402070303290620180c005041c84038002da0030350300008008014080d02d42c1c9038801d80000e0756200312540c03520f16403d02050102030051401c0c0c2c0c81c48031101010405038840d4200520b110042002400303000c01c1e25210002562064962480901c54084002411942d41c050001c60540110141d8102110309002d2484180c005244642c09044024588400340080700030b840d04004d2881e07c0742e140d28108d0881c604543c0003401d5079050101c0c01030040510200024034600c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 139635845 1250 139634595 139634597
    0x90c06030513200901080312090102090102190f050d09030515220201020109080316030f0b01090e0c0403080a0309060b12060a0207030201020d1b0f0c020105162406050a08060f0106 79
    0x108400c000f00f48900354405019490f41d100d10342d00c1c00000c019000101034509040515180310203515a0b014080c03c0b8810200141d025030021ba042e07007105041a000e5400f0a801080c6003454002155a424146011250b500004c03c801e0036080c0b0a001c410060303800c200c840b6590140050501502c44000d05c032200c5403040b07030715034003060031011640700f0740203c1740403030b80925482e03103e0401e9440d03003914012802c80d04000a25080625458903410f000d40c0c0d06411041c0c43e19003105041040000e4140d500400908402808201c008005010743d8010801c0840e0303551b0009090045107069420384400740c00e050304c600305240c0408021140466030f01d0f00701d4400c0c44010303582d140354a02a40a8015040310794041c03450090b40c00c141d40c1c0c13130444048001c1c03400d5882996880d5090400c0e18a190395100280c0010810f000f4003110350102c0d02d5224000c1d00442d502d0702d000301c24140342ca07100c072800400c7c68078054a03400b04000b81d080200800000e4400f84026100c3e5182282d00c889002c201481104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 139637095 1250 139635845 139635863
    0x306031511070b0736090203060102150a06050108090c030735060f0702120f090103090203030319060b0702060924040e04030206010b0403080d050a06050d06090c06030513 75
    0x5031040d0a0340088840300c2e40d012461071110310700490050700e03040e05d4100005440060f0780d45068241d800c0ca0380039581c0140c2c2e0b441000c01d90b041102e543c00070742000708141d0642c8505240d41c080403000c4c04425104840000c0007048503420b1400040041801800484482e4002c04030500c1302e076000310b640d40030b88040c0541c891002eaa4075158151040b0b43d1008802c0300c00900988003c62280403034251302c01d141e0342914020030780741d00c1c074226030f01c054107404eaa501e9070044c40b484818030460f10081284540502d000b06090425400090445c0d02c10f0711900d5011500c184400421440c1c1e0203440024aa00c500b4030307062640b190081041d0340300f400725452050741604182e01d440ea8920b40030846540c04001500c0c1c4807034175007010207510315007a6000d03005486990b0000a0580c0f4a400b100c007038950180c0c1903410304550246d072002414014220320000f985803940032803a0b85640c40100d01007030081802140107180e50400305241c1050360803044c209818401000401c0402e8003c0a14080c1c0c404524 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 139638345 1250 139637095 139637111
    0xc01061205100c030f1817070c14030307080313110613050108040f06060303080405071505070b090c1c0201030f06030807140102040b07080405030115081213030804030803011503060315 81
    0x84008110b080403041c0c0e01880d200c0d049204030100010460340e075203d00c005520070802c7c449202c80501602c440100f0400b56a0b60501c40c00000d403500c03805000c0094110390a041c2250340c0c1140d150411184880d009081c06268014804100d44001107208180c40c0039160070280c000c00480c1c41c0c03003130203800c1c140503000c0046030401141c2d084070b5840c01d4009204005a0307480c2e1600805a940a40c2d040d28a03104091021a01200440c0d610304000b1030703900d440749851100d40d6020003079140145001e4890090107540c0000791251141711030040703034510103202c03603039050701c0050b049a940040d181840e6190810078400100e121003100c0d100c079000000c03441e480082e00c1900d4064400d5400c070643c448400304030481041400c0700500241c401c124000e00c2140d03014280c00b400d003050b911421100768001701d840350000d9900d0b001030000c01c4008110403e059100e071100e800582c824ac1c1701315200b42d400001040442c1008450040e00801d81c902400703002c2c038540b20380400ca1aa544075204080c4d482141c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 139639595 1250 139638345 139638347
    0x705030d020408010204050901080f19140706051b0c030304051203041509050406060c02030c010e010e061606050f0123011b0b061003110412260c01061205100c 70
    0x203440c00203035502410340d56141c49941460103500984911801000c071180007207240d48011640d2802c5210f26402844003041c0b00040240d040c00c40310f81076402c0340d0b50a0300311000000612842d80500203e4503025a500008811640e050082040d07903100d9030000c1240d0740140e6004401c850444030304494841020340004d03805070a41c070699000f0f0001852800a810340160000c0800e001c64070116000c103e503c2d52130070180c03950820380c08025890340029003070170000d6005190141071400d0602d0502c01290009000c0f50307155105001000b100c1c1200e4940a003004040d01455078003800052180ba1607500d0074139801d03400c054403411042802c24288003045d59911030030500c440711100c0078481e0300c210200d05002e00e00003400d0315610f014042a40350421014001e00410030002c150340f079040e1410385800c1c4415100b01c03038054100d40d4440510400342c0900001c0c41030640e01c0c0e25a1401d2a035981c3d10790007050031185154841d0302c125803c1d410000126401003001100c10201c0c0304041001808140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 139640845 1250 139639595 139639597
    0x50f42060f0c060103020a0e01060e0120030d050402030d0c02010804150f1b08010803030105010c1127090d090b0f181f031802090c070602070c06110c010305040b0606070503 76
    0x10000c6040000850b507040341a01c0020043d040f28026035810303101035228130020803121001d008c2c5001180200000f05080e500c2070043c80301a000c480c4208481c1520031400504580c048507440341340d1a107d9003800150300d0144200c110030178103401c0c5121420f40d69400038000080040000d40040c44660139080d030042030740c00951419054480420140c180b0b40c1b100702c10005074045000c0021402c4e0004105204000304883c10b076503058642103442051655030014034407640d041c9a03004400d4044003443c00d240c6004881ca100d04408080c45145407598540b880d010740c10f12444100b20321003004101100302c09040314014490400c18503564000d41c500118540000b0700c80c1604050301481092000b00449904020040b0b2558217000c0a89521b040201150038004082d42c05025000030400d020b034504000c0c050f21744035103c0941090240c2c0c4030581420810303440100401c4803120380c000507010038030044d26030100900342048181000d80b12071b1940385c03004040306e0155200180000510034100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 139642095 1250 139640845 139640857
    0xf0a150e0303181009051801241e0905030109060603050d05030708060609030f060c130927020a0b1c1407080a1e06090c0206160c0308060a0306050f4206 67
    0x185c401001d001f0901c007100d13281c1c81d0034490745800c500c414010040740b40407089100c42c1542555240c141c82e41d485180b0352454a040c00645060110b910300000c1c060311300b0b0140c5a1004d00884e000114280746042050400700c0120030f2a0410008008005240e6004a0866009030058411988406070b280c0846e1404024030300b00c3c203444c442c0e20b0400a225809030000c11352103800b44249030138542c0d00ca08240564100c20140107160000f001c0c0403083e0070b003071045010580d000401005000340d49000200c6641e01c00c4203496603903404c8800c072842010f001d0099200236080490700b143c3c6460607013801008034078040c09200d40704c1c3e1103540341c041940440740c0d8002505040c00c002c008c5a40d6800ca03000040000d100340300f001d8040c10002988101144490b00805000b5444d14020429566421a000b2200070200d640c40a061f41012010843c20f200f524450010740d00046240d06051991400382054901042025a20035141c490a1100400032071080c601c0303c2d00c640c0780d0300340711030000700716020703032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 139643345 1250 139642095 139642099
    0x2071a09090f04290a02070512030405010603060c091410020309040c0302071b08150a020f0a11161a070609020907021c0503010605180f0a150e030318100905 69
    0x6106009015a6540b041d5002e18440c2400a90403030800c42da0f08414820b02540b032421501100009091800903001044007a00ca8002e80d09200b0a200844005410589060320242e65401d030603c00c003c03c03807281c03c4c0c001d503032803c110b4042d40c41c0c43c60303e841010b441040940160108201c2c407100328020010794058402c018402d00013041e41100040094021340300075241222000600c0415030307100407903c01a50481c0e009440405400c100c8078282101c060800b0306803990810500c82c203074000c03d015103103c4641c0c0d81c2d40e96480c004501a503191000b5504010003102d00040200030350400006130905040d00028440d80302c240905115005169050020b034006040c10200a1026030100300d110003054226203000f075180c035881048803540801d00605005c20300400c43c01010b406c8405810091440c02813810a80032141c0000c14000311503a030001c8024000b4604040740a40c204280300e000a0094005508100c05422054200c090a4010a0191220740aa156404e101c2d4407000060140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 139644595 1250 139643345 139643359
    0x1c08090705090a0e1029060901050a081b03070801080f0705030304060c030c0807050f24010501320319140f1b03040b07110102090d080d090b0c04170d02071a09 70
    0x46d06603c0f56030340888070584020510b82d611119107000800d03030781e0302036042c3c2d102401c00440200541ba044406401c1114070040f03102021900002c40000b1407089400740c1c2e03034181700e501d4074541920780f8413551201c0080f90070180d014070041d100041079900721405490b151410442030b040c182c448112002d00604491800602401407200000e51590000801ca080700c05600c070800900c0c00319002501c81010941a440042040303600c9186c060140041c4002c006807604065195008401040001800c0d10803012003081490074a00303c40000568a1a40a2100440e481d02d08600b044004204070007000c0c444001c640b00d030001000820041da11307001d0903980c90500c1e080c88082c0c42005c4918500040032505c0c0302448003018000c1e2554150091f1607444000c6899603404a5a005407082d0242c26644840c000c01051204001900440c0801020b60340c990420a07283c5c0302406080c04a030603580018203031030344c156000540e2022240724401c601c1c041100a10b0f0104c1c2d521401c02030503070090f0703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 139645845 1250 139644595 139644611
    0x90a20040801090c0b0f1909091805071502031e0c030403080702040b0105120f040516060305010f090912030207020f060403030806090609010b1b0a051c08090705090a0e10 75
    0x7a056002e000000e00030301d02e15801a0351501d00d04428803902d400003810804c180205134003a40580a01654600203090403000103840300c10302c5d0300f1151881c1003041001c00311240c0900344007040c05114041c202008859800c002d420f0b4000e9900c2c8a034900740c04446040d00c0d200d5440707490003416141d0703415450081d290ba5654a0504003e0380d0000e0505a10035032038009103448a42c0514103d4006c0c24812200038031590b41d44c940440c580c4001081a9441c0c0115810801c445040c8900c03000901403d4500048550404014086202d06038101495582c40c01c82848082124101c0017000d0000c81d10303003d40e486043d44041800b072444c643e42c05130003803004540401090b400c40c855501c17602c000d441c20141c0e5a40d40d000c11104030400c4c45884100f21041002143c6150b282055140c90700b118002c450910596684540c9414844030480800c840071f4503140b8030856102424a420041460050800d50b0920300003800c0703900064141c800305542c845094155030403d00a40b10614070392001040f41171 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 139647095 1250 139645845 139645859
    0x60f060a1b06060816171f1e0e0706090503010b090f071205100501030c020d09061206050907170a0515010e2e020c0301141f0305010f0920090a2004 65
    0x17030814000c14a0048894412002850000507042c80c0c40030800c021003100f20101c00c00c41e00030580c42000d5440801d00c0c400c1081a0f851500501050504280050503c3e52900100030118141c07600703c248642d041c40c08500840d95101c0044e81c000b42c181d400c3d131045841300c000a8505d0300040c003030021a60304002c10032420245540c0b540c2c040380c500303032010310031101503c000701e031154140d1b041d050104800c0d01040c002c0030310800341101d9100c240e0100207031440d104e00000360805000c03505580010041740c80619520031588c01260071000b4010240a03a0500030502d0070b0314412b0341821410041680340042d083c0d6155000d0100404440e04074a4002500c00c05a2142885040215003d8803410f8506680741c03c0521662440850080d9025104c1c2c5408a400842c152844030303411028001d60b00c007001290b000c0c070841c80b19940411000401545502c0c144644244600c0c07941041081d031720300300c41c00384c5a81244690154500500207040003620104a110658a80914882020129000c1144 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 139648345 1250 139647095 139647133
    0x1e070201060e07020604020a0b030c04090204080102130501181503021b0109030216031104050a022214040b030a150204170f01110306010c0323030708060f060a1b060608 74
    0x10321000c0d48200d0b8030340d41c1d10300240d035141d605541c004d40110b1301000400034220341c0009503402c480078841c45460300b03555261200907a0402d401100710340c0d5001a501050041d10744d0400e0043c0001e00f84061103810191140030000400c1c8078009030500e0003d0380c1c1e07020922940c100c60741a401b0049040c201041001694004d00c2c2ca0720b0218098440c5008007094800c500e4002c40031240d028641e45108024841448050500a0050361500e81c0a2148240c00b90204a0542d03400300300d074000034042071520050925a81c0d0301045103001d40d1a0034485a425100494081b01d0280c11107801401000854070300802803055a028082c031b010000500400c4081c041903402403415040000d001c1000d0301c034800b04051000380c0c0c2030350200e15006aa070340041e000d6502e03035011441c92201c1c18600000120000d0056000b10b036100d00040d5078008220f218a003032040c02c3c411341000d03150304d418054003020113000700c01903841015420316524040000c01015801c0320001d40903580903511001b000d070080f1202 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 139649595 1250 139648345 139648349
    0x20307090f02090310111617040612050a090b01050420130905090f0d110708010c0504050111070317090d17090111010b01050301030303020a020f0d0509010e0303070f0b1e07020106 79
    0x4c41c0c0580e20108400e10030502a1030540701004540a1424002c91803034510102810302c219140109029010030010344103010300000c2c0b80c11380b40c42e4903482c3e02070404000c40e071009000704985482d1a0040c1c010440b0300460718150340007070b07500050f010484800b2001c000d0205035410703441c050001c7d411130711490b40103e02044a8014100b1b10580d02c41c41145032700c85d881c0c5640141d0303503844180c11f076540c00c0c41030002442c6424148155009644c90b02241c0d400c0d114101800804501c00080801c072a591000640000e580040c0290402a05580c0d13610400b21403003850040111000c54605a203680340c503a1524815030105005040d0b10072460403e525070004401c0b2408207042040701d461b40c11042c090b48070b180105a41f428616801c6a03400d40080d0000f01030b5a0842c49602c001c0c1e100041d040018243d03600c0703151200740c3c03100c1c07440000402c41d100450805000360400e2203030000107030700440c02840c490350100c40500c3e15a92040404140041505c100301c4d401901340a01843c2c0d5010741c40310f81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 139650845 1250 139649595 139649599
    0xf031b030b010e040501080a020402030423010504020f060a0f050a030b030303010e0109141303050a0504030609050a0b090705450a0516080a0903140a1d120a0f020307090f0209 77
    0x91543d218100012141c3c01d104103000c603046200a40014a8070364019640140f0030f050300d5600c10440c440025a4003241c0c0400c1c202690340794240f1040d45056240c40d03250300f07000c070350303603447d03c401500001c0a0300c01921800080c02004102d900445000742c01400b981c0c140901200d480c0d6a490406140c490020700c6400300c032601e0120b00e45802e4130b4000d00d60344a010300a41d0032216078840d940c00c64641e40101c07600800c2007401d1001000003081402001d00c500e002d00c1c020441c5010741d0a1010102e01c024240a40503402424104002e448000e40b44114041903174540d4440885001d402005c0320342c218640c1291603045804130000050822102d01944118000308a241d4441001450a00c425800361020402c0b0000103600501e480d007280c8407141c82841e0040d071000c010841015550840c0301000042041d00d522041195140540210620300448419056000c07440726180c4403604c44a02802841c03101d4141c0083d52010088400100400ca004200c620b0744401808000d41000400b94 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 139652095 1250 139650845 139650857
    0x30f0f03040920040b0f07020405182a0d05030f030907030c0807050f130f05010801020c060f0411010f0e09010612050f10050613180c11070f060f031b030b01 69
    0x783c4003162001e91a0210f0f07200000c0600e001c0c00d0004a03626504402c21803480c2c020104030490040e1198016103000300241e208051226101103021410418810b011200400c0007061584440c4030b241201c01d40f442055804694018090510034154494498280c4104a0000c1804004031000400c2001c0703030b001da440400e06640300d0400769256580d03071141583c4a050b9003203c03005860045082c03601489480d80000c2c0503e45081a002078840c00d0303012201596004ca0b6410014005121070307503106010000000b00d0b40303065502c011040000c9120241004204000800558010305041c2d81c05200180f64040c41c0d84d450500800c04088406c80014580c10200403400d99101101140d00980101c07208628007030400060281c580c01100d0706201c1c1d0511004001111052074400c0c09140124143c003140da5056588058100708044400140590022104210400522024000396081d514001024004c4104200c0c00342c8841d0307041482c01804000d024401075050750040000e00008c1e03c480c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 139653345 1250 139652095 139652111
    0x302060901020301030521090301150501141914070506010f050109060e0a031b030206030109050105041407140d0608100c0807050703020a020d060221091b010509090402030f0f030409 80
    0x2420b0340004e01c0700911a62000701400b035450204000300320902c0303840761030900304415000001d0a642c0c0c0071001c3c252540b9503010030310255038000c0d44000b07a402804080c0b403030510014418040518138803140001c01c0034540040c9107401444003284c41c096001411507085503120361540002d514a03200b6280410002c840010380c82d4001c030346092031200d00401c0301c0880c91070368859026004424030303154050700e46001c0101c0141e6961006e10b01914a15000103840e6050100b0f0004079a00d000601050304114000c0221050703000945110803910440300b1070b1903000040110028000070b0f080a2036a00851003202012144c0303620500b254485030751139100c1c1e034070703461400d5415102d00440070b001a00400201800b50034000c41030350140c2c0c8542c0d40189085c043c3c41d400052105080d200d584c10025180c28805844030820030019411016448886100d01c5000003800500c02d07182040d000310300324800182555400c0c00421181c1500380700380c13002000c50070b018540740e0f801805200c07000d43c640402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 139654595 1250 139653345 139653361
    0x4033306081f0f020a02061005030601082109100f030c03050714070c050a0f060e0a1202040504050a02040203090a031d0306010b0d06180203071b0510110d0216030206 73
    0x282030032a5001d40c003601684030014210b04100c40d4565120741090307260b6001c1000c1440f584003e00006005e0713405440c0c0c40c10320301c103625102c0b00560f2020703201e54000401880780070002325000c0c15540c440e41c100c00403d4031102044825000d45110541d11000c403650041d845908100d60b2a4208281e031380c1040851034058040d02210310650700708000400d5048100501c12405000b009401d014094440e0358641d0303040001d81080c11a04445d1414200c4002007026a411810b18180c9a1048607502c034510b08100071400510300e202c6019204035200c0b000700d03050041c1401144070498000d0411355a034601a20a66070342c960191040300000c0081d400314038075000c04840b42c040040028040c22040e4600458582c15420020f40705c80c00a039256400504900c0c50882000021640c80001d41c0742e00d030031000a0b10000007540031080e89800f07a6443e80c0020800705640d82c0028201100241080c4540c1101446002e584c00100c0b4861000031500c035114141650040707498400c0c0e0032103420b96210300b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 139655845 1250 139654595 139654601
    0x318030b01051003060f0b0a18060203070f02060702030106170c042915040608040b0106020d0e0103050c120a02040e06010c080a03050712050a0b03061e040206090105040333 76
    0x8006004105208010b00941c039102c06241c00003516403401044458031004a9420301c0003d41c40780200c1e2400040d001c0f141c50b0483c403550b04095208480045152078240f000e0744900c1865401007041142c1e088040841d82e465080d20140f0340c010f1700800005d80c4410308034844800155108016114030b103280c00443c5814002c6016040070804440b0501103800000707201c1594140300c09910007030080c0030000c0c2c00384020142c00100f0030350b6121b485a0401e800c1c84285060b068011030b0840d04195a5620f05541100462515403c04e10f0b000906540d15800c010850245010942c211007152040c040788030360940180003913a820308100c21036a22070038019686040e11305001010305400740203884156000e40d000c40d620070a24103003c500414801c40800071280219010081d85a440d20384507050300b02000095400011080c0c0081180c40c194044003842000400003845144006800c50b0140d100e2010740d8001c541c03204031444084007100710248c54000d41d1007000c2c21121112195281007440380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 139657095 1250 139655845 139655849
    0x1407170d0c060e030408030a030209040b0901050d030f0207090e03180303090904060c02150403080a0e03160b0a090609030c0501050c0412060c030b120c0a0b04080712051c08040318 79
    0x41c941c800c1d00d01e115903800303014040200100b04940001d00c0005251281440103140e4035041c1da90060791140b4188c2003008491414052a01840760b40c801070007261502e9188400054040c10154106405044100d160030780d02e412031071070b840c1810314109081d035002024104008846500d0103485900400341940d0b07000340c21041ea844618800800c01003810b43e80400c1c8900c8541c810f84400900e5400480450202902e08500141e0700400300191701071548940b09000c000b10018500e4144420560001e0036049038000e4060741d41d000c0460000c4100d5800380314599800081032108030f00505028004144494007074609500700400600c00c85a000200e41c25501036000c0c481c4080030782d807248030003040e240c0440400d16507114445800b603915840b1040d0600c02c86030007400200d15820038010741288681c4407000d0b206060005000003c004184607094510b1b50380a08039194003803c20b41e02d000c5200648004404c2c1e0602c401c80300e590310010003403083d070090319103c80c869000c810a910401c641c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 139658345 1250 139657095 139657097
    0x3060105090118080304031104051005030c010f0e0d0b090d050c07031203021c020301051503091023070e09011203081504091b0302150c070b0d0204031407170d 70
    0xc210311201c0b036024103500f009a03002c600c01610001d0310b40040130300c0e69025400989616510051014251404e8051070783d000d5405808840001c0c50b003c0802d40d9501420040c6040c41000c403251224203105208040d40000000d14a480f01c0040d4102508204c4040c1d91141440c00b400c1c0c0603d90150160307003110040180c2100500c841e500e103071180d070038801c0c4c00c86511007019000c20903d80ca8800201001c111800c110340c0069980d45442d040144562901c49540800001482001100000820310000d40318140d80d0100e064051412202210b082e80d042590310214100240b03d1003a030b001e6048585100161020101a600c4850200c868440c1081c01400940c0c202c0002e1203100c0201803084032010007900203e86921999264102c03604510304040510401c02002c005601c0c01000058040c1c14000136603140003014070b4010b80381c0040b4040c2c068400b20000d08005408401d038100e4006640241902c080040424801c03500e4508a10442d24100108800c0101842e404138000c810042a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 139659595 1250 139658345 139658347
    0x6020d090501140c01021c180206070f060b1012140f04140705030a1a06040902060711030a060e0c0a0801060b0d0e07090e06010e0a050c040b0702191403010f0203060105 74
    0xe0a001124516010f4040c0400042c0501006400c03141c00d001074a2561042560350725910620040c0380d017150906080c1c14482c0c19010031400145c0c9424044521268110a08c440041c1241c10040094100000300680000184001881a503403107040d8483c038900048080c031032210708034641007100206441489500d003415010500007480c0c440d4403190394108100b501c140e290382d58006400c0c100b10850548031090301d4070010038807850341c1c000c05503c81401c80d4100038401098000c24914080c020340241240803031841c0500580d0104440400c00e5888041404182d0345002d174a40c441d40f013100600d00076105074002081d840b00601901c0706880708118130f0f5003040581e4210710084d00829140c41031a0180f40f4012a1124260140000c0800303020000c0489501d401210031820100a0104504a24000900c1800d12800c0b0407901140c50680020307407a2041400065844604031941207007214800d400000d40c42c9404082d0320030310004030000c100750a132035100181a0300c400c13a005800500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 139660845 1250 139659595 139659599
    0x31b06120b010c021309030305062b060b0910080c09040803240a0305030a02070602150a02092107150507020a06050c0f120d0605040c090306020c0f0604140706020d09 73
    0x19035038400140100140b4001d40c1c0d2503000d40200d12511507100b41542001c2d03c0d440340406041e058091187c10070001d0b90f001c09540e850641d02d80e071200b03804c69011600002840b0750014444107400240d20200009c0460741c15080413a01c0414510f0548915a020b00659000071814075040c401548207a41098083e131840c0c0d81d800510508040032804160f94001e00d40700d5002c1c81c2c4030201c1c43c1d4041d5100700001c2da0f03168200c0d00b0180c50314006078005411540300d0291008400700540f600340d00b1000d501400340c3c0780d80440c00041c4084006400c2c081c018601c940e803c404c0208000b98034021940d0380040c031010400c0c00b0740d040710030384290708007c2c0d040502c00e403040040c82c0c407800c024200c22f4401e070190f40c1000c10a031300f00360502e565501c08040e20300b804201440800524800d4000912003100d081140d5042d01102a00b401150720010b08141d5020034200101142486240001c1600c5070039141e01b49001c3c60411092612107511011521480340d0220f070450001a16121001890700c508800718 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 139662095 1250 139660845 139660877
    0x2030601020712080705060c0a0c0308060a0b0724060807120515071115070815150406020703060605040203010b030a02030c040302220c08060d02011107080304030c031b06 75
    0x151025022034110701c00e0540014805810300c0950340f8452140d42081d61314042424194503004028121899441c03040141c1030805410850103c042e541c10f0030404201c1d80c80304000303283e40d87c859200702e0340904000303510010000886400082503e4510745040719800d429901c80481e0014044e04038643d0181c1c0090142d08000307001d81100501c0790007114008441001c0804c055081a110000481c46044560b000c0ea1010301607885400c007201c85880c403511300100c00428004010348894000c034140513507486aa20380740c60080e220201184519611070359108000d641d03403800d00c03081da40d41d40740010200391850580200c9040381c10000100d801c64482c445144003d5001520303521103100c0402002005071124080c075030b001c120b03a0340707442c9500c1880c00616082d1000b070f201140030040f03610100700340f40c3e0740c55505d062056020700e41010603481824880389040b0841d00840098403011500204004090040e8010b6034480c8034046004100e658040c19110820300800c0e010849580c0c18881c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 139663345 1250 139662095 139662097
    0x30f050601050913020d060308041d060d03260117070504022b0b1c061526030714010501031703040305040e09010f0507020f010614030709020318030a03060303080601020c0108060402 80
    0x20302c01302000516200c13412030124120390f565032044038041c10104042100c003800050305c0781456414503102c0a6842c202e0b00103460104d0b40340c00241805071141080b100d030841240e40782d904c190b000c180030740380d0350310781c0c4c0107915003901200840b04c42e02c540100820b040c2402d000b651030404002e048030140c00d2200001c3c2508904000b04000b68581d14094107a00d5a81c1e4404104402036aa000c0c036060700003810010180d070311000d07000c0303410b41c0a20400c000c0580900307031000030515981c001c484e80c54554101c5909500c90900b002c1c15003106110751855110044d84158122071203040380d041c84040708260305030a800100c9014001c40e40511040088000c1d142c6003a40c444110000000c1809280013850100ca1007038501400680c84085c031154001001d00c01c41b00540005036012194130580320000741e88050358040d080060781c020010502c0e0803c100340c9007010400071001d0f00d848240001b402402040584416030004042d030012551075400490164550a810ba540311078aaa0302070910001e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 139664595 1250 139663345 139663369
    0x2a2a0d02151e0708030105040c050306031b0d0506010905071106191a091e09160b09030109050d0c031206150e060c0a03110d0203161515090c030f0506010509 69
    0x401160310501c0c0b030390034a59600400c1002e2040002d95100d50500040c00103d843c19010b07071041c450108140b0000360313800180c00c99031480d4a01c0c0202200241008184084020700c40105144614030000c202c0413102d42010f407280c401c0d0b03552481d000a00e01c003800d030340780e50543c1c2c2807241008a030384400e08200c44e5001801149409003100664030300d07110109086200c201c3d801ca07800300c030007541d4005d84079040d60400d07013080b4103000510b41d40c403d001030140800094071410352911800100c1024948081d008038448a41000030b90b40240e052031406010b4101c00c40d0124000742050310000e0004c4040e1140301c00396a040000f030706134814000002d031201c0516a0006600890034084540700c5034003003041c02c0d1a64400d86d02ca203000d5617440242480e05da03017200e07001c0a43d001400380505022888400b01c15130b0307400080d00f2118400c0a501e40e8010549041041c5908030607803c04201058944c00002c034244040c2d40030065555a0412038040340c6003540e42c580003420401900300107140109959030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 139665845 1250 139664595 139664617
    0x52103011406040b04060f0f030c050f09040605030a080d1112060603090a050313061106040203030306090a060801020f03150108010612020f0d180311010902062a2a0d0215 75
    0x1142130f0319240c41d040b0a801c168400303070002c1c1c0c1848070b41540325804210080c01900506090000a01008015100b4000e106540615000101310582245d544e0741000c1300400c0081c080d030381031020a003020303206580083c1d0310000d601c1c101255452500e01a2003110307040d034110380c190451600c1c1c00c0c1c100000b0303602c0600071045911403902d80c4404240b06100400444440e55841c003800c3d40b5140018120700c002481c4061560899020400583c401100b203036400801107034203001d155540f0300000d004150310b40005d00c2c17561001c51041070803072200f0011030003124881090420700c85500011100400700340991000640f032260b04111081458014101d044111008141000d0713030504090300703c82d040c0211880308461101000c0c107140e0000701901110b44944001d12424107140c0100b4603074850380390164007006200074002c03000240d030262055544c0c8020144c03501c4240490601e04801e062045601d02e90300306d40004202490300700c443c0d8171043d0740070340208041d0000d02c0340b4006580003054201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 139667095 1250 139665845 139665847
    0x3090501090203060114011b120c02190b12010e04050a0809030c0d051501330c0f0605040212030703020a021018030b011e060e090402130603080304052103011406 71
    0x2000503a0b050000c0f178007a1510b610703a000201d00c038000040c00c2001c81140b041c100f404200e8440d010481301e00c0100ca507400582013070341c8088564400b05880c1c00c101c17010030010044203500130407402c0035800180303036040d40413508020627600d035000f072082c2d81000c3c0c40041ca290320040e014800a403040300078101c08580107080d00d4030141040040b0390118a0a482258142c2128050b0f41803400854482805810010070309450090b01c0c10000c0c00c6c0800c000380c0c52440f48500144c00600912560181140310760005000303c4d11010791a011002c5c03c826070b0104e11407008490b1600781a0000800c1c0d0346e9558041e40104402c2916400307000f203010300d040b0b02e0010405001d203180d0811020700c03003100003180302d584070240039894415001b055800d04481c2e02c901c02200c01c02000341c151710580a990f401003c0354040d24903140c0e80300041e00c84601c00c0139225000d041071000070a001a1401a51081d401441540e80340741480d080c002c03a5600c48490709140520900040c0401c80350880754070341e070788805401a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 139668345 1250 139667095 139667111
    0x101d0f0c040902040620030301032006040b0f070c0524070c1d1501030507080402010f020c030607050a0206060f06030f0a091502041508010e19090f0606061d0a050103090501 76
    0x40c0c403eaa105401c010007190700100c0000100801003560131401809102035811541155104240c0c41c00c03400702c01d01900003910518820755111811280181500c0c2409641c402c41d00ca0b0021880d007100300e041d1410481b40800285030304000781601204017501c018011000414a2203000a40046406696405001d50003050315001e0102440b4050001003c1000514210700d01e0b0042e00804050b8504141c100401c0c8800241c0140e94543c100d6824246219210380c0d00030308901d49941980a240d041c0b040b01c05000d14160480c0040040d900d0507801c1c1c41840c0c0e64001803015050115007241d80280c810000140c08402c009030058000d030841001041620302038032007003078041440210f18907456001404100d445005825400e80f4603440c1400411985000e00706a071a4000805402e40300345188100300c0c10581d140d001210b0303686d01082035003100c0b81c941440e0703008006501814000c00d812034a5107501c90001c6041d10526400284007000c0a401c0c07400444c041d04944901311441c0d0348421203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 139669595 1250 139668345 139668359
    0x10216060c0f0b07020a0c210308130c0b0a09140604030807080c01110d0606080403020d1b050a15150b0a0513050d0f0c1202030705101b030206101d0f0c04 68
    0x20890203481c1550090481004504054406442e20340c0451031920715608d682003610b000300f85560220340c15081003a11a40c3d01116164980b00d000c7c4000e14003451020080f480002c800060010100306607604903115403900801038180c040580c207581e000e00d00740010000226448010b160051003150b280c2d0074a91951903017825035003803000c06c40240d840880c40c00780084e024401c4600805151030700281a0501e61006900d503000315001004004c250384085000d652841d01020000d5800002c603003201200381401c00e280549029103201d00c609041c441c11900f217840721004107035505061f69031700d0220498800c1d02c05034004460342500b64030300100085c1954840403000380640c080d0150311f05040071032030480300c1d01d8519048400404d003004812005600c00092041c1544c0050358480d520003a407200c203403604455501d001d11381d81e001501c0c4100300356000c12228002e81700741285982840d180d500e0380782c4441c2c800c6401c040d541c50100001d100104a030420300d030040c0380000305624140d100c6c08 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 139670845 1250 139669595 139669613
    0x1104150e0603010c0804110405040507050d0b0f07020f031605010f0e0a0506060102030a091a0922050c0301030305030a0506010c05010c0f020c0a0308040e0702100603061a010216060c0f 81
    0x10000440204a1040102509081c0904e0180502610f4040083e15081c0c0d9000f80328031002c0003880c0500d0759840040c08104040046074007030304009020076000010781c43d10225021040302c08000060030b003004641c030913000240d881443c1c2040ca0180d0704100244440a5030a0360701e01017920950b4a41044112413840b9101d01c00d00c01c040b82c40903200c903400d00e0074414904070001d81b070281154010419681200d900c0360300d05043c1e849080200040c1c1e0f1144e003c88049024060000303030f000c0b442c0d65112001045980340340000c001103040a0115a403070510146890200348030150200e41c08000288010180d5401654046014140805900b909459003800c50301c511078401c02040d55003842d10502a0100300d010303d507800440c0c440b9015415590740d00107e001e50701c1100c0086050402048210780244a0a1640381ea45d04003040340c19a242048405000d40c0b1144200c0ba4414207940d0340154808940e0341c8507c0005550100340390700e004000c44940403501800d90f00016003006100c00504181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 139672095 1250 139670845 139670849
    0xe090709090513120f0905040e01021207110f0a030e01050a170a0204170303090307081c05100e0601020303040c06110a060e03030f1f030b150603040f03080c09090103110415 76
    0x2d2102c2c3e40c8403262a0a18200440001250502134500b46051800e503003d43c02c1c0094690660300071546a05150413503001e40120750204a425034880200041e455004440405108260b01215161540400c203151911909000500011440c0c0420b01e00ca500070001400081001e25002d0101c0c2c400d01d0040601400540b0301942c05030300014104880180c66441ea070f0130001a2001d1865400c0101c46241d46e441680c40040c0740d2200481c0000c0c0101c1442c1411000840f0315030140100c0c9050724400584401502602030124014000306009510000c1540c0c8a560700c004a1046a400c000060704c01140382e1524101921540e020b02d00050018081e0300c202c10055001540c81e810a10800800654010403c40c0003100d030b10054128186000780c05802c59402c6030b0000c02e80d403900b85881a101c0000ea98158002c6000020f000c00c000c020300010359202d000c1da0311302040c0c0c1c4400a0000c034502c504c00c12181c0c445000c1c0c0c0140042403000031103403441000200b00003452048040f26844507540c136 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 139673345 1250 139672095 139672111
    0x10507021815130b0303161707060f0606030c0c060f0612111e01080f0c04050a08030705060c0f0417011b0801060906231806030108010902040f0605010e0907090905 72
    0x102c0700070905040e042180c0c09072921100340610900c004c0401e60342d0081c80e0303d00b121005401c8404050246107074004003d07003d200170440e0340c1d000500380304014003090030f91904501d1038003200103036081c842d1054004140c51030345c41c85040310480d00c42c500035042e43e41ca149422a540da2000414150006290320b03128031847e450a40c4800c01c0c02000303544039101c02480c543d800010300300207180c0c0e40240c90550107140c00700100841c0d15524004030081c00303545c12140c0c12200005000c12601c1000005e00f0000340302c4d00c200c81081d031300c3d1480c9454a000d80c1c0c01c020903a2800784070a1180035280c0c041c080f80c00301c00d1000020b00301d0030046101507840e503105041000c2403030b540042c840641d0022055003d45498200f41c2c5880404420450300084240e41401207440c0120311061800b140141d918000c08000305055100e5845210085c02800c410700c3c202e20640c501640013a220b074a85c0a90000c98005858280d203401042090001c2d5074030081c401000c11200f810007003100c55580c42818002d1403c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 139674595 1250 139673345 139673371
    0x70e0906100215180606040e030703050a020a020307060c050c010f050a0f0c0c14090a110d090201050c070608151f0807110303040807021806151e0c010e01150b03060105070218 77
    0x110300c604c1802c00f6409482180104d00307201c09040603c40003c1245c0c90b29625103480ea5803440b000c002241044015075000394140982100044c040c1d903c58503805001b40520103035091a407102005407202102c00d10313100702242d070070b20400440340c1c002d90809070b070950b060612250004c455680d11801008980080c6194265011040c0c1c2c0b50400321034050340701c3c850717990800980301030b2001e56209020b5001c403025400d03100d001d08021a4810803cce02d46119040c800c84400b01d80ba08005001e100c8111281c507400301c0c11701c0001c0700358540390902d1003041022a2400f807500001138802c82e60038400030040340c1480464094104042400c02c0150701c654061032502e501c0d20068410031510310300711801d18800d4102c140038441207654401c041089000d0303007000305646081c482c462054001080e03e814012141c081a1141c03081d5041d00030b45500c0085074001c1041c00c2413000f10304400300d41400360200e030780418000950070354003a40050420500040c0341d0403031810081c907220103800d800ca8401c110783c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 139675845 1250 139674595 139674631
    0x91c050d111009080a08060d0c0504051503010c0306080c01020a0c092406050403030207090905030307030c030e01090b06090f07020303190603140102070c0e0903091314130308070e0906100215 84
    0x1b61261040d5000181221100901036003a00c6200c0c801d070385400b400e03100319a89c1c8041180034005508040d4016005802488249000b01014004103043e20444021b40a1a040d02c40c09600c003180e10894142c0c402c21482040303091034498001840b11074880d80d0041c3c102007016520110b0096804000d0043d83d46269586041d46002401e1148030f91000043c2c81c200214800059008001d4036488803461400091949100804601130280d8041518941d40781080720010700181d041d4592141406440307c0700182c0354010900c50a10701118030303c005800500c017042003c0c6800c0c011159043c10701d034000c80d8a640384e460b9001c001c1c0c00c0804040240c4c0d3700052103400c22543e448194002c10302d107030301809180b0780178500985921502c071842d0320030305408001460080096000c100e0315544048400c000340b8200e00781121041d01104103030049404c92002a082901c50747c3d1008260300d0203021546603403680b1003441803000300300041c90198024050329000050354031803001e03c1101c0f109050a0240 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 139677095 1250 139675845 139675847
    0xc03050303070908011a09100f1403012003180307060204060f0201151520010c030b01021c090621050a020418020403050703020108090a08030a02091c050d111009080a 73
    0x41540c0d111300866410b1840103906a14061a2546c02c28015181504103988098440440c2c400710342055170030a00302c01012a44c00d0100c11004032601e8190000c210584441c01c40503808030324101c03e505901400c000054403080c40240155407220107030216400d051079559a4026038115801000000315401c4485c00680d60900038a00080300003000d07000c807981003403000741c03880c820181108103010940104c030380c24054080883d480c1c648100002c100340c29031010020064004054180e006124201e00601c023040c0d15170f078114080c4010307140ca55003145003040036286c41900d02d003848002002040075140f031841d507000341803103140302c00401130f5240e05000b44c80c0182d03441d020005880d00d01c14402400001c1e40001c08170290b0743c0900700011144d07140c162991800428542c020100070020040c003428603195000303003600160031210702d10305281c0c4002502c054920316074044c3c108e0b8000b1103100446409030501158607552034054811548071002c84006403a03103003070112605200020105009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 139678345 1250 139677095 139677107
    0x1020d0506041a0a060305060d0615090b091014010c02190312020d0206061e030304030609111002030d0b0f03010c0801030c14100e01020a0b0c070b010b040b0d020306030106030c0305030307 83
    0x6118015001000fa000040100c1c000c04024001c141c00e2540d107401242d0295103080700b0b20b5800350f120b8828840102c42500ba0349494041d80310f010701c400c3c00c0c0340c02c038035241c0b51460380700f44924804800c040390310380b03400541c03481c55105525071418010f0804007440540c40c0c41400046011405c148e41211910350f180c1106100709500104046420503a02c1001160b80410950780000c42100c100c1aa0740300200d00c000b001112444003603141c44001000002c00c20356422079021180034210303807594150074005202a1440480d0254010381003048084408580c0d60b0007044424000392024407801c4000b0082400c46103c41d042c2c02c04590402c0041040001480103100600200d0504d200d0105008000c19154a8146182c0060140080820081d64030070414201c095801890101890034000e03440500c41e8000c1e00140c075000040300010a40c21150030441c2e086038a54600d5514019280c00f6040007134101030a6130741c0c19500d4880000c08a01c0d0480948040c5008101640e40e0303041c13192000d003407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 139679595 1250 139678345 139678361
    0x708181503180609010c0504140a05040905150705070c180f0f060302120a12110a050d0f0318110d02040e06010b09010801080a030203090607110909010f06090908090d03050c01020d050604 82
    0x442c6c1c104005019100d0340312081d582101c148209900b140b0520400141446040c0c2c8c22281e003052808043d50b044c060009070140c0343c203280e240d06280c1d607200c82504440c03900c102600501203c0c00c2e000104410b800e0b00502103c0380c96217900000d0303452001900001918006440e0107022500e414080c801e52600203400f4448101500040000125903a140c2c0080b07260307184180184011a4064000c1d104c1c10301c289030911ba808400e4031800c40700b0701005081c0c200c1158180000034a420764904036544a019071074072180e00100348101c4440e124007041005200440104e8000340c5440300044450400c1200c4d41c00ba14050015584440e040c40c001001c9010503030000070541d0203409505d011a801204480300810152076080d51801c15007042c1420441c081059900100458204051040e0640c04400d41720078184052020a40e14002d030415110f03007010103020904100600340c42c07850003503407044941d8441e00b02141003521098101d422a0040c2c208454195118803c00090b45014810681 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 139680845 1250 139679595 139679611
    0xf120b1b0d1e140103211e020115050904052104050405010308041706070e010503040206160f0501050a06060509041d1209090109060303080601030e070513150b07081815031806 77
    0x4295031541d1510036002c00201c030318114101c3c144140e502d455118005641f20b2550701802d908404680c4031000303001f0a40c0340f041c0850186c4032400410103140001e5a58010b50f0010014003000c02020a00f4451551840c450740011404000000d0341e6100c0b405514025400350301d00f50344039032501c03249c1c0c91200c0b440000d2107050b070800001c000100b5088602c0b00d081140a180c01c5481390703217520108429101d8001000c049140180c4000c007004440b072500130b480ea02c1000280507945981c11400169501402401c0102c1c9041c092400c003420709074400040103204030445440182d120140c42e003014031400383c0705821940005c0d40ca003582002c03081c40b0b006001c44203040010a02d103443c001d01c00c41c4003400e2217040544a03282003c60600c10850780001e1304008054031902042c0711421030040c4211300c00705d200200a4640007824907568000c0d9800b071034100842c2da28114822130f542521816601a140e48074002030920070b000400f50000c2e40c03040071a000b01c440c030140d1003c1c0c124a0071000030807181e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 139682095 1250 139680845 139680881
    0x405040c0809210a0807030b1f14091005030c0409060f1d010b030f10030212010b0f10080103080f0d022a0d05040b090102010609150f120b1b0d1e 64
    0x3124101d08081207480d14811490242d11a1b2aa4030303003100030381560300001e40d108040500011030240020001c407901d0409840e29a0181801200c01400c2d000e038045950b80206502c40140c0007a020b94019030313011704414245031816440c0c00104c011100d5540001c140b500b004a800d220b0203e011909010524080c620315000c1c0d03240040140440c0300c01040326034040d20000100b140040440b0382d20b8065a4024a038002404098814500070290120a10b21854140341e44a500d420710b400c9418200c2c0090743e4804650382191501d010783c0c1c3c80380c01d01035803894040000208042d0709101905854490486280420004011804680c88404441c1d20b15410021110001540000899003100d40c41800c00d501c48501c900140e005124030303846000f0080c101700341c1180041d030380c078440d50995003a0150004599255488040b0442d004d000040404100001050181c82d101c49400300301d82c0405d2896251908030540c050070749903c43c1007504014005071100302c040036103015125200c24071a203e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 139683345 1250 139682095 139682143
    0x100c050d050708090f040e07030521030c0301033e0108090f06220206040b070236042907030507050c0a021e0d0503040e060409030f140405040c0809 65
    0x601031441403c0455100e034110f0305c9000119150342e0017120020b1011003c0e0703080c09940e42083ca403601c600785250382c04000b24030403901401c0d03080400e490040040740b103c0390940c0e086a803620076501d001d44910b69040e12055611003461143d50450480c5040c1c120301b00324806401c0e00250003140040e120400c10740041d0070f024bd4948000403019130040c401e01100103000c09050110703101d80c03072110029400c0f81d400a0045038082d2140c0050680520076030b1300f940340c01a02020300c0c440045040410710f440040c01507000c03180700e402142e42d0b000380c026842d500040c1440483c1c10440300722405a06a68004082003100480d054171540354400300c1805c0442c5440b6041040c81e03182c1341c048000a10600d5030000543c0b620b90101e00c1000000005400004000840d0a000d0b942e0b401503c2174078290f00002d40054214249402490790f020303031540710b8180f40310120106031003000c80140c820f003083c881408001015500c43c0903448943e109600c44c1c001314104421020304003008810403d0007282c3ca1113007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 139684595 1250 139683345 139683353
    0x4030b130b1303050f0c061009050609191506020c01020d11030403030507230a0b060607020a0e06030a021e12031e030901090f030302040e0a05010e01090b03010b100c050d0507 77
    0x1030180d0101d0b0200d10500c1819141c0340c2036415000780542450b20715008580c0b100074110001e01d850003040c00f10241100703540d55030b1080381030703407001c4070001d4101400310041448440e429200503219458044003160050300c403d81e045d0000c0042d4010310043e0b0100304860b07000c0d60140300141d245034240c03a214910f142544402681c91040c1c0c44000c04009001070300e030003031180340407000c140301c20900b40c3c0c0744000f00c0741c5c80415640c0c5890768064901c2c620000c04078001d0b18100080341e041c03690241c00889500e141a580d40380a210081400d6050b014502c09840140d8410305010110a2009102009d924000e07040c03206114040d800041103520400c001ca0001598041031380500e01e8101981d0759a03a16001c03840d024241c10039004000b01040c15580b8201354054001d0070079200d6094001d030455440340c4144040e21000c3c41030a0300e01030380e80c1c010b101d68112a0450301f07481ca0058000b16056441c080400c02c0c4001d003da603400003a4241c101040bc00c00d042c0308014440d03109281c81c9044c480c140c0c40d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 139685845 1250 139684595 139684613
    0x50306060702031e030c0f0d0c1103010f14150105040506070f0201230a030c0810140103090f110108010605070c0e13020402070b01080c0a06021002030709080a060204030b13 76
    0x8002442000c0100d101400c5541c00c20075062080c101c42045a0624140b48019682c1d81262400003c64080d80030306035100c1c07074000344d11403c25001d40d9031030000f01c2d615190000c05079406d5410720307099500c454483c00c42c0308a500558945080b5440d50300c52624202981000968200211504114040004000030364826017500c2045410059003035202c6018801a03030b10090720301d60508100c2507181500e003c1c91703001d03000d40340300740c40c03078070b00f4069110594402c0703407001c104907181034001c01c4034a024000300c1d80d0035200c4403000c9418100000c000c01c280c4c41e2200c401c900e00b08100c40300c80e8203095003080c559218482c01d00500b040c3c00c2240c201022555440d08100c0395018000c0740103141000203211182d05c140700341d140350300940211354500c481d091962940c1070074000d10f28a84a060241d020905110300c540044071007a501034145511411035941c00303540083d04000400c401c400780812054800d102c514003484c45543e00607655483d6141c546900c410060182181880c0e0f88156000b0a2002c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 139687095 1250 139685845 139685851
    0x102010b060f0c0c09072a0816030905060f0d140105090c1602100c0201020106150c1e0c0806090709020702100819021b0606030102030403050a050a020a081201030b0f0105010503 78
    0x550141d032a609140201850201344036422a0f00c024040c06105203150070070158400b4481402d41c00045a038810705203101881243c1c001051030b030003000f44174000d80d51158041c001c644245000005266031744002142500003031001107911000140040b681e8100e0300c0b8007a00c0300c0c81c03880b261445600d0400007803542140100806641e203400104904e0803541c0b019528021076000b00360000300480c07084001c002e03405401e800c82c007540c81d041c0040b6003d1032641001c0304040295a4901d9034001390782c0d540408954041600d061080c0301148200010310b045248005406d616008107858501000c04515040c52036100c10039103032040120f4000350301c079001c1ca80d00010140c100b501c1c240d02c07800b01541556000c6a40540b80c0c03031000c5402d0600c1056010300c03c0c00507101e07a0072503c254442d1002c1608034031060b140200030810030445103002600175005082c0f5240300d0300594031101001c0c3c4440d403031f0b0f502c000c600c201082d203498010310412881d0910360750001160404d6030072139030500c1c001800512001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 139688345 1250 139687095 139687117
    0x307030b0a05092d280b0603010603020316170601030c03091e0b0115050d1107060603080903010c03051003020904080415170c160308130804030c080d02031306082706150102010b06 79
    0x321000c3c0725480d15600841b56282001d01801d5aa40e034404000b0004c2d0410707a882007203103e40001805030300788520041500030213004d604556070b85541d0015401084110510b0f800d050b1200070340e00c04100f035010050200741038813212280e2402185403840b80803030160001403000e10115504005140c0c0003098580042c0d03201000036004003000b41c0c1180300d005484004010750f06250000c400c00c00700c40b01404240310306400a00171012842c005800350f4a04465001d02c90000013000c01c09441c092003040e40090007003008615050300d0341c034000c850b00304440d55440400d42ca0031902020a600c1d11a041d0722040401c1d0490401d10741e02d03800000001c44480c05403c20401201282c403c007500382d10f03821840d90051140740e132103942c0e18048003018458420201c0038081c21681003403090010044a02c005c0352031050600c40750610031309441c0013a010303108180f15855050220750012560b08c040e032540b111074006000d18a441c4450b00f280b0044025224112390501d010f5076250744842080e42c42194903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 139689595 1250 139688345 139688401
    0xf0b0c010b03070b12071413060801050a0b160609050610030308010605040302010804170c0a06060e0a0b030601090e0307060f0e070f08030406030209030a0503030103030c0303140c0307030b0a05092d 87
    0x1944400f2200c081c00f64401f110180c0002a0f82240c034400080010110359a80d1244007503a0fa803081000200d00241c401c842d402c3c03004001c0c20503c810000c80c000c9106110b014001058001c40c0c41d0580340c68011210220320300d411040600505420695450040290b4906180341c203003181c0c0020144080600000c020b540e440007400c4000040806a43c170340c00070801101c54500340c07820304030043d14840c850410301c0e652207404108440340c5409a43e0141c0400740041c1141c0e4a000304c0c0c000100003a481c4540c0d6400144140c100041c0903014160850f00d140c1e01c00b140490000030060700742440769124100440307007828200603203200442910219076141c140162a840000007090030002c1c0000010483c0c04008000f10030903401c17240c400c3c0c2040c043e40d0100303c0d0b40c9612050f0101c42000f40e4081a10f2071052000980261003504941c84c88840074003000003039551040400e02c444815254066009004107140b0090f428001000070000c0740d0414240e21810312400b0308191001a0b01d51443d0040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 139690845 1250 139689595 139689601
    0x11a0901030c031409070e010e07020a0f06090602030f0a140411120309090928030c08030a0906060806070f051201030b130b01060309030e01020a051e070f0b0c010b03070b12 76
    0x40644d00801444c0304002d040211454940c0402e9250300c40c5024203104a50503000104208510352241407007000580c0062040c445540c82e80701074130114160859100b030711400316400148990018601404030a051400d81c0d04000050000b5204004403825640896808100225540c10600c040c81d100c20384050013403240d03001d011030540c07161642c00c40e000880750701403003407040c80052000e842903c0c400303410b042541d82c0007a111002900d03203409400142109100008601d0b00c0009640220601e14001050703070060f552401500c00e5640000c1351034010f1010441e400b508000490709048451400ccc82c41d10100c070910104581e1706000113030601201c0000208854500403d01c4006500301d03040d44a10741e900e140040107804103040032000540c80e034422480e554000603c40c1070320fa138088040d0a608a503042d40c20101c0522051112881c4601200015600d111110050141241000407940c0d10004d550307043c03c3d551441945030280e4000c8808010f00d0124400707403143c07000b95a8080285032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 139692095 1250 139690845 139690847
    0x30501150e191e06140a021b01051b0a02010f051c020c031c0e0c040c0e011218030914030706020703030c02032a0405070203041820030f0f011a0901030c 67
    0x40076078200c110403610f141100448040315024400489116580e842c24071104200c4d0740c04103009005031140944d10402c0400d42e200003900903d0903070a030604d001401c0c08a0f40f0307403000505800c00c622030305c5500b1900034141503582c04989400000481d003403061812289003400d40b0b14200498800614507402708400040810030f20840e241c0d034482c12018a00d1036142c8e200840200118441c6100c0b0380305800001001d41008d01424944e10700e00e4482036844102d800055641d828400484881c43d03039038810302209076080d50003800e10399000b03564109a0380d00308440801c450440c0c1840710310961115904200301c81d800169030302074960524000039406454800700c0d140c5814003460070f89400c044510304508680b190000d03520b13008220ba06000799100c901041e81c03244103501a480c6452190600903c40507545d400c00c0a10b10207842195841c01c0820f10107035a03642042c2c40212003440008103000c201001559141d014000d03110000c1d000c1c01c0d044d0074011680c851012070506040d200da604038161 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 139693345 1250 139692095 139692139
    0x5010212042108190504050a02060d15091a0d0c05040609021909051f02120d060609080106080c010c02031504050f100e030a081f030c06030501150e 65
    0x50380d00241556040d061902e095210007100504600104021a840c80c0d000d81c031a100c0103000d1180204c03010054000704900002804006000356954401c5107504401601c442e802046840c000c14070028984001d0145050511044c0d0301c0000d00a04200444003218050744205070342910864556202ca0304c5031030143c480300e50b164400b550041c5000303000103103400240c00030b21524214040f10f211410b0102c0c13080c0c420100354011075400c80510214613110003402e401116049403d03004a5a88200c080d510540302d40c440c0b00041340d1162a59070401c00550411400005010080000d11805003072480300c40d5201090742d4498108000e4070010015501c041c080741a00c0920642807150343d190601b0829a10841300c0c1051406100380310b1070008540d002e00c03650020f1411500078615290700030304101c030580006000c039051001100305031903003200e000200340b008610404210b03400c02e24010000e011134005900181807458000d03c078110817940044214014603040b52007468100d4421f10303405c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 139694595 1250 139693345 139693357
    0xd0305090a12020a0b0705070c0605030a0e030301240914090a020705100b0906040e120903030909040510150b090d260306030c0a05030604080325050a09090b011407050102 75
    0x303903030b60000042071496020a8030400035000310703001c410b070352242202120540318908010708250390380b02007400100c0c030960045400801c070b5a00810003040c0481071500b554020392040c00521420b065066508101c0103141d807602584e0700f00190012300c0c2401c040020080011080c1c4200203900000f000c48010340d0589141c1034120303044400061010031840c0003414400340b168031600100c070024041c0c1c5428040c11440c540484041d00b0081c400d80100040c50700035040f2564140820f10000e0555120011034510960062009005100500f221f4000311150301009030f0011100300024880002e0901c125490400280c8011044119500b020f00e0912008040340315040803184003e04550b0f048400340d40540400c03000d07600100c0740c003810000c032000140700d000e40680000c00050003085540d000386a10214015480c1c02541522020f8641241c10181e540c001c0f0780c01241459141358400c081c0c8001e0305041c1020020300383c028001800380040d550803100d440030000340c40c40801c0021740594031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 139695845 1250 139694595 139694603
    0x1b122107170405010f05280b0a03050a0b1b0304030905091906171204051023030406020304140c1315080a0302030403050f01051e060102150705030a0b0d02030d0305090a 74
    0x28450425140044c040c1c0440c0545031101404c10010429000880c106999036643e0f00440300c02c0105c0600b0000068101100340c9640481c000d41d001000c608140a145801032040e19403000c1c6160a0307a005401100c1c081c0a03a68100060041000107078100b45541e00b0f45d013040b102c501107541e0f40940c40c90740900201c2d01899840c11b005002820300910395482c204d00e4149003e44428220384104010f8030b0007103214480c0c1c01204e201000b8070050240c1c0c440501c070b0070600756065049850711603095003981f0550b42202c50540c00000c010034801c808046001100100c00030340310502c000000111074001c010344040ca2680c1c0c8001c1c030302c600c104020548000b000020305640d144445418017940341e030800d00c0290340c1d0780101d4402c0300000e0340605c50340707208041001c401428030a4444040704902002800113041d8401e00700d131034101028019190344107480769035501e542d91030680380640076200003012043c0250704034281c100050360042440300c49204149000901503803840080c42c0fa0200801001d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 139697095 1250 139695845 139695887
    0xc041e09050706020d02010e0d050307050706090b01030201030621060b0a0317090a0803031b090609062b0c0503060405041113060305010c050705030714121b122107 72
    0x12082250102e01881118103980aaa90403030950406a007640c003001c1c640402e94000c9100e03a20b40c00c0c090b00c0519048050341c0f404505181960303036030004a424943c0103984181501004008540e0b03d4061040a84284603000828501e03e00a45000c03460b8182c00600c01611640162a41c0d1a1103d180000350f420240d000d0680402c2c0c0399603441e540c400290b0a01407526007402191258000040341d004810180c515200c0740065615150182c201c3e0050035488601008103007059507a034809084440b09146900001c1210755a090140010041900841c0c50824a40c0c04166400100741da07804541a1030200d0ba5907030b0380c40d1144500c6079100d01290300a074082c1e021600314000e41d1021055038804c00c02000301680040007920103000c0c0c610010002d5108005803000111103e2200c030790644c858040300c5880180304034840d12a0440c0031040d03024240c881034814040030402418961112804880c0e10f0115020398007418140795031603440c080702c121000301e000c191080075080d010a900b41540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 139698345 1250 139697095 139697111
    0xa020d2007090614040221130602030a0c11010e150a0f0603080307020d090e0403050c0f01020301091a06090a0302100c020d140616021e0f030f03040209010b0c0c041e 73
    0x5100141040d0190311007044a12001343c8040c10a88210740c1c075811003e003140d8107a011103640304e8040038010b01e001043e4440c000010000360142c000385001c1c007421040401c0e00310a07480300a10f41128074254070141d80c1000304107494040082101c501d00c903640c00c804c0703000765240e00b02d0344040c01d001c42e01100b640e0304e007090010078041d081010f1801482c1c19401d49054090b81c03001107403105182e00442c0c0700c507000980480c000034000e030005c0070910000c500303507031707130302c12650703e45402c90300241c0c40b003402c45d502c8902d01c2001ca000352030f00141541040701e90038142400c48000c0380500c086400000c0c0904041c6c401201140e001e5941d66900d998000d00001e5103284900e4140f210081040d0560607610a100c08641c0941034154010b07561071132680201034440300219510b00011180e00d0581c40c90045a00d480c0c0402c01c00d000422503c0c030702c46c003841e40d07900f000c1c4140908408168080b201c0d2600500c80020421004100041108411100400c0d11280074640740100304041d0306c041010b070300d02116 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 139699595 1250 139698345 139698359
    0x60c030302041a2701050d020d1416020706030212060d02030f0307030905100201411815040510050403032403020406050d11041a060705060f0106050a020d2007 70
    0x7004900c0740054001010b4443c0403052514402c110707144c90200d007050000900c003079a03d6028042000181d0f0000c18401500300b003e010000058441d411400e6140244490741901000040700078004d51904510b0288246560444644040d24042c4101c8201c4072181c150b40e01001240705204401050301e030745150519019040411902c121805410300b012043e50040c0103105003480080b421080503c00440c80c00d15a42110652440f442a484030441101e403140344001c02500c00c2ca03810700d80510000e40040040c0c034200f4500d504000150510702008006003002c40c81410381328039400c01007400c0d00c03285001d60281201c5d550784d003071a038034250041c00d03c01081c001d41001c41703009860401c441a151000e209001940384805417070300c0c5e80450010794504059018590000c00b000000c40344078a101c0003c0d00039400304001740c40a500000500035805500c0b05218010070482c20003605c0e10100100c0a034460301b082c182c881c00e000c0c0800c0d1142c40600c09030141c806002c2d24006990425482d215 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 139700845 1250 139699595 139699597
    0x301060e0112020102070e04050307061113140301060509090717010b10050703030c0e06090d021216030303051608010603020a030e19171206100c02090f040203160b0301060c030302041a 81
    0x20b01a030040c45035590000d403401e07011111900a40d08107015501d001810344404c4007425035000759810307102c01000076000c2c84c1c1e101c00694000d0000c00d448440f45402441c100b45c2902d0058010900c80c0e562182030210720400002d080307040720030f02c2140c0d202802c121011180102200305902d40c000030185c08015040754031400801c0c5161003502c0801828016000880e40c4400822413582c110008001c54204e034a0170441f641092480100342419000f030300c52440341400c03419011680c0340e2400000a001f0540c25000b002da0100c00d40368240300082c0c801000034072825040c45007506165000440800151080d00440900b8100340301300e91142506500c003880e1f0656414094546030034602020100780b40640455403400da030301c005400340c1d4076003808100710503444e2480d403028003650071240b40050300c51a5100d48140382e6060310b1510f900d002c0c0181070611018070741040d161102400309011307545030001900c0c150b0b03102c1e1500180ca03050750320f0190b000380b1032034010b5442408500800800104040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 139702095 1250 139700845 139700879
    0xd0801030b09010c020d0507020f100c0b070507051e0109020d03110f01060b0409500613050c0d050408090a0b0406050702040c0c060903020f060705040509060d020301060e01 76
    0x320801e0000c2e92040d401500301d9240040074401a0050500e80251502c208054a030741c0b400100200480068100090b0140214000d0710000c2048804444280f1a003003100e142d00c1034050034a42c0c41d16a89907501c540305c3e02c040301008030201030340714030040b184001d6122480e044d5000d010450001d010f0b04001e03001c2c0031840030441c11845280c2454040c000180103041c101d0341c0310b000c080c1c2098200700b1740001509400e41584141d4400e5000420081d000300e41074029030b85030685c4160318155454a607003040d0707100004040c6c14401d01090002d01e8503210710381c4641442c80c205c0000d05840341c1c601024030348541c0540c01072803030902d400d10050062050080100c07001c01c03510380d0782103582d07a100c04020707000714800c80c00414410312210001d4201908039a44820f85440c1910b12070b013003a581c2000709d1341c0c4010140c005038031200302c518106208128054001d241c600b06242030900e00b000180700c81400521301303401003107801c0100c411901c003500910050400c00981711640e60b1101640c0721085242 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 139703345 1250 139702095 139702103
    0x170702030a060f06080708030306091b0301090b0f0103050618090c060a020105090d020604021e010504051c060b0a05100e0303131716030b0105010809101514030102091807020f0d080103 81
    0x4c40700002d0000800603580007201d4200014506503629a01002040c5038000c120704000d80c4000b100c1d03142c80c0031050046002c0c044102001803810600d000380805011726001250501d031525080c02074940d15210490302800303070b0603d4580140d942d03040203810f040c100311400b6000000800c80c00011034064010ba4450500b40c4222444091100e0040303954000980740a034211154448604010b209181407100100301814800d2405540d42c0200c0c00c09a580e6018031903045046400c80c0421000d0b020b01b04203050122003e4010504210014a4280300301d844001484a031103c038200c80d440038010350b030301102c1a05544d00c2907651200e0748410000b20003072a840b58051106000301c10b40c0000e03400003e580e000b080c000c40c660300300001035130b5403500330303004540d03a11134807903048ca481c2c0e1203004214010364141011450b003031034510740c504040340295556105e640148403030049034540b81c0e010300d2030710300c0d14801d0b07249034079641000d90400c0d688801d085624010036516805803070f00b204209041702c0c46 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 139704595 1250 139703345 139703351
    0x201090320030105150d030c051c0305040b06030c1e0a0e0406020415050f0316050c010608030a0f09140d03090801060803030615091e01120203010905011e030305030103170702030a060f 81
    0xf49070400c00c10b43d1017031050158010140005440400d20642400700010b01c41c00c11175076218035440490041804040e040c4000035256000c010401c001d03203100903080341007074005110041d4001e0004072405415401924444403100302c01115039500d003800300080c400f4081c010040d05090500364082c1d8002e006007407040704030a0214a5540c03280c01210320390000b1032102802d40c0c4440318003502c580c20000041c002c102e014032144511903420b2080303000401440008680d0b8407980b18010b1b141140d003042e55810b0000d010070820024285a45220b0080343c1101d8002d001a45460256004042134001d206190300e4004042000c42c0000003c0d802400e003190400b03114104004401e43c2e034460b2680554004090400c03004203011000c841d1140355105060100301d408440030800101d81090340802400368031240100401444110510841103c0c444980c031002d0650310090110300c410700c8000c10b8035104441d510340102e00750040c0c0c0c0009070300400380c2d035281700c903405d1030009400c20085040e8464a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 139705845 1250 139704595 139704601
    0x4150303080f0106170601110f06010503010b010f020604062a0908151303030f1d06060f01030c21060f14130615050d0605031203041a0c0301120201090320030105 71
    0x2c81d00d61480e0488069603207900001c043c0ca8a080300718940a4903440c1446104000925940320070b1009034040e4020000904e2150f141600f09400d642e01305503a6818818280c0d041d100c81d03603010034110703805908180003207010f0108807400c42405400c040003900908240216092107030b44003008a00316181c001c100d50705214450040d0b003080c1c8098442428415442e201000000c2c081d070081c05e01444000341c0021038010300030042c0c181032104031030308015800220820841d4980301d0b00c07030440c00d102071908100f00780b0380080241800c401062034401011780d00303034001c00c0040642c000130050020b080e15002400c0e541c0c6a14140030569005103880f80d00c2c04064103d11115510502085500f1622581500303203030307d00203842a600078000800702507161100030906e40c030200440d6103550741203460180e0300d00e00380c01c110320780040700600b01c000003140c80140000e1040035016281500d01c00703940c98480d80101e04c0161040003290f4401404e4092440340500d415110701060120090158000d0103d9030b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 139707095 1250 139705845 139705861
    0x617010e010b0409051e090304031a041e0c0503031b0f2107020d0b010e0711030703080705030703090501050c0405040606020106050303040b09120109060b011e0c0303020a030b0415030308 82
    0x20303000340294040254244001c0281507034503000030b40c005801801c1b51107802c02c0c0d00042580c114040340c010310180d100140c200100190140200c010300c86001511020b801d05540b101d40003030700030200426040e01040c050080c096082802c41c02402d0041c1100d40d2045500e2740c6c3d1102043c808020b41840c080d00000c64807011005c10b0040040c2c00101000004416090000740d15410000301070340c000c1452280070300040c501c00703109400307072000006440035850b1400004001100d20505402c0c507800c01d2000500280e04020003e41000f84d5007006a100d6844060490081c40e1404014015600340820300201030303003140080c416034405650900600381c40d900288c1c04e80706a4401c0580617441004104002d02e00b1a024000c8004000e00300c030307180d55260324070500b510020901601c4103669208009540e680103211184140710300101c40d00056000e6101a0080346600c4000c0c1c141600000c00c010101d105c4d034070079104100001d1041269013445414844040144d000450103d0300c00c0022403a04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 139708345 1250 139707095 139707119
    0xf01090213270b180103030302030a02040504021c06060903120507060b04091a0108031201090f0207050a060b0a050a050f010f020f010603051606030219030f0605040908090901051e041a030304061701 87
    0xf1407101ca20600749071b40b856a08070000e60004001110184e400d200128640e40d481c001408481c2002c0c4510b01740100b031902e0b82c1c0494030580c0c00001071205041c4100300007000000100b04021545c00d200d6100c2406050007405440a80d03d2a03501500e071510070000c003c040d8241096a45403601000010381e00c8051580e9070b88500c640100791040800300400032841039030040250001820710145c00c00c4143e695442c034081c030400f011a0859200c0d0300255543c10f0911405008001c2281d03129900303032134003000c5059035414031000c84c1005800c00950510034002c01c0100e00305c03014070000f080041e030b403418490f44410f0783c04400307074900049490000b2114480c0c001d1310241c0121802c070110b0010382440960082c00d030038007558450707901c1e03240009155580d40f00d60746460340078881150b56400642d003009900e00301604403a10501c1f887c003105141401c1101c88044082c02520001802d181c452103000d000d190100ca0309070b00d44400a404a5101e83c440c103085040185508121321a03601d078004440a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 139709595 1250 139708345 139708369
    0x30b010e030a0609051504240204050a0605131a04030605090106030317071e0e030c0315060409110618010228170c1b030705090f01090213270b 63
    0x11580c40845010b003c60065801018840d00c620111094070f400c079004280340342c00c200c1d0152a4000c130300170420840407a9807034a8011460a80045150a082c040040c0030728441d0f00512041240c0498041d000c5500614140c1c0074020080010044000c074110035269a805400200c81c25400d00d00890a414014052641a250725441c3c500340c690302c030508090480801081c48080145410200345290319810f422395000690b6511040582000410b0500d0490b0045109003c1d50000060400011020020b19004030302200c0c08501071035079050203400302202c4202d00342e021400180142c2c944141054070720340c20100b0f80039205c42005031000072490b0420400201a1401a07240f0300e40015403130b040d85211140030202060415500c0c41032245004501c0c0b81c00c0304030250380203d0b0020b07403030104a440f00602c4115221102d500e4002c050041520040c42540d007030a80215400420f00302c1c41113402c0c0036080480c030620030581c0c2428400030100c1d10408105540d17150188a801070b080100307202070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 139710845 1250 139709595 139709599
    0xa0c171c02040b1617030703050f07020a11240c0604020a0b0301030b01140a031209080708010b03280506071e0806030a020f01090b040308041a04032a090906020a030b010e 75
    0x70401d88071640010004032010744c1200c09541080703000588102c044040d6001c1c4081c1d0340d0008140c82c10445182c07450001070040d03815076200d440380741700040711400c566110b11030070f5441e42c00d0300441d400220262010b50a4140c201240401c80d1400c0d02c80010340a0301c00c074000c64110f08055614405105d40381303c00e000c090440030341c150040c040c94040c406144ac07203401c09456004000d549032110740c40303075040c1d009080005a00c8001088102003c01040014004500003002213207c1c2d400042e540303940150220701c245100c1c1c1c0184030000a8411004000750700030080d03a800f40b0f0b2040009103070022000d403001d10310494010110761144200d6105208150150040c00324010a8080045889403e0540e5040202e41c09000c5070820607100603200961203040416100c0b810907030f01400105100e040d588000400b4007040000c602e003101030385500c101d000805a114070700c0c170080c220303440c00715040300088030700b070082800400580d40c0c000c0c520702000b59010005c0c5a440700045500c504154100780d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 139712095 1250 139710845 139710847
    0x905060106050f1605100b060c0d08060a0e010816090203070801050904050a14031315080c070813270c050301051e1903260f0a0c171c02040b 62
    0x4099940610020005241160080c5090004a120400002114004c1200d40d6000818565007000710340c080d017401040104d074000e040400c5c440c10035a65003150340c40d032001c004c10380c00424841d0301d8003030040b005032149000803201507854002c032964031440d00c4c4000000d0806070390b00240040c60b41c400e41e03005480c40d5442c0030f480d174030380300810250041c050410b0b655801138034010030000f10807124000310b0f0301b030343e501131a00c1c1d810000c0c00b1f03d14801c080d8402d004900100440c3c01056038014002035101c400704540c3c586542d03090505119a000300400b02460b4a0807580c082a9a2881c807088000c5484041c00e072400300c0c01000041043d14000524100403503401d00040c4014a0022000050000003101820030b180c0c003180020511065014150846411040184184a01c6084459072183e0910445100a50111000c107981c416149a22640d45010070b280c04034510910015a075180c008845c103280010034410740c501a0b000c00c50f100031a8100b003c0301040841a80242c4045916240c005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 139713345 1250 139712095 139712099
    0x40f0501031116111215060409050a0f03020304230d060209190f08060603070602060a0c1707090e09010c09170118062f09100915030209090a09050601 66
    0x190090702080c42c450858540c24408544850b6440c940f0b40802400355601a00210350507080c070240283c400302c091582d40100c6c0c20031006c000c4101c0300540240c015a00010102c1041c00e03c0da0604d0020080202056124450780c400d00d40e0010190098034000c0e140103032401c00c0c001c800d12050301d194030310a400c00c41c0384500790041030a83d405040020360160000702003c442c1c0c2c0e07840d00c1807801303504a00351480e900101800362810030011954810702c04d4004201882c2040300c0030756111001030401d41c0381c50302c850212411030b1040031a4400a215065010014240700c00301404001107409240c902c01800c0e800943e00090500652500c901c1c03648840f0704880c03d0003180d03002800c540c0e000c42d00a40d01d900f480d080d803840ca1441040e180c0c0c0200e00c0003462108a0141084c1074040e904040740188500f00280c4444a607038046074007041045038140205043c0003001d81e11085140d015007400381d10524a1020b00707030076800601c9085001c480340d044603a1044005011580e0042024100b07a1283e001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 139714595 1250 139713345 139713347
    0x90602060601080601230414040207200409240506030c2202120405070602010b220905010b03030d0212010806010e0705180a1202180c030c0702041b08010f0b040f0501 73
    0x21807500004c0625162001c200e80030b40d84043e4140440d91014850790000702000541403003143e44040300800c5509600e0196161503c4410140303502c06484410800c2c1703070203070f030541d00c99000d8034840747d100304208100c05a030510b031604210054480c500c100d0814002403036a180c085a0310803106001080e040249901c211070301d00d40c614180040d40c0c01a801c20400c1d040c104001050382c172881c85400181500790404400030700b0b40760541d1b092401904541c06400c88040000c000b074201d51805000000c1c0f628850030214007503e078410304183c00d80030005640c0340710710a80c2c0040240c3c0041d4801c44030280d0381d9880301603444009220740c481c425074880c00b15030381074410001410101d0100c5035212010315014002852900c4640c0844812500c00c4500e01c21800c1808142039440c10040d8020b019140c262600d02491000030100c010b02c9d00300250307540440d035031a440740c0b20200302040c552002c000380c1507010f400c404003800b9500ea0141080400941030260301d00705e90959003c10440c500c0c0b40d2030600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 139715845 1250 139714595 139714607
    0x30e0703020a17030d0e03031f1503090206070b07080610050405060703200f1006060c0201020c1003090c09090605010503030a0210111902160902070c050d030c080307050304050d090602060601 84
    0x1c0840da40380010042c8407807080190081b04409001540030b1966070500258030907041082c07000c1d00d440000451400c000261255090102c0c408072070401090f080942e00c001030a5100310340e001428100e550041c01002d6501c42410792194200303030354009490241c2d0f0000e4516000d6807180300c0d400310040000f040041e1013100ca101c40140100d003150182038401d1103060410350780d806100035584c0724180250b40d0011780d004240c01000f16040c0b00030f2084c0300ea00000c1d200c2c40040c40c01e5014145e030b130b41407925961280e801074003440e03044001407441e41c1d200d00c1d011015001c00d66055440905010010446180c0407080320b5801c04c641d001095013042c01c603604030103401400174030042d40b4824002c002c0303503414203082c0420400341079001d4203400300c600001161440058001c10380645c41480300300002000e400c000c405076101114a50b0b0320000500d012079081204540c0140494030101c24040065000b0003c1c5001e24480c8081e5001703400a104103d901b540e5038880c05d401a8465404101c203035000720 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 139717095 1250 139715845 139715879
    0x50102150c0708040b0f030603070e060d020d0507122109060c060b0303090904060c031103010b040605090a0f3015091a070c0311010e030406110a0f12030e0703020a 72
    0x403260a06040d51084811000e8100c03103141b015072040002084110f180c10b0000c6000342009500280040c02e11001250318400d203414000c1c01000302c0c0800c4014031208110000013840004040f0701c1c001110b1604000c3c84008952103000400c10800e94100e4034021640202600d0165543c082c07280c000740c0b00c2da805003107a4218950075010804c508280340c1c841180452181c1c3c05041d000c108144c111030003e04552a01100b43e40040f0b080c0011b201d15120072080b2011150303907183c03030ba44a1080c40000b9404c0c42040e4081d038450700c000d0307400068411502e1000080e004e0804802e5100030850304036002340f07881484d4014000084015544c0b0340c0e69042c0c2c04402c02d14080d00512504159004500c443c9001c1680c4502c04140d07000b010390101944034400303070708240102000303101e0b8072032503061a0703901e003d2409100144240341061007804641005804801d5410029010716007a00d420300000b200c000c4080c00000908211100c0300100d40040e0750000c60358054200d10747c0703500d0540b101c8102407510b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 139718345 1250 139717095 139717103
    0xa0c060204050411030114030f0d0e2106011d010303021c02010b04050109020301080706020c030303060114070b10050a05030114010504020a090302030105090c0306070f1e030231050102150c07 84
    0xd00022886445a128013000115140a015640c0d410192400d08500400c45010310940c80100c082110850224000707a00c00c481d42481d5285055000015600070711501d1840386c1484030b900c1e03581d400940040d506048a420b50002c401d0406603404510100c1d50901014002d80e03c52101059034585544a0445060721407000040d540811000078042d10800c0c2d00000d41c03ea000b000602c807100c41807000000074a100c1c00200140034018000c02e03201d000082985051040b10f40f0900c41c2d5409500465940e150b03c41524036851508101ca40000c240c4c60044900a124114004c50641070512540b00d039600000c807030f20360f40da19003800c200c065071100c04641c041140d5020000010380b001d000306801040141e010b070034494001d8052601c0e24030014000010804001590020703d500604d201902504940c0010004075210300140c01910948180310905080c00f1115881c0080a0480c03c0350350701d0bd40440039450b03503110012690f8205004070049501303803031000700b8842c42102000740403103482 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 139719595 1250 139718345 139718347
    0xb060d1502030403020f0c010c030c0b100314030703080708010803030406051b0a050304110901050a06030f0b061b07060207080c0108090a02031c0e0d030c021c0b2e0b0a0c0602 77
    0x1054404200342c2c0c02c196011000342e40301c806a030305d0311802440340544e600030a1804000102840d200200b888601503405003004c29040c0204d181140c2c20101d01001d0f50b045103600c504602400102c95496109040650008580741c0200b43c405100d444618100c80301100150304644aa48410740208400340c05051428004181055031168040142c00300603c99201c1076200c0c40c00c0e06000c0d4607801c2d5a88002d228604520060000c0e640d5860441c007510790901d00040c0200d20409000014503026800c65805440401c010701d8081c8000301d00c9012100550a54006998414082e88c1d10b14503802055680c1d00001741c1da41065100301a40c5502600b900225078030743c800c68002ca4240707180d8804800b9007201d50088404115080803407100102c80a4640300315450392514020301c00002030800070b100b88402158141d90798100c0420441d02c0e50041c501c460030341000e4011400b1903c8007000a00841103444c4961240043c03052007408070f43d80040b855240028441c01203802010143e4116101c82d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 139720845 1250 139719595 139719623
    0x13080106052b12090911030603070317040f090608010b040507051b120a030506010f0509031902040b040606020d02010e16140a030501020d0213050415170a0204090501050f130b060d 79
    0x403642e0300c80403e515800009410200c0e204107440c20f07901036070144c1170100180900764400045010482c1c0d0408032131508082403041541e518421a80614204070007400d010680c95100d5008404942031400200950070481003440282d074002c4130a038011840500c09071880304100107101482410b0441910900b002e0500340e044945c122a500c04002070342d1b00c1c1000815600101e81c8011443c0760b041003800c1c10142070000e652034031f10001c444150209201090704544403a04006030900d070050092003295140c0350001c1d41c4040c69205940158248440b030750a1540200e00340b4002c0280f501d4844900f0300340544195464510340540341c001c01031620002c0811402c4c4041d0070403090b00c14015a80321a15240070381c0280c140e030040d620840ca007448100c00000c1c1912010101c4180940811440f62558601c6044c0901001c010390003070304110801e020003038194022071140310500350507035660300c0741d0602001140d034400c3e00502c6154810b010802d40d00d08450740090152050780480c446e41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 139722095 1250 139720845 139720853
    0x305060411010f0207151d0607050d090f0b0708180604090b010915121d01020c070306050c04030206121909080309060f0c04050402090a0b04030813080106052b 70
    0x11411201a100c03503945158840d407075a03001c3e02c00b0340511401e1000704440e5040500c0e1000781081e080a45c030a004142202a8500c5060100344102d428003e007140d48407480d5082c0751fa1030b0845800104002501c0d00c0000c41c140e031005120340c0c159070303c400d20325007000640e540740305140d4015807026002c1102d01c405900166641e100901c040c1070903404c04545082c6250015103190703440c1d084425513107480020300d140aa03120304425188410020b0104403800c00803102c4250b000c10f0b00300800554000034010390004c0b800200c00003200c5c03180304200401e980d03038000b2000901607404002e520607404c11400b030310010310301c4605820620b5541c4801001c00002201ca04a075000c0350120b9050001004103c42910248440c60740107101c1d82c196805442e041403180801e10950103a284140c2e80818000483d44a000d0950080c1c085507901700d41d91a01d9091148442e00700032100c541481e028400800c010b40e041c06044225000036100c82da2072020381004110444880707032070682007508401000045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 139723345 1250 139722095 139722103
    0xd020405010b0c01050f130209131b0509010f0608010303050307110d0314090a050601120c0b040603091509080706021c060611010e011a060307020f01060308090405150d06150305 78
    0xb00401c440003a51801240c80603402d5030001009a0681d19000d0100444521444000420b07646e0440b10708940c0d9988403401c0c04210707110800500000304070b4885c0951034860347d07200300582d04101c4026070300382e9a6000c02502841c141c0900e0000850080040001900840195411640c2414401c9038a00d105650314a800e9682e81420300090711031044030394072291184034580080f00c54000d011034076076545905a4920061081d8030210760800305410030700200303071100c1c0302421181e401c6ca03980b1307075443c20000c1c05072040003c03d4030304c085044114180c04440e403168030600399100f0000c0d41844a40e4440c1c01c001c1d00a1003413a507499034201402110b00e1a05e1050350041c0105858030081c20000c4006142110b8501d8815241c682c9401d1030b07000704030010300d000100b0301c40840781103603030b40d030340201c02c80c1004580710703e0030301c2d030741c2442d401104012140025001c015019101080030303036200d40c2c0543c0b450258145094015031040010130103d0082d800640c0c001d04a108122102c55503030341c8051070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 139724595 1250 139723345 139723349
    0x9030c010f09020a0b090a17031201080610060f08070806060d09030309030908010917030403090e010314060c04140d02120d031a0301020a12020d0605100c0c0603020a090e04020d02040501 82
    0x800e6960702d0701500b10301d070a101d0382c0068007101c8601800c004010740880d0a800c828040c88551400102001c25044010811280d9150440540e410a960341e80300c459928902a20300a000c2d032812200400c00c5071140141c1c0304212440e1765010440d445001082d20900c1c80980a950040d00030007246200d40c04900440201c0361013503900046911607810300400f4401c00b6040700b40030744d04100c41e20000c10344505400840b07100700ca1ba09503a030740351880e0603103c0f403066500c04120661401e0001040c0f200450301c03038a2440d00d400642e01c556a81e8074030703464948114001d035000070000403c1c0f010241090f2110300d048500c041c21840f10150240c20040c07401d140c1c02554000a6202c1484c445001c030403040c1d04a007458150f0003981001744100029010700113110a0208880d40403e03004c01e00d4002d60488401007201800303428400d016a04001e0815a080400f039800ca4000078001810501c64801c81e000001e5640c0ca030b4444c04d04041c4e80580840c00548181d901c02000500714000d681c4070f11036140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 139725845 1250 139724595 139724621
    0x1020703170c061f05090604020d06060c0302010b0306010f15091e05030c06090d2a030b1f03030e0402180324130c030b060301140c0d0e120f0309030c01 67
    0x6160254814000d1402c4001016404100059911101045410b545807002c5d260201c400d06016640c82000c00c0080c01900820480e03e41010000180190002214054079000c0d03402445182011418507030b03903100a1049040c038894031481000103805822041c1c1c0501c41502d0000862527031003100b80120b0240b244484680000c0c42e40420292404009441d100c440aaa00b40e007040c245c04002445818070400241540c1c0c8001065996011003103210b84e4000200c4100c450115100c0c02c04e03030344014045400c000d42a001c800081100d142d400c5207442140d61640d511005004044240300194000121406080141004260843c1e0b01404212045820134001025002c2c004006012120010700541c00c62a048425040030031244080102502e4105540d0100e50f00c42d00c0100340101100c0700c40c03203107207140082444100c000c039100610040e00c4010050003414090400c694031f4400e030b0b120307000300c07a5000c010f04249205840c0c059070303112341c0600070b8030f04044815814900307444040315080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 139727095 1250 139725845 139725847
    0x1020109050a1209081b01050a0504150c030e0f090114031e06070f14070303020a120504060b100f0c0f020d0807030908060106030509030a03050901020f04080c030f0c01080f060102070317 82
    0x400f5910001c920b00800d0542c0c01800850484080b0180d02c0da0203142c034a04110001890f02c41c401d004100315401408582c11170b0580007840280141020703182c000c1180020800121a03a035440c0460340030f4682c0c48000c01d038103045d03460150340c14200d44d45845010b4060180a045020054031001c031609203a0144014000d0380c80c2c00000207040508c216a040c080c01056101e21510940000c19100a964035060041c0d848281c00c905961408060800840340c4e82494200820420150044030850308265000310040c207000b00c0960b00d11140c94035050000c0c020404140204101c0c10806d003400c0d0003d850504860007903220791507180e02101c0240d0220308410820001d4010800a440c018207440c0350800140c20000c064603140c1c8202042041007580702d002040c0da254080d811503a00c046000c01142d612540c80d42c3c42c6888441c84682a4864003444040c01d14114000c59017402e018016950307180c49944800b1541f400316005020742d41140f080319800300010b60031412004003629212085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 139728345 1250 139727095 139727123
    0x24061205030403110301050f040f0f080406020a1b0510050906040b04120b01080c130e0705031f0b06040501050f030a2003010e061f030209030c0d1b0b03040f060b01020109050a 77
    0x10540494100c484c450080c6e14010400080100d0304050135082903000c4c008150b84449420b08064099030000060038403180010006911500022440710180c415891139001e2051926442c0804101e84129604502c01004035661036104000400c10403030010100da0401e80c40b0300343c0c1d125a0304590000b80d58020031440e820148500240c10500605424008001c011290000700300341c0f8400d500c80412003600c0d41c051a00c1450b00b80030b06c6000c0c200c050111542000c1c0c640095108000d0800d004045d9490302a41c8481c0d410b044044070203883c2c4c187c42d69441d1039429107a0a18907413000302540107250313072040390780c03001010500f484014086805106403a94140030411215a41c00741c4a41e100d11201030340441270310340804034505400030f2410300503124101100801d0500d8401c1e100143e02c0400144041c0400002c06a0f90b0006041c03115a10801070300d50041c1c0b007052005584c00307800c91414451034800102c031508801d0102c40c3c18030022500382c42c60f68516282100b10700040311501525040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 139729595 1250 139728345 139728353
    0x1090b04111906051b0c15030a060605090603010302100927140601020c06160503040810050601050c1b0607061a010e010309020904110d0206030a02180d24061205030403 74
    0xd00c06680c10948400070b039880c1c200f0140c89441201d109403141903018520084418042c400d00b0303602c51004d00304600205c940c80403a6400c0d403007100c010480c24680000450f40920070005c2da4810030002e01900d240da405e54003009205108a40828200304441d14017113900e070307409a5002c04030010400212540c0318240707282000e44002c208205c03a10514041000116a0b000442c1014190240d6506a5804842c040c420b042c0103c120094543c6c440050300103900c2400107140c41c000c10710348038200140d8451100444030b905c00c081c0444240e50100007114455000381c610000050301c010f21240c6000e0b041e07941c420990704106c03a4100300352070202489520b9600310b5034603083c00e87e00f4a000c02000410f90300140000e4000342c0041c05045000d9101c416a40703d0004514845800900c4603440789030000005c80658017419003420510b0581c4076a9495003420b44804880c561b01c80180a02010b00011010310000701440d8019a55101c0e81c00045103010018114000d9002d280078503691821410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 139730845 1250 139729595 139729609
    0x301060207050402070b0720030c0c0306060411070305130509130b0a110708160b1f05030a020d06020901030f0e0d020615030607120905060703050103110907090902070501090b0411 79
    0x1202c68015401040000005000e035075480b80e010b001d90070040c58800180f446201c441d10b092100305098030000804000d0290300051401d9400012402c80d61141e0b5403070184000c2d1503920806015010040c018000020b0140020380381040b41da0b0010b25a46603107800203441e4120a890800840c08206900c40500c07800c103000a0f0311406007503051140d0546291101024491410f01a02408001c294480d100350441c1550143c160442c000f0065820700d01c00300c06809900920a0300d40c6850483c2c009001e0a02080c80c4800c00d40041c81c0e040c64102c10713120600a980300024050400d82d881030001010141c5204180e40303401024000c1621480820000c0d1411030090007d0382d070b44010407800140c07030742c002031210390001461070102c1128404550380e102510380503000801c40d0240b10704202e101c5da410351101d4100c03070040a240e8114600741d8144044131030152100340c00120189810b01c070801c40d5070000d0041500c40c2d0300002d40400c680d00c03912844501558221a1081d8190b070050341441e11007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 139732095 1250 139730845 139730849
    0x1b0903030809070b09040905030906070803010e07170c0c0c0904050d0f020313060c172106040507022d010f02040609150e010c210306030b16140304140d02030301060207 74
    0x1500803d0450b04018400c0d1890164040340f901c6540ca40503180b04200d014130581c1c003000006024251120b900d8984506d07160001d000d51144008504000354180388941c0002001700c48164055615490305071030800e495206603068002e500c0742080307408003a20303030303010540c85240280090007401200c104010008201c9130203560031544140b0950f00d821091250200c12a40b079428401c00030500741c5401031001547d018900000e102c003088010320014400040b0105800c4645800301680d170344401c02c422184107a4043e40181e1141c0340700031030030303070031200180964103032060f50651000360280150035500306e401c420308100e801140400115400c2400386010b80304000c4004051004d00c0e000034410450345081d20f040248804004080c4501e8040c842c98030a80c102c1100a081c1c0c03503803001740281603940300071107160303100c0b000003400405031481301103200046965000d82000b0f10030fa0400c464002034003e448500003040c8100c0340c20810044800711541c175030041c40c3c503585840d80190070f0030020703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 139733345 1250 139732095 139732111
    0x8060a0b0a061404290c070812160b15062106220b060405040f05090d0809030d1d010905060103030e030303190e0f1002070209090c090601121b09030308 67
    0x700211418400d000c3d020f460503103072505802c403401041c1d1404000c001402032424880c440c40082c00301c000d6000441c0c901c09803034001c01190850111a40203a10070710904110301e00c40c0c10080c42400001c2c0407211481e4001d08031400001c00c1c141c21000141c0a40d0014041c212400301400d03000c0110b503511311005a021004644100d9180c0134066202c2d00011408541c1c0c03441556403041b0300b40c1e641e8400582d4013030640984104005100b00240800802059401d2030f40391152001501c64548141c10300c5200d030030132202550601b820115214050070000e00d1040040ea040d0880e10301c071030000d10503c00e50b6405080101515459420f000c1c08085c0114804c5010790410410040c0c0340e52418146d10454118035000503000229180050030f21408020345241c50198495501250403641c02501090f4002c865110b401d4450161003950750074224156a04500722200107190341d030040b40e56801c142d0000710085058850820545012001940aa0007007444200280245a8007400311684034001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 139734595 1250 139733345 139733357
    0x507050f0f060f1e070c0b1b1605070315021b0d05190507140609010e0f0709050c120403171e010b0d06091b020c0307060503070c0c08060a0b0a06 64
    0x454040d241c880c41c00605144040c1c8000d40440d0340c1554510803810445080c1060f5030300d50405d0030009003d04000385058030500c1d50480490300d41c1c01410b0f100c40700714504421062030715124066070303101c2d44060785050f100381c00303003c0700000403a80584074201b0b82000104c1c0165600300014550540d0302d8442d40c4559181c3c44542c0c0d0b5001c035500b00c021640d001710b0752130106494004000086070325204405d030090107c104500044000c010008403e4003625003d00280925086010b40e00c0e0344403103240c44280c40e43d020100801c0003910340d070303c040e420031380704001a40f07028400162070810f4041601d0841c0010000401c01030062641d00e40c19400002e40031000380b001454404402d0f013403606005086035035400041e5080c6c0842554003800c0280320301d417410301800c07105524001a4500c03241070800940101405507549140104d924820b0f00c900b41c270744034255203640008880c02c00c1441c40c120788a40c0140c60201e44c0c044108441c92146150035000b0410740212070a0080d5030700c96500100078024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 139735845 1250 139734595 139734613
    0x100501090b250204092a151d010c020d0b06030d0302030c0d050a0e010e01091203060b1b0c060d0f06080d020703060207111c03030e07050604060c0318060507050f 71
    0x3000000c2c0a03034954041c80c1807040340e0001800902104400910b00400061514040714240398280c1e03c0c3c1808460362542c05648042221160403080403c1d000102e841c52461000040f4030100d6504490601d080c01c0140940e034003103440c034a0880700981c1c801c42c039242081a5843c040159144403110340c941507007582000d542c000001d00070b162030085156120307000140100c5081d8071180d8580c130740000a04c0000304d00c03058a40206008039003615040c10702001d1640f420301a009080403503da4204030b51516070495000700c0190840c2d0070380e404e20f00444d80505907139900c0310050200d140c0403400005107840240111000c8030f103076034042e003401c0d000340700305600f26500418510200c03034101c5401b40c1d4803002032510b50400104e5500c040d03404075410400c00c0300c40e140380c4100e14910b403003a00c0820420201549040c0d580d04588500c40e4001030812050150903c1820403082161090500c1100e115454100c5411000203801c003000050002c110b00003844420402e00c608a00700c2c80142030b06070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 139737095 1250 139735845 139735867
    0x30c09050d060f020d02090301050c030402030a03080714030106051207030b0303030112020a050901030503090111010522020130140405100513080f13140112050c12100501090b 77
    0x14896104407403051840c60015814042c881e00142104100f0704011503841c8044e843c210020341107081114000e601c0c04e0700295a070312481c0c00716030140d42c00900030540a140c40d0b600300c4010b5801414030040101850b011503201c42090061800380c8966110181c81e940c0041c1d20031104440140f085c2e081604000e095410354070080100c074107540d4030003204103061045001040d003120701c1c0c0d40302c82d401c07014400000041c024040b0250198000907030300c4001d05a2044c40490996500f5110100c01c0c3c503800d200d40345180d0a5458001002d841814840f00303010612098500000c00d400301c40003400381c2c440b41480740515601c126903202c1102e0b001403e50341080d84070603076192407001c0039403041a551004a010003455401c40c050b813a41c08048142c2e02c850011080b141030f00700c3c1e043e0014110441c44045500801401e003e0400d07e010303542d410f40301c0c4c0d02c078128901415010f0904900740b4402c0002d0340c20942518176041c07181190103110140b20345400001040321800e0b43c00850000d00610074618a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 139738345 1250 139737095 139737107
    0x209120d0c14010e0a050a05071215020d0b130504021315050d021c120e100e010c080c0d0e030d1103030411040f02070308090105060a080a14070b130e010501030c 71
    0x15004070101e41e050a0b02411180140f1514140311668858000c3c031100b003140004202c080075128001383d40f600c5945041c2d0f00c240086005000b015070302074107508003440780791754040e107030f43c4500c14804290360090740c000c150500c1c0440e01030700c0142c1e10341c000c000035401c10381c07018003103440320f00010041c080000040b54440d50003406800d02c5546400038240a55071016204503058030b041d04680c141110324901141d81c1d807800203450000c280290400802c034a0440c05005c80c0388525224030750306805030001101d98001e81d0008841c80e0380c06008403040d0303030420041a4070701e2040c0e440381e90701b9100b414201403508041819000070440c8480001090207808419260042e42c0602222410b07014000010b018010f40080401d00c0c91000c6a24014150300030001409100c80c0d030020800c5071169818800c4a50f001c1c021048a50b005455110005100c84c2100b024030001405a541d01070b154125042d040c1c0c8084240c0c030300c0f50300e0304005001c00c0d000d0141e03950040209007003c0140003c40030020701a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 139739595 1250 139738345 139738367
    0xd0f050115020c0105090618060c01060f140d0c14180106090306140103020d0201080c07081306031406030309130209031e070f1a0c0f06070207210b0a0e070e07030209120d 75
    0x4552504c48d9034041c0751900c0381070b6054004088000e00000d80ca81502d003d5580f95441360103d035040c4081505038a05001052807800b940100019060504110b1003001d0751441c1c0345002c0c0c20555901c082a5001e0045031241c2c00380405644500580f0314608003c015140c6600388140103250303000c0104016540c685000c50403039428245900c203036031035005000c4540140c440c007600780500001c2ca04903402c0005c0c0c03020169429600d0401c00c00f001c0141007521010103c03846501036008108102da2403500024490704800511409490302403803401103401c022001800c0c04003901404128542c0c880309001600c040c10784500005045850321907842101014010140360302c4400140c0301115210078880300458a18140448555003811a4000c1d0741d070703520780301e0381d400c143e03411030090340260841c24420030190f04100b4408403910f0704d05401004051420301183e00f407003014000107005034610301300c5100d146035482c0182ca682c0e00d082880107011071000d0b40149500036040011610381c0141454076 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 139740845 1250 139739595 139739617
    0x50306070f050c03030114010801080f0618030706090501020403060605060c0a0210051210050108071b02060d0b0a09020c01140601390b04120c0203030d020d0f050115020c01050906 79
    0x41c10040703a4054540b44580580e00c12076000c0040042030741d4030800322090710300c0c03800c1c4c0c0c84801d90b0713070f90b408290380b500f803502c2618201360009404070f19a171200d4000c0c070032103500c0501501e01c7d107151550b4180c111114031000304d5060350007140400034000e15105000050400390792903032030003051b201035540314200e076800248601084501c140e291032158003602c1c2400e80d0b01c002c1c0e118500707100442498010a51207000e001485c0790f4001065144a40d0382c030b004c550307241c0c4e503005c1c2e685003e582049810303080948201d00c0d0903528081d11305155134403010700d0000c080c03400c801656a103903001e95600b035498208030b82d003201b0184000e014560b40c4c402140c41191384000300c444c034904803041c403a02d20000403019104240601c1c500d0401270000101da000d0007684583c08050030083c544d681580e00700c4107003001a60540041c4034500c0701c280c20303400900e9a1010a440050301c1102c6e0065603045900a0300440c1801d04143c410f0301a4603010040b0320810242424242e007000107504c00030b47c842c810480111 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 139742095 1250 139740845 139740857
    0x5041803031505060a1112130501051c1503170403020a06050705010902120c03150f0403050304060b220f0522030c0506070503070219030804060b03160311040b040605030607 76
    0x10381640c080e02d42074030250400600d01980e4551108005101e0b0304840e64040e8035000720352420790420b800e0700481c1c00080c030303400800c1103107450300c0300642d104c0c2c00609491030340e08885550440c04c1c203042d119003d40c88024100c06042c09045041130091402c480f1080d06031040e0030001440560b540440c030604640c4c0e645081541c481891802d02d0251030703032900c001d411602000e2074410990f408244c03185e00150a4045520486100740020500c1a00340d8110084074162404940824884d01c0212b6009005a5000c280440960041400700460708a06509400110000000c0b050365020b43c10b100c1c0407950092100d401c14034480789089901503890740141c0d403000b0f018010103010f0058641c9483e0400255105840e05080103001540229082401401451400c4041c141d00c0012078581310341580c0da02c8100d41d40c03691440d000780722180c2c426501d0710510032074101f500d00c6012000041c6100e450300f0031050036000c040c00180c1d010050f545200c0d03410309a05026a4074001845a44140507280032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 139743345 1250 139742095 139742111
    0x330d050f010608071403030715091a010b040f0603020a02060612160909050d0206040503070b04061e0c020d020c130b041805030702090a0c0203270d0309050405010504180303 76
    0x14518021100d051003000e0350911200148250022840000b103400700110803204001d54000c15032030344903600340207003025800165039900c001198007911015108400e99440245a1480380902c200242c1c4001e0401d200042c05122004050480c0b0008014504081d81400d00549020352683c0004080c43d01481b065814410514001c00c40424603020340c40c2c002c2c0f505600c03486010302801c1c08520503507a5204a5900d02490303840054401d1045404c600a141480c4040d510354840c54001f8209030342035500c0311107c003017800700c3c03503c848582c0346100350018071340c8a4020041d01300040041014255044101d020229440d40c655040c045205213100003070030410480002c00401c0c60409185261700100c2000040140c000000c00d2400c0c000c803001c552659440300d1045c1910b50201e81200180c00601041c507854030b00009000940b08040760200300d40003400040b60102c0006030f41940011044403041104d4103140c421030340507101c2070b6400c1c88007001e40c0e44900000103038820700070100b40e600c1185c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 139744595 1250 139743345 139743353
    0x9011a0306071107090c0302031008160303030e03130602060907050411070201080408040e0405150f0402060702060304230c0111070b040b0a09080715030c080f0c0a0c0507030605330d 80
    0x8510190811003020080119503006c010029002254403400b80700c3e2004010a01000024a54850788113013a00594445d040d6501200507141b02401c50000b03102c00e01040360544d0001072054003404260b4000e00c482d01e41404850b25007019944218040c40c86c000b041d003000310324402100e0b6115020f08140e802520f131031410307503041c2c8100d6104040e02028081444200080495142051001400c2900d902c8e202d144180d00744980540d002580002c0030403140c001030401c440596441030240f40700c0701940752031181c6c590091580500707035250341d0031040c4845c61541c0c00420080c1003450501c01050401e08014041c070b118411801140700f000c401040b0100c2c82c0d0700c20000b0b403028144041c25100159a1a0110480385840b09400c0b00460300b031500c0c007200d00303200d0900f091150306120200121501c401d96601d190340d000b0500301c400c0104454113800440e104200c16402948140400a9545008400c03240e000b480b280c013402d4031030074101c0c003040582001c006100c6013081c21107200d07514010324a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 139745845 1250 139744595 139744603
    0x6090b0714190302060f090607030b040e01090803270307081e0c010204030614070212030601120212060306010b070b0411010504051207060f0f0804081308100509011a03060711 77
    0x1d6942a14401d0300c0d4000700004149858820542c403035021241140c07100c000101042c45c04540390307030b00340d0312110004181e18841e8104154800c0090000504107002c528510f081d074003134010030b80340100004140011000d5400f100410b40f128203810749030480303031800c02981300d00c90001e000d80a20b8000c510f158040c40240300c994045030f00c100307680d030b13560082504550203900301d80701c140c440341e20307010f500f50201003402c003420700c17a40b49640038001503051020100e50981018101604000c10413000c4543d9440c144001d00d101c80148071460131510703007c8205441c012058200c007101d0305080c008080000e6070025402c2c2c1090740440e002a41076039410040380c642c01a0f0703200c168841c7c0440d940009040001c280c03402071311b4542c3d42d01c01c407468040e402600da98a107041000700090a810000d8081801d48010f44900440d00401c14021551100d100e031900d03800d00c1d149016076a8510910030503102c00d1140c50400c60094046a418040d000000790321110024912030520091052070340904070144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 139747095 1250 139745845 139745873
    0xe090f0414030304030206070f09050f0904080405030d170702031e030603010f0f0902012a031107030204020406020312060108100608060301090b070306030507050d080f0f07080d0f0f0606090b07 85
    0x101101c0d10f03407501c0e090082d61450f09840d040042140060b1107000207115a1a080c151200644412810016030060155482c002003094a0415050001180a0340c05100b5000c1e0b001c9070355605a0b0158004400c0301107400054840c6080d940100284070a0103a00c125a5043c0c0d107403e14042c1e2269500401300b405028a0605098124a4a43d2200c008a1154420341d036182c000e0780c80070311072040165903000c0c00800004104403521000c2560002074483c03d101c1d041c1518202c00d1303914403950381e03011600b607800c5030b0040801341c0c001160342d02071480c0d910302c003950000f02403038205100e0906407031210f01d405d42802404200031b02d91000418940b000d42044000350307400b142c841414a000e0700024028882c501040300c40380104400001d0318945000010781c2d040d00201c0301c614040c0302500360160ba07031042c0480c004a50313050202c2c6002c40c1c03c910141c035007d9000303000070491400c0600031200716036600001c0c43e842d03850182d0512890b607004901000b640d041070102030b520350741e909003a50580559 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 139748201 1106 139747095 139747133
    0x2010504022b14061f05010905040e03160501270209150a030c03080d06120c051e0402031806091902010503040f050d030911010e090f04 60
    0xd9411900c100d04510b102d540100c0640e0744154040c40c076030646400c10f40059040007501c0200030f4280b08200e403039034604010315080100103806510140503040c0100e5039070011220304e0404000701c0724419090821141083e83e24a8042d000c1e007410f0030001070380704241545001040c420f07000c0010031540100542e056507115400c18012070a003100e16544800543c00000c0440d44185c0303800b018500a4544a9840321183e20713079016a5441d03807140c0c2081d0341d07050350440452103900c1100d06940781243c441c0c14a003c007108505c1c10010041c8485d078002c0c800020f1003010401103c1c50300003543e03903005541465541d000104e44988051919114022080003104010341c86000119030080c030540d651104803480d03451341450207001d90300300004243d031070b90000e050003c1380804c100040000d1a018040075644008591681e0014040201d40381110011400708200b20000219414035 = true := by decide +kernel

theorem cover : BRFrame.Cov 139568345 139748201 := by
  have h0 := BRFrame.cov_init 139568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 139568345 ≤ n) (h2 : n < 139748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
