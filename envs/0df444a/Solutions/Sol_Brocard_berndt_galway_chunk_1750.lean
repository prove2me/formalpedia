-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1750
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:32:28.972581+00:00
-- url     : https://prove2.me/submissions/d2f59db8-c202-4384-9578-b5caeab18007

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 314568345 ≤ n < 314748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 314569595 1250 314568345 314568347
    0xd0207060b0301060b0a0807030203070c1e06111b0106050f011d27071809090321092303070b04050a0203060109060801180b0406050601050715090209090f1c 69
    0x1c4000038500c090300030001d184c1c4a400c18900340c0e0141140e80b001c20071284c003040040b84248212403084100d0741e19962100d469542c6c1400c408490007441d100d101244040390040b6116125980c90340340400c001c3d99440d050302040c0510b441e001e120950103079142800400540d21085110b001568091900120000010842207000d692510900703420030f8020704d108030800700041910003020b00550307403110a41d851b40000ca17607102c44503840d10361001d0404001c0001310350fa41c01c8010710900c030f420942c5a801003191300074000201d1a0440120a032900310060a20590048101d421079075007103908160001c2c08520b550728400c5903401013003e031034080050103006c01404029802a4028151503155235624205000703051140035500b0254a0710420030090040070700c0d1412910750040705101c40c0d50300c603241c9200130040244114107004041201030b0008405011100e14501c3d80180060740c0f200c036006100b80340c1001403903941e644d07000c20544000c4001c0040c0f541403600c00c5c2e490b1040c040d220008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 314570845 1250 314569595 314569601
    0x103090b0105040213150807090509040c06050f040b030c120c0304170307050912061008070e04260703020102030702060105010305060d0f0201120f1d070e0a0207030203070f08070b0109020901050d020706 89
    0x100090f4510302c450707286000c01f0b500400248c016001640c2d50a9841e07219420003e801c2c00c1039400800c402c0a100c42009010300400c0030f0b10603254170040c1d860030030760b940e440058903038001c0340c4051401d20001900c0d10458414a501500700c105082d090741945425501d24400f000c0c0c214030300300c107543d0120010b008140305404813403a100c000740404200f071240364a581d0b81c0758019240c040d08002e440300089080c0c40005140c03011203003a602c0280b11030302c0b00d03100e80c40380c0031034070342015260b00c4c11444c601c1c81c4180031002001894802e600050f504d24040f8002030601c8010b030041810103080c041480707101c0da21104080e030419013207200000100914401a2078074420b8000750078815042c52208180310a0b43d0f0301019140d401e03843c00600c410701d9624240d84446da11f00420702650070a0000c10510b104503030142008900c2801160300d0302c29643c440080184a0040403107000f43d00041e920b0030490b501d501e05004000480f800d50810b10340344006407840c01090303074996007241d0100703607038050001e190 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 314572095 1250 314570845 314570849
    0x50c061b0d02040b07060506040209010f030b18040b01080607020610050103020901180f030c0819170f0d060503011b0503150f09070201141302030d1215230103090b0105040213 77
    0x71085564550321001d90784680c000780c4040c0c0c0d60900d80310014085040c980211442248142e442d03d20040c400d200940c020040707180d106400065482040f4003055805600d2401140502c03503c118940c548110146011700c001d00c668210342225040c410003000420310402520024200907071250044401200d50544540c19600d14004204000511151f12403030320003540d00078107242c86501c0d01c3d5141c02d9640c0c0114503440001050192109010a00340240d04604203000701d1803900d0005420345491450304207202503a0f0b09603503030300c003081249801d120b03520440b882c0101c00000b060413920007030440d000003005e003a0040c0f0442c001c0c0c1c1075641c0300403281d030a00030001c0c416000e5044c02003000340207081c0168400322908126010070708aaa502074030364907069009004082684a44004841c40c480c19280104080d40314022810342e1200340003081c02602c080c0400c204c88045080d8602c5048145070b1509041c103103851303106008a1050700106044d51400d480c0035130b8640c05c1c0000140008070035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 314573345 1250 314572095 314572117
    0x3141b011b080d1d0c040204030b13080408011506090503061003030e030f01063c03120c020d060c080606040305060c030414030301061701090b0108040605060102070f1202090106050c061b 82
    0x1013642d11130003500340b140c01044803045404842e081c01083c0180400c0741b2076400081c00d070003a0440000c00d00310584004031034552161403100d08082d60b0745880d0707080d01ca4038145c501804003628018805a68845400c0b4000c01049009103121304240c0052401010b40780406800c04c01c0d0790b2940455030f18100324510240c26004020840d071550380002d50050601511206805004003814410700d41c80c20703203034510206045480000941ca5a82c500d44d04040c1c01d922001404181c0e000600943c0c0d903070480900d241c4c0a0480412002c9c0031002c0204009801840076218513401e2006102243c0005802540016501c08103540ea444500740189007000c10045261284000000401e4491348a14026001032404210714039503604c40d1400e0054580e039811060002e401b000006020401d940c10023600a01d06006840c51541c4480b0f0000084120380c000c1081200c0d010390103011410281e01c814014051480c0042c142a51801d1460301d035440605100210660144812550a0007004407500c4401c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 314574595 1250 314573345 314573351
    0x112050a15170c030a0c090b0307030f050a02010e041104090b0a080102070516090b13090f0206040b21010302090402191d0402031b091b0705060103141b011b080d 71
    0x39400120b200321a8a10304695640120114520f19050005064203040d43c4803005020407818541500e009060081c40c10354180b140f44000004581013069000055006c1d001a1002081c40d000144c414460074004074011850302208503165084c20094805403800072401281000c030700c00018814424580200f04254400514081000000164a044036941075010171415642e0b420f240111640044107580003031501c1a0780c81100a00c0d481091000d20410b004602c400c00d80e004141c603034100b500141e0703e0f00300c0041e8881d06181d200000e4805402d030490304460f1b560565001c29201c4d180508000e0040009400d0aa80358810003143d5000d802480e220079a194050340341401c1c441025502079000b40200444810b942c4031440c8145110a0050400815611100c550700d0751080c440c0241507102c2e0041c03000c400020400e0059034000c500030091007000850f0700120500b00000b4507010f0045543d214008101a60402d0005001700c1140010481c824502e040045561149101518181c0d107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 314575845 1250 314574595 314574599
    0xd020f1b0a0b130201082806060f020118050304031103031b160605030702070509090a050f0105060117070f2f25060e060a020703050d0314070e0112050a15 68
    0x2a002806030040350048424840588030080c0d90700a8042194000e80012108000100d10600c0726820a48061045003c40000f6040300008001c44540e0b4009c440016800780340440e03150b60900a110007840c2682140c0d00625166032000d681380b00e140310061202500d8019140d2540d0180191400920103504c1d45104410004a15490700308001084015620240000c0340151040d81500c3c4a00032a0b001040c2850400041101c131500040c00ca50701c40c85071030350100c000740c42407144200e00d0721f40800100f407030f08000c40058074450540b206111a508950304101c3c00030740c0034085503409404c81c100b0070010590240d8003200d03403000c9805400b0300108440824840d000001d02c0014041400c0741818400d0111110310388142c440780f00c0d400020710010790203021881d0032401403241a410707004498006980740c1d580c3e81401001014140801c0d82d031841540e5440c031a548990b4045ca6501c1c041c50b103108071030300181126000403054211242d98500085141d0300507072219600360081c81070100c1290b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 314577095 1250 314575845 314575897
    0x1e05120c010f0e030618190c050f01030c0813080f040e341101020c0111030a0e010902012c060316020c030105091c12020a0512060306010b0d020f 64
    0x10845490391070014005841201e5820701c51401c142400030024058121515026200403c41c2004600040c01d80681c40b52140c0219040b44a030303040510400e060341140389460204104000d4180b41e0a05050501c8150030806510891140c0d001807414841006c512170390801242e035000f40c001102400d5030000d00450030301c00009003144035504141031301a02d880c4084034002c6881c4810b500c1c51034590101010362071540511584003482c4002c1c40014245001825403a0944003104195100c010000051100201c10750180221740d4011000034001000a980003c1c0b05810741e0448104204c3e158010130719020a00c204030030f150300018511516400d00ca41d555080d4081d13480200c0c098070410101c9811424180034040c0306145501c060200c0d00200000a004400130540030005c02402c40801e1201e0b000e01e2001c2d14031200030760740c0d0545032100c148451865500c05442680b01c3da11041c01041000c01c8402112002004440c1c00750f00c45900251075006402186003100d07000e22090303040e100d44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 314578345 1250 314577095 314577103
    0xa09090b03071a1c0f0f0b0a05030606010309050111040620010e030909070c0501050a021308010b0a0501030b0612041a0c130603020c0102070218090d0804030f050a140304061a030c0a1e0512 83
    0xd1b081000c10084000c241c1c007000108501807081d990550031102c0007903201d40c0664854543c4901400000c40d0b0500d4400d050141603021f034000c03501049243e411200603005c8804400e0200071030340c008124110180c200d250b6039001d50340d405445205400c0024809501c15800380107104d5120009000c64103160b010000650012612036443d800c0e80b50b4002440c20050041540004014180503019402c060044000e4074070362610781d03000842008020741c41040700b0329151180e405110f5010410070000381206140c0005171444a000c0c034107011002d428400c3ca4a4001103888504005075629040800741d4064010701102940c885541c0100c1c0c0c421f02c0305003003c0b520a1040c03009031000106001410340d540502a500034001584004058145500410003040740c440542071185003040d0901240103a43d008450807605551503c203d81c00440380044242c0c07460b80210007401c01036040c500416403603103080c030610071364200b1556100c464000283e880c402801020b04501469a8076031006603803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 314579595 1250 314578345 314578361
    0xc0303031005190305011b260c030601030902060304030804201c140d05030105040c030606020a0318090c120501150c020405150301020a0f090504181101140a09090b03071a1c0f 77
    0x100b4801442030700c588ca0b20309a24041c1c9a0400b0242e1043c5c0c56070070161115400c0200b40d28103141d6280c6054000d42c1d601d9018501c41ca20955810303076240f070710345400744407030b2407000704403518071200441c00c0040d9440c07651400c1d1084a0a400284958190804030b00102d00c00d806159140100813480304203e42c0100118103890041e542480a83d6503064110100d56032407041c200140c00c59500c040c002480b41261084c11343c0042d50b41d0520303644030031105007200e6035207a98002103012405020036002c2d1074094140144a1607489050300049a0000307007070940c5082c8000e1040355564006502051150000000818050001c41d00c5e40154140504410144000c0c4800f103044a078001450303242c2405509007240004070310321860801603030303a5214050381c00c4859052181e0910026032a900c0b41001c0c10980d2b04035910455120301d0141c2c00b408407a00204554043d0b0001c9001340442c1c4801d00010384083c01403100c503aa10040d025800c40300b020015203008101c3c2c00d01036410303c081c4143d0043c40c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 314580845 1250 314579595 314579597
    0x3090201080c04030b1618180b030619020a09030c0b0918090d0e04021c050a0b06071709180c040e01060201290402040e04060e0c0303031005190305011b 67
    0x20503142c2e803048030268080c44c88000c11440c518000100c501c2180440c0256104441c24520044042960b8001413410301e508240e080c3c4007142e412006000040c061a61040c4e015009403200b411b000c020442c07403001003044071104640018004909a21403010000215040f074500c400603512080700d03c41079480b100f04c8038490072602a0420722100400d131070700d003da0300d0140100501074545500341c030218149410154460390074096201c7d020641981c5003004034000e40006410300d014003045089840603c240341c000c00d01405401c0000c0c43c0c2000c00b0042009000c011500c5030783c20030000380f0850740201c0410085003a242484545c50040c0003420070340d40c1241209540b0fa80301c10049007240e0345504617140c0110545010281d00103d40e0f0508a6050003074005441c0036180e4001000700241903900b05e8201d5510f420320841c038501406600060752040380503600d1818100184107101c6058020340d48504000240c482d00302d601d00508e40002c6901400a02c0081e49064140e070b030004030314003404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 314582095 1250 314580845 314580857
    0x5030403020108160f0f20010617030901050d09051e01050604050a0c02150c0408010606021c0c0f0b1003020907081e0601051210120c150503010b07110102011b03090201 74
    0x1200c8414900ba6484c6901c1240d49130070b160a0130050480f0081075228448003030041c009141c071380112100c180300a28061004c00425070524162100701103420051080d400e54100b44011111350f0b92081c1110040e07032420b1000b00f0200640e0034003a081001e810b5460002c403107000c0822400c124190000c91013284219400c1046544500d03242d000c0c0c910302c0014000581020011111407080cc0300d40b15004200203026078286519140410308440ca10b400031000350744114050282c1da40000d81a140081a602d044040013900d070380e03015101c0203400070041c0300542c40800a1110310307665080d00c00640e002000c1d00d280f800c01c03080c0581809801c0e902c0078a03007440440c2003001c01381f10031903140c000d04041c1d5426151a0022019019041014000d030360f01c2d5007520070006075902e00c41c0c00180300e01c2c0100e81c403c0d0128074111040400c3c41c610720707070401800700900042042f42294410b4030102030300002c81406040c01003004070300400c84940561410600814404c0701c00d9490741c81302c18400d10030b172201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 314583345 1250 314582095 314582101
    0xf0d030903140111030c0d06050325090b09010b0705011401060c0203010c0e01080a0b01030b03070303050a110607090306020306061204061a0f100e0105120712180210030b010509030a05030403020108 87
    0x1182c03d0310382010552008138410404103044044180003403d111108071000542300d41c5a0000a0030042180c800101e04030302201c00514001160954000510506508000500b147c0700400c10036101480b0b43d070041d0001240c80b0081c4407003900080805120300c50200550368485074090a51030301410240e019610f898185d201c510302402c040300b40324a05840c0e200e010360798081d03c0f80182195804950400d42c03a40040300d416281004900040c600c0394407265283c052150000304010402c5442e030ba4183d0050b000e00011503002820901581d41201c00580c2d40d903a05030100300b1612400204076020f40354102040244030050348800b08208500041c02d09082007407081008080c190700070701d42c0c010206c17500c0c0103205005002c141d0700003c042c1012820840070f803d401c080c5120403680e41010641c041c0c0341c000b1001b01c0d0310860b6400c10110500100085107500421020f42580f03190340141039950920000340c1c1c3c0905c0030340e404100014111400c2c42c9440c9080b940301c1c0c001c1d200c120b011075000008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 314584595 1250 314583345 314583383
    0x1c020a0b1015051608031009020d020d150605120c16030c050f0106030309052403040f210c031206080a050a1106090603040809060d0e06160908030a030b0f0d030903 72
    0xc5841c0d104920b00320001304181502c0d04c41a582c40900401054a040c040002d01a10503001030321010950030f40060701d4a8240f03410f0801d9a440c0d411322100381d54062001d02900350001d065460708115000d80c900203980348407682070184250080801c040d006000c62504043d4817032504410305d881038003582c00012000c4282401e944082c0001808150000014486c600340303902c03044000c0f242041d10280c0591000d5114505034820b8406884644005034001d0602101d010b02d1030201d07080c90000c1c4440d0502e50030060885120250007020003080c1140017101c030302c00d80c01036805407503510305548001d101441c005550f09492542290b0141031003c034031035180350500548021140203851940b4556541e038800c1342c103510400c4040e502c0041800a448100c9a034807070204029500d000906007030a241706540c1ea444400c4803001e04009100905215011010043d241d110303115082c0805c440841000181094840411864100031000500c4090640c441030410489015282502c191540c40391 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 314585845 1250 314584595 314584597
    0x23031b03100902090406030614090d0215132301090b090313060819020310180b101107030624090c08010e0408070203061005100306081c020a0b101505 66
    0x3076509030524800d504010300d0146800808012030001c2c40001c150703071680e8a20f4112a0620120b4000d50300d078400b0000072000421402c0000041d5000816051401c0708001011030b8008001c2d8134048180b11200d0308000c5645120052208030305c42c1c0d14214420506118003c003060203094076100c0c41c07123001c54440c06020048494801d42400e1385428503041000a8681000280c01d1001030742c00207403003600901d800e202541c02640d02c06041c41b101890042562461012840304c03055041c9880c0c107040342903541d1030a5112000b0141854030011105080c410300b17040c0707658005032400d828000c404901e40700b003916140210f90302c00d007001700194032001c4403c104c1e0a0002600042041c260040c8024101c0400e103641c014404c1d4400c0346015160f501181c01c01800b43c2c1d0b40309407070558510a001a04d4908220310000c4001c2c6010840c00e86088000d542e01e20868031411215500405003103940361003448550b10b183c1c0c12151070308070f60410614941000d106407040301303406503100122001c40d0b48190 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 314587095 1250 314585845 314585851
    0xb131d0705190e100e0c090a05010e18130512040603270305310302030601060c0b0417160b061c03120b0307081501090b09060a0303050a23031b03 64
    0x142c2c0d000c485418200001c5400c0380c0900100c2c10249184000a180600c0003c3c451003107014400c156203a400078800e00c4004601030b003080717061146501c045601900d80e201e1190421016610142168403540c0d4008619012800094810b0081422802622030120024000c0b5016954200411740e03504410007030001e4400c0d20101a44424600030021a214201a10000714130550781c681c07641c480c5081c4029080c41c0800c0f40c0800150a43c1001985828440e0500400f40c0d4105502c88801d0350341d0311085110000c000511051242c00303104000d1030940e00307507828251061811400c1e01420708110941401c200c07100d601c40c80055441820081e08100301840895150701c424403140317011800b07200608103c07455580c01d441040300000e50f40c0c1040250824024400b580d0071059414034000c1d0081d160f0042d10740f8040c2e040b0701c050286546403001500b0860340c16250503620b030b003035422040b14914400c0031301680302c20181c42c518000c1e5148400a600039040c8030805e9207035910f6203501442c140411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 314588345 1250 314587095 314587129
    0x50106050703030e1222150507030809010f1805191a1902040f140a15051602040c11011505010f0507060e030f071407080601090b131d0705 61
    0x107000500000303003c0d400041403203802c0819030f00902c00c113181c04071468016071460034441040b2181a00c01c001e01b1720b28400070b05584c086803246401c1801000d841c620620340c0c02001c0020240c0001d416410a40c80562140d0390000c061042a00c14600e00310703d0445144241e4050141182c840400c6540340700200400740d003c0300c2641034980c41e0240e11102d00c0000c009942444444000c14542007080c03000784090801c1e0169140414181b20f0a03881040780c01045a018000c0140e00340101809000d0310610f02c405486c1a0b41d84101c0d51805031004a00e4290081d045070130011074840980d00a602000a1030945000300565102c001c10340780410b02e00d00c565404581000c1d4050308952286c8020031205004e45804580174044840c410300d1688006024140214049841d0b010000f16040700398401000c6e034001d06070603041100280d03c844d01886401c801994540d440d4a6a41310420f10200005103140c00304080c2d02c4c21021200c4601c0c00440000c1c49024070030001c681450b140071850001008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 314589595 1250 314588345 314588347
    0xa0821070201090e040203010b040e010f0b180a020c10020f0702010e01051201050105160f050c09061009060e1302070501091401181506030f050a0b150d0f2d02090a05010605 76
    0x4d010000a5212405003099815541b202000402602c40b8060480324100c0078000103403500072054108101c513511b00c40184280c29a07045142c04550b48205c0d1a00107080090040c2d48481c030001c400d00e80000300110b100d2050000c1031031101d1a00450280003058001c0c1c81c0e521a0031280001103840c0d202d40c083d07130b01213642614018401544500b024040d100f00304448860301c209103480b0484507000d15101200c40364448061500c450820554194103d130041e50391402000400502030450001806031170b040001c0703441c24201680d1824800760340104104011591a81e45080a84c042c10040405840d00030104009001c582c01c14410b51168802100e0081c800504130b41c0e42e1240800124407480c0444d45800010000c01d03400141f03040c1c0e06102c0c0300280508a81850404407419008180720703056078852501907029240d128803090041e5000400130f003058181d142c0b108810f6050700c0201d0b0301d2030180442064903c2c280c0000000c850003100d107078942d640c41c0340103042074401c02d00451001800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 314590845 1250 314589595 314589599
    0xa0506010e0c1c0b031006090e01180c03060b06040306020711030d09080703200604080304030312050610050d0e030313021815060706020f030a0f140103030219110a082107020109 78
    0x4840c4c0e02c107042d800030082c2903807081e8440c0c80d030040a0f41c1464024144550b500c0c3c1006d9a1044240720b45400401404071040700e44450b51542e001c4a0802e1101030020354442500c400256108812140039651004045407900214100034421011042c81e0900038454182c0c800c42140c001c3c3c0d0968101c64005004240d002d00319507488501e43c1c0c640398101001b80002100300003559488000c2c00282084400564846141d42001000c0c6080a44e04aa150740340c801408400d49601c0c24100007035a1300d0038480c0d51031250744500c40c01040d00700d1001300d0500000c81800790a800d100d400016850003101e200c01c0d03404910051010f003d0065942a01d9041000d4200500341404800340020f01d008007030050070b11406a0702c0b206664401c81d8201e892a03035461490728002e0203403295206040c3c504080c9030f025030540d0350180d43e420001740301c12080081040c1c0c0e2410800030742d040380300d0180042d004908141d560f0365055552100c442c0c0c1d03401e212115250780902c0e68031900c1507840351a01613407000a098 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 314592095 1250 314590845 314590897
    0x30f09071505090d080c0102090a0f0305030409050603030712030506010f021c180b040e0f090303040c0e100807141f02030a0c060e01090f11040b0105030a020307020a050a0506010e0c 80
    0x82e000c400f0300d503005080c030300082010401a0300508030603401d0340c0c009607598003040204022003229400240b081046804c051020400000554094400f0204001010b07101d50001034514051020000d1901c0d0080300f14103122549a041640203810030381316a01410390400050341c441e151680c640725005041529004403500c90a48400d0151b01e40030126000c41c4c4428904001e50311940008000f11385110511070042107250742d06500c45542c1b406141141803942d10103103054914803d080120070701d0008162100d01006401c001824400216010349950784001143c00088031003c52154540303484c1c00d1f8082c2d003011000c0038010310341d07400b0390300d4103024a01c00d42d2071079030440c1d007545d0b000d0f690b0050710b50b160307024030840c08050f000c2d03442c07901d55024901d070121115208001081c012070502415040316608041540e4111400240140e2a5542c440b000c0385819107000018103980700340000e10060120214403103045c1c6000ca1410b0007143c0c2c071042214402c0c450070820038810745001021003005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 314593345 1250 314592095 314592097
    0x612121d010518060f0309160f060c06050a0e010c2c0d0f05010915020904060b130603270f050d02010b1003051e010f0e090a0b160203160305030f09071505 68
    0x111400504403410011a69480c5c40d40303420032030b1800040c1c0d00c0020480034041c000c0007058014486032444c0c074003040c00c00308014844888984014885521800440c0c070248041c0c0028500c40c42c058020031401c0700080008005200810480f4480e000c2c56221112010002ca00303031040c1c1070003429600500c0d01d46d030b66001c00d91400100a6602d550b9139902c240005280580301e181100207200050b03161420b20080104491890b0703c0505558010042c5000d0410010804d0003210b105040000d034180481c80b441d003c60714a643c41450030102070405104100f0601078050a1a0040048881c44035406030240d00321030700300401680c001111001003a02911a03000107078030484182e016070100101c01c6079641c6691003038000802c015039040d03003842003214020f40a41e000e01c500300240f449500e10f8480d00d40010000d4a03203e0052001011050b40600070022141620082d400c1100d40740e20320b0600520344d41050301c9031004005d1440109102d0040021990182c804030756003d90b000040c2c510507500307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 314594595 1250 314593345 314593387
    0x50a0803070509060d0516111b1807090e0a020301260f06040b0601030c0503060a06031d07030f060c020c090a02090109030c0801050906010b0c0c0904060612121d0105 73
    0x40140420010b0b11070345416000d8101d5101d0700394003203880c0c00c01c0c2100c1381e940407c0e007900c0000c10401c14400302428030001402031010074202e0f04900800300b600045200215103c4c00501189900c0050001d115482031081c02102c0c2616600049600d4541400040c3e10082c03151383c0c1d441010f0814800440064180c0c011209409000c40b5a0107804004039418030f20215029200301d00d9a0301000004d580502460906030842d02d00945540303070800006000d0012809103504055507280c8800407404080d440c0402e8441034411901482d982e843c00a568900a0a084404da400c280260314541c0c0002414080e03444000d0803110280da400c21002c000f074004400c16410480711500010210303140072940300c00b8007518400801c240c0740101c0c4641c5001010f0b440100700001c01c01c036090300c0e44000b2900541019080714041d40c4c2c1d490741c0c18144003030303c010b410910240900040b46401c12001c440a08040e084c0c070b41f100b01003e04034005041c0d4592411211a0218404000c28040901d42d6011041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 314595845 1250 314594595 314594597
    0x306021303051009030e0103091e0507030503040b0d0b0915010c080d0f1506020c03120304060605040c021006050f060d09060204090533180a09060c050414060304050a080307 76
    0x18096507600c4081c60301c0480802c01c240c084c1d840001c2020325900500909844c0c00a08061000c41b07482c6c0d0350b0801140101c0404201500d050051008100b41030040703100440e0420122030721280c481e201c40f1001d901950007a00014600207104c641030400d040114442c2c1ca604002018002d290801520400241e040882d203910040003901341e2103a541c407a010031114003050000d6180001952202125901d40080080d940300d0400c07000c17140c2c0e00142e03040611520b46000b130b4a170b48880c07400c50064403041c1c02c0203a11604280e9203160080d80000c440308240211075040c070a282d940c0081c00000250100d81d140c0080040042c1c4903451460f8214400c1035228020051406035107e12017011076400b500c006019410030b0281e4841008c040d458440781701c28203001098011050070020b0020105513107240d520752150303400942c5090b080d0f07011842d81500180240710101030341c0001080f56105000380c3c5401c990901850b80380742000700c140c03842654040c004002e000c0344c42d20380b03484a03000181003034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 314597095 1250 314595845 314595877
    0x30509011107051005071a060a03020d1a070503061009050901090c021507080906090601050904020906030f07090606120504080904020c190606060e2d03120c210f04030602 75
    0x111604c60341c01c0040c0b141603e0741c40645034150b52800c813a05040100200807160131160a02210b0307964880340c801200d9044501c26070410a07407070031409601000070784041e188804001c020a95820000642c03252004031112001103880c880c007524448014011107800c032103112700600c024816a481400701c0071850041702c1382d8102c01700403071040304030460f000310020741150240803241c6002c02c03404c0d400038a4940509101e606101c04501c036404020b2029105501c0f40b0089a100c0d242400b203400c8241000c015104490380741c0120b000580301500c5103a00041900c2103144004c0080d106050007140d1100c9114030308026103041101a400840e04500b9501540389030f40720f062010380b84e17900090720845000c2a040d2410501902e95024469040c0c0180c1690307501b1660150103420015883d8807114018000740c1c2040042454482003401c0c8444070400042d21440341c030000104072119618036200c070005030742490b00c007600900600b0000070480740144000c0c00080c545401601c0d5005c9404413070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 314598345 1250 314597095 314597099
    0x140304062d09450b0a060f140d020c0c0a060f050f071109090109050106210f0816080904150503030d0f0f230a02090d03080a140718050409030509011107 67
    0x3060b4403c3c2120f94401e001c0000d40c050700000010390007450f0180d0340c21a1151003461074010301500304001c01d1307021401c11089080c640c5100d03000308142c0d10030441d1562300b1500c03601c40031900c583d6032005840d000e2003050602000940c584c4209074103c4404a941e030b5183c20a024001031688c01d0f00f00101c11508501d070350903404083e446000344144100b80d08000402d511485080c40da08645550b08119030f2215030140091141441d0000300a02603031000e0b40703201d90025414140b04034001c680701c0c010b40070708a08081c418001c080c405400b158030102d40070415120400007a03045400d8610605405070024010081c4006084c3d02c60a01200103501c003268802d200e0780707007070b0171a01c007400c40142605e410581820346110300c0d010907a1003400d51404614040c40c880001d003e12036030600c02420460300d00c000075056100c039080301483d5000401c64091501305518080c124074185c500031400105007100c001780e00c2c80c09005d61030704179406407906468120180011a0080043e00402c0300b503204e01100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 314599595 1250 314598345 314598419
    0xd120509100e0a12080a1104050604031101020a05011107020a082d012003011412100b0127150512040f0f02100e0a06030902030709020304140304062d09 67
    0x8181309250195620030301480d0413a0303148119801f82a411265800611062000f80c03a100c0407507055030342290302d07820842020030041b482c202c0460001807065003098030042c45018841c001c1c0c02d90707620840c0c4610741c1503200d0504c00da032041900c000b0f60030500c40300140d00381c550092000a480710199000800c02c25440c8211070300d0b03440b080ca400310000c40c001004106403021fa9400341c030f6240081340d555000c0e042a0280c15540c6640741202c85a060351486820482e0b80242e048a0512890084061913002c4903035407103924030402e200762112091100c2c9107411141c4034104407030210340c400003290b40c04c4c2c41c0c54503001450040010121084081c02c03020402503a1074020b0704200c07c40303d40d0b80321010020002803021703080250b4040350074103003403040c0d081c0140d4010031108291841500c00603201e91b6541442c29000001d0201c4041303a000008022500980c003400c03201c210307120b984040c0010448003482d080c400d07401154960001d500c4520511003458000c5980c00c0f6100182c61149900d083c00781 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 314600845 1250 314599595 314599613
    0x9022a1e060403030509060405060c0c0f2a0901030c09050402010302250519021f140c0d02061311220f09020a08010204030c060503100312020d120509100e0a 69
    0x44000c52940104204000c06a140c010268801210405043e460410b5603880d651484007400b40303070345071234040b13041320903504100a20054100c1841c21030308440203c94158880700c0078028030b8a03c1c071000000c0c514003404d0500302c0e24100c07580581084c1d0394500d048070f0f03c001400081d100f00d0402d1340800080243c1d1804942d90204c11a052650039600c0d82c031b519107180b4160340540f0000405a03441d1882c03002d0380d86c01700b010b414030220003007650b40310740912000c40c0c0c101c09483c66541034600c0440d503204998000038074021103e8194003103800d00e8aa81c9890700042070806002000c0540d03400040045041030303c0d000c0004020142044005c03ea0200790b00c0580b442401c0081319a9034543d07800003984ad0a03134900c3c0050070288000c600c0d240c2140c44910004102e400351205000000010802e4003d044000c54001c54000003d01e000e0312402500a44400300391904a00040c141e56494140840510485001e02000401422030400b21483c3c81c0c041c04003000c60704080c3c0144050900411441c034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 314602095 1250 314600845 314600893
    0x1f0612060b0a050102121204060e0609031308011b050a0e04020c0a031202090906010c0305091f020d0f1d062203150203040b0402120307051f0609022a 66
    0x20408a60340e41c041c414410300d0007443d4841c81c11948503c2c3c0c281c0200800008039444800203040c08032007030380c460801401420148100e100d0a1040c5c03000c003c103038a4040051b1006071000d6003544110b9665100440c03d8031031690000884150a03001c4604075400340c802806040454100401e05454000001b0101c1e081014240c4070342d040005500205644001200815913103500f0441c01c1c134039a41c1c04900515001050a818450301d007a50300d05244c0114107841510b440280000300e0010002c0f00035220401c059003180c00b52042410600308140920140484c0070195a502001e415407041a4003c5142524102e90030040822003070380c06040648124400105001c41c1403080c0e4690303d4178a1503004c2948010510364814801c0c08001070b0070052294210b901141d80d40c410118400c03030b5038150302c20000d00800901c130f000303030590003400e22080f6550324918244d07041003482d0b903c3c2100030a0788140006158850750045804040b441107107024403507141c2082c1280c1c17000003041e07042440c8107454 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 314603345 1250 314602095 314602103
    0x1c081e01080c01020f190204021c29060a02060a02030c13150e0d05061513090c0807050a0e06130209030604081e0c0d0804020f220e0f1f0612 62
    0x108002c0050f50301004007401e6029410002c0884034000d4001d603081d0303d512007000b407140e5000145252451056030194620b401003110400c0300e285402a40d1001012030745210b083d14240034035200e0a898404241e840340c94141d00a0942a99201e1480c002940000d104203c040790a0049034506060308603002c000e03040c10184c2d001c1088201030080c103101c90303103901c0c54840d40002d04100009040402e50542185194885a41440011001450304480c0f10712550546107400c0c218030611a900b610902140e03c403200b0b491140d9120740501c4051a098052441e45401001c0480c22904152141c0640d22403200b200500b40080d01e03001034241582074400792001c00c008142c10011500c03080e002c42000340c2540c000c80c03030150b64520064a4204400400c01441a50000030341503441d8929000d00c90701d0002c148541c66003103607601c6024404140144040186040d0a041c8144000248038002d50412001041000c8503000306680403000044440c000585407240003403851481051050407a00c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 314604595 1250 314603345 314603353
    0x31d030c0a0c080309060a05030c12090105150405061c0f06020708361011060702070915050109030206210a0b040b0307030c12050a02130504050d021c081e0108 70
    0x2508000003441c2c1950400e450a800401080040d641c030300c41102c0c0c0d04d5005040540d22550342c80104480c1d03000d100f00341c94441d81c42d0800c000365a0302c10b50202e40b048a170130460803200b03010301042c801102e001f1600c95030003a0446e2008862044503c804201491240510034000b00550b5100303401e90b0080e1a0071a40a44042003841d841700041c907945d44440c4030720301d03015070603800b0a5a0100c2a201c1c209240d008008091712041041d01c243d0030f200700107151000300d88143c1440d103402960340c1d005114480000c2e01c0c0205643c8400115402c2d9403c40703a059544601290541d000c02403681d00511001e03c420401400c0d00d14540c400a000e140324500600700004c0d5850041d0600003034600301e40d021071094100c1e0740103000003200780500340156031703902407030658001451801901d4850821400383d40462440115a24000795030860752181d44904262244009010408d0783d541540b155a0590302a2617201080d60314401d201503680710564102c0e82d00e404d100d4800280c040324082e0804000c6400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 314605845 1250 314604595 314604613
    0x16051005090f030f19180b0a1d13020309030705070303201516020f01050c030103020109080f060712020702040e150106090501050405042307050301030606090615031d030c 75
    0x40248030700c503502c4102c14040d5180c1103140c04608000c2c030820245100e0900d4a550302100180b03e0b9004080030600301010141c00358461100b410f0b0b641103980d216001031141d6003d000c42089800a101140801a12441c03008881410000180d0070042902110340300522010012a404201d81c4005500980707031540d540002c201445105074801203104136681c08800301380c1c000d41c04410015803203141410b018129425185080741030041100200c82150300300401d0042d403e0701d5000a5040328801d8842d40075155a40030250340b01c840034041511160050800140e150b0f02695403002000ca44c020018548141640040d04656102d0f80c4219290f004403100d10880700c0c500205030140a0034209103207420b2a06000030b201d0300c00c40c064580545e8648000c403000e1107a200c1d25620300458640070361558034184ca8018a103030403d10080d10700070b00703100b0001000300c041c0c8100300c1942c40031070032002e41c0380c80000260081e1200c861000000c00d40d8000070386210209201030010310640c0009002650 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 314607095 1250 314605845 314605861
    0x1091e050601060c0302060402090c04081204090b010c03050f0d1104060e133c2d05041707050f030d02070203070e0708061e090103030f020f010b06090616051005 71
    0x2940507001801885907218480c40446c3c0c000030b40660141e41291b440c80d146e603941d001025070b402541d20284075440b40d110300200c0098000e0140003030b01e906010030031407900b030355004480001c41c040300a400300e0303410804014039000032001440520194103010070720400f801c080a1450b03026521850018005242c0741d81c06180080038002c09101006041c8460303180460f61030409140421020829290070983c280b005214821542540d495104200b010900c00122503015400d050401100a0514079480707880c004a0b1040350300907a0807002c41c0f000b640345030710840f02582c000c620a5859100c3c03404205c00d103c000f000240011100313400e0258883c1180d01c14140781800e01d810116051990038108101a688074040f01c1d8402e00469200241c00c140820008650328520091504600c00c2000032050541201084518581c075a00b11480003070f000810a00301c40c64140b1556110b03038200481e07005850020060114804c04000c41140c0b0f8000c0d0f52070341e25010812403013019542d140d00401440c3c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 314608345 1250 314607095 314607103
    0x6080a061802040e0f09030a05090f0604080a0c1a270907032711010311160c0e180703021003020c0105100e010b1e28020703151503020f0301091e05 65
    0x241d0305e100e06000c3c100b00d40c95507140d004503c25182005004202c5406599407540c0d00380b1301d9100500f10994440d154a9805d8441d10f507003070241c1d144a40c2400019001c08803c81001c41a40c04d00701650910811030074501d0000480c240100342414203a40110320303980c840d00780d1800761020b910001a0035001c003048007031440ba0b0700801c1d40c4805040c0040008140741100f40c040c800400d10300020070319040c0d10701500a0041140c0c20a42074002c0e0092010400c00440ca901501c1a01414400070b075035003c1c81c00311226501c01800002e4100101c03c00041c10150f606410f0141039060140c18860000851402c44404680703661848031414401c008a01d6404503a5014100f40341a11f071070803190304216031002c40000004d42c107002e40010410701c1d003200710380c1c030701c12181c00e08421845020384080025a00c082d180015a50020007050070386004200d4481c900e0f185ca079481044000d2803564082080e4411881140c980654032100c095001802080c0e441c809048100b186840d070f400036081803071038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 314609595 1250 314608345 314608351
    0x80f1b071a090d020c090105100908070b070501050a06120f170a0305060a060305010506122a09030105070e030c210601030c0303140a0836010f14010f06080a061802040e 74
    0x25500b01d18842c0505d84c6488600318103480065440100313101103121708450001065000d9040e034042c1c8540411030907407400c020b00d80c1038024402845603450b11482030701112041c0c42007006100907000c1203000240c21450440340c0c0350040025240f64031541c1042d190613880200b682c00026079031010040c140c5051181440985603500c1e04200b03644c100380c0880e85c64480c070b810101751014014000340c802079141204c22204045980309511403250281110020f030092040b031840f0f9402d11001800c0c003840780364481245100140181041d605035000c2c06402e80840094103400b44404440240451040200e90f0085200700c0d0140c00203891400c00030031110342c54410f29000d4004020622403240d1000c48640c0100029600244880381c00c3c0300c62030541200300d81d40708455076030500000356078019802404241c071454000d2205456032032000380010002d0107009010400794905010151041e07101c030340d20810000c1c001540988441c112441d5446100c801c006003a000541488041d80c4a803007950 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 314610845 1250 314609595 314609597
    0x8040213050108072414160f0818040509060c07020d02030604030f0f0302090901060e0d020d0308011e0506030c250b04140c011403060d170903010606080f1b071a090d 73
    0x441617142c0038004280000000b03440125403004204c0040c2000d801d810309000c1a40701c42442d425040c18034000740c0035004000d10640754090342c41924224200f038000c1078031504003403025001d039a0b04d100b4203610076040420141c4c0c0202c031602501d4010384040180d140903d0282d1150414070800340b100030841014000d00c8030800d801444030141a40368103642505507603c07418a09404400000815100d2041540c0071354404110b0302d0a200b81030300f1100c05416176015504c006503650601d440400c0110441c410f058024000b00000f800646900000d0032500b600326040d01c1d007052103010b400313103540302141d02928003060350070921081101c0700082c105130344800e5014050b88005031002070591a0301d00c030f00c0344504400000048460f620b610861a64551082d403030b161070208100d4400e23058000010346802503281000104d1964000d0001600c9101921500e54442e550a21448000e2045452110340e041c402c2c07140d0b4001445166041108140f44000c0c10750302d25001106902d01405030102c00c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 314612095 1250 314610845 314610899
    0x30e01121508030d0e0307051902010c0816020312040b0702040e0106030b0106020c010815090a050a060f03031701050d08160312021c061505040306021c021303170301150804021305010807 82
    0xc0009000401e1f2400070f8040c0300e001010423000c90004cc0c5108281010003000d41c0c20000b40000115440040404814001e0b021140404405451425103101d01e004003050000c0034040003005192940003d02450a83e40000ca0b60302e90360344d00d030b0059070001c2e00b0100244c0c004007a0b0004950340900007585c42007818080b10a1781845001244210700060044102d9946500c0014280801d5401c801c0003008100007240c0c42690700d0a005008500340082e60070385030400c000000750b524018604616041d00580702501e003984049600e4184603a802c0204c0038090215407180840b00d42e4405030141c101c54040c0d500ea0084130a414030100c44158020040f130221410321000c1e072650207816a410380364042401070b501c50301940c4200302c0001e80346131261060b00008101e020310b146904184203ca1041c0c00c0c6500c200108669514140000d0049402034158002c1240195118a9100390414005030940c15194071141120701919000d03041548035500010007005a1308942e594a690714000031081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 314613345 1250 314612095 314612107
    0x2151b0406120615020d1403090d051309050a02071104050c090d060e060c04060f030902180a0213150e010203070809040b0a170606010f0c030e01121508030d0e03 71
    0x4505640164007071041080884204160062140e0344624050036124030054015030210000039900c10000605070001200100d01110340344403401640d00a84240002d89624500b9031812658bd400c0b444000141019820001072020000c0c0b280e1405024280d8015a581c140d030304200301aa4405100036014520b01800c00c01110000070a84513050011610f86551866605098010b441d908090882038001c5e0720502810041c45070040007150101e48034070a25000e0804282c04584042c0c1020b5003100b140e070140c03118200c0b070a960365405800b0081c0142010a203138002212464150070a41c502000c811004155a40218910945810910046181c40310560703400d034880c0518840d0f40e0140b03444041804c184e07aa6030320418050100d00c0d450802e1001001c58560361010151001c07030128814480d050512880307059281d1401d600750300c5240181941324011a045d124983c2903000c2f16949003c0c80d801030111419540c002d101c01802142c03601400160101182c1c50014140044c0d4010045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 314614595 1250 314613345 314613391
    0x332070617090a021c1502070201020c0901030305120c0f0711460e0705030a0c08040203300a05030123090403230403050d0f031e09050a02040c0215 65
    0x5400440341d8180c5103240f05d60340c06526000da40b0240140208a5070440c031000050b56596400380071540c1c000d0342100d032135054490074042400300a0001074000745c0100195075502140c2e110303258000003520403080c94009101001290354005190844d40311a00b0342d04145c0720b00e0f141401c1d101900c03e43c00841d510b4140c030003590143c41d54440c1034012a00e407a0403482d0520036529030b450028440407982109074a0104001401035204540700b140b414034000502e01154030850070303a44603c0d030250043c4190048030a030403202c108811121b240d00410b600d6090392058419000e40041c00d05502e80d5510395041025400303418001c01c05040400c0840186d6004550718415140c0e00f00707405042c080345c44d110205c1c01c90384103145000c000440c040005000410080001108066088551303500d2095580214044059030034420f5448004040410391a580e0f1869034010000c0320300c541c045a43e04c00d0a5808203042d6031076440c00802603040300301500f07144000600307000d41c0030001e401d40f1070b400c24000c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 314615845 1250 314614595 314614603
    0x50a1406010807170a02090f0a050a0b010c0308060f120a051911060a02010b040203100602011a09070e0a030506042f031005041406010e0603010b0901050a033207061709 74
    0x100380200c50141004902d80e0007001d005d8811050b4025142c241c4600e02481c02040c907580941b00713040301500d0803000510b19101442055943c00e0705943d02504010300c0c1c0c404070340d11180600035603841400c441c00070071a0344e1445089081006040090140d6048504089041a4509e82d144070001e0201d02e402c40040d003d035074041e15134482210110745841005908030300402c44000c00301e401510010a1184400c0000c56140485115500070b1003c980c41c420040c100105440301e00f034000f02d5000218a0450084050b100c0c144006028240081d079a52210361901ca81510191001040301d503818030000c8282d00d030501c5003d184024907014100b03103408a60f6482040b06013000d9140d03100c0105003040100c1c0044c50141810000300e40140d61100802c2003100b1041d03450a102c0d40c40c0c61000c800505041400333904030b0744000c0c0803503005072441d220010704002c001030030801c0301140d10031a660404080c94402e03402d400b590003442d601c1d040450241010004c2d0b5041c000402e168000c000080300e00003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 314617095 1250 314615845 314615849
    0x50c0904080c060a0207020a0504021215010e030a110414040804062307060506010806190b030a0b0907020d020c120c010c06060506071104060b04060f050a0e0d050a1406010807 77
    0x9502544180d40380d0400c64000c0c040d08032a052503024030014030240b018541c001e403202c180200c4111480c1340e0355000f00822407043c800c07103132000003070000022102d448070840600b1480c0c2c1030411260851518000a003024426a0100d030841040194080541090311a0f443d03643e8a0a81480aa0900f521402207501452007240c0030081411807200022108110b00c0316014150380c90340b0346a100500d00700d0054481203860a00242180740090308a240c481080c01c03810f882121000c2c2a50308140312420260f00040036140f0807600c41c0000d031030715101d80c223020b441490564003034007402c0310703c0c03c0090502450740d203050301c00c40700c012080301d03d0503022071241c1e0854000d090455000c4018a44039001d0b0000b540056840040031404401f803103010b10540c0e1030010212020031409480b09a01d92090040740122000602100c4912103e01c1c010001080c84110f2420181e07441601ca1001600a8000007001c40c2c00c2c0d040b000c490b4040200400214100540c1203001e050150305005680781c3d101264 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 314618345 1250 314617095 314617099
    0x603080705070b1c0c0215040602030717010501090b0f13120b0606120f060a051201020904050c0406020303040f0c0f0306271106070c090e0606010908011a010806060c0a031e0201050103050c 83
    0x4c40341c5d0400c1500070000402a00505420180203190a044c45002504100c4e04a000704002c0074603215002990350070203040e81c2c2c0c16151884120304040010015402810b9610b84102c0c0403c1941c00c01e00e520b001c40c0009080b4121016070420803407500b90700c0e004014000c0d074040c801c1889500d0001103074006140d4031544040500307015641c4d00c1d00052400d02e4030780c4030f00e4003c403545001c040c401d90190014101d0410584052160741c445400310a06882207110f1000160001d0001c200041c0309080c6008000e80101070400c51079884106180301c0411650085650a580d203100b087c8191002ca00c48103001035244500c034020305a91a0384000800d10217109104005c0050220100302e0710b10349070b07070181c103101c02c081000741f528a4665980d02402d40d40076001c02d0409000141c1940c05000d40e0a460b0600210782d200d5110401c015074040c0005042c0c150301007014007510403c0f00b01002032610784d0b4000e5950021f0348115640c0608030114014041d0b0459041100500c041076000581260307401c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 314619595 1250 314618345 314618351
    0x5100912060c1b0b0709060804020607030509061b240915070318060905060c07260c06070c03030b03150f090f1501060815101d040603080705070b1c 65
    0x100282111060360b4040480d100da0010f000d903c0902080b900081d10840644d200c604110345c5130001960803801c21200258030801c200305d1040024070810181145001c09010641061002c003480c06800e014011000980d40c0403048555074001031a440d144411183c80000700c0394100b611a2507101c2800034950240c004914010410541c840d902521004171707014049184640c0790701d000b03400340038608801d035224030a20002c01c103c1001941120802648903009009680a100d078075030034a00d030110304041d800414081c0c0e100c441414040c49200c0c0400e0b60325802c01180c0d500d0b0180850f000e40e02c40318004e0f48a00e440100000300c8050040d0080c40500b03200503540d03181c2403010300d01401046031034018051a1a1013a072600d0350b0b41e4142c180d03003040d2204103040e50342d401d43ca0094030340c1d905041c0d842100c02c802192104c1c0109400b00031803200640b0440000a0400854282c1f105580110741410b070003d080010b0040500c08040646800c00c0703014504810380402c4140d084050700150b004540d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 314620845 1250 314619595 314619611
    0x142410021005060613030804051305060d14070509070e042d0f0902100f0318030804032d021e01050906060622030f051b01051902250510091206 63
    0x1451000fa200724105200588174415102e1803e80740a4200c0e2150f0750084183d2000c84135841290b008551182401030b20071440c0101c2500c03540d080808030810002c131030054140101c2c481d201c80365144e12a4405442e803a1000a5a1083c841203400c0c0ea9040404c45694424110424418142c40c40c0182d036046000301d000034600031450700900221760002d41c00203c44010801e03194000c07641c50040d0003281c4040155000904c0d1580303000c0010000103000900e40400a03001a000e644024410162440600f625400c50100128004030405a9101580c40410640d00c800c03d030341c14015110a040000f17104c581824500255290030203041c103032180401180340180520034146190702080b907440905001071b03070380c104103100580c0700310f081e6064003600510860030f41500300c45100074641030b561035260030703c411000032480c6000300e410001c5000c0e1080f03d1040103c90520f4019582c0780e2000303905264070b001d08020303043c151041440140b10103c041003105003025052419015000800418154 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 314622095 1250 314620845 314620849
    0x1506010203180411040609050a0905040203030f0d02093a050d03020c0a0602030c09010801051e10180b031806010605030705091314061005070503090d02030114241002100506 76
    0x82940052000040b0022030005011540071841f501129000d440c0340103941e07100e1034080240c031800c80d000b03501a403041011021002c040c00c000d090303500c450200141004090070001c0c46042a00510000880d044c40b20a84070b01d03091252a000c0408031304807a1290740260340c40c103403141e05140703c0d0028194045819284580144000c900603540840d046560b4981074210031641e410140045002510703000c0041020700b45003a10100c0088506007840b030501c0407104001e882140c0100c0764041049002c0c0c08090316505450f00c80c090071141c4000f82d164070380601502c10513048400401000e5200a004008840d04481100e130440014038040b56070304d02c9480818101c81c0703900004807856243c404404070010000d00e40a008134421039000c42c0e1050724103004c403594059081d000d4401d80080040301a60f244c480c078070405462018002007186040c0700020036016004a4264024012000707200b4a068645181c80150840c1111400503104400c04029518041454620026560398000c61095 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 314623345 1250 314622095 314622101
    0x801170c0307030804080106090212040b10051507110f0901060509012010150f1404230f01050423090c1509040e0d08041b05190815060102031804 64
    0x30040902220102076603444c0c4401c0c40e500a01c02c54030654600340010419490314000c552114034090348051064035a6180e80600c40030140c1003840b51801020001030343c1e220303028410641100701d00c500351546c0090409415481c000703907d1034072410860184071060380d83c04004a0640d03c031031426644a200721030050b1000c0071107425015814003460380c0f000f81c0750307400140d08070200e94000c0c003031200e00c4980a008414130002c0c000c149440d4000e29040c031144a500d1203640c1c4205c40100702080d0341d01980305d05409403c440010141000c01d1104229150359960151801454155400c0000c5030303113521460004165840e1000c180b0307241c2e40201d18411020003507840d5103078000386010780058610150111070ba02458070140a1420704002241106021582c00c0080426484603155562156076208044244584a109808048002042c030361a8003080300c1c0d0781c1d1503100d0001000c0d42011052460185400c150f01d0080003d00c08101250764040250750010010491212000000c0c1c1c0000d805 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 314624595 1250 314623345 314623363
    0x1b040b0c0109020d060504020127050f031e01020714060702030f0c1c020601090f05010e0105120a050102070305042105150603120c0a11010c03210914010912020d080117 74
    0x4c8075210001c20f40a126056102d00e0040f8800d803101c1290902c42e010480d03103400c10020315070304001684010052420650304081070350200505a8040183c041460615003c2d07441150826a43c00301d0100b04104003608030088959401004001c00e00d40030358006e542e44120086821900d1010501d0318480f0010861700703031054040c3e4080244201a400d000359108403d22500030494106515041100081e20805040c1e0b80b103160f1001c12a800c0c0820b0042107020b0000c4a5607910801011002180080c8054898180f09596241d0340d1880d02945c003005e410580c2d0514a118805003044002490000700c0c07250340c1018001060039681d601002905041c401e080840ca200000205c0c0710f1350480115a4506c118424480d690000b24084011500005113039001404030b20f0503c07540070075440101a1100841c0400004140d21303440380d0b039440fa0300d10050740782c9030580c0d155030703003c010488020080a81200e0038030041c600c05030f20907402450b060303040c4128900203101b44c0140c04802814054603074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 314625845 1250 314624595 314624599
    0x2a03090b0703080906130c050f030708070b040501031a0609040e03040815041407060807210204080d08012102090603010209040c0518090c0a030b0f0a0f0e1b040b0c010902 75
    0x1e154202401c002d010600112544042401250300141c071020780300e211145141d400028010100d42048180030310800e0540321103030f1504c14584c0010301007204200034000380c502407561b10b4a4503d000005025100c0c0d0f5079002c1c1407083c60700c80030b907204e48401c02a203462900032a40441c0c880080300c0030a085218940202640e4060140702000c126007800b512801640b081200c00c050f8050a800b40703031a0060b600601c0c00140207400441c114600c900c00381d100480c4050f002c840800c03c0e4116036002c80c2d2190788421503d03000304e40030228068000b44294010b0007150040340e2645900501e13001c040c102c7d154000e20a148140c08034840751000d506a507091600500204241400c4220107401c170b400400107001031500500d0000c0d280c0c20084010341c012416500d0180c10106054800c2e006081183e800c2c1d90480c94150a400300b86d900c0645400051601071044205582400041c8440c3c40c1c0c010a038201441000c8004007203034403520100c4003100c2007419246d444076051305150340034000020340a5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 314627095 1250 314625845 314625847
    0x60603060406080102030c070c1505040b0307020f06010609290d02070f020307240c0f1401090512030a1a180c0706020315010908010b101d0402040807060201050105012a03090b 77
    0x101801c1c0801d00104030323050048075001442c954a2290550125004100600041c0140b104004c0a903006000d9030b0828100d00680d65111007045000d131611100b640030300005164640b0401c00303420000c80c480345100402d032000b400c0c2200a10085400c1c031407814281d255550028004040c00200300d00079001e02e50003025580860343d562514000080b24074240741600ba020f900c8090100c3c082e60301034151640c054210221b0368071944440f001e00c6030101040324a95211800d0a0000b241405549a1195010301c556141d08181e5034800031109600c500c000c0009007134090303a82d26600e05d043c3d0f603403581c41c640b1494026076900b0601a03850086030380041140b80040144101100c04a2035128201003e0369034851943d501d040342800c1c2c1ba100b0f40219007000c0d00e0b202c2c1c1c0201e244103004038003486001850804011240c1e03004207040381d00c00d40c031402407600510310501c82c030780e42130003001d005210902c1d02440360000088607002c1c01840010090403022010410800c06008140c1c2000800c40e0303050507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 314628345 1250 314627095 314627101
    0x70f0302121b040e0108070602010c0206040b0f0a0209041d010507020a0b1f0e042001260a0e0a0f0501050709050102030415030906090302010203311e0b0112050d050406050306060306040608010203 86
    0x340c7d031a041409294090b508048003064558800510300784900e4100307203101c0982d2514651040c44140260412507104d400b0080598180c0780d5011710007004441e002c260481401c0ca035907e40c2100c0f4050000011500101e0440001c18890442d81ea003110110f0300ca01c3c401c0400005c9280d121003141d2003035503d00a51400c2100340400643c0250500550b4205003580c81062001101c801d00012000c510210b040c400180d90300001080041c2d00070440200002d0100c40c404801d85040c0704050221002c81400208000f080402c0c0100c0360012441d0030106146070034140040d407640501d0056129403400d14515141c954400d81200e010305802c6141008030300c445050090203548122204501c0c2402e1103207940b0001c0440031181c101c012184040b0f01c015074140d40740081043d0080c4114610460329010202181002444a000308241540c1860110300c6180080c1002d03003010781c403814080c007070004008454002c41217079801401203074040c0d560307a1048001170044c0b515801950f1a58404010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 314629595 1250 314628345 314628359
    0x20d06090510030308010815013f060605030604020f120705090a051e150402070602090402030a09020114031e0405030706050c0405010e041503030c0c0308070308070f0302121b040e01 80
    0x40c10341640c0c01381e510700300f0580c1c031200026500e10820324240d8203000036600410203028400710301d40d0040c090008511410401a0291188241d0f5080d18440c204500f00b140b800c001e864420b02e00100804c3c0c0c06018589030603000141000a1a42407500980e0300c10300701d200400d024040360000d80001401644a130030144c654a0007040f0132501007111090ba12405900b00f1542c22840f0b100d01000580c0c0d4212160503020b000c042c2d089440c04441ca40d4083c8034200140d540c50020354411120440d00092a0500c2d0000402c0c545150060b2004684108180700007400c06542c0940c8005450443c10001d072120b18026195100b081e00242c00c0340d15100601800e0840781c4d00600c00c4a100740da400d45110700280810040b180204c480101c91903034500200300007030080e01004420b5008492101c846583d80d1140102c81e40002c1d0b0460014500c003040220040e008410040c081080303207800c505004a81d1448807042c1c6c0c000d007002603000d540002160118111100301c41c00713080b55000056039941e56540c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 314630845 1250 314629595 314629621
    0xa2301050906182503050402220e010207060b0a0f0617100504020a12050702070506120601020a0c03050105041b03050c010e120316050d050c06240d031809060810020d060905 76
    0x4079800c1038100401354060880e02c0b0f402458087d40c1c000f86000c0721201c820140502501d80d401340c041c1e500340c4400003180182c00c284054080d072400382ea00411442199401c21055080079004001e099401c0f44040c4201548084118208508803101d049070b038544034182d003c0403181c1d078402a4070074000284d090495a21480458a4111400082c025600e074050180d880b203510780646a0010414070601c3c48035110040c02175008501030041d0380c00e1180c2da13121400c0b0003c00d504251030581d1200c09202c1044182e24070600e091100c45400096142580c1c2d030f40c2c0d01c074104440b0080c100042c00749800943d43d504100c46224456403001c03241d80308003240c0f400d501c40361020000d413010301031400b06d40e041c1c42c0944111a0300c00581740140243d40e581c03288444500c0d200c525210002085010005510f840d40406440094000d80301e244030800b40b501e1328000038502ea001928818200282000807410008480c120340703c104001503241c40000043c07000620240d03010000f0b05050070140036600c03154071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 314632095 1250 314630845 314630881
    0x60603110a0803250f0b01030803010311010302071a060a0b0309100b1203070210021002030a020315030d0906050d151410090e0606030403020f010c020102030a230105090618 76
    0x140d04904160b684444050312400f035190079083c0c0200540700d030004205401c111848052040005ea21603c03507135140c1a0f2a0030007604103c59883c0000018024454200758000c084c01c001d01e01589888000d586551180c00c030b038100d6000c3c0c808190041340300d680d60402e590010b404610266916841c0a1401d103031748038030380e428229a0603c2c00940c03111600b131000c8410842203c201c025444c0c001c442e801c0c8481c08200b042c0050441c001d00d021040f01110700d000a5014641d605409600c070305102185d10a21030004c01074074400d500c00721410076441c1d0040b200204480c4107091890b00d03070321418211000b809901108071503090b03501802150442c404600f9041242040e150032400542e203240569180350380e4003c5800d0760302040002400b42c94008025588203210b031059030800035407880c10900b960b1805003400e0260350040108a26a1081c0c880c2480c685c10280c4810115109041c3d0404441d8040c01050301445100000805540b070340c0794000420010108001d1191410f141c030120404008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 314633345 1250 314632095 314632099
    0x3020c090c09090a0b0a0920030606070506040c05211002090f0a180b19090b060f03070914010306031104020304030302091305061c02210123040506011d13060906060311 74
    0x11b00e404112400c66109001020000130082401000009402c0e041c5800041245034041e17000c0101400241c1d0034030610b400b0314400ca0070f0341c02440c00e010800c0f080301110214240c8008891401c009422000904c90a40c03282c5040c0060340c984110010035443d20454201035000b000c0300310005500416020407101030150010104403503d481c800304900d11802089201c200b12907000140f00016165002001c0c0500c0105a6890007084400f10029508216803000200340b01c114200104100741a44084040d0700340f8080000f20306541c0c0d0543c0c011040f510740c81c0900c0d8040700140406001c1d50440705944002000d40213214601c0041034007a01d011140755000d85843c1c5250510301091002056990354003c0410b075618100b400f010714a12081034156080d03640f10081c62000340d0b480c02c1081c107211802d041c07921032882c3c0303420454075010040c0d0050750a01c050030141925046566110707078103e9960758000c12030f600399042c0703c009020400405000d95140ae40008200216013603035042d02d03041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 314634595 1250 314633345 314633359
    0xd0b01020c060a23090a0e1906030614060f18060d06020f0d0e16121b0f0602152a0c0111190201110f090d0803010803120a060303020c090c09090a0b 65
    0x900030b0313214000c41c480690030107003481d0244107001c1440040c950000380e0700c0b2440016030310420503a09540c0340b0b030b1040c1c46031a41ca0704128100b00140035442d6100d2002e694007640203003090003280309008510042c48081c01c0c9080480d005a031503c3d000000c860b008442503440e0748480c0c00d2000c859100101c85140300340390544090080d03002246101c2e42035015101e41c0c0c01c0e14503044480c1003192000c84100c8195449008081076140031401800242c181102c03144070301414900003916288902e0724458651b0b9910781080f2600268040c103103c136041210409580740b1000704032180074040d199111406501300310351710000c052400040c0a07000110b003030041e10201c3c0880240d080b9010000c110a15074020414a112020003c00510003224090180880c5210b99140c0c00210782003a005142c49800020300000241c0400303a00c01d8102c001060104001c0b8650ba502035640c5404005080c000c4000c40c001501da5020141590036500018145140601e00a4945c6000b004c440aa491007981 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 314635845 1250 314634595 314634647
    0x9030408190f060209040902031c0210020f04260a05013c050903070b011806050604060c030f0306080105090c0a17060415020708040f05100c080d0b01020c060a 70
    0x150312000c030000c1038004000c00150741035a2030f104003030351107600800e070095141c494040c0181c41c00c120f10850110741c00402c4418554400c0e00078200003111020160f01c9e801030009480b0300800000b168211602114840c101038440c3e00054084408111064024041c82007002d0502406401c000070028151500240310045940391001e1a083c900c0c443c89401248c01e80c2c01c81080195210381c0d00240c049084038240700e01d5595603100c04034260069540300500c003810401d44075207400740e400a000c003200c031142007608042004000d141140d1014041044884100300c80d24040e0348290042c0901034020b01c01480e2840c201c6030745202c0f081c05140550158503001030301000401c0000401070680004d0035090b1519198502d5100c280d828040410740d00b080f01d40000303070f4034400a00003000c0700b00300008514644070401000508402c080410701140c80814000207100c0e00803901c0711030a020000941c0d241c00d000407490242c10400b4150003180000b441c469441c0c0010740780215002c210b050280c802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 314637095 1250 314635845 314635873
    0x15081e04020d21020102040503160302130b040f02030135120c0102040f06080115050f070807210c020a120807030807032004050306090a1e02030c030609030408 70
    0x1528961948004110201150052030510804041c5038010007910f24121a003035290803145006803441e0015070340c0060100001e007824031485040b0801090315006980c030f23680200c1c4501200b121a000c00c80c0d80c136210022642d136a5884007116a51a0904545070368641c12802c0707190354a449940d024a940816107003207403001040c1562041c80c0700001e0803400342411260710705030700074040c0c00b9000d5400380310104d120040c0c01d4103200100003582e9030504a514140c0360300b1516228241d1074042080800400a25403a5001142c00c1c00d603210700c5c090341d103209a0401c00080300103014181c5d000c0316a110300e0644030b0b9108442004d50380c000c8419900150361410075403045a00608000c2c40b5140500c041c80c0800c3c0101c050661240305800c000c2503100280b403110b940c0c00c0c1c4100d0107014100020800b4001404c0800c10f5907403001c0160020714a01c0c40980b00c0521015149550040740500d030340809085403000c0c401400030340b40150440d00070f03003464031700651a0b4016000b051054420260404081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 314638345 1250 314637095 314637121
    0x1150305100e100b1521010803180d0302150103080d0e06060f0603040201050c010c02070f14030c13020409051816060e04020901031e0504030806040b01050f0904151508 74
    0x1414510b40200b943c03106415014001e040094030071130f803101c80c00c520541580e16940040201c0c03074400d018001c802420000f4060760722010f070032090895100b40220410034003601c224a141035011242c2c45c1c42c5d0034080c60103c2c5001032010a103040c661020300000200207800f0013806110101020511940c40350102003a0b48110031a0f8090b40001c00128064060514400a541150040c50150700e06180c20850500391600429207200503401141c0401c1034110060f091401303460320380c0c1c403920803c405500180e0780d10390030b01c0d00d98400d030001d003110010b082042c1c1c1120010005124140720340c0c540001035134401c004021846500780201200020040c1090100000303031083c50300c1d4242c0e641b401c142400004c0d0014000700381407640d11080c81c440c1c526a0009203500101258012645141030703d80108041ca001c0d000c0b0b4041e50030a0782c07c1c45160380200c180c1740c0c0c41c100080c00c1d980b1091040c1c0090080e21030004600e2401081442c0421101da40b000c50710507201a03030311810407644a8080b07030450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 314639595 1250 314638345 314638361
    0x60e010c03080609060d0f0312050c0403031d01090f060518030d050313050c120a05010b040b010210020c03040b07030507061b091e1a04060905030f06070813050115030510 75
    0x540d00d400061028504404e1050b00544042e04440700f001207540c030401148440d00d8142e0200c0c02e800b4042d000f01d180b0740685030f4404029003034035041a24596000e44035080c0001910034801c61a030241c8141d0b4481d0300c0c11001080340d0540c4410f47c658514010b0103da000441c0f0301c8200241080303503251400c0000d0000384900340b69039002d281d07984c0c55801212155016a00312518060107411400303940d6050008609400b43c1c3d8003030950707408d00e86451421105006070320b50140d402c10042c40740030382c1c000c681e84c20900110f10000d42c1c1c590200c0d005506600c1680c1100f40b03a40e0717000c00c088052640c00b0010b0300840e40700701420489007c00381640b1071580380522240001480344001400900003500000c801301d40c5401b0480c05260301d40c008a00361402d0040300115035040401e08005042e40610400010081507010b01000010040d600da19110700a1003c02408201004540d002d400c2a6482070b0316074100f4001c12100c1030402c0c0c1051220110310040d28607110340a98400040028441c90306 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 314640845 1250 314639595 314639597
    0x100303020c0d030c02090709060e041b0c03020114181615050a031e0e24040308071b120314070c0210030609020f120c0f040515160c060e010c03 63
    0x1074480428402c000458415403822420440041505001a141c01c3c42840c0500a40c0c1c84000c1040d00700341c0024444030480d120148502c0c1824810035981040c00608a4110098a00303c20f46d407010381001da014140d0080c0c0e103900c5081c00c03410030050b040b01c0c0385c600c10b45c800d10105a03130074a21110b13031411a110a6000302801000e100703c0704941e00e80100000c017103000b0b460801185111480c5071104040d101e450785000c010b0789404c2e00004100050101142e1886413080c42200d400c440044040c03003220041000302800340390400b01c2c00e16800748042000c00d540040e000f021071481460f1010445691016020129060440156040886600711849464150399140800d0969020040d0200c843e4100c14245662050081400c56a0b400101202c00306e00000a50303800100500d139403d004001c0941880e04010300003a450400301758112000c40b41c080307810000031480311103110040e01c6a6000c1101c000e0050003031500300030340f0006241c2144c1845d2120300060000c0001901c0020609030010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 314642095 1250 314640845 314640853
    0x308060d0c1214010509061501141606140702010c0f080402030303060d11060d020c0706180e07121d010605092e0803070506040507050406030b04030c05100204140910030302 76
    0x221010080c0714554142d00d000c0c181c0c100d849828a1034450840744150f80c500103d0300100100320a06034401340c88405400c0131720f80944160101d60604005002c5d140141c407008411241c69002d00109400005a56143c13903040c0300742e07083c103890190081c030800d080d41010504058000c4202400341c40800d02c150b401034044c5146075681420000c0010f82140308890348086045000c9264407400042c041c10100345a005941e01ca02d60481441c1c00781660081040042c41c15511001c07104041100d412211041b158180c2a2107201041d03d6102c4800c118242a17403410180d0451400c01003000305401c0c042e80002c11080e0f488506000240c00c04803000c03480349214900c5c40f010111282050030362404614191b010664640445130f056902c40b00c42910294448000c2c4018031006114a0b801000708640410040e46103556019940c00c000f08050240041c004043c0144101805004510f040f0a28115036440c0c580c408503100010b00248640124001d000203541c1000140410080e2038040d0018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 314643345 1250 314642095 314642099
    0xd0507020603090106090c110708062503180c0513061a070c030f05030705070803070c03020402180a0305011d060f06091b070605070e03010209011d0a030f060204030308060d0c 77
    0x8810070740e00141c40c038003c0350741e00c580000d080e030440e225605800708260f40e4402c0701095641100d01d8000c1c240c22414454200c241400141007200800d00007030b045104131418060300c980c0c0f003a001041c45080c80610402401c00d11400c000ca020706000568100303c0e90388500703060302c030442d13012a903403401103450b03440c3c400750008500301261000c0e00c016403090140d1503a254a0781ea90dd681c02261020480740c651000c50014200501801408045e0950000440c2000125100c1c51800241888042d0240358002541c0c00801603020717950700c4659001c1c00d00c00c860350380d9242007402441c3c0d00c448054601d0080060b410344c1d400c00704081c0d00598200c8400b1100341c84010406c1029000034100e8100d0707802c4242d403080c50402c0c40f0050040e940c020500041c0520709580007914011020310840c0c030076403040100b45c50603078112000d040d0502c04500648000000340001c00d50303960150300040e00d41c9003141215410407106400900a4034401d5854004544030031050046a001c2e40300003c010800d10741c02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 314644595 1250 314643345 314643349
    0x5060d060e0f12070201080106020a0809060d0605091006030606020c0d060b01090302090f04020102010606050705150703060504020f070507050a08070e13082106031c050f040302100c11030d050702 86
    0x1010305240340d0502502c4004902410300d51401000016000540402003035003810356030401c103d81d005100c6800980b44c1c00d1015902c0500c50322980459910441001c9a242c41d80d441a9000c00090540a05a00c0903030404919020040c40d40e4410080080d051103000704030300b4404907020100d180090071602042c02e10390f81d023001500e650007940c0d04110303a4403800005a0b9610b03403a24000d00f403c075540321680c140780c000203003510341d0790704034906000042160310009440042d00d02100700a00c194042c460302d481d80201e01801059114a40c468000301c1c111024034011802000e40303900c502d0071522103541d500305002e02c0e10114841c070340b80d5400c490300c10042030220304110b5038000e40c00310f2400c1c00d200e050354946640d40c11019030982d0b54001b01c00c5030344c520500303c002c4581120045008040409442d0041d50410307080a011400300680401c00c4103a020388242520040d590060400345078114410000b0001c621104042c0c0d282c0403800804001760801280c2d1241116040d60345a20744481602 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 314645845 1250 314644595 314644601
    0x70e0102120f12041b0909080f130b0409020d0612020a0b03040501140a02030a0509014a1c180308090f030a030207060f030510210819030f05060d06 65
    0x204620801d40208500d0700f25584884000c1d02c51403003843d482126000e6914007a400c007142d6009041c42c11314081d00e81c008520740c08140c0d2803641c5c042c3c400594440c1280b07010403081c4090342c040880050082130100c0c220001e50081c0503500c0703060740c041104d140d841c40d6050202c0020480a07400545d04001806011600801140e119005900206100025041d80c200b005822142d00040f65804814442d52825078020260040c00c03210003440042c544ca04c00454104460031403691103104101d01d8024000c3c0c0c44d120000d03002e0540a2f03180b420207164240380e118001841090300381804800724400c405d0003480c030315502c1c80001c03000b803100504640c1c4144241c2d01c14500c1607440026040500d82c90340d000c0044490705842a23001e801228508000a030840d0740406011090500304420040001140c0322040d08669081022021a401c03507400c0346505528940050054a00052800c900411800c072412540900d40e0f82000001403000c442c008035181a1042544455108502004106150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 314647095 1250 314645845 314645857
    0x120e032404170304080406120c1403061311071209080703060b12010c030f0623060708090604030308010e010b030108030a3009020f1f0c05010204120503030609070e010212 75
    0x81d02c94060b04020145990032a001110101d81c03948000a040c0f00180d4070501c5410701504500d000d000031f003580c44000d807403613800d02c1080f4181d500c0030000400350b540f2030f1100d910014600804101d0f0b0100c4400511459100c16020f40d030b8080003d2200342d00718440c1d90550f0803076a240c400380c44024116a15031010b41038640003640d02903400e80c604da40d040000e00c50070b62604400c0d18005942c0040110741d500fa28a039502407190034550000d8100e440c410440c00840e2984c080b5840c1c0e80c0e40865140c509014051040010b0700082c0100300401003540004407141030303d406a5540d0590ba03030720045450144000d00601e80b07590400e20140006900841b0a514583c540ca035403208040900b04040781203550038200030000a807540002070035801c00c05d004080006040e511000080e44031000d0071f06040300e100c2d582d8101301201c1081340034041c2c00e5042d9000303820152440381d410501400c3c59592030304165005480b80302d000c40441d248500a041c1402d2004060b00908030551020800d549a50010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 314648345 1250 314647095 314647103
    0x705060c0c0721030305010609140607051203010b2d090120060705040e160504051c0503030a0b01021009050601060c0f15090c080c0109141c120e032404 67
    0x1120000c6116400d81250710480300f1400d007441c5000501e82070050a41c0c0c010381c00a024460310003c28840c5135031080d200006c1403020f4485640c2c602180c94030921f0507801404200b0190004000803aaa17a1090020111486100c2c00071150301c03821303844488821650114050801c00130020b00001c0d5000e014109083c3c100002d42210b0070701c5510300e250a1901c111260340008070700143c14019000704403420b5800640c058130301c1c0e0b205880d0410280580c41603014440c4900050103016802d880442c00280b4081c0d4898103494884c18102c0300c0901800803996014094050f009081500b020309100d08a14140c00c84000e00c4d0070f91070051309480c0302c142100c0680d030030030200201501040400144015807026404c001402a00030b00f058180c840194003d410150400c0901d0f0b522681c0c407015440035600362450350130940710301d5000940e00c540c000702e804100d0840c1d80f0354001030000c0c02d401103040036035646890701031002c0e410403d5240c4a80500c01c400b001c2c504031a080301440010000c80d405132103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 314649595 1250 314648345 314648353
    0x210050f06040e01020d050c030a0c0908120c030d0f1a300102070f0b100501090f05040506040b031020040609142d01030c05040605030a11090d0b01030c08030705060c0c 74
    0x41006c090948100711103150140340c001003441104030700c42c030506005208500d81420240c5c20f16001036200c80a0202d814106007010841580c0e01000f80101c42e0b070040e49010800c481c000380e86014015082c0901030452400415400c000141045042c030b030603000356200302400c501050b1407120140052905e1150844d9402d028000002c3e2401d84410a07260141c00da0800914103072903840442055504500d04128508c5801c0003d03150140c5003200faa0022680072525a4510340441c1c0208100029250b03d80320304840007502d188103030b000d1ba41c4171401841903d4840710003c4652504c0c07180b4030403040050312001c0100070420b640e65900304001e5006007443c0e080e560702c1e405020031001c59003d452481c0719001c4a0900c660701407150340409030b00d0342010750501c0e14164019119002c0144401c4001d520f81810b0130750414070208440c081c1c41d006084051121850400781860442400f08541c80020f4030004034802100100b5504256886002807030b84e580c881c0b00d00c09080c1c00ca0204d00e80c0500c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 314650845 1250 314649595 314649607
    0x3030d0f150b0a0831060c0309050601030609150603030503060f030c01091a04050612010914040215160c0603061409060d022815020105070809100207140d0504060210050f06040e0102 80
    0x1403e007141c0d458501001c0d20f50000c21146c2c1030881c103c407800c03400c51043c0351602402e0350004002080d001d04680e00040b00040d40c19040c01c00d4403400000b62540c00300d079840c080001c010507070404040c600075601a1030a450803044041490359541d80c1c102c1d240c0c003191040d1401c0000001680f03a500c6100f40f544941c0e400c2590703602c0407681d5504022080c06601444071300601c2440c01350710400100050f11802c010082c20b090300480c0c2c07401e488200d020120744002030b42c0c50100d000c0401420500d54421000410300765100d0b4001c00411140c01140d0800045001c050300c130b4039042008078040d01004042c1507150030260f0800150340c0b800b100718446107c514084060b8420f0f1528010028100c800002c81020b54441c1c00070f0845400401c50030602802c603040c00025400040c0010780c05108800c01a980e155a0800c5500c6c00c6100380009a14424403070304004095000c8040d00c201c0d60786400f00c4010748991559030050b1007048a000f19400f06000024a0034a401c0d00400352407a004800149421 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 314652095 1250 314650845 314650891
    0x30b0a030f030f0c080f0a020f0f0f0705030601082808040e010501140711060c0a0507081e030c0c190302131d0c0d08070c0503030d0f150b0a08 63
    0x6005548103a0302440c0d0101810700b4103410071102001d00415240190211002d660b8000c1c003401021440c441c03101004c1140011607008003c000c8158803a441280c4400f0303599828907a44135400142140d82c1d00500000040718200091200d050b11105d00c041c01000d40000815111041c610301ca0b030092805042c211808102d0000040000c0e0030341c1034004983c0d40c1020005000c0412010b046000c5040802c00c10000c9410902011205042140c2c41540c0c4c1482c01c0205181c8240d101001e4803a010f007540c001060100050307510031340009403640f00b1241c0c000002041d202d0141c3c104000c4150006544400d030340c0342c003148070451499140c1658203032903203036000304e000c1000040100304174698910f45203008000480050b44c10344099401010b10501a001003000c1d5030140c1c800921071840400c100040006156041006c1c0a02030102c907100e451248242c0042d000d11400945e000e03142050035851031301c01c5ca145200340e4a800d02528500040c02d03c0032104040c0003000c0d284640c2001046101d10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 314653345 1250 314652095 314652109
    0x203190e100206060102011503031205190c02011d150f06130e01090c0801060f0e06030102120403171b0304031d06040f08010e011a060703030b060d0c170106021c030b 73
    0x110259000b0f040d1443d1120019003101e14242c40c1d484a440000b900304000b0364003080400d04455084404102038036101c1b440e1402d030182503100c00c1d5040c00d2002c01c6048903030540c0b042481c0c42130710b0000c01d87d004681c10a0354072500559001f40c00080c600e0005030102940f8050150400b0001d056102c0350950000782c0c42c200e90350340c0e000e40c480c0d0351502d00c400180040144204d0107000c00a0082000d01e14112135040e5620552184800b0a424400058421ba8080d41604d8502c2d50700c0541000074502840c0041c94401341c0502c2c8441286508042629034600071044020354000d0907e0500e5525980c500751803000503100d4941400144603141c12098480c60040d00003042d003451a083ca0600f082c4aa509440c101031420200e40c0c5000792055200c0b50880e2903c000d4032098034116520b416a040440181c24824a01e41d040741c0300190848413540c040d482421108050b03a9001e01c40803d000c682d404c051403c1c414240140e210300340b1900b5414114020400030348040c100090007003920804900f04d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 314654595 1250 314653345 314653369
    0x112020a0b0f16110f2e030b060d090209150a03030c050c030714040f020c1c020f031330020603060d0506010312080108190b04020406090e0105010302040606020d0203190e 75
    0x1119800c1c450400e061407565040c1700f6000300c94240511108540d0110340d8200303032820001600c24424181d14150103507000c0400c0c000e0107802326a444096410709006014600000c9000b440320900040c0d29070503c107172513016414020001360400b0302c0d5482c125900c00e8010015207250050310318200c4d80d682c08111600040002c0984a9154403e000800c021169250b45c1c1101c143c3c010892140b074103034045804e0140a2580d81c82580015800c20220b01e40070404540040310700c00065091641e0300400e0300b03030003101c0060140300d0f5a032002d0010503020001032a002c901d45414055513000502e40280511f40c01003001d00200c0100e0700035190903240000aa205894100380802100465075200c2c1136031780504140d0000303064a000d44612a1031100d00c0a0000e4014a0721802060442d659030700700c0341c01005242c0c0c05110348907000e226940207050030311049120302d242c0400010028000f1500000b0344180744c000c0d40c100400700034030b8484a0940012041007103148205031201d55125240658 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 314655845 1250 314654595 314654603
    0x314071d0307031a070323090d09030201050a0309110a12050606030c010c1401020f0f090a081222050316080d050708031f24080112020a0b0f16 63
    0x10418009444150000044402440c001d41150707a051010402c40e611075502242022200c1c030195445c4031044009015000c4000c00145850411200444c0300b041c0c1140034003070340010b4500300340b91184255030f0400345200003030214074144040e070407041c0243d10145580f8062040c00c9503a1403541d00007444a6020b070041103110281c01641001e0001c200645540404160003c02c0c1c050b0000002a00b5800c0d4910001e290016511a2243c2e0700801c1d0140c40050300c2c11101503846010607481e1000c660020b402c0207020f4041d000e8005a40100007a800070f4030110b118000c3d181049040308040340d0182e402214409c5140290f00140076103080141c0d4041c0215501c0308482e039418034808900749205c071000b8108129083c803802c80410007403402c9036000032500740d813905155040111070480c403030903904c0b04c1b00d6409001c4484448824424807040c10100320303518403400781c0c0c8418100c1d0a0f00b800034006900010002c6007400000d402000800c0b0f0030f81d0b451101810084403581d9a80e00c9c06000c80211 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 314657095 1250 314655845 314655857
    0xe0a090c0e180606030c091509090703060501050417010902090403030213080307020f01034a0105091209030703150204050a05010804050604020907090f0305070e07090b0405010807031407 82
    0xd0100c5038014803415003601d0844903000c840c0d4180c920640d4200001e401d4131301c18180040803d04560841049409001c80600b00c0d100c045a40000f481d06074000221a40c0a250642c000450441c400e01c24002030f654140c44140c20b040c140a00c0c00002c000b4081d0558207527503101040005a03540401e42840350b4807a40c1c0250340c451010070740851208055000c034a003503109000307000059840c0c444007544c40c002864005000f00542c1c0300f44c00c2d800c219042040c1034240e030300a03038034403040a070816400c003044046000940c0c4010036141422500c04031011003841e0808211200780050090040c01030b0080241110582910390f201c0183c901340c24005030a00d903900003002c0005092401b821801400d0074248000c02d0314140c0c6996484a0303000340000d1064030701c40c000a008038010034542010300402c2040b050b40c15107a140195940199000b800010b10b91500000c8080348a0f070141403e807001d403003801c2c0c100b900c0c050055511040140c4100c007815142c00d107403640c12070640840e9104180540da01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 314658345 1250 314657095 314657111
    0x1615022104140109120807170c01090606080708061605040b0415090b030c1911010c03270f0b06010212070f0b240f0409140607020c0301050411100e0a09 67
    0x10856114042c40c0d051100e00d0008118030b0740c500c1e951400041e0040e55450341c1d00b602d464409041c88640240d040d11a8000c0f032002a0600b05600040045100d49010018261134602803a030b1a0807c2c071800c5980d030f128030000354858460140d8050f00140c9400c285041589820307a00d8565046504141980d14100a801e52103640c05000340340103040e540021441c500f400825200c0c9449038405842c28440c06010f00c1e4142c503c1503502c2d001002980c0d000b00140032809000901904120303c0100308005407000b190700090301103c0025440760300031034125200b1081c0d520075800d2000100014154000c030300c00305803c003603030030300410f035140c4500c41300861080c10785040305100002802040814800b002c0c0980b0001d80701c00b00b0000380b5421a074101840707502100240141410000c01045030200e1b244100d02014005541e038001d0303200342c003500c8011111400b131500722241110068240c102e14030310a18030381030000140050f086145010f041e00d81030701e008142031044643c0105242c41c1d869640c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 314659595 1250 314658345 314658359
    0x5030d02060f10060815131118094c06020f0610050103020d0908070f12030506011209081b07090b0a121737021615022104 54
    0x42c9a0118180c5182c1d4405801c0c008000c01c502c900401168884200010103503445c3d82e0000d0110303548200d0941406051125000c0b41240c3c1c100c000081c40580c91041c50a84502d000c0d40c06902ca0894400b4050425036000c1b01a05507442038000380344641100c13040062595a014106400d220300c030300320300c0400c51500c80024600041002e0910240d0071100078800300800d9203e41d80201c0d0b00919002d626540030888250041080c0c0341e00406c907410014a003c200140390501034502c0340681e00102000c0025101034003a1441196001d0010345038a10307400620310981c0c41410858026007070303581030481003809180101c0180407802e5641c0d02080040010850501036003460120030758018500b1860210784006c2e0741426507004044616070510250702c1024501640c0d1029601041d00144541c2c2d548040303184a01002465000020140d0300011140001031001c41e89040780320312081c051614101e40032a800d030800d07100450140b0059a85035141e40c407064481d046403011029071760307850030354 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 314660845 1250 314659595 314659621
    0x912010905031216090302090c0f0705010603020a151202160f0c03020f0f03300a0801030519150e030f041409010e27011103092401270605030d0206 65
    0x43c10961420401000c4d8502e0360100125088075419500d440c11502c4601d02c8003c0b50080c4000d0340711841c1c000c100300051000c15040f1030200ca000380c400c00c07003460301d802c5440c520f01081062400843c2e022100c42d42e82d0b6080ba80100703001c48a1102c4c0d200c0840082d80d4072000c4548904058858000880f402e000303502e09010080c00c010000c4589040960106004c82e84070a20f20f4503d400080b82e038509030364980e410351481901c501d41c6d114080c4d035558521501500302c0c03e00703000a0b40d20f0310546008658050f01034002800039604180d9001501000e0703580320000d813100c0d0304c0c1c603c540c0c00140000400c2d8201e4502400162292946078104508104c00344000f6a0b0160310a4081108410511070004905201004030a540c854600754a00c1c1c0c4020550243c05040b95120b2800000810400c0c1f04202040e001c0e41000780a100240d110304c60400d800c00c541003801902c000d8208580c8100d6108544084141a010040c8010500320390f6400003070701384030000e514180560031450800c42d003e07180300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 314662095 1250 314660845 314660851
    0xd15180501050d2a1e0906080d032003040c030501060e060f040c030f0f060501020f010b010827100c08070c030f0e0f0d0605041b061e020f0f07081216060209120109050312 75
    0xa0010030445180c0003600b55180d040ea40864241507881c00c050080e800f4024038211180700c12001d40e030333680c106881d144101d0b01140c402914036511f000d402080c2c600c40c4862450040704010641e003c0310700044204401080605a201c05042c0d503501998595006030140041990080b00c0008244d0300d440006414004401d1442c09142d2400b2074031115030f81c01000042d0030401c90b801d2948517040ad10740c0054140100001d48000344a080350301142d8074025084264044095a0742c040300d038031885011799414402400040104800001c40641c440c802c03001002c40c0c410007880341e242c207411a00814201240000140da0094649041005000007800d160b0884400c4602e03010400d8130700703080240f0a0440040d0b400040c0c00c00031040d44028401c108481c0114805403d44088503281e40c40140e1b41c071807510a440a9005090781c1001544003042580c405100312500010b040803156503050080d072002d24000d0b8000340b522405050740d1400d1146280a51040c00116500c00c003079070034440340030802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 314663345 1250 314662095 314662109
    0xe041d06240a030206041712031f1e031b03150c17011211120102030702070609060c08030604020a0c17130b0c0a1104020d15180501050d2a1e 62
    0x12240403c010b0300c2d001c1c2160129403c00d90050796800d0035046090502e11440c001280c80c00c400700034407000444000103a080101c01c5101c20120a1350780f42c0c444412043d144e0b64509660b0000f01c104082a118822800f500c044010042001c541365500c96240341803004000340110b99070001d6882c69030b04001c2c5103d01005243c1342d44003540c9480c6400c4811290584003c221130712000c036502c8140c845501c00c0414020f5140255141d1a03d40c400943d01c18181c41503400140500c8000240c042c01036540880e069008080070b80385680c0e09042c0006580404002401c006074801ca030004551500038241c40000d8000102e03030369584416150503403030042e401200c43e400d4200980d01c6c80000001c3c201c05007030f90084105000c40c074a42c00041c005d005d148c42c0c802016040c400800d142e44209c40c1144180d85030081035104100707107540480c4c111842400f4460f00f01c03d000581201090320803c4418200c00b5181781d038004112025508a182d40003503200d51a5181d4000c0245a00c403142a0010060064 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 314664595 1250 314663345 314663359
    0x70b060a031e080702090c0304030914130504050309030106080f0606030127020d02090c040501081609171c030f0b0102010b010905040b1512061f0e041d0624 69
    0x442e00e401003800e8469440e20445000241407400700710419040e6100290010659455840c0400c4064200d070300440d802c4000034580200400c045030b0004841080c80005000201c000080d0900a001000050400d6502d480240701a00155800f40160030140c4040f03405040e03550424a8501d00e0010090102c5100380d040003e000c07040212001c544068090000314590001d030341e030000c1281d510031aa00030350000c6e0300340d0400c03241529150040c400c680c02a41d80b41d00320340d501040714450011401060f40010f846420402103905009101001411180140c40f040f44070f015500401d00d12250340440032a440e441080d0181a051080004004080c0024403400f40c08000003400c09245004940c40f4039550700e003642d400d465041c44509413110180120f80d4424000c070ba0221a8a4122201880703013050f01c00030a82c92900040e03030b42502200ba200c290081000004000c040c108401c0400d848400c48100029204402c104990203000c01c03504150f41c80003402d4044218200450000703000e800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 314665845 1250 314664595 314664599
    0xd06140a090b0c34020a1e0902030408030105010f3542030106092a0c080703270f080c09011404020910030e1612030c051204060203070b060a 62
    0x680311590800c464900210701c65004c50050600c900c11307200d542c2c065080f81c4480404159084071501c00c41c0021482c001c890021684c949009003079100c1110f0041c6a008284010041035010f8404250684414200030380d040c80181081c0e0508a0080d0351b80e10405640003242045410801c080d82d04140c00000c5941c828415410840403a142824042c0d0345404983c009502400e5001100c03018440040c0240421a615080500508136400001c807201c06140400d10514651481504941406480e60b0380c0c210050b8545011a812456003a82448000c0d08084038200003100e2507561841d00b50b05443c580707030420340489580300c01c0380c2001d02c071070717010000252241c0e55104039941150b044007038803d4104801000b10f4068014800300399004003100100c2c0010a0300b6811200881031f24a0450300b0000303003030f800d060b611100c6202e5100040c01039048440803e11070b94100485034081e0b4101c41074440651440485503125900c90001030f00003003500410401170415081c1c2148040700d803044542c3c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 314667095 1250 314665845 314665867
    0x30509060402090403091d090111040e0106050d0f060e09010e06060d0b093a080105010c060902150a180504060308030f0907050a0f0806240d06140a090b0c 68
    0x80c0014001900c00ca420000042c2014800d044040150000103c0701c1000403e103001c24201d9401034070600344a508007443d080c010202001910111069080c0c50b4150b640382681c29502c1d5031029000c00c10054540c01c0c50000d001c6a17008100040014698007621454403020316401c41300031440203281600701001b070203c02d0f640e0761884d04c046a0402010249901d91549035881e0a44040b42d105070256110294ad807030082e458000a90405100c40c0c4180090108078111100c040c01d015450104103211036620120b0800d501c8409182e08c098400c070760b0200800c6500315190411107500b00021980c0c90765041c9511000c0f46140140002c1e2400d20481c0c3c11981d81e54041e020050003210f041d03007800c0020b02c0d03c03081003010300b004200207440241c0041e19840104111140c034090300941e485442c011035081c0e9880d0120203812411041c070740e248441101c00f000215051044290303003a81e103440d050030500000090007401058030040016a0fa280351400a0744180b0050400ca00c1c6941400490044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 314668345 1250 314667095 314667103
    0x308040b070c150c02010b1c0b010609030b0a05060612161202040e0105010806030a0f0c0504110c0a12020304090609050f0702030403080319110d20090a0314032101060f030509 77
    0x40700b0b0329040440e071806008070803401840e04a180c242d1044007201000441640000410003460240c0130600262f070702c8110940b010340c01440000c00d2500c020f400101401c06c0c0b41e016a40000d40208060300c2e04130050103141002c042510702a5844c0a05c0300400400c40e000b41d0204201c0c0035000d41917080a142c040000902c400c14480d00d41800280c60001e9510350382400ba00400541c4809403000300ca07e10f00340010500d849006a82c0102e180026495000c08400c0644113440d9400c8000c29010000d50341d4083c0b90078332941c47d081548402e0201050070320706070103848094a004000014907140450800c1c0e0800406450f0b102035404c00c00042c00030038030020441e90f00041e483c05454581a81041c48402003441c55100d81d00d17084040343d2000d140034030b44c2054500c050505594001070400c649080c07402d1140361070f42c592022070314004100107040314400c62455150311013902d0424408034224085a654003007800e00641510f40144011a04441d1155404c0c1140c038007081140350405074aa55 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 314669595 1250 314668345 314668373
    0x91a030f04030c020a0305010f0c031a010c03180e041e0201080f130b0405060f010603050108031c0e0d0f0201060e0c0d0504240c080f090304061206030507030308040b070c 75
    0x109091280000c052500860080e442c0f84d901421038000141e50342860f80c000c01c0c8815114007080c0c281202e1071015446409284400c08184205441176900ca8005403112041402c0c21400c0c80740c4d01000c03030f074849160540358000340035011051400c0d140510700300c0300340740c94441e03261035140300d80e0016030161340d128064640c0270190900303901c5c041e250b15138501d610002d20030340203200d07040324405c1104010010450078040c901c0e00684402e40e907240c40058050720f4013402042c801e40d00502c0741203c6243c141c104020341ca04000000503022400400c82c5040000662449001c40d481150440c0c0d2a40d0904c034240c02000014080040c0d820100d110421a100e803509105505448902181c280003680b104c1e0f0303803c4010350303440d05804103c003141200640380700f07900100800c070701d03c00180c01c4921044005100c2d00f0070601661510381082002c0e81e581018010341c1c1080e555032100840000c000b040351034007450180d26201202c2c0b6042c50011f404510040c01101088680d0604a000074074041c5100d907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 314670845 1250 314669595 314669611
    0x10f030302030a0f05040909030914030105091009060e010606090509070e01020c010509040e06040b1009140708100b03070201020d0f02070f020411090a090e01061d010e10090507090501091a03 84
    0x43c03651031604201c80a011b0381d0026415640b822517410105600050078400f11150240404c1a0380541c2080500301e07001180e42c1d6400b90007102d00c010840780b5640c000e01e401840340308000cc03402480600103003112819001900403a204400c00d00091170000319003a445152440c00080703040d210340c0001e45902c05540c490b030602001042c02201640d0303580251a510350040110780d440d1030542004412010b058640624440130300c0c102040c1307030215010310310117030b80340d00800010340d254513008562680380200000315801300c1e044c000c20140545801140249103d600258640c40035009020840f42d0341ca90880b60b8901c1000064002503009444424854049600155240c131060803542c0512400c0f880320b51107402d83c2e90125881050390f10001c41c038401c01000300100d50b1200880e4001c0821601c1e015200310f100300042080d40c14416003160700024000c803a4001c15038407031120f0151001900c8400216503200828071030741d40e201078440001c20750240000c00342d03401540c03d0140d42c44054507801e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 314672095 1250 314670845 314670857
    0x114031006030b0d030c020d06110a1e02010c091a090904030206060414060d0308071107171b0a09020d0b06070b090c03060106090e0c0723010b010302040b1c1d07050306010f030302030a 81
    0x19089c00030640c800f0007022500c5102c41c1e0740c3c4040f80c100070000d054040128550482140424000d80d10500c01c0900001320b41c0c40741e0f8a403a0620049410f039a18044900210b440304002845050f154050602d002d54883d030020200c60515804100903100788a1081549560300f008200055031041c28842140307815050900441d00c402030112181c1c0d00384584014a440342600c00038006820040c010540c45910064915401401e107200c1003d028000e40c280d07000d070314208c0621401002d94001d0001034214013000504800d443c001c640e90303401405065600807120010800841001d12100b040c482c4100c0152040350704050014188074640c1c01442816800740c000941d500490038111040036800940c802d400543c04418500b1100c801e0501807555403e1440075241075000e8001d48003075409510485080c4030007828485092040c20222840a64440f0420040d0f0101444142461103c0c0c4000e821b1071420402410301e00380041c3d0002c411010b51300010008280c1c080181d0f00040c01600d00700d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 314673345 1250 314672095 314672119
    0x5030309090703020a0c06180203070b030105060703200a0b0412080103120c1113091b050f010e01030b130b0a06020a080301031b03080406210e0a0305090114031006030b0d030c02 78
    0x80351000440c06c00204414070f8540c010500d02c0c0304034084100240700310b040b01d440a880315100300045c0402e01c0783c1604040103000d8903000900400400182c900c0c0034020050b400fa580b014603260200400b000e5440720040800c0c4010f000310501c44007511403044c00d00040651540d034412502d1800c48800004006940c40d41d001003201b0841c41c203400035001024800d1040f0404948402421000011074140c0f00d00034520741c1c24030075005808101c801c014111700307000e03c4240040d51040000c0711142d0406a075104082e08030b9540c0d600c5200c10000c94900010070001d04c07000d20501c40000e4000c0025588040001c0b07001442d62000c40b419650311607058001e00c08500084800c0b0b0b003250b000104400000b040118480d94000000c1015507100303d884a01594000c217480100c42c0d03004901201500442d80135000319005800030005440180340c40409501d4011701000340d86c10541c2c0c00c07d030350600d1047c1080101c2e8140640e45101c02d0881b1003242c96003042d13034040c14001e0b2102000b401800d5134814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 314674595 1250 314673345 314673347
    0x503060904111311030601020f0703050705041509180b010519030f0c08030703030e1b030318030304080f0c04110309030a0e041401060c0b0c03010f0e060a0306060b031005030309090703020a 83
    0x410f5106080e45028414003098481d10981a00121800c600621400e0146145500c000540b130f801c4a42143c00392152900382001d1001400c15034100e4003141030040000110003000740720742d8040c4c04001511820480c00c0c2d141c40403258806a00071071089440403100c00304410900d203003400312a8045020030318440300780f40514482d103070340c0e00c1200b66000105614041c503416400518a0410b10401c0e03e900c0b882c5e01003007000000c2d20742040c54242d4400d02145214a4400048489050009088178102a51004010703d0034440b005a00b1042d08802c03190450341c10103000341c06840c0d01811210b41140b4102200c02d82e24040d04202404220050507019a2600e495202d0407001c841010006001e42e1501c1c40503200345012b9100b10389065211001604684031442524140d510010960300c05628210b0300c039070300b000041e03c0c02d039018510010010000e640c600ca07990040c0311a0641d16143d240900104050841b1540003030f02a800c01c01680d0182ea0740c201031150f121106080058441c542080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 314675845 1250 314674595 314674609
    0x80c0d0206091e0a05030423090705090111012c0c04060503150406060e01090c020c0306040c1202060910031e02040509070309061b020102030a0f360b0c0d0c050306090411 75
    0x24024005000021f008946041c8461788402c424015141e1100c8d800c041c402840240001201c05c030f80001d0040c880c15105610400c3c1c1f8103040102c0b4400490813481d61103400c01741207120040c0d142601d02032402298004414418401e400c08100c5080016034949808644c9801040d8500301e03001400c030b00041c04000309684080060610324440000c1981c4941d401002000702e81c00150243c032580c07551841624000441d60b22441d80034100d203032004c0c5030594841014484441c1240d1000707050288040303e489019100d0300304811583c0c00700717141b01300082e0b041d0303a1844405030340400b6004200601240c1c46030110650849060b103400580f00006081c01802003000c000c1081c2003404440455007016415000386018142c04881040300c11100b026039002c44040740b6003409072100203601000c80e10428a0311107403405904860741401c0d8001e42d981d400402c0212001c910461001c41c010407080540e109014911321541030443c0303142000d17400901c0300e1800a000815891445070302d50101d8550720 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 314677095 1250 314675845 314675863
    0x4110408030a030c110303040c0515221d010e04031b050307050105060f0105251407090e060106050408030d0506041e0f05060306010e15010504050d080c0d0206091e 72
    0x103059070b444a4041000070041c2c581902003000050b802845500a010044100e80c061648201c80f85211031030705003444030a90115000303030720210042c0504c1e02071040c40940000c400c40d062030b25100d40390030002014040154082103460381c4241d1001445820444070342550441d806050140344507507000c01a440403404060000d18501021518000f081015000340d0300039030048a2031000005c030318004445a014001c1da04411300b00070307503480804402c0501102c90b80c6000d2004040102c524440039454480141e00414100380d540001c01c04245085c00000d0142406103499443c2a1804190603030f03030701900040145540d42c800c00700f00143d9960307000030000d0307030302c51000c0381c3c0e104544c200c07103000301007040d1510410341c18540010300c18a00403400300e05807035140e150500740e41c03184400e104107074114034029814883c00700804145c41c0d0780c60398504079841c4174590060f507519040081900381501d055400d001d40d44100c0a00c070700744101180291000c0c820712490800e8801d06410f2501d401072803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 314678345 1250 314677095 314677109
    0x812070f0303090c0f0b0d0509121e0f04030c0e0a1404030e03150a0e0f0a02030a230307080d0f0c08070c1514010510020c0303040b0304050a0b090f0c0306100302041104 74
    0x80d510000308a012036011f08403a01e0121000c010b556141144035403a0350b011050242c540303004010132034030303241c646000d03490050447c0e29041c280a4011058541a4840d400a642c00c6480000c208108008000400e500203003402c002d00c0b54002d56130007260f000d00b02500c004c007402054920f52078943c4040012600210321642c03600e9a5040002c81c0c6001441000707440c61321030080d12040711020900091b0100b215601070010990a6220748441450203d10805084000d09400c101d1042110800c0600040340c003460b001c5543c1d540050010b002c07540c9107003042d0a42410856030086a07500030301491792014007420142800482441c01c0c41c41d8186040752010114540b440d0700d030783c9803401c4281078142d0758295141000c81040d00c0e01666100c3c1c000846c1070b4168803c100901030079010f00c1c040e42d0410311401c1110a184525550502e030720204640441c0c196020041c03c07a440d450030460601c196805901400c40c604200301d00a56081c154080a4000ca860300b0141c17060181e40c1048600074800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 314679595 1250 314678345 314678369
    0x40b120a03030b01020d050306102718050f041203020d020f1306020d0504140f040b040905060601031b02060a240807061e080610020115060503010812070f0303090c 72
    0x110310780a030080449001d00c0d030041c813070010101200d03400740e801c80e8041c2200400d1079000d803441010443d0b4000b0315405a0350207180c60307043d00000c00c08940502001c0e013940f00f003810b00e00000312061421030707900a0605402c08250f07030034800400c0400c03080b03200c80d540c0c0f890096510761200042c40040e1103040c0250b40b4180c4000f03200301014810300d44920a44444d41d09443e40d00c0c00214003110781d40a030f8043c1d4212148841034450307c6207010000410181d80c00350000c624440a00001021a00c6000e425219a0455401c00041d5030b45032107034000b00e0300c03070300c0340b840c600501e40e08000d580e0700004024024440e940c80c200c0b00740607c5909640d40300c451a00d81e1180c1580c803220225103414007882110080b48840c1c144080385002580011b0b0300000c25580c440e81d49e40d034202048442c07180c16241c4002d55580f2007401007030700266102c20001d441c0035165907035203514259415250404078010100300aa09104000000d441d4240d407054041d01403a0210322003c080c1403603400045182d0000030f1000c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 314680845 1250 314679595 314679613
    0x2040b1215061b010513031b030c020402040602010c18080c06030c04050a08070801050708041e02011701080106030c14090712060e07080a0f0608060613021b031224040b12 75
    0x81030983d01e00d81c1c404240000d00c100d8803850440f030011803c445008011450b8010f0f60300b2800ba4400c2070010040c02440c08a14038407264011a04070781c010f401120040c0d456440a03104a40c12000c41c005001420b13501004c40c61034445a60b071190070801000d0f01c00c4d04000b001c01d6452040106842c05041c0051100c80220351b0340050580d034180b50b100b4000c072035007803100080d600c074001d0000a200e190070035010140c0c102102a010b60189080c0002c0303043c010b05480d005074040d90342c0d141e240030f010100b000048290560401e02d401c2d10040c1d109100104107c0c0011020707458035828030340c1180321400c10a10041c2c05400c200040c0c461030f000241c13446a803070100301649511160300303802103c03000c100300018021125243c003551854041c0901c99401100400c200341403010180c00310030585040181071091107110a001283c00c480c0c07101032039001140e2803d6407407400000e139401907800700514403007804201d0b022a4004070307c0300c054807a981e502c4515810ba00c5200180d01410347d10015030700b00d05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 314682095 1250 314680845 314680867
    0xb06040302040f150f0b030115050d0606112b031518050403080901090201090b0921070302090106020d140714060a0504060506010c030518030c09010602070e0a02040b121506 76
    0x21043c158040e14485000001604652180c2c080d01607074403040250303145a00300f071427241020124000010400034200700244124a082c4100c0014060503681c00f001044181e4070686445c5544a110856107240b00007022640c000b0b0903e11001b031100c2c10040380f039450000442d0202040d42d40002030b030080c4040f1448130310030325501c400d00ca9442911402a15159801d840342290010b1400a0101e0b4203040140002d5282002819a071b40c8000d260035901c03455a01901c8504040f0039001425500180c010700840c505030007024050b0805100a0140c40164500140904044400e1040045000902c5030600c07416090701c00d804103030401117074100e0400811420040c03004480580c1c0e030320700c0c102c04141c0d40d601c600d01c100c0d26180c02d941c80500f0708103400302500041c5150880741c0d91501c00c0c081640f00e16169240f41d03034001d00c041d4001d0400d09180c00c0865110800040c1150f060a104001c207200540380306042c0c0354110503d030309200d05692911488a902a86204404e03440500031030f082e0740d10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 314683345 1250 314682095 314682101
    0x130903270807140f0d0c0f0303020a12050325020a120c0c0905060604090513170c01050105040504080d02030403020c0604080d0201180c0b07030c0206030408091c0201050a030b06040302040f 83
    0x4801c01802c0b515034594825242d03000420320700d40c0303652006116a0600e558070380741104000030760180c070b44009569980c4a500a001040758422030140e00800400c4081c000000461183c00c400b505186240d860020194827510000d030907000c1c52400e0704100341c410b551003008400f0076298008030726601c4a000403405070072610b86904c1283c1a41010801080c0d000703d40c020f850059802a02c0d50341414141850000503150044c0305040c042c0c1c1c1c800d2444042907010000041007451440015078036441c0b001100e00f0764005070070036070280307080000307000000351248101c4510401d400c07001a01c07901c0e00e00c0c0881c103009030700f1035042d44000003050200b0781203000b0030803080100d8036130000c001c90b87c1e140034200c403107408030b07800a040c00103000f00c10065002107400801c61a03200e842d000d44c1d41026640010843c1d04103645c01d4908010101e9003c840341429500c1d10480e042601240a14100e02d60000b4000d10405030010308064a5624201c4161503101c141d4000d9a0300074014084010381c0c0b1020802 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 314684595 1250 314683345 314683349
    0xc0c040b090906061212040e0f0a11160317010b1c150b030606130807080706170a021303060908070b070804240608071d0606030108030703030c0c020414010e0603030913090327 77
    0xc2c270b5400c10104140846920491000c004008201c604040c580800301007c0800030303500b40d05100041100075400350032881c0407806485a4081c581e203c800036580c038000c928840d00001050b900d821a809911041003640400f1500b2910510750307250f0741c140c0411150b0156040a850f41100980d002c20703080408960201130315407480c2102c11300c0d60307200c2c0c04443c40880182e0035140e503502d17080807400303c103090780080c82c99204281d40300c0d0000c0e035241d941070100d840321081501c014901003007100400001c000c01035080503941c0b912905030308007074541e918210a10324840d21502015207071890362034001c4e08210010130034042500c903019610410340080340e110008190b0b2641c0d95100003441c034680b032410303681a114914000c50400c0541c0e075060b0300800814412200b0b2003104400440141d9543c0510591094802c4500d1429454800c0005500307401a2510707200390802e0040122035200d0003000e40da513090883d404521061542804daa10504058074010226a0510b605201c00042c0e103003030342 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 314685845 1250 314684595 314684611
    0x30f010302150901090302100c0c08010b0102150403080609190e1018030f080901021b0c0907020706051c0e0a12020606030c0108010306200c0c040b090906061212040e 73
    0xa01041500720b000e098441c2201d03880c04220700001c14405428580d0840c1020085070403c1150100d80340c50754405240c4039440f2000d0b60791210103d14540d6814080c10800c01c040c1d240c3d082d8203003015034000c0c00d030307a10080415014243c07810004048680e4200402204d20800b10100001c46442c04516250348244443c4028035080c020442c4519106911001c80b950305640e80010110300d16208a510310701c00b9003e260159028480130720785c0801a101011900e80907801403450303a196100b8440a110020105000e642140004102e0715401ca000c850505411040d9008100da0710400b6034001c0202013000a03441c4250605038040040c000c00806071081c0036021110250340341000c25a54041c0b04214500040018004000040701c90700b000d81d085011b03004004500340d8130081440903411060304000b00f9070000d2785c18026404c152007896106c140540324180a8a414824241c0d6840082c103001c5c018001c0d4400c5611a2900740b1122228561042a06a882d075170703400c3d4000c00d0360054071151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 314687095 1250 314685845 314685859
    0x101d0411121c200606010f08090705030d050705060a0e0606010c0c0305010510051203030601020a0f020d050a0c140d05250902071b080a12030b01120f0501060905240d11030f010302 79
    0x190f10b00310000b812a1181d0f405a5805030140700602003282c000b040909109064490b04a01180c2581c0500003400c1d0f42040340d031260345580c91820502d00e4004060800983c40c0e1920520142203a00403032180e910030b00c2070a014940604c50b1400403501c00d05540003801e15440c05e0103225482c4030001c519004ca58040f100d1000783d03108132241e25200c1c402a03a4035400769002e02040070001c3d0072407072030300c2d003035030004241361110843c580b81e590a03c16200c100312030034078582d081400810a60441401c2c0b40d030069545460340719281e6515562030b20180c4402a40d105000c465a100d0b60b200011480541201c13030082d51140d0191820354012240c40b407140c40401c06101001c21000b0001482c0613915402110b0310280200e040703070070380050900c201306a04000454803549102c2c8117030302030492010002000000c90b0340c50041c006001c01d0094100d54414100440300300d00b81440c1d210010300002d0701071210b50b980c9001c14146401000048500b40c00403401004104082d100a043c05040f680240c3d011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 314688345 1250 314687095 314687147
    0xc0111040803160c0b0a1e020a080f0c1603060f05010603020a21060504020c060109150302031e07050406080c1014120901090209101d0411121c 63
    0x80a0a40201c0c041c55100d548180011441c0414003d1122449801900241c807601c0d12400c000100d90f202c805242c02103081e4440032400c01d2940000707201803841920150411682c240c0d210074140c4100c0700404a1604049041901e00d24103218000f454407000322855401503991a00d078010740740d15060f014060b80350800008185019008842c502d030240c2e5a482e85400e40d82c2d5076440782030450f001a0403040e0703496601180741d0700d981c40102100110000100103540c9842c04c110300b0754014140080090903075003002c000503180002d046d000815000c120030b19603440b061000e440c028041e480598842e0501c0b20014803d003011541001841040e12095400700503401e060f03800c840307445010740313892800304882030b0311281c0807041270781120031080045840d20807500012080700c000d84070585418481181001400003a001c10461140414988589450076841da14a03c00007141c441380036003101e8840580628060200f00c42180c621030707164004440b00c2d00c0043c102601c3e0283c1075030500043c010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 314689595 1250 314688345 314688371
    0x304080c01140906070503070f1d03060c041410050a08070e0307090c0807080114100905041401080d03050c0a08190f0f060b0f0a0f17072c03070501050c0a0b010b0c01 73
    0x1140d00c01c1234591596100c0081070354080b103480e10004c1c1041b04040c041088401503039014020a801520000c40c1e59450394103056800400400b1003420f140701d120752446941101e40c1210a5508074074060401c4180c82c2d981b03410541e80200680c2c50940d00d40500403000c911901c05a01402d80701a29560f00300060340c034142c0c10380f4414805c1c003417210103118118070500f5510300320000c408003008030300e4194240f66452000c036042c1c61018404003e10340300c00d0010712240103b04014884200c061030180214101840707134140500c40c0400036000c00001e60006284403034241130341e0180d003005102c10000c0c4006a0310090041c01007402c0d0040d02418010001a1030181c3c000742c0703101004c224420381c40c001e0041001da40c020400d9002e0010b22501320001e034813100f1a031200d548590300c00e0320342031801404500003201c0e5055180c50550342410b049004c4403d0707100000d9074025120203003481c80d940c02c04440d003103207000d075600c000030718035540180085111100840500308a8402100900c401400800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 314690845 1250 314689595 314689597
    0x201030917070b0f0117060c1b030301080f0105100e13030903080d06080105010530012706060609120f020f0a120215070302061504020d050f0411150d020304080c011409060705 77
    0x2071506c110381c0c0000003181c00b440c80310008001500c5030399001b010240e9500801c5081d038209902840803500710707150000180e402030050590180c002e400003140d0034240700c01c031414010058071401c0d401e241c4106010406008540040103141c06c81000341c4c5500702c5203c01000b030201c3c2d0241941c50b500309000011a030520300c40d001d088040d01c0704440c041c8024640d10700c0d00304100c0e4402d08619921a0700c5490040003880e480c080d034500f02c1201041009460170300318142c2c0d40c103510420400c403e4031410890300701070b9061802090351203034814078051014000168482d49030304500394440314a42c400100010165060382e89a84240c8001c40701c1e44115580c200d10307025009010b03015030031030b0000900f00d82c2c80143c1d040750340100500050030210740c94419000c40703030b00301c41c403503501000041440140540240001c0345402c0445440c115149404850541801151507a480c4e103030300400450308203c4c42c841034490103c030810081007070004e61295040b030b1203000c0c0e8080c0344034090040840c2d00c42e4810700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 314692095 1250 314690845 314690879
    0x80f1903061404020d06030209090a0c06050307090e04030201111b1b0d030809330901090c1505040503060903370503070203220501090b0c0a0201030917070b0f01 71
    0xa50a60b003801465028480650f000d8116055419514800440141c2d241c075000ba01a404110040c44000c49519010100c281e042e0490400c0c441e040c010820540e41c407004050558070f030800d820859856500d801d9000d8500d6040468003040013107040007280118809400113030480714201e03151204500560351940d141c8507203a58200c5038614103400400d0044170603c3d0170a0303100084445204424102041603040c0c6800c149400c0c1d50b0860181030804c0d080203143e008034281c0000c01101016607900c41865030f15101d00811501c0600002d19540e0203041510000c0102170b0035500b0901d80105503503125441086c10208240070300740408a0440700c00300e036031038000100c440710b041180c082340141da4540002b00f00d0710441c8401c009046040720400380001ca03800f04032000c0c04010307080800240c09441243c000494820042c0f1055480620014841514580a00f00011016510b05041c2415204941d14051003c030029030007040103081e866061241c200e0b140301d04426600c600315003109184003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 314693345 1250 314692095 314692109
    0x150e04151e080a030c06230106030527010603050613080a030209060906070309080606040e1009050a050609100b0604080a06240608100b0f030403030b0607080f190306 73
    0x586028014160001c20401004401d1880146115510340d2068070748081d44104600152100000d44c00b0800e00b805a0004032259448851160644040b003110810052254104240d110380100b074403040c1a900700040754241a104400411520785418080c0c43d081c0f10454491080100013031903081e4913a261090329600900103464481b283c00201c000c0d42200760130603405003003001041101d40da00001032040c1761080d1a07140d000e52829044038180100184614011410408580c0d201d07040880c00c424100d0f00c0d554002076625041c14498580340c1090300081c1948608814042080d0000403022884c1041c80004d01240b1008424000c0c14002c034440c01c0b4642d849042c08800050540c0c2145580405091a40207103c10b4140400c00004181d84142c02280d68241403003651a0107210500c0901030480c2020303e00b81c500c12590855100051026041541d100c00103280c070341d1000102c038100d5802400e07282d210a00350702c0039022940601d494011404501e480300300d01c07034002d0040e1012a424 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 314694595 1250 314693345 314693381
    0x121b0a21060315051009020c100509010b030c04150317030f0a020a09031212051504051f030321020f04061d06161a0403021c020105060609011101021201150e04 70
    0x100d81e42006400058170045080b10302e80310100e0444464800750813902d090100400d8150f15280b0410102d0b100138081c4491a41040071103842d0303441c0080c0c17501c0e204009840005460b07580c42c410500c031126981004002024030803118106220f13080185005d80203002c00103586807259a4a40304a01c2101118400f040d4003c50800c0802c20110320320003003126900b00880b4200007039403802c0031680708490716880760405070512030050800c2e104041e4001e01a001c0c040066103580c0e40c0c1c1c001101e0a200080c10405a466140e03407800600080e00d840c0300041d03c0c25900d400601e402d800f42034006001d56400510542a04014a5030310000316101b01030141ca081d01e00407002c11580c0c6881100442502d03d401f044804100c4a0b101f00b2100d88510301070343c00f40454a40c80a081c010140d4901708080442e130500040c005c03555038060458034560f409091a0002036403a80805029006d11001c246000781c410000162280800300340b030303096003400e507200c04811802c44104802c40701516900401031314 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 314695845 1250 314694595 314694623
    0x608090a05070311031c030203100f0f1712031014010c170c03090901080106170a08030609040317040f03030f0216021e150403020f0406060203121b0a210603 69
    0x40307110340c40c4c881c002500340c8001d2207030341c0c0f01814511815a00940005d5001041000f20f270348071103015014141d0700b000b100079149400c0401e40c400c00b5500a410b00b141a40c140000074000c100224241c614080c9819030f1a03240541c0310007120f100301e2145040c203103080550080d440d8421144a10080d0340422003965130403802c01c1c07001c5940c200c0c1a248182e844100410381603a95885002170080100e140007007030031802d0095000100085894a040f142e10480c030010005855130143c0390300100a40e4050748c2039669040480d84000d00800b401d00d241c0d4a1020f00092002401032124228026141800308440030041c6000700d106041c0701c0345100149685040c01490420240c8110900b85000742189005900008001d96505042d01c4012000042c5c20011810704500f0103100e81d004407420800b02d4a808000783d140d20407008081c51b03c481c0600011400030b641e02c503800a610402003641d45500040380c016144150000c2034825159402e1890f0505031113500078401625032006041d01148 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 314697095 1250 314695845 314695853
    0x120f070909082a010213050f010f0909090218040f0b0609090d0c020d2a0b04030b060103421a0703110f010c050712030504170d02040513060608090a050703 68
    0x1e400400c1e040044000705240b03000b40040c05840302d042603141c510b1840e0408121a02c03602d81c443c0c032705000c035100030b0301441034008040008513691000040740007206880002c0d005110030002440001c084020322003031248900c02003002c1445420010482c0d200e8400700b14190200b140e40220031b610400c00d04503110300c83c0405140c0070748080e00b50f40702d0761201e994540700e0011070491a0a07134259580c500a41c03111500d1503030018460413190501d03103800d40c0c131607881d4003500030980707414142c40d0360340741d0041c0c03240545035032900d01c41030f855062142081c06290f0241004982c2e8425840ca111008100f4961085d580c8440c043e240c1640746c5058559a01034403000420700c200c1c880741c0503549900f03410610a01509022252942d200c550768041c1d40b81c4541c0681c051083c5034109460113081000042815010b5401101008282c5448020389240c1c0d001a11994000e260003d0070600a0303191560180c00000a9969603100c0b1034060385e504401a54508480c6000341140e07101010410200f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 314698345 1250 314697095 314697127
    0x14010507230d091e030c21050102030f06031908030f04031206030b01050411090604050d080c06011d0106020105070806130207021e090108030f122e0f0803040810050c0405120f07090908 81
    0x7c107045c8052180c44002030307190142240c000300c1d10001d0503e655000c015491500307001c00102160381d510f1501f001e00864440303c429001c0104184420958800400c06050103402101c40c180703a600380c20320042c0d40364074101e656644284030303030743c001c60a207844105090300e070000f502c0c039020317025040d1801e01d464101080042d900024054800040800200151006c14070503180a000784202623801404022030744558080140c0c801800c5916002c18000000d038090381c071903040710b4100d480c21249400840050020b109503080258041d50079807800781d00c0c101c03c0c41c400003050170840300b1505680e038031f03649582c0340d100740102c8540e1800200000f8040f007100c4841c2e981c0000c481d03950402410755404022a0aa0049000032000341d5000010803249500010942c090001d05000d1800c0510b0030003082e0740c0d5800f04540d00e0700c9545540c00584680a864203032001040001d24102e01440c824501980340c20400d07148805900448101003003119141c0519082290b001c00309601c1e0846a0010002c0c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 314699595 1250 314698345 314698379
    0x30c060b0a030b0f06090a0b01020d080a06090e1c090f06110a06060603050a0b010f05040314011b090911030105150a140f090a14010507230d091e030c 66
    0x40040d2500001c4040b40f000c50503d0310a0fa20890341501074117198040001c0307401c005014840c61420010503000756603001c6500030000c0140d0a102c1210348800d0146006000b594120b208240d24000703450640c1100000c0f010f08410b41004d1400c103101c0e02010440341948940120700790481000d400700300301d91050300c10112001159054400e103600503583d1300d090760703e2603000b030000a44440c10300030b0a00591090150101c02400c2400154040b21006004e078082c03803101400351035116a6080c00c580d02900081e041076000c00b0007845018201d04081c207040310350b000d10241103103080281c01500001d03008030790686100805401e61741913201821070f450b920140c92841005403014540103441c1c4000c001e0840f4030200a8a03d4541282d002800403800040d0f0004c2c21880310030558406a903045000c8520307032604004001080c01d007800d001424040b04080b295214424000d0002d80d0703c0d803040808055800d04140710000c2e140c0d40300c0488200043d4040545410031541041044182043e00070030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 314700845 1250 314699595 314699599
    0x12020c0d051303021c1e150902030c0a121203020307050405060c0c1e03010b06070209040227010807060306080d0f0e010306050409050109031709031801090305100e06090a030c060b 79
    0x90440c1c80e1380c040780714804441d0140b020196000700500400020818800e003284002004900031050f51315440741c0f01d1041d00c40f07440c450b540d0341020015510280020249020090320028485903a040c440c14048805003082d600c44942d600141c40c0e1510178021a400360745580d4900c0c0c101800c110810402d503200b0030502a8038421100c03005495140c040040c0f41800300300100216002c0210203150079950300e10300c160f100704010005c0000590300e40c036000b608a90107649440d0000c0414803551048442d00c0540d0345c00c80c180c44000198110000303815001c2e078445541c280109592188004d80e9140350b0400c86020541c44220070380102d10402e03059150420501d4013007111956103000c541214405101520141d4423526a0028140c100c0740c1c0402440181702c0c4080140790450300c0e2900c0380200500301c2051600d8035291620f0b0380c4520b29403c00785401c101941c07038105100c01150000c0c44004c000000740d014050000314505804508880c0703045c0c05840b075440d10005950341c000102004e44020ba = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 314702095 1250 314700845 314700877
    0x17010b09060403061406011b03050d02180a0806070e0d110907090504110d06080309091807090e0604032d0806030703141b040203100603020703030e030a090612020c0d05 74
    0x811405c5c0105030562200410301051030810340001021b0301c0c0d03814003141100106107011000a5441021a209640400401601c0320540e804220003075100e400e0b003a41c80b81c2000e0b030204403003101103440ca001c0c40d1031b030301c1d524103080460091094981c20004064064145100c260b0300d1b40c2000108254001400d02d40b2208a6446000041c200c403020380c0c042401c00c00c04600741c07082084c1445148041c2506000540c03d08100800084619034002e10400c902c800c001c1000725808070410a020103041001001d00c440407440311a603a90b2407084500b50001242c40030b03070441401c0d032107000c0a200309205021516441c1103174015600e2080280616405204000d8004045400e1030300e10741d00245036001500410940300d1542007948824031416114070702c10020302007070003d03d034410400c9501074100942c0300c4410f8202a00100103004441040d40400101055120340c0410208180d4050741c82e0b00f485075440000d2a8100d0064034480c400710351000d031a07440003d020f4070190035000c1000c1514 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 314703345 1250 314702095 314702099
    0x11010e0a090e0304030303050c09061b01060306020403030507290c0a17070206010f1e2d08060a060902030c0301050d080705030c010b09160206040308060409021507020f0117010b090604 81
    0x304440c41c48540070890f410108051080681c180503c0380c001a42000c2103003050003180c00102c9620668034407200003000c2e88441e803007060080d00a0001940c01150440d15076a0341d0501416035400071008540c2d4132103050500d04100c200d80b4119502d07a0311921760180b10386c0c0e1460390f03811a52224003090203010142ca80d4085101c2088085442500240d01900955141034900e020840c02508041082c00c03d6002114a640c0e500c4401c0080380c604442c000b0030410642c81c0000c2c0e00e40c2101c0b84d11118540a400841d0048001505a004402d042c2c4204840380d40c541104049000545009142c4941000104528a4108400c1a00f68002c01c50580b600c0071a541d0146540d20110100700e0302d0351690751140e000d14150880c1031784004d80f00c0400c0c1c2403d40d9460000c1d19514024030044c1440210720105182d41c81d0f80d0700405c442c69000d070103401002800f1501c080c80c0d4100c00c00407032081002500c0713030285510621504296413030b903500d00c1300b0503402c0c28540a0b0503004100300c0c42e0404414440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 314704595 1250 314703345 314703359
    0x3151509060d0c0305071b061d0604061d0c0d020607050c180108010501060801180e0102041d010e070c0c06080a0902040f0509060c0f0906091207030510050a0911010e0a 74
    0x1016425048807000807101c40f40c84000d016124018a000e09002021982c08120258801e03031904140c0d00c028009541141d108580c1c0a220b00081d030040d42c0e20441c2c080008105142c0c0c00003801703c503400c6000700410b42408503582d0382c01211010b10b8100308113801700c0c0018100740f00582043c602c9482500c480b0791207800401d403d040c169001205030f00c94000104151402840340c14003500700b170303d0280104d40c103210881458800341d112900040c0e81c1e030704140b0300301402941134030041e086403807028003040c068103069820380c4001c0c0100c440742180800800c1c4e03841e000710340c56440b0f03075401101c0483d0702c3d14203441950301040080c11840740b0340c1c840e102c03000180d840c2e204082c50f187d0b601400103101d04103844020701c3c2c904d00501030302049000304040144140204265540d44204464890b03548110340042400503401d040d58030034911800314003108100d0302013034078449290184c1e000c21950340c501060b141560840c210240006000750180c2421394460303040900790180250110f41c1d10f990fa500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 314705845 1250 314704595 314704597
    0x8070227040c1505090f01030b060d02070c0f1401051e03040c0e0711031e13080309120102120a0906090c27050103230f0f0c0f01050315150906 63
    0xc801408000240c04101c1000701401001010780780500200c90b0f400745500004c2e20520032405002e2107203c0c0154080ca03113038803c1d0030030340c408500500305a03124408080300030041e40000100b100d2400c604040450071604400103203048812400b0141c1e024400319005407880d610840c0c035089010006400c1501a070039180095015612590f082540d0700c0c9420101040d0701d50180c10301c403c100f02906002501c490002c00d4850306110340102002508070190740c2109845030f020110307661640360400252a0401001500c445101611307244040782c0f80c1e4035540e080780710f007525003400c0c0040c03a00810450b082540c003000b0a80c0c800c07200000e0104080d20b0340c1a40b00002e61107026500c18178400702e0981da21007005043d080111074001d21155042d0350303688442000c1444210910284440340001d40d0000f080200ca00c100c40c103050752100304881046a8a400c800402240501080040010154070880850f845595250056040746001408203c1504080d0076010b4140703800707212481950340c50320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 314707095 1250 314705845 314705899
    0x1b090a02031b0c0a021323060307050913060b0d03080103151112010602010b01090f052404031b0e07021c030f0609020702090604060f03060c0c140f0f03030112080702 73
    0x503004100740030351881089000243c1e1508540c0322800c1032020361007c0654000c110110a820140c4c02c0345686100c082840e02c441a0701060340700601c1c00600400700d512461502c0c4060041d0014032036018039009101c2856880761004002580381d1004102040c5040400c03c46490005008507101c949003180c0c2c1d21035000490790b120b600f01900c00410095809204288411000b800c242c41e0552500207441d9903106035105003401161151060a400100b284a11070b654602d07030080d94a880d140d05051450703136048150029410b118070004a25903030400c00c0c280c420480d0703071f001342a01003600741c1142a041200c2d209509150f15007055011480e030a000c1d1601070900b8140043c0ca9000c03500402c075a00d071003c1c104500983c41c102d024401c606040343c06e00180c9070070820200d030141010f10202d82d015002000600381a4044615132a4204d0100b07140c4c0720700c420300e01101c40240001008684a03c802e100740e050303a0036000d109070700161055000d01015400103009003440c1142c00081e00140e00c1ca2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 314708345 1250 314707095 314707117
    0xd050703092f1203090405040602120903041d0c160c03020a090b010e1002030f1e0a05040312022d07080706030501030201180f050f03101103091b090a02031b 69
    0x2064150b5250101d0880312002228a003015854001e811610fa21451a000703001341c0c0c40e03800050500c140d5404036022030ba513900c104d00c2d0618084d88140d07282d410030301401d140c3c008400408c51740c0b10303a0075030b80138000d90003410032600c0d00d044020888903044200c0c03002c85548a46110000140e40c40c03940040c0240303501d210119103102e0040006080b0741550000c140302c0c050402020401981c004183c0d40c0001f900a0314031b5440c8049408111208203000b14030215060000d40e004e000c076440340c054011284100140d14641102d0b510680e01c0b517100b10281c3c1040207000d807250810000e0044070505503034400c1c054030212501c07441504e040400c940c00070f0000c241c980c0c1c010000c650340b008400140000004215030340300d0800c00200c0041c0c003188645840340c01540b507071441680d410f02103840c4050050307038200075200c1d025001c40ea1070b402c11030782039595026003010000d0014100588620000004080346400c0d030340c0040010082d040980001207062981c0c0f01c0c0d40d0301024010040000d03180c9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 314709595 1250 314708345 314708393
    0x16030b0405041103150103080304141e0102090f04090515060f030a052404030503010b0711101d060c030f0d09020a0f091a01050a0e03030c12070b010512030d05070309 73
    0x269100340740c0f800740f0000e05e08450b00b0320903004002154210060703039040f950000d080701d030302c83c80302c0c45140c504801114403215030003030703861741800c040015030080c540340805403040000198000d0800084401703100010340f45400800000624281d00150564891401003400c1c01003030b90000800d03d0051080c1c000c540e40d40c400340080b040c503c540386140b04642d202005540311498540da0007407a50006100304050342d540443c601d420001d01803070b40001c400010300050f5010000d504001c00c0d0311040090303030241d071903010300c0e80c0352a0510004981122074901d000f58506440c0020400390355018070580f02030320b0307a10680c04006135201140038009081c0b02c0040301000d81040900c204448035140010318403101000c1110301030740c001099500f000c60f00c0c20803408030054440424150302c2491200713800d41c040c101014a000c0035800203060080d00940c0300078442c0e0780320018458001500c40620b045580241300340001c465080e0081940300d030342440d0104103c90650b0350303000003000307844242c030401c52 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 314710845 1250 314709595 314709623
    0xc02040e1914012d05040c03080c150702070f050915120303071202190503040f08041205070803040f17070b0d0e1014010902070503042105070605030f16030b040504 72
    0xb0074040c240700103811124401300011489801440505034000b8021101d40b1980010300344503900400000454000d1151643c814001c00c01d01c1c1ca4001a80700740322485840b4002c0f5a58a200250107030a84000d480422482c600305410049101c070f00034103220300c00c121840c0310001501c07150003c42c1e07502050001140c0700c0c1841e90001c2c002125042d0120505132060001440692441142600d02422424620ba5a48030b44c101205444402d410140801a0002e40003e02280c1c80031902212030048050360342481e2075000090f10b0f03110b40e01c43d000005942020500120341500d0fa0049461103680443d2503450366600141c140390000b40008010320f940e0340d48907643da02d052010307440c0c218111004116240b00c46420521605040c02803010a80c1e02103581c1c01040410001c0b50003400c1002001540f6078001b0344903480003546075404540500444000160660007034080c0ca01071005039660b11026600c0d03001c4010540c64400c2c0d6641015147e1103640f589417950321441d4000ea010384e8020580c1c0c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 314712095 1250 314710845 314710883
    0x91627061d13050d030c020a1202071701090c170a0b1f0806190209030102040e0f010501030c02030c030f0703050904050a1a01052b1b0804120f0c02040e19 68
    0x440002c044140b1480d42c04000000114042040e00f242c890909000811202c040806c0346488450030f4000d08904402010403089500003501d203049694101010700d20918181c0c40074244c6110690040243c4010340c0b06003c007070f4140401003014507600040b58482c4603240c8590015a80580d1400e88a52004018501c2d07103810307100c0d60000d030032014010811070406200c805150100c14003c0c840305a03010560351019582034044400a090450341ca80540c10540c8808d0000803084c80381d1400b091600d6054000d4034000f0090701d80790101d03000910709060000c05012115807003100101d0401008115102059496100b803900400450030005040048040c816480c50729101d4600d0510405115035200c0f1045941c1084401a2329201520801e482c0501e0101803c555800402e00c6d01d8046981440030340c1c80100c0c0e610a5008001d403800300385421001f603a04161607140d0388000348d040030143c2e01608050300100100911030085441e100e00d40c0e854000403e000d0001100d5105160042c2d42c0c0070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 314713345 1250 314712095 314712149
    0x2d060201140f0606160b0a060f0305030307140415050c010f090c030807020102010615020a030e01140702041d070303020f240105040e0f01020f0904060b0f09090c040305030f0702010809162706 84
    0xd80892240c00800504544bc2c3c140e80340001040e0108000d010070368504604000020742e0b0040101d071942140c9862215006407080e002402141110744c6480304a8400741c41e00e015100320290441e04200400d4255212231038280e1180c40c0990640d902c4450006080c00104100700210000d80c0c00b5102140007031800403c0c1d030100002d19410442e209903581c000c050280210760510780c0c1158001600300e290010b520322a500f24201e5840e501400c40000141500811503407900e08512042d1490b8092441c0394001e01e601060722007044803d490010300c29030425902000384100d0340ca08403020300b11022681c50030b80c1d010101818840e0f40c003040c0c02600e410203008110292207200c101505144001e13450b803d141c02400105d5100d407e0040104600443c2c0c039040340c014681080130b8a0399108144041081da501c500022400500100000381d03000c10081180f02c040c100100d880c1c00d109280001003024940c800300d00d080030f070080080c1451645e166104100042160410300d0720304a5020641d0b42d20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 314714595 1250 314713345 314713349
    0xa0c05030c0a0636090b01110a0f030e01050d1d0f0f03070f020a1e140306040203060403110c09091b030a0c03060c05042d060201140f0606160b0a06 65
    0x8030401041800880d13000310300101210740e03801000042410905200381204941140900e19080154001c280440aa00300c2e2081030f4080e05c8030f01a6580c9020600c2e655001c001c800382559003102102c000080c460030740c4c0c40b404103051501605000d107461072441269041040b01b0b84100703880c04010800c031420700034000c600008201500000810100481d10391180c10740c000e1070110014039220071035840319a8030000d0060400b548100942c150003403100344216009880c000880307201000054500095114411503001c2c1c090143d90b06c80d6a4252a02074554108100702d01445084603120344400314500d00c541801e500401940e18107005070030000c0d00103420b15000ea0003101c003220106000010400449900802c00916034503175002c11a01341c0240c0c0c011002207402d0410407030352960040960b4002d8150004036895696944205034200ca89042031018840c00020004035104000045a9030080c005494180340c6405006804454526004100c4001207801d040c409010514460000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 314715845 1250 314714595 314714599
    0x120a0b0112020a0e060a030e060108010f0f09122d021c0c08070b041b0b0d050f10030f0c080a0308040c150c0618061505031902150703050c0a0c05030c 66
    0x803510411600082c110035090304d04901803000098000581846030b4000000121000d0030b40d1119611500f040740a4026028002030250400048204810749442030103101c660040340a4244610010b0036194100614552006100c0403146e0f10901c01c003581348100d00c507001d40d001d010b00320300140c8120a44041c0440c0c50b4104003c2a088900244000c01241e6000b500b001c4a01000d60340d92504850900c4801002201c6010305540041c2201c0035401519201c0703181041030000da512030102c2c8041001c200c402c041034520922041020842c0c01a49440642c020481400351580700e00280c0d1502100c124110b0000b56541d04000601001c0c143c0e04000e0035942c148a50304284e0000b000b4000c90f451000903148a82d5025194160a04251546025076016505100b80e90b60003506102400b02446000c1c001d0058403100e015840181450b809156402490548910f5050f038030704130035411040c1c08a044c814108102001d100040010820840c071803121101c00302d0501040c54204404020518 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 314717095 1250 314715845 314715847
    0xc05010e030a17010e0403081518062e2102040f080f010209030318010e030a0b1009020f0d050c070b01080102030106031d061b0405270603070e0a050705120a0b011202 73
    0x2c04003075117120000750425098a4010542e07240c10784401588801080810743c0903120b0386d481070900d4280d00c1100e03c20b017022100b516030200d162101c04490310b450344d1041e121041c3d1190075000c8501482951303100c070141c80d030918400381c00701607980101c1c0d015410107500003171b00c80010011103104004011040108078029418242003401007940c901540380840c0f05900030ba000c5002c1030b4031034800140c06541c01402c58048140070708001412800650301c07601403a0010b200491075036510b000722400704690340b50b0589428010b10007000200701c040c15105880c1c0f010805080414004031195020707101c4d4030001a921b5141a5000d02100d4003400750404843d43c8180c42c00300b8400c003245259101c0c42c00170441b00d640c600b40c03004a0861242d904815400911850360072181d030b480d041e400c09600e03905420a80d254a8810402d540d03220b51303104a4130900c03000070016440e440141c1241c7c0d040a01810706c1da080c040303501c2d001110000304580c4d202c0003c1d9030b40c8419000f5a807200a00010480c0d0701011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 314718345 1250 314717095 314717099
    0x604060b043b0403080403020d020f07030807050c0307060f031503020f040c02011b2a050303011e0f0311040f150b03090307060203011d06030d1e0c05010e030a1701 72
    0x40b065001d0001050940040944280346504080c005038420006250030407008516041c6400f401203041a5426001841115100c04030113000088500703071043c034480140000d5186a80b4400c0e80e50200e0411692801b81084030030032518100100b074060301180d2507910740100810320081c200d07040e104c401142103c1510003000036031550450074011050507035002c02d0728441624213070702425040c44000f800301c0908038141c030306d25032003c50200444200240c0300849008015000503400103402c01400e0364100f00b00401c5030113104c000712551081c0e810302e070040c1e050792500444914001075006039101240242a03020500d0f0600c04c140d0400d40d80390082012111034008208800c846008046080b440040810300d190010003d503060160b2011055549603180da2655241d224000103400d148112800031410718a408110301c040e4680301d0340c0d10310f0401d047c007001032003104001c05d140c2d013844091085400400c100307016000d00703030b00f0b298020341d03171209500da0040c509603000c8550041f5038445001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 314719595 1250 314718345 314718359
    0x60907050d02130605090a140603030906030610090e0a0203040501140c0913060b0f070c06050f0304060b0d051204140f09070e062709070f0e06031305150604060b04 72
    0x715420705a0155080c840030324a1840300c03c0100f0b01ea40207107600803004410800181c03010b80010220f0514a1400103142e12010185030790f07401249091680302405100042545c1018a014a0403410034a884203490740d9079a07000c540c81900ba24500c200c3c50b000801c010a205090042001d2003440000201040c40e0494902500b0701a401c402031140e00b48982c3c800c2280000d0f0000710151020400440d9160403c00c0d66449961000302c1c125100908428002025400fa400790360f502d04408440d41d00d960346560750000180240442183c0c400790005441003c250f0800c080030101c44400c00ba180c8c0c1e135040c4468030640180c0501a144615102c10b9850444d844806580349c221140381011107030b02442c41e00107807690003411414090000880781504950124124010000c241510f07000c000f030300d500744200c1d405100083d9040125089121050302400d00340d0042d42e10802c92101200302e5005541e40130b040407010001581c0c1c0708840b02c144101c0349890300c10320f4014200c82c11010f14040c50584 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 314720845 1250 314719595 314719609
    0x250302100f0f02030114011803030e0f010318110415080703170705121e070b0f06010e0310140a05090615150a03020a1205150d060f140906090705 64
    0x40c00403049501c4032845003010340c19410a800ca0390500c50305545941e16150300031801c000300d60706107000810241c0b1074980c0c030034040110003d40e07415544080c987e10401040c841e03852404004075042550310031729804102107810f050740031944141c0c1d409540e80e62100c204030a0b038200c0c0047c0c10f00c56059240070003005c0000a03e1000326a400501c004200c8140d44103400716008100001c0c005000705043c040507024407000500f072484c800d401c5400b021500650a60080c01055401048001da580126289248124005612400500d0000007250410f4082818032165001c1c0551441e12400d5410349158955040742d071102c1145810009454203142246c2d650202402a0075541003200e048103c0307441e061025408902000300c45555070001c0300004001358401c0e458a0005111000b42c1c00240350715000f15809041d0140400541204550411040920018045500560758461110601c00c140210042c01c80071001071210391400e0040b05082102c028800c01240d00001005c2c08076a07a10f031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 314722095 1250 314720845 314720863
    0x7080f06010f0c060b190e041b050d03121d030a09150804030f0507170d0e010902100e04090204151a0c1902130501090209040b03120f072303250302 65
    0x10021413111060004211010018150094913040d06d0501040c120620f103c483d0040d8030601450385032500c26400112a40324900840d0340c01420440700c50040391184441c0b26100074120000241c9400f804c1c1c2c1c00c6d5025190800b0700c041a080810441141030300900824024081041c01c400080031400004285c0c41009000800b84841c040d02024454403540580c3d50656200040c00c0741c141d40b181c0e1840051300f190f0300e12110142884201c9004d400d040c041c5951a40e8090608081040440010348070061415441034000c0c2d500d01407903015981e20b0107040c0844042202892426050000b103070b1620301d5035001c1c403070f00013010855084014400253b1100350624101e42e10300c0f00901c1d02c0050318452041a1600c800340c14003002040f442d600d54020f1000c410125801c0140072503d9043c181c27246035484248018600030b0200c40c0b181c1107404001d0004130301ca05140c0e07104405044c95010455240f000c18904c50b8000305544942e40d01c240502c1d006051a59201c08540ca1182d6000303560306582 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 314723345 1250 314722095 314722103
    0x5010f020a0b0612070305010c1e0c0f06020307030b0a0b030103020103060b1c020702040902040f0e0607090807140607050a08070c0f080307060902010509030a110a091b0e010c080307080f06010f0c 86
    0x800c000071084d11042c0b02807005940d022000703010030003007840020020b03285003043c0400b01c0003203000710700403a010f040c02146142e4002c10802d004c0c401500c3d40c0c402500010042d1090580720400c844be01c0c0da40f241d000000d8800e1441c9035846c1d5041d4000102200c0c4507070045034555600700b00319900e45040e004a50b1442c240b03a00050b030359504500c04540a80403140d002500541401d58200a0304410381040403110b1400d400c079211a40c900c00222004112441760038a20b810117002441201d105001c0385000d184050a502d2801515540303943c90482c2d030040903940740401003081001c00c510700c803400e8001c0100d005000384080c100000c650f2207103d500c000520250fa500851001c5900640035075800440040c1550154003031810440c98980f80040181c1c0305139982800030403140c0b601d200e03102c1090486401204440c259400580c3c40402c0345203824107225a00c004000020803480040d441000180d50f001d0083c10b103052803400e1458081d25840c18068404180c840141e440b4000001083e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 314724595 1250 314723345 314723359
    0x2030405010c0b040219030f0204050c180111030f120132041d0d031e1404020603070c080a2601060e0d0c050d06051023060a0315090605010f020a0b06 66
    0x5944001503801b00700d0540114008000d8034004140700c00a170104039554001d0b1400d0055940c0c1c0030800a261050400c1d100f202e20748007120103000c1d442180c244c01c0000c521801c403072400c0014082040340b074002d01c5450309280ca481d4010701141c0c00744e81c0707a6000e80341010b0308083d0420f412850610390882110045005950756020800c421003106051144d0180307100a840c038002e1410b5004014000349000300800f5041020708003007424151061150400305140941d01580302d540c204001b82e44050052810080c1d941d90810100711180020a445000c940391400f81c0030141c000c0c498048500b600b000c1685800c480100495600040180d40c402c20850711841c1003990b603e80b0403143d4075141c000640010161080d5070401886621442c082c004410700758810561b00d4215250720061650500c0c040884000400180d040c070700b024264483c1181004a00c4d00082c0300202c101804030351011030900c4e200c140030000d40d40c1103600700c92040c0032440a040301c02400d464050b0012000b41c055801420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 314725845 1250 314724595 314724601
    0x8030a0503370f0c08060607021c150b131b03020f040f030b011403030a0f030c0e04091a010f12020d02011b110901170a0b06030c13140702030405010c0b 67
    0x20351800c40602d500d0320769211020824902030040100002d0889451036403611011021083c081c01030390b8860070300141003502e0124981c2c00e201c0070704c6450310450902c00c802100c0c0c80000d080f003001d01e5031040d55039800084040e03202d41040401283e0048285e400d03850045c015422840003134800c0b10038229810701503903038040001d40001f180300c0c030b40c403208001030415004410000b251021f0340c105c0700d00300281c2d0880c180300b20425803640b180300c0304540400c10040360034484a001c0d03000030090703564a05200b445a07000300e0101d0142c1c4c0c80808220307900e1030701c0b0024116419001c0c8143c1c0c0500614541c004a141c2821083c10040c619040c0c0070b0310074140403401004681c85495006a500c1800098503100c100710302d0400e0402a540c40180c2c841c01720725001081e050744003c5c0c03104c240c0404e80010070070035a0316111b9155071840540702517098004d01d5040a110344503c028003040d02c911a40020b844010705100364049040605403408641082008026903130388410140c28054220340c0d0548162 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 314727095 1250 314725845 314725891
    0x2011a03280209040f26091e041d010e01020a08240405091c030605010f050903030c0f0a1e0b0604021305030f0f07090c08011a0d0c05041419090908040b0c01060f08030a0503 76
    0x1d50a201b0079442400d0ac4030001030741c07020300140005281581f0092000700d0316541c0d41400d03800f84815202c002124140001e00c510022401c088114405140c04452444040f021605484e000c0b684010310703500104144409503401e000808034000e0740c0c6810003e040c00c1c0000240044204224102040004103c5001a0fa03060044075080e0003504101d81d411400500c060791034100c800000d40b041e042c00c1c0c0c882c1c100d11920758402014294402c0c4402c1c40c51b52a1810040250001546180c860fa0710391408107068408000d011040e80107403000b04000c2803415105490a001c0341c00110789941803880c074540040e00221401d043d60020b4100c80f00c0c0d14140359a44d009400f60803994003c4504044800403016004002041920704c0d42c3d0661816098003410300242281c004c0e104100740110b14010401688141d0051402c5449210018503242c0d4426004c0090b410111456400f0795580c0c0d410401c40d803903030100c00000d101c1d000240d41403000c4c2c12405081030100500043e1090b54000d850701d041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 314728345 1250 314727095 314727139
    0xe0108070c2f090a090302060703060b03070305042609240a050319050f16030c080402060a0207080a080d15080312060109030506070f02011a03280209040f2609 70
    0x3085002d0310400f118984801d003000600000b0388140e0260040030080f034001c901c42c1c0200010313200c48205d2149152030303101080f401448001c0c4295813503201a581d03100d0540341d09806541203907050b044941c030390b5a2a400c0102c2114a1a42080c0664040480315035005202e03040d0f0307420a00b5401c003641c4036994155580c6c2c580d11007049140456160000300315040459640b00c9004600180c0c8070781880c95140710683c00c4418601d22a0003046910f400580140751282c004e0001035418815a000c540d81d5000c1c45240820314003044540344008142c802c48108070384541301000c00f445d20a89030142c0b0304014035450344550030080d08044550b40000e51564014900e41d00115400b600700c1d0400c1c41c00d250000c165082c26151440107508100342c5100c06008440d0b9594980e4000303002d0400455407400000712200308040703118014002c80e07808005030f92182c06051003a4042c240440c3c103042c0e02c0c0340c4a1212200c000c0004c4c41e402d1104c003400c07070034280c3c182030b14025001940d0304845110a00e000703500c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 314729595 1250 314728345 314728433
    0x9020304020616121205071d01032c0c061213020a230307060e010f0c06060911070506070801031709030f06070309060e030702100f0c05030a0e0108070c 67
    0x180850000e080c0f41041214075541c00404416560603001060480401045d01d0090300c002d4001150b04c0103149000114051410b1807840505000a000c000981040c61103a02d003010303156600c4102c141000d180d0410b12440810010840d40b0a18210622003030b0595054003811000910540110020454644280700f101505400101036a08074244408800300c81c80c4001c030700d001e4090814005001409100010b218440507100c2c0900b04d40306500880744146005000d4584a45403e4001103844807445080240c203601d401d46035030741d03d040c204a850104c001d000401004a03100040000c90042d6541c0c8c02e03024548000f0a90314000e120019141005030850884280500f0040c00b03c02034040d0300006c3c2175403090400b88926041c51400d55164054050007a4002d42c4803204490054480d501e001030b10246414080006003894a0352840c1d0342150400e41c0115400b800c41034880e681000303045038030103e18500301d0f40d448070b83e55400c3c0070103d4880d40c074445070303030301080d8a600c50203a4104c01c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 314730845 1250 314729595 314729617
    0xc03050a060b040f06030305090409060906060303020303180706050d020c16061e0305010302130e19060204090e1609020a3b09131b050607051e031201090203040206 72
    0x12911400d040000003407102580b1a4443e92800c100481d49051902662040780e405441d0705083c82d06420034000500b02c050703800c4510603940e20f80100051b640b0b1060402850203070380110b0304d030310700030103039140c2c88020051149940d030000d0400c0203c0d42d407007005c845802d03c042c0301c05605c82d0382c10660280b80904400e46c06102d100403400c04205540c1c04031103a070ba01c17079981e8141c041050320314070141d04032082804083c0d00715045a00d6420580c6054001d00ca030b0000c61001c4600d00040d90700304000c607042c4000105c0b45c01d600003504210004440c018100d0051803d00135025150404411001540d003603c03498260319008908081ca5601543c0105400076003400d0070b40d4000d9914040988200d107000c2c5c0801041e040d40c0c80c011450070420074062142c4c0e8802c441d01c0d00caa00c0d503220024500034490040d0711070f1200d12004643c0e603d51001402200c0e20410040014450403a0407258100360400c011241d940280108901441303080c030b2280c115401303901d0050343e1351503034004540c0c3c510440784616 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 314732095 1250 314730845 314730853
    0xf04030509130c0305041e05030d0b0604030c0602100b01090e1308090d0f02030f070b040b0d1e0504050f0d0203040b09030102040504060305160b071505060409140d090816120c0305 79
    0xf411030b0950011403241f44243c88040404411a5802c00f10a01c21036014040ea842440005081d4125600c42642d43c0002422941059038954034030300100c81e0303900042c00581101c15900750310300c0300e40206074a04000342801d170034050400c0b5001210200c020b00040c8040c0b01411030340144000c040c2100c000c0364001d001c02010346098100320a20340e40d81d44c0c2c102d00030f104550080950b43e00c042100c209541c650303046186081d140c90105000c80e0006c2d052116126507800d05940044030f03201c985942d184c0300f1100840c032490142070803400c100c078458552404d50408214551566400720459044d10805101141c5800032038001c00d0082c00750341c20644d08140380280206c1070041c0000c49180d00e41851040c404080d446004000b00e42c040c0074001040c0381601c411202001000d80c20141d88010081c5c40099483d940b503d80111580d0080c1c128001c5401c010703020074a46070300c2aa4580640b20342ea004103045c000240003014040424071804d00188601e00c0c60108005203030641c6e10003160800221 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 314733345 1250 314732095 314732111
    0x60509150307080f0309120f1b040f05010b0a051e03010618120201020309011b02040504081305030f0c2202070614061206010e07181d06090f0403050913 67
    0x594a031501552154801d102d0004005003c0c1c500088044095101c0400346040010000502c80100e860740c4403510750b8000d4000050700450b0410503411900041c8112031081d466020a201c1104d0744041200030b03a5041200500041c40890201d0b103500c0643c2c07500981e542c03002c41006a48003140303000350800341000000010320320b6100d85521781245c05030940c400300c0da641d01c014458107031410400902513042031014148030b6006218030304c11407504c5120550004850341c009000c44800b21402c0b00c01000204820400142c3c0702d03683da0207040154010705440031000c040681d142d07602c0240a2003150150280200c4000c010622000d03071140c1c080540d2a103d5a05d844000b03854400c0303002112001442c0040c9803031415001c009004124079001e82941e03403c0c02800041420010482018400f0b4800b119007840703924828100144180d5819010420602c6031550a1120161550b4443e4500c04240b2040031090890981c00550600b42590b0744c080071408141180100c00300000e00724602060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 314734595 1250 314733345 314733361
    0x3050102120609072607030f09052803080a0b040b03030315030111030712050907050303040b03220215070201030f1b110d021906150b0a0306081902040906060509 71
    0xc120300030041107858800f10b60b10540100e482501c2000710b0102800c0f48824040781c040343c0c8560175002100c52801169180411a66009513030701011300b251075030701600200e81142d40307228a180500402450340040c4001c00d80307006045200180c491a55541d640d0340080441d40c0c1c550007040d14540107801e9940703070f282586c0140481e10700081c00b00c0c06075080018851016100340b0441c1e10822072610354040c8001289407400080400034001e04a80c800c0d208003082070b540800141000703040139810b06a40380f6240c1d03081c0e1188000b0800d45d642c55505c85000e00b0042c1c0d00c441e2901048101c00e05042d454680da070004070003405001010302d07100d9240401c1c0d0b10314481e400502d0300d01e281e0661030718032101015080585d60389229001100068200e2803441500170800707074140568a000c0c60700400c1c1c45544a240002d0303903660758031098403204001902e40b022a054042c2d18020400c1c08050a2041c0c0e859446114035040040700038443c2c2c0d07942003c2d03002c100c400c0e0311010103800044c0c1412002d240040b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 314735845 1250 314734595 314734627
    0x1d37030503040501060506041a03040f0519110916050a02031201170c010206040506070e190b0c061506070b1305070e01180605150307020703080a031b03051506090a03050102 76
    0xc065409501701800800c150070702c8012102241c80313140168000e14820400b1038038542004e44111612a02034404501007403040007159601501c0000c4260341d41c1035841c18422159010002502031140c1c1170400c012000f01140f42c41c45201a0300b800341e13450240c044101c0c1540708507a0741c1d09860074075400218000c1401000441c241190200b19407241f102c200059035a4241114000c0099002c0400502020302c01c14401c0b81013640640130301004101c8016248001c10f007074102c00b8820001142040c00110100641904019100184013004568401041851107002401f600c0408180c0209040c034846005a0364115049001d0380c42c49600e6418140035040c080c1b01e014074480d110030545840a14612440003101d40040c1803540d4404a9492120140c100511000c2507004c0d210000020070010402002081c009940c00907155080b04c1840b100303040c42100e40f9040616240800c0801004518980888501142c540303484081740d00001726909160703000203000e0750010402c442c080741404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 314737095 1250 314735845 314735851
    0x215060d0c0911071101030207020d1407090504121b0b0f1305010e0d03060501090807030f0204020f0a0206160c03021e03041e03141f090201020c10020d031d37030503 73
    0x2005d00211140c04011010b0b40580c2c0c0303019502201140c1e10300002020086202100300314001541d00e001e40c3c400944089070701c05c0701d007a01c82d13401d1604070702801507204140301455021062030051a031041d86070210a00402412001c0e41604440896085144d25400b08400ca901c13030300030301c06410042080341e22400c6100500d40440c0c180100454151f01a0680809496003280148029031543c0c44d04803408110074810ba0700564208108400094000c006003075210854006140c24207100b41c004414420225982c1c04115049644400003940498124010040343d01c185240ca6501c0b24110304510455000c0c1c0d520341045401164402d43c0811208110b9024020000101c041e281c0810745911654528001120001c111020810b809074070140542d03006104840d40c4219000c04100c02092140140d00940d0200c582042125410300402038802e4170380400b9065030490a0942d980c505580c0001c03007004800c134080329140c004a1039280982c60481c94180e00c0803406007400342085d8010f03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 314738345 1250 314737095 314737103
    0xa0308120f011503050a02040e0f0106020712081204050c03031b010f06050a18020d0c03020702030118171b070b0304021002030c060c0f1201140406060215060d0c091107 74
    0x200295541c402210000e049801403000c0c039000e1081450118028040106682c01d22542070001003094054800b60a00c03600c0f00403180302241d41800406850011150f00545003203a5000b48031001810a506079910b03034108010601c2c541d113591510f1814103250710fa1031034061202080c00c9995035002d1a6140c0c1c1000c00d08001c1004106c00303041c1c0d405851060240035004809440c007000100307a10700040100f030180f100d00609202c403981440c0e0a032200040508c00080d00400d0050541c9420b200e0a000c032802c0d404181071340b861566a2586410050072070303421b14540800d00d00035620342200400d03010b0038900c00350360300980c50b0711000301260020f0307500364007c407003910140780b45038000011203042c106c00200410f0b0690390b10000f2510756000d803212004008040c007144094100558a160280038030f4440d1010400301c02c401d000440c3c0150788114215800484090ba400c40101100e03034000f40b040d28850b60120550078906030b800c0ca294000c80c00503180064480480d00c6000150500f80e1107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 314739595 1250 314738345 314738377
    0x203030610020a12140f0406030b15180f03030c0114010e07080106080c03060f0405070c0314090d0b10150905030d030605060315041104170f060403020604060c0309020a0308 76
    0x12207049a544070304000083c510303440074181c24016402010b082592105110b4040d152202d070b0a00071043d90059480580802e4591180701c1c0c251500c0921400100041d0301340c50704001e5128071900b81102ca8680080c0108403941c2500c00b0364900340121101d02921200030b0286401d1420455040402480b036001c5540c81032011461441c4981c80c03403030407124070380c2d284c91280d110410f1400c0240c0c03001c0d2080e5440f050b0700c1c0c0d0810280d03c950083e944620356a07107c540c010f00c06420050304000d00b640403401c4000c802c00a050542e86c0d52500180000d0308659000306541d9410403650700e030f403c190058100418020860070300345a00802d01d105440c41a01070724000c41d111102501510300a01a41d58004000e100090300c5610061100e0b0b54603000402c08681841c0d00460250540d0141d044119a50b015400200069008203c003101c22a0240024500c912b0309440003525030070045c0000345100c2d211050460345078400e40041c040360340c00a09420050f80ea9141110140d13021010302c1030102c034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 314740845 1250 314739595 314739619
    0x816051e1b070f0806070f030e03090901090c0807030e100513060203091e011401060804030201061e1d06150d060e010905090c090603251e081005040c0311040e0a0302030306 76
    0x740885c070b02d0301501640c1c4030303c00c01901048007034000e0070480b100500c0911003801ba00c1030558403805407074001c11941100154100e01c030310b001003800b00020000c2d800d25051075120741040000040c40a40842e0a90b8005101d0701d4a90002605211540000d02250300200a001c0c203040045000304900001d10150070444c02034000440c00d8801c65003a1307100d40e10301000100306540c041d6501c0703644148a840000303107141d1161030000e442413121703521413044000c2020500075071513034107008480242156110043d0b8036002e030001d01b07218900c00000640100114400710030200039003200c0054050302c020340d00950b07142c003018001040129000440b91182c0d40b100e11441c20890580c6004901c090094030319080e030120066a115a0103810709140e0362040c900064600d00d82c0d10804108880c40703000d41c1000e02d040e2a1920301100c1030b41d003002051a00040c00006a143c0340c181c4210f990002000031700e01d00b8200024000c003040c5503103c00e1070250552200030103074040011482200c0031298001e11f46 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 314742095 1250 314740845 314740859
    0x3010f06110a0311030706290607050304060e0102030c010f0c09120f030e0109050a0e04140d08150105070503070c0f09090206030a052a0a0816051e1b070f 68
    0x30a5215900c1082d00300464010100f44103003c502c01070400441100e140281d0b542d60501195040380501f42c81c1078003402c160755000e6101c4100610380d14201c3d070b05030800b90346840d4141c50784280e200b41000d11084840316843c07070b40240166030000342c201e0020001ca0986100d480064a00146442d0004007440004110482e26034001d01200381c01500d8601c1c40c52403507070700f03940341d49020000c0c03810310051010008103992070700030350005454904040400f9082902d031510344480d00005a0410b6003240810180b45a0b000642540c031000c00c00ca80503050b070109006031650320070100090413a000015800c0103000200039a8000c0711554805180400e603941044002c44680d4a002540800100302049051f003040d04130340c0d0000c01045003910304220701d60044c103801e0815a40c500c083c07580445c4440c4601d030008031213580a4070b081242a8141c600340b500401c144a6580d40b108520304508500a19800c810300f40c400d03401c0c0d6400c100070010303035181541d03070742d5500c44c8110030700719200d4503000c9099 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 314743345 1250 314742095 314742107
    0x60118050c0a0203071502040816031b03021c021503070302070c05040c140304060f020a02161514030403110106060908060c0a090e090102160312051005030d030b01020304120803010f06 81
    0x4400d02e640034604241e0640da8034440c15019130130a10703803190248030204040320280b007619106061302da0b59040862562401c03660013040711441d4407084030307484000c1000d070f103a84150011400300c00600c1c4000645a1001450f078840030345c28030040c50408030411041640590007068800d000c0c0304c0c1d03039404e1540e032002c010070780740003101517000506044007229402c003801d401707150428880e910218081044e080c0320400c907004078000e0801603008040c240101c914030040391001d8a041d0425403009050018083c2c244070700c9062007072700042e000002605051103100c443c011522800000d000c05175590000400c062001d00803284280550030100328450301141c00c40d003200c110380d25286042864060070103078400006060b8055950200700c80c295100103074600c0d49959100391035214002007035084400859100401003807100166010a0150f950700081d5001614024034000c1003002040300100e007140166449800c1c00f004001004040081540103541603500d0458101c10440d5211030490351 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 314744595 1250 314743345 314743357
    0x506031308610f050a051501090507050703120902030d20070e0a110c010203130b0106020105091b01020a020a090e010c091508100308070507050f060a02070509060d0203060118050c 79
    0x6400c1c0c504518400d0003035a0b00c101803500a590440d070002d81c940303880d800d00c3d0420070112019089601c5403048890600c9a00d405000c80d044100031900d0401c00c0a0003621607000d02a051255040020811407955003000510581c0941602d07030401c441c8401802c0e480402c42c0d542c03e0006602034060900c00009502021a80c243d030403420075131645000c110040c00d03c10051880c00208000c0964080001d000440c0900c90070300c007804010500c1d090100c100a410f0304a14216414401440342c01c620001b20032507902440c1503148445a207000050b4500001e401c0c000790001ea0040d00003a181d1250341c007460060b0f40c00d400034404000c1096003100d52115501a082c9124a05c080d450495840b0f60b800c0e44d07100f188455004075260316600d80c0c8000d40c1181800712900d03404802c00340107a051805410143c900d081d00c895003081d450785400780d200d035500e0140718051188040019500d90740c00b0704015080da0080c054481650319600040740d58090820103198117070401c4003181d00b0b484010101c4e02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 314745845 1250 314744595 314744737
    0x504051b0f060901090b0a020f071a0901140d0e0309040507030507050a0f0504050a08010b0a0602030a1d0409061118030a031715190303090f0506031308 67
    0x24030071041008000741604010001d0f070401c20000d0010400c002071500401a444540e001409114021313100c1031300d4030f1400e40043d20080c005140b140c141e500720b8400d5031050202401c040c05904d0303181d4003801c0140181c80003000c1d06414102d201411f88001301c010954a01c00b0388007813046540312501501620025142440010404c0022001d400c1c45030740c2d00300c1ea4014a02d40309140c2983e400009410b0482504503040c1c036551050101d1061074041074000081080d40050350a00841c01800380880700d05d51406c0c2e981807200c0000c1d4946503150b610001038103600a10800400c1841d0b45504804d42001c81420381d00d032428908249a8030703000551a1100d139055850345c10f82152070a42101600c0701521074100745000e00034410041c4c0d94207900d15045154120350000c507a01c0c40c140206002d150380d00103c800126108140510780300c0004481e408014107000042c1464507207400e032094407038224460706d1b00c02e01500400c00c001c500500c00c1892184090b84190344501515496440598103075400d13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 314747095 1250 314745845 314745859
    0x705030601110109020306010609090f0608120a030b040c031415030604060e0a0b040302060915040804050d0312090605100905090a030818010f020406030e0f030f091f030504051b 78
    0xc0c0a58800d0b50304084140e5000004626005554007207407800b070080c1c0051010031030291007400901690701c681d901200c070801050007030626005415464051141d142041c40710001518030b9480d0191304001d01d00b03171020384100710030009202d00800608000e028602c110005801140c074001e4010680e07050140010040d091540341c036a40d010080801958174040d501540815501048130700c1106031066009401419462400b803410038100304d11042142a506007850501010889240954084da00c0543c2ca04102118600302038402454544c452000b150400248608108c0c990b0003050083d107039009807001c030b541c580012a0075150210b0382445180c0c02610040c003ca8802c10000f5080b29000b00c2e50305c3d0007019099640c1c2964060140e1440b1a43c00180c10000c1c0c030b606204401e03000600c24003130142071522002e82902c91107580505043d0046c00720f01da050aa44000031540f000c2a9a11704040c0c140d00c0840c05000303454202d400380d900c0c2c06001120703900c183c0c2080700d404075010001c0540d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 314748201 1106 314747095 314747101
    0x803070206100609031104020d1410051c1e0627120f230d09050f100b03070501031802060c0f0d050a1b1704120605010b03070503 57
    0xf10080003030361501000442c8a00c24802d1007100100c80160396009000305c660050801c3c03840c0c031001208407000b07103c03040c5107100b01d09040f07034003da9200c0800e50108a50600a05960030090040ca03c1c8400f201c0c0c1000d4403108440c40d4a100c1e200c005030900c0d001e41480c089501011020407441c040c644414144942d450180e503001000d4a03010310100c40d5004000c2c6100c2c1d05e400038415280c402c1d50b064030141201802e0f540715410310501003040c610b980c10040c4e03498080142c0c1c10814001c03144034400700c100600034407540300070280080801c030341303040c004600824540d40391072481240720140c080180c1c1c0d46401030039605075076030040482000c44100c0340c1c01c1c00c1d111022035050050070421402d0860300038019a1103280380100155001c50507041c480c401505d02e1124000f11078000402161000b05c024030b12800600445007080580e0300e0700c05641c01c0b84015204100494020300c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 314568345 314748201 := by
  have h0 := BRFrame.cov_init 314568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 314568345 ≤ n) (h2 : n < 314748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
