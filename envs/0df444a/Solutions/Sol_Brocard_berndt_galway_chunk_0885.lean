-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0885
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:27:17.223211+00:00
-- url     : https://prove2.me/submissions/91fc3128-cb74-4655-9f33-a01845edce5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 158992805 ≤ n < 159172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 158994055 1250 158992805 158992807
    0xe07030206030a140a0614120c09070909150513180303020f04170a11010809100207050f0618070803040e190b04110a020106170312191d1504020a0b 65
    0x202988000c2d0001e401108030142e016103542030030802c81014000901884880071f00d10400c208071307440d000b007130203052043c3c42026042400b0780c50180026210010012814051b900e41e000032046014419030308a80c01303000b462403c2d06e05043c10883d00c04400c45c0402c144504000300c0c0c100b100c0c1030440e440701c09070717040c00c0062341c400010a0400560007903510010031038501c40d0280914840201e9202001840351042d0002010488019152400c044d00c00c02401ea100b00c081d0001c4032510307801025540e0282040b03c4d18a4148102549065000c403010010f59049008044810f00c00300507101c05400c0ca00d028505103410410100d04144000306014900700320303082c01e006d0040d020f900c12000280e0241c0148001c0110801049165104120040c010f40c6030000025524100d9000d68664401c030401452500180962200341207001070415000c4102d80100301d486910103104d116801143c8a000220700e418528201d41480c0d01c0b41500c0b41c4501c3c071308c0c04200069603210440000c0c2c80c3c03000426 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 158995305 1250 158994055 158994061
    0x7150f020c090f0708091c0e0a030b0c04030203060a0204080c011214040605060f0105070b040602071e0507030b090a020f0103050a0204090f0204031e050a02010806270702010c030e0703020603 84
    0x32403a121010700103940081000c0c083c45050f2844100d518420000358031840e01c40d444a200d140e580300d00c2e00d00344240c440c0300c1c80c9200aa09101e0044a070300c098008150401c0c55840b901d605181000c2a13036104581c0c03800180030011824280101039006500705801c6041600c0c242c010781d100d5a900e02e6403030400810180c42034a04e00c4542c000003045425001044041c0381c9403401c1d5008110039a030040c803456001c0e24040e0030350711800803200d042c0d521100c8105282c490740e40d080060b40003000201d446903c60714090642c0c0c4d032004c5802c001580180020f003141442e504245200d0400907094100c0c40c2c00c008500b0300075031189100c10700741c00300a00e4001005c0c0d6400d02844000d0040381c1114a0741810f0594486000f805c3da0080c005aa000360400d081855401a0b2650f0500d40940c0091464010b0111000590b01a46c20a03034000f201401c8141454003427020f5074009003a03001c6800800d2050030603c200706509102c2d0103192403e40c14108078a02e03540c03001682c1d036010384c48003c0c4620000000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 158996555 1250 158995305 158995307
    0x60402060a14030a0b041a010504091503120503040b010f2d0b0c0102070c0501020d0909020a20030c010507090f1413110304170715020307030912020a050c0307150f 72
    0xc0b0111241c44403050984031304201c1002d20103080c085c03001611a40c02c04080b011100d01074602c40000ea101619128a000d00d040790070000f41a8071050005603011502000011803180340010000f1442651140c0d9607180c00d182000d108881a0020088270a1098051044a045100b003480039620650070078089400050032585100042c1c101d07000c1100c011a170060303030074015000342a59505c05d0442c21062500c0c3c100480e9100c0318031aa440008096001c20004044c00340c0c000d00065402c3d2a101c4401c031292100341e82014075509c451202c60b8030002d0b8050201b6800e1065903040074251500380040ea01d043c0a4980d00050380c0203059903400141c80e200e090341c3d184000c0807203400d1100000d11150308905460f000540040300c1c10f032040040c0700083c002007001c8404542c800c03a030142108211586070910758000b900007c00c2801413540d581180d4003c10414494002d01d560154001c1a06100e41d240041c200003903246c015019611450091041c2140403030030000941461500350300112002c84 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 158997805 1250 158996555 158996567
    0x11808180307080d03110c0604020613030f030816090b0a0e011b0303020c0708010c0504120f06090803100e090d11030d0203190c0216030809010309060f0b1c05060402060a 75
    0x2901d5052003260000520100045070803000b4400c9902c08100d500701128002419210740708111142e03130840e5000030014038040d00681603c3c078943e4030410301c4503125921200075041103134059010402d00001c000c0d00c3c100c00b08521310b8403c42480d041507401c0c5032429440b943e0040c802044d0070b00890140c0c050303842e481003901d140b10819800200c0d006000500b40030f0001d40c40f00604164034000c80c00c02007800c0d80140120702c0301511039a2410300d0645041145203000341511422101002c00c43c1440c0041040c601500b0707a01030003880400d130b50f4100a8140b00012610340d00c40c0d40079a480c0b00410402500c04600302d0446031035070901410060f60f80944a0071031280d502d186030f0b8280b011048c000203202030002440071104c016400c0104940310f40d0103070798600000c2540a40d081600d08103000040801c00a010000301c18107000c03405400316907558065400c100541c2c4491581c840b041d03d000d203801005000714101500443c60a20141d89510f52960001040070b40900e0700080d5602d1b04500c200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 158999055 1250 158997805 158997847
    0xb06010e0f03071404050f0903031303030b030a03170105030a0c05120a05100b01020c06031312120e060906061c0803040312021206010210051012260d0509011808 71
    0x805460f01e0079115810040758000d0303040e0740c1e4026450440040c09101107d03007000d009408a400a504640e18000a000341c400906403c40801d40c40c0c20400509850030003001080030300c00d0310b5a0295614072419503147e800140d1003688664002035103d00490394180c1100d05403241580d8486044103d00c052919042078160010854404c41808150042860b032004074041c02c01d0b070a4a848401150801113980020344803110003071011820318001806000002442c51141c1c1401d640007d42a500f0710102c0360007408041454110780304006100100740100c0d540302000307c40c1460074043c1c40b419126100e07503801005011850001c0490141800b13140d5004813580c203420155510040c4c45003e0000b840c00392030b180d000d84120182901418001d0291a101c1e41c81d40512142c43c1303181038115501c09108807000e68000300c240c00c1c0320b209485841014200d142e40f90400d070395625501082c00d0111a0010061070160349481030548629010160000f41d03150401e402035214440088120152182c003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 159000305 1250 158999055 158999059
    0x10c110d0c1205071a0f09210f0c10170a0f050103080702040c0309120c02060405090f011701090201050a0f031d010e0c04020301030f120c050f01050114010201090b06010e0f 76
    0xd0307000055051200005424440e10032825606600d541d0003035540c4040d50b8000c0c1ca0b04914050080701500303a80740015107074007440241002e480f681002d0180d81140d013003441c82c181c81e8000954081c55241c04004105180d002aa01c0807510010008003c008070581c0f1840c554590080c40443d241d1041034211000305c48a100041100c0d5941c0c0c5030022959100c0c5200b00c2c01783c1d041c0108940701e80d0191081c00303001600030302038049031030692100b241c4903075903603d00701c1e8000d4041c00042401d81ba110801840703440101e522074180d5050450031403c054100c00c101150740e04140641d00180d034042c003507034050342890400031120408000d0550103494951104c1c010200e840ca00d80325040e005420460441c00b061054074911004801844242d101c03d003c09031030034036036082e540c1c0000c04814500c1c1405c800c6250101c203039001503440b0360410042070282c440581d101d200600c05e00c803140900b4000003100340020480c0c03c2035a950407507111802490181880700c80030350000f00b07840e0314140210b56180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 159001555 1250 159000305 159000323
    0x2a030f0702160f1409040f06020307020f0109060b01230a0302090f04140403030c030902031506030f0303070903020108010e01030317040204020f21011403060411040605090c0c060a020306010c110d 86
    0x484020400f4480c1070b100368080ba08076002c030700000e4141450501d000f02d8000180c1d10b850100343d154400070790f1010b40800118414a815110b1071002849250009480380402261130181200014118940d03030241810400140034003600040c10401250160b01d101c0c14096124481080090103001da5081c4660f001402d020388005000304540029100b5446602e003045428022001102202c854040080d090741c442c0c00348103c0740724001082c0394031810003001c507400f00b6401104c050442e00140d9030786000c603a411900703004544c4c000203964094115650761808561664400a09091000001c4a46024030402040942d1903680446805070000041c40b80c1d50184030401d1600440c480004100c00c613254000414642034020401403031200c000c0080540b515076884000005038a540865409550380074001465203903040c3d0b03107202d03004070300c41141c5410f8075020560a04d00c0040080c10b00e9841081048566a0451084203500340c2003142e848603c029030b80810b16003652024042c1003480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 159002805 1250 159001555 159001559
    0x1c050601030b0d0f2112051503030d050406021e0703030608010b0a030b130206040f0906170303160306030f0f030e030a03021207020a0e09060105191229010602062a030f070216 77
    0x6001120a6206c440b180010442036a881c0c0e403038a074400c802902d040c0e0540007000807980d8a0032641065070003500450006103885140c1040c212689207507580c182c069600411900c0a041d0940b1030400148280c00080c4810303007071000011640483d81c0802070505001c0c43c0424107030b520080081d0030321640642696541c640b650759001904100c0e03c10380421906101010455481f0003080100c13082040b40190304580703a081c0720b0a480e07000004020308055682e080080460903000798201418081c64805000d088182001041765030a440780034001d03400000c1c4800080da0008113032030807034464a4410384422440c8002506041158402000d40ea1000103021090300f010441e94121102100d4402a0f01e0a900300c5000c148901d1250310b45130703207000c004040810310740c0b5800041501c0c3c508180c151001007a00f0701e0781542c801e8008a0060b84040c0811074031007060f0400c4910455501c480d10070503880070b020304200d03202c000d20b080700c02c01c5900f0200b414a402008800580d40b01141e000c003c4503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 159004055 1250 159002805 159002807
    0xd060f0c0c0c0311010c080a08060103051f27020426120a030203071b030e15040b0d020c0102040806010e07080c0903301c050601030b0d0f21 62
    0x44510020029480e140c1512069118001c0708240c8005901c48076100b20145940c5a44661044100e03000d41400300041c0e4490011f46400020140d20070191600c7e01c09003401e00004080750801408284682640181042041a0b9504480445016000b808003d0805105054440d00c040c50691900780c00880c02141412032844003002c041c880544032820036400c01ca4a5036211114103a040c80c8110800080d840c162003900291707405070340c1b4200f5a403101c42003043c81440c008a8541600018440310f091207042c40c110100c410f00c00400307103201e82440e040800041e8144078414011640da60300141805082c5800c0d01694003d104039425980c866954025005160404450140001e2815000202e020003140c00780d80112402030b005000050140401001e4100f042c40441c0d80d000100042aa10f02074650007002030003080c21401a044212074094403d484c8050270b281d043c5803c000117260300c1e84a85900401d01d9411044200c0047c5060a0420702c1ca8a1a042c454494101c034808030389003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 159005305 1250 159004055 159004061
    0x16060605040b04050606031f030f060c0305010f1a091306030312050c0412020f03011b03060f05030c0f06031e040b0702060709030302070b071704030c0518060f040e0102090d06 77
    0x1100c0c260303030a100c0e08400700c1c1040304031201201c4a07a4008130600105001d606001c1c5010782a8140c1802102c00c2511b80e140c071000039114031411140140c843c910b4840703480d418029103004003080c0c2003031903000e800c0c0380324241b80d44450341c0c2c0018400700102d00c9142507601c00804451a01a08000300300c0141c486c1030081c1000d200d500010000350a04011400c43c0e0411011101101e0416041142051095081080c4500e03101d00080e4503648400c04194424103509015244403c580c40011314180f52070b41c0e48961000304c1e072142c0d00c40e4209000000300307911841120355964070112403040d92035a4500c5008440c110701403030040281d8452040004100c031000c00e00d800b034000da0302164040d80c0c4614085404a80c1c40c0030040041c1c100034070400400c1500000b9141c440d100704c525600c03c008180b5070809980140c1c0c41a682008009400c211500304150b50205180f100c0c1c1c80c2c000586466400f04007822062400c0600030380c0e0711200704081c1882981a51400000100b83c1402c2401e50700303100c005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 159006555 1250 159005305 159005309
    0x111902060f0907050f01030e1b0f0d05100221070e010e03061e0c040e040507170607020d0e0d060f05090f01020403021509030f030a0504030606060c110904030203160606 74
    0x16108403004190300803050058107200c2c40c00345008008041c2010f00303221803110340c203c4541c103250312071a1810000750103001000240b98200b0105152014070030070003405075196040b80d8085c51640c654140822000304200c40803503284a1702582d61194619250900080302240c6070640b018041440306255102e401e8200242007640c80080003541c0d0b00c00c142c1c032018180e541c9150080200c401c034900a54031154242e12103905003003641001d0b910189482851000c50f41102c654015080a11441c61a002044014015038000302038a140544010303554036600e002203c00e104078251800440d83d0f4007402c6e1034080394000c0d0244200071200f540341e80a01030a907503e4215018401002d00c1804051082d94216034006040c00781c01c00c20550320000340e5202c0042103030180100c6001c80101c400802c0200024242a900c0560f00c51450600604445c40c0303030001401c0103256181c0d94046201e003480035041e54000c403140c18017902d4501d01070740785100e03040502e00f80c50041c0010005001041d400303402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 159007805 1250 159006555 159006557
    0xd021c0c050a03111003020a0c24090b09060726090106090c020c0102010b0301180f080708070305070312060e01270c0507110a0e041e0501090c061d030706121119 71
    0x21440310250103400740d000305024040090000300c2c41d4404502d1a076907102d4554146240b5039205903407925400709495150000791340c0c030458cd200f44045803500300607440d4807034805e1801d81c201100344007180300b040f441c41c40704d00300b43d05412011800b4000c0039031141c4020080d0740c40070801038120100c0030f03456070b00c0f1216541c05546040780c4408941010300a6141d91b405010020410303494999030308640b862880b5043d075502c601800810001210a0018041d25000e5114151240d402d403070010503a44080324040140d9040c8001001171138401d0210a05554401e10503003145d0808019803040c9049214680007458108192103440e141c00100800340d00780100c107041250840340040c003000307130354902c107003a00340f1044000100440c030200b4108010107250f03e0101e1036282d03503885490940310a41816680800c1d910820094140c0111103c11100c001880d101032003041c00c1c00194440702c51f84501824001818500e40f10115540d0040e002e514029400342c2e200c04080d4100560b1902d000d4441c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 159009055 1250 159007805 159007819
    0xb100905030625030207170703020601170a02090109020906090d0b0a11041815120602040509070f08070503130218090105130507030201120212130b060d021c0c050a0311 74
    0x30344606103040790f0340140f003608500e4140421100d04100c0095115942c1581c1e130b2000200480700003c049001410018001c0d801051035505114200300f001c05200039654a951118121800503150350b04880d0450b1604500180c8811100f00450943e11a20034981d0748000308002d0340e010040c0301c03100d403400b841e2546000c000208122011046030722490180800705d0241408881210000c0d4100d241440c014913090320905d51f642d81440c800800c088005c6544030f0300410f082c07080b8200340180591040c00c51510001c102645080030b000107201800716010400000700042d85402d803202c0400d812a40a800a03131040a403c1140c42024020f40d01d004030380d4200404918220700035020b180c4d00903008405004050714580c01964100741040703440c0c0d0444c0e000d001810900007000c03005032240d41002c2c002c10300541c0303d00d01250040c500620280c860b5108018000143c0c554150308030305c4115040c00c1c0d002c2400366041c04428400c0c103910041d40429295008002c00c95102190140c98100351924 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 159010305 1250 159009055 159009061
    0xf060603060227032b0201060e01080303011e0e0f181b0901050d05100f0b1e01020105070203040b040306020f07050327030d050d0506011101020d060302031b0307060c060b1009050306 80
    0x1649070005290f17140d104120b00c100b064940d50102d00700e02d0641480d80000a0002d40d21515a54217480981c030442031a0000300040120300b08400d030b015a225000907511100700d06000c0a2988600090108454861810300142e062280c0c100200ca440d605031040381c407418410a140300260108902445c0a503004000018103414030020b200b0100790302c00094481101c46548500040041d80d0340d00d03e181c0d448400c110f04584031064142c900c4800c040c0b03015190005480003a0a40f803001d4000d80843d402000304002c0b50b400c0c20161000d607a0f01010151340c1d4140885540c0e81406003220240050000180d403c4030040c1d061400c0c2220042c01e50041009003000040644800b03450948001142003003104860200d410340c0055801001410048001c0342c6040405003280c210341981c202d041d0f40d0720b01c14420340c40c04000069155541610b20000c206c1207031b01203034a4010034400c4206100c020312001c4100103d40c2c0003d210000c1c098a80130503042c240c1c0c0000c2c440301c4644220b0307000b1b000d10008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 159011555 1250 159010305 159010309
    0x2130f120206030f090c0409210801050f060f0d0c050c0708030309060403121e020a090801050c0403290a0507090608040317090304030218100506040806040f060603060227 75
    0x4003800e01a00200b2403415607407003028402c0b9400009208005038003e00b0072196040d9100c1c85055000e41c0034800d040303071740203c005800c131006625103000014070008800401030340da201404401240e006441c55521000741405c1c64901e0300034100241070345801d19140d51680359004006c0e050b101d502d501202c607043d82d946111600c80c44140c0307038041c06401000009000c20702681d0528070307490303d00d80000342000005004554650b05c02c2c4a00900319000103038038001c180d1100b400300141c004800200800d0800030348442d082c0c4100d02c8000c000070032a00c5162110324240d071702d01ca040d12001885014614050100400528044482c1c3d070100360400b9010074001d20844425100d181d064845546500500d0245241e800001306064601c0c4420840400142c8500c42917115482a20408c100141480794004140034100e81060307000304828441004103040008100f0340090704030718107040d00206030600c90040c09030307070b0006084c6d0f500000311560b202c01100318005182d80310743e480c1c0c201d1000c0101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 159012805 1250 159011555 159011579
    0x409060e09010c1112030c190206060a0501090612050a0209130603030207090c050d050612010905010f11030405071509050a0303020a060c110c061809010e16020102040e180a0602130f 80
    0x1d000d00803035014500e902d184003117040045801603010104ea80c20300021001c0004400f914a0514005811450030b10416041001214004c3d003004d003010712006080c000300800004c11022004105900c41c000300b100c44a8950445020102c003902204010582c0720740c200103800c962204900511828200141c4a0018807a100d040c141540d5420325084000074021301404000d040300c1e0788112104040c5c80503420074030030850041c2c812400488c003034a415000c00e0840c4c3c04e80c1c2e0105c0419108000b0440000d101250070002e84460940640784004840011a04000903822003600035941250110074590000303143c0c5940c600c42c03c024054451942c00454510b150744490340601c3e4081d040308a03091401d0300c0640700440003501202c003203049100c00182200e00031b80c40300900010401c240000350707220b501000202e182b213000035841c241c136060070380048110040403552000d44454008501c81c50501806804035088101036484402640c44188190920300c01c010001d0720303520b40010b0071842c0c25 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 159014055 1250 159012805 159012827
    0x602030406080606090111010510030b0f010311130b0a0e010905070311190203070f0f0b1503030d0504020d06091b08010e0307111c11010f0509090105060c030409060e09010c 76
    0x641d840c02142c0f548000d10413181c00641501c0d050244241e188144011b0900c83e0f07a20400d0b008802e010568030b503040540c1b80c00c00180c80207100c5130980d001880890051240d802100c18261402d501c40d003c91602600200b040700f00742548450b000400048030008851058161a43c041040080c0e0b16940415011198103240c500f000003410700950611030803d0320104082a4140103480c90071009944500030a0307003107070703088401d02581a01c420a20040781c0880b075000e818046100d601c403140d2030001c4e80c1c23401500c003145181900c4500150854a0304140c0c04c10703031903010340305000c0c0140c2e5261903a1184251000f003181d030f0f0704003000003403060414010b1000a5001d040035604d42010364903110709240d02d01c122140c100105286074001d074001d00142400d600d02a0306c5800c203901241c000182245c5811080c0f42c01c0110502480b40d5942e00e091500f4111002102c0ca990345046c00e074605407c501a076070085c00c1c414900000003400c5da5100344400e2144103400000c00501c3d161034002e5079061202 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 159015305 1250 159014055 159014057
    0xa0b0a150501030507030608030c01091406280204030b070c052503121b05030307030f0204030b1306180b06120a1e03030b090702010213080c10030f060302100f08010602030406 77
    0xe00200001e50007544465000341503443c000c504c19849a48182c41d541c4102c3d44190940c0d5103505150600c02c400c0400801c400060002c0c0003541803041c0e40c0080003600080d00098142c1e401c0351118a45015411a402507034040d40c0212686407100740600321702260601034410b400340b444060a01000201403c40303110b0702c6900340d8406811a01c3c0d00503441c0e00022a00240068a001d416000c940c003155550041d1250f4002c580da4507242c1001015241c503881041c0b03000d03006000a10008060500c01540070710324048000e0310300194281140a45161b220303201d402e801185d001014444240b000c1845a03100791009510082c034080c40c1d50351882401e00150502d09103490310358080c03004210903d5410700070b14004c03500c2c0b400032000600450090b01c002d0f01503903000405900308042404031600805804010b04582c0700385101090b240d1014000c0b4008240d92041c00012040641c0c3c0044081c0d82c000c1d1a040c87c64590b4080035003022120000040442c40000000640e6840001110159061 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 159016555 1250 159015305 159015341
    0x303060d0308060f09011205013210170703030e1c140c030303010902090f040b060d020a030207060e030c060a02041508090a05010f020301061202130b07020303040905090a0b0a 77
    0x180703440c11509010060106907200e80c0d0055071140c80d40e00e410481e8060010188484800b4002e071810a085900c0c0c00402e040d00b2076451054841510400715610040801c0c0b400007103d980e4100302d0008654550300185c08459030768140701c40300c01c800180501503a00c039440703243c52520780c5004c0011200d8842d40c0b20518605a40b150300000d2655082805c00300740080803940d0801041e0700083c00c1d904260082109142c5c0803a13121164a41a190114600030a48041101c40000c5000c140141314509041c402e0a400040300c040040c401d038115030403981c02120400602e220419180c3d00c0303602200c100c1442d8411300000c2580c0c0c040905c00c8604440e10b101030b03a4402d89880205843c400c500a0401f442c074015800c130071010650030b0203040d5440304503110041e41c0398104000600085100d16040402c1031041c0401c80180b0740b1000420240ea88003180303551928142d1000914611940c0c00200c0310354100410700c2440c810000f05400d9180c461141d19081b940c0f000d5290342112003c036106c50082003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 159017805 1250 159016555 159016579
    0x13141206101a0c1b0906010c1a15030a0501060e0711060a11190f090b0c060109090224030f1302091f081e011505060d0c0e0a0314010c02030306 63
    0x48801c0480e82101c0d1440c1d1407a04091982c0c09480c14600da0542070b40000030319021407030701d41c640044815030288003420708d48520601e41d25a071424158010344003405028860200344010031100542411080084c100c034071010740c0d40b41c4240030303118034490082c45046c40c1c17010540c09806591603400e03101c4240700a0446070f4031254514060300c10701c4004084850200031081c04a0601000004000341c562079607030800744401001400820380c0e92014a5030f00b000d01c520005401e000c2551030455005000124a00d00f050000038405071142d50740205100b01d0040400d420912640650b105020520036001c031a50b48002d004e02a00c10b620000707600540c0c100020300484605505016410a1503400750845912481e80341c0c6017244204000c1e064040c0c0b072000c9039158200740200c0c01002c41d003030090000180741c540032030a28010302c00c7c031001c0c1a072140441080c41d44109444038040b040285400c2078507a80342072000640c1c1d0004c62020b038030b5080104210f01a8000402c03240030700d4004c0c01c081030000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 159019055 1250 159017805 159017819
    0x6040504031b0c0b0408010212181023010806010612110304030f0c05100b03100902030a020d0f0804140414060306070e0d0b0915010f06020303061003021314120610 72
    0x101400c030b0200c8440000090114403880c0701c40241000c0c29890000507560594488400400b400041001c00d070600c0c0f60030013a140f0340002c0f03080070800c10504d401140da01240d01c01c0180d1540703180701480103d10a50000038091400003900c9048841d50740b0f602510f8010700808000362160301121010300030f020000308001030b01c41c101c1c07620b4054031880c1060304401d00303030781e002d04002400d50382400c81501c0d52132a5a951500381300240742c9000101c1c0400400c00d10341e000c00d0b1240c0c4094800307407140607100e0604c1c0a010280d42e0aa200e00d07071241259603039a80302d440c0401c41a00704030030517002d030b490a1580c0c101c030080c0c080ca1501402004000300419510340c4800c580001002203525003101402000e0000601c0c0205854050a1120060184030b91080704e0030181c1d0805130721003c210722080b0300070821a600401141d4100005032945e801c902c60301c0c07106401034131070303c4007000c0b54032916140042c0ca140031021403070f094441240c0b141d01110b01c40c561240d07110801e441c8450b020344002001c100e19 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 159020305 1250 159019055 159019097
    0x10f080c0307111f05010f05040504050a0f02060c0102070f030906080907090b0406050303040803250b0114010c02120606010809070e060d030915030203041704030305030f07180305070305060604050403 88
    0x200f511a0484000c81c2e5040d401003120f030f90104034401265190001404407216200f081d201a00c42607604024230f02d0192180c0d540c0c0c5c007003490b001c3d10801d150741c0700a0545d110170301183c10b01c1c000300000355502d200c145017600c6d404210306010b03030002e8224400401c03000d02c41c01115000d0501407000b45019428005100000c0100700301107a170041c1d41e58800541034406001410052403100051500e68004001e440c1039030418502c40311350210060740300c000144030001003906407070b04c0900811050b4400c50042c1c452041c95600030b5401291f810030000301000008142d03100304000c0c0d86800b840d454421440d036440220340101900c2100110016076107061000501034000d002c1d18181104540c1c50005101619528216000080c5c0000800040c000d50036a0b02401000d1410000d280034070b136480080c00707800060b14000d04580510b02040b20148503440c0f82010f40790405d5180c1c461030b44c038038102e81d460307025210840d0a030059000040b1640361a101c0c040c4595056115803e00c0b01e1070b56484490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 159021555 1250 159020305 159020327
    0x12a0210050a0519051608030115020c01090608070309140c040e06010602120d0f0203090304060905100f0309020a0f231005031801060b070804091a22062102010f080c0307 75
    0x300710301442800c40e1010f03102c060015147c0030b50f0f02599a54101410311909500c00503641c03041d0b5000b114460350a03640300c0440000c1b02c41914080140c0e4483d25821400b40c40c070300b60007505000d904221901d601002084846c0c0d10704048030100000818007060a480306000d1003a5800352300b00b04a8204004008002003000c40e5450000060800c1d1010f0700c01d0403030700281c89400041d400805d0074015035402148000141c1070880d514100140da050004200d800d450481900f00340c1c47c1d0a40c2411500d45003c0b01024010307044401c41c90f40d480c0c0c0e03c600752944c20051030400254041068800c0c6007440d190360564404130350b90782850369540c11348441d41c1c424030320071042641d0740c0c41e54005546142c1101400c94584116001a500c0e481c2814800c03d444001c0060f40e00b03264043e040403001d40e6210101d00c04a008282000115481000d1500040600e80e11a00e0786c2000e0400811443e8602109411114401d0721580e803c1d05010f102102c13040342c2150507a114a200f007001c604010301404030940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 159022805 1250 159021555 159021557
    0x31504050c1c020d030305010e0906010803040513090f110109090b03030703050c0f06160f030506132007080c280b061f08090609010e1b012a0210050a0519 68
    0x2901401c07a80481d45003080d18070181c002031f41e19401442414044c48826800c202d454004081550512017203e48a100380c0c0700c1c0070300c41d0004000e803224084064101d1030001e50411482c0300ca4141604100d032100b41040c2045001a54030800860410064422120074041c090700850500d4801d9805450035805013000c07412a03c2002c41120070b00c40100407240c40b807802e1382801911610540c1c405010754549200c00c070185828201080404d854808000f41004114a008920030010480008800c0842d000c0c05410000004501041c407091030700825111034500202c8511006807202e0101031414410036060000318100d1040202358032401e500d40102c0300412001204840140e0101c5100310b034002030011804a104029840350f06100443c4c0c0702410200a10103800060200c07922143e10154a0b803801c0480c03402d410b50390344218071012005c01c003003048005002c0416000781075001a4201207115041440000108a02c100f0954103122200d4650500742005c5503d009043c64110302208 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 159024055 1250 159022805 159022849
    0x10908040b07170f07110103140f06011e020f15090a0b04020303040e150102010605150d0f0608010905030d05010506070b0c07050f01020d231605030c0c010903030b031504050c 77
    0xb03291090712900130036040c040e104005030382d02141d25190075040407104840741071501d8034500c5154001e405050b04c0e44102c0c07500c00c0e051581e490a0040e034440f03100f80b240c114a03024010040e00495000950b00600d44901030481e031002010400080c0c096800302e07000c5c9429004114904006810f54100c142c04c80c1c4028242c0c4d013450f8131002e94040001048a07400c5c01e14041c0381103200c080d43c0a118900281c0420754103503040794411151603001d84a6030f030740140001d50700d0b042d43c1030000c3e0319480100030303100c1c04000f400540001d040007a41c0750803510700010405e10740000098036180030340441e83c09a42c090b1841151342d6502003403082c0da410506040c0c54a0040380066580030600380300405c45070700c2000d0005608807100003808048c140d01c203d48601c4500c000e041c400c03045030003100f040d00a044d07403030416582d560b1042c41c0e03001c038003580765410020360812481100b0141c040c3c200214451040c1e04540c81c2e10340505980b402da100036a03000d011608400041591824a100506c10545410f5486 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 159025305 1250 159024055 159024083
    0x314181515015414061b060c07030f0f02100c020102160b0a0b010e1309050a0507030c091a130c140f0307030509060705030f070905030a030818010908040b07 69
    0x45428200760001910180302003140c860341c40d08203141d000d0308038048040c3c002c400504241181c1d00341110200e41c50b10840700400c11402c1d01d404000d0300c01704200d2140036034040342801d2548120540100c4401c4004c9a001c45105540d217225681c181034012843d402015100140f60071540284201c04680c0f0841d502004514141c15003d4959103655208006c03820003481c0c0305804004072030218515a04214044203018030360b64800d03122009035102c14000040c081c0c11468060f18108240c0700041c480d0081250010600012800799003c841e1100010f20400160041038031003108042c3c0a664000700542800d850100705501c41c1810a0441c101503c1000e01d03c1d02400c856000031284544c075140c00810032035820b50601961360400a00001400541044c060140c030074080108200b0007548080000b6046d18071400c0408000d141c082d054441c032a0460500500700501100d1000d5050580d01c0d60701700e40d04051007441c0c0b0703294200c007000d0b00307090030100c1c3c81c41294032541003a9194004040c1c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 159026555 1250 159025305 159025367
    0x615070b01180227010912080d0b031c050d0507030903020604060504060f0207080d060f031703060109210c0509070c03120912080405011401150c03031418151501 71
    0x9007121142d0904d111200307070b0312103400060000b0010782080d4035000402e000040050606801e031030741250520b45c08210350301c14801180c0740c40b00700400c0303035054450846a00e24642d0404003c1403c020780b02414043d0307030382e41c40d4180d00b43c40c4554001001a84510001804944e59a0017079401c50300c107040c04201850b05000d0034059801c0b008081d100c240000449904083d4142306880081c54600c001c060458595114040e2242d6600c004c1c0c070f0b1000e800070010300140e1040d442e20016007403014071004060340000c110303c00c40a55030001c965500e47c001c13010445103072070700b030142c4545400d645028451442ea034003140c540c1e00c25003a80a400c1c1e258900000015920340b200c2c3c900709400d580c4c100c980d2034542407150958000f1880240d01d1030003480140030f030030400d40c00b140e0525101d0501c240c2c0c541140c40c08600400d4002c0d0700e52210203551052201122590141c1100485030808135580304007503d5a2020400c0251401d80000840c2d5011864650041608581001c00000300c00c19840503c80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 159027805 1250 159026555 159026587
    0x2706070b04030e041d01140603060c0d020403060203040f0b1023010c02090406140f0402100e03030d0f02090307050102120403111906030b090c0a0e1c0203070803030615070b011802 79
    0x40480201851094075002c5d080900c41c0a036444454080d1401318242040031a45600c0058800e410400d000500074201c050039404681c0215800201103590780b801e801d000c0604900c0b0041203030704041d40004102101d000c010b4000c151041841c100710fa190b0b492000e40c02913024154034605006040c0918005a580c03000c4a5200c1ea01030700c808118007000d4488212508001804103c0700050340044c0005600c038642300802d42000c50a1040740c80b00740d08002480d40c040d9950441c1d0300390405001c0302003043c0e250042c007160348069003105c40080e02c48005a0b01e541318035410b07801c0514140402c201140a11080002070f42c40602a080040c440804180b44101c2e150010b40120392610788003c0d0f1401d00450f540c2d401100002600c0c05c1c4000380d54001d107030f0030913a1600c1b40305040d13039401c0071805012000301c0405658024115051240d407600410b403650412100d1602c900d0017082e001800020030000c0303980855100c110016660b00f804039115156420b083d00c80c1017141e0078402240c4841c6401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 159029055 1250 159027805 159027821
    0x91a060c01240b030103020112060b16020f01031413020406150206060f0f09160909140a0f05010b03160203070f1b0801060602030a1d04060b2706070b04030e04 70
    0x340042001e69503250028000b6a8000800d00481d42030340c000c00c06858940103607815658240380545c4d01610642c45000503004540100d000c020f0009844041007004400c02c981c0c0510039a88500d00c80310190055046440c0030305c20b20001003200d800078507407032600c2c40f5138000c051000300b0015596071102c80c0700700500c0e14025844d000d64031030400c2c0152440d00c00703500c1161000440c2e600d01e11040e00400f00b1300042010b080100f990048910300f0006030700907048600a480010030800580c0002d002d62407000b2010b80e050241245490001702c03003000b2500032541641c3c0078459441c40c40d2551505a200e0007408a20322085000c14030026002620314034400c41524046c440350751807000115000c0d44052a641d00c80b1445a140007000c200300382d004030549912560a0500300681c00441c07544440c0c0c0008181050750003454028040303540e041841c0a0200c08581182300043c100c1e03100050040c06103641d2929600c00d01c2480b441c00001c1007461f880b07038440d21a18201d00201410000b00d81660405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 159030305 1250 159029055 159029077
    0x31502071a04050601090c0c02010c0f02060f0414100203070314090405040609060e06070f030b130606020f100b0303040302130e0d0302180901050a0b0a021c030506041b0207091a06 79
    0x22091005003d01005030368054042113600704061048000050032400070400d0003410b0118030700c03000c402e00105c000204089500900040e030744108140e01c262180e071083c01440244000d0410902150921601444110740c1e02d4004500d403028607201600e01c9121740c28211680c4000300011403c580301c1740a0f86028a00c074140110308000a4600030701650000302c4604402e80c0301c0e800f00160503a200710b4a035200c0c241800e0018000da2104003203041c442d01d01c0a0308000e00d0901c81e00003802c982c00101e5103c030410110588640556010410060b0380c122111507601d0381c0148014805403030507210001d25801072101c00100c110b03000207030a0900c0070540940020035404145808841182c0349190001e09080721031842943c100800035003280d40c0c0f8020310441110115207800194000c0102000d80c0308001d00d46d4103032003200030009005e84030440303225000360305180c1d136411030982541d034400c0c50541c02e0300540000c41c20000e0b07810081c22040c41c418080324110241c0413290b01c03490010329003201c032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 159031555 1250 159030305 159030353
    0x9052703040f0914130b16051b030a0906090f030314040302041a030d090803070b0405160314100225020411040315050105060a020a03050307170c0901020d0504050a03150207 76
    0x209100696a41400a1840301c2905c003441c0f0000000e00c02d800820390010702003250b0b846a24a54004450a0081d00c140a8204a8002205541c42c0d0000050103040c80303180da0700a02603441d1002121250024404c10740810000001407000a0040b0804103030b0550b00754005050560300c1d00000d0a41d4003c00301a0301804000c02442080d00f020702c07018038403e94504090780c500313291040032580c1c0d2084050180503c3c0d12076021804205090241440480140d035009050588a0501007a44150041420f0107441180c01c00100000389000740c0f04400080000b0140ea06000380c540716074114201c00480c0d01650315040d40141c40c00c2071014101440c0680722021120710200d44550850340180c00c1280b1821061201c4400c1d240c4c0000c2020840354145052500c2e91651142035411440d0007803d0303108100c1d2001001601d8101c1006445840f01c260300702d0f646801c03a40c1c0f06a4052281d80112500040031a80500108003840c902c0c038452050707210700614008442d240c2c940100d600d900511b9130180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 159032805 1250 159031555 159031571
    0x3120406110c1516080706060e0f0a090f02012111090a0801020c120a05040509010303050715060303020705010f050c1c14091003050c1b031309052703040f09 69
    0x40400a5401c02d40303058544410010306584401e14900401d070101112000e2801807000700500c0c0b400b0349015a510440a104039a00c0341c03600d40850404441c81220b0310101030002d541ca118901034203005a0300003d04440b4021144c0044038005e40040c214140303100c0071007019a2515980c401e1078060b128004c00c080d01c0e00d03940c3c8204000440140d1102815a0061142940e0b125000c2508034542c034a80e0505551440c00400507903090007a07902c1540d00200c1c2000020901d0741100040951501c0348a504002180c2d0316080c5003250700500000d030047e4000c050a0042d0350245042400e01411030400506100102070010700e0f00c1d40a1030041503522002904c4202144c0142903403d001251404a83c00d11604e03d02103011144002c185504040d00d40004c50341d0708079518103c401700000f29511100308866079600c9a600c0d4089201c410b41400c444000080d105100c2c801c941c003c480000388042088030a00345084040c040290809580c041040b00080703a038034801001c0014030b580000450242 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 159034055 1250 159032805 159032837
    0x7030c020d02070e07050313080a08040c09021608090d080705010c020c01020d020c040b06040512011a0a060207030b0402030124030309060e0105191b0303020301030c060311030406050603120406 85
    0xa002054820540d4040f000c140003003100b948069a2040c1603103403039078582c0d07142d0709100c952142d40304000d081c1e6180084e03000d400c0c0da03101c030344244150300441c1156000d65603210712800f244140c80b11800301c4032031010548002030700c1c480280900140203007411806171280d2269003269008a41c12102c1d40c0d90ba00d011500b082e0140141c2a410009002402074250031020103515044186d40311445540d031100d09404542d20358003614084d10001d800280442803030046a4001d02d4034034034a9a8614041d640000e20b40744c40995141030b250301d03a004d0f10955145580e041403280000e4000c0341d046d500c88503c0402064448103030600b124101c20380b658024a5070401820001c0160011420401c0103005520300707907084811961045c40481804070041e01e035401c1180c003c1620f400515450030680c00d04005c1c580d0680155049e0781c090240300002c1555407800383c0c200c84504900032600c206c2070000070003169141d0700c042d60000c40941a03401c186090135520115510940150010900400383d80043c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 159035305 1250 159034055 159034063
    0x3051903030b1e100201090c060323070f14040b040905130204050709060e0301090c0509060117010603021e0903150903070203030403031d040b03121c050106030c020f010b0d11030102090907030c02 86
    0x4c1440d00080044030181d484011404019004180900d609d40e03282484c0d0104180303503050005142e5803034020301e05016100600d414103031016400029800c1030b030441d004282c070b07044908840c585a80c55103401c1c9004107450152600801000d5000710b0103481d4800740c0c41d07c2c00b402c0e00c200040c0e55001219801c12202030314072010320958501a0780f6119001f03000440305410308080d20304c22618060242c1c0c807030340100c0b40c108049172a00151160840002121074254011740708000300d0740040981c07002420b00600c164090f08540951640c00382029542e01a00c2402241e00302d2207401c07d80f4a08080e54011031328641c407660080340040c0007114203400741110503a12041c0030104076400c1c040ca00d6030300300280da1444029074003e80281700041002a105400840b0404602241c1c0d080c400b540e922007000c1c1c0106902004030015002e480500b0140c40810710402801501c014106040b03029141c45620801d1358401c590798156500b008408007540c0c2d4100042d114440596000c038601e465043c0003414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 159036555 1250 159035305 159035329
    0x406030510140a0b03090a06151a0f030a0209010c06150608130f080903010f09082107022802031906060f1d040c0f030b09060c0403051903030b1e 64
    0x1400322002d140d0540e0b41e43d4905408200e451014082c0c2d1252100750499080000e50324000306918948080701191041c664868400c582038a4003600f071084408003100c5185c42070b20500001700e0760810008402c680281c1c043c4c602c200041c03504034000c8046e039603032a040329035640c6034140c0010040000c02c403190380600a140c0c051001054200305518a990315000c43c01c038200000c1c00c1e81e00210302d500706a03c0035800204509600002800007006605000d80c1a501004c2c40c04606940014000f4522f11072513022406051140e0007000a41c00f01c0c0b40340301d080b11420845441d0390607041c1c02c0c07601598040040440d00040215041180910351038440100c500340c0c0d000700c00030207140340c00308624201070201685400d01c40903480d91039603507441e140d204051550002c0705a0006d5510210510942000c1140318042c90805c07144140c50380c0074144001c1c0074071310009116a02c010281c00d840301c1c2d036400c00c0d50124400e0402081025000001420040d940d403401401c0800f100c04103200392414901d0841 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 159037805 1250 159036555 159036569
    0x1050f01050c0309040f0216032006040506070f0210020a0201020a020c0f06090d060f0e160801050f070c0507050405240402070209010e09030f0f040905090c0a1e08030406030510 78
    0x21500b0003a04100e51603000700b40740a0700c43d6507070f4245480070041c3c940468101030650503001d44507507060314024101e146000200c194804c14007214032810f4034006140303801190890300030022582c68072000c03900c2c0011101c11070300310300428110485043d424006409954016000543c4841998070028a84074000700890320501c01c050080649480d050b084036861f090035036101503248868140030010f4150740444151803031604c000103072603000c04610407142034051044902155603c420650a07180c0c141c0d80f544504c1e00d50760100d101c0b01e00405807000c1c07191040041d106455601c10004c0d08070342c2d0031100b6140d01c0c0c500140c041d80c0c00b01000c1c0ca000c1042c2c400c840071420402150040340002c1c0050181100a05840b40400e0010b1010800d441072540d1102e440e60741d580118043e10b000b60003500c130b0300d0003d46c181004903880e1600407422403410b58015010351181d9282982c0d441045292111fa009040d0710070002144450050000380080e00c9075840200d900d0400007045251b05102c0d0344810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 159039055 1250 159037805 159037807
    0x23060a0c11040c0806040f09080301080106030209090609060109090f0b010f0617091c02030c030f0702121912030908040b0c0c0a0602030f030a27050d02010c020309270f01050f0105 79
    0x82090313042228079800c010309a07000104a5400c3e030030b00000301215540501240c10200c000103409105400c900141c030320944003600d050301c5280301c803540c3e24415500715410340c00c008014044510140d20900314503000b402da500d9450041d803600f2002210a03040040000c140e2401444515000b481010803a2560044440035242c90700d601c40e00d038030b0f5007441d80300741c55a40d80013050705034402c00039034841000200941e80d0700c02290490658617480050304901070060714a82c40115803011400350008042c00c030060f405000c09540d00ea50840d00c420703001c3c045c19039811382140404c8071a00544003410b4035540b000d0355060604c490900e8a24001034452052034544414021a640070003643c2a0014142d540c40d1070703440f40060100640b1032a101418a1940c0c1c62140321150386024100800c80c0c050001d59481e1811018200e003a00c0180007481d0240c0d008000ba00c0c10360070800074050a80344001034003491400056440e600e00d40c41504d80501d2800804014032052070213413522040c11209003006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 159040305 1250 159039055 159039071
    0xc020102060414070b0c030408071710090203031303060218100c08071505070f03140601140306030708060408030f070c03090b03060a1802070303060504051023060a0c1104 75
    0x1d65600000b000204511030800d400351049204002c95800b0b0700c4c0703150102e92541040d4070f1403a60780e00640310342a100d2165200010390505584119085210b00c00d024200c1e0440540d14440503100b400000c0340c15110400c410f0b42d0710018064408040c0d48a0074000d07030346603d02d0b000102100060810b09102d040816441d0865076004020072202590115400351561403a05080340400c002d81c0d0002d0405040a04208020f644000074005d04051510f04001d121408001e10b0b20040040319807a020500400f0b00740c80800e0002d0185a11420040c1103031100350304d91400740e00740001906d00b1180544080144041c0c00c800200c1c1e95840205464040c042d20030586004214602c4c600c80c40c030300a0400804540c43c1c1d201c0c43c1c0340101414004c4640f01c036540c4084544002544426000e50000349031450200d280c1c80e250041c036010384451090035910700e0506101d00401401806000b000c800342c0d8a0242c00c079202c01000c0e1020350000c0e11912940c0300c0e5070418004c01984006024881e0b407030041c0b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 159041555 1250 159040305 159040307
    0x1213050f0c040b06031614090307030317070206090304050120030a26160302071a180114130b0903070c03080301180509060a1e1505100c0c0501080406140403030905010c0c0201 77
    0x1c1c0070304011440c03800c05402c60241540803024400c2000c08d07901402000000300c103040c0c01036483c4240000c01800300d182c0780d9445a00301e843e00e40c16150f10501d6042000100019032003001c12207d8001202a4035809a10012106156034800307640000441e0000c20050640420104c800d00d040a4909844405240c41a0070444072481000d545007890f5011030017501b03004650182c140380070804d440d68003403401c26000d50022240c2000c180b241e1982052041c000b003e082406140c082c164042403040c0640156841100c138078001002080644800d103d51004114058880340c000d5001e143c2042c0d4a5040808130080c0c1518519069800c5d0304180911410082c0080d200364031151505000640b00300034813403030171590244000d0040d1241440000c1049110150b403d40844008070b5440011580114040d111510480005088144009070400c41380d4010400580d0040c0b082600160084c0818050b030344002003030f50160002a0340d0040b0004202c400d1282203410704007270400b407000f1202d540c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 159042805 1250 159041555 159041581
    0x9030301061b021c0605090a0206070803070302090904080429090d111917070e0411030111070f0312050c0405010c0f1202160504020a051213050f0c040b0603 69
    0x85420300704602d08044414070341010b04100952580103025142c0c8003024183c40e01010801c00094420503d007101103609143d00240c00e0700f0043d4094010341c14140192110fa003590001001203080c981c08000c0c000351566a041c1c15071207a07101c0c0030070a480d0760506c09501a0b000315800c42c400620303002640c001035140c0000c181d80a5001c11284c80715014640d1a04118650b06c1ca0359084e0400700c50007120042400c0300314950191401c043d19030780388904107407000d40d880d481c0c0e200d01c101d051000300120b00480c2c000014520864001b07000403c0030075400d40c00b0f420740d5010707201c1560310283c5403034440c0415910010083d00304446000034407590801a281d141140b18500c03c4074184140c1040b1401040355018140300383d00d0300b0000c80a47d0009100c0040d4554103001001e0080405404010a4620b840d10075240c140f0f403246c0e21a81441141802285a01c0d005840381107c84405000413000580c100314071030300c44042d0b4003e0704030885040180010783d0801c418842c40f58000744100403d4158200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 159044055 1250 159042805 159042809
    0x607170c030117010f020a090311030a03050322052b08090d030903020a02090405030418150e04020d0b01140102100614061308030a031406030f0a020f06040f080a05070e09030301 78
    0x43d59905265103101103940100340300203552070920b00126481420300d4106c003615048900800240d80b02c40c82060800d81c980c0a04100180481c606101040118850380c00c10601e02c3e1803403201c0b0440c051292145443c1080c01c410400104206441c0070516850b0180b103503002c8a0103040c03842407424010009629071303003244a00c400f01070792030340c00b001031500c2080384001540c1c000c0c18013030850a060038240d031a40e0050240c0b00010503180460f503c00110381c0300e042e41c0c5105032080310341d480e802e04882d00c0003a134002c7e0069038030104125131003010850380c1760110300900740c1c034446944040141001a04011628814a942526100d02040107a00d10488400b40b4402180d20755910403250421020011072600000c503107110104107140da098056118645900b80c44421a2195560f4020140e941903018000031054100001c1d0b00010309061a94400941e4000e05131802d0a85600c882405140d9581c0003083d141c1c007000c802c005020f01840000301030400c046441d411842c25150042d0307288418 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 159045305 1250 159044055 159044069
    0x13061d0a0615240f020d09121410050402090115140a18120605060603040203100c030e0f01060e010e0f010e1005040c0e01080109020c0a03030908070506090607170c0301 74
    0x1404155601004020702e0809801c40248030b044408080c0380b0680080380d82001c0b040402d501c200a06492400040d900464204a42c0c50104103402c0240c10340058496003800c80d400100b03045c3d004880b035401d0114041140039044001410314242c01041844181a4400c00400c6e0346a041083c8155010303800c009001003c512655840968800071201d40e80d4039002100b050300c031130390f010172912150400c504505004803000e12180d1262400c000e1240300603500258180e100703151413010156690480300100b581e600b4001480128409024101940f444062407543d46d074401c1444138680c208034a0b0b026000d41c8100050030303e0f126001c14901c80040c020b050f003c81501c0c4c00140d1840054000101500c000341062154080700b000240c044104020200d0116a040d0000b00d081c5c45035200b0351703000d00d607800002e06602103152020340c0200f0016200356031084003003080301c011410400959004883e020014001454510b03001040d5070482c40305564403c4c106001d001e0346007002020f89040d04c2c11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 159046555 1250 159045305 159045311
    0x916050f03310507051f1d06041502060a0506100c080f0d051801091e06020c030c07171c120e010f05060f0102030301030206040902030c0403050613061d0a06 69
    0x55a00e9140e0126058400c0076032002c00c00070940c90400b040c0201880d5540708504440c405503e641c10006a40c000c4025804001300c650280c00f0140c0c0700303102261081c88803092600c00c160420300443c010303503c43d410140c0f50000c0c5002d21642160b04125007a409030843e4020040d6081c41c0d000146148064220501000080b004240c06e02000c142200e400041c1c228000341e030b43c0004081c40018100c100c40317002c0380c8101c203801c2c00f0045506002d4031105945c00b070088600ca10454028404040b000c2c582078612980c28055002c503510200018000d10003c10b0040850907d00210010082c074000d440d10b800c0d40050028844000c00021411501c00e401d080009484101d0011000107000c03009280340550f09110550a0702822540102d005e40d03019202140600b1482005a03900d1000788002508000100b00c2003141c20710350b501442c2c004c60301c002540d207081d949454480c5402c0c400d540c0158401801c043c1401040081e01c40c28080402d0b546143c2c81001400c0d100c15102d0000391006441282c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 159047805 1250 159046555 159046561
    0x515030114010909050703050a0e0a05060c030907120507080607110706080a0f09060b010e0315061e0603010905011d010323011b11010c1b03110a0b070e0916050f03 72
    0x200400603140540100c4c0810031591401220040c0585415114200c009180c81759800c61080081801390b49513030498028074081e11580c0701d80e4180d910052100341d1030f019048000c1900f4841c40c1c82000ca0b5401803000340389031810688401c2c240840a0002700a0100504903100e6801c00801d64400710b4001d8107051000381d403201308507805001c4840803092603929106441d410481a54002c07011268280d898540d1940500145070340c0c2d80005003400d090142c00b10000e00039140030342c48209070280e2041000b070110100800714196030800e81024110700d454200500c030000d4a1380303d0801d046038007405075015500d5901e48101d030540b048403201103c4122100b142d0055400d410810401c001c1c00a13480322646c903401d0040c16901900030f500701550030f0a0705911107d11400e40c2054088041c1007440103480296820b0742c0014107803028000e40e003e9000e1020204000013610b5215694588070311098101070410445600f5008000d02c61100e030341e80350200403da004069616828401580945e01e403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 159049055 1250 159047805 159047807
    0x20313060f0201060513020706112703150708010806130804030209040201030905100b1801080c060d0e01150503010e06010323030705030301031a0108010b01050f0f0903070f050a051503011401 84
    0x344d50040c9405c00d014030005901c914541d4001e014050080c0001c2228500030a401880743c46003208915144c000d202880c1c1420801d49401c048148005045625012030032902141904080303c141d400f0404820040080b000240310490788010a55040700748000c3c41d0b07a0303070315241c0140c1c0406405046500001800c6900031f038044c1d1421900007084030900494409400d0280c841010490b00400100c202c02e01382d51511140744e81640e001c0c00162800f041210280606500a003000c0401162aa000041c070000c081c400c11180030140c1000c0c00a042c10038090500751103050b00640443d900140c010030115140c218a401c7d5040c014611803500d003000d00e0001d00d54000c40e032010b440c60000100010800c8845091180031405a02c04c5845581c1c0c0d0303045540c00c031500740030760b2070204908100660300c03000f40c840180310100c2250003ca013030005034000720f441d081180d000100b040500b00002e10951a0500316140208812681c1e05230100c848000b01c9100d0006110b0170410040b121b603915026 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 159050305 1250 159049055 159049061
    0x3010b0414040f06090e0706030e0c04050c1c090c0b03040b07080c070b010803070b060a061e05121501080a0c0903020609010504031b030605010f060f0e121009060c020313060f0201 79
    0x20a900700f070a1003010b480b40040d5000300345400c40c0b03061134422a94000f804e2800390203214805603441d00601250146207040c0005031000034041c00d01d044c800c2100348404040c102041781d2146501900089402c2e09250240b400c01c00c68005080d220801e004000004030080c8516038450306d545021201603e65545485c614050f10600030400c105010020902d40000006002c0701c0740289512800c9440b40014400840c915002c2c8100045100880811400d040b0210b451255510304d2308519160300214008000b49044d40e8100c0c568a070980c4000156038412000c1e03400180d0010b0070010510780050203007003e070491000030300a407408070b0540ba45a0107034064900840c2c108a1034a1101c104540160441c3c50324002221b1507460000041041001000402c0c2a5038241d00c2d00c0e0800303100000203035042010500784030f41c0a0f8220340f9000943d1014040c160381380041410214038442d80303103400030949800e441c0d0306045620a0003040c403146000203c010848040f81442001b01c0c05d045800c80c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 159051555 1250 159050305 159050321
    0x2060706090809060c01022d180d0c08010207030f050a090e0910060f06020706020106050f04050a110412020f0306040305041802090603010f09051501080610020304080a030e01080c03010b041404 85
    0x112140106400d803c181040d0014011003054050b210002c8d17002882019898001c0c607805001c1080c280603d4070860004200f090311b51a0060007a5500b10076a541d14103030007071942040ca40d82e50041121010942c2001c169640d4040900b081da0805002c03503401840210309200d4088144072150100e02030440512001c126065120824003140c1d40351503e00c0503840c400d109000040c030a10b003000490f68810321910003690710040200155065410820024050150209501a03900d01207560f040082000400003440c100041d1040c0b080d1900400c011005842c1556009030000030410000a074414220340030b81d0007108021140f8101c012a8000070b0054012880c1c021500000100d040c4c2c0190005504442001c8401d10980c0c3e5840045803a060b40880454046002c4902007909441c00c00c46c0040d603420203104880c10031f5a00c084151800880942c01d8022800a84000c1010f59100075259400078400e00014510f52504074039071040e00c5107100e181e4000b0003e407200c1003559503a401c0008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 159052805 1250 159051555 159051559
    0xc0a03090f050303090c0907080903160203010f0c0f0e04021306080907030c06170a0e0a0305090105090607060605031e03090409141006230f0f15041404050c0702060706090809 77
    0xa100d03d0002c041c159210851800c0351f2165429500040d6a5031242c5443c80c4510b10b05e8002e14245100100714040d1000003107022a499502c44031003406070701c8644603ca03e403912a81d43e000164129080c054410211400500d000300e00411100300301010300a065000c1f2030141c42c15182a03650721266500300702c0c45400042c06410307030040001b0b006602032108000400130402c0482a074507101d00b4002202c91a038070f05895a001a900300012a01510103042656010b041052030b141c0400300180036640440c1e002c6940e10364404091086040030040705c10300c89500c0041d00744541e0824134140d624007601e007480c0e11032078030b440004040240c20540404006004012603420041c6004500c02821241c09480402c01c10304c01405c014101c0d2860401c20303480c010340103140011110040c03003400354817140e1807504030700c00b1040388205407562402030000b82540194110404001c00c10401540d00c007805815040d54140091805662500100c80c50607501c40c0b40000d040140b880d01c206c0070300901180079 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 159054055 1250 159052805 159052807
    0x2062508090102060c0307020c0d02012102031009050402010207030803220303050610080114010c141204030507050102030301030816060605040516030e0304060c080d110a050c060f0c0a03090f0503 86
    0x8080122030006001101400d809071100390340d88001141132400103d8000c401648004240c101070b003020000f2664060041c034011524558910312910138a131001d022004003a40003003007202440c20300304658050008000c09020303078100344c0c000039a20f841d43c0c08003400c40da01c0040407030416403c0b01c2046248400180c051043e003401401c005d0b000380000c4030140d00030f0411f0280342c0c40d01441150440c2c1624040059001d280d60080011240c07240c01030350480e50b85100541041e8409401c103d100e45480d080304029070703a14107519019007403e074154046819588107100500000da0304200f40c903d281c14191080080c41c140d428440050540380e800340f0780240c03a08041c00145c000024000340103001640f014000815641d1615a5906c620f1180c0800030700015181c400040d00d03100201903200601201048521000c20014451b40c0000204004520002f5003d840f40f5014015598400c2c6480c494540600e020400660f8bc0d205610701003041507901c91504d0b0402c5226203c12400c1d41c9c03c0f03c102c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 159055305 1250 159054055 159054127
    0x3020c121504061413080f09010203090a0e0615030c07030c050a02131b080c0a03180c0e1006030207111216092c030703030b0f100e0f010309050a0206 66
    0x982c010110301401500c4d100c0803500003500ba100c2d60031140e41c4198421020b0b850002d100306800241c1d040b0050b800c0c110700041004c1401c0355101315660000d020f00003800401030a24008001780700380d84c2c001103142140c040c41008826510841985c4c0319a40600309071103000c840d80761440c10140400c4001754401d4440d014110f0710206944850740c2110103002000055000d02829151910708031000d039041d800400020b02498804e4100189015600d16480200082a42c0c3c1d8254844107800003011640c614040214a0000c02101e0b0000d2006060862030038407161115800d40d118180d40d00e025641039011290120020002d030103a2b12403021001500c180c450b41006d0182488844440c101401c034561201d400041d580ca00c2c0c007200c0160010740c41e008241d60160045c1ca0700c0b460179540505d100340f50920301e445200780f41d4042984c5544540031400c00a0800243c0700b034145c1c846041510344651040010000512014200d0301122115210b64038450303000c001c020032951803c070040880c041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 159056555 1250 159055305 159055313
    0x70b070c0306150f0906030224040e16020d17040b071413050405060604050d0f0c05060d0504060509030f0409050c071731031101020f03040f080708070303020c121504 73
    0x109040d1102c4d0b514012a050340c64a00b04140d50031804003035401003407082080c00c0000000340c0f441208013600d80031400c05130b40c0d80c044400c0c82c00c01c80e1011044a410070070072440e039606200080e80e288040c10a4582b0904c80d1001540c0594020300061801148001040c803050148c0c01142c0c2d612000c20b403090f91981250b140c51440703809071003000e0056043c00d02050b11450030409540c182c0b0005040c40c00365455170f031508895110400d03016500280d407014040381549604006040f605020341c00414141082c1c5800001c41700300803c800c03c030341c10911600f02c03405114000c40d8101d0301848000315640e00e4444010390548110b4000504000006504c2c0c44204403120150462100e514009529031401507410544107003504004080081d40719000d000003071100401c29103066042c8100ea0b9601020001103241d0350060300f202c444030100c0d441c100f2040310b007006908043c00c40079020f850800d2031940c0c043d56a000c1d210440c0e00c50041d503540c900c244402000305880d810a101c00002e15400d017410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 159057805 1250 159056555 159056591
    0x70302011b11011a0d150608010207030917072304110301150807020307150f020702041e0f0209030705012a0b150111060415110c060f07020609070b070c0306 69
    0x410078800f5400e02d07003580d10303407a9480e00340381034107a0140c8410803282850b5503071080380e0f52210169090903600d5402143d0601d00344080c140c458480d4403161000c60910b49544003070040c0a81e410310036030085609221040b20203c9071050b0940101c800242c1102c000c0010300640540511600c2c090786c0070000240038549650f900c044840f081c1c581d28201d1b00c0d0f10001703e85911130796030043c100b07850104e1020320301c45250f070101940c020410001070400c81940d0001d4240c802c201402d201e408081e1100c021400414403806581c40c0c1d80650861618100001194640c03207688107245c1480010607943c40c2610301a910381e40040900710813010340044915000c66168000d661014900e5a0b040005120754000c00d0000c41d100c49000041a041ea0f81c2e0780c0b00c100070b882c0410380e04443d5403142c85c040a0429040042c01c0480702d410040c00992621005088561600804120856004005100028001244200950703e003c846d25540d41c00a040c030050b0300e007543e48000c10213403801c1c0410162554001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 159059055 1250 159057805 159057827
    0xc1204080a0905010206010f03020d0812070c03080901020a0801170a051002030f01050a121b12060902030610030c06080606090a0e090c0102240901180302030703080a110f070302011b 80
    0x14075a50382c503070f45440049030b035000b003405841810f00d4183c000740050b150080003400c0ca0740c4507114407854180440c5400044110a4817404042201d071440801055009aa03007944500400d00840c05c0c201c105c0c000500d030510600c503456000d040718142c80d403e00c0081c03011003881500103003100d00c0c0501d2541c80f40c0007540116811210a00080c00200399031410303480202c03c4805164503005401d400351985103c0500c5500104140d500007440010018114034861202d50b008180003d080c5050707005060404800070001034031300544800134000a8000742440c400d5480c00c1c0b500288680d44c0b5008181c1714407460108683c440d104c0f0074001021054202c0c01841a8040701c00d60348288040d100680c0d8411400c0200c1d0070066140780728101000f4904800c1c0d5105070024008103080d00b854564800042031540186d0044e08006851804c1c560401e83c81c0c0d801c0032040c481004060040e03158443c00d0b01440e94072188406d000542001454403d4004c0c032032800060b0500345c20700020390030103003010b00f0708 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 159060305 1250 159059055 159059057
    0x52104031a0412050c1e0109030908030f07150b0d0b040201020f01050408041401201509070509190b12060105120a0c05010e0607060c08100b090d08030c1204080a 71
    0x5540008007591803056540c05180c1c040b20380b00c3c51020321102520b0355085030002503e01d10802041020541001c410202103540310400019040c4c0d0307509004110945070380110b40c03075520070000000c40482000844551641198001c840c034042d00d42c0d0540a0201100c0c00b40d40403040482280c00d0144d6103c280e8042e45c801d800315095910318030120380c00e032a0111000f901d0300100344010001986800711062000c20140b41c4500b0a620301c404441304144000803001c3c0c658891415058280c0114100380c0c1c00008280083c44020714280c0002c07449035004080c80c20740800542d840c0250482608100c0440ca40144400280c03124800c803a0307580c0d03000348102449200b12020380202d0f54070205100c50b816401442d03001805080074010b588001c602c02800390444410403120f0045003103441881428190340e680d00140d1704107902080194912034100d481d8501041003030316200d03510502c210700310039480603000e900d0741d6441030250f9443c081e14450030540c0d0005800c000c10030543d08000d001c03440613 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 159061555 1250 159060305 159060323
    0xf0711010f030b090109020307120f02030f011d0a0209040207050f0c03070603140105100e061809010608090c04050a0e030a0206060406080f15191103070206070201020a0e0103020705210403 83
    0x10940071002d44204549084d008800c80c00103002e000c4071030300110760085240c103154200190700c3e48500c04681400004002c0242c2c04000c0c040415403200304507004041c20003c0316541040001c1c00c010614002c0e101c50f0701030f9400100c1c03814580f20358066445060704807007590703864400500f00980700c440483d8250b100340200007010601d00d0082c8100b1251085079040e2960682c244000d120000305240c0c401018400307484c02c152265503848000700070109003080d8075420f509081c800d01c5484901a0040000d00c1300c1c000402c11240f000103480b600e02141104c1c04580f58440b80c00301c0c8010441d80d4004115400005511041e098000078401d000d21416641001040c0c2d60b0245c0030348491200b01202026000f041c800b040c03101c01c0d98240381d007081c070468940b14403051401010040b42c1d20b892122605002c08420011407503010701078250f01400b6070009524080042600600c1c2540b444521418954041140300030b10900f00006100500c540020261000e068903144403260018072003112080e40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 159062805 1250 159061555 159061577
    0x60e0a020c0f07080c0108041a0c04090b0105090f0108040f0c061d030705101d10030c030c0801083d0506030d0c0b041103031c05090f010b1003110f071101 68
    0x10b0014110040f61001c50113050300c00600401101e1000b80a00f082c0c400c4c04018a4190b03078040c04152050281038440fa0325030340d07a4a4a081e02007918421146071781808414401d50300c954072003070645c41c035440c0e0910305060a941c81c1e24068a4100035510068201c141403140803074469044003100d40c046403880195912980366004040d5100b14602605820588540100503918001c0481c40c020050849000e041c0740300765000b02c0c84c1d05d028426a80002601c070302c035881c0071903018802d0861260349032514085a6051030241070ba10041440000c69500d0444c400c1300d0600c01799101e21401300303600c00e050480500c1a11503071020300015101f0a00c039000b041084d802407030241800d500050ba0082054100c4d980d00e840c0c1c08200308840300203c1d05400104118002d1825441c03440c505011000d50008076030808142444c41d0185a500d10307a282e0785000011510707542c60b10110a511b140d1860046028a6500c07a9101c5030b00464160000898008c103082082042c08800b1148004003a81c8041100d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 159064055 1250 159062805 159062833
    0x702030417071206020906040b0c0106090b010503040f0201050a050c0102040e040515040c050405220606090f0e030301050405060a2402010f1b03091b0306060f2412060e0a020c 77
    0x82c41046041c0000c2814400000d1341900949145400103100e28200390342c0e200d00d0044c5074894403009109942d02c4100b40060301151060280d55582031030042e05600c0c2940d00c0d58214211944040d0501c40041085503d461144d0100e40c08030b00b13414000e544860340d800f038051107074000f130318100d9403400345030742e15215520303031910f000d102d00e1300035a003501040c1c60b00090100401c00903000088403013440a11540f800c107504c0ca04030b5903510965001a080d483c210810b03080760601c94040f0245410000041c20100380001030720b06566048074006a1501c51300700081c2c06c0507195102d001101c1050303c00c43c42c002c0c22204000d504c2000c81c1c0092001c0303141c901170002280c7c107401c2801d00241505805601c01842640801081485080045e03f0134400243d606140443d0380d0080382c81d5500e4020910409902c0580c10004100706202c0303240c41e007007000070030020510b40d000d402c04001041c0312655441604d908580000c3c9042071071040d080c1840058140030398445607801446106818001000e8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 159065305 1250 159064055 159064063
    0x6090f0c0203160b10090203070e0a1a041e1205060405010c0503010608160c061a040608030405010509090415020406110c01080105151c020316181d1e0702030417 71
    0x203180e683c02030f208142181d640c0c4001c800003410716900c46030b40050104906c110f52008502846440c1c6800b8000300c0d00c8001c2103894000d070381003074403440500a8078521820701c0034180d900f0348807000c150351000e4060800c07041841209a00204134018180c440805100010900d0b0340201c1c00341c0020b01601c024018261414482842007030002510000041c43c00d0150070aa0940342c0958a002040d1008a480e100e095900b00302d8940e4081c1c400d80d07412400e518040c450140140740c003a0146050600c1c200018090307000d0f8040b451f0140001500013010085130030290480da10f0f810308219200e81e11030030028800c41069140710100d2262a41c2c281e60780d8003985400741200d400500c00d4002c2342c1204072022681c1c01c107034820200c4020321208000c8840060025520a401c000543e040c2c109038000003c00882c8001c0b51060362502c0d001c03062100929000d0500145c43c60008080c0c895212a6802e400c07604016849104104500c024880320340d50110003031080328070700d03075280441440310119240ca0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 159066555 1250 159065305 159065317
    0x9020306011502010902090106112a010e12010f06030614090c1005090405190501150807210c030506090601050a050909060a030b0a1b0801030503180301060906090f0c0203 75
    0x106601200c010000309100601c44100d6885500c00490f0240d43daa01040b01c062007030300000046044512142d01c0d000d4100885d5041501c0425607020f00c148050320340d419032011181c3d050400c005000030010645400c0403030141200e81d100200400070107500e03101e000744050f010403142c65090519214040e401d4820003030080d0130000142064200280030040784090b40792030742007403000c05d100c0c4048696403481881d00c501c4403070107240c800c064095100411107078141c01007e4540380d1500d0503c82c41c0d50084a4503801450b0307041c007188020369250105031f661000b0301c181c48140c0c02e00c405170703500f5541a00414001d060555128031191510b40054a2074020314000c031002410a1007021814646038000541060f4064554103840d40c5a440c0e5409200040301e0158482d519599681401100d01e502040c10f21240c4c6007001d03095065a650503201e200e12001602c00c44440ca00d4221159401c1d801800202102882080090f60310700b000000380015141407100750b46420009480d5038004421900c2e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 159067805 1250 159066555 159066559
    0x905091b0612040c210203100c0c0b0702070f1401030c02010605030d050702060d06080604030f080609060904061e0b01140306060f030c0403020618121f0c0203071b030c090902 77
    0x1050460004002051510040090b90884d090807400030b210140e10030103080c3c0c1406011183c403003003a030340181881c00c2002c0c2030180d250752034254030324001903110001510642c1d00090054194076950300807460076649420000203000082000290001035400f07002e0507190070b0300c00b889103521001c4240e0803621035102c0d0340d81580242c00c41c2003000384564010652684000c200f5400d0040c03512014040303e6554002c07020a6000700148028103401c40c6a0003286405450300c80c065280000103c2c880f8000540b4540c080d00940000c2020405541c000b4484940780d0380760201e800784d401410310060441001b00c2404504c07510f42d20381c21070915201b00e078420740000e00440e14003443c8084401c0c030341e4801800003401900600000c00140e540100400f003e01c448403110001603030507801c1050100c0c0c901d00300c40c1103a110300d080c102c1071101e060007064142514540059040c1c0500702c00d038114883c41400074854890340025402402c40500903105882c05001900d503000d40303e00600041340e9205d00040c3d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 159069055 1250 159067805 159067807
    0x12110f09030709110301031b030210050c010207120807170f010519030503040e0a050c120705160b04060522030c12171303021c080a0902010e06040905091b06 69
    0x80041090014800440041c0c01c0341d506a070b480b0b5160003101e840902c51104000004010400e0010320210400400b990080b43d0001d10b1455002907020f14251612105120001c10100c0140b0000c3d4151420369400210030066212071500081c000041184d45601203244007900c88032424003c03840c184a4005003101498030390034001007001840aa80d001e03541106521740210000d44280050401025100604407060806115600540b07400410003011003c06000b008800034103042c126401c9029410500d030b40707030300c0c2c2c04858a035502c00e25000b402e10400c01040c0803c121082d801544540e0071500e00300300b120074000004000c0c101541c00500007880e40c1d0310f444042030401c40c038514207034120300f410480c41c0080080e444298000f03c400307042c1160261490400e0580600c0381d045411846d123941c10080c510000064892640a4441c540705a5141002c1c4116400740043c2c001050005005079141c80d910210480a01022503820255008002d00000011239890681076001002014070b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 159070305 1250 159069055 159069067
    0x709090533150a0c030306090e060406090203030409060b0702040f06030309061101060504090305091002070617090102090d2a030209040b0604060b0d0608070b030405070b1602040f0b011211 83
    0x42220741c88015554451014015000c80490400c024010700c03042c3d882d0503452012501340981283c2143d4064030300b507400c001e8100e10310303080490315030b038010ba04c2030001400003202d0011a14501a541101040c2e0b8a8000c2c00704e04000703040c01500007207100b1181440544040401c5200780c03041c42c84000d000c154180e03010300080f409200d80000c0510700800008406617918001020b0384c4522105078045080051070860a052221140002120500050080c40c3c5402c000809649410f01402080801040410a400829011200d07290310040480208001d81e0504801e00c1c00a480401c3c1010090302000009070b0b5131152001c01c494000f086108184d94584818400d4603000f01481d40c002e9880f07001040a0403918084d0085010740ac10024541e41003942c2c2c2c6241801c2a000391012150600412000400000303504013503500c8414041d40f117001542d00c10030112a100c000075802410070002d074140c4901e075809a042c542c002d90320940ea071084d42d210b600c1101c0c443c06009403044c03010005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 159071555 1250 159070305 159070381
    0x803040b0d020c07030c17010c09180b0405011e08060c09040504050c0904051c02160303141b0a030e010309020108010608190509070512120702210607090905 69
    0x16000807844810090310f8100040802402c1c110150801c81c0c00d1041d00400380445444048080240c076911030081008540346540503045408904c201060f90030000c2c1030f080f058003540c10440740b20300040c0c424009541c6403001e0900020507080074078050031051b01300041446001540703500503c1e40307145491611005405000160400800c191003a2146000d640040d407034070082244070300d0180d0080d0070070306400703001c40e4411254401305604546c46850180540c98040542e0700459505003001c2180701410003042c0d056004005050002c0c002d0b10318000040c01c0b021038200615442542d400d0089034601c001501202c01079000070b40051040001404003d014008190704500d41b28a8119102101d80f520400d844003103e402e5115003001c50304100c80d0400410500014102c44c0203025034580c0514001c0c541c2c009e04101030700c2424540d0b4103042c1d402d0390441a0420810410603240c02d49081503015000c0d0079070f0300c200c84104c1c0c541400a0a0400d0f04092105d5a4610701801089035001b103034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 159072805 1250 159071555 159071557
    0x1b0c020120060f0a0f0b03070b0304110d0303020d290405190c110705010c030203031605040b0d02030f060406080709022107180e0408040501081308030702160b040803040b 75
    0x4100c614044014414040700200708082441002a05000d8100703140200d400310581c0c0c144080008083e042155150a695012841c107090703801c64a40c040c1c803a0f031981800031070942810f031500c0e004590340e8900010306da4940c0040c801c0d00715004e0148005c0d02600030075407400111071340da8180b00600c08505072481c5070035086a40c000940000e20395592800003000c0c021038410840300800b203124090f10b2107120106218071401000300742040f1040c46003e8802944a03c8001c1906d44108940c0320300d58052070040c1e082e540074020051225032646034100c11a0b00079842a21b00c1100040c041d000600c082c03a042c040c2e00b05032090103014101c0c0519246440d0040d405c01212148401040513410942c60040b00d040f030304c00c184035a03a00300d211264000042e841946a0810b02480480104100206041c0011603082301d01c01c3c170f0084810354600c001c2029494a81030014203484001090228a43d40014444e0504000d4000d00521035995010580b070792103075100d07400b0f1035003040c40204800c4004030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 159074055 1250 159072805 159072827
    0x1050f0c030412230405090907060f0809150f0405150403120b04020904050a0b1e01020a02010c260a030b0a0503060f0402011214010611190b060301091407091b0c0201 73
    0x2c03c1c501e040101345115209102c0001e4030b0384200701d034003150400c02494035801e041c2d0007130892005009074500740230700200581e0005813071005000700c0f5030114840c030348204407080301d0440c0c0400301802414917040e0590009d00a48081c0c03034910440300003004c0002e00080184c0500e074151521400001c9400c01c000103000b0429000d41d1060782070088031b43c107480b1401400e00c40d6035801400200c0c0007080c0c040010709180d041c4d48558012150a0081d121b0b40c000442c48101034090910003a102e15620b080410f102c8080b4078508103815004920603107001101c040e02405500d51010300001800d0414860a04e1051055681c1944480c002c43c1543c500305c0c910355007050041c03601c0300f40c03004443c2201c41541d01003d40c2d00f18100e02e220041000070390040c81c03201c9403007134000948640307003600c4011705501c0200c040190046039544081145550250301c40308040c0d9020540510807100d0403040f5455620500c0780404860a100c801601000720f043e00a5890049444802c1d00511540046400b0f955813 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 159075305 1250 159074055 159074057
    0x60e0606100f09060f0332090316020402070804080312060307050303070b0c03090304050a03080405010305010501030209060a0e0112060806150603040302030318030702060c01090c0801060b071103150c030103030201050f0c030412 100
    0x8013410030400351041481814403408200703078043e00000101c40e045101c4d00401c88ca40070381003071001141e60b1103941c500c02078083e0101e07400740e01c805807800e04803030921890b071060f0214070002907a82010b460080c1802e22844c421001e460b01d043d03a0384141610707481200001000307800c581000800c2d080707003407000c2c40c0c10013a001c048034141500c441c0440c58012941d08141c0b04070301d011030200300d10341e81801240d024110a1a0940c20311141c4400f00303a490144c000700c94203001d503408084a090340308110401821414500900c441a9200e05450310348205842d6505038184030000b0400074202001100c1c041e55160303000b50f01d51b940f481d000160000c00300d584004240000c112032405a90740c2009089142c0010000281440d0245081d44081d00c075a48450b0003039040000801051408005884034503400c40311419a0860801c002800c1c80380e07400c070340d240303002c59a030902c1140001d100203141039a2081d0001c003c03a464500b07d00152240c100d5401005100801c000303400504401045031880d001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 159076555 1250 159075305 159075311
    0x6060c021e030a08040801111612210209090a050f010e041e0b01080f010c1e090b1317011b051b120306041107051018060e0606100f09060f03 62
    0x1c1440007034200703c80e580c0d0039116900045000e004600007882500090000d540086190a40c0a5403d07400c200c01c111000d4022103480400320880350040341315821303031000510100c15440c03038010103400a401c00d6071040d000755003000c00181a80107900c0303000d020b030b51700503a400050f83c6000f0720b4003488a4010310071076900324802e004441754007440341c04009403031003080005520340c14a20000e15000f607031241e070b541d260305020200c5181c54012440032a8100303110b040c104031508424081d1480b0085a002040c0340c0800200704c401710910100041c103803107c1c0e148ea81c00010184100c642039410141001000d950f040b01400309440c000c00c01850641015040701e420f904004040e20709069001641c841d001c0340000c00c209c56841c103031180d94100400401c555041c8580d5072641545ea40035210f0b5501e8165554040d4100042c001003008a00c96200d202804a002e448842584030300d03080c5c40c01406075a001401c010000d01840c103a42c4045410307506c0005051501c4801c0780c86440000d110700c20705075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 159077805 1250 159076555 159076609
    0x60a0801090305040512161e050a09060603050709081203060f0603130b012304020d060509010b04030201180605191b031707051201061101140f040b0a06060c02 70
    0x80c0a24041c2038000e844858540d07141030140f0458207041c89800c801b64001d901507011807012800002c00b07440d4004804123103090b881044001440254010a80c811912070002813861100d8110310251421543c081c855a240c4400540d08408140a66690743d08007080c100703401c42405000e140d1080c0300408608429803001c1c0800c0b401e40c000e466018079105004141c8050084c01c0c030425004212000c0640e10110307180091424006000303030820310464002890303414400040d001640075190003004c0031420350351074106039816403017440101d01151444480c0903004804044c001c040b00c02d1a11001d01e4083d483d40e00c095050075030170f840400d2000d1030600075081c124031050582c40170301c6500e403c0442c4a080207045400c60000300f50808202d002c10011103e41010141541141e002d030414040311020b40145901404e107402d0620b000078a00c00070400c071740610106280c000d034020241c0d004c15880b11004801510424050f034000329a6101030f44005060051248191072801c4040000d040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 159079055 1250 159077805 159077819
    0x110a0e0103111008090307020f0a0e180105010b0f032a0a0e180106140a1e0504051305090c0f0a0305030c0114010e0106021e03120117010c0314040209060a 68
    0x10a0300240c1d04404190442d04190500802ca58a000550b04080001c2c1c070f8070014039a624400c1c26402401100400c80b0382915440b00441d410217010a0b10300c2907040d26203200e024004182c8040505820340c01d0000006860a403001204e66100580c0c241600c0d42e0307240300d0550340800916a442a4a40d401100d020100c0c00e0300001c0e2034120500e80d01d01000d0743da418204881304084058929401004000410010f50820482c404036811107124584400c0b03c9181514940715000c00c8402081d462040040c00c41c2d0301900400503100212104161045901000002ca0b001104c003a40c5640c840f20103540c0d00e24004030650100ea0f80184616846522a56510300795001416400010f130744585100c00e2100400e0040c45c0588104441140c0c0396241c07540003582ea05810014000f200c01e60340c1600300c150700910844034207291100d40c8429a507555040038000445104003801c855290a408246461090140c40603d400304956100d8984560702000a81d03100a8003465101c4030820000800d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 159080305 1250 159079055 159079079
    0x903151107240609020405060d0c05130905040c08030a0e0105090321070201030e030a0203030103020405060f0904050c090106020102040602030418090f0614010611061501031e2016110a 81
    0x7441c0c03140c00c0c2a002c4002c611094041c2c030410781208516500600c02030025480d04801e072041c8a560010204013401c030541e080d0f60718810702c0c01108000900ca100400e00d80840d40056001d24401c5180d541400e50b507030441a264018056400000b410001c00e001c401d601c600040c29400c2c000030b0903218500608800c480b4840b208610398156014041241001e5603054490351a60084920103540b5007030040300003d4481c413050100a00c1aa6076602003103480d294100e8481c8140c1c8081d000702c40b0341c1002d090035175440d900800740074403984503000041506032040c000d8508a540c1038004606040c101b100d24080700006c108880304a90391242100c01040000c00c50790b0a40e4003e40d00013542058081070030904020580090b41489440c10b04480103030400903030107902c030010365016000e00d16000d004030003030009268a090100c0b80010003884003240c9900c01e5001180c0c444107444c6a00840e00c558181d40180c000c803d4072a200c00142c0000302c0c45991800d06ca0110043c14100707001d480d056000700d0703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 159081555 1250 159080305 159080333
    0xd03110f07061d03030415080703020d0f0e0f030903070303050c0a05061305010c030c0c08070c03120f030501140603011503110301180b0109050f0613170c100903151107 74
    0x7100608030a50300f1401c101c04940c065800d4000d14540f40c00d01166810072102c42c079001023040941c0c0d00180c80a84a58141c0b0b440ca02190310502243c2030b01d00260020b80956244a003803402034601020503028000111045584094081d0846924688059990fa0080b600a40980c0900d15444001500921005100745000c0c8002240c2d6586803c1003400c441080075142e0500d494004602d8400d80c10a462001e119446840305580c3d03149442d0045d107a58056100900301d03031100004d08101e90b08664154181c40d00d542d41041a80e90f03802e08074455101955415402070710800040c001444030a41d4a06814140c0c07d001c20031400911400c205580240d200140205500311028403108085c02900704090f424070b071484103141000005482c100e0300601c011f1040340f0009112640500101e10780c80241203004805841036200070360315841d2030750307190000d2260041481e40351f54280030300741c41d0b415641c0060040c2001c40903808102c004001c1709410340c003005000e0254000041312101c0281c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 159082805 1250 159081555 159081557
    0xc0d03090b071e0c0534091505102606120109020f0907020703050d021e1605100e060f09032b030237021e120f040e0406150b07020d03110f0706 63
    0x200b1003404031b0003000e96000c141c0000c00c080703003091189103811000024010a40e01c0403154160b4102c41000d05448880d440d00d41b002c084101200001450301400381800c1c4685000d481500e5011250340e412801c0f5848000000d501480044899544e0309000c3c5601e54003c80a004403240349841ea145e061a05607254503843c0140c1c0900e0b8000b01942c504400b813905070160400501c140c03045141e9040c07031b49225004660042c90300341242c1001500c11038082d440c481000d4002940e44102c0f0a44105a0740f00d01d0185019110b03800090f820401420002b0790b009800c0c0d018031104201d6030310110f010303501c492008000d00030302d6070380c004014413030b2006105150038100c1000c003580100d890181c00d148400d1052011301c01c091800c0004040045204510382041b5000556207464816560160340200c1d017001300d03000d0800702048100005e40d0b02c4505002401d02c0d20202c25a40c1390b58a0643d07202e2503a009400c5500108601e0009000d00c5030154030400c10802d640c1506401505c0c54542495988054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 159084055 1250 159082805 159082873
    0xb0f031515060721121a0a0b0a0903030e040f0c0c0303051803070b040c12050307030e0d0804180b09072c010906050a03020c0d03090b071e0c05 63
    0x30072016007180701908500151a15030510a80f80c0318000143c2140c96202c800b14800e144002c8001e22a00c142d0500d2883c4102c10054050303000c24000d5440c21841506008622284020694410160075203503900d40c0380d65000006815598103c9440400c004080c0e0030646130b140d40c00092046000d40b05906569076507181c204130f068107000701615006002c0b10000c5c41980050b002d81c000101c00c6810541c1c0182910f0101e466603d4080101c8150ba1702003c404d5a0418420040080104c0100401e41c001d90b42c005110700c1d00c100b003150300440058000c1010004100c1013110448580b8080d40d4441210400100f03400342c28041500114101c0300d080c00030f10f840c2d0940d00e1440100b140305030100601c50703240740d80c03260f0403001a041f02d07014040e1a0500c000800e0790240103209404840d000b00040b41501c440001c041c001070081d05e1600703000c44500020130001040d052141021100c600c0380440d80c98000b2079a00c1041d40c442e4540401900d40b80585c0301440131400840c056185010040024030f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 159085305 1250 159084055 159084061
    0x1002070b0711190b22020f010c11040c09180e03091201090b0a0e0709020304080f030402030a081c0c0f12240305061005120c01080709121a130203100b0f0315 69
    0x1c00c01103405d44203001004a0240090025854240c0305480c0c07500b0a007405101a09a03003070000b100d405203642c0943c800e003490105400554880c1100044070b4034143d01c0400d000488481d00240c03500340900d0390041d801446140050700e0f0840300c43c0c45211820000141c03007250b5407101030403c0c5040740c0695149854401d0441101e80030003040009200816046046045c45d030b4440c103491041280c95500c0c11004004038087d95014800e50340c1456100c4204c40d6954943c40081002c1140e16000e000000d03e007144590210303014403c882d00940da99a554014100c141c0d40b2040100080e0307036481529050340041c3c0c403064950503280e90181d400780d40148003600c0c1030352110a0326005904168081c4400b8100440e8071500003441030b882a0003405d00000039546c254048803641829031003991b64021444d141030603c5000c00b00d015500e43c0006000c0d4495442031000940c4000c0340000a405610a503d51481101c0c4c90b840001410001442c071b050b4501c0401c0060729100e02c051001c0c5d510b00f03200c3c3c28 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 159086555 1250 159085305 159085321
    0x63405010e010504200d0602030411060d0b0414010302030d0810150908160302010c0b0a1e020c121e0d0605060a02160f050a06050c010b030106060c051002070b0711190b 74
    0x44207440460009086170389980c281c00705100c13000e4524014086034010001c45c04100001c4d01850740c012000d4010350703c46c24028142006481c0c8044464040e0f40f8040a01400b03024049800e03042e203070090300910031440e0440d03044600000c01050080500c0104101092820a01e00c600382801c00c90b5580c46080e600307003200700d8144a0f007500e005400d11500101040180d8204101c140450b4000a040402c0d640b100e00e00c5010303011110440c0b555a440140d11000c200042d07010340188590742085a04541ca4885048014818130070030b046c040c062000c3c0c168580d5982801403c0d04030b00c511001c240b16a403400412a00d4104c50104009a00f05010309948408e8401c0f00500500c00d10080d00c000c00e1600000c82c041850074003801c0c0401800290300300100c04250014100c03807201600800007a540c80304000d21180381203100301d5260183c041e0103601050383d4002d4925041d0031010b50419a100d03080103a4100d150f041c6c8500c44c138090125407210600400003205c0c0c1d1107029496103400c619200300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 159087805 1250 159086555 159086573
    0xc181e120303150d0602040909080304050f0a0201210e120408390102010b15030601030b18060d030c0f03050405100c03090303030f060504020d020a02010b063405010e010504 76
    0x10500e40a64024020842d4101c1c0d2416180b150f500d0a440356800300b861414600068840c1e50481200c0d0f5007042103610400c40c0d19402140b045003d00c09136640602c20000894032205488000b03800a020b648051109108400824102c140400c0000540e04800300703002d410910809030a8420382c6000c5410410b514080c0321503400c568420500c81115100c00504032800c10b03041002c0f809800001100d0000c42c1d0007584003001460001305680ca8a0b680c0c402010700c0c40d8000c503041400a420f042c100541801c0a441408050442524001040c4e440c0f03170520030030764003006081d0100510b1102d810045101c0300c100c4c40040c0c1c0a507503100c1e030380e030309003001d0000c1010019205070030040360300c8280d40400d600008083c26aa854540070030110704940c02c183c003400d00340c1c000590003440044e541c4200c40d00e40e0b005216220640e0028041402c80c8820407a2a0003074600381c040744400702c848030b0161503c0f640b089500c0395042a50310a01800da89a880c02c541003500b09041c2c60f95160140424080303510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 159089055 1250 159087805 159087829
    0x102010605030d050703121d0109060606090609120305040b0331020105030414030c010f020301080c040605031b040212070c031101150b0708040803030415060e040206030c181e 77
    0xc0c000f031400c04003484000f071103840707024406410061608202c00c0c10707000700d0700320003064541c001880b01c2803610141110700070028020100c1b00540752900c0050b2441c080d03440360040b13900a889010056181004140591032005401c5081110030400410b000c8502c40c05140500c12500024001401d40b40b480e010f0700c030f01c400208a40e00d030071000110040c4e0f809004c481d03126070300c0103645404103826100e02d4614094281941c0c000c7d403d001202180c0c801c16400b13581240d980c142156441c280090500c0129046400383e9501038000c40c64040c448000c000200d0095000500300510304010404540c40b40b800503038486c00000c00303540c0f465043c19440600c020250326140000c204031421901c120018510611880c107640030040b401800b0301609100340c400a004680613a540c03407800e4580b42c1900c0c103d079503400380342d00e00e00031380892040b419180640c41590301912503891901c3e02c441c0c506e05034200d0310400034035415401c0140481d8495901d040e06c001507800004007440c802c6810400b214142d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 159090305 1250 159089055 159089059
    0x1109010609030b0603070b031801140117160501020a08070807300f0503060d0c05060703030509060a090302070b09040f0c08061206040b13030c0c0803040f05010e1311070c140102010605 81
    0x6401405002e20010880e908807940c4031504810702101c227202070151030b0448000002c0100d180c0006844000c4002c910598040d000c155110480081000507540d0201d0207110300603031041c410a00000c0c91040181101d034081d0480c40d06000442e9901e88445079814805030b1840548071060301c00700d014001500e510304987c02c11160200440d0001446401300a14442c403540c9420142f0040c80360481d000b90140038042c117050741d920214240030300a80010340b440003e901c600c000155800303c2910401c600d29601d40c0c06098514078000320071425412051045a00a80d15060507104086038860340030309000948481e421882c008040048200c1c5c0003146800380e030402000c010008000c0d8148961204c0f500d82101c5415940f410222030034200003500a203442c4c06000085404100080500202c40307001030350302c1317800741c030780c001142e1000540c050310703410248140490a600200e80c00440f46074420346400c80c1072088176103503926403900e541c0c0003404d1500c80c1c0d0024400da580c280280c0000d4001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 159091555 1250 159090305 159090313
    0x10f020c011202130504020f07020f0d03170c16060b030601050a120602070501140f060f0402040e0a09140d120e060106050301090b130501060e01031512030c1109010609030b0603 78
    0xa400002e02034070300484a407062142e00041011550301101603010150502801c1191103a40505000c04245d00460040c0d224038001040e0180c030385060556914407540c0b664441e46410840d0110340c1e018030010f400ca0040120900c010b5091301544103d29142501410011a450311000245400d084068115a0003019040c1e024002c2205903120004017540c4075100503500c58440c104039004240000290325007190000a00c485955049a80c5005010840741801090f400c07100b000100d11070341c4515800c0e0340315440000e0004070300c0d9120900710340c06030304800d05a6104100042c10480c40741c0c440408240c03c80c141e440009090303c900d8903100c3c2c2d804002c1c10b01d541021000ba200f030005101d500381527600c4e50800380701900c0746503002c48050b007548001d20043d6162100540a1003c101c60107002030f280c980c3e440c554243c031903a60403c407040005244a221580e4034102c69003c0b8121056603c0c048049800909890322107429000f440c003940d82c00303038941c1140350031034410201910b4a8400d82c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 159092805 1250 159091555 159091573
    0x307030f0b15091201060e0103051c030b010e0f01022104090b030304030309031b050411031806010e0714040e0a0c090e010803031311040f020c1018030f050f0705010902010f02 77
    0xc1c4660482c0c89043e4210740780842c0c2c1d00e41580c0c60b40900405d8002c141c42d0000340000008201000400100c091103251600c801c0199040040341241d0150075214001130003001d41024608098013010f03450134040c41600d400510782a4100d602e051107010100e6440310000e0100503010f018490030125000440203145041e1960f04c1c01007200c0503d00014000501301c02204400200c100c5d002c00003031001510910400608001018080d001260844400950150b07112400400401c42c14162404030601e0201c6403180b4404640101003000c1c0c0840d481010400407441d0800c40b034031903104600001d00842e07002c07001140100002100e40c404404186060010310098401005580c6e0050740401a0602040c2c681407046c0742c110700844e03042d00585030080e001000c9049070001c1001103c01000c846221b161200094211488000049035000e04400d0320000030b0303c07a46042d500b031a080c4c50817504000d803070b03c9440c005520404c0112030603036644200504558212450440c00c050328005041507070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 159094055 1250 159092805 159092839
    0x60a0b0f150306030718141e010e060607050106030f021801140103020a09030807030305040b1605040b0c01060509070206010f1d06010e12030403151a030a06020702150307030f0b 78
    0x41c1e5258001c100300c401000050392138504000201c01480c40980780a11003107003264007070040217521100001001180005000d1200c101448480402d10f0f4089083c3c1741e107401407120054201404080d40302d44200003560209100740903600c00745014000b8400000301900c1001460880c004078160f00300800310040140d00c80700b600c5207050540070b0a01580d140700d41c02040381c40382d1964000618001010440d00c0a040d4560702c03151140780301c1d00750344406454500b0400010035101c20b000c0d002400800090004003003003400f41c9404841e440010a845403644001000c0b0802242c10500580c005401006040c089100c42401001200344120300d8021741c01c5030f100f0320300b070040005040c4548841c400d003280d10f80001c9285d074180b00d003064a444588074501110340000e8400300743c5c02c680c1400c05000900b040c650084056080090003404000002e0707a492004e50011740059034005c0381d0755940c10655426500841c400e400c81d903000103000b0140301500f0115944100317030900907051044151411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 159095305 1250 159094055 159094069
    0x50c1b03120a0e0d0c030203090907020c0405011a0a0302071403031303080c04060e01110709020d0207060e03090f09040602120112140610090e071e03052a040203070203070212060a0b0f 81
    0x800013440c10174200b40403420f040c1d01d1446503100ca240c200401070104880960301045025070014219010300c0fa030390766a100c08035000328000c140829400c0800003c05024020390003452038034030410b41d0032580d4403400b1005056801c12180688441107400a0500301540001c05580c07203c0d074080d0050030541000c40042c500f100b0021100c1c1400220b0704140e002c49801c008250050501c01e02c00d5544507103509404010350064102169a03504240c2481031070326002c0b003030301e102260290204141c50600010092150005081541d12a40c2049044c10040300d0599079400381c42c040901019198503890302e6041c2c01e000611400f4560080d809200f400d0786680b1629003241e00b8040e012440440302c038101ca08105166210744245001840e104119515400f92036086900600a031004000403100281111040000784000140b403c100b00c122468130b94080c0d6000003041c41100e0402031141d002c2042401411860703039080c0e106500300018842107005000b03219900b601c51441e1032520402060701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 159096555 1250 159095305 159095323
    0x60306010603020f030c090d02031606110f100c050d0516080108011b08151207031b060801050103020a050409020a030e0f03070209061003090209130c0f080d03050c1b03120a0e 77
    0x51082c00141f070060554907501c045600d190018159807001e00700c24039440800045216040c0880c9494100070407a041c040380907501324151101030007901d81442100401045a1043c5000740070381402800e00500305031042511a81c440c4a0034a110034442c0d802405d2090160b2000f5400da0404108407034a102101c005449080c0900344034200707807200c0303e8040c0001078101c65140c1100101072a01c411381c0e00050403004490080000e41031440e444006202c1c1e03050030f8011080031030b61040040280f54880d5008000c451981c0c9001360a264403501000180d03885070681d1070010340c0340c0385030606c400c07014000181707052100c0f4001c5140c07600d26404284200001005184202c0501c40244d1b42c1501a80023600e4956008148100a142c10648030150400c291401e443c2c440329400040780440d200c558030020380303100074010b0442080402c011005408010700d18480040140f164846003004010481d50440303000000d103850300d4083c00ea09409010080416001a081005000f60020046030301d0003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 159097805 1250 159096555 159096571
    0xd080f13050a230904290f0906060a03110d080406080405010b0f0a05061c020a1808070b0d0c020c04060b180a0609031509020303030c04051f091701180308060306010603020f03 77
    0x81eaa80358281001000c14200600d0200d0444801160800a0600c60030340b241122510714001703a120700b41004c0c3e4810082b071b4203980000e50903205001051000c41e1a1401c003a0041104290700310a036990307165a00180e0040d0f0115540c501400704025080c05500610041610807260000d444c1c000101554400c2c81802d000d10400a4245c0d03030903e404440e03010b00c00b80800701399500c4401050040500701c00e40c0070a901c03001caa00c004614090046842001c039080c400c4214107105548812100824075441d866080d4810b02c480c8d03036259111801840d009000b131250461720341c0d00d87e02c2c44124205c510010f42d0305c45c001c1030350107000450300022383d0002e40b6005004400003050003e03040005100c5404083d5140c84044100001903100c440284182c2c0c00c05d6803004040d80d440e04030000800c0f03401403000302040c000001800003c00f84500302844014440c004108504204002c04031500c1a07002030b00041c80d442d040010307500782044103030b0040002c1e2600314601907211310340030458080604032030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 159099055 1250 159097805 159097819
    0x2108070c0b0c0c07030203070b070c0e07050307050c0102090d0311240412050f0d060306060501110a02190b0403060203011406071a070c150b0108010819020d080f13050a23 75
    0x783d100410040e040180d41d0140898032501d8840742804a140c100040c215800f220b45600480c03070a84004090340140e52540f181c038259120404140c40743d400c5080341c0000da40d0b0030701ca400d402c1c1da0b500c064a103d0134080d860703099416590f0840d982c185100400801064188400b0701100f00c2c41e9004010b034496040005c15000b2901c85c042280c0a20030005407002000c400b0401c642e500f0b0080e07001c01c0c2201c0c403c010803c44207554100544110324580580b80d050780100b8000781c0941005520401030a42e2a03058130751741912452803001c0d50300140c1080d40d0155000c00144801402c1c50700e00025107104036032050038144035640d0f4584c070030460203002042c20792800219003120b006040d0484101d40c4611005054102c5594160040c109402e205000940490001840c03002c0410300c848540401014100061101d40900c80003441c2402c044414204c208040c003c1c05402402a1040d44283e1509c0200c05d460b2078108100c286040c0c0051205407407100300c2c041800c265007140d1a2040c1c05032900c2c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 159100305 1250 159099055 159099067
    0xe0319030c1a1905061c080f16060b0301060305030d0222061e05030c0d1a040213090e1203010311040e190b011e05011101092108070c0b0c 61
    0x1110308946840c0c00070800c00c1429240303805849030040b01d610541000405600c215014100c007420344c0c0060f0b68003a00400301e507107403420007800001460a8140100145031501001c0c00c0c487d907080c1e00c8589407100010303c0701c2404080003114083c607210b0b25400c070000d0140d9819034580588a01c168070700012003603400140140071080312048580c6807003004d10005c9100303030303600707c0035107080154107481c40c42081d450503a07102c1ca409902500c2c0200030741d007801030501001d00314102c024040042060810440b201c1d4580882c2e550307000401d00072240220342182186400c08800c1511321010042c10140c110598030740507800c0000c242d9045035008104113075040c448002107401084602c00801c0b1170f01a4a07034005e0740844003642145030074844c4055144981e40e92086003c0403003000f04800c205d40f101d490400c015840f40c90002c014142800001401c08030f035a0710082c21052546824a003200c0c0c0004101c1800c0d001901150303c200703141070a0b590740e0801e940d40500100007c0a540c07280c90040b0b49 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 159101555 1250 159100305 159100307
    0xa0509070309020d03090e070306080706031a09010303031d03090d060b0415150f05040b0712090e1302090a090b06041509050405030d050c1e07020d02031006150e031903 74
    0x3000c600c45030060019548080350f4280140200d141c1c1c06896090400d03070001c503180c0e510a208030000c40c2d182f400901491800c10350102d000d001c0e00f0003c1d10209040c1c3c3c1505040b65a9640041d000390320945000400000204d6154040d1101d586068010b402c240212107d03a00c0340c3c500c0401c0207510420001e04041c0c030400050041107001035040e2107003000341c00400c021807580c030031008545180d00c4541d0404916a41218644218021811120b505021802c0021528076210036042400d08242d00c2d1152920700340003002c001144c6c00303d2074500c0d20b207040d001c2d0705192070240d403c2000c0c2c1009004001d07268445100188001e080203010f665038000c0d001c2082c4000f550f5a000d0300c03c2d01400e1045050900b41150b0b031b60032946821741c0d0075142101040da881900d070100c42031115200080322880356403168003c800d030002041030780c1000d1248c0341400103a43c01e21a85100e0203120034005062414494403540581c802d00300744091284001c2c05d21340c40d03940001e42c20030480e0780703000c0440903040d540b82c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 159102805 1250 159101555 159101561
    0x3050604092003011808040504050a020c120702040506062b0608030d1409031309020a0909110c07090b03100504060219020d0806030303150f01020c0a060215010807050a05090703 78
    0x402500c110042c1000080c0c0c80080d180003840804218000d2009003880c600016840311120001464842d080100300040c0c2003580010f540300010321801070500840180c0c180c10002d441c401da02c8081c0c0300140400452905200381d07a00b100056402c2030a1202c599034000340c1408142416004504886003540c040c1d00766041500035120f00c2c419a600e03640c4603a50400030f4620b06010424081c5c0c1d200000e507503091f001040d9500860b000046400031450024070b000258480f00d034400c208111410040351501407401340860a0701e020040e96502c0b6107000c413803070401c520350b081212614103260020f545036400007044400d10791f0342000025151540d01e4040d000744035001c51000d410002009402c1015004207404c2401e01454680002540c3c0f18000c00d07469101c2110001104880e134800c00d03407035040940d4926040c60f01801200c0030203049100003543c4040d66408000143c0c403400d002d400054440c0000ca0061001000900d49142018009001240300d401440c5c001c0620074001464035100b90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 159104055 1250 159102805 159102821
    0xc090510060c1113020d060f08061501050a030b03032106030109030e0f01091a031e060109170f0106170706020a0b1518010b03071e09140303070506100303180303050a03050604 77
    0x71130210364503482c641c03240002e080c0c03d10815071103028911000400d03c01c08500c0c42c7c401c198900d030100c15029440015101504910300710010180c0d19054030380c490714200014031090300422200c000350b2402c0316001501d1103000b40381d98040c1c1d0400e0714202c00aa0440300c0070304041380858104c8030302404200101c448128942c40f08107452f10701da4148440d51108402103000d0500c8191701164035400022a03580180d013030340d002c2d0004241490800c050b940b5188414080d40c02002a10034071200010b1031801c0d606550003130b030031941c4c00801c0c00004120410034400201400c0c00604a00b4643d51201c0108283c000e2080700c41c2760b10b00418220700c0d0b4951850f07a880450540140c60315507101c3c1c0603007010b40c004668450120700100054114507014454100c1c6502c059524544003e00349050000b0301490000800d40612050144600285092000307074800c0c41080f00f03821115185090040003074100c0c0b89046d0200b41d8809050020a0313004007101c6000060b4140030403252a10030100303000300101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 159105305 1250 159104055 159104089
    0x20a170a030b030616031b080c0306060c0307050105010602070f2607080a03021b012f16140f010302071a06130603081206030c1008130f0c090510060c11 67
    0x42e804025a0301c0c4003000041140d04299420001818111002100034124154850108da03c8000141c40030070307554020f56000c0030141c56142086400401c0318030315003081e00700b06c038107944802c01032003816810050340300100420901003280074540001d0031a808108189910a89440c1d5085800c111042000f04010080174040700c09440480c20b00075121501d901d02e04042c903000164014480d88200c601a10b010b0750310320142d544160342c1412400c200b05a5200b4003940c061b101c2c014010581d0003580310002d01903502c3c4540a004200b04001c2c020210100303050600d80b040c84030704046450040e01c0c01203002040c1a1003803584822000a80e001c3e01541d10006d0103062600120802c01101d000e01204118a8140c0300240c60b40d03804c05860709941001543c000c5100710501d10014841d456840d00f01c0b061859240c5d524009840c0c080311103144403016160549582010401c1c0749482c4213980e4802c103082d00043c4003908045005209000d200c401038903507401503c1440080c0e0361607000e007080e0001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 159106555 1250 159105305 159105313
    0xf0304060804030305070c0c05010f140c100e1513030504030b160305060a06020615180703050403140a0206060d02180a0b030706020a02060f0c070f061e020a170a030b03 74
    0x20303400000300000340407a01280041d00707240105000314050305912000a0b40320714031141031410500112a4400c850f40102c01f00400b80404160800c0364000030b02041d8945070181203807140407242c0209450075001010026440420540c9000d814100e840307400c00704400310101c280c0b02c1030030102c85a009513000503140748200d40901103a2600d0750f00b04a100006510103101c6076a5a404000030040c0034866100036070800c00020f4101180303445030310034030040181000405110003141700711240048400310003280e0b8030420710007419006104940e03811650403040c0e107040e01c00c4c0802512184043d1401e40a244a40c0d400c80c11590392a003050940c40789010480390707528000e00e00001908000c400c9a000b0700500b000460183c1c804a03a082440b50058001d43c500314100ea14602c081d80149410003090090600c0400c01c1d002000486009044a54441148030061074081c1d600f042800411000d5501801e44c05000135814560090340c2a08800b240f6190000c0c80781c00c5d005003001c0c0500982c1800707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 159107805 1250 159106555 159106559
    0x151b0a051209060a23070302030a0906020d060603150f1202040b121605040204031e020409050d03020304030e0618010804050c1c0b07050901021908070602040b09040b0303041203110f0304 82
    0x70003d4800d02c140070400050041d443d41820901e030841c0200310202c011034402d40080c4900c0c0c00f039001141c01c22079030900040d1008442d10380d0001c17038000070090308080d0384513102082004d6041c0107009081010040c580d21540c90500c000c031741c0340c06a104052002e50140e002d5001d554840d844400702c4880507003030402010308001196150a800446a42074018070100402d09041500c00d403003d6951216802511000c500c1584d4180b000d616070803a030182e198403000000440034405a200c66080391400f41e06c0341070528024010005425405000d88070601000d00e000c2e207021079269070007200b030038441482e4945042142c1440c4043c03402c150050603080603102c01c060341034071141c880c500815139580300361600e010450b0f01c0d116250b010707401a48900d10380b40c8800741c1c0d400680b5415100e400400d1900c4031aa88080c140d0b0400d5200c00c03000360b0003281401482c2001d000f28294182c084020f54505030a1910700101d0000440b17001c0c0400500500312127510300204481a44c0a034421b08032511a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 159109055 1250 159107805 159107821
    0x50607030c0206091c170c0a0308060f10050406080c07080901030213080111070303050609011a0307052703100501050102070b09030703020904060203060102070f030c0605030717070e03151b0a0512 86
    0x41c0d20076001c4032046d400f010929400c00801003603d2084080e4006000b00e507410340c0b0211110700c005040f15521200c000250f81d0943d49443c004203d071340540e180c880e242d0340303080000303010303c1c00003030507104080070400c444030000d03502c0d600f01c2d62180403d01f070060f00c0e490ba612440e048004d03550003000041d031915200c0701410940d08054150706101356230038041a03640300103122014100380b00b620810f08c0017140c5808a2400580519446070940c54101d08207040c01d0105403418480680c07072380b003a40500c16203196505017845002c0c00c40412480c184402d51418000039a164458450501034460100d050041540e084c030142c001907400030695080313401d0a0800c02e00961080d980b050240c85074075000544465030200e00b10840350030030a07940c1d125281540c1610300d50300042000c002c0100465540018440c10381c0045d0041c00180e485050b03442c040340505150524500b12001920381342e900300084030341e920208240c0d02c414221344a855240302d480680751805104416021200040200b242c49 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 159110305 1250 159109055 159109099
    0x70b03010906060e0904030309020310060609030b01090911040b010507020402071a010f0305060f060a1203020a050706051e0c0708070311040c0311070209070915030614060301050607030c020609 85
    0x80d941c074410800150f559050242c1e0450442d48005030802115000038001c203020707901418401c0d00103026182c00c0c0160403c00402c845141d005400030401c0b4070410300910549090762409051010810000001c06e611101a003042c0420720300d00c240e2701c5403080c4503641d00c98401d8500741c079030142c4190b496001e1440e01400410641031000501141c1e40c0000034507640b1200b2100450790400040c1c46a81c480e03103060381d584080209140d0f040841400001020700300750310b00940250190707003d0050031120346022030030400310758000001c1020a01402e50324000c105045008004405401035440b10a00203160800d440d9510078000ca0043c03600c000705209040341c0c58603015504507000c00c40d0f8400604181c0458041192200c8024000d004150047c01c010a2a07070300820941040da0a19540e40040340070500120f00280020362184010003000940c40341e0243c00940c00c9074031900750341c1407c01103849800b40300d001404010300100c0b5002551070740c4084070342800024100303070072202c09030340c0340864 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 159111555 1250 159110305 159110309
    0x912050f0609010621020402040509040803061009060f0c020a030605070503090d030218131506020d0905040b060f031504050a020c0f0610050d0303020c010c02061008030708030703110903070b0301 86
    0x368014600001c1e8a00010f219900544111001881c843d41071002c2035014402c20725022a005a801c0002296581c0c82c1007140e03114510584030301c0d0341c034580b41c014414440f140d91007075000d11680000a21440f60840076410080310245455a5906014000680304080940c409481d003481d04040c008007a51010045100d01c1608040320402654207030101e0407449245041c1034810304002d41000b41f807400701100683c034056020007040d070112201e112581c0010f00c5d44888050390246011303071103003a0400c22060040104590410881c40d0040200f441440707903c04140b0141c000100103407044244004030300c02030501500802c0f05c1c6c0760040403440254081c5c3d00303500d400d120b480d070441a102c1000810500c40c0b5001480b6040040c43c25040c07114076000c5100850505800380003003056010248030321850030040d54001c100c00d081c2641108044a4240c2204100da00204003200103d4100e200b1650080461300d00003c004415500300800d5001d0b803102c85a00d40120f4400041c03264070384000e141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 159112805 1250 159111555 159111583
    0x2403020a06090b090108041401050c03010501030e03090a090b0d050a0c06080f13120306030f0c030210090305060705030411030a050604060b030c01120b030c0909030705010c0f051801091205 83
    0x14003544400c420b6551481d14803840380da024003000000015482826a1078005100d0218062058140301d2031600790b170001c8a9602c14200044010446581d08d40600c0340030755014400b85290030000340220303826082740d000b0000f486865204842c03031600c482c460800c840b40c01000741e941c1a040f030302d0206007800040c0315040c0001d00b01030104081e824450400303405901070b001418500c501568492070368146209907002416034400000021951000e440c5881038822461251554110300c1001880d43d505c003200c4040103911071080c00000d400047d00b40e048286801c1090702e999030b5141250008080c80c0c4046d03050300500808604004000071010f000714400c2e43c050008e0799800003450750302d0603088802d0780000d902c1c0b05a0600c00714a580610380d203003806001d440d541450003000c40da01d031100342e80d0920141e00c00200b0006014082c420001151b040e442d280d21032101c414001015802504d01703503044161566680300700741c0e00403800400202103034803106003030521030b08006844a000340a608 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 159114055 1250 159112805 159112819
    0x60d0207110307062c0306070e0102031b070306060b040b0703051602060406120506040507020309040f0e0618010c0201180b070207030501050c0417030918090f15090d03050f0a0f240302 81
    0x4400d501c5e03484021083c030720000c2d00804581d41d500c3d8046400c615400078050540c0820880000c440c0c20b0b014442c542d43d0f032001c004000300e07842c40c48e01104461140d4401c0d03860207801c4c402403044180d4001101e000039050300d011512031203a40d04110307640c5684070000394000800140020001e0300035550082c0c0f0946817500300450390383c000038401030b10421a05500180c00802c401495441c050f8007d01000c6d002c02c20010b49003050a0106183c00d20a03503113450b40507003102c80c1c411224002d00550000407124030003400702d082d0006c140b111403200150002c290600a000051401d4402c100d10002190004002d00460400d08d04023800e43c2d200340140ca06d40b0460040e0442d800c0700000440d40140b0002d4150f0b280a80000084044043d028084200b50f000e2549842d20100081110a0140d075043c039a001c4141480d01145207480442e00014042c1800c1004018a822001105551141c0c82e181f0118640c100c0d01c03050f10007000b001c070580700081e8040c015406601004048401030700e1082e83e4103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 159115305 1250 159114055 159114107
    0x130e060d020f04021c1a0310110307110307020a030602030603070b090d0803130803100918020d0b0901150e060f0306040c051512040b0a0c0e060d020711030706 70
    0x84510004000c90207074104048188208580c181a03000b420907035000c2c20749002d4840e600d0800360564452007840400409249054103007440c05000245030600d0910040000c00c84107001e105883c04020852010f00c840e801a0162550041c0100d5101c203a0040210b1002522490280001c0d0416030317000d406440745a401180c0c204107242202d4070808000e24118540d002e03990303110125800200140802e60400c1c414000140040000d54041d03054060203501140c14013904104030781e00404144000711035110803101503107030040504000c070381100d01300c00281e41d900031060141c10304883c805242e18110b5400100c0c06040c2442c0e602030001121004107500807041090b40e40c120564000c3c00810040e803041106281c01c0170000c02e540600e00900341085c6408406104000c81101c0a8074051101c1b0108004e1550621a01d1b801d4021414000c84140da0782000c40d0407801036040c8203001c85c1e8001307508001d00410b00e2051001c3c0c400181251140303601d40030002c0c24035510101c01e400700c004007416 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 159116555 1250 159115305 159115309
    0xa0b12091c05091309050a060b01082d09010209030d090806010e061509031f0504030e0a1211030f0d021023070c031107090e06090f0d080a060b130e06 66
    0x514080000b50365150a20720300104001038164440d0942c80425500c444110009400748101e4610a00903440001c0881403070380058004e09000b450305122403c2c2c41d0408841e00c070400c2d41500401c05452010000303a0b100e111507802403150707141340381c0c3c9072107135040707202103980e02681d188107840415090b11150390762000c8410310100181d4600c0d0f80400550b0303007412014000409440f45040080445000c6503840304c2c01c141c001d42d00012b0102d400d444e8000c210a05070409035100e90f81c10141c6120350352a10301040b00300c00c501d24480007803d2401000502c0880e64080046014486001041d03038440101110082d5030341c0081c10078800d40508142c008190108000c0da2052000310040c89403401d41e031070030780440d03580000410890500c103c0603819031401c841005014080c1031070380800980c070540405241d16000f4000c02c500b56941c406014207002480c08981c5903405003182c1031408440d11010340030f00c040e0801c1d4000c0711840310041101c0c007410b0003c50500d81110042c002c00002511001c0c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 159117805 1250 159116555 159116593
    0xa0201060b030c040b070c0f0f033e03070b0310150513060f020a0b0901020c0f0c0a15090803030c0301050f01110a0206030a0f090809090c2104020a0b1209 68
    0x50f8114018000344000c0080464102c0104942480f0b010f100c003405403601c00e00e64022100784c12284e455050607400b801041100c20040329880608610900b12003110b6039800b0004d800c950101e01403cbd03040720180c56649003080b841c1c015103880c030043d0351645402000c0c0740c0711950901c44c030b19103101c101240f014000d005400702c503050a00360a5589000d03080c00002e980302c0b82c402130220210b101e11a074103004910350b074194901403d00e010001d07079075021084c41c03130b80360003092021a00550041c40c2c94038101d81c0d8002051084231846290200f421211810590351403407103a22829081c0000410091040c4c1202c0c01141610003c4691151104503070004651030100002c00040c2d55000ca04020050301e42500510f0340036140d000003180c075000d00c0910f14155005510211080314001c10300072114900301c0c8a42d9400b12407038464a08008441140c201c403034020707d402030500d18280d00170400395110823000350007038140212190754541541d04001c41528080b00c21285130300070680640804440c0700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 159119055 1250 159117805 159117811
    0x30f0801210804090c090e010819150920011e0c030806040b03010f1a0d02030706030e030f0c0d080c040b040b09030106050307231813020d14030a0201060b03 69
    0x449105007805189070344004440240c00d05a418074801d010000e201c54540c040c110103030200f540c50044061800418281c82001a008a02d076a00591881c1800e42c8144c803401c0c89a0344c0040c410707284030b0301c0d240d48030000b0700c0e000c0c10103480ba10000c460126002d0020918521261080c2e075800c0450078000c90620480c039040000c403001803d00200b540110307200c0d02c0034503008680280006050120080006d084030f04415507080042d44500000c0d00f1320707034001c0709103402410540d41e0440342e00803680003e0702c2e86124000c4c04140b564488404541c04020015245500401c1d080300c0d0760f0384090200786030f035000802020000500040006060700d180401540c045070490820117045c207080c607080c02c1d0a50810f035109501503581c0c2e01c0c00a04e69408104580041809030712124561200e014101c905805240700305010f03100000c05402a012040301719940500361034180e00d00c20075107200203005200e4400e8041c02c03050303101080f801c0c0c2c810f010000341400102030300204035842c2d481c210422607000403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 159120305 1250 159119055 159119069
    0xc07230a08190f0c030c020414070315150203071407030204020f040509090c0604150512010605030610020c0a230a0602030c390102100204080307030306090236090112030f0801 77
    0x804c074900084c06080c0d045100c0d44020808103100b030702c1244503820360344102d610f080002d841d640e090510032040408500903001c1e42081000744c01c00e80802079603a00c21080020f103c00c4074489540310280c0c00b4030960b00517617030041c025903a03483c02052040030b41c0c00601510340b00705650004621189000200403401c980302400050802e46894058049007200315120340038040200000342d0089103070751382980640440d03240e25840b4140308040c4040d40c07003285022400d651107804c0c525480d596003140581100d4000c0000b4a40320812806168011158224550000780160b0081111600807001d0500007403d00c00715101e00302c0780580300344110541c2041041000c001c210703500541c03a46507a01d8200c1c04e41170045074213001c00718050004a0340a036000c031140e500089112020558140200e40003484401415402d207541d8200c0b010500892692500218072505614140720170440181080305074024100c08141d81e40391201d954920840d0302c1100002c104080c480c640e54014041c56040e1a41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 159121555 1250 159120305 159120317
    0x201021602060d0905061311010206010810020f09040e07080d0516060207020105070b090705010f030509030a120b040c020105010e0a0905071401020a062408060c07230a08190f 77
    0xea070244401c41c2d0201d03034400741c402d450340315030008902c04122040c0205045d04a040405105060200c110060200c8181c11500290010020403100240d0f00c6100d903980440165541c04d071204105032481013424154000341003140c1241c850710040351190840c1c0400c801c1d10007a54105e1001c135040d101350b0001c0c6802c045020890408205290b01030701c411841030611514018641d1130309102c00d0b40c00c90b0b004a499014002c00c3c0150359200e1541d9148540c5420144502c1c1051114140c90303000d880000410000320f026054411812500490b15120010b0710801c011416544000c4c040c00090003000c0b60442c600f0003041503500349200d11000c083d0014050801d40b4207200740c0c00b030f401c400c01000701d045100c0d8040c02c00126155224881d5004c5500b11012988024612212004541030b48107417443e0300706a003002010070f1948121880140d0108580480b040300d0071f500c41900d240300080762190b1080c0e403941400c00c45039030002c1000d43c10310042c500388003c04600071101e10803844080000076070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 159122805 1250 159121555 159121597
    0xa050709030b0c0d0501032102010902090a05060f04020408011410062f070e010302010206151c020409120302041805091203130f11120f03040501050a0207080708010f0c020102 77
    0x2114044140c000c10900c8000346055131085421064550070f030410b44026074025044044d0002400450140b41c00500085c0001c070841c2d0005443d92030010444d8444a850310001a011303600c0e00b540311111080140119207882e00c1d111601d0003015032070880c100001c810303404100420f9404141000300c40003a0755101440c290f85c21503000c20008100e098071010780d0001c481044840600c00c88001e040b00d04c034644115803450000a00e03006001e0000360080042240b1184640c4815440c1c0c20313186800108041e0408052003c42c0040240c290003400381007100c80b911181c10b030306400810448100708107640380d4092000c40303013007101c100303854210383c40d40011401c04006480c42c1c0030359402141c82c10b4041102e211500e071018140c4158174112904010440c281c80c1d00c1c9840003490f400032000c0c200409030034592501b05a40c81c842d600609050000201d400d0505034400c0280358080c101100c2500d1041d5550b01200d406440c0c652404c454141c1844541424944140b003541c0d054000940d000d59041c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 159124055 1250 159122805 159122813
    0xc070f051011031c0911190b0c0c031603050d020f0d03050604063804050a05043902011b0807030e160b03090106050603070c0b060f0d06140a05070903 66
    0x1480c000c0780c0c80c000c1c082030042c0860748002c0038044c030803294404404140345999240601c682c80d4100c03034083c454508a07502c814070000709042c803001d0b900c502100756910f1120040491410710116500341d071610680a040c1000c042401e030b44030840348500101c07409040c0603030081e130f00e8084001585a0961100c050304c40f18910980209801c000050f200040071500c1c0c0c05409040e4261009215801c0b60840c03640001010456892540e6140402d84c541001c0c1000001000118207200c0e907403045840728010a1407103004503458034004071031500c024082c60b101d1b9100d0f00000400002001552820035581c481c1903070400150300085043d41c5034803056840c07900035402040c855010355001d22502041ca4070f401c480d80410000f03400011891626454140740850075101142c00c8280602c20500500c030640707400030722104881c2d07404500381406660fa9408250326622590344a135004152428190500046511100049808010903405552212181d8069035020380318040017400b000004c00100d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 159125305 1250 159124055 159124067
    0xc070e0c0c06040f03090e0a0c0206060102031804050a0f0e06040515070905011107230f0d120507331b050301050409110a0803120a0c080103140109050a080c070f0510 73
    0x841c0c402d08041a01b01d40760144910821011a03084844a80c0c0744d5441d019035404104c841e130f00c410f091009525241c1881c3e9501e9030081307640080c40c05542c50740302040c01d55440d07800c1603006424446c000c102c42c0121481c545d50fa50f4040d10203890ba80100c070304070b04010204241c418402c4c4420b45600b000c503480d04004445200d1100400551070044100106405851010707114401d01103d505c00c41c01001c1004000e0b041c034541d607401d8880c401203140d0100046442220a100301d00364208952680f28078103010918801c00321408000511824101407244e000c080c6131981c24000795420403400c0f00101019a203114605102008a0f400b40010001890070ba0420500140316070703003510045099801207144c1d41195046000242c10205001d0b070f14510404410385c4c4940e80703a0080c070410280c503038042e100480c180400341c40d00c4400d04990021100c25004440d409900000304c461910490a0480f6580c000344110328441c0582c4100207100594407000c0020b40d54000c0414010644021040ea11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 159126555 1250 159125305 159125333
    0x6010e0607050d0905010f03020705150c070f0303090308090102090901031407030209090604060c0918020a0306120308010f060f05090d050705030304090f06090e100f020f0c070e0c0c0604 82
    0x110400400c001070019106019070580c0c0142e0340c03202d003080b500740000549000c25a02d550700400d4818080d000c0824400100c220500703515820090454440028008580c464a80050044c0c84684450000c02d54994080c008a901940c0d420415807542d0400c94240d1003245192988a0520350041c40881c0e150049100420030100c01c80b40215500d501207030041504980226450b00100d041009114050044d4140c1c12181d25040103128104411b90803c000c1c0071541c03005e0240e020030450803680c000c0e07015102410ba000803010321002c15140c014000da009010b40301c0c09800405c0700084c014010521010610b1f81380e180c642c1040240028041c4c02da111182c10b440d10301c83d41070300042a4030180001c1000d0505c0203070200318070305c10543d840152071031588004540e6190400c2d2029651000c54040c01c002c08000002c0344903901014070001031700810084410508000074641958040021740c60101c418080d41d414443c0d4030307154106141d015091000a494021000040000340c10248901d9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 159127805 1250 159126555 159126559
    0x31a1e0a05040e010501030519380a020c0d020705061209030f0c0a0620040b03070e04061814010302010c08030403210b010e0a081b0409080a0314010b07080306010e 72
    0x400a541d0000607054074100c00302c084403a55030340c00501c2802424131400f1000760baa50440c2d4221950b950311a000d4080c1007118000c0310703416041c0c2098441c0691000b481d45100c48241d44154100307080e004000303500c014410f02583c030418070802c40311400460504116031b4000c0c60035003001110b800c080b0046000410002641c00304108407004210038002402e110307903100005040008080c6048811901c03001442d1149586102840285105890417030381074500c4500070648a84070380e0000c0e1180f68248000550081c14001c0100b07610440078001a10b440d03074204140032032080702078903485024080c003010780059100d50b1b44501013040d4000458100f84a8500340804440388c140c40181d50703001344910180a40c581c2c07405900766a00800008104400b20f420703007a0389242c00b14090b0344505000400785043c0d0086040b40b00d82c0d60b5680440310f100d800210781d981d184582600200100600c0140740c44d900104030001c100344003902d040d1840c641d401200c60f03113507803039101c015100400c10840c601c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 159129055 1250 159127805 159127819
    0x4090602090a0e07090e1003020d02040b0d03020c0a0905061c02010c05070f090e010c1707180e160c030c02012307060606110309010c062406020706031a1e 68
    0xc403181d224a06640b0007403080b01d04502460610b0b40c0d008250400d40d84c00030032284040c1040c81001421385409000b1664119a00814101310b0b1001c2405409001d1340780da448003014021006058000c10004c0320080100c501c3e00400c0d442c3c1c41100d0480790151441c5802c026907022074920401243c2c072214803580141000700403095030380d075020300d003142c150820f06c2c004150309010403480402e1302486504a64500081c8114000468020401110207a5100803054820b01103492180121651a00075080c00040c1d2881525042c82001726041900c440300300100303041c41460064031898035500c025605a940c0b031160441a00110340c1c00301b01c00f0076500d1303005c1c40b040b00450728500303c002001445c0c466040030a030245007041c0034010600000c0c2034001d5030030400c9080103a03a030040c6485000d40c0d006800240d5024009005408451004140c08240b0891030021950580020340c01c0103c80181c2d8050003000480368040d401c08011003152a0400c101c9101c0c2c6e541668107410540c51900d000d0064 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 159130305 1250 159129055 159129067
    0xb12150915060636031002030103020907200d0c230d0f09050406120203060c0a0c02120102160b01080105010b09060d0519061517010b091003020c01091a0f01030302030904090602 78
    0x1084c0c0c1300c064000d01d160860360b02a010254107091000c0f825078041071004500715131440c1c01140f480b813001050001003008044402c010140c0f9040c04507080381c1d244048034204d44401102400a940101c016174180400c51b0348884507882658440f00c0100d0b882014100c40e5069280079074442c00110b89082c2808020070b80401c0503207491049400a0000804c40c61a9885030300615081c0384001d040d40110b40010004c0001840c0c0180c07007610941c3e415582a9551416401114024001ca0b42c60168180c1c50f00c40c00e006010001110780d0680d50705a008010f80d90f03940c50003429522440042136040041409024118103031603201980c410b000c1004044403454001208048034526005000300203c005094003c6030740c00307103d208a0085121a00d241541041c04024003401980c80780e500c503810005081210502c00d4041d80c0064400ca4006e20050542d40360545d48040c0c1031100005038610341000400007029551110b04890705900658501111081444090300040d0800d80c1c911346c0030000c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 159131555 1250 159130305 159130357
    0x30a0207050d0c0e0c12090f060112050708011d0706020a0b16021501081c05030c0d05040f080c010507120c0e011b05070f0906080d050a120b121509150606 68
    0x4d200e00c5514440c02c05950b80582c026000013a071405440c00e030702c0f640005400020001c6c00940513042d9440c400211452000603d0114500242a00074000b507509001c1a0900d8610900454042609400588800b00c0d11050100c0e0360f5408404040c0c60381d8056404180b9442e0141c1c0480e400201e50f205a8290068800c2c407604005400c1c0d0010029a101003804840e40d8440d5501482c5140c05203480c606e50708161401c64001d00030700d000d044c03e2075a21000309040007600610961455405002d00d61182d25801200c0d00800040318200007140440d40400740300001407181582d0343c400f949480e111441c465004403111801c40c400c04030554001034080d004540c04000f014000d05d0f129105c81441428058044182c9150340c0c041d99503680302d0060400343e16002800e40c2c01285061800e0309000c0203d4234032038080c280481c01103400101c00c50b1041043c0c0c10104201c4031851210b80031900030740382d400c0219a6440f5481f4203410214101010a55528000c40209081c89969500e0720080d407100ca0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 159132805 1250 159131555 159131579
    0x409050307110f0406060801030209101203020c0117040f0b0a0e15060f01091a03151302030615031911120f04030212030103120c020a0f12030e03030a0207050d0c 71
    0x40706039960200040c015841c1d01c0c101404100d034150503141804840d02e40071015104d501c040c04000e200b0041c5c14002421100746000d004020301a14200c01c0301d2a0f0a420042e4540306198201800a10084405d203800e43c3c0d040d041c68002c0ea03100341201410003941d2103100b08024043d21881a80e526030b0280644008104048a1003981659003c0c04e10b080c98802c00444440f4100880c0c140218603000b00800816591101058485000081c1c4e40340e480000305030000c011064810b900901441c018400190164059442054252080e0403400a40140b810711404100c03043c04034400c1d500c0205030145015000701c038401503100b800e01e003045040c484902c03030508212000f17038200d5681d07001c010074140d0421900e0440116180000d21395411134a440146119080740c450602001e031480c4004c5480300041702008026454461428a440f02d011109980540d402540015080a03002d5901c1c0350100072515070700020b8000f00301c0a854401803203a40ea89400b4190751100c0c040d8400a03021300001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 159134055 1250 159132805 159132817
    0x403031d030601090f0b03060708130302150708010e0f0c0a0f051e03090d0c0302030403030e030a0b01060306060f0306080607030504022b0b160804020609060d02160c05030d02030a050904090503 85
    0xd012900c551780f9151542281d0303800c135200384280c1c800f50600c0401600301424a82201d414843c2c00b1f80020b050500703902c0c0940303007401003c00703808a1040180150303211003494140c1c0e42030645003456444a813030b46c1d540b074042500d00040e0781108000800d038541c0a062610700d0040389050050504108020710140000c41c00e081c0d0403a9000002080704202061064a0814640f42000c0f690003644d40c034001d5503030140740401020722100d45c028503002c6d60100994200c0c642d000c1d82042d4250303100c0300d00402601d00d5200d00d501054002032102c503601d009018183c1520540c2000740900d680c1d40001310050040030b401a60002668040031340514041c0a841003481d81900f07548405100e51710b003c015004000300b0700784c00440c0007895644803981c4948110b42198040f9010781d256183d150000380c092060540c84034a85100040002502c0c400d491301c0303100c00340100d0b11401d03402c0d51740c0103250f1240203100d0f82d0380050b04104014080725000710090706030000e000d40000307183c0d00e00369505890b5503c51 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 159135305 1250 159134055 159134069
    0xf0f09080102040306060e0105010507110d081c09050606010507031e0c05120406020c0d0b04030320160b010614120703110d0b090603010e0a0f0f05121207050f0403031d030601 77
    0x554400c7c03080000200300d0780c0c010300b002c1c40d0140c64144035448044820145030101c038810300c0000c80d040144000c40085e107200005550304c02e01a04000314080300100aa000f040303d40e8001c10000600781d60042c2c0c1503030b05094142d220610542d034800760411810545601d07010602004150090110301c04102420782090205d51140c0e0b1903042c100040e01c0d049540803014410030154a00b1000112090001740d002a4113040101e0b00c0c5c079000600e094181005410041d1443c004141105e522142d0b2907010282801401484900c1e600c64008540e451048400c4030b0498008010b500c9500a081c450564842445d290008078124644031144813a80880201d5006582b540140d4038140342c80c0c440726802c004118000c000da071008018081c2c9030341c1e402030040d0100e0102c50302801846010703281202101c3e80002038a41040305a8420300c050780200040444108120f00090351302c50081088440d40c1078142d1800d8140351642e60121500f8080d4808514404c0e170b01039180c0b01c103480800086002e4060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 159136555 1250 159135305 159135311
    0xc06052d01030b011509050d150222050405090d0f1205010f060f0e102607020607021204050f0f01030f0c0e030d051309090c030b010308030403030501090504030f0f09080102040306 79
    0x51400c010f024031a040e04540b60f07034803000409101540d048200c042c100c40d820340f2801041059420002081400c0006d50100a030001036010701c00c0002c400f10389200940303800d036101d0a84c0c44a00340b00840d14203c90700000b540c060b90f0841d070054040d0303a1040310700000340341002c1007103503242000f41641c000380d1040900402a0070706002d007a41010140c0c036880e145180501d11f100d450f20000d0740d9407019000c4081400f0a803d04250b0000742161100108040007405803010308144000959a000071030720640140156040804078501c0302c0c084504498005007101900e9185408026022104c03000e03050504d0313601e01c500b0300000b000b409810320742c9800d034031520071102d4640103050070020206043d6040200c20031441b409128074070305c0708050380c4d1a8500010110340f02d24103c000c2a860360800390a102c40c0310000401c104100004611403031003540e003442244d13640c0d80b141c0203480c015070300100400c0315101c12a0007a8810001d8a034071190070f1500c1100c40344c0d42d414290890388176130000e80d9001c1d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 159137805 1250 159136555 159136559
    0xb13020d02070b061f0806120703080301051c050c0402031806040309030308100f0b1312080d11030c09040519090f26180409020405150f010905010c06052d01 69
    0xa0f408a40e9000c08259103616810f003100850880e00c8040000082c280107424010a090351580e041890010130a601214211a00c900385103d26130802d1103414421580280952181c1c0d079034107401108107603c40b00074851481c41034208406074200070f140542107401e080010034440740420855002d5806600c070001d855065050081403100010405c0f825810455020003124000c013920700115041420800d031030f40c0703040951080c3d280150f84032055402c200400f440078010030300001c040a08019504000c1e08203020001030090008603810400b84105101b510402d0a0a80040d644020031401c901140e600380b92288080344c0c00c100003690003841ca00781d2242040300a0080c21440c0c82103c400c0e0030117103004a07042c4914416640c000140c280f000540f0702480c0c886800440002c1d50041060019143c00d0411403426142c410306240b094262000f1242c10754043d4504509882042e920001c4410003912200d0144c81c000e40503040200401c407000c1e0000d0441c1c0d41803000551b125902c58601c0d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 159139055 1250 159137805 159137813
    0x71205150414060105070f0f020d0503190f05220302030d0504030318120201110a0b0a0c030b0f0f010c110a030305070210140307030911101220030a0b13020d0207 71
    0x20b46404009182e426401060060f56030b04082558031103a03010200c460060501e01d06542c85812800c0002c0d04024001010400c206010014006140c0b060345604c8911a021744100d50640f110040031010640410409144140c00200741e818042c0d8400b1081c070f115681c1e40800c2ca01315017a0800c2e80000c50218081c001c042d0302241901013100300120406100d424295114151448400000d0600420401100207070380103104410849030080406921483d00b001c10002400041d10000002803428043d8045407801800c211113000c030150401c04118a600300540344201036000c1600e0a8210250130011980e0700031450010750f00c6691001c2e110307503803071040c808000018480141401400c1c00c42079904d032150019650f00a406190200d0f6060407801c01d00d030250305001d001c82e04198000c1d40303240d060740c104405200c10408400304210002500c1c0c10f5651400c001e90012180a40400100f41c081029070040281820000c0010390011742c8445110200d07400900105480c3d9004100c00c4140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 159140305 1250 159139055 159139061
    0x100801090c0e03070905090f010f1a0d0506070e13050a0b0a0f0806071404171501080d0e10140313120305040308041506120b090c03010c170712051504 66
    0x5114503003022031102020900094032580c00d406400104c40d5101b00040034007c041004080f84140e01c8001c12500d10007007841000303025a9050b081604a0365408802c07035003481510056003e401001921041d11034007801c9030040c021102c07030b60f442804000c092001c140c05d8460280030b20200c0000181c480786903401d00001c411550301c9401e105050002c02c100310840031a02070f5021f0741c20f1a003540391107250f0080d14124011500202180000307607100c1078040740009450481d000c148405540c8687c0e0b918552981c1d40301500a01d80000c1c01c11504001d9070400314070101102d40c140c107080e20103248144101000c0d400403642e110344c1000660401040c407546a1140034180074514040c0054682514050f03d00e0602504c0149034840102018854281e258000070207031403640d50f400a030714100c0c20a20300d0100f051321003c8540c0a0b40e100318480c2d282c1441901000121501d0b044115196140c0020258000402c0c000600c40701c131310309000e054003e1060382c2c4511001c45500380001810001c1c8011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 159141555 1250 159140305 159140321
    0x6080609030a0921080711090a0203060d0803041401050903040f0b030f040b090c0a060521130201050703030f0906020703020d030606050d020903101406010f0827030910080109 77
    0x29400400c551903007641d11480303000590742c21132400504c0070341404503020012100c44000d402a600440d83d90200320801c2c0800036090411510107481e0f86135261144102d11054072195802490120610000307604e060184d42e1250055603c00e2900070565402070942d48111000c0789103800008051154015086505010b0310a03160068250310b0002986400c0410140015100040000000704261750401941a148001800c254081e40e916a000350003a0400c0c42d000020100500c11045401030182c00c06101d2031003540b404c0c3d00701c807450700159208d44c0002005c1e0f0405450394440031a00c80e05001c0c0002c0c40d4401c0400503550328035410000c6c20002c16241003406c140c00d0144c204400b43c1d00c002600d41c0c2d41041c60006903030b02d0b041d50000e440d003002c220b0f12844403400c04208081941000c8146482203400f0380f00d401c2903003900001140d036420119003040c0e643c0c500c20900081400c41e0003c601c14144040704482c0307040003840004205d031142c1052840003883d030000510401d4858020085 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 159142805 1250 159141555 159141571
    0x20325080607050a110109050706091a0f09011b0c0b07060c0305060a091d1002030a140903180a0e0a0501030c140d080a0512040c09060b0a02030a0807020705030d0201060806 76
    0x156420700c0b0800810134401c0200c1034003000b8043c918403104040079404001101e9110341180c4045070b94040c0134041050500ca2100c00003020070004004c4412502192007510511810a2820310013800544e013100c440f0100f84001e004031151000054841c021a80c064520b258241c2d4072841c541c5081400d8940c3e820024007014181410700103d0b80300c842249042c0c80e464140801c0405c4488601d220b100d0303020102a106210302080580319224940c01540204101c4a0601840024221801c5a034a068810011580c0300b00314104000410b074102603003c0c2c1005250308496a503a0514058004044d2200c07582540d03184010400c00c40041000c100929008024008030407190002900704003401001500780b4400141c8008028810011a05001e4079a2102e40b550b040500b448040b000903070203601c407854038010011450080b004140c4a030802c01d540207500d04500c0c0c4000300c40c2e031200541032005500c00d170030b001710b055034090105140282076640000768451800c0d100510f4110b003d0300c502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 159144055 1250 159142805 159142813
    0x80d03140403140f0d0b13020403020904080f0417010506010807020606060403021509030111131a040302041824110c07062015040210090f05100c02032508 68
    0x41031502014400381e40c80360301424040b003800c00b40c840350412032044000000e0240350008828503108103a07071121039401410355030b0624184040a8036000c030300c124040a58091201c01c00030740054440001442201d640c1d01c880c904055070782a49004e4000200c4100303007540d442d4030030480305503440404954002a144024001d6090010128000344074501010740500301c4040900390483c030580031566070600240c02040111070302010111550000c80c0010b12289680000149517007a075203441070360b106841c1480d0301c0d07e8503550801c4011302d500340c804004030440303003907040c0400e0540401401e821a40c2c0b910105000352891900c04941000c0d582406a150910145260090004450056455a081c0061742d0483e42907444d01c00740d07042e910380c0050300c2030014018054240242d00342c0624800e60710801035200401090300e100445008040380c5249400041026180030000000c420000c3d040818141d00d00c1d030046824141c40083d581010b088070006148403441c215080402000d4030341c090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 159145305 1250 159144055 159144071
    0x3071e0201120c050a05090a1d010f0b030603070b0702040e0706030608071715280c0e01051c0c031103010e010503070e0c0720180702060c0c07030605150907050301080d03 75
    0x5042c4d40902c5940350f01700030300401d40c4900c0c0c1d04c1d12400c1c1390180c981d85000c440b5454500d41d01c07044c000824010540c1c2c803c40f241000400558038000d99000d044002d01829980d41050030161040c0c1043d0f10030703a4425103424150310405404e110703c0019010923030340407031805e0815031203d15040056201e4101c4155060160007960b6010560902c4050062a5013840f0740f580801200500740b0b0203130b903001740c02203c2603500f00c03841e25500100444c0714a40703e81000c2600b00e80151041d00481500c007a0b0014403a03903605030b1203070660104100c402da0341400204060414032101440d0402d800c010204040031006001030700d410000013000304140302c00403005103840d00c03002100380500341c00100302031048904481184440458603c0004014100840340d40c000401c0000042095510300d0240c06a81c021582c606e0f10305007212400003201c0d008161151442e82c55200603c002001009400c0c0015044a6a0b5481c20f1406024200a43c0e4a5440394141000e5a0505840c070f44030728141880d1483d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 159146555 1250 159145305 159145307
    0x2030c03070f090f0e120a031a0907030e010608030a0e04060e01031a041a091516020d120b0a0609090b040207111c05030a0207030b06030105010b1b03071e0201120c 72
    0x300d2003c0c0c580605000c10f9020110494402400d40110220350a0051200300400c1e070320543c01606014106507014002030300703e40c2c00441d03201c8008400d40c4c0c110708644000b60120340203070005d1680400141c00041c0c1c11360b482c4000c07419034020041c03003400203100e4501007001789883d00501c1c01400b054a600811945565506990400250b14852140f40c496002406210070494524010300c51b0181c1384240b480c00240703058030390048a0888500300318120124501c42c8510b402d503204108142c00a080b69041c1100665502d0400c650139094942c56080a4034161511a440401089107440b03260780141080840300a4400d11000301d400380e4410322000002c2a9852400403001009980c02c00110005c0f149103400e948000002a1551000203030000d0051740c001151011240500700c80d00300c0ba00c80030205403d0350401e101d107140c3c05a00303100c1c510301a40c054048907096a10842101c0ca0f00340309540307556285090341184401070018407956425942c0280a03e800c0101d0240c040041c1c44003208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 159147805 1250 159146555 159146579
    0xc0606140109170d11210d0e0d0e01030f0603080a03020304030809010b0f01080a02130b0405030f120d0e03120103060203150103020909070302030c0903030d05070f0203070f0f0c2102030c0307 84
    0x5404002c01c017554410f0010900248040307246002413aa190208403100110741c00380361300841d11400018613000d844d0340354020128104100200071394076005121411030044016100c500144401e840d920240000040c40e8400140032201d03580d24050307141d1425040191104000078940c01099040c0660400c0940d0b4a00007101003c0c0c00742405621600c03481c80304c20090158001c0c904441000d0040401c0c42140036000c2c00c00c43d1000c0307049a0b000b1440f640c1c215241c1c070b01d0843c6045094014007207405408040d40043c007401c10709004490610403220201d01e039400c03007a4000d035240c40d800030600c00074518588141807441820300b019487c10000c0e202144002c80028504000c255020001c07074124003070f82044a011000050482c0e4844640c040120024038042d102c240108010000d551800c5002009892005420802c1d00040da045900d540300b625a1102c0d04403001e048040000c19440482070118000300040f2041020112851061610300f030500c455031413007035004a40400440b81c14075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 159149055 1250 159147805 159147823
    0x140405010305071103070c170723030109020d0605040308150102030d050604020409021206090601092103031107060e060f090c01120e0d0f031505010f030902010c060614010917 77
    0x1c680001c49503a200300844080654603242d504c507000004102c8103010500600400380ca142c0b880b03a000001c81c01d6286c035610b81051040007080780320341d100403d50020034480d82d850480d001d0004541010700d41c5c00608115450704040360031995074030900c400e065101d544103500c49804c01da034418104018001070f40c0c030301858080c0c2244d19141e0300003590310746130758040d14014400030400303545070b6000300740b00c420445003150402c0c014995800050043d6100f00901c004444410b40060400c41004030640d103911071284c030980916840303084118948410790002c11b601401090000341d1010244075050a000c000f8005244401d45401800203603800400c100c030200000b400c001d10044105441b00300134198804103204540108182c80d400300b0f80008520b183c004440d60100003803104101390039541c00107401031500080e5441116000070340254030640489005041000140300940d50342000d40d0085e0308018040c05404c140954556048070390840900340c0c0c140403414509120702030f00ea17505945 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 159150305 1250 159149055 159149057
    0x1015230a0908030406030911030a080906031302090a0b030c180a0903170c030907060f02120a0c050a060b040f02030615091f0c12020c01020706080a02090619030b0114040501 76
    0x240c10459074012a0000c0c0280b0441d41075039100c1d982e48038007500a18049805031101d00c0e031001810b6003131401280d080c1070140e005c83c0d0b250a10ac2c2d60f10500030143c000814003041642c48540c850056030340d030320790f5038802c0b8402140401d02d102d08905141c1880c07480404030380258843c065000c2044d40c4006515840f524000c000a1403142c2800e00312251007005107102215103c1c0014800200d0100004501c5407254804442400340c1e00c00c8203c0d04401602034400041c0c003c4400c602c4440e006a00270a0003003918039040620304000d0325a142810802c0c07000301d0f02151f0300c9180c001c4604003070051301e1640d0115a011030a41c9440c9000c01d4640b80001d480c030915041c00140700c01650b45014070612a080300d46151261402c035070070044d20114416505a03002c20f0501500303820a071001508100442040c0d000c3c00b14580f03401c00580b064040601100d400640030b00c51003282e5200c0c4030261440d031004460380d138a08078440d01c2c003404644a100f409030401070500b40304840c02c0303000303411a42140c000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 159151555 1250 159150305 159150307
    0x18150905071b08040503061006120c12180203060c1e0903161706010f0b1b010f0e06100509040b07110115140a09180f0609060203101523 60
    0x40c90070222098001c418410841250a070001e1007800103100c0908143e84090b01228029145d219100030301101038454000001e00b1070000a0b01c0c00410b03001044000d441d420300307a22030700d203800c0e010041c0d500d00b1a042c614061510344000c01c1d86010001107030042d10007008146011010001d103090441030400078090700c400019061450b880030403030a00744c8030b209c145059040b0380380d00200c44d000440001803041841780034004590b0004400b0f4020441c0c03240e48001340390809500500c0c5d49610203035400c1500b95620514211900c1c0303203005803d0b03007600038030142447d0300c0c2c688241010303000c094000300d005003680401c02001462180c2c0c4103400c03000d14100100c8075040d04038a00e014004004100720704008403640000d580401c5070b06103448a00c1140c90103030381a11130841c407085640e00300d05c507442c100381206800e011408461058403058001c0e4004100d452907a2aa00c0c02c1c1d034015211049006402c2c8020041161000f50007912050f061a06080101d01e800c10908582554074400b485004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 159152805 1250 159151555 159151561
    0x3070905091009022101060315030f0f17040501030e01180b25080105040c0c03080112150501120213060f090e0c04141e011a0a1101020d0618150905 65
    0x4102e4560002003c50070b20565498801100c0c1800d10310821100305000030840b0008680035001b40181c4202d5110821004c2ca900d2958980c04503002c0700314410741d5100000c4a0250100c0c40040742031440903c1c241c0325070740c3c46250070001000c9031002c0c021504d00e85d01d0f0400240e4804482c01d0350342880f58005a030360000703031101c05803461204403003100c2c007000080c2c0031351110b080c030340299a550480b40103c0b01005840202c800a441c820480c140050004801000500c98117074807159107012a402000440d801c034420406000407242d003a009900d0000344059400700f14641003500c51809030710f800c0c0a00c640ca10340681c3c030382c254070107010b800d46042d211504039001050400601d07070740520040c8103001e001a134005812030711105850012600071500e207240032503a88210064100c600104034000e08415052520312950807400380c42d803c01c030506071628004042400608014010501c0028205103001d1901744842481c10ba58244503040c2010324180c0d400d0546003d04851007000c0c00318280d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 159154055 1250 159152805 159152821
    0x180108012d1502060f070e09040209091005130506100e0c09041419200904020f09030a0506072a020f0402090d08070b0709030f0f0507240906050307090509 68
    0x301c8542c0154916403070405004199942c001985402004002c44c603925585070103604850154804010070342000d41d8001203801400c0c503003c401e0348100800b007030340c03002541002c4003004c2d92400da6201110040041c00d42061150501005d034002444101030440b05240c104801c4821500512180ca110004101c1c0c14241c2c071950082c202001004158981500e40061062200024140441c0c403003490008640d210b8007000c4000e449030076111443d503040a4411003048065409460940301c420001d2110015035101007110760ba400703201c0c9006c0c044c2e5150512000317202c41c0e40e000407401c441e00856241008038481c00001c4c88050b40680b1250b04036100003000c90064469840300d1a0000382e1210100180000f41014141e19449105d0300d114a4884090455100d03002c0d000140403502c880b58142c00262503159100c840d00d116000313488034903540b082030071500160b02c400f400c401100d06803203045055115105c7c601400a50070440e055003424940140540740d1030140b540100d59410100c4c04813 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 159155305 1250 159154055 159154139
    0x105010815071b080c060a050903130506070c0504060305030a030506040c0c032706020a11030106080c1207051507020907110705121005090319080403120216021518010801 75
    0x10f541001020b40d40d0f43d0700107101076807070384110786000610f0719000210b00a0340c0c010003160070640d403e041483c1d032a801c160030030459038132101048a080490510005031f079181c5001c0c1c8c1c1c000b94001c0020756250450b0003805426240c3c003c0c051803041e4074042d40307020016007010381700140c035406240c02050a00d081801c0400c1c90007890800d41080c0c081a0000740643e030000f03016002078464041a4804074825060500b43c0b442070060032502e0308081d030514003074140b1040040a041c401000c8a00256854010801c85000040003a000c00c00003da6003041d800e103400c0c15034211407140380810499030f00c0803501d502e512103030084a205400b629221004c907901008184260900504100198142041841d039264443c0700a0f031201f008925a101c5401c0c00b0b0010503224903007507107403004e454142c0074011000b03600211108031303240701d510090b0b000758039074041c031007501840c00d10100d0741d585124000760301c002e044030720003030400901200502600f800070708155120110007401c0c21042124070341d42c10355 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 159156555 1250 159155305 159155357
    0x6160305070b1f05010203070b060913080d0609060b090901050909031218010606021603080f070506070905090c0c25050603040b0103030311070f022209050102030108010501081507 79
    0x228000c5642402520401c842e2104180c000326a089180144c0d55401603890340605400900303a41080070000309141480c50155a001c000d0000703007041980182d95084194205020501b4004d46d5003400b48000e09044c42080003501450f55000e0801031403200203403400f0350501400b8040c4c4500740101d00b420b501041940c030f481035803070001d183c5072810f00390407503070030702030503020380c410340c28200000345032400458658541a001d50050034140e09588035108554002d91080d02350710010005040410001d1040347d014074480d94405a50910300b0041050014014200741072580e420811181080b40014008403035408071644655240c1c0080e01c0c2006180056015070b802820010412080001c41152241078034070903281040741161000301070303225004a010040840e072144021001520345440c0520f810611424180714a070030044141c03068444003001110b5503900400140310380c0d0f00078012603000d03217040401400314140403020014a01d0001d4007000030300c0f09000030300960781309a5000c580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 159157805 1250 159156555 159156563
    0xb1b19020f0409020f040603050c030d08090604080a180e2e05012001050414060f0c0403060f0605030708010c0e0d0b0c07050a050109030801051e061c060816230616030507 75
    0x4a0181d8a040503900c0c2c0440802b1b039031190185203160840a40181543d5009641c240000d0019582d59603607169142e1003481d9480612450b0180321603040c01a0706200081d03c0e404152800030700b0404016144900c40c0c40802c1090004210000003a54014600204940c001d10300010b18600b03c10030007980246041181c0515401c01c0104010700000c0940301d4038511240c000c550541d0f544046010490b9400d1f40d0920840c6010001040441c007150401d40310021f510200007203440d624000280b620382e407903110401ba80d440300f502d400b04e260030100111615a003925800000c410701d50340c02801b81c50090112408007400b14070301c014482c1c2006120101c6130300c0300007080f01480c1401d000c2c02a00c0d00344109481805020a180b03518481d0b9901e80c1e4800e80081c0071282040600e48c2c500c1d001c42c01d4480d6103001680e484400066131742082000e03000400408920011490401d5070005003112541c0d64205072250a45011106480f800204d50000b40381c4a41510304a025103011074061040b1b03200a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 159159055 1250 159157805 159157811
    0xb0d0218130b01080c03070f0e01110f07081006050904031407080706090213090506070f0c0b0f013303020708040e040b01080105010501140d0b0a0b1b19020f0409020f04 74
    0x101e070001c55602c030380c1e000002602c0e09503807507480d03000000c10362004440e8400060034444003000724500405801342c04820504105102120b042c4910389080d80754504100207600000080100460a1041e00040300d02d0850501c107076410000800d25810016000800b04603680008140d014410340640360100d5102e680256299100d0404501070700020360180d1050b28a000c424115001503c83c00d038905a000c8050b19560382d480230151200c80d60b4610300814042151481e1000481d1100903d220359a8440e00c00100d50605035a43c0c0e41d850842c10009079040810319107238034040143c0741800e80c1d210a280150b5549210710308607525000d50790082e54912642d40900040240c5001f040c0c1c16105100001c00103070b80c3c0c2c2e800445821a00005100c01a0307810041440d40c526a5081810702c440040e10350300c0704540d5203d5801051340001088000c0d50f030214410720007c4e20a0182e4448100d0302d1201c402c40c201039800041030724425000c40c500c1070b90f40701048001c5481e030b43c1104240050041c010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 159160305 1250 159159055 159159079
    0x60905030c0705010e040c08191b08091005040c0e04051009081e0f0d0e01110f070302060627060109030c061110050906010501080711010207060902010f02070b0d0218 73
    0x2080da00c090b24001c00780828010215000340d42401e21501901d03103490703a85c504c0b2544440c00a003600055200710018600c2e150003552030340c1c2d41c824540c0001d1500c02d58400c0038500d4049000740c1005681503220b00c030541031100f0320000c1040c1e1804401911000d08100d50a52246c0c0382003850001c210b004442003e0410000f80c0c01d206811000d1702e58104042e42d0f10b00f8110f91844a04558403032180010701c02c040034080800c1e01c1106078010306441101600000b21500b00001c0c2809079045081159544036002851404060381030103183e401c00c0090359000e400d04a4000c114441030301d0050622030051a110000e086c5a100e41c0804004541007403000c030141f030710f51070300900a02c0c0c41d010b942d41c5071060941d41e4003118041d2042a1041860901070b150907420680111400d14029003040100460201c1031050b202081c802807100a2003040c0020300321300309200150400c007040c0081401d64001040c1004030a810b9000c0b1340721030740307911070069452010b502d02a00c031819407a0055006103c030280c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 159161555 1250 159160305 159160327
    0x51315090317070b2521020c030f03040b0610110c0103020702010e1201052a09091b041401030c1107210f14120406020c13090506250302090102061306090503 69
    0x1405174a0001110b000205540c100c401380d80020341c07080f140071108041000500500650b03030207000081c40030f10940786040300d0b002c0d0342412034105903415141c2c00030210a20103545401e05400100e107645040034007944e08420442500d0f041294203d5040c1034000500c1c20071a031140c1e600c4140100c0003891060071405c02c00666001700740884000c522a24548131040e014000041503810800945140a140c6030000040c0292204080c11000300c2e46141d030500f5514040050282000d000d42c8031b00c60398401018800107080d41c001301058405e00c5220803881400c6080401e00c4c40555045886e0764400300c8403030b070205411145c40c100180090240c8940803003048803074904000c0c84403881007110a040110300c1d50f080c5a2266128010150388910085000c1c0c1c10040414204084041d40c000b90264a0751992420300d1811030312822101202e0440b600700c0000c020005101039114036045080c18200b10020b55200740c00f6150071520100040c101c2e0410501d604260a8035030f00005484e21880d410b02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 159162805 1250 159161555 159161581
    0xa0b04020102100b030a140102040b03010801090507050913021012020f03040611040609090f060f030b040b0106031107062c0607020f1b060c070312051315090317070b 73
    0x60100d00502a40405502ca08498001c184502c0801009030010303d0343c6030b54821079480341000705d99455400380400a090607215000d5402004064008182c3c1c12407468000c2c1080520b4211030302c180002400e01034181d0600c030304d2081d041d9041e92103080403d50100c0940b401c069444402d402c041c000502039056456420146004e14821038050145809090007070600f8001d501500c0001041c0402c200201c241c2600542e802011301d10700050030940795070525191305190340060780e10038440401d1008101c4030751a141d00410480c50200880104141054843e100703030b03440684000e46942030381188121032512a03100036002c0d00c01180303007062000405e441c1e0400310b8007a030250088606003070b5143c1003c610070000742e07103411402e07182c0340b54601040441c4d0040045c00c11144580780d03020000170040490103d848041c0e4584c291503503d8684104480b607090f401c011041d50600d40f40e003210941100107030080c0d03640058481e0b1400101c140105842c002d00102a10303015041d1300b40110120410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 159164055 1250 159162805 159162811
    0xe120310090b03010b03030a051803120a080901060503251701060e010911030604110c0f010b0301060b0408070e0414060a0b12010c0207060f09081e0d08070e010e040e0a0b 75
    0x41d014031200d600c0d03400f05400c03203004004d2140c01d44c00400051820905c075800a11141e8140807882e1611704100006c43e2074240324007500030745200c0005484803180d07005500a035200e800c000003031040500b8a008241c580324444400c0200705414018603084060031400300010740408240012460b1143c08618040c00151060041d4035820f1000070a40b91013074003585080359484540b482c91a12441c0501c40140420402ca4400074030611500014540c01e06c074040c0c1000b6800d00104891408004060850355a0342c005404008108803c000c1404045011130071210300c80d002695650b9141422220b140c40ca01c40c030100c1e03000381c01c20040354420390f030700111b00c0920a035a02202d40c1c0c3d1921001e402c031044105942d0141c2d01044007003040c24401c43c60200c81c42c402c1d00d001442d207540c80b90110314000e291760001c0c10040c140307903040c181c054081104040d400d03c10b1801507128100408064800c0800b40c0000381003001440036000580ca8542201c00c1050006040342d64010b2203043c00c1307543d0349080e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 159165305 1250 159164055 159164069
    0x61e0906200a171905100e090a0c09020307030b03030403050307170301050306040b041502072103020a1b030215091b03030408370803180303010e07030e120310 70
    0x14141e11210141c40400c0d5012101e0580710400044211550101c044200400c1100403182ea849100a500c00c035004450042440d82c504100c020f05003030ba24460044001c003a491154420994000850150096002120710765540141c1d030792160b441c01c13400b404582c04042e4041c800001d00200300a0000014017155028520032140030b50340d031004910b0782c8020310800c2e0307144c5e00031404100485d00d130040321030700140318822903001070b43c40d0081441030b60889141913590164400302440d100c03000c814445141051071a00718540060340b10090403080d40e11184100312071a000d020000c15000304101a0980403081940ca4035150150075140e50700e42c111004400ca1214030b601502e541000002e49041e641c2400151070b4401850440c211203e105002c540c40f0131100341c0c440c3e0058142c1500720741d04075000f881101d50300e140919000256124902100eaa039600c20001006405c0140c000c00d0f4100d0300f2403030045004a03a60070b0562809411401220608c540081400f580403040d440e002e08031681d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 159166555 1250 159165305 159165341
    0xc0f0305010c0309033005012705100317040e010e070f0903050601060c3008160f0503190606030b030d0305160e060c0706030911030606030a061e0906 66
    0x100103003c80035100c80100c000c001c02d08914a922000032120003004001900100a210300d40030107074403505591013a4041c4111151107030403402e6001d5220300e8400c104403801c0c030500c60b42c10101c84c1c110080c9220321000c4c00d5000c00c240e08540c1080060112401400e811518007080e507100e8603440048041a20624086010314030503014040c003800c8544101c2c4d400c5130151816038a482c0e002d0b01e41a000d48002c50f080e00c1400e11010b44800b1004142000d000b41d13141d1700c40d8005000030050100d40c009010200c0c204405081442e141b80c1c00401160480300720704d003441d143e0321034a482a80f07134000103820203c60f504108000c00c149034907504c41d40c1e85400443c121380b03802c00d0001c425011224282d400f5110a18218400c0c02400d014107c44480018054112031502c4281d1484500300540e5070042c000103078841d0380300320904c0102240e44100d080118040d00250900000099a4a00c0309900078013450300c070f01240d0700d098006032001e000c3c42c0782e6100c10b200403059443c11074001d080d80c0401c4510018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 159167805 1250 159166555 159166571
    0x50604060c0e100206010b0a11010204080606040c080c030402040c03020c01050a050f0709032105040e0a050123090615091002100507090e130602160807020f22050604090c0f030501 79
    0x580f20525203155400c2d50090802642441071100442d0300c1008807109100c640b40c502445c1c10003d200800050a8034006804507060035020081550b6441110744108140d04080c08103021403802100c2d001783d4110740c00a002c005111080c1d01034001e11101c291254039110800c20910318980045100394001055003405680d07425007555404190301000d0130310103c580c8841d04000b04003201048002090034550300341540d030090511414400c8032408500c589500040007040d0b07261490441020b1070103203070b10b4001d501002140d403643c0014035151041300302c00c084203210340560084440445015203055281b0450f1070005c0d55942854900740300d05403900700001c2da1203100d0701141081d03850021450000b52075403111640e00b070742d03000410341d0410742c03c00481514414101d0466131051090940075241c40640c01045412882e908240c0c1c06402000312a40039203c990002d42c0d41d0740c11003d0009125100c92010400410641000511210b42d01c0c0c00410f50180030341c2040110b1b44101c009000c202 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 159169055 1250 159167805 159167809
    0x1804230d021b06040902070309080c0a06080f1b0307030b0102060f0103020319080d02040e06130501060e19050301020403030203091003090302060c0a11010603110109090203010302060d090f050604060c0e 89
    0x2221002000e005030400002c00148509000910407000c0b03004100300d080a803103d007008100d85c0401c40c1180840e9104d8403c0040d800f040c0a0314901a004480c1c00b01090f18251018160303800c0100480106071000c80003a140c080b95803080e0125014194965849190035000500101044075002e805442140000b66402ea4030088141c160303075002e400361980c010900e184001c6401e036140211900031080c010b510558003544040d1004003001c0f105030f612410604140104030503040d00c400200c604240c0103102842e04481c076400a50401e8644031071102a00c4100080b0b1103941d00095415400082d0003c240b690020103414582d5049030311098048002205508607201144000c0242e0424000101c044649201510b90041541820a000c800b4117015a08545050304220fa002844200c04070342940d015441030060024600114615411500091582e010300514640c903117031284a018100004689a084490350120450b095801c00d850030b5400b0f0001c00030308030001800010201c8140c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 159170305 1250 159169055 159169063
    0x1603020709111603050c12031f0509040506070e040e03130302181b0a03061e06090819021e03030409060503013b12131a07051b180423 59
    0x380d05034551101d50320f000c0d507020344203500311440c0303400507000d41d059844199080c040250310410b608160400303a104c0e03907845204081c2c3c091f00114014500003080100080e0300150080d00000c1c682400250310004c10b00103009000c2070344d80d068041c0400316102003140a413104402c00d680c030807900891620035038400d8202110044446001c8840c0c02a51031598003021402404112004c0c9000b150013501c404003401005100c044201e00b81d0851082080555400034858018208a102038103401048040c0781c0e90f0390446044c0640f09444040c00c0b00014100000e0002e042d0b1005030a45e91100da96904140c003c0416201d280e00a500306041c5404000a4858200000030400b912040804500f98007011103071241e9034100c25072058601c2070240c06102e0000d020441e1010a1081c9003d0901e048288000780407216070100f0700c0188400d100151000c03500c13407130000c00000a842c0400e40d160004a141e0010003c00518940c80c805000c14448045503403ca000c0c90885110340c059a03401c821980c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 159171555 1250 159170305 159170317
    0x203160303031b14071205040e01080d021203070e09100e0108030d0609061505180310020901030605040507080103080a02120a09080f16050f181e010b040302130b010203160302070911 80
    0x44c01000300003440005030007402c0c40c2012030300c0741303491810103441f900038064452003078004100f5940079160a0f048640d04010f201c100103600086d150640c200590082e10301264044128440e0b0761a000013150b080c005000500108040320401d01039594841c2016107230380c041903030100690709289001c01c0103603450164400b140c400400c0340340b04e02c5d24040219051b80140004903a1145c0c1100c0f00581e0795003c01c00c2141072240024010b9a64401c20005011200c6c0c1da4071071802207041004000d61240c110308680c2c1100d4220012981d94080180b00305d0901040c880a0100d2007000316403c52140e501c5246001a80c0b0b108089608055102e100e15644100001a240601d405500c0512540c20000c1c1c04030301c032a0001e08590784c2900c1c0c2c1410802c00150480740144101c0a4060b03030580505a52a01401400201c0f04d56144c02c4c25034010030540c0e0558400d5990442d203070240c01d002d5034420000c0310040b015068011884929520b8000e440d4102441036150207410200410850284902103941c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 159172661 1106 159171555 159171587
    0x1515040902010c0b0c18120705010302071b030804051201020903060a1806020f0c151509100305030a0c0c0501030b0307030b06010507080d0b0103050c090f0d0203160303031b 76
    0x195243c0f0001a1032282007e00c8a24080f4000410382d030040d1482880d02507a20f42d06800c01448540f001c1441c4410f00c200802c00000380007100014200350381c000c6412448003103028012038280d003e01124180d00da0401c002050744004140c0c02042d010840090b41020980070b070b100d0300d0403078118141c031008007040001c1048103000d05004000204021200303490700740c1031128402088a0170b50343e0300ba018a17a408080780e5030030189084280110380c000300312031b50341d0101180282024501c0004496907058400041003035801303070103180c0c000c420150040082601c0d58860022540000d440641400300030030044010480000080c24640c100100c0810b43c0780b22640018200d900081070f00b43c81c8070b07040c000c00040d9600d40d4400c0e113003030104940d500c4020381e01d03000281c10102d45907020403c0c001c02c0d920000c00c15405400c0300c0c1000019142c0720300c18110081041e02c11130b10442d9848 = true := by decide +kernel

theorem cover : BRFrame.Cov 158992805 159172661 := by
  have h0 := BRFrame.cov_init 158992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 158992805 ≤ n) (h2 : n < 159172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
