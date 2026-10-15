-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5210
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:06:18.527645+00:00
-- url     : https://prove2.me/submissions/299601ae-a441-4129-852f-fca17494886a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 936870503 ≤ n < 937050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 936871128 625 936870503 936870509
    0x9040212121b0601081b0a080a0605040309052403070e0307030b1f08032a031201 37
    0xb50601003203580c030b034a00c28008080540c1060007954403001800322030340c409031105041984560340c4004030005003900000b00c450907041801e20030068141601c054000c107625180118180c10003143c240b51010b40303508200c000d101e0412048103142c0c00104a801040a03902d04240107550038016400110f00800c2000c0e85414800e548642d1002c113409035203054075440108200015003c015682484020200707000c100c0010590211000181410071405010001d11203074004003a80b0941d0603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 936871753 625 936871128 936871147
    0x161e0201240501021014061c02030615100314010b0c070803040803120106080408090904021212 43
    0x1402600c81020028070140100c0c504203803134924106072582c81c0d4091044940230b4a94401241008003551400341c3c405000c2c0500900d0800c10742e0010703416000a10040958481303a1208051600c100da000343c00d582e0140f54151203440b54500e5452000d09000741c9003281d9904030403058000040c002427011000801003800700d2084000c480705a980d00d034182d82c0058100c4000d40450420018040d042c03074001c4610b50310600c0201103807214610004980d02d0310300320310070b4454080750001d43c0415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 936872378 625 936871753 936871757
    0x21e03161817060108190f1b030f060507080705040b0d05060f0907021005161e0201240501 41
    0x40064410b10040181480c8020001041da81351314064104d400040c54000443e100c02320310340c21003141e003000e408042864462070410507181d020318071580f0f042c0c5d207070701f01074946140403a8248503d220b40e0310500014800e005d44c480d055408280c1201c00240206042d80c031150104103c10003c44041e07001d42c0140c501c40f02e0b06842409107903446032200e140f15001e0400400081c2540d04410090120304010304620b502c001d0003540b10085c1803141d100c4158840e0000072920258001c84c0c064540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 936873003 625 936872378 936872383
    0xb04050102010e120d0b0109091a0406080f0a0602090f060d021e03161817060108 37
    0x200240340b08056102c0704144000c00c04c3d41000c001450401601e604854110141031510b00003860b07840c40c8140449400c09060b4404214504203034800745080c1c05600041c04000f0060f01c8025101e4001c2c2d5500ca1208400a2a0507008243e5035a41e07507a034500d25402d048007400c200ea82e4591041402c00a6022810030b40c41c210180c0900f8010f0092030040c1d07441100d40b0f0407001d0303200d641c00d2030035114a00c4502100000d101044c01c04100044202e142c5000b5441100040c0320550405000302d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 936873628 625 936873003 936873011
    0xf0606061b010209120106061d030304120519060c0f03021207032408060a050934050a0b0405010201 45
    0xc049c411034980440a1100300841d1781ca10a508c52500b403200340c1d10704841040004c1c000c4404040311140c401041141c10705048000b40044102e103808650080740d1441218024000c0d900c0109a0025401c11913541c91016409000380300c4080407004521080c0d01c0d40c00c1078441e12080a03202003002000b0380d2425031007840c110345e80a03141e42d400b070b8081400d0f0030041d52921540008005071643e03c18071003001c48928100b100d00c2e40c014541c00582d034100811b1800d10340c400b5100300c1d20b00368001d00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 936874253 625 936873628 936873647
    0xa120c02010903052b0e070513020909010b0f2a0f0606061b01020912010606 35
    0x4105481031091903111945550303090314041000c0740322041ca00d4804412401c4411142d1800908045e900c16501d60090810291400501d858200040701000041042c007060041121122030b9580b001d12605650502d008640c85004d2828a5078890003200da0031048104904a40c1750303140b201488010485940504583e02d410000c403201342c455106403000c035003103241884480c540400710780038540ca14041c04001820178506100051390000c290740c01800d00d075944c5105000d265400540c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 936874878 625 936874253 936874271
    0x20d0309020607110a050d0602030f100e011a0d021207020705010f020c22020a12 37
    0x41094180300c015405a0380301000c40f8051940300c504000d030a904600401e590310150f60105a00c04881090310081c40200c0e00114400e0081440c0c00455a4130f04601e40c114200e180241d0f403e0660304801404045881c01c18100e14800503900d290900c1c030764908840a0742e0101c46e4080d2080d41c1c0f0001c1c460a42d40402c182d501802090910780311540a1000c001d40d50f0710181d203040c6c0301e170030300c8440c0301800220320392191004408060195a10004001d000d054442010020340b80c040c9000d00074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 936875503 625 936874878 936874903
    0x8190c031a10060516030f02160b0301030302060f010b0403020405130602070c141e040b01090f03110102 47
    0x4e00d07680b065249240c44102c11940b400c0c0482c0c0900c1880110070041c1c019074161114100d08582801c21503009000280400720040c0140741d41085159070040e81d420b034a15455051800342242805648030091240380c072038000902450f00c40c0f210101203944910b081d5180d01d0700f0b180c00b800914042c0105401c031044160702e00076500e02260015643c0d030036003a4850700c80b2050700034170000d01070b1046094140302c0d00110000701e00b040700300c90200441c001c0503800010000140020704144000495 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 936876128 625 936875503 936875507
    0xd0f0e1f08100b2710020304031a040c090c121e0c0908190c031a1006 32
    0x12402d458503203034a0192090000340ba40c0105040c64043d41600d540e10b801107041c4001c0c0202044d034804600c086c0d541e030f0260000b920385203a555043c1c441c1d1950401e0481c8103542c481441c8403c81d14002400d000390514030124000d211003c0d132292000c0c1940d114101715000c0807521200000380e6809044111080d50706400104200c03000c050180c14030018840300070000c01c01010403030480a0500b02d908000360b0704000c00503103041881c00030011850103014016800301c0998031501d503503000c003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 936876753 625 936876128 936876151
    0xc021615030b0102190609050703020d030513081c0e0a051201022104050d0f0e1f08 38
    0x3d00c811505c9201540e00214540e12124010704c81460200d50520030f04101101507690102518001c6219554503a6110121301c03110143c40895031100701c241d8000381e0200b20740f11141e4820710f940c42c030343d14008040e5900a0300192604410741d100035004010030800480109040d0004e01030b00074541c802c0c158460003130121091032902110090004d411421074070b072146206905802c441d101320710f801c040360002d20001814001203592a1083c4004e03c2000344451070704251255400740740e0000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 936877378 625 936876753 936876763
    0x60907060e010e180c120f1e09100e010605030a06020c010c03050105130c021615030b0102 41
    0x1184213840380207915501c080c0311903d280941e580c900b203000484c4514450308280402e0713101805035020705458601e014403500c0c0400c1d05000d55520603943d440c4c9007101c0d81c10032640081c0b070019400403551b2200c510b800242c000800c0b00c1d900c03130303020038a4001000301c00c035001070303000400d038170940c800b0b02c42d03500030614501d41808507524100000311644071210400003040ea4401015030054000c00404e84074801080590395100d50782c10241088410b800b69000c0824208205481c1ca5840456 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 936878003 625 936877378 936877397
    0x70501050c0c04090f0b01181802010c02040c0221120612071e0503060907060e01 37
    0x444000c56101c6500200a401d0039001104c1881c400d030607680341d0031600e540349050000d098000b446800c03074100198940d45141c0c01507002c1007a03040140c2d40100c0e13a58000800c41c14600002a0040380c56000110125100f0004c1411918404289007410b564450b840d40143d40000c4c01070016200410202e090781c81c02074840c2c02d00070f603450010032100f450682c01490802c01c42d2150312080c01c4001c400165502c0522a503481091807001400400b030504070040e0070001d9a2542e0b50421100c5803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 936878628 625 936878003 936878017
    0x60f060302150a0201021207080105041406100c0c050a091b02031c091e120207050105 39
    0x102e804030342d01140e503402c2100081112041c0b20b20075410f42d5035100c0d000c0060460703810039010103002d11a0a004480c0641c0c10030b40701490b402c1000c40141d004800c094001e59400301c0d1048121241810040110707120810f415000035156100c1c50080041c00b118000040c00360440340c3c881000f0030700c103032074002036400901100012103001c0301d1000049103905c0000c1510a1145080444000c181091841c06000d0900743c005022000d4100c02c016503054086500f100c0d25807005488034000c2c0c82c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 936879253 625 936878628 936878633
    0x5060a080109030905100521090c0a06080a0c180e060d1a010f151b020d0203031303060f0603 42
    0x56060085403502c44000750304101900891581c02b96040e429156210041c1000c0902900c1e22080418101145448210341c6150011010000d480206056442c00c00c0d1140341220320b540c5140c506900c407200010308503400807000420b003d501810340074000d070140d81c3c105d049402c0003105810065813030031420f8841c120070030428005080c840c0e4611142d14824000704c3c02a00141084602d28000d074042441c41d8080c00502c20a030005800403c03c20586d4050315500d0313988207134103000003403665 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 936879878 625 936879253 936879277
    0x1172a310509011d0c0c0a03020c040b180412030e1e01060506160605060a0801090309051005 42
    0x4107985040b884200c1c55141341c0c0c0e00c1c40404051849020300051300ca10948480e44d041c198042400000c0e55011101441803d0004003084503d848840d041c6018444500c0840d00080c80100e404680c003c890601146101e2103000e0030382413071890301d512601042d000070140b1040d0000c0c85400060030048580600f04810740305401c280410403039008140c00d5558000c1000341d03a030003c8120051600c0c10092000c80081d1800520080041c40313954025444140140045801a0243e0320001001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 936880503 625 936879878 936879899
    0x3050f070f02030c1f0f091203050c0c0105010306090201172a31050901 33
    0xc203020620075042003a150480c0d10550b801c00070740c603008034203081c1d01c0e1002d280d00d100e0030b41c5690b1004402c1e104401071411a0f0707404011207480d42d51240340600d541e40824051580d20700c0091480e068440440c0d00040d602002000f180da12071400500400e001c0710305a000031200301740c46103802c0c1c03c48601801107110f8203c03104000002800007000d142401d51001600c3e005004240e4606a180716000c800c0b800d4085110346a8480d1460266048681d8840340c820810000100000d4141c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 936881128 625 936880503 936880531
    0x11d0d170a0f021f0c030b1309060f0504051507230714070320220c020d0305 35
    0x10324406003080d101c803001720b2203a100e03401c50543d1410003020100c0781c210710f1002d00028030180904444250602500c05507049451203654400da4100b4040c0000f004050807450448400034020418010184003800300e00222480190724903403500700310f990340c00e0f040c01d0549259a00611811b04c641c0800c500380002481680c1c5400100d045c1d50914000c02050307030005408a61420901b40c005007400d03e0008003464036000b01e4024811502502c0341200c1d40070088003500c01c200c0c0c3d915000c0e0a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 936881753 625 936881128 936881173
    0x606090609040504021302040e0103051615140714150a0b011d0d170a0f02 34
    0x7001c100001032002500880e0b015a0780450540001864001350000700f15a103054280c540c07640c00c1a50502e0141217004103507030720310102448058102d4016088001c52490585c0b5a2203800700205140d101e400409030200c205d02144409050000540780c2003081030802c140d29648410040900751200c0d050002e003c202c8084103510031200a66966090240c018482884284142c4411452501e4003101510410001440c14065600f1240144e0690068402490140c00d0b9110320000c2004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 936882378 625 936881753 936881767
    0x80d1b03140315040e030415081302060901050f0d060609080706141303140109050606060906 42
    0x101c4040d40e07100c0d039440c1a4902040b40750711000380c101c1c2c2400d0403c1040440840108140da4082e4000e02d09080841411900c1900494001540310500554403015140c4031019007074107141494000d10b802c4880e0340000240d0050000b10203015120301c0b040c058103070049502009402000010a8900d10340f1900070f01d0b81d400442410014180080c180070a0b00722900710301c01441c0c01c078a514401c800c50b0038040e2f000f88500076050356980607038404a507003442d20344211054150010001402c0c102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 936883003 625 936882378 936882407
    0x180906050f03010c1b0c0e0f040b09030c1905030d150515070f170c07080d1b03 36
    0x1000360102072248110f042521447c2c454188a000da0020340d000b1b00342c2c49540702000b003000000300c05150032000d00c1c0c00560801e50049149030380c8045048440941c0890211041c08118040007610144a11180203008203100301d5442031040f0310610546204240402d0212405509034044524494001040e00c418000ca9210806144bd120341c1c44a5003220030884600d0040c8240824005040302d600980250016100020300c0301146000c01110050900c0d40742c0e00082d04130310b800c000d195 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 936883628 625 936883003 936883037
    0xf020c070e090d030b21030403050105060d0c0501030c0215011203270312180906050f03010c 42
    0x944142007241790715440520050004610b0302d464071120848401c035901d0300030b480101c49640c20480080c0c0da50038103110380d8450315804000c511040342010015405000301003500d5007103116803110082d0000b60b0540d454020f01c40045031344c0f0940054240200440c1c030428140550100c00306940071060300685101c0200c07604003006080e0105520404c440f844000101d024446401c000080782114459000d041256422070703440b50050007100525090740c812500d03407000310342d0001c59010020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 936884253 625 936883628 936883631
    0x14123c1005060706060e060f030d030902010905100909110a050412050c040f020c070e090d03 42
    0x2020304030000c90400c041001606688000052150a11607034000c40c2551501200b418115405418107210303811080c4080c50540f800601400e010041d40780100796400c49000507100c0c49070325003040750800ac10b941401340c5950800203600031101840c200304124456032852003414002d40c070601d030004100b0002000000e00741c01440180030700501c00e86041d10790520000d01200c2c214410005225004501e05507403842c1884990000c00e012032484203d4584400125182c0b00081aa0010315 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 936884878 625 936884253 936884371
    0xf03040e06150717250f03050f071401050a06060c11010c031412 30
    0x81c0c18410042d42e00030f803007000b0b01c25a07440080500140d000405440030000300f0242014108600d200340c503240303c90a42c0540511511100345022a10820041c0307440c10140350042e290003401e1352a0103070420b0220402c161039640c3c00c01d11186103043d004180041c8400c1c82e00a0744003486489109000001601c5241800303404421407003050b016800c002040c40440c800c0320380703c0782c24030103401400307208844032800400076006842584c070f154a4460802207401d501c00004540c0408052100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 936885503 625 936884878 936884899
    0x109050706230414030d030608211c1b090b0301181b09080f03040e06 32
    0x42e540d914803200545040e46900c034980055001c03042e03030780340203410041a0800744400c1e1040c0c2d40ba86010b100c1c131414484402e507503504e1b9050300d400141c3c030382030740d0507414003003000b900c1425451110500c0ba410280070780e40083e01c42007080004c24940c80307000f52081805240d2460072070310340074140c9045a04e0132214110820032140d40300203884d101c02c4183c0705003544104140c04030066843d01302c0800c0c24081200c1c60600660f00c21101c542c0108010302001d23405070000381d171080040303c0c2c02220307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 936886128 625 936885503 936885527
    0x4060f12020c0318031f0e03040504231b090f010e0604060e010206090109050706 37
    0x103220321404201a08128001c554984005480329200d500c8408120000b608030000440719041c00980911454066490301c54a000f620608001074000704907a1a094441407001244503516440303401b074540102d500e50346401c80e804000340032021000b403500a204d0b40048800c4080002c12045829464040340c9410700b4211100044e03921329450000c25805c00c01c0400c0100f82c03150025413000c09240b098080780c0403a81d4011115099910403200140a60080e08080003000c0c00b46107900c1d02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 936886753 625 936886128 936886157
    0x70309021201090309081c080a09141203010315020a0e09040c0f0e040b0a020a02030406 40
    0x2881e40c8030080e40450300b400f0344003216201c0d503501314403c1d1400720a503081003092183d105031b1811540c404120300c1d6200d1000c0350080309030900056051694608904640100c1a40300880d01800c8140b40320901c40c003001c4e504813802181c0b100351940045291000304d12a02461402041640502c0b03015410702020141e8800d11130b42c1107445507030b190001400707555010343c400c9003800702001c108070801c51000403442e080b0540c0001541440c2800708043e40f240036a0040e001008401c0081001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 936887378 625 936886753 936886759
    0x3051b09030d0e301203040c270e0705101707540e07030902 28
    0x185094160344500c240c08104d91000c441c80345071050b444031900c4001c039103102d25401562203492000780e0b40144050f07400c50b07040080103040000880f8142c0e04a4841f45100401228407055a0750740c40030842d284c0040381c041c04a490b19224a002011081c60180a24030185480040c0c035800a80404180000304070f807109000c6000419900d00c2c10550384108401e410003480d080300780390b0006c4040144540040101219070f0003e2040101d401c1190320311a103445130002500107002c0c80c20141d030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 936888003 625 936887378 936887389
    0x70804050a17130e04080301052b030c110102160b210703051b09030d0e 33
    0x110380c020307142c0120403001411001c090140010f1800800d0059008220003000c800c00900c07058901600c03881c620340414465107000d1809541114403100410346a480d80300c100040304c100c10405070800900c108000c1c84202c0d503203c900840c40503036600000700f0361402c51488640102a9041002a4040d90441a08581c0d50106501030080903041c02400900c80d0101c3d90f000100d5142c030051102c4c0700600c0c2001c0404429040040000c02d88001c074001c1968a01400d08091040115000c0b84 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 936888628 625 936888003 936888013
    0x10804110a0803090a0605071703060114031504050c0406021b0a08070602060108010b0405070807080405 47
    0x10040c0100410321460781d60b00160780b44e0b049024014825050401c0000fa01c60140d001c861286070300c100c514030a101d4001480c034140d000075107650304004d00e01075000c2180b29550002c50285003004459907490031020108400c3c1c40c3c006140000c0c0c0f517014032040009940018401401440d0401c1072a00d072000d03840841c2e0500e503113900180d00c40c4508440080c50395000700b009070599810400034020200b521045c071050700c9080c0c03061800121800c0c0082c040500ca05010b5421602c1803003510 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936889253 625 936888628 936888653
    0x813120201090204140f2208210a09050601060e280b0c031306030902010509010804 38
    0xb01503a5544928138150081c1c0740342d900d4070303e072400303c80500100007047c071950200c4a140e01e450710300e090311120710003035800610300b542d9a42904a608484070490170401a03481030344200403968000c4e4000030440c0c3d20580450781981d807103210a42d400c058858060b50081010701600c1340341c80364880138000866400c03100303211054481d152010107500040020100f0740c4000b90b1a03000002506500000341010b2900304a86052a40001c1052041c49100fa041003402c1000c54140704030440f146 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 936889878 625 936889253 936889271
    0x60609040f061401110703030f030216050105010308040f14060304112b0605070813120201 41
    0x14030301d80c036100340030460007088401c8655280c420b9984d1a02d04e5124000c281c0e03a81c80500001d0080b600c454411002c0621a03001081d90b070099050801c0d5503021070795100d00751102a042181c618501007800e10050b13511003d140001e0504001d907a40340b12a50010031010b100242c8094083ca0070a44060559110074619680e00340c2d541a0707a0310a51810855401080d401c684215080d604140220394410f11402a1138003810340212004000082555007213a03010784100c1e06400d65403512540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 936890503 625 936889878 936889901
    0xe19030c14030304030207180b06070204020912030a11070e0106080c030c040305120d2306060904 44
    0x140b07142c208582c22005644a0881448094280401c03a6451140420f0910030b4060317040201ea8035015160b8000e001e550040f403000c44550302c1042c012140d141d100200d9840341d201e420001c20300381c0c00c6151455903001c0c0100106502c10382d084c0e200d05031181d5484200f81c5490340d800080055000034044005524140008000a44244030040904120901640e00c5100d0300404e24100d400030b10840c0386443c50203100c40301c0310440441c44c0342c6c000c0007150810344880c20303c0003240140c018901d49 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 936891128 625 936890503 936890543
    0x61c20060a0c170c0703030215071d100201060b0d05040203190c0603020c120c0a0201030e19030c 44
    0x4d1784825906d18000b51795440b40040035541c0581c14010a00180c015041001c030041c140210f600070340545010302c034480c900361419004664030744100141c000c04280080284001c0c03100003094510b0580181440c0c2503500f25042c0c00e4124003010309002c14003880300c650548900d40780c05651000b80300100c510300340d0100000c5441040010f16110300001c009040c4800398400c0e201400140081511291030300c40c0c9284984110607a0160080000c0c03041001184040c0304907035105480c0c01c10131039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 936891753 625 936891128 936891133
    0x7020607030c12050316050910080603010b210705180103020405061c20060a0c170c 38
    0x200c00719843d00d0b201c00707407213040c03480f0f0b86a2111900c007924000c00c00c041c410025143d80e95030940c2c186980e03600b001280c036218140402c5c050120302030780c44c1d040505d64110407a0310380c01a80300c200c2510340009490725103803280d003040511626039800107207200f440710051025140130b501150708050010024110001c1040b60f10095028618054418240c00100b054221206c00f40e401183d642c2141c006203409000280686200704c01c5030040c222103143c0ca404080841d040088689200380d6504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 936892378 625 936891753 936891773
    0x60a0203090d03051903060314060601050f160b04030806031002090d020616020d0c17060c07020607030c 47
    0x80d90b00746c0c1a4072040c11640510546c540606400c0700389030301d43c9002e447d00ca0011704100300e440c500303808407001054616040d601d80c210303802e00d644480660781d400b0758049001416000601006207802c010901c07100c03040c064110301c0c0035200360000313109c1c0c031079403800a01a03031000c9040d00760404038440c40120160013a002119800007403400b512440c02a0003000d0002c10111204c60004200045035445200b591100c0c5213020000c3d020404540c0011030100c0401c01c034006900300003014960 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 936893003 625 936892378 936892417
    0xb010503010927050a0b010e190b12011d0712020607081602040513050705060a0203090d0305 42
    0x815144c41d089001a031003485244690300d0301410030041441d01c0c83c20400c0c503a0135260309020804107102d984070150a0316956203d0b80e100003c1c41600280421600c25240c15400c440c101042101c0e80300b0b00c54000741514002c00448081030300101158100320036501d6110b101d6101a9a603800d00f20803900305030059030755114490040c000514841d41050451902c4c3d81f5049490308864800e41c014044030303101d08d03400801c07560300c000e0543d180e542d81125403070700395035038015140550500307810080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 936893628 625 936893003 936893081
    0x140f12011406011404080a080d090f060c080105010e10140d0606020c0f0102010b0105030109 42
    0x2401da5000540e442400070f12180c02010200e1111015641626482c0e070103011803520f01d8070b0318125034018424120649a07284546030005d4104282180140c1c449c42c07003c180c8405841c07002c2d0247c14168005810710070700c40792a1402c0d5503030250302072001c2d00320b081c48804104403148403200381c0506a00701204074500344000c03801c6a000aa0900b041800300d980521302c1315842c004900365960585400d010410500041c0921803a9030005846038107034040c0000507541c107444114907214401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 936894253 625 936893628 936893651
    0x703051e06011b1103011a0d11010c08191409130225060b19140f1201 32
    0x100d005401300e000342003500303440c220324091b401400490f19240e903d03a5880d01c1081d003146d001412503550701007400141c580809000000d00081808101900407107001441044445059601c1d03c0130f0b000707008907241c2d01d800390300c41250300a11416003014120515500800c3c01d8007890049252461050803c2c240d80c2601d41012610320381c1725400101141030446110450407481c01f000034915007040d42caa0012180200300c1c034814424140780111f20b441e030914405ca080d450100078496402d401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 936894878 625 936894253 936894263
    0x21c181a09071a040302090c04050a120f0203060414010e06060f0f03010b0901060f080703051e06011b 46
    0x5000d003055034000caa1f4a42151500e041300400d80c481d80c03044c0760300210852020050340c0c03000081c02114030300034400e001e41d000483d4001303130a00c20304607412600380c40c25800c0800010404d104e9260402c60440c010403c03400c04000050000a8181d4401d00c9a410401c0c03001c0a6102900850b010103001780a00d80596100c00b00a05052003841c5150700043c00c2d1400220610700c20301415006015660864040300740010700c3d81010180100980d0500019120f540000304a6132700e4420468015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 936895503 625 936894878 936894929
    0x90e0708060a09151505070803041e0606080a050705090114120f01021c181a0907 37
    0x300c0e040085c0540340c01e690b10200780340d04141e42040c00507110b00399103200040c4000d00010210440a16a080410070b003100307140c10450400100751900c0f81241c2d0b840c0780000503282032040c2c000000d0030386007c28020303059070341400b105041c40302d0503002e0001c01d034000150802c241c040c540490854410902c0900741d04050503100610812003580320342c2c219213041001e061113401c4141000042006031170003010804243c4580a12660744200c00b505002d420741000346034003170781500701d280c50005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 936896128 625 936895503 936895541
    0x7030212130906080c011b0804121419120e01090506160503030c030a0606090e0708060a09 41
    0x344485c0d0114002c0d50700c000b1820074028041c15103d82c0a100c4070704160510a94061016040c901141c40601e000f0b210411007000308200c1500c07a41c0d01c04041c0f2600036134500b20f9241d25220800b2428803003030010708030f8640e800c00380b900705640065034010b89450700c80c0389010781d6414105011301640000070a11030400c401c81c008620440c01076809100707803583c3e4082142c0c214020b100300d110f445017150203d418907102d1000c0d181c0040000300b0108100d42c48403036550484c1c0e02401c403510344081c5c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 936896753 625 936896128 936896143
    0x180706030b060c03031f120b070c1a01180b040905060c0c030705070f15050703021213090608 42
    0x1b460490510309525000103002d510b54411840c0002d40104045401000a040021503500302d440e04855081062080b095000c0313001c4000a0f0305450088400039116002c0c905102003505142800120b80c7c0001010701194425000300340310404a00061844000c103109881c544140c41c0c460914190280e44070f03030507124191404110504001701070303d440c50101d10344075141c003c5d40e0320002e59603510001d980090f0040040c084a4199140c0c1f060f500a02c5198003c2c4840b0781c0d10301c011510340c41e5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 936897378 625 936896753 936896791
    0x2060726070b06010504030b06280f030b090303010f0308070f0803010b0909180706030b060c0303 44
    0x3201602c0c640e84640005682501542c03100501d089400d4002880505103e0b00000d0300e0511007800084007070b89060411031444c3c190308000036000e2040c41c20014400006c10140e04074007480003452071541400a810740c6e00c3c944e80009004040005011000c200c5504091001c25401003003035612561202d5009003140d000000340c9120716417250100b20688010f4034151118007a0707000030940b0514040d0203030050039102c60040e81c00103003400b064141ca01d050004502c5401c400505410600b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 936898003 625 936897378 936897383
    0xa181112010501231b2a040b0d0f030809031315090e0c070206072607 32
    0x2125089070514800641c0c4d11000714507129450b0720b140210880d2880950700c1c80d03500340e07644408011009160364503c0c54408840b86882a24030030440c5a80400d0045081c58003c8940c0d0070103030744000840d54084000101485681ca00700c0d08a4009040ca40c054041040070841d00d0030b20500a501170254080d8251512210302070242c0445400c0d441040c0600d00d20b400c01c501404400d0035140240e80680e1090303a10b0a007841c08841d1607040005541048103070500102001145401034041140b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 936898628 625 936898003 936898007
    0x3030406091406060904021e0618101b080f040b0c01050a1a0a181112010501 35
    0x810b11071070322290045030a03845014042c1002409543c0c6030204100e120501c168084841406c490076030b0a521b030540107040381c1061016900900080100b40400e0603850804842003103c13400c115882783c0003400398041c510727411018158860003400d113480b50f0b030321481c1c0c0060b00344080003c40070389498064008c07604c10400c034501003000400ca00442a07c5003540b10b1a02c0e4442921700041c00180002540058907003413509000511002525920142d03030b0040c1607480703041080740300400a079a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 936899253 625 936898628 936898643
    0x91e0905060301200702011103121b0309060a1a03010c210e0307060903110303040609 39
    0x28001c04040c0319a0410041001d80115050000480704e480c1e00242c1e030f0b41c0790600040c1c403c6500900895060b100001d258004001110711441c09806650081000300c5d003200450101c1740015107882400e0f82029001c64504146984031024021500304003c960504031800217003122022444100400c040c05058108180d45021b00820070028240820020829521003596802a000005d1010f80d0300c2d42184141809178441d001e540c0325140440e5901d140078903008000c1d10700e4410407104d00b07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 936899878 625 936899253 936899261
    0x1170402190e1008060c0f0c1203011205070b0f16030c060c0e040b0f03120a091e09 38
    0x42d04e8003852612058201d4544190f94020801e18201040c00303801845c81d4102c61041c0d4210703140310f4440c03103411752080e4041807041040601001c24420140540b41c001d04080d80380b1441d2000101802c4198010000d81807000080800e9403000d00d4011000305425651003602003040116056028055524407850301f40181d103005008a801d003841541500001d600034003c0c446800345185450381030340410041c404202c40e19a00083c02c2c9687c100203c06450300c2942540f080d82020092400c407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 936900503 625 936899878 936899911
    0x15070b0103140d05071211070b121b2a010c030506090c040501170402190e 34
    0x7a080d034010f1906801c0340400030032500a010004000070000d1081071107136803061400214081d8a507050742c070003542c1d41600a00c1a403000514900c3c0018040c0025610030b1129828005c189000c240186401d46034181e50001c680d41554101508400d42c4c0354611710300d801d110b00e440300402038900160600b070581c01c00025200043c0b44130064181080f0522981ccd900100c1031441c03a08080c4180441d80351440001c4a030b80001c1c012480e00490464001182d088507034074203000300c00e40ca605141d074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 936901128 625 936900503 936900533
    0x1b06090210091a04051f14070515060d0b04140a0b0f0103290c070215070b0103 36
    0x251503d004581c103e035030042803030385001000c0044854400c2c00c1c54a0200344010303001a205c013600350402602c3d80a01440150182c00c542c1050085040700003050a482400703500704050020380003d240c02d4015030420502030564007110b50041c80c00022002c05011280c045007006040c0802030b5415040c3da04c240282d0a82503442c04260344041c0a1800300014050f1401c00680b846560001a21182e4002492003d11480154805001f580021010b44a034541d4100620900c03007101950514 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 936901753 625 936901128 936901169
    0x20c0a210f140d1e051b0a080d02030411010905060f13080303010605130e071b0609021009 41
    0x25140d80302c08040e0098200d0300711ba595540b100303400718190003e03107415401c000c02ea03280940079030341c00a0b40d08115039041d40103501c25480f541e004002d00144400440722002103000341d5403c0781c0c0401c41c0c4000c800300080600500e5540804c13040c8000c1d1100380141c210780003a030180012400104840d45060021000503010340300c0c44503440400e00d001c82c03006124203604100b10b0a040c55628141042c032a560b080b41e034540e071b0050034218a0f580f06880c01000e001d050301c41c180f6441e207503027005481c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 936902378 625 936901753 936901787
    0x90509010e011b0c020a150e030f121c11040f0303020c0a210f140d 31
    0x2691403e004101442ca04507035503501c414055942000500d10040072550810b4540d135584450082c07a02059001414806101c030707403407c1c1042507603202c0428600078000d40d0040c10300c40f004c070b12a03016015003282d240e000c41d500e5500c01b9000003071101c15900e411900c035601c4070b412041414061000360018400d4415005803420b2501c41041a20780c8109070100049946d00c4588101007a124100e5414048400c5203011404000d84e51008000085c09405d0a0b0380746440227040d5a000c40710749503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 936903003 625 936902378 936902381
    0x6080f0f0d1805061303050303150f030f060f15090109061e050d03030f020f04090509010e01 42
    0x11a0b081d04a2030070b840400390103074034402c040102c1c0708074420240b4003a80d0081c690000c100c0360f9030b04010050150030400d041308207104d04282014085641800300d010174202c60307107070300601c00c40e15a01031100c04214002c01209510115407030780000e0b0782d9491a04c0e4000e1902c060300090a80c1804002c40c0c650908809d10302c0c000c0048213007040180c440c074444100254040c42c0004402d014218407801901c00c1428202a030100403c002c101c95042d42e204501a60514000300700450301e4120307450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 936903628 625 936903003 936903017
    0x6230405150306010c12031b0311160c171006140306010b030a06080f0f0d 34
    0x580d900a031081501001441007081d0715800505214140070105076044002865002c034260769884a54002c95183d21003d03210400380c800a002c10f040c075003060030300c00090000d4015901c0c02d140c1500d801c0743c1411b050902041c20791041c0c002d02c0d07020702001000c04d0b900c80001410445d04201200400c4410351b6011098841300305480e5039036054020200402000d1000400365401500051001541e5a900d504071858903041c2010b000c00c6411819518540d8002403040300599002c3c0d0802c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 936904253 625 936903628 936903637
    0x141c08040b2505130e091f06030803040b1315020c0d021c03020a020102070c0623 37
    0x14181d00c856482ca203401864509255540c0000d0300c00c1d180c2e940e1030791000f01c035162020148440b2000109140009111214105101c24030402d44801680d820f8400034003052030800109001c0b5180702d20a89d4000e00c03a868181d13116480399a401d2844002a0740003041c90b50205801151314024810b45880282901c0205000c0d0522f0380311082d80c0114600800134103900182692080d8000e4040c0d94010380c1014404c201e003076603070001400c003c0910060006002203007601d403200000500554 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 936904878 625 936904253 936904291
    0xc09030f010501080730081b0c12061608041b061806050a0c141c08040b 33
    0x41c056501c1b07070403030300d40305c0d668111107800700d20a50509041030b95003907604540016072110101c69900c10b02d50304001d41000407040518054090142c452031505420342e0b0201c0000c010003408011401e800a420b02c03040c00c040642c0a81c80620546030a5a15040144016071140071074000480400000a0503070050045903101100398072204100e00c401d4943d510b2150a00f205288107024044074441203030480301045500041c943c45e80915810b140c20060481d000007820040d40011451b410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 936905503 625 936904878 936904919
    0x812010801050f151c05010f06080a050c010804170d0b0108010515120c09030f0105010807 41
    0x1c03844180041c040d8044407100c8140d54040c0d510013100c992014101c1c0d110852002150900300d02074955420725801840c09d2050008915500241145080ea00708010305001d80c28100112401c040140050341d105421800b49802e4144000c000c01d1826a00b040018000c00f00e440050291041684024840d4291003411400b80000000719a201440b0a4001100d41c2d0b4070882d512007030280e50b4404d500b40c0300d00c1d4115200c00005512050680f0154000c03a64042e03620a0400344142c480b8021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 936906128 625 936905503 936905521
    0x6080f04051b030102070c08010203010f0b0f12181e0d0302040f090b010516081201080105 41
    0xc020b26002503120542c0c995040341903030340554003041500c0110750501c00e468014081300c4001a070725031425140c9207a0301216002394900f07260401040000d0040b41041e220024581c21b0031140701c2e203842c0b10001d007034819041c80b1003503800307910003584581844c00b40d0000010365002c01d880000d00048001c130204d00c9507004036845118040c0050040700302507400201c43c810181002c1c0d03e022588105482c0c8040440022206c0307180009540050381680011030b070040005400034411402c1c81404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 936906753 625 936906128 936906133
    0x2010204120b06150a0c350d0e1b0a29031306021306080f0405 29
    0x44035602d402182c03800079611204080390403003d000800780c541020100d0300ba0b000035484200c0e51450f0f405080c603880c0c20b00382558500d10000d00d4409008100b410b0b0048a0040c402001c090610704644150014036444a4044981004101e0015400d519030b1b0704216540d6140c24200312024000c07212180503190406130382c294030341d40c40043c00c401a20307000c40006d000c051000700e009000d0760f000109640b12000500d081441140c00d000d1765000c2081040050700f4440c1c050307c080e2042c0d401900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 936907378 625 936906753 936906779
    0x30c0201021e1c090f142706120c0d14070f050a030f05010f05180d02010204 35
    0x114070b101c48400a4980c020300134074011100d00da4a400e44030b920469a08076902081030030741c054181c1d1170441c9805124070891544000505081ca00c0741d00392074401001035000710050742d48202d035601c040c41405107064008200303e0100c40c050034844a08120454855220710491001150404006549600300c0d10003c0c2035820240c210366030740310716081d200804c5a41d90740b200c4020340328002c0c0740515841284040482d0b01504020107800c1c0c030b0034070350703203e0a0196441004140204298010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 936908003 625 936907378 936907393
    0x90c0d23070906090e01200f0409060308040e0c030f010314070e010e090f0313050402031012030c0201021e 48
    0x189050000010601080c448c840508880040800b003c041000959038606421190054421078001f0550240042c140003c8030048a208080d414021002ca07070a50386d8006500b41010303002c1d015840741d19408921000d10710310580c081d2088510509052914094841c540350b100382245840b40c100b80021030400d429451140b007030380c81c11100540c899031440200307a0042d509901001411030385c80400d000b03054010440340c2c800c034002ea082c0d50102506d02c40d2007400626285010200e91702006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 936908628 625 936908003 936908051
    0x30a0305070c0e010303050306040c0801060806120c06120f090c0d23070906090e01 38
    0x50554a81e8440c0d48220395041d40c19800141100d0301030300e03c81c0254000c6d101c040c0d40f4a801c100b00000ca07a91800c4d04818000c100c001840358550100741c6a5001c034080d103845117400c20a0912a02d4403184088080c0c0c0040f0025800c40408920703a20980515442201120b01e07490724480d440e26100301084540cac01c0004107a941c0003150f42001111140d2010115403031048140e0440d650410f01a43c100d02c0150361103900400416034548620340d120744401c0e00130003c07072800d142c140e50f00b030000300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 936909253 625 936908628 936908633
    0xb0f1909141b030a15020d06150e01050c1515360f060609010311130e06040b030a 37
    0x20784099900c00303c0c5c885101031b00c5041c4c0c503500700601c1d14101091003180c2400045600703500c0c1c1c3c0e4103014100100c0055540c1d100d40d8104030069030140344040564103e1410302075010f52110040c108004c820070200704030610341d81c019160a00400801240300e00c0000d800b010b540003004241102e4180444943c10741900501040c3c064180043d07801890b03400383e00a8071104d0102164580d481c0c00c3c6039004405200326000715200380d04408040760492a041c0161055640010003030009404541e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 936909878 625 936909253 936909263
    0x30509010804080403060504060b01090f03110d050c0a0f0e10030b0f1909141b030a 38
    0x2681a0b00501c2001d800b800d180d16501d54400700e48007210b040718078030395504200c40950707040740442000f000ac00030304901c000e04560b1141e090905245902c0c0c012506178004204001d000d20071010315000240c4546a056610511710184003a40c3c4200341d1101c0304400440c507100c8001000c40142c03904030500c4030164460500d20460071100611502e036400501080d0030020406016841c0094001d0301003018190800d0643d030304007901c07011075050103803440e1100c41c00c03a203002ca02c01c05116002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 936910503 625 936909878 936909887
    0x81c0e1818120901302702031c09030803040819030507170a06030803190b01050703050901 41
    0x844c07040703414035080841c00c011010281e14010b43c038884504500a0442407001d20341041c012800c95103522141c140908401f41d00501508280b4445c104003040c03000c84005040400c0540303103002000c030340b10318000c500540c002ea05080e950f01078030070013050b607280c848901402c2504c1c010401844540c0300b0300c014002d50603030021224507102d28140e02c005c1c1126420281544500106004c2020308070502d210408190400a00a1a64085c015100750041201c05004900e08111038003c2e50f116 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 936911128 625 936910503 936910517
    0x3041a2a0909162c03060604140c0a030b03161e081c0e1818120901 31
    0x2514040030018a107190446140410301c5261340f4580c014211004080c90000305410300300020b0003540210700d0702d105072540c0c64128140da80c028400007862965980c400d03004070080c2180091041d01440740c030b158941700c080c2001041c001c8641c0d020030308500c0b5145a1041801c00d14620800e0601d40c0002080c00140000780d0b2290702c8413666080000c141c6141d0300208518010400c0143e0340001a88e041100311420b00001403600e2901001410748041c85e0750540050740101c4a2032030400800b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 936911753 625 936911128 936911161
    0x50618010c06110c1b0405100e06010c0605044403041a2a0909 29
    0x2925000000d005080c1112034030410100c1c40d41001000091500c80003005084c917030506a0030a8240003ca85080d100550401c0c1c0091081c882200c20b00c040d40e81003201894045501d03800d64895400329a8291011a014203d6501d2007580540c801d03056107182c4000b048040b2030703801c240303a03010b13401c0300782d08840482c0c613000b100250611140c0600e107184a81106401482c40c07822440302c0541c0130000d903002180b150f0412900d070000300340d401170b6094424098080e052079151001d801411042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 936912378 625 936911753 936911777
    0x30806180f010b1b0111040f0621050a0e1501031101020304081011130f060905061801 39
    0x152160131000d50f03000003601d8250756030101d104100040c001014800401c107000104081c0c01c450420f00c2e444104644581c403112940d03007856400a54800106a442c01c1036041087c441c0b02074421103840e198569010050b98000303100131141100403d182c02c1c03803540040140d80844030020040d20060f100f1543c0c00018020002084c040d840741002140452074040480c8005011503c400c070b0030650a000c005000c410003034010320720880042c03051000201800000b16100c6030286445064101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 936913003 625 936912378 936912397
    0x3062d05010f1b08030108060903071709060d060b0a020f0f0a060b0319030806180f010b 40
    0x25022075010710358042d1580303000c8100307013051480d0f41c0c03081c0300c0d11009100d40030000b1407485022040d1105690302c400101001581801c12041940240c00d031140d00c40301c00c0005c0c5a20861a2040381d0003001c501d88500e480d82201c25019081440403141240b0030b40201c03000d409482c2d00460200003059101c07000045003420000071074a00f1502d03641612485170706400000c117240e0010703141442110200d84003141e56070b0701041e0005156082d6145016040440010701000801c0c1b80a0f146406 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 936913628 625 936913003 936913007
    0x31b021b040e120a02060f010911090609040f180308011703030106140906040603062d05010f 42
    0x30f52001404610320302802014143c1c0b640e07020300558101000c4a0302d000c0d00c1a8130034410a4245040400f0700308002e4200d03050110101c4005c0e540701d481c2c1002c2400342c82d029a031360400c1ca01d04a45103e48030082c4201080040c480d559140c1d49a80b80d00041c03001900c0400c501c1d880b94010700c014003000307008011004400400c942c8040c28200341c1800a04250f21582100000913281c480402c10603402001c1c0d050b42c40240c5030642d00b10503a5005003d44080c00e845100d0410a5000c00c0050b0b541c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 936914253 625 936913628 936913633
    0x100f06030c03060f050a020703021e010f14040c290d1b031b021b040e 32
    0x5555040201404018030707000050002c15045081c036503060b0441000203031a01e40c035030000c91042e24802000340e00210b100e84100c680510805911944940c004260003c00e001c0100445080d245d040c980d903a135010a01c0140301050024101902c4030310322406441d81841540901c601402c4000441010001543e070030300281a081520300880f000c140c4088441c0124010b000303040d130103c9481030f61300001c411301c00240c070000b03d00801a51076142200315507006414403014211400061b81c891 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 936914878 625 936914253 936914261
    0x4150c0509130911090c0f160c210620070c03111f1d040903020c0a09020a02100f 37
    0x100c040b11408503921007880d094110230140000410021041c50354001084896518480d201d10588d0744d0141c807620300c000604582d0340b0204000d40c00040c02c005001450019001d035120092850000700100340c500050351254050000204076203030880c946140d0341740050a8000c40350141c441a107840d1100c400f40c20007216609215415900d513485200941c9010764001d024100303080303052200c800200d4018007500d5004110829885800154000003a0020400000c2d81030a6000b190020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 936915503 625 936914878 936914887
    0x608071203210606230a0206010e180d0e180105010e0415030c14010f030507050d0504150c0509130911090c 48
    0x3649003003039954560000c1c1c005006001c001c0381c23760080c5500c5403800c3d41481c3c590b88240c1a5181619000c661a14100502004007460071020080010000f0b020010884c0609203400a001001c03d01d84410b0000b4001018032022024039130030f26050030203005500b0b4014050300c4020f2001d400c00502941c4a0034644203c060017040e01030140d00e0301900c00c08055006004003000d00090f11003000701030502e01801c08554000001910b645842000c8524600d0240e040700d80000850001500780f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 936916128 625 936915503 936915541
    0x30c02030909040b15060f090d1a0c0d0608071203210606230a0206010e 33
    0x16114948080c0c443c41c8501121030044c41c1041c0c2c1d500000c101111218025542405540040c0010030101c80c00704100321560340302c0389910329104800403004a0f81c0076814070f80e0014403070b50000010260468070182e800610880fa120406d2035900c080c80e20540c3e500c5090800400e0220303009074945070207100d0000140c11103030f00f455020002d8410a5200d400007446141400d44501100003010642500b05840507203094605a0002c5d0b880303d044c0114051200d0800202d80c0c82c03480b101341c00d116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 936916753 625 936916128 936916147
    0xb0901140909100608010609080a2010030605040b06070f03080907080304090f0b040501060906030c0203 47
    0x4036840d00c0a204034080725280000c2552416120440d1690300c515082e08c2c0e07031507284180580d0354000c81d00c440010f010310882d04c0421000c03081507100300d00c5110004002400810314200040d50303960b02002340d0b10741030003480542681614190300e4040c103510380f800e1010080c1c402409102c0c480004c05e111000c01c100e000020702076003094076111922003514002501c0011520101035040c018914080d00d045d200c0d4074101c030115115440103500c1c00c201030700a0010742d1040d00c03d600061100301c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 936917378 625 936916753 936916759
    0x7170601210203070f080c0f06030711100525030c020607110f03030f0406150b09011409 40
    0x1c0442c1170b00821840c00303041d8020001444100300c0810601e00c162540d0f50360446900100e01c444c000503206505001504404000d002820070240e8071103c56000b003486981841200c035000c04070240702c0c1d018001080d08140a84500034010380603200c0d4264005d01541d6600f26003159070701d01d039a907140581e001e100b9101d960448100041c5008080c1a01c0205d042c0c02c0c289003140c104d5450602145050300111010010203180c3d800f52002d0380002c0c00c001d00013940180d0385404520414001e00d034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 936918003 625 936917378 936917383
    0x108091006171b010504051002010b030604060f0f05070e130e19020307170601210203 39
    0x1500d600d82c0380400724200408000c440c0361158070956080d50100704411014080107030b44142c2031a03e480d042001c80707051351180074255541c0f01d50001c910740342800103500c07880c02010081207804032612814101c40d01d1800c05050f040c905000c0c0b208213907003c0c0844842501c12180c541400306900e001d48001c1c40c800c1c0c4a100c05100d182c0038250010001c0c021a98a54000c5058820103960b41c242d19008480c003001444064100e030006010072030300c0210001080030200510b00804a03590702003807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 936918628 625 936918003 936918011
    0x109050414010806130c03060911041805300d0e2506080c030601080910 33
    0x1544401400740e8003a40d810410386901e803040043c20f403401c1d1490007031420081414040c0303e0040d2900800d02188030303450f0782800c6104032408a030b5070350024135000d4440882d00c00f00c21040e4505108070207030b850404c40d19448083c402070b005c40c61071001e020b1b401d03241c1c83e0b001c06600408060000c04008645c00071400c00c40c0307050240c4c114038819607a00c0c841841c00020114150345c400740680f400e10f540c050500c18004a81408000e1106040c01070341e4020808400d410040c6642050304608144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 936919253 625 936918628 936918641
    0x906030b1f141305180f0406180503070506180307020d02090403051e07020307060c030f0e01090504 45
    0x110b40c3c1c0d80380c01590444406a4014141041c880854005040103d034541d0a56102c44003090000c1c00c986d00002d10f0480c030401048104c0000d5a9103070071030303200880030f540030340c85081072010541c01800281e01e2610a01d005601d000c4256020500400781074a0107445512a0305c001003c1c1402082164541e050030101d100b283e815480550035240c01002e802c0e4060320540d05c020441e14007682403251807a8041d01c61340500744984804030740340580031105904010326543d0014030307500c8030302640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 936919878 625 936919253 936919267
    0x312080a05060a030c060f1101050702012a2003070506041113050606090f010c0506040f02010906030b1f14 48
    0x20050351600e50321b60351111171500c100c0700c0ca0140d070040420b600b810103004fc659a85d080340320303609a00c0c00a620607600820010f685c01c05800c141512018186482c000d0905502c01c0a05800b4400b51000000b19944500c0383d58450b020103003c80b03160180490401000c200c50500b1a0705100400703080e900451010014140708520552191024030414000500002c4481d4000c504150610703000c0103558503031170102d80544100804c0041c2c4012400703019500f0380c0c207810040e0741110002c40c8407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 936920503 625 936919878 936919891
    0x1e04080f13060e01050f07020f0310021b12030402010c1202070312080a05060a030c060f110105 43
    0x9241e440040c85040300143c4606100708440d0321503002c9443c0c07072080c0da41d200e040c1507090f020800d44091b0000300b00d13410b10640d024001100910f0018107030200400600c28a0802c070a15001c2c20440d5040c44241441c404004220060f0303002030043c0d01242e0800c62072408041c032400709074541001c40d040030300000401c109100b02190300906603841400003a03014005505d5000901107030f83c01500000303203200307900b0740c05220003403007aa0405d003000b02c2450003001441418009508507041070b00e01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 936921128 625 936920503 936920527
    0x1b030e370c080d120501080c1302040b0a02011b1106011712030c0901080603061e04080f 40
    0xb8405805000c4005204085460350040d1307003403400004220502c0009594030703a0b410b09441e9003007034121044c00c0c0b070024050b592284070444000902045020303410360081c01d100e080a1000c1c84e5200da00307101202c5113010f003010603c855009500601104585031303551900903020038200c40045061b00e20320441b9030000d80d441015444040f0780c960f1a0360b04502096803061055009126074130b041600030100c10706035000301256030b03100c3c0c0120f81882104012a20240b8402558654035160b540c91 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 936921753 625 936921128 936921133
    0x120f13150c1209031d18012306130e1305011b030e370c08 27
    0x48907050480342c8880d081042080c01d10420f8941d906006008201c03022201603000d15002807040c503110006000c20b902000048195132180c40a030400202c00b44100c44440b8041c4000b217a400302c9a00803540f15083c01282d02041442105a0046440c600c0308440420350144480c000d205000d90f100000340301e040c0034822032800b044194005803000908000b040c2c05581341c080ac0e0f200083c25103001c841e406d44e4540100d5200d81500740c40a4030108510004000401c0300849440301801c100e402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 936922378 625 936921753 936921761
    0x1104151d271207060c0824010509010e030a0f02120c0906040e0a02040f05060a05010203120f1315 44
    0x5d01341642c0c001010962120035961860029941017022140051040d4100e0703060000200710f5210320391041140d01d54204e806401c83d16420f100307050a400f42250b50b2000c82c8503081c0d07ca5580c0b6881c4012584601c41c0d18007400300045911140304001c0541a0784103e01c0c90352049228080240e03031540144803800c03182d0000000c3d03604141080c0845200150001c90541d0300030082c08062080c0215003d51002c12140034190507100c000304241340c1c0100c084c01500f83d2001d62101362080341c203580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 936923003 625 936922378 936922391
    0x90902032109010216060c0602180d120806011e0c1104151d27120706 32
    0x201c02e006015994803070450000541030001968481c7da641c40c440170031a81c070b0000a600010559a001c036482081d40c003a41d0780c0d201100e071064800c80c5110743e64004400d014100b45800f900031418820b95001c1100310890540341480144881e00d800e01c0c1e10741640c01c1044818101c1b0390042d4015090001c81e81460039025205403c907600400c1b2125070b20001200c051036001c05607940c2c8407416400700b0b00c0d101404120f0610603070752190801e0f11701100d061000d50784541e12004080320103588a15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 936923628 625 936923003 936923017
    0x150d0f0b03070b0408030304060216080c030a0206060907020d03050709080f1501050108060a0909020321 47
    0x5152400610380c10480f50614100400e1040d0341c00042960b50190307001d100903940c0c405007084050794000d44200200111400304946400380700c040702412902e88203908644c0c03181d03130300820803001368000c1d641d00015800c00d451440e02103200750015640440c1c03a0030003402c1155030b401e1051800c0c245580c4020943c01c059541240c54112001d0a0300401091804410703d003450800540720003a240310704201959900048011501c090151412091101d00541d9031075070500d07201d00c03e07036010034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 936924253 625 936923628 936923651
    0x42916080414010813030f20070e0a360212030c12040e0402150d0f 31
    0x80d41c0002e8080c100c00464940c1000c035902414030052403500380000e07010752101102001c00741060351880440c92100300410700002610a11907000e4030b801c000c4200048102c54103c807104205000480f0080801c180307034030901200c0d04a021b03d20101e800c030344e0031500d4102102031b40204541510025590340668903082350248050600440420301516000300c8110b600b00c8580c8400900166550b800700a51202c07071610300c48059400300002d022052a910a1101450714234400141e450140ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 936924878 625 936924253 936924269
    0xb0a060e040e1204050607110a0e09010c0801030819031404081e0429160804 35
    0x18011442c0c1101c1d0040c81c102c0d010619407001805a801080d02641c2e02040090034020541020000c4000c040e0010048546a2544040c000b0341200c8009540d03007464022030509224103c014101c903007010005d4140070020414180503c42c08000700c0825071036030300400d2162050050980601d2044d6032407540e52698805881d1150310400d4050807010051000708000561000c0e031400070f807403003200850900701c0e010f001d20b12400707800b2402884038488014402003000300b03002401030314401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 936925503 625 936924878 936924881
    0xf020301081e0601061101090b040f140106060e0d0215130306050a180201030e010b0a060e04 42
    0x600e0311890034010b0310b090544074895400422041c2d1901e4401d40c0c1e001010110780c205552501320100c040349802800c24003941c41144c031243c050525040107104036448940054060341084c000f00856613020313821401d040b0003105c198654202c980700054a102031100300035940b40c4040340d030004c1d04c005400f20070222400350200f03200503a00c8200017000c0300c506001e6000d0074600140c5400c0075510a900c92a01010701100010303408940c0800034150705019884000000c4148108480c5400c20703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 936926128 625 936925503 936925513
    0xc0c071715040b0f1008011b02010b15090910080a030c200904170d0f02030108 36
    0x404451070514000000d000100d08900c2c05aa486000890514010f407140c121440c5501100d0b404a0b050303528060500e64000400f511100ca0b18a86900030300c40707103020104100e15040c14188400c2c0115081150b00e0031400c245c4840f41e8000c1d00d02c0500840a9076418420b410480c0760038003200014041a94101008200680000d060b008502c14400c40702c1c0450114690000c01340c4040d10384002110b80301000310a50301141d4944168280c1031100070319090a0a021390004e0240800600507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 936926753 625 936926128 936926143
    0x506040c0609060302070b07050a17160e030a02030703021207150306061e02060c030c0c0717 42
    0x41d0019401d1b4441d04900404204031440000c040e188242d001e0220045a032410805011503842480302140c03050724190169a5248807000c1d107140c2241c11070580d428180c0203030030084e1482e000262200344611000e40205500400740c114000c0900050000d40b031181d08004100c01c003502e000b401048a8010710700400c000851400441c44030822820800301140c0c010700742a6038807100540284c1028000c0d0781d01903010b11007141c0380c40050003090082c000718400b805101d801c002405180104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 936927378 625 936926753 936926759
    0x20a1520031608010b0d1d030a050d0f11070b070207030c32030d1b0506040c0609 37
    0x14a0042495414400300c894544510411b08070101d450304040c40d1003640640707121140342e4031102160b6a51289000c058015040040d074002101c0c40c202c0c4a5100440c9405201590703141d5041107403070b05550390784101070701c40d01404070000c500c030b45207021000407220f610325030182141002c04034040442d031360304102d84212a9440c980051040c1443c06481d1070002c1d03068494140b43c184465604a001c1c0e0051b661103228002502c14404c80b0144410301021024001c140c5881e0b554010036161 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 936928003 625 936927378 936927421
    0xa060501031e080328060e1e070203070f0206040e160908010606020a152003 35
    0x20001d003020010f410000f801e00c0c45d2500c04142c07280c03a6580341100b034080c03000f0403004071030107031442207a0080046107850032582c0780c40f0380c03450150381c0418010792941d2160001c1c06a80b40e0300000381c90840b40e11072010400c02c03440e400000e0f0070b800740360301c203030011142401000300c2059441c03951184903103103444001506884042460a88955000e60b90060b808030203102d0124090517411080341e1403400c0e0006041600b400400100002a45501700c606400014401c1d84000702007015081d08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 936928628 625 936928003 936928043
    0x2100b042f0904020d020306010207060f080103150b03100e060a11040311040e0a06050103 41
    0x703024240140100300e40140c4004042191504281c40141d0714464003921444401941c05480050b07080000c026541c06103006550aa003190041915400203464001d4500c6030803020a000c0c0004100003000450690540320f0098408121580d034000481c1c64021040220200c941d00c0f1a0b060000c0441040b08a81c0844003074005d00082110301440c032564441d600001d088003241c403440d0034842d1242e030040c2540c950b12001300c80683c03400381481e000804003808100d502c9442c03040b1b6424000303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 936929253 625 936928628 936928631
    0x403270303020606150706020a090303090b040302030c13020c0604030329030706050a1e02100b04 44
    0x1424800507016801140c00a03c0600d89074020b504140015100b56040140a844081c00c07030300300740400030104503020f80078814584c10654220082c07240c18111881c0c80d055038007007500c42124804060240030400c0d0a0301c8045070b00c3c0c060343c4c038064201007141c6039440c0c80c1c10002e015081c120498017503040c44108000ca91101c10001500d415000ba00901f507541c50000700300c5269000290721010043c4c4135081110308041600e0001d4149500d90040006180d4220b50038200e50010101a07c511b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 936929878 625 936929253 936929327
    0x30f1103070f170309120a210f03090c031b0609050402040e0f100504050403 35
    0x80c10505004904a92030080901c400d98500d04641d05440c200115401d83d100100441c6c0080c01400d5455a0b404494500320780c1009000c0d56032402074502c910f11002d41103640c40c0c003603041814000880c014401500305882d009910140040415040c00149d4130804040001060441c24444003400f1a01d660380030502491041004100001d000801182c010f0800c44101040e516500c1e100c9204c6407098005941c450700d000d041c07000f015007051003041044159601c00c3d41010001c5c008001e15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 936930503 625 936929878 936929893
    0xb0d0609060917090619050405030f060402041125080c010204061115041e1704030f1103 40
    0x1240140c50300c6d15055500410300310100380300100f41d0410004005c0410075480520030504460011401041d0f103042520400040e5480340480420301b130003d011000c0c10120454403490950101512020400341c58248a074a5114901a40c41c0a41c0001800181c03982e11040c1440c02c0210f0006403544035010381c282902c450020384003c0c1c9843c903210f540440300d0b00c044891106644c403e03a002a5142d4201c040100e96803c503520a40702e90511540c4c000c00d21086e44100b61901030110081c0008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 936931128 625 936930503 936930517
    0x7020433061112190210020c010c03050c091e0409050a0c050a170d030b0d0609060917 39
    0x15800b800312030010300c10044c0303449034101c0e0010036132503c074205000c15042030010800d01114841540201c0f9140319540d82400030785c85074903444105110b42000360b500030404049252608003545c610034032104001d0800900d035005e41e161642014503008080342c061030a40410042407400108031000342c4140c001c3d5107031070403e144c80640e0b00c0ca2140804400e042d04c03002030400503580e98044a900a801510a02001c8498684040140007038281240c040350402061111040742c0f0003503480e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 936931753 625 936931128 936931153
    0x318010b030a020d021c0f110112060e070f030b09090d02071406070204330611 36
    0x826242c3c074000501d800c94041284040403441b02c1c13001801526003141e84c0d00010815a0130f160b01c400b003d032440d42d0000040300060b940e01814040341e0f26010441055440082c03441d004c1085448110105c0381c400e03004005292401442c0400d079081c5044000d441c1c05d4561001d80145c41106400500d02d03000003074049000c040140340d281440615020f200252600260341d0000c80d08180a0b6080556334181840f5a00c0480c4800c19185083c00f01c0540050140c032540400c9074010509542c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 936932378 625 936931753 936931759
    0x5340f0b1608130c0521071e050918010204150f02010b0109030308060a08030318010b030a02 42
    0x3100020b00186030350703c1d081c84420910a54100d4800901006894032030520715010b1b1102d00850540d00f100344074030480030001405805810410424210480d20000040c0f61004104403000c1c09841c200c03201180380c1c010181d0392000d10007400140040b00b9000c070f4203910844050508101441010150b9043c4050107665070703407214950007900d80c581401081ca407070b00310209841d0380d41c1e5080b1040f6844004140204070030300e41c4013200441c000d20001d002102406003455150040c100000350 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 936933003 625 936932378 936932387
    0x90e060f06010c0809030d17070c0b0a0e01110a0807030f0c05340f0b16 33
    0x115194040111182c0f6542e02d001d43c2c0c1e07a4400c00c040142e45c1c0303081004010305c807180d0b9518446415900ca102c10b81800203403600c000c12405a00c42004034010080b03481d00807085c000d0000d070502d4001c07556400b40a6030855044d1700f40000c100500240d810a4909215000a41e001c0090009410050045a208840c1d03200084c0b000e0140c0d80ca11001021035410100014118500320710510100803548545007104440200c21100030404100400d1513503908001220b45c5000d648018000080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 936933628 625 936933003 936933031
    0x506010b0315131503060617030c072d03150b0405040c05010f020a1407090e06 36
    0x8040b02d0584565241c03060300182c0340014528070100d0600059030b0000001482030580003101580c86032464a003c140d002d41c00a13550344200402407001d504101010800d05400c0307a0b207200c040400309505010182440000b0400c0d00d640c0e00112001090305180c51103404d16882080180c01c0191400c00142c20b10780c50300159603400e48142c504008001142044a600c244140f20f0740070b5101e103042a1aa10108000b901c40020f80204040a890020030781120200042c0d41805440d030460492 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 936934253 625 936933628 936933661
    0xe0307052d2b03030e060702030c01060f0501140307050c03120114150f090402250506010b03 42
    0x1d08204030300c49241d1490b003e031030301183d82d82070440c44905001040d54100096440003035061400102030041c5401003014204813180c1500c1d0100180124000121314074605a000000440b054060380903120556091b000b00c039110003604501d611814003e000341c800c1c05000107c800c0903464802c01042d0507203500000141460104400c440d810b800c00302c101c99003c1e40a20a15462000503400c0004086c0d0311451220034042070308059085c04010b80040540071010410481c01405004004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 936934878 625 936934253 936934309
    0x3121e0e0306060d020402130f090507034107051e090a05010e0307052d 33
    0x5104032420704c2040110364603541111003010703228902d02c1c1c040d583c0700c00407101040d42e445040e401c3d0b03040c800011200c9129106002d820458540c44140c100c4040240d040c0a1880510461031490142d40202402007004252446401641c3c0e8580e41c0c0c5030900500c051150000061404060027030029034101c0d61015044003c0d100c0a1900c03010a4200f4800640f074000760380d00031364110740c000102c1414056900c1d0307010070405400c000c1c200408860310038011980e00298561600b558908154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 936935503 625 936934878 936934891
    0x100510080f0d0e030a0512030a0606081012020105040314070f06020307030e041503121e0e0306 43
    0x3848900d200e0f020303142c1c14041c0c0b203146000b2a005224600c10700070000c01d681d0361792504184200440d00141c012500704411902000500d02520718154203031000701405503014240c03440100c92504c22500020640b403410b051800380d80000091003019209140711300e4107441d448100c01c90303580c060703d6800b800042007511400341c0750500381d00081281510703581c5902d5241d01d03620741c00b500c40403001e04100090f0583c1100c8110001c0720424144507105483d00a003107054500c0083c0e40c8800184c0342 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 936936128 625 936935503 936935507
    0x7060e060903030714010c08090a030f0c150c02213108100510080f0d 32
    0x303596401d44240000d0941c420400020844205240f5407010000150b000004089031912854010b0b1a0382110355a21980c40300002e0000b1817041c080d02040344110074091025200b0201500034020a00311102554007481c0b00d5030060344040c1d1a06042c0c1d012150b180d1440030605c10310b81c41c11a801e51803200a0b210a0780d0807802c807070f1503903001100b46d000110200c002e00c1030030250b88020011a040501a00041e150143c805404c090702045040001c41c0c4002140d2008004000d00740c441141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 936936753 625 936936128 936936139
    0x21015030206090d14071706010b0708031f0b071502070b0112051609091407060e 37
    0xe0f260001025042040e0800282da660701c5400340364005440682c08250104211000c0300e48520a4144440107030451b94581031040b100e501803564014245980440041e00e00c00d091148424441c0da280740720703918035580340604a80c0d540092000d480800e1740324412643e8000d00d0085914690344503010840b41d07840d200294841d030307c0002044845001d0421305210305900210b08101801c1e60740381c000342c003980b640392031418207212050120490300003030004c103c010380200c0604195202606c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 936937378 625 936936753 936936757
    0x807080a0b010c0b133e10080402031903181d04062403030c03021015030206 35
    0x805e1402d00d040040900302d66028524030010f01e10a6080e0920318121003582000c800c2071102800070b0307100c44081941c4020003500d5050303000e464801c215440140500240c1e0107024000107524a012241101752855020351200403400025411b1243ea282d0345520074114801d00c02c66031040d010030202c5507600250881e04c08118401d41c3c0c546520305800b140d0b1f100d04403030000c0f040001015048114400114043c2d025650360184000d010f2040d80d520001d10440c1c0203060405100600d08400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 936938003 625 936937378 936937381
    0xf12050304090b06070b0c030105130905100b0111010509010c080105011404090c0905100807080a0b010c0b 48
    0x2044d0400810b0080340c00188844a1180c080d0410207080785c0c4940c100001e0050241c0c40d01c8800e06064104506400412004a01000c081c01101c0b408207078a494000181e49005040c4018180c41d0b180c0130030014507d9066018102c1103201355104c1d421646d0300c000440b01c07102c000200303030440345040004005018090b0700280c5032403040d081940885944100140c4101040c480340070100300d00300100194143e22042aa07400a082c0c0410010940c036000001e080c0109030320000c00100c415070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 936938628 625 936938003 936938021
    0x30a050417101401051914120111030c040509070f020d05090f03070e010f1205030409 39
    0x1c0da030304141c040d0441d282d040d49407000c44229039440308a96412174005941112171780e0007592690401210f41d020301843e14001c01000001070070054500c0314040f41c000e000240756103031000320514640c001d0300c0c480c2e2007103800b1030107100c180303042c00990350002001d00302015035002c0303200040e4030b41d50001035075418400e02060f102001d40b6503102d407103410075000b0103a42c480c548030100d61607c52000c0c02000480325000c0c0002c581d8840c501d10058107a03800c00011070400d03290503026005001211 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 936939253 625 936938628 936938669
    0x806070801060f03020c070314210309030f030405010b0607140610061d010e06041511030a0504 43
    0xf10ba01787c81d0b881d141c00c000d10b80c50100c81c01d01a0001ca07031500c003a45034050714130346170150711011170f203140340c540007058981c0035130030300000305d020b0000108040c08000d4100f02942d40005107802c1d500c00c070070b00d011030842c0600d2445584a014a800003441c070140105420101d0303103203485032003808180310b06502e04841d04810035414048000400b010a4076440040d10181052110a00d50348420400142c4070030702420131610643d10070040c0c5400141c0c040103540481d8881d952000801540c42d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 936939878 625 936939253 936939277
    0x1140310050919020318010b010f140a090b0307030b0f0a0b0904090201110a0506010806070801060f0302 47
    0x6402c01e07a0303c640c40043d566403d00015058121707001c00001e014a5192220000701c5600c110250382c10000d0907528503283e032808032001d04565002d41030140c1840300b008c0e0000344502803003000d948501010380300091180d59900034015181c00081215110b920142014004120b06006648180a041d54001080d2026200584c0d8420981040c110716114403200394040280c00500c450603217000e481590342d1612004802d451a00080c090840030840185015451a203c0c2d4080c024003102c1c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 936940503 625 936939878 936939901
    0x1c050d11032b063c0815011409100b16150b011403100509 27
    0x1080c0d00800b1089000c60250540040201101681e07186006040c3c840641008000710202c450b000d003080303c0000841d02010312001042c0c000070307440b83c565807840d06551041050307006a00c0c1046143c04d00c0100c00c0d0513200380610b800f0583c00c8650034845c00fa4012100415100c0409000340603080e601806002a4240c1001081e60a411941e945400c56a025600c181c1d1503194078110580d5a00401c051032814140012a402c528002075000807800042c46418002c030104800b04d490980c55 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 936941128 625 936940503 936940507
    0xb09090129180a080102091f020a0b0408030103050c150f0a030f020409020403021c050d1103 42
    0x41030308030100c110200342c0c0b882c1c2007078220031490109411034040030800da0ba805064242c1c012000065440240103880c0400702d0009110b0041110140c4152110b181288d980e04109040540d003e84032160080018020032104000f0307512555011203036140a030700703e010f02a102c1d00c100039100080b8040441d1844030503001c0c0d003003419083e03200b000541d01d0701d85696403000290004d21069203c0e44108041d48008500b10301d150bc5c0158005001c1c0003420600d000944038403034000d43d1840740f4441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 936941753 625 936941128 936941189
    0xb190c0809012001060e040b1f09050403020a0b040302030a181a0d06051011070b090901 40
    0xf80e10640d00716a160b07400800c0d000d14620420040c440501d18681d40462002d00044d1894840c44c041050480c1e0740c00741000d1107a0b14030205041c11302c2009040d203002d5200000d41e80ea8106410060f40d2a0001c8410500090b54000030140210a0886000444050074981a40c0c20340c80c039540c1c031881d08030121a10b8210759440c3c0c002002d640d4500168a6035510b07031180c82d0940780c460b2480e42408020b41000302e171040c0030803d00ca400d4441040d43c2d07044580c0704441c0b02c44c1186d4007542090300d450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 936942378 625 936941753 936941807
    0x40e0a060c140412051218060f07020405130501060b040503100b190b190c080901 37
    0x542d210302c2d103895072115401c1450310b80c031000b203410b03029a04500095041a105440c2010043c00116032150007101c1400b0061b0f004e4003c04150003c03d0000c10016903c9008042c030403002c42d0884041440c5a161050a540c845d1b000b400340440144000d011984000403680320341100c198010030741a5410012403002030f018034a0510101d5518008500c800c0310000400c4201995007070103400d80c0b42c06004503807000702c046006080b06802c0040060640c804c0aa408500140046080788681 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 936943003 625 936942378 936942407
    0x6140d0207020402041d070c03090b0d2c0106060c0b010303050c0a080304030e0f040e0a060c 42
    0x3030f620051000c2e140f10701c004500c0c2c40b802d107040f00383d003180109000f0a01c02e400308803101082d0890b120700121085078198594611100d0030420290100001030058542c941034807200c00240451f00030043d04034100208913090341e0310350407194051a1603020303024091450041c00843d104000900c00400340c2400c07100700180e260b4500e001c0d0b80c000c440682c00911024202240b501d0880110309a0640442e01480350440d030303103112501c865079944010040c60f42d40b4480801c140c00781e1003201c076521 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 936943628 625 936943003 936943009
    0x6050901180b0a122a050d0f05010b04020d060513020a02060612030f2a0706140d020702 40
    0x280014840800840e4104000711200340c41c154190305d00003131003d200450140c05000d800c030310410400000950344410620500f4071407400841d8001d40900452f0898008040c142c0c1410740300c680400c41c904100741502818182854258502803c84202a6841001912450181d40000004069160b040c003e407043c1e080110190b940d85c0c0703440b400d21001d507440881003854254501d83c05808a0b407001600c41d0482e00c0c103860304800c01d0b849403180011500142c20b004002e580800404005075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 936944253 625 936943628 936943649
    0xc0c0b0c12030c0301030b060f181504140108010e06010b0316050d020409090606050901180b0a 43
    0xc1212040f000d4940000180308004d41003911a80143c4203031081c12082d20488000b030801c07010000c5022400c850f4500042108449865002d554200500100125031840c10309141b039040901829245600b8440040208000001c41c14121182040c0c0e044c21505c072520948481c1d01b00810500030480148125140490030303100900080c0360030000019010218035010040e585207900c014032803180d0303000401c96516a00c00c4000b03103c10003c00024403424a00001d5800c00300c03038000080c0c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 936944878 625 936944253 936944257
    0x309150a090305030c010615020606221112040302191104050408091f08070c0c0b0c12 39
    0x9240981e014080c00c0b09004203610302a88d10310710003c003840000d141c1e100d0310004101031105c20515001980a80c404407500741500d85a0000284a141c1000101141d15041c010142c072460f144c200242440300b0380403800741e03400b498000c242c049043d5000400d0036040480b4006941d403070b0b500d014481c603c15140c0b8560089a59024001202c400c0c0340c2e50074501c2c0807521150390f03540d1075000407212030f40b54000090880210359400d11880e900740015001e2841d6400884a20f403224000c41c51081d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 936945503 625 936944878 936944887
    0x2030c0c06251a0a0614030c060405012303070f09090c051c1808090a080309150a09030503 41
    0x84010000104e01b460901084d0031b030a41500c07007a000307400c1001c418240e44c40b22402c507002d449003801c1c030b020141c04040560700701414800d244c01d19454040144281c0c650300803003000051000790f580ce1050358890b100b00040322440a42080271401c00c0040300202c184104201040032090303800010b80340d031226080001d10880403401c0b1984a000101c00b041c40c43e05012488c0607104007030003142032100319400705102003040c8001880092020802401e141e1286500b20041e40e88034043d283c59 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 936946128 625 936945503 936945511
    0x90109031a160806011209020a12050f16061b0f020a0602030c0c06251a 33
    0x4140454086001e070b01c1c4030340d91124403030008a060390400003e81e80c42d400140b10550203900e01403da80505803040c80284405200d590300c8080003918404500183c1c0c164105100020340c010741000600381c1002c503804003203500c61074042c000c0d003403d8800c2e122000004230307166100c040200114207035444642c02002480c0c00d40e10766034001e6032900113001d038032250310030405c001155140100644880419440540f50750014000c0c03024203601540303404507100290030400c001a07581243d0b02505c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 936946753 625 936946128 936946163
    0x30e01050f042a030f0c1203180911030604091110081602060408070809010903 36
    0x4490140511040050800a0850900790301091030240c00e01120f4599000010784000f40000c00800c80740c10500003095000c4005180c138900010050b0082d1801511081c00c01a003441e100304898000201d10005001d030000c2180300481051860f030b106400c110082030148016100d010300b002c4500400d8840303603112003c2c0310f840c1c0c40700c015514010303100218414882c0541821500043d05100c0017401c540c1c26107400f140c0c0031008a4480c02000b004a6554041d5480130b426140401c104c0e104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 936947378 625 936946753 936946771
    0x110a14010501090b180a2703020c0f01030c020c280f0608010f0e16030e0105 35
    0x74507003030007900d4005081c0816034869152140318000c0003401d148000d051303901d400e00c0355401001030103512500085100e00c548900c8082c8504500b10341e0081d0050a101f000c00e20400c00c441c42100480c038141850030301d98940f441c1e8000b581412906060f0741c44450032500329a040000b01c506850400e41d0502480f003c10391035240301000003194815100e040c0c803a41c940740d035100440300d5806540200305581c4001840c3c2802e542d40020340c20018140064404890208103080d03a1080703845400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 936948003 625 936947378 936947381
    0xb060f0405090a3c090305161104020f1b060402150d1d0d09150f110a1401 34
    0x81400d00d1244040d207044501404c0046510b41807100c00000d0308070302602c055640c2866080b86404c61410100040c0440440155025100041c074060040502c0b000d005405403450103005010000d500311036070303010701b520081d50044000b0700c00e10604600340b00404000901060101d20741c0303114880b605d030240e03810800d03490503085040c40150442c1d0242c0c03c1401051041002280c1c8004040007030118500300c1c40c10010850455501071264600b004160304142d031040c5100d03594655240c4160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 936948628 625 936948003 936948071
    0x10905040c031b020a08071106131715071b02120f07090b060f0405090a 33
    0x188a1003500340d603001d030070440c142c5e159448110094101c6404200350030002d0340c20300c43c4141012000f0081400d051130000d80003483c0c5010b030050a02d229551035502e45e0000104600c1c0034a07403000d90903520919081c0002040030f009081c1c5a40040c500d80e0700c900440d80c80240c503403911a20001141e2222100808465451107580705041103180303444ca03440c4440c00c000c4100e40ca40210415600c0ca011301c1c140c2880650440180194802039a482d0312010400700b542040881c00108401c42d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 936949253 625 936948628 936948641
    0xc1803030f07020f03060103110d020d140601181a0d0314030f07200615010905040c03 39
    0xe41c18514801205074001704c004e01003540c1140c0d40e4001c4820300030303c3c4902540c1041d80c21411903c4003044610300d13176004128920b142001000f11940c1c0c03107003401020b64803105284001c10240c120300440070148042d150b6103c0308103108013404207969035a1419400c0061b1340300050742d415901001075000310074100d1201e03164034080b40054000c0041910386203c4bd001500400c03418600803030056080796603e24211202000f030070048811407150f0700071980c000d141c070542e410340ea60540d0160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 936949878 625 936949253 936949267
    0x303021c0617030403081204020f0306240d1109130f081e030f0c1803030f 34
    0x1c58034004440d2490004400000b03030380590f46d03c680341c01d00e0300c09030003040c044c101c0c40104200c0c0c0c00036240440520070b031814007180e0b014090320000005038421886140c0e007800f5020001c14081c00c035100d42c00e000f040804494203880c800a45813900d1541b910048501028100c0c24040e04004019801c103080100c000002c0c120490700d40184446005118650103071488240c651062200104001c221214450030040844841c219166074003080c000000c40d0441d08600d84043d04041c2c0400c00c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 936950503 625 936949878 936949889
    0x11a250302210901080109021c2301050f030a1502070804060c02090a05090d0c0303021c06 41
    0x70300342e1110100c81c4140100600600c1d4250380d200d44500e0656040442c00f68803286034444540041c400d12402d69107c2c1e0401c15500300ea910030810701c1401107211419034980d0307665031041c422000c81c280307100754058005c82610804500701d420700494030140300500503d030060300c0d141d4052682150708241c00065a00c103c80c4298a40644110340144181104010780c1c02e11444090351880c15011400c1840070400c102c0041c140641d040e114840700c14035010114480c03803050302c0000c1c10680280b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 936951128 625 936950503 936950533
    0x240c0d0206040b0a05060f0f062205040c0201020c190807060516030e0105011a250302 39
    0x2001a65401940c6130030b41e501039031240e800880740d1f410b02800740340031909101094000340005003008664a40e811100c545404061814100c02c5001d1045081901560402180500003903103000e9480348225500c91820100b9544040e41c1044c200800103101c0850b202d4540010040c401420032981c600b03104506001044046071400a03252041c08041c082c841c121034040c1003032044103100d103100c0910341d40032104040c5100045960f0b94050101810000003150095004250030800e4400d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 936951753 625 936951128 936951143
    0x201020f0d09061409010e010822062c03070b0414030c010501090b010e240c0d020604 39
    0x401d0402032141004d07403c00602200091500c82c00f4000641000205004944501300c3c01c1001c03046d10340103c80c6801c0c3c0c480036080c208054102048001242000107801124005161442882c547c40d420301561510040f07490b43c2ca0312020150003038840c0c003614200e852941ca010801007040c0b0748840f0000c2001d40c54100314070111071403004a14140001494410303266580c00f5045c50000c980c103540041c2c082c501252118050083c0c1005029501c01c034600c4c0c1e00700c1900011010720a611030441d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 936952378 625 936951753 936951767
    0x307031409060103260c060f0609150307030210121d010c0503091005040201020f0d0906 40
    0x1858281c40041c00b941281e820580d00d40400f4038030282e000d86100300c500c00e98035402c4200407010818008000f90b40c420f28646110000a084c030b00100302c100c1c40060405030b900c64203104800d4140d600802c40004803a0304441ca00b07007103040c03c0ea0079202d108081d0440345070ba80c03074000d0030450381000241c000c1e0b5000d0040000c0095030a603082c2503880f400140e800700003d40c000d0b000010781c01130783d0380034582290050044405201c807151f40c01d482d200410b5400000aa0488000c000c11904695 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 936953003 625 936952378 936952381
    0x41407031b090b1c0e07030308010311040612020d02010c08031311040905120c01020f03070314 43
    0xd4441000180391040c407061040000715108000701015580094062600d18002410170201c07518460203071103000024190300090040c180c03805202104040640c050402c0704880c11841180e040a402084010241c60584030b404410ba006040810030341c0310300e65564040790f0084880e07010001c0401c00c140103110480034855030442c02075408202d19405500d50b01c0c0d03100c052a50130076290f080010580062482901030f54581c1c84840c0003d0348a04050030b014014140081014442001400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 936953628 625 936953003 936953051
    0x61406030c0a060804060b03120a030b0a090b030d081005120a1401180f0204140703 38
    0x902c9031207a0b03240316200029103400c0108000500c1500800344c50400242212541c004282c10030240e64004400500443d503140580c1c400ad06049003000001c0c1180c400030002e0354002808240ca8006038030054041001c100c0008062000d85003500002d00000303003d2803000d00444002542d1240c1122007525010881030000001c000140180c0e04114005808444055503d80d1442c003410003250040384d21030b40300d8642c0b40294000030321151086d0003595002c503441ba070910301d1200e0b54610803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 936954253 625 936953628 936953653
    0x30e04111b030309070306090804030c090b090c130e0709030b0406020433081306140603 40
    0x1010303520398200407884590b02d05044c040504a940c8e102103502c00c000310740c41190025544014860f00f02c40c1e850440800910b5519070807801901c02000040001031000220703804402c5071500216600d00309071078821280b000401c80030a110000b00c001c80411089030b03005204901c1018050390340c41c18004140c0303800380340311a88004020110001d14214103c4980d480000b039030b61a0000c21a07681221000e045c0d500c0c804081d101d1450710407074030392484803489a0303441030200382d085582001c1c00700c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 936954878 625 936954253 936954307
    0x90e030306030a030c33050a0c0813051c20010504030c0609030e0411 32
    0x2200c1c024540100140006800d9640580b00514074901c00d407141c4100210078040701c5010091101480c180c44061200031040c5001c0c0012100f0140c115040b0b54640100080e030584c00100540d00500000c0c0c49880340c41561600c07a2500c460452091040742e0804690b401d4560015086c00110703245100b15011000e02c03400d401c1c06c881e0105da000d800201201d1800c0b004c00da00e544442041030091400801c03010807100420252802d504108144000010708043c8004142c040450804070304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 936955503 625 936954878 936954883
    0x50c041112040809010e09040b04110915040e1c200309061204020a0816090e 35
    0x11118004031800c0d0160703554429002607451303544000e1500103d420020b818406d0740e100fa886070902045c440141c007510710a41c0308a03455403842c5801030030400445c0c002c862105000c1c0d9184041c506d2801e003a0490503103041c0c1c01c0c0031500181000302c540307030804070031918040005500b00c044030380c41114080e040c2c48100d80c56024503d00141c142c007080c3c842c81400d5204890a00c810041402c640b80d074040c00004080b04003d86501102200340b618141419100e40800e0b05d0603c28490701c2c20801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 936956128 625 936955503 936955507
    0x618060c010b091305030a031a041506020d0e01050d0b030703151a1f080702120403050c0411 42
    0x403034001741782d5001007000503e8140254031061074000c5105140441000c000040781c11035204411415600d041131104104a507410003405902000c17524080301c0f0ba0103040000f8017a80070741c5c201038214903294041109262010020b210056405c00748000300c010031000303400b008004030b06c010541221460391001c0c280c1031503601d500c00507100403800315101081c0e03207044410b40c070007405510460007a808108040302401c80940061800384024103403101c141c0341000300300c8030440d5520b1000541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 936956753 625 936956128 936956161
    0x7080a06030209010b0a0c05010e0f010c09151110060b0712030e0a020618060c010b09 39
    0x1580105a0f140c005001e1000104000280742c90040c4c041c42c07400000992150082c0725035082820300e035844ea6601c40303010a10750b080c180380c806040d004034140c000340c80c080401840e00044118080b100d001030171000008a0160300c80203450307200700b170007024040c00c85107400591382c80340c1e0700d80038a002d2020030441080515101615180e488041202508113404a40d41901e50041d0b44100d01c510046650242e8880b40000d16207201e0103040d0040f0062160803118400c042d600d115401c000c0980 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 936957378 625 936956753 936956759
    0x60714012415080c0f07140303071706040b01050a0f050708031e0702011a120f0f0607080a06 42
    0x280c0c4c541042c8900d0303108941503200d00c4045480030900c5aa00c401c401d410000f45001c0c0d6010340390000d40702d6850140100360b040c010400c0b07220740d0802c10000140c1e41c11004442e58502e0501e0810070b0295a800155020700c10224001c0210341d0010412440c2a00c5d51100031202031102ca0440c85510b03000000c9080e40c010031103a9030003c0119141300b0803480c29600d042200454001035416200c0c0328008103080407080200b640c101e03044003080200306544010384540c8101e10007000c009042c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 936958003 625 936957378 936957391
    0x6090c0315040c02070f03050120190311160503030406150506071401241508 35
    0x4a501c14101918190b6002c00c1d0b2804050081e410b04d09103070001c07840b50b08059000405e10005401085210118000450240003500940f40543c0700d00441c1c892810404400f0b00b584600ca0b80c003010280e90750103616030401c00002c041010b030703201c251070945542e07001105110600c2054490300030707c032030842410320b000c4e8030388070214485025a8501900320012055047e40031002904040030a90001c912020b05031281505001083e440c1c0c0124659650714100307841d541801080918021b10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 936958628 625 936958003 936958021
    0x9070f0605090901320a1703040303200a12110a0f02041a0d08090d051506090c03 37
    0x640850144408117814240f10f1485c80c001c04000003540d440041342c45c03c0e6028180d13040035420014042c0241b5410002c0002c0c0003400110700241071801c03011858440484410040c0804d40c1d02460002052003558804401c000320003e032001e10b0010700d01461a1400340900b2405942410110303440401400400e651100010344484c0e160700342c03541d0300206907000701c1405901070180c0a0700004140200851420901420344000660810300100010504006c0600343c0e020700420407c80021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 936959253 625 936958628 936958679
    0xf0b0709080706050c1015080f010b0607140118050c03012901030509070f0605090901 39
    0x2105210f21410710000003011302281d0340c1072094800038001e201c030030301c8424810550304049080c1c5d40720700e94650050341406e954442d41800744c070218a02c001d1181d414075109881d21aa21414261035140030741d039414450f191462101c0c4103804050045018080710060a07003070600750703421501601100c030700d10a090a440c028058003203a80003001c0ca40004c2c0d95580903901880c100140d044041d0b085915600000c100d0762200003020f0301142500c207440142da0b1200ca484100a55001021604 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 936959878 625 936959253 936959263
    0xe010e150a08030a030f02040308040e01060314060105180d060c02010c0e0307050a0e070309020d0f0b070908 49
    0x902004065000c0c1410401c2800d82d031f075082100001140001c0054405000400300c403c4455161540040075603034041501c650030036006081c02910780e000030494070780450103515512464102c4e4005000725010b01c0018041c030742843c49440d109035040d030001111011030385840d12044034800501d580d542c15400b6007600f28a08075010700149182c0e104580d03011000780b60110304454550b01003148900c2c42a000c03115002c040b004a030820030b800703451a40c4440e1510b8100840c901d003201055880e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 936960503 625 936959878 936959887
    0x60d060c02100f0c1e0e15090a1a090f04020d061202041401030201120c090e010e150a0803 41
    0x1101d24021020141700c045000c40d18080701032a080e5009880088480c11085000000c00e9441c0e001c44802a4175603030742040c600d9000d140c00c1d601c50140c0c0d0a105121040c140000314042d1a140148014600800024070340211000c40e08403242018003001c811b02182000d00c240480c007a0030006041c0a0340c51580001e141a000ca0984941d5030b4641d84840800383c01a112580600030702c211011003981c46814008000c04101d403004c01860001c0141d0701d4600b4000450016200c80c8e00243d4a403 = true := by decide +kernel

theorem S144 : BRFrame.sub P3 P4 TB 1680 MM 255 936961128 625 936960503 936960527
    0x120c0102070803390703050c010801051e01030f020f130f0e100b03060d060c02100f0c 39
    0x1c2d00300b890b1304503500d044c189071001d103015021042c3ca010b541d68000c985982048040706520340c3c004001e140142004c0d00c052068040e00035000100020198026041c5079031013181083e200f034117505644161481c210482c0c0c0c4e4811030f07940030003060030340d2144520001d043c2a01003403010700107200e18040d90f0301e4041900070504090010f03c01c1e4200401e003903003290007d0225000308069000d00e8135440b4054010f0700c40600c2c02400e40080e99803150b00045c082e401c0001400740b20b84c0c0000c018240c = true := by decide +kernel

theorem S145 : BRFrame.sub P3 P4 TB 1680 MM 255 936961753 625 936961128 936961177
    0x6020c0406030b06010c110a15031514040c1806050901080906011d090309120c0102070803 41
    0x122421002c80410890102403050030002c00030080c0d43c88c255646c050f13141401d078004004d400240ba001c810b03820b015102d4542c5050b64a030124102d18452400c0910000f04503e20040c401c0c0300600d100e0f03000200e01144060f01602c500c1e540c107501c0d07903401310004d01000c0014122401c181c21150040c04000700c2042c10f041028501941030707200340c032410300705070940c42500c2166030010151f040d120600b86000030344450382c00c0ccc281e0071521819503803442c0544a000c0c0d02d2402c41e0544100000311007 = true := by decide +kernel

theorem S146 : BRFrame.sub P3 P4 TB 1680 MM 255 936962378 625 936961753 936961757
    0x181d01080c040b03030703320307110c010e04051b040b030a1a011b1401110406020c0406030b0601 44
    0x18101c3d231002856020301c0e9030f030118580f0710141c400d14070b403a0140c1c103030036120b003024280184849050f0843c0e108aa001e9445101ca81e80c004442c00038001e0b0466002c40c160359100691001d07038004041340b0303806100105000c101080c441010314441d4404840410000002501140311844031025050102e00d00980c819140d0f2001010910550300405007100392044242e882070031503080c2b0720106d507001d0010800780000d030790500c120003844004540a1060f14156250305020344406400c01e41 = true := by decide +kernel

theorem S147 : BRFrame.sub P3 P4 TB 1680 MM 255 936963003 625 936962378 936962387
    0x121f0b0a081603020705100515040627240e060f060a181d01080c040b03030703 36
    0x40b004103010750080c00355580103407552060740c01d040960303000c56002c01d002e0300b880408808040000004c0200307980d420302807850300c0c5105041000c805014840000c054449860313001c2940301500c00e040e0403021441401103124030300d80720200440c13a804051603402110039110111550101c8010a4017481400341450400c42881401c80d100d5140b000148050445040d00700034001281407020202007080c042c50002e40291402801d262405104402c81e10130064060f50a100081e107042c1d4 = true := by decide +kernel

theorem S148 : BRFrame.sub P3 P4 TB 1680 MM 255 936963628 625 936963003 936963031
    0x10623090909190507060906080123030a05060a020310050405040c050f010203121f0b0a08 41
    0x1c2c402c0c149800c42e00c4054203085451585006860220b07201d0b4031a000a10900754003411503002040582450700c110f5050840c89000e1416086e91144d4880e0b0b18075410b09a90b40401419007210780020a9481c1401d102c80b00c0c0d0701030340c03040750344034080482800000b440b07007404d203d41071045030000c5610a91608000800142584408030319045200602402a903411082070341405401c5001c48201e080e40829003101420b0816030190064000903c152081541c12001090340015000341c100 = true := by decide +kernel

theorem S149 : BRFrame.sub P3 P4 TB 1680 MM 255 936964253 625 936963628 936963631
    0x60c090e011e080303010602030c0f0d0905101119050d0801030305180d020d06050106230909 42
    0x120b4021850001405800c054040c0d948950b9030303a40103943c0ea085942c0301022400303110680c1210304800101d01c102071086580358102ca07452310060195046000c010041000558100400d091000300401221412012411840c500e81401c14a0501c400180d001c0204000b460042000c240d002c0107842c0c20381003005461400f02031148c001001035030380d01002034100d044820300c0020300800342d020f00e04851283d00c51000c010b0019034160b03000d91001507034411004050040d0343c064204102481d = true := by decide +kernel

theorem S150 : BRFrame.sub P3 P4 TB 1680 MM 255 936964878 625 936964253 936964289
    0x40c1409090a06050a060e10031815150909050f010c0f03110d0c0c060c090e01 36
    0x4405030f407200800308090351402411703405000310b591611a030b035040c1002c00003881c4c0701d0001c1d1014549001c40e40c406007002d4506400007241c00088a10710310f10004c100d02d008040c910500074081c000d14101044950881d00500c40541c0510101c2e460704c00f4111205080303c0c003584044000c0b44590b030001e0071071030094110048010b90343c1c9060741000001c00301e04082da07482c4c41c01040082c000c007840b8010001c2d1882041062001c40c0780002889041c20a22200a8010300581419000d121525 = true := by decide +kernel

theorem S151 : BRFrame.sub P3 P4 TB 1680 MM 255 936965503 625 936964878 936964891
    0x6040f0803073509070b04060e060403061505101805090405150f0105040c140909 37
    0x4440307841c08583e510316400105040c0b000000c4440c0e85815881142000c003607142c0c0c800c5110380c3c0e101080e02c120320364a40100000c014051090710400802d52000b411140303804d5903a00d900d01680c08100c00414030384556842041a86046039010019070300d6402d140c16000605d100000802d20648034250107418100001001c0040602480580e4900f940c1d242060303043c518907001d00101e0034000c03140124503100c1c240c00c00c035003c4c0000700040342110940300c0c41c01c051081488a10300c0090b006 = true := by decide +kernel

theorem S152 : BRFrame.sub P3 P4 TB 1680 MM 255 936966128 625 936965503 936965507
    0x30112020105160b0402090c07030507031209050a0b0a060830040812130806040f080307 40
    0x2464403080f81c820310f032250700c58881a503801c4c800206001c114103050341d00f980c0c0724450341c85150812030300380da000748103224404001d0104069200a40514840c55001002e02c40d80301c42214008125440d0000c59550300f1500c903d0414075005000984407808500e0810051501d9031500c0f0005880780024461483d0815100c0038260902020070012810012030103011022406030f0303140c1204881c407080000260b04003101e00e070040c20603c00020f20401c2c1c81501c2580c0540c401c0c0d05c0341c2d112041 = true := by decide +kernel

theorem S153 : BRFrame.sub P3 P4 TB 1680 MM 255 936966753 625 936966128 936966137
    0x1e0516061b021920090c0a0323070e130c0e0102150606091513030f05150c0301120201 39
    0x513490325400178042c9015880d00901c90602c40e01700300003050000f41406c0491700c0e40050701d00d0200711403180000540b0140c440c02c000b600c2d00002008841c0e04816641d200d400c0e50280e510840e00c0d20400381d111a55443c1d914800241494941030404000b007100c0c5060020380c0d10303418250344030f01c1020380f217110b040c100003c0c0b8078800c1c1c010680942060b000e544030101c100194880b081d0a524401d0080307480f0100200c0c1000c1d0302100485500d801690248010003000310351420385151180103051 = true := by decide +kernel

theorem S154 : BRFrame.sub P3 P4 TB 1680 MM 255 936967378 625 936966753 936966803
    0x90302240d060312050a0f080417070b04020406080c011e0516061b0219 33
    0x8104000e003035200106001141680d0105107036045007442034181003c4182c4409005041040544241e0409051081c0c1809400c14025a94030f038204140907102840e00050031490001d0303c00100602a201c060055000b0755080200d0742e12200003990386d240c070812040c0400c4103004441318500b54203101c005000100d140c0b450804940b0030110607007100d207039011141c0c0d030b81758084120f800780c2910303d00043c20f88500c01005030303540200b885c804c0e1880071100689074000b00c8629060301c141c600c0d1 = true := by decide +kernel

theorem S155 : BRFrame.sub P3 P4 TB 1680 MM 255 936968003 625 936967378 936967429
    0x10c0507030b0c12101a07020904060510050405040606170a05060c03150d060c030b10090302 42
    0x4e02c445502040050040c541c2101c0c12030382c03c880c01c26860384900400710300010f52074040c1c000043d4100000100240014800c0c0d80070315400120407030b00c440465140c00102e0b04403202101d049031800d903108401d00504a182e035442000400c0200100303581e41d0309544154456a01030300b50700c11082c006c40401d0710721540030038016241201510081c0c1c1c021050802c940600340c640c0c01ca10119141140040740b47c14032801343c9428940f41e44800600078511342c02d104501182480c0308030301d1044840f = true := by decide +kernel

theorem S156 : BRFrame.sub P3 P4 TB 1680 MM 255 936968628 625 936968003 936968017
    0x50d050304080d110615060a1202090604030305041e031709030118140705010c0507030b0c 41
    0x441820500c0c0d080f40a40854a103100e04121390f0424070406502c140007409000c1003407070f42d40000e0343d980145171942080103079014045100041d83c1e81266851003001340b405440e81d0b901d160040075030707000780034400481110180707c0c413544101038659003d0781d51000034041c03020070078003c05445030069902140c1c50342d2604085003031984004e50781e50485002c1c2d003520500000c1d941d8900e10300381803903110350704010b0034502c10400300350041000401c0c0c1c0d41c024106142c64a500c100141d10740a121 = true := by decide +kernel

theorem S157 : BRFrame.sub P3 P4 TB 1680 MM 255 936969253 625 936968628 936968639
    0x4090b0310290613030344010803180103020a030e30040e01050d050304 33
    0x9000e000349050902c2c00c2c64034040c02c40c03001030490545503401d800c0d4103000050307a0071301e0740d0215928101802d584080e50100b0310310101c070782c4980004115441e0300691009070080d0205407060029a21b0884560400c500300580101209500c207001910903020310001d00c0c043c3e03080a00b00182d4401412a00b203019082040d545080c600c688140ca22a0f02c4002091a01c1c440c0c94480901080c2813070780050086120383d1044039400f10340680180302038907120b6203404489208100301c900e084e0350351 = true := by decide +kernel

theorem S158 : BRFrame.sub P3 P4 TB 1680 MM 255 936969878 625 936969253 936969283
    0x106052b0f061d1b01020706080109020304230109290a090c18020301080f030f04090b03 40
    0x4080401550654000307010030f9903c4559000900d00c1303007010ba4103551003584204881da900004284c15030340d483c5c002503100c0e02c641c07424100e40702030319508003a1072244d83c0d0ba0802445c015404000e881780145100714441c404000241048080b401064424003410301c00a405070b6942c0c0c0082001502c69000c001c5003e9880c1480401c00c0d4459140721066600040100b042078401c0040188054900c0051031901644c080d05180e02d200c0e9201391500546c4802c001e900039a42030000c145951020 = true := by decide +kernel

theorem S159 : BRFrame.sub P3 P4 TB 1680 MM 255 936970503 625 936969878 936969911
    0x6070807020f0604081b0708070b0901170108010f05060f180a06170106052b0f06 37
    0x1d084c84180003a040180c5807080c500050b01d03110011400f001501d40700b0324460320700103070311072042801609200030151070350400c1803410100010038840c2c51900c100080e8881c1940740d5541015881420b5240105c6500840503200011100f4000f404100410102202d18210810300c03c00f0071000e14254000100034182010324510b0541c4000501d4002c1006100d4981704561184400940c02840c501b00101c40700b51300d0410b1000170075034441c0c1c1240341d10300c5170448d03e42d03a8555465441c4c4207071 = true := by decide +kernel

theorem S160 : BRFrame.sub P3 P4 TB 1680 MM 255 936971128 625 936970503 936970513
    0x50714010c17090705031f060b120a0e071a0f0f070807021309030206070807020f 37
    0x2910800011103039500c40349442d1030100b0707007604500801c010b08501402c000100c1c0e51081c03903078100d1003c030b03c50741d035414980c0a542c1c0c000c1d409081c494840980d6010074015600545030152150412186400d0004824090118602007a95174200c00d840c8091444106c4d03a400390006d480f594903e50042103070704c0901c03a95900600e040e0307100340e641f541c407052503004001c202e4080009214809040541c1400003a901203042d90740450389052045040c0c5480e10121328202032150440d81d24421 = true := by decide +kernel

theorem S161 : BRFrame.sub P3 P4 TB 1680 MM 255 936971753 625 936971128 936971141
    0x8030402090615310305060f04080d0501030f170c030a0c061409030c0d080c040605071401 41
    0x10600d83c3c00303101c1c80070722000550020140300083c10744c414104003049980040182019417a203172a80c1888400c010010307180064200003404840d0103600c5101d00850117071100303120b02c1c0c0803407405d0003402e1002d03411900e40c0241801005482035000c0300711203a042312420040c80b00c114514028019140d050008502c2003001c1c400c01c0300b0300300c0110040c840d841040c3c4c00da0b41e400804200c181c401c540290b40c240d01c0d00405100c1805160702030320081c0040d40c007601c3c0c9000300002ca90704043c00c2d2402c = true := by decide +kernel

theorem S162 : BRFrame.sub P3 P4 TB 1680 MM 255 936972378 625 936971753 936971767
    0x4021f030621050706090f0506070c2606090705010504180b0a0e07030506060708030402090615 43
    0x4440c1d6140300b15040e0503d50f0030881c0340d81060013008101c445c00d02100c074480002c941114020394480780d4510490901c0400d0717201c141c1100c45904951210b22031203001c1100286901c0a600050718800c5c1c503004840c40c0d40e800c0500c034043c04107200b4481003082d41c0040c500320444601900c00423400440d00340026135850915041604900000e50502c41c0701d6605120780360380078000b91126803a014498561002074040140020f106110b8070f400950503803511703c800e004044012103150f4884038 = true := by decide +kernel

theorem S163 : BRFrame.sub P3 P4 TB 1680 MM 255 936973003 625 936972378 936972419
    0x1203030a0b090705040f05010f03200c2a01081e090c0f0904021f0306 32
    0x61608811840203050b58850300c1ca440701e50084807144581d01c14010000101c000038000c540c0310f0501ca500c07001d914500895261502d00704100b020440000e40d1010b4070b80040c003a0103004040c4440900740d003c04d02c042040b084108070300d50031070780b420180341d0400000100065280c6c100005120a240000c8c800040c545840e440f5980d40d514a0410325104c0d000c0c208040a80b441d1500c1d05a200c8c4d940641440741a02ea446c058690f5241c1401c5002c060503210342000c01c1d2400641140c82907a003 = true := by decide +kernel

theorem S164 : BRFrame.sub P3 P4 TB 1680 MM 255 936973628 625 936973003 936973021
    0xb0301060e040f11090103020d060209280305061b0a081302091005011b0803060f120303 40
    0x1290400482801080d070b100900120040745e042ca81549140c00041c030540c103800002c0d042650028100c010ba6440304c464056156800c00d00200344541c4d074142c105102c0c2e081c441a1a98002c00002410b180c40d166100c0c845020000f100604100070910200d850440050070842602600f039801e20143c2d60b880314062080e082c602e244e04d40709080c0000107103040c143c0c0c00442039505190369804001800c0c8010340c0d91244e001c1c1d4840701910541700020383c3d042881101703100b00e030000005001d0809 = true := by decide +kernel

theorem S165 : BRFrame.sub P3 P4 TB 1680 MM 255 936974253 625 936973628 936973643
    0x120703031e20100b0d05030a1d03010908190810061409150714010209010f030b0301060e04 41
    0x5003103450500303003800e000410300140790445d1031824081d80a00103514200c49070800f6111209900003240c502a54554030b41e119403002e00070f4950880c481e60300c40e40d440700c0010030218903140c0310720440c0c1003128081c00c01185d56144540641a2541d82c2416141003a40b15000003403840380c0d400c85600082c040506214180000002e4014540300f108241c041b02c00c5ca800365401c0740a03040c0c40a00040700a499035020b00d02951000c0d4004001034000b150207070720f810344040c59100c160750480b80760 = true := by decide +kernel

theorem S166 : BRFrame.sub P3 P4 TB 1680 MM 255 936974878 625 936974253 936974263
    0x90506060714030a0f050a02070612092f0105030f0c03070509030d0305010302120703031e20 42
    0x8103c01c001414141c2c1c2c44045c0c4080c000107200040e0700035000f0800030f0031500b16080449108000f882030600030030120100074102c0d40313103074484054011384070440410a000d0180b003080c010b040341e0064486000898449101820710000030306006071007006107400802600f40141010740d0140047d003014103160407080000c0d40c890041055241c600c144c408005c031044003070803101e400c0d03413001040001d441a5404000c010118900107041c0b113014880a0f01080201c6400ca0342c01e98075144d0340321 = true := by decide +kernel

theorem S167 : BRFrame.sub P3 P4 TB 1680 MM 255 936975503 625 936974878 936974887
    0x9060606030408070c0b0c1c211b08101e050103020a050c0a03050904060b1309050606071403 42
    0x400c0201c103480c9400f890204145040102358601000140103020072000300d0300c4402015000114004c1c0024100701c0030710550103860031440350601003080780e0100011000740d042c2c003502410140c800002c210160309110014690507002d500d05054020400c020341c10b200380c0580304103100d503c00300c80d40c041d000d0074080d00c10b47c01080114000c90402501180d0016184111030014003420035011085203044800d400134500a03040382d92100c4100b0158012490780440003480c0641a40a15a00c = true := by decide +kernel

theorem S168 : BRFrame.sub P3 P4 TB 1680 MM 255 936976128 625 936975503 936975517
    0x20c0d06050604110f120613090c060f17040f1a01090f1409060606030408070c0b 37
    0x3807400b48030340400b241513484450700340300f0481c01040c000e00420000451002481d00419419a03541d80101c0d9090454a01030140712442c3c5804000c015440c0715120103e0388100131104038501450406100d1000381c5014403941d552601e0341c010452141d00e003680c49400c0f4040141c009800e00b9019406082c4150000c00c1550340401c6c208101c8025003080900c2c4080b03d020302c50b44800c0881e0194200c0c0c01164115102d85440c10300213258464604020054546c1e0540083e807005001c01070302e50 = true := by decide +kernel

theorem S169 : BRFrame.sub P3 P4 TB 1680 MM 255 936976753 625 936976128 936976141
    0x60f1208030a1b0903020a090e070302040209030304030b0f0603011407021c140c01020310050307081c020c0d0605 51
    0x1550241c4000c40e0231891031154261956400004202035440c5900b00f002075440303e90301a07013500040c0b00010000701001e19642c00341080e400490120302e05003040c54210303a04040d2040c405180e617800e1000f1541c001c20200c5180c0018600d0010b8100ca1000584080642c03541d020000100001c103d10300c05019030245000d60454000540030701d03580c0c004c041d5a0302046c0100216a0410104c0461602c07030700c072510184609500644071580e04290025607100310114040d152503842e00c041298 = true := by decide +kernel

theorem S170 : BRFrame.sub P3 P4 TB 1680 MM 255 936977378 625 936976753 936976759
    0x5030c161b210206040545060139050a05030904060f1208030a1b090302 33
    0x14100400e009030b42003009010102c00585903041510200d40094618071002042441110070507001d8440644400c0d10a011181c0103842801150020307030f80c01445940c41d5200d00e00110b400c2040c949112080b5003600c1000904801401c91052000703c54064007441e0b019540c0d59241040b070080410f4aa59101103905500b51800c1c0c42104020154110400fa44a20b0510000060140c604015026500100000d04803a509030000340901c1c14080c24060303042003100020748980198041030340 = true := by decide +kernel

theorem S171 : BRFrame.sub P3 P4 TB 1680 MM 255 936978003 625 936977378 936977399
    0x19060305120a021006050a15030e061014040c08060d020a03050105090c011e05030c161b 40
    0x4e25134a0704070150035500107000e1598088600c0b80c2c00e001446412a00c0c0b1000f524618000ca208581c42c02d0f103d042250689103804c0150850405000c02c10b642c40752540d0f03000003036504210a0000b2071004020f400082d181034030440000d80d41c2019542c816003204047d41e00f02000b0006420502c00c0c9942e101c02d900801c901207000341c511281615040c07442c04441c100360f9101d0724a50340c2d400c0744a0025034490741e0401801c02154107075102180c0d0240108c400070070303980c0c000311880d410041d100d41d = true := by decide +kernel

theorem S172 : BRFrame.sub P3 P4 TB 1680 MM 255 936978628 625 936978003 936978013
    0x21021020a050d110c070e0402010e0901081e0706020a11040f0c02030c0c09040b19060305120a02 44
    0x4016130304020442c180541c00c0455a0790b216603100d40503804040c03401150569215203803403280c0000240c50b560b060350b5a10005030b518a850a03414624411001c5606100400424200c0484015030f00402003110306449811503100300c11102540b0507a0741218031003051240c0660804486181c000d184c13600c0c80d4103a91410141e00c050300d01d2188006600b08800503003020310180c2c200c4100c0084004001918022000601c010740010f042c610410b034422220b544100b004200301e010983c01d580c = true := by decide +kernel

theorem S173 : BRFrame.sub P3 P4 TB 1680 MM 255 936979253 625 936978628 936978641
    0xf150105040b1503040b101e080c3a140c010e0409021021020a050d 31
    0x9600300081c2d040d10010020008134555511516020181500541340c0380b0300c5200c80c1c0c03001440c0854038003581c1000b048001d00b03090031464058058604010000c401d40b01c1c802510f0080d910043c0c1001e401c00001c078030306400a409900184642d0050084000642240c0041d1207220000c60046491601103000b600c1c0c0541141507202408120341d00507400075000411501c0d421852405404041407480f00c120700e0f540d080d50b4100d02002a40c0000700034001040c0080340c007840c0100d040c003500 = true := by decide +kernel

theorem S174 : BRFrame.sub P3 P4 TB 1680 MM 255 936979878 625 936979253 936979271
    0x120e0609030a060c0f08160f0210050c04090b1522091a0103060e07080604020a020f15010504 42
    0x5042c1b109003c103208103e2081442100c9003140362426100094041d80c0032410449400b0605161354100002c1c008480c07ca40002d00072256019000c000154040050051084501101c0049110188061150340300e40700c41d100381c46c00c1080f20480c00c0344e450340395080407600c10144200d9920108000c495465825100300000b407c83c01c022003200c1c0ca485d5100425600d4000c24040c000c5401043c0002070b0b900070000500e0111451003a14540e60300e80c102440a85424480c2c0ea1040b41440c17440 = true := by decide +kernel

theorem S175 : BRFrame.sub P3 P4 TB 1680 MM 255 936980503 625 936979878 936979907
    0x30305191b0f0e130902030106030212010b090609090d080a09060603030903120c120e0609030a060c 45
    0x798076450410351160700c00c0800580014484c150b40000d00c0aa00060001591960f00c0d40003c5140e00304401010180c4d444d1443c501040c84c00b040500d6010340144c95440c96071501e07a03000b503102c20135000350109000c400808149070080b00d910103d04180e104208012180d101d080c0500000710b83d01c41282c90345404001402a5842074000c00d61103030b03010079440000c0414410aa031481503500031607070040003d00048010360741c104400d03080c240c002c060000d1840200c8500411080144030603 = true := by decide +kernel

theorem S176 : BRFrame.sub P3 P4 TB 1680 MM 255 936981128 625 936980503 936980507
    0xc01061a030f16030e072408040201081f150804050c01021603030305191b0f 35
    0x1a0031070502e00b40d00c20b0300300340181c180c01080c5030407000750ba0b040b4060742108100001c02d07825a11160303502e07043c41142c031402000e60148a0410401d040c0e0550140c5c4640f4011030301a0f64884c3c0f980d840b5240c81041fa0002e50382703a04081d6020000081c0c0071040b1a243c0d5100b000c42d03907400c515050a20380245805100070b00d00d4195000b1100509141c4cc19108a500b16601450003007445c0c0c8039031361040750800c0c5810215181500305040450102003e00c452a40d4080994841040c010350203c1 = true := by decide +kernel

theorem S177 : BRFrame.sub P3 P4 TB 1680 MM 255 936981753 625 936981128 936981179
    0x12190f200c0f250801020a09180f05040b04170f0313081b0c0a050f150f07080c0106 38
    0x4071001c0c00b40707448030b520780d92820580d280c100c9407820840155584ae1101200c030511144180e51040d440b40700e0709a41d03402d0508051850000b1038980d0341000742c0400c01d20900c1607011041c0c03640003400d4500301000081e5071074040c0320b60040b9840400e090314550000941c11202107034000e10320300181e030039042450384d5004110300d83c020200400e801103028010000c045200400030030006030080b800610b0018955240c690b194003a958403802a5554607051014500740c80c0f1802e200c4600505e03 = true := by decide +kernel

theorem S178 : BRFrame.sub P3 P4 TB 1680 MM 255 936982378 625 936981753 936981757
    0xc0308070b060307061d0f0312212a12190f200c0f25080102 28
    0x4026064101c00f5450001001024107500c1000c9040040c908147c4081c030030341c1501c2041e50039071955600310014000203101c5925140100d2665020300c82c5c0381000c0b101e016462202c80806d082001141809091301104240f1480c10305445010485260741d08445540e8401c100c10301d40711400106206078400d4111107441480400b00358201461640d0605445903071125001603414041641031200302226421002503514100b2203801c604040c90781e4040d2410344011800d00000d07400d405100f = true := by decide +kernel

theorem S179 : BRFrame.sub P3 P4 TB 1680 MM 255 936983003 625 936982378 936982393
    0x1050f0705031926060d0c03030801090506010503041e170d0c08010812041a070c0308070b0603 43
    0x200b00c044213144901e4034941c080c0c0107455010030040e00078006110071382c82e44004004564811130000782148011310484c0200d010307141d0009400c1c28800d00b10304082d6a1000c2a030200ba0310300040000c2d00740d25500380600b8461249a490400c840c0c95a0398090104c00e201918404c02c0802c04100c400000140c41c10000900b11071243e403a03501a0300b4141080303e491045540140c400580740c40520a100200c0c103030014850082d44248481503441216160038811140d00802c524400c1d041040f = true := by decide +kernel

theorem S180 : BRFrame.sub P3 P4 TB 1680 MM 255 936983628 625 936983003 936983027
    0xa3b070302030a150612030201020702010315080c01030c030b030d090f0510080c0901050f07050319 45
    0x2080ea22000c605000c0c1c070303c5001140820020513150014070103480118820101c2c40341615019020390000f19049020904203015800624810303035111045800f04001051642a42c00055000309400d003035400401d074480001d41c02c82d803800c105014840c034196071803c28581c50812244038006013900520321419034410ba0360000d603488288281c00910082d0003e940f4400000107803400e10403070348052078618010036801c09102020014143c2518001c1120500c042e070480f0840300440302c51 = true := by decide +kernel

theorem S181 : BRFrame.sub P3 P4 TB 1680 MM 255 936984253 625 936983628 936983633
    0x2030d0923160515160206070804090b150a020a06230405010b040e0307030c0201080a3b0703 42
    0x1c1e1441c00d20f05d128512400841040100d030445002d11142d4005001c003405000030349407a950009441200b0710410150170b094159142c20160704020502c10380c0c1e404504002c03266004600484c007808401c00542c2603618182110f041041f440302880100001904240c0310480115411310902802800f641e840b48a5610010003080e0744840c82c40065000e00000c40d403180ba616000101c1c0072448030b0b00a07003901c800701c000c1045250500b521000c400c201682c0d0714000d000784005e1140c2030550b03 = true := by decide +kernel

theorem S182 : BRFrame.sub P3 P4 TB 1680 MM 255 936984878 625 936984253 936984289
    0x90510061214060c0f0c0a0c030f060b1206070509010e130516020c0102030d09231605 39
    0x4050713076405c02680f40c0041e01c950b98020042e00d800a1041d0203411030850307060010034445d0700600716442c503014403001e000614400c02030040d4605082c2c0800c05d1a480080000c015a1103140901010b050524041c80300f04803101c0041c1c076030b40030050001c0050f80d407441400700040761801ea1003546881390010340342603110f84002035280e026051480c0c1c00c0a0712440910100103102c020080c255103802e94070841c480b441c408066580401080b000208400002d01046a142ca0142e441111145d0 = true := by decide +kernel

theorem S183 : BRFrame.sub P3 P4 TB 1680 MM 255 936985503 625 936984878 936984901
    0x80c1b0604140d06020d0506031203010602100f02190c0c08030a05030a09051006121406 40
    0x2100400091078040c1101080c002d015206007404025030b04c400c400c0e6400382c81d41403040da80760414003a80b42020001044e240f828100d00ca030455040c424003c0d2179035141101c00d03407841d407299807201c8603031041d5045809e0444441d150b00c5012036603140141919a1049080c0d4604034840030001c5c1250010088419440180e5582807560342c9000b941c0d001010f00c400240d6a5101e02103205160250303070300c00e4101a000380b91701c1c501603001c02d2501ea9200000c111604034690080d109002d0040b855 = true := by decide +kernel

theorem S184 : BRFrame.sub P3 P4 TB 1680 MM 255 936986128 625 936985503 936985507
    0xa0b040204050a14100509011a04120515092d06071103090a03080c1b06 33
    0x540003038001d5072501c0020340c1e04a02900441d0502c8542c40c00000c00346026000ca250722441d90007110302c00c2215000001d140501110712074014602002014641031620001e0081031246200c1150341f4090540c02d00401002d2200c028802c0190502400303180010b0041c45c18bd050008814a0039000b2541403810307d810001806503000c0300c6030034041d80c00080d5400080c0755006005020317030720640014000c02002816406458410b079003204030342850281000142400c001407103420341140701 = true := by decide +kernel

theorem S185 : BRFrame.sub P3 P4 TB 1680 MM 255 936986753 625 936986128 936986131
    0x42a0906091d0c0a030905100204080d0504150807050c1203150f0a03060e03120108010b010e030a0b 45
    0x111840c40ca03d58019201c1c0d008150f9643c0d024400118181f0040b40000d00340c1034007603146e0341800d04203410f021340d549095060010412042042e401c040e10825a0f401c03a03402c010841d82e03100743d400d6406101d8201080b00740d028070040301c0c01021100c400b43d806103109203007501c000080e49041c004190803008000d94400e1680100700b001400c260440d0426844074001d480c14a0700f03040b065000003c00f80c1210556075141c015641d183c0d41d00c00c1c1c6ca040211030803402003414101c240c84480e5103900 = true := by decide +kernel

theorem S186 : BRFrame.sub P3 P4 TB 1680 MM 255 936987378 625 936986753 936986761
    0x2032a090c09010e030f2a090105010f080406020d05010e0906150a05042a0906091d 38
    0x91a001d41e0780828034001171300d020450106e4806600400c0e0602c0402c20400c00f42080720f56402d0355104081421104200c44c0e403809100c2d09010840307544000450a1203502e1050327015116079001030816200d520104100d6409800040078600710308103000724038408001c200e520034031030b40d52240c2e90104030300403c0140010b44a500d000d40d8031603c1c417080c50390b040d221402d41d0040403075040200d084104401443c04010b0f200348004902d950074045040d01c10705c3c880225035411080341c030300310340c807 = true := by decide +kernel

theorem S187 : BRFrame.sub P3 P4 TB 1680 MM 255 936988003 625 936987378 936987397
    0x1090203161806290c030a09210b011a04052205070e03032502032a090c 33
    0x2e8400040010080c5224a2030000305c1d4883d5070440d00300301c2802010a40c040000c202c19a41100c84c9a2507001c0c00b041008890036541c0c1d0070b040340d0300600070303144034010107a01c0c0707418954038104403000f514000f0801c814a0600c007503854035451907010f070000c0c0a403e040120b50740b240208540403902c48020007a5090100080c803102c003404460f070301c02d01c400c419105810007607203040c4008281c06c10303800070a08003410134003144000700c500c44c91118019400041000460300959041d640d807040c = true := by decide +kernel

theorem S188 : BRFrame.sub P3 P4 TB 1680 MM 255 936988628 625 936988003 936988049
    0xf0801021305060f1b0a140708061902090d0b0f340201090203161806 32
    0x40116200d03042410040c1904c900600a20071017000c0c003000c500c0c158542c58100002c0710b4066030080c041c03002020018403201511000c03c01440d80d41c0783c20076104035018000740c0001803180c0801c03c50503581c07164074040d441148140d01002c000d0419820604821100400620011030404a22079454124000071a83e0340354943c4a0280100c18000032400b502078210080e41500c20102001071b400100e01c040c4003201d40c1218540f02010b0781c0e0765003034190345207845014001a80840380d082110 = true := by decide +kernel

theorem S189 : BRFrame.sub P3 P4 TB 1680 MM 255 936989253 625 936988628 936988639
    0xa06020613020301151e0611070e090a050111030a18020a050904081c060f0801021305 39
    0x1240764080b0303415585d038550b4041c4807000317821060107041c1c3e00044080140c50290044171401040d00030500f40504004900c011002c00035141040e102c00721104100d54035840c0c81c0514041900000030095400d114130134591104130800382d4820340b80c0356401d0021450005041204500c4000065000b029801003403045041045180d50800c0c400e4012030f18103018103400714143c0c100107121051940e1140c1c02001810902214000500701d2880210f01d0111030252103c08185240728150040 = true := by decide +kernel

theorem S190 : BRFrame.sub P3 P4 TB 1680 MM 255 936989878 625 936989253 936989281
    0xf05160212030702040e070305010b0f1f230a020709060321050c01050c03150a060206 39
    0x405010301c107465401140d10003900a4138180b00b0b040328410001d810402c0300c0c0308000038440e0500308002c1c403001c4407406034044d422022104400003c00c1c0f88941610b40038030f00c0c1c90a141500045500e01034a017011840012189a000884003400d950500010002e03051002d024812149917640350422800681441410006000382c0c0012440c4910202c1d909165400000d1109081c054a2200280e00545400d210100901400001e90801460f89421074505401905040d5200c18000c0120 = true := by decide +kernel

theorem S191 : BRFrame.sub P3 P4 TB 1680 MM 255 936990503 625 936989878 936989899
    0x90b0a140721050306041406130b04020d060b030a050c0705101a0d0506070f051602 38
    0x5000e5000c40003240014584102e080030007102c4400012008400e11a66080500900c0f008134180020f800d41403401c100403610b00070129a041603065100c120802131134550b0342c120360400322201011700200d601c5038500a00750303105841440d54a840e03c0c00107203048605106640a240e44030014080c840e60b2903140101412403101d0025030203a55130400f08565407560202d0760800c3c8a6400b500c0b1030324015402800340040600c400c01032010420510b80b8a10085040b25800c1d607040381c0c0d24848 = true := by decide +kernel

theorem S192 : BRFrame.sub P3 P4 TB 1680 MM 255 936991128 625 936990503 936990517
    0x509030d230a090f150906030b03060408030c0d091a01081c0507210e01090b0a14 37
    0xf84200c81c1c00b070050940d9050525285c0c0c580c4103200085046842503800520a05c000241c0745100e40240c0001c84400340180c08030b1346036619883c900d540014411000340d0400c0042c680d00030242c1c4030b0326100d2802800d51034140e140150303080800101c181c0c4030500560080564003004182110b04260480300c03410210b50720501c3d45450300301400380e40c2a00b90354038084d14004c41650f4000440803501c030030076680d45145a8541c051b00505000f4052054000b98504680d54404081c040040c062 = true := by decide +kernel

theorem S193 : BRFrame.sub P3 P4 TB 1680 MM 255 936991753 625 936991128 936991147
    0x10e0a0f05030c0d080a05060109061e03060503030a0302040302241206031c0509030d23 40
    0x150005100c5620740d8902041311003074051807135417110358a080003401e0304115403015001314108a4501002d000043e0042141070244a03052120300101c40e00410880040442d5005a540341c000042c4043d0746c1d95054000c0c10943c0c0c0221000240540c031916400c0184061800302c11021606108418250b9503100d1138650088024080c1e8510344c004d0004020a543d03008840741c081600402e6010450030b00300400c240402c500c0c1072041030491242500c40c0e14240c0a81c045218600000d2390300f44 = true := by decide +kernel

theorem S194 : BRFrame.sub P3 P4 TB 1680 MM 255 936992378 625 936991753 936991763
    0x1407020325020d0302010b33030c04050607050a0b09010b0f01080a0e160512010e0a0f 39
    0x5044501c002070740120b0a600c122082c990f040d00311000b110410364285016804900c0307181c07248000d1044081030f112160201c108038400d003070021a08480030b583d10604154542c0c001904980c0712000c21100c99200b129408200048160404d07400501e1000801c01441c803407000c52603203140d00081a0401c0300c90400286014400e078046101003040300100c40c06203512030321010901c42c0c0c83c0113032440788942e41503c0d501510140200c0f01100c440602821143e910b9540d868180702c2c1c060f000f01d075 = true := by decide +kernel

theorem S195 : BRFrame.sub P3 P4 TB 1680 MM 255 936993003 625 936992378 936992437
    0x1c020d1b24020d050f0114010c0209071704080c100603120c05010623030114070203 38
    0x100300002010070741030303074071200303050b5803e07076440041000003c020220310740589080c0865400c0c4c0384401000809104901c03c01912800e40d070804140801d0065014020b04000e40d2400744440c0741504120515802075110701505005000e400803014840d1710640e801d0302e512850711101084101c00c02c40c0c81b102140812180c5d90341e603c202144609500a040c031241c001c000001c80340c0c10040f0103060030346031070a100c9010306024005201c103082d004001d80e40000c0080304001140450b1000086 = true := by decide +kernel

theorem S196 : BRFrame.sub P3 P4 TB 1680 MM 255 936993628 625 936993003 936993053
    0x30d09020102032118060c04360c0813020306150a081c020d1b 29
    0x5008042012800400000c01c2c804c289003816550906010003041c1c010466220100f0b400e030048101c1c3c2c00700703850300d8034102c21a1400c2122903c1c690341001566003a201010130f1445180c001d050311000003e00da8803190010b00404800f50000729103412013082e05006031000526036070401c501000030380b10345801e280042d0049140b48c01a2119000703000d079550904900b0404c4c848862100d40944040f041803100884c2c075064144030510f008407004040030081041c240002e4900c2c2440d0625072 = true := by decide +kernel

theorem S197 : BRFrame.sub P3 P4 TB 1680 MM 255 936994253 625 936993628 936993637
    0x2070c0503060901020c07120b13240506090f04020a0b090f031b09010f08030d0902010203 41
    0x6101e0303800304041406003c03001c0c001a5114210001c0503c0d124441e405643c03c0703100c1d10060404500f0307400030183e001d82c0d25943c103400204149840000246007000300b0202c0700e410341c46007013584125803066101d070704265004d4030207450340b19503900d519904807402540070341e400f0b0050101801c0303003002d810540e0010304150318100e14040000c0c2080340109400c5484000b446c4816068501b45010500401358280c1d56454942410051034a920030801c020704603035101c00c0d00d0000c6902c02c00489 = true := by decide +kernel

theorem S198 : BRFrame.sub P3 P4 TB 1680 MM 255 936994878 625 936994253 936994259
    0x6090902071a06190b040e06012604021825181a0c070303051b0d090902070c 35
    0x250308001d004d40010303618500c0c401600898046000a000b503a42d0880152262101036020348501000480e11150038910040007940060014222038815220413000312550380050b41c01c05043c130184d010350701c241201908400c061004918150f944011a0080700c01c2d0b5140798051544d114543c0005500c076942076505403641032a81c0022105526a03070308000c0d0003584100f0303807444210300c0c0352440404071500017014041e0800035501e199041d49403800800c000d41049000302e8207410409000 = true := by decide +kernel

theorem S199 : BRFrame.sub P3 P4 TB 1680 MM 255 936995503 625 936994878 936994909
    0x201031503050304080a110901150318150e07060e030304031e140706090902071a06 38
    0x1c2e0540c3c100b548a440c203508a0100741c000c0014541c4040c8242100f01e4560415504192032b2041000000600348141650b0762403a0281d10301c03940c000302d05194001c024150340c002e002e84c6140078107600d030701d04d6036a40f0501c9808524035004240c12014404054000c508041c5146c07281621040c20703462111074501d010128001040344003240d1a8120941d80040091601e840e100400142956005c01500791040c0289400969895100c9440c42e805400780c3d0007507180c240c005410f0b00420710b440c = true := by decide +kernel

theorem S200 : BRFrame.sub P3 P4 TB 1680 MM 255 936996128 625 936995503 936995513
    0x50a0f0201091a1b030c0706020904240612050105060a0f09030605130b220201031503 39
    0x110700f03540845004100c10b503081e00c0100b04003120035250029890007004480c0654044141d040c2440c00b59502d58001e0b41c010315005030002d843e03403a1829800884201ca201c0c0b07042080203500d2440c10100c1c0280048003424080b90400c3c20580100410340359a0304450404441d4901040100c20748007050303c00c482e19a10080c101c52500003042145460328200d440402d01c00c0034560a83d8031030055040c0c0e04070300085094075a00240207240015070003580682015512042c40002580d40d9440f8 = true := by decide +kernel

theorem S201 : BRFrame.sub P3 P4 TB 1680 MM 255 936996753 625 936996128 936996143
    0x50136080d08010f0609050a0e0703061503090606050906060f0f070b15031606050a0f020109 42
    0x440140d840341d02d4120665050650781820665107a101204001042e802485607032036841c03443d0221414545480d801e922a490b0580182200e5080002c1c6401d4030301102240275410b4100703028590098030100445030726542403068441c1d08585079034016108014425140c0c0e41f5800070101102140a050b0500c04d1070b40c0c403446d07280d00070740e101c54005416002e031b85206e160900201c1c2d68200043d025000307a500d004005003860080b8072005061040c0b000801c134201e4000e401101606a001c800d = true := by decide +kernel

theorem S202 : BRFrame.sub P3 P4 TB 1680 MM 255 936997378 625 936996753 936996763
    0x48070c080307050715023406051b120409050a180303090c05013608 31
    0x30103990000051120900c110f080c1ca20042d030350b20448a0502c1d45414503400350700f090043c40c00c85030800c15845809055641220001c0e916800c0c4122411101c0c1c002d000040c00005612140d03040e8200040450084134000b0f196000c04840005a980030b10b0085401c1591504007140f400c05032500320040601c0c6104c2003070100341581c5405030040c07880c1c14086405200b0208001807640c046d000360390784c146030001502450032803030b0000d03680564245100d1000303078440a00400c07003000400c4 = true := by decide +kernel

theorem S203 : BRFrame.sub P3 P4 TB 1680 MM 255 936998003 625 936997378 936997403
    0xd0819050a020a080a0e0a110307050303040b0a02253302064807 30
    0x81c509a0354000c61070441c03032500100000d6000982c8141002245a44000c075941c6801c3c0403005800d10940c25005681c1e5101070043c98050f000180c2180c1e621596034010401c180e100780103540040c000e0300071812400711620f44107860f4068400c0d003034502c2d600741203c135181c40b4608140c5003101c2162003109c00c240c040e401551a60060707a60003900032460551081080f007003003461101702811618941d1901846050140c003c900380052159030400c81c500c2c4518100e100e40c52014107a180d0030324 = true := by decide +kernel

theorem S204 : BRFrame.sub P3 P4 TB 1680 MM 255 936998628 625 936998003 936998011
    0x20304030204050c0c3702010c0c0f1701060b0d0c020c091f0e04050d081905 35
    0xc00d0b9880d81c2003880c10545c1403146103201e8801031045181c45804215240384003c0400754080260301c0310308082d000b24104580b509842010404414000000e051400a0280b1242c81d103c22680b0a03083d0b40d80d03503685649001000c00980195804541c031200c0c04a2000c02c0340b1040ca0001c3e030a00d05e0b209c04898006000c00700f00910411031281c00316001042c141c40c0001c07507031078640b4102e00a2085500030010f0b4042c009032607500e806006603903808a40b102d40304143c51240c42900081c3c50040e2 = true := by decide +kernel

theorem S205 : BRFrame.sub P3 P4 TB 1680 MM 255 936999253 625 936998628 936998641
    0x81603150302120604031805061614071514030106120b0121020a08090c0906010f02030403020405 44
    0x201802c000e0801c2d08008140f048030034404010791f00c7c03a42c0c0070401d5403942821191052006080301a4a130594a0300c0c904550030128912518407070f070035010a00b10239000d50031607200340759101c1d1005803022024014090009226400c080344160520940500207600441c0b00904145846030844c207042c8240b466601c6d0000513a03801a50104143c981180c01100207500035070380310000c0280d142c1c49400100c0002d4003d1000f41001910f01c031080d2030038001c20503a4080d40d80100240024500318 = true := by decide +kernel

theorem S206 : BRFrame.sub P3 P4 TB 1680 MM 255 936999878 625 936999253 936999289
    0x6051009060e0a030819020609010e071e0f06020d090e040f020415081501090c081603150302 42
    0x2001b2800321421703500301c80940d40c480d5141422218940d00002c510341101c503041120904d100d203c4140d003d0405450300c5510343e5800b0030744154240d41c2c0030702c015070050300c040101160028611401041c00d40602c0d803c0b490195038000c01440341d110000d2299503100726420548016007107802c080e1804000f1541c0710340c041142c0040b210744c00d00c50541c2c401c1c2442e07110740003144615403450003021365103d08000380a84c11400d80141028520040d14034040041c00400b50366001855003800300d1032 = true := by decide +kernel

theorem S207 : BRFrame.sub P3 P4 TB 1680 MM 255 937000503 625 936999878 936999907
    0xf1302150d050f150d12050a0c1523090a021203070b0c07020406051009060e0a0308 38
    0x350604c4400c1c0310a650b00d04102104403001100d100d04d54991034019541c6058800038408001803294004c0d00401030010207030b400990351581c848940000a014003208600300c6158180b14048401140c11014010f000b0f4011000608022a0715424801024684800360030030f0700c02801544001800384400a20070700c43c5900d82c517194049071040c08107460381500181c0c40f4044120603c0200e50740401034004136050341c0ba203001c5821100317000c070340585820341002d482040e0004280d1114030b140e = true := by decide +kernel

theorem S208 : BRFrame.sub P3 P4 TB 1680 MM 255 937001128 625 937000503 937000531
    0xf01050d1e0e0105090106050108061c1704261e0304170102030f0f1302150d05 36
    0x100b41c01000c5502e04008244c01c1c541c1480b0759001c444060b1288095a5528002c003d98081c012582c16000e050032408000050000544105020140300076151200d051010410100c428545071861030b01c441d1a00c031003800000100908000840b4001d0b171240c1c0010001e040c19802180e014140381d54540ea180c0140e40c0040d0055842100c0d59000454160350707078401071a0340d142c01da0700e1500c5900c18010b000302604040581d4501c2154001d401c620380344440649004440c0c044895007a64045 = true := by decide +kernel

theorem S209 : BRFrame.sub P3 P4 TB 1680 MM 255 937001753 625 937001128 937001141
    0x40b0c1303060b1507210e09040605060909070f05060708040e011217090f01050d1e 38
    0x8090000c4c0181c2000c189030800c4007404400082120140b9000104401c50311200c45000861400d50b8103100222055400807200e108201c1000055440301c0d000321b5048800c1011603540d012641d0751040305c1c0c019010210b891403010802401c0840103040d00300c0c41004000e041035165401103101503001da00840891444400c004184521840603030020034003075520b5071802c1050008129902d135154034190401000240306400c169071a031151035a4195a07100001001c4803e1000014024 = true := by decide +kernel

theorem S210 : BRFrame.sub P3 P4 TB 1680 MM 255 937002378 625 937001753 937001771
    0x103060510350718140c0f030a0c0504050607060e010c020309090a0515060c0c0102060703050c03040b0c130306 50
    0x42d4a280c45d81a46c4001214866118080480d6510f10081c0085203404603d540042c0d44081e1605000d807505848600050710360b00700c80022114940c4070100142c18242c2070142c0301d07600c1105c0c0025810415007800103405844024018111ba540d81c50004005241c02c0c0d0f46c90f61088409014155920284084551500b500200702c1e4090701c182008030311103e100b0b10545200340752241115085840e56a11606102000303000a08042c2c414018025510410001c100040d803044000081d10310b9 = true := by decide +kernel

theorem S211 : BRFrame.sub P3 P4 TB 1680 MM 255 937003003 625 937002378 937002401
    0x210307030e150c070e25020c0a170604020609180103060510350718 31
    0x10589100e07480303500060310b56041c00d0380c1e0302c5a96500c0f041030085540e088083c0340020050250100110102c04c00ba10014842d8081030344040d5903110381411152044140c0000410000d200480380628260a000107110584403902409500d52001d031016400080078034003603000100e410590fa000394800c00000805190010b900b010211a6030450320000c100711029910649907149942a0041304207081604151241c400900d07201c503035407019440310425058001d050304140e1003800d4500 = true := by decide +kernel

theorem S212 : BRFrame.sub P3 P4 TB 1680 MM 255 937003628 625 937003003 937003009
    0xf1002030c0105010e10090b150c0f07080f0a0b040c080d08250509210307030e 36
    0x41d00c1c002007801d04041020500c2095440c1d441e42149091041640141070504d030620780040071142c42700500c43c80c0c2800b420741c1001c040c0082040e84088003c00e07103000c4582e03200040395040003041500c0b002c0d02107000d80745c0c1a00800c0c0700391241c5591908041c421070340d51040300140540141441c072103501c9030206004550f03052201c01e0303a095082c10540c4a100c418601c00c04124100000c1d942070400ca1a04003c031803082010344e204c001c000c06260700310b50141c00110002090005d640301c45103 = true := by decide +kernel

theorem S213 : BRFrame.sub P3 P4 TB 1680 MM 255 937004253 625 937003628 937003631
    0x20a030b0109051605030403080621030702042711011209060e0d020d0e01030b0f1002030c01 42
    0x150044c00c40c208060043c0541c20195080b00c1901e4029500d4200600b65030345000c00b11380000c10548010002e901c1c0c01d0b40e058615280800100350b014000d0f5824094140f8407a0000d032600b6814143c078003118000010007021495400c42941c1608051400b03001c110141070b00041560011101510307241d90b1101c038281c40392400c12904101d1400c0c0e0005e005081441800940325115440b0701e24141a1114408091030391125455400100020300b0f91220006a5900035a29000180103007030b2503 = true := by decide +kernel

theorem S214 : BRFrame.sub P3 P4 TB 1680 MM 255 937004878 625 937004253 937004261
    0x8040e06180a0506040b0319030f21020c0129010e060c010c03050105030c0d0b0604090c03020a030b0109 47
    0xb11040507250f00d49140700050f42d86230a905240402d201d0340030640c40c0314030b0b81001241c580c0280640d0440b0004064450b400c07607000590011881800d01c1001f983c0110a81c8061303440c0c50400242c6d0b0004003902240d81040035004402680d030342d8001c100c0341c8106006c1d0082109180d07400c8054050036003442024030030700400c3c10000d03190030b14011203910941c0c460201911030b6601c41c00c00000b042050710075190b01801160210040c0c690b1454072016601401220006602d450500da0640d = true := by decide +kernel

theorem S215 : BRFrame.sub P3 P4 TB 1680 MM 255 937005503 625 937004878 937004891
    0xe011413080d0c120b1801140607080a180e0906010302010309080904060b0a0f050708040e06180a050604 47
    0x1c4421130742e0303200c58041040c0000030b044d07060060351840a28203c142047e600e41e49c044450b0035900407405a0750b5002e4000080060301590511800e850021200003a20401340301d04a001d003220701c01500d0181d10310342c01503005003400c0c2001c444500050201c80401d58a03482120000d14592220669426042d080202401e690988407010700c44107124803008980c0c0501514180e03920581020320a03201c02c00002d0b85c107407842107945601280001003103442c6a042d003115016000070b40b81400007 = true := by decide +kernel

theorem S216 : BRFrame.sub P3 P4 TB 1680 MM 255 937006128 625 937005503 937005521
    0x60d0510090203070e011b05031b060702010603020f0f04090501050a020403060e011413080d0c12 44
    0x80407036000b1a4807600498079400c8410701d40e00011030301c2d03604029001e6203400e101d10381c580004000380014802403204c031091b01004000d2034012030401c100078145d641560314103803003040140c030fa41007581c02519048400324845400c450205014240648000300503500e4042004014581e550240083d01d0003030404008032070340d1103445406c80e20f80c01c4c102008200b20600195025041d40300c0c407104140f040140e1030824150102c09400e0f15041c030741ea038001c07c0c0b80310000070824038107104805035 = true := by decide +kernel

theorem S217 : BRFrame.sub P3 P4 TB 1680 MM 255 937006753 625 937006128 937006139
    0x901050c0c07030204020f090306071e1e031d190b0109270302030405060d0510 36
    0xc204001401d1180c082034450680f54112005a66038030004c19014841c02114010381e0306005035418014101d03000451440740d001c164051321007440040e00c0c01d461040000041c000c1c400c2092000d0142540b0a038400341c88140074000e984465800840b2281c41c0c0142e00e0741c00c010584101b804141801468080b6600401a0840c207001010050710032210041007100c1d4061100364140443c1c0405000740103075006003202500540c1c5801c444009007010380400d0300e410310031800d05100840c0 = true := by decide +kernel

theorem S218 : BRFrame.sub P3 P4 TB 1680 MM 255 937007378 625 937006753 937006771
    0x1e06111c0b0a0e182a01053432160b070201031b0206090105 28
    0x50320240c51030507520912907901032048105541910707802040c2d01003461480c9069004c840d08043c030544000280010009005404018500c0c021420b07281c03d107000351030148a4038044101445804140380c2c0c00c07100c07103115075031803000311884503109800489510040e500c1e140280c00218a004c440040e0213100c03002e103ea48000091407072079500080303540c00d11060030147d41d00c1d80b0390030a03241a0304040c0c907051041d03031800f400805101086982d0307000d0038241c684010314a003502e40150900328 = true := by decide +kernel

theorem S219 : BRFrame.sub P3 P4 TB 1680 MM 255 937008003 625 937007378 937007381
    0x130b0c0a021f020c2b123e1e0d0807090608041e06111c 26
    0x1505040b81c0c000307581c80450740001805a0001c981c5010644c0c07030a8450741c0b111040c0b4488048400d11498650b0b01c03107040c80401408224940f055480e0000042c80607071408500c900d01e001c103500c000a134940c1c0c01100d4400b0410310300c40c2d031450003004c0c1e0341c4107107200804400900400c41c0e05800d0307101404c0c1400c024055030800250070b00c10443e41c0c1e889070a4640140c8c0062007034075a0305201114003002e0350000e0300a0070081c1000d80b000710000001000300792480030701c0340c85070b1240700d001032240 = true := by decide +kernel

theorem S220 : BRFrame.sub P3 P4 TB 1680 MM 255 937008628 625 937008003 937008049
    0xa110307050418030c11041a030c0a150804080f0c03210f010506130b0c0a02 35
    0x2c0c0780c03c220001100e40615403829124070b140458119907200a43c1020900c1360749505c6464000c5996080396420100584141071900c0e01940107288035025151041000d440d038580c100e0f0072180586840d44403070f201e601d0041d020f4040c40e0450701d1054000314592500d000008041e08032008015441952460501031055007071006903036000d000c07000100113000504242c0d0042034464403000200140704e59a0120300100d07000b264400c0c86580180b00040c0651034031080fa042c040ca85044000 = true := by decide +kernel

theorem S221 : BRFrame.sub P3 P4 TB 1680 MM 255 937009253 625 937008628 937008641
    0x307080a0818040902030604050706090609060c200a0f1505030403050706050709080a1103070504 44
    0x50690002c03039444000207040c000b20840940040340061204101c001c0d010310500b4140700500c0000203010049030b9165940702101611800112070038031642c03040301c01150100d541d074400501d0303002003c0c2000040018160b90000b1850024191816550040c1e0444907000c0040c420300300d810402100da1007840c01c1032803031810195001421441004c5002d0900d0313a80d08040b0b00814490603803000207100300411201140300504081c594080720b40100c0713210b0300c5080400034060415000c2c01 = true := by decide +kernel

theorem S222 : BRFrame.sub P3 P4 TB 1680 MM 255 937009878 625 937009253 937009273
    0x8060618090d03050601120509030a032a0f050c06010605070c080d0914060903031305030708 42
    0x1c07602d80c48200a1101c0ca40280e118940103d014100391550440d0301d84c80805441044030614040c0e000414001c14083c0c042c0500080d0b80070344054030200b0352118004078800482248002c08000d6580c0008030254010000c0302c284030401c030262801503855100103001a48040340c1201d110440c5c0704005001240400d820f06441e21036078400c00f00c1c1e840d2101c3c10303200301902441154461010460104503030303000c000400d101e1256041d05082703145050205420035000b6031080400e60440e454074 = true := by decide +kernel

theorem S223 : BRFrame.sub P3 P4 TB 1680 MM 255 937010503 625 937009878 937009891
    0x3030f040e1302010c14151f120201020703081c0207030504031208090309011b0c08060618 41
    0xe8170310f1003441d01c003c2c0480d0070600b0f042c04000d001e02c05d210b00b01050182c00506402c080c3d1000101c010412500f400c00f01c400d00000500f58144024450b080c1d07010303000350440b2030135034403034450b282d103c8282c8100b402c004840700ba0001019200400505000c0e54407a5292411860848040716000e0011010481c0b035409104910350040204d50413480e007400d0006400e0b5a824600c3c2c00030f44c0009010b021240d0010700050880d001284952203100c0843e07010010002c002d00302c03411400700707503500b = true := by decide +kernel

theorem S224 : BRFrame.sub P3 P4 TB 1680 MM 255 937011128 625 937010503 937010507
    0x60f04081006050f1504080d0c11150d02070c26010f0c020d140903030f040e130201 38
    0x111100e01214003440354881d00c05c00f154100070340134080490f14a10400c09450384842c00d60322483c8564441c1450740405c04040c17000350050810a01e01b0b4103027100b800454410804658005a64201c1402c01985141c1c0716044102e4203019400c03200000c0500045d40010099448020049a0b80a11224044800507034518016030001e910741c81c1468090048201600a007081d690300d030406240000e070441e4400e0884045107040070500340408050100c605600c0125494040401301d01c41d000 = true := by decide +kernel

theorem S225 : BRFrame.sub P3 P4 TB 1680 MM 255 937011753 625 937011128 937011139
    0x1518022a0a060b100e040b0f0a12030206070c03080703091a0420010908060c090a0302060f0408100605 46
    0x380d2581c0046c0c0c0c0001d1003180c410005000264a5214281c10014500d4041101b44881e0302c641e07902e50080d003c454154580b880e04a580c0c1500303040103400a1415400b141038a071083d000362074090702032140d01c180038500c0644400c6110782a1811a03e4012511114044202c14441b42c0034018003402c1c003d0b0100d10386168940c0f03d92000304076040f034080c0007440c2400c82e038660441c50060354002e840c080c1c459090030001c0210394012b01030302c0c246214141a4404400d094040d00c416940d01404 = true := by decide +kernel

theorem S226 : BRFrame.sub P3 P4 TB 1680 MM 255 937012378 625 937011753 937011767
    0x1140904031d04090b040b0711030a1407020301150e01091518022a0a060b10 35
    0x10403090440d1000581c11004000d00082244c600300d0321180303c10340c415601100d40400350020800a140d03c42070460007518640d000d5898504800c1c001018148480c4c0c9400c2d407500b00240401c11503809500a00711040301c000812809135a52840d4a100f80c000d2240419590a080c4410503110302410074000f5104404104109010500540e6000750032644403015007481d0034410031811034840011280c01b8003041d0087c2050360481c81c082c1c007541c2d02c0d031210500a0f1090004200041d401c188 = true := by decide +kernel

theorem S227 : BRFrame.sub P3 P4 TB 1680 MM 255 937013003 625 937012378 937012397
    0x306080c010c140109050114040b06090115030f14130308062403070c020a0e0114090403 40
    0x405000c0c42c420800b01607152009502111840e60041e0080040c8d00400c040424003910545007503c480030143d010410500d0500b207403030f04a480f0b55900c03507010341d28070348103401400c0007205815003150384080b9081d028002c0c0007400d22540d180c0c42c684805400c0c0b454007601521019100764040c241c0303010810a140380c0400304032440c1c00c20b001d04a440e5030b5000f1007103410344034160009401c400c0d648000200380c0c900a0006050306e00303426a091b80c44203400140701c4030340c6040700c01800043c001d42e07 = true := by decide +kernel

theorem S228 : BRFrame.sub P3 P4 TB 1680 MM 255 937013628 625 937013003 937013027
    0x60b010302041a03090c0312090a0f150804051e010615050304030c060b060d020a0f0306080c01 43
    0x1e00c0201c03500701030469034603409000c0b651b082e00c0d54100b0480140c180c118000f59903800d944410441c02a807664040500c104000c402003268200c0488954109141414802c155695528040303003807075a11507440000c45001c81441c10401015071100060b203400d2461a440040c0e03201c070a9450380001ca60080006003003c6904001461540000031040c01c02340906051a00c1d00a151041c1c0c5c00c802d0304000054008400e0b01143c580c0760140000406000c2c014045c05200700340001d0074170b01720309 = true := by decide +kernel

theorem S229 : BRFrame.sub P3 P4 TB 1680 MM 255 937014253 625 937013628 937013669
    0x9040b01260a2a1806090212150117090606030d0815090a0207060e0703060b01030204 39
    0x60300096000043c4900c00b0744540b41c0c0c010344049261140c0005900c081210144491041540b04008050351881e904040c1d100c0d140700074a204002c1c1000510080b0481e00e205c1103960107140c69650000b44124521040c9025500454594050350030001c80e4a420070120030405540d1070099100d00f027140340d085652200700f42161103486148001003102c940c550560b040190020001e0000c5070200c42440d45030b510ba800242d4845090030301101c070b194068000c681c200e035410320b98800007100300d5 = true := by decide +kernel

theorem S230 : BRFrame.sub P3 P4 TB 1680 MM 255 937014878 625 937014253 937014263
    0x160c06321c020708040608151210020a09030f060509060109050c19020a0209040b01260a 40
    0x584602404000000250402e1155101c501c0c1a400c1030f1b10100c00f00f80a4000c10000960800a49140c601e04540540b20807400b60010740c3d90707109403e11ba0208542c0040d02c03e00d03545c05407440c00e000b035502c001908a001721a00e4000042c4c0b8050b0b0b4028068440c070000030440c1465030242c1c91040326501c10250a05400401134000c01c40704410032000e6000e641e9103400503849400c025403245000f0001d500e031a514001186010404180d41440e0b07084a005000c07c07048800710342850055081 = true := by decide +kernel

theorem S231 : BRFrame.sub P3 P4 TB 1680 MM 255 937015503 625 937014878 937014907
    0x1060c0f080a020309060d0b010e100f05070f060c1d04050103030c0602160c0632 37
    0x800d880c82c80c1e500034011905280c0d0010001d0742c1d10300d03803480d1003002070a031707202098001001105205440e0a051240308150304c0c90b0307158000c0100d01c1c040c0484107540250001c50b8110010100f0340c0000e1401e0140c80880d00c903503210710140340c240b001840c3c0454100d80b65039225905160040010a410081007510144c210f0809661840c1491100059401840f00100100000d20000407880d030b00c25004094200b1042d030305107101da40f00c1b8041003e4000c00c0720b10b4150a030308000d01000220315 = true := by decide +kernel

theorem S232 : BRFrame.sub P3 P4 TB 1680 MM 255 937016128 625 937015503 937015507
    0x20d06080d081b03071404151e18090b040e0d08090114160807140a090e01060c0f08 38
    0x340c4d1039a03074401007840003041a880b52950300c2e0703031070582d6143c0441c2d0740035200445403d80f01c909c0b60403040040c1c144d41d44400790b00b0a514001140e204c0440403e414403107100180181c40c104285801601c50b161142043c4c0da40030707003418020300c3c49d40d000300a403c0421200e034040c2c2200315104041101c1c0d03900ca181d40a84034520b50741c0e0144191403c180e18142d6021404c800794858900a40004c0c118101440201d0724414247d0041146003009903142e1000e60700e01d200e500c805c6d40080d00300301d40 = true := by decide +kernel

theorem S233 : BRFrame.sub P3 P4 TB 1680 MM 255 937016753 625 937016128 937016147
    0x50312160e041a030d031a04020306100c030221031602150415020d06080d081b0307 38
    0x240103070040f41c484650740254544914802c04456a40c10741004040ea960024a460216580c00c1804141c1c081644d940d07a01510b00c00060f860315200e031039108507442c000c0c4121031114140c48100d061a0034003818550400c0c6000042003544868600c8103008040700d84020542c0030544045c0208606010f04000d02641d081c0515120511054041e101e0000c2d01100c1001020f40c0c2d8402540d54582e544400c0010500010006191041043c03280e441d0b0101926614616038079480101d550060 = true := by decide +kernel

theorem S234 : BRFrame.sub P3 P4 TB 1680 MM 255 937017378 625 937016753 937016771
    0x4120f06060f080307051203060f090a0b191d0402090a1a030a050312160e04 35
    0xd0201103100340d159980071040c01c005a00400302503101081c01c41c2000b006028841a03134078021203440c00c61400d88002602a50904040741c0200040c4000c00d4880015800c41426554050551040d00c064a000f0250b40c3c10680300b90a031284122503400e41032030b0b504194600030341e001002c001c641d44031403507060024807141d459404a800304061100250b24103200302d0110703074010b01c081c0d40c4500c010018400c0d81c1c400140003540c180f038140d8007400c1880d00300ea00130f400c804050ba400614118 = true := by decide +kernel

theorem S235 : BRFrame.sub P3 P4 TB 1680 MM 255 937018003 625 937017378 937017383
    0xf02030a08040c1a030a050c070309030303020a03020d0509150c04060f05091201111201050604120f 45
    0x10024071202038044e10220b80b900200c80441d9040c00d03002162004c10242c00d002c04250005a082c00b21980e56400d0364440754a142561003d60107907001c4440017042650800c41000c0304c0c51a841014003482e9003c0c003928050956421030001490041c06c0c041107000100010810641c10402a0303c1d650181c5c1000d617160f8003508000742e42c3c0300303005000b241194204010100c80316218401003090094810304a401c0d642c07a201400014029800b0700380c00701003280c112102207403001c0c60540a052 = true := by decide +kernel

theorem S236 : BRFrame.sub P3 P4 TB 1680 MM 255 937018628 625 937018003 937018013
    0x31b0e04020a121404141212131b2108181507061505010f02030a0804 32
    0x1400003010303507100c0540207100343c8002d28403143c07030281000d00f481c0d1601e510030381d682c28869000800300355042a6038030841d05058601401c44009886602d40c005680e82c2010000c4c12010520811040c08001401c1e11404c94a0000c00c0c070303415800c80351001001a01d10880336200007001e00c026010300d83c4000b007410505400400101608008522440090b0042c020a41d40c10759501a1855003014040d0407030060102400d052094482501c2d00943d81e00c10003015034200400080401c007001 = true := by decide +kernel

theorem S237 : BRFrame.sub P3 P4 TB 1680 MM 255 937019253 625 937018628 937018637
    0x3020117061e12060a021e040e01030206091c3917190503040501031b0e04020a 36
    0x441c40300d03c00d1580954010022000c2039500100100c00b0920400c60380c164840488080b02c3c000c03405903601c100702000040000d13181420182441c60b400034500000c0c2c030b40214800321503c0c0007000c1200d00b00b21060b034454a0b0030f24210600b43c01450807180d8021204070980c400041100c2c2e001350208203002c189001c7c400030b03040080e03441840e0f6500c00d00c100c442050401d69a0b0b50010b108090004c9d0038824400792104c00082030751002e00c104d45078040301c90103113001c210207074100d41044170400 = true := by decide +kernel

theorem S238 : BRFrame.sub P3 P4 TB 1680 MM 255 937019878 625 937019253 937019269
    0x4180f05012903060a12020a05030f010f050c07022d040f0603020117061e 34
    0x4408555242180c009a00082c480b821242e100c1102c201114010025048400c92150640c01c0400c00106040e071039100740c160300890405404119155803a0301c000500005041c0c0c3c08204e6040e80d00c1d8040c281d020110018645400005542c0c0c245600580b881d8540103002d59a0907042c00300c5004a00c101142480354100000d6400c001c296103501800043e0011202c001c90010728610014000034035030382d0040004c0b1306e07220800c82d9545602814011201182110124011000d80426080 = true := by decide +kernel

theorem S239 : BRFrame.sub P3 P4 TB 1680 MM 255 937020503 625 937019878 937019891
    0x603040c03050f0319030606050a0f0302130603090c05010203040e16020a0f06020c0105010f05060418 46
    0x1540c440280c490400c0151403e5a5940110302040b4081d5031030b140d0311061070b0080c420030b400c1701c0d5240ca955003080405442910321100000da04c8050517000c001d1046420b031880040400352981e500d0001e25002c0a04103060030381c125400450640d40304000a014401600b0107140d40301400207040090300c841440120f0a0408607803004000440e440040700410405402410000d02a00000c0210303030f80e5501654020004c0f4415242c024500704014400d4030091107699003040401c2c0300c0030131003 = true := by decide +kernel

theorem S240 : BRFrame.sub P3 P4 TB 1680 MM 255 937021128 625 937020503 937020509
    0xa02070e040b0c2d090906010302120a050c1b0d09120c0e0403050909090c010e030a020d020603040c 45
    0xa40c00385000c1d2603810011044c55aa60740210140b281002c4000c0c601c034141031050041c0480c0881201130075a0014030618001403a69840110a096005849582500e00444840310111400000300c550f2400016250100c4180d80d411400340e5840041600500800ca04941002420184084150400d100b8107215050082c9140482e1401a041780c02607650f43c03048426041a58102c0f40c04001c3c45419000303000c038203581cbc0c2c0105402040c40c04000307010705c0001000a0038016000400005 = true := by decide +kernel

theorem S241 : BRFrame.sub P3 P4 TB 1680 MM 255 937021753 625 937021128 937021177
    0x90b030907030c09050f061504090e0f070603020702130203010302060f03130b040303020a02070e040b0c 47
    0x801c1e14840004c0c0da41303020703880940b081c0c40c0000365810540d40d40b000c1114041c1d4001c0811a203e8040c0000e2140d040d003a800030000200a0741161540048940b2640c1340072010b034007160000303800040403030450800c8401442c0d45220300034190705550441d40024503601500e845200c24420210000381085203402c8482490764100c400218181424107005020350320514000003d8880c140001540d00c0101400030300c41d98000c03da45040313846942044102d82d0210b0541d10304e503030400c05004503 = true := by decide +kernel

theorem S242 : BRFrame.sub P3 P4 TB 1680 MM 255 937022378 625 937021753 937021763
    0x60310020a02060703050108010c090b18180702251404061502011d0d090b03090703 38
    0xa90303022910040068000208000c4d4954140c411240908a214020007050940c0315028080c1030071801031948014001c5107101c80181c1005450300c4920010385424080d104800c01806069410340350341c40580610083c0c180c0e415104008118044041d1080700d04107494410380e0001c1d400011405600581c03503000105e8840390859100014901650000a030403210410010032022140076510050300150f0569075102ea1055405081e18282e0b00c0c0b4aa59460b680d030139038a0014123600c020b003 = true := by decide +kernel

theorem S243 : BRFrame.sub P3 P4 TB 1680 MM 255 937023003 625 937022378 937022381
    0xc02062106030c0d050c090604060503070b040608070f0c0f03050d060902040306240e060310 42
    0x10361020320040050482086620501a10408650000b146082d442d258449540140144401c0501009104000102030180c5030800c0d2103a001107250b0f0740512410740600354a0b81c2154a8905d0110028400000500440705211000c40e0600394554842602d00c031080e084240c40d01c910b030107840c04903424031942c181c05854070b241c8903020415000d50f40003081101d004540510040900349814200001400d642480024003040c04100940c1c0400c40203a01100080551350a0741c80c807482c010 = true := by decide +kernel

theorem S244 : BRFrame.sub P3 P4 TB 1680 MM 255 937023628 625 937023003 937023037
    0x150105091f0207051207090e0f0109121103030906070e0f1c030212030906070c0206 38
    0x48180030341c090030054201800d000780340100c00d4121034043d0402e02e800824002d0000351510035907071030040100d40e90b2074050405140c10003115164210f0340c00e2188803c1401b000600300e45201040e55240516500c40d0140f655803071006803020030035036010000041140e40701380c10700038403104000d000944e8040036500150142c0701d61090015141e0440ba009800c0540402c48022444005100a8214540608840d8585400400d01c80c107100e110031010086503100f20850362108a1003000344 = true := by decide +kernel

theorem S245 : BRFrame.sub P3 P4 TB 1680 MM 255 937024253 625 937023628 937023649
    0x2107150905150318100c050a020105060303042103020309180103140f07060e030a06020a0306060f080f15010509 50
    0x210440d1f005015010980d99071f0000d02140d100c0604054607800b4501a4402c01d00c01e842c0d880165003020003003082e015000e40166454522102e01185c0900c440c7d007411705c03411407a0001001003001001d1a000428520000b41c002c1ea614400444c1e01e0b100140b18603000c100b0ac030040c0b80c14a5038148800803480d5400801195507901290000c1c016104500c540c501043e000d507400328038140942c4160b8402c50020102150590301c446001128503100c0762614100001449240d1003078641e016800c = true := by decide +kernel

theorem S246 : BRFrame.sub P3 P4 TB 1680 MM 255 937024878 625 937024253 937024271
    0x9030a060b181003080c1f090201021b0f210715090515031810 29
    0x2140561544042110781c02c1048004446640340c100340255800c0c2451590700050300c0b4080607104038400200034401850803c01b19081c10800c0802d0039003240600020382c001c040c14070f8101c1c018041c10881f03003091940b03101a403210b0800206500320f0a42668100003c2c403003c0b070400c0e12001002c0b031091481e0442071020200400d07081a02110342e42d004d180c0200004c04940146110310051240060313820012020340f540819a45040240080031010061800c01ca2640070444281444055 = true := by decide +kernel

theorem S247 : BRFrame.sub P3 P4 TB 1680 MM 255 937025503 625 937024878 937024883
    0x20109031d190810050919170d020d050115020d080a1805060109020d0c0504050906010e0609030a 44
    0x1e550745103100e040d0500f80c0c0c605004140010000300340241c00031410242125104c0d00da50f01c54105800359148c610800030140801e145021482c0002c3c038044402c060082055418000c642d1a0f0b4803145215000b990310600d04010b103540c000000650010710641d00154041544004511006600a0050950041900119600c64585e01500e8800c465000c100300c0300c00a00301c141c0d22441240035055001030014005100307584140c0c00b803601e502c00602202d00b44882840468900303030658008 = true := by decide +kernel

theorem S248 : BRFrame.sub P3 P4 TB 1680 MM 255 937026128 625 937025503 937025519
    0x9010318080703080c07110103020a0c061d0706021507030209360601020109031d19 38
    0xd80e0b0b54051810050030100700505054a04001000310f0300200c0d4171595410551042440c0245e680c420041c0c0c1101c1c1f00d4540350780a00170500e4460160340340480c002101d4500d000c1c035400c0d524501c0d52808242d85608442406036070034241c0c1d02c001802d0a01c070780d005190b00d142c010b101580c0b82c010048201001c1c10480c0c481d01d4841c0c00c0c11030261491101803013103a80700b1400d10003030290840b1b07582d00814142400b01602081c850f550440000d9607503d103a9524030340240c1c0c0e40100125511024 = true := by decide +kernel

theorem S249 : BRFrame.sub P3 P4 TB 1680 MM 255 937026753 625 937026128 937026143
    0x2403100b1306090816231c061103063a0b1e010608060609010318 30
    0x81c00c00c40e64036a55200e030058450002c3c584500d41018410700c1400f5101e0300b44a000c0c001c45500c0901420642800101035280000c078103408840220740f0510700d020040c030814400d190080d170424800142c0c25600e503141040018111076410043d04440721038020b0072240b00308175a640700b0b086d842144a0040500f0842c64031480c2644100c450b10b004512101c00042801510f07020f06068850345c0d02c2ea0700003039440740140200c9401058005040503120b840b406101e005001409107014000d800 = true := by decide +kernel

theorem S250 : BRFrame.sub P3 P4 TB 1680 MM 255 937027378 625 937026753 937026787
    0x708030403051b01020c0f0406090f1a010e0607080703090f031407052403100b 36
    0xc209100c010003100f08000010585181c0090003e4000313551400c41411007406040407031980c0000341c0d95940284002c1040100030310000c141c0001540c02002d441c00005284250040014401c2d4440d04009503008800f406c51494000c2540311020740d41c0001c00120104440f8260101e40090341c4140c4000552003a0791010559840b800f40714184000341d00701074054103041c0400c0f544641000c021703000046944411030b65a4883d520032086280341600301c0c4188950016903200d0080810303032 = true := by decide +kernel

theorem S251 : BRFrame.sub P3 P4 TB 1680 MM 255 937028003 625 937027378 937027387
    0x601090b07080d290907020a0f0b011a04030302060f07030b09131403070c0b0d0e070803 40
    0x4020b00c054600710200580c00b004c0480341e10142d60450004126008040603c4105100105124110f002d001a600001110700ba1041c1c0d420740901516600b640c14981d00c0c1440c11000c42030041004005d00003000040c1c1d0018000390f2004100d001e403011030f100d800c0e09030040c00f000e00d941c69000012004001588040c8001e85208a0103005141e00c20015482e000740c03a8845e0220113420440e000390b050191448000041000f4014035400051400030040000d003400010b4102d8030b01c6410008 = true := by decide +kernel

theorem S252 : BRFrame.sub P3 P4 TB 1680 MM 255 937028628 625 937028003 937028017
    0x3022110050c03011203050f0a0915080603030307080703090221070806040c030b0601090b0708 43
    0x18468245049000014005810710080002d070780092401c89065980000e000a0801000d04003115140102040a1236000380002c40c5195140c120f812001112150b400ca02001c3d00f4021048440380400e0700c03c150594802e1010910880c014031440b40c7c0456945000140c69801d6000580320942c55a500c0481d4103900786a803900d824180306034805000740f4002801207061940e1800f21916841c40301600300b440d2480400d4140e80305002c100000e0004031111511406141081840c55100c28 = true := by decide +kernel

theorem S253 : BRFrame.sub P3 P4 TB 1680 MM 255 937029253 625 937028628 937028689
    0x3031006211109030d030b060901030b03030f13080c0103111903090b010803070b130804031b0302 44
    0x1d172040c5601244094084500317051000350442010f000c521010350180e4880c004000008040743d0400900001001c1c0e203501000340040082c0503981c0030030200000300081c2000ba102428144480e01c07403040f42c6c55090141c81e04092081054040000c40e032402036100080c4035411a2501c0328540c0c55903800355480c0d0181e44200c1c3c2c114500400280d540c51031350580b51480d9800488180f406185885840b5140c1060400d04482d0b09254800001a03a41d1601328101d9140001400260720206 = true := by decide +kernel

theorem S254 : BRFrame.sub P3 P4 TB 1680 MM 255 937029878 625 937029253 937029259
    0xc07091d1b040c0c0c030b07020c030a1407050a14150d0c05070506070203031006211109 40
    0x443c2400a03001414103015609164032281a101e07060312006006889460000b541e0f544207101ea0b5201d050081d040f902c08a10038549803002d00e1040c0e071061010300c102000080c0302e1822011913002c440d213040260307541e4203003a001d00c45074528040070102180010022009640e201e4030035140d40c20502d941e815243d03806803a10310b0074808003030800411540240300303202c218810300c80342e14219019805d00c4d10b2905c0c6080e11061400d40b041d02c428000c81d1a00e1000d08000c0031203c01810000012 = true := by decide +kernel

theorem S255 : BRFrame.sub P3 P4 TB 1680 MM 255 937030503 625 937029878 937029881
    0xe0105191d0616030305044403040c0519091e0e030c07091d1b04 30
    0x11400181c0380382c08000c40c0e02d108201d030302c02c0400750380580c0d00360301804005d4800c50740c3c0b01d10244141404400d00c1ca03803468142090444040c9001030220104030009410300b4889919030800800000c0341c000c14440044803425920000001c0c1c0078090500319000d00d400c460025402d0488480e5004003595120b03901d034244030302c02c0005030351503e036080d82c0b480384984001081e0088002041070030256484415907018032030000e11003143d03081e0300e1400c010100001c2440014003005105082c20103 = true := by decide +kernel

theorem S256 : BRFrame.sub P3 P4 TB 1680 MM 255 937031128 625 937030503 937030547
    0x60317130504060b0f07050a0b07081503010c05090409171909080f0a030e010519 37
    0x541c0110b00541c20181e00b0300c148400e40302990440082c1c10314554a404407401c01601e03011000304090304000000081c400301e42d500003074144c4207643c4a0803291401040d070003850300b01d8a1440d0047c1c0050380600c00340c1d12601e0039800c100310715070091084094403008540c8860155000d2982c002c55507000b41d00341c4000f03a4120705000c0042885401034902c8494203006261514100c600007070811609000c50311090380200d041d60f03002c1c0403040e103150106200480c0508610700e48804dca03014221 = true := by decide +kernel

theorem S257 : BRFrame.sub P3 P4 TB 1680 MM 255 937031753 625 937031128 937031167
    0x909100c0e030c01030608061303030b09010b031512150c070204090b090f0c090613060317 41
    0x10401103049035907d114100d0345603c10004100d9014440000ca09070303500904d03010910300300341302c00701e50101c03000c0e4050410880000108520400c01e8a81e01d811454201c40b88403140310540b0b212991081000103116808880e400403c141d01c207040c0c200c1e030b81c0940c0980107000f00300050030b040418140c200c440c10a00d02a032810307070004031000319085000010090842c3c1c02919046c060062200c0d5030030500d0303441d603550f0f1800301c0850140080e18400c20800003059540d0390b01942243c0741c0011 = true := by decide +kernel

theorem S258 : BRFrame.sub P3 P4 TB 1680 MM 255 937032378 625 937031753 937031773
    0x31b010e06060d08030f07030f05090c190321020703080f0d06060c110909100c0e03 38
    0x540b000412408541c81e2130409100050512000e83e82410100f0002d6201340c3c000c560607090f0b07210030405810075214458690f0300b803525041c0308101003220340300d40d0000c0407415030403640c2c040042031124500b00b40800c0026041510f6034154050401e0000c08101c1d2031000700341142d05049403980d52007641c07681000711409a003100c410000d130384204000040450351420780354142100c00c03c85070f54540c40f030302c1d14080c62030313602e00c1c40d540c18194cea08289801ca103040fa0500400c40540300b10500d = true := by decide +kernel

theorem S259 : BRFrame.sub P3 P4 TB 1680 MM 255 937033003 625 937032378 937032391
    0x2090a1122170d0807081f0b0921030d0e070e07050a111617031b010e06 33
    0x1800080c10b490a581340001603a444600b1140254090320b2040c0c01e404403d82010500300c0450726001a00000b07851959841d03008040050600100f4190005252810384001c2407110100640f207a80c0803414010400640e0a080c0358101006608800c40c21148a000c7c8203074507502c08040d00040009031218211000b900f48480d9035056140705014000c1d5a1030300900400d40385d40c10205001441c0c50440c0c0c10410070a000041062591007081d11782e0717641c1c1e001030b0460082084590b41250 = true := by decide +kernel

theorem S260 : BRFrame.sub P3 P4 TB 1680 MM 255 937033628 625 937033003 937033049
    0x10b0403050f0a030f031a151803031207080403051909180902090a1122 33
    0x100c40c1001c0b00180d41701000c1c841c281c0ca00d1801094000d0304c1c4010030101c20f83c0f221002e85c0420366510300e1f203030f885551025000081503200348039035207c40203003031684901ca003100c01d030011418240050f001500958203190050300a1804908098001d00011903142d001031030340b00030030085041000000d0a030000d401d504000c2354800d019450700c982c00b00b981e1080c082c10440c14581c0707920013404003043c024280c0382041454000e60b10340c0025010035800f00e039103a0107681e1911400e4030403940500 = true := by decide +kernel

theorem S261 : BRFrame.sub P3 P4 TB 1680 MM 255 937034253 625 937033628 937033633
    0x3060103060b030609070c11030106120b010e06060a14040e0703051603020a170a06080303010b0403050f 47
    0x10907104d80740e100345403001086015025854003e45503200d07013040c000944440c40000d084841320ba000c0701c1800d0708021940b04101002000f5809406c401c007030080342e800e2017800703d102800340740b8007141440b031541c0c58100042d482400f624010301800301241924130301054002c000e440103aa0803505150403030000011701d4000c1c000c0c0e0300448000d030344050040c050410303c4800e40c48061301d05007a003542c49001245441050000314003900394000741c21754461035407401a18003085901001100c2c2c = true := by decide +kernel

theorem S262 : BRFrame.sub P3 P4 TB 1680 MM 255 937034878 625 937034253 937034257
    0xe03070b270d17181c08070c0c090b061c1a030f030415020f0a050303060103060b 37
    0x18440c0c2c40079182200c00c40c41640d0a03031401d400102411101c22103401d0265145098405100007078031754101c0e24042d01c0d600c1d07000980071000519014022606c04a03100c0d0401114104545485145000341ca20741913041d07000401408528a036034081c1000c9011900010b102150300d02c5009802149150a503440b24070a9101800043c034000020003141c083c0c2e844880b8105000e21000c8090f4908071815802c5102849030240c19011310901002460084000342e80c10301c800c9586116400240c = true := by decide +kernel

theorem S263 : BRFrame.sub P3 P4 TB 1680 MM 255 937035503 625 937034878 937034893
    0x110d0305040332390d030e12010506151c091115120a0e03070b27 30
    0x15140c0300504d000329034500300310100380014400e80c500d0707000c103900313510342d1384540030b10030050380c820344903000040700c10010415407410360145105168144000c1000a495003404d5200d100c284c4094142c484c0004a80c52031841c20041ea248411494050140e0601141195031042558140c03403881114001011580c001e00c1040d00811020001802154440c00550300c1780e8400442042900d0030081e083c1d440e0078180c0400d882c2504c8212000380b20004481c004442c4100506909000b041c04 = true := by decide +kernel

theorem S264 : BRFrame.sub P3 P4 TB 1680 MM 255 937036128 625 937035503 937035523
    0xc0308030403020d0201020a2a0f080c0705010306060914190f03050105060d110d0305040332 42
    0x7150802c81da601c0d04e00844030310b86001c1c9070b24900304198500e02741c0058142480b90f1204010458414001c110310000c40095a001c039682e9001074007910058095940401c0034040c040c02030642c001e90700504003a00801c0a2180015408160ac5010194010b840d24400780101403003404000d0050035040a400c2d14132080c1c200c1c854480e00380410a00400070310446a181c2060b0900d8821402c0d20090b503045004901d2820008881701c4040038188cd8030810141c840c1000c840c4c1c402e0100d0440c902d = true := by decide +kernel

theorem S265 : BRFrame.sub P3 P4 TB 1680 MM 255 937036753 625 937036128 937036147
    0x8040303051b04290a0806101b02010c14070902072102031206030a0c0308030403020d020102 42
    0x600b20400080c002c042d100c62010380343c100310402c1c40f2040340f041403031000d00390800c5040e100480c88800c2440654942008c48051042071842c00c0c1c2040340001070845102d42003044040d050000c881001401d00c81d440c2d10b0a0786403650320382101e200580c0e03001c18100039442440142c1e51300c94601641d2400011150507942d900005500460a041e8940c6102034190005007080d41d0620607a00d03000001440c0344000401107020b441c14030348a241501b000707820040d4100041d411644104001c249 = true := by decide +kernel

theorem S266 : BRFrame.sub P3 P4 TB 1680 MM 255 937037378 625 937036753 937036801
    0x717060603162a02090106021b0402030c160c03110603040507032409030804030305 38
    0x1032000a103120461001c00110241d010702508140800500f0b000103a030320003145200710075500c4044902a40300700c1c116400003074034a0001c40d8a0070301d420402c0909003803880003c2400060741c03000e401e404100f401000360462015251088003c3c941c421455503030068a141010f0f003082258900252040e00d0400502001400004090044a5000031b140040d10141203001d00051482040c0389059030030070000c00e080640c00030000f4419882524100000c1c0c1710790140354a102c28001c0d918403 = true := by decide +kernel

theorem S267 : BRFrame.sub P3 P4 TB 1680 MM 255 937038003 625 937037378 937037389
    0xa0809120f06090f21071b050411121005091807170133060f02160608071706 35
    0x2054503542e40c6074044103035903118440c50306910000140c1c0356154060052006251180c4ac0e9a03000002d05450b80741b007004212000701d0005e01401c0001e52141409039a105502012450b0307400c3ca1a0340160501145034468850000c1d640011214070a066001002410703480e65940c50303459404100c8810750244803000c090101c052103041040c00c5c055840154103c2061040e00c003840f91a4004121004035900301c200000e03640300c1000803d9800c644803400e4a280004900c545261401c0002c0 = true := by decide +kernel

theorem S268 : BRFrame.sub P3 P4 TB 1680 MM 255 937038628 625 937038003 937038007
    0x909150b1813030c0c030b070f0305010623041d180a0809120f06090f21 33
    0x140405458407440520341507003003d13107122060715030290200e0800c0d0008010300c641d41c84054001c03c0c0e0395848252204a01104604a0340b0a02481000510076804880f9503c1c5400b001ca012140000c0e42c189010b070387e03810f80704481030303004140307070605010004220002a2030720004409040c0d02c00500308401c00341da00d0b400c2d40e02c14540028880d401c10b000209035071400300100141c0d004000300f00c46e00303824405807255a40310450b4045405205600da4031280342d00e4070407500c80b5480c41c001064 = true := by decide +kernel

theorem S269 : BRFrame.sub P3 P4 TB 1680 MM 255 937039253 625 937038628 937038631
    0x2d0f1f0605030606070f080a17100506180103090804080303060f090c03040b0403090909150b18 43
    0x80c80c2e00705100148800c030b009201c515011034587da507403c4a50302041d4580002080200503035004040c0141c1070360484412107031038104909040001d034a80c81001e101020141d618205c22115901075009a40b00a4018000c1a25280d4420701161a9030040711440d2043c00c00b0100d4101c03600e000542c0310701070b441c2d0703011aa0031aa55076540c11000480548240c09014100c42c001518020341c0c0904014144500c90110508191844440c00d840b00200c8680c030401d000220011075011050019 = true := by decide +kernel

theorem S270 : BRFrame.sub P3 P4 TB 1680 MM 255 937039878 625 937039253 937039261
    0x3020c01050c0c040c031a06040b04030602090d0606032906092d0f1f060503 35
    0x18100301001501d05441c20b810722102d00d26a00c0280180001242d4a100070084d00604421710809072640f884401c103850310000300c40c00c1380c0c0004103480c1450b1654075a44000e4010145281d00112800070080000e615031003401d0145100c0ea200b4400d0082c49055680c0d41d1482510f030907180744179a014040076a403134a0a1a074440c03d031060043c400707d5025254a4004146154200341082c240c0c04d0214025210340d440340700340801d9050000c0f180d594030642621107080e12030394004c228204089 = true := by decide +kernel

theorem S271 : BRFrame.sub P3 P4 TB 1680 MM 255 937040503 625 937039878 937039903
    0x23010302060309010902060c01060305012316030908190824012106060e120a0302 37
    0x14080d44040c3c5440c1c0250b407140740303500c05660b40c14010b0001c0300da01800059024070b14078040c0d09551039059100701c1110780bc2807280d24074101c0b4540c264041071203c0d041942041c0684103030002c01e490080584210070101380b02079559030000440d40e1405150719034608130790f41d0300074010304400030040c0030a010480d1402950740394040c1082407031a4510000c0b01d1408144003810908803035460f4001c20002d851019540d0083c00e01d035464003c820f142c10098561034225841c0a036985010041c40c = true := by decide +kernel

theorem S272 : BRFrame.sub P3 P4 TB 1680 MM 255 937041128 625 937040503 937040509
    0xd02060c030f15060c0712050c030a0c0e06060906030109020a090f150507110a15020123010302 43
    0x101590102c3d080041c03c20712800d101c14107203000b542d4001404141c0c454603014114061010f441e4014105010152140480800107110348a004400e21010700c010980d55400b40300904894038000e01c200c002003e0f50002d0348048029900050b600022030307400700c2110020b00b185503c907440181070181c10700f8107000710010f020800201281103020b00070300d80302d803082c0e071341e405130820404548401e8603400c45c10005001e4809503003801580013000c1c841c1f4240381c850b41802c0c8662803c41e421a0300b0 = true := by decide +kernel

theorem S273 : BRFrame.sub P3 P4 TB 1680 MM 255 937041753 625 937041128 937041151
    0x3060f0f010306030615091b05040e07110a0501051501031406040b040603050706020d02060c030f 44
    0x106030003030504002404540d81d0f1039940070350740360340781480d0301000c480350034810380b00c00b8403442d0b00b20041c8903000458a4400d480182941c40340780105841c0c0203040300020b40c0c19100303440101c00d0f28071403c02e50342c0b8260340d0b290041c041e110555066070981c080e034141c001c240d4481d209010140e42e0200d4140990f81304d00040c00020b1000203a40b5030420349403a00031001c50001c01604000301f0055000f02003001c028040217040000280051003221420018031845017202450581c004030900c01 = true := by decide +kernel

theorem S274 : BRFrame.sub P3 P4 TB 1680 MM 255 937042378 625 937041753 937041769
    0xe0a170a0512011502071a03010909060b190f0501020102090f0f18010f061403060f 38
    0xd844426104904603501c004080505180039610750744100307800800d142084026200b950b1011501f40251113480d8503009010310214910f03820005400003400d00804106c4049480d48000106a5206008040094010300c1c00d80d02c01441c280b4400d00e03813030751540914150391041100c11001c1c0c0b5140d0004140d04010f8030f90710303c407c01020200e000742500110308542914814002304441e0b0381c0c08440c07021140c940d9105d8003011401e41090340d09101c1030f142c65030701030100c401e02c41c003604200354 = true := by decide +kernel

theorem S275 : BRFrame.sub P3 P4 TB 1680 MM 255 937043003 625 937042378 937042387
    0x1a06060f0c0709060b042d1401021609060e09060915040501060e010311040e0a17 37
    0x40d10025200300c07580807994100c0c1c1e10413a8054519007241ca074071641751880c030100a50783c011020f91405001030f00c00e00c004540080d250192905282d0306a507030108040100d2526605030042600c80c10303000b0001903960020b900640503140c4c0d080900340603544208100b40e4a400c280c41d050f000c1e80c40400c0322130301800310f066003541052107140007140c00769685c0c4c0c3c44510301b5800c0e00305540074000031403600e441c0c0c03805100b45e40d1074118540192070720000c41d885009c0c000c1d240c20214100e85c0d90015 = true := by decide +kernel

theorem S276 : BRFrame.sub P3 P4 TB 1680 MM 255 937043628 625 937043003 937043017
    0xa02030301090b061e070506181e0304090f0e01060603020a092711071a06060f 36
    0x1e0540c080c070380c10311003025208400b000000407205c02030186940f0a408881c55a01c0e034681d000d152603400c028504290b400b040c00c1e4448010100c2c880d641e03881000c015246401e03190110395065509051a004503d51182143d144005091142c0d4004100303619003141003042c1d00d480108084803600c07540607000c01410200042d0030581d00003070000d03a80148108000a801c40310004650800384041e00c81242c5442042c103c0d400c8028007512642005100310b00d001c4080c4aa256aa00045 = true := by decide +kernel

theorem S277 : BRFrame.sub P3 P4 TB 1680 MM 255 937044253 625 937043628 937043651
    0x10504081909091a090105120a150b04020301081e0a0c0303140408030a02010b030d050a0203030109 45
    0x1c1c0440507190f55120003c02e5030901c1000808003d4160b200c10214208101c0c064010b1100301e41400c140a802140240c684000c09005000184800a00304140c0c1080e00a0700d4464030140c0110354940e900d4074801d4448031410f2020804200c0440c4030418010300144002545400259110105240d5a026602d4032480b550780701c0d210b00c0a000000d5090000d00140000c94115000841c800d4404410141420b082030b4814040c0141803225045007640002030740d056034900f200010350f2807200d4 = true := by decide +kernel

theorem S278 : BRFrame.sub P3 P4 TB 1680 MM 255 937044878 625 937044253 937044257
    0x1e0b090d1103061315050108030a1b02030703262502010c0c09020406030e0105040819 39
    0x1000c4005038070180403600c203854204111414240040400da03048504000d0900e01034005004030340c10795103100c1c011480c0001c07540c022070b58070342e403104280038809900350b074040180c5c0c00380001e038021401015646081c40c45440030072074803104002c0e202e0352000100a60860310700c040d0101d88440980ea000750f10b100032a0b00043e01e040361034500041000000b818080b9102c04140d000c0c0064800c04da07010801251050f45180c200d0300c080d00c010701140b20510003921092009503038074402440328 = true := by decide +kernel

theorem S279 : BRFrame.sub P3 P4 TB 1680 MM 255 937045503 625 937044878 937044893
    0xe0d0309150509060f06040c050f090f03070f030c050a03021008040f021203041e0b090d 40
    0x2a00c078a1010040c86520300488441014200701c1c9410803000c88040302c054403140c000c40c6001e40c1c030404236512030183e0340c0002550000da40d03503c0c80d0a0020b1020400f941043d0740c1400b03040c1000a44903070f6100785804032882506034104259803041008403280b4039100107900a540c0300304180819100e120b00341d601600c50700640e60032480310b4002c100d0381c00c61181d401324142d000060501044003141c0006200e04a169032501d0300604140280d80140550fa041c0c0d401800d4529401c820003505 = true := by decide +kernel

theorem S280 : BRFrame.sub P3 P4 TB 1680 MM 255 937046128 625 937045503 937045523
    0x1e01030f153305010f230c0d03021e0304021833030106090e0d0309 31
    0x4210748002c1d030454901c00200121000302698400d00542d40035521a207a100444554007201416000905c61071442150640001c2096422100090616241c28118090103041c45095141070010039400710b4107480c50003011003054103203401216444d02e1450030b0b60014003801c9900c5101780009850700009290302030100c41803100060701075006808901d8070041079100ca580303814154025400c15200040c0103216000f0305141748202405000b004021510460042c801e001041e6061684 = true := by decide +kernel

theorem S281 : BRFrame.sub P3 P4 TB 1680 MM 255 937046753 625 937046128 937046141
    0x105060901121104080f070f0303051303080d2901140903070302040204030b1e01030f15 40
    0x80540c00300f121026602108443c4001800b08000c100821010815280d900043d0001501c0d0100842c0344540c03522006007030010118030605560b11a400140007550042010781d0740744510841c1500400317060400010140036609107600003224bc1c44081400201070b101d40444010030000c2884a400003072005a01d442481c801000585980c001b40c00110300c5503a03051103038200844c90464140805410a0705d05c2207042c010004125041100038030341d900540003012103c001d00300300d0081c115 = true := by decide +kernel

theorem S282 : BRFrame.sub P3 P4 TB 1680 MM 255 937047378 625 937046753 937046777
    0x8090f0c0127081618020c0c0910031b060e180a11040b040e06030609150105060901 38
    0x1004210341d916501c4130204541c0c02c40702d2060000c50560b98007424503941d03485c02520920049040900101140e2405101c40054000d202ca11010706031003000c00090300b03110030f03c0742824514540101243c00d0a074003415500c851500c2c584200b9a1060000f840c0c40c0c4101400d0344070b60708145c042540c0d004c6100500190243d80c00410000d0740c0030601241c28040036a14500c0f0702022011540d5585a003809140c4a0340d000c2165180c001ca000010700039810810010620010180742c02e44142d60 = true := by decide +kernel

theorem S283 : BRFrame.sub P3 P4 TB 1680 MM 255 937048003 625 937047378 937047389
    0x6030507080615041208180f0604092a080f0906101701090c0608090f0c0127 35
    0x5c441c0c0f9001203078460090280c50380141108040f0038440c44140e28020403c0c0d548600c010b03660482140c1c241da011000018448100781c2006402460398034100949407010001681d000c1d4120000c40d10582c0030010190070f80e50b032501e11a40390b035402e440070901c0480e0300100340046100c14003044204a5a1000050b00c015951103821110180360b00460110300c18809100d0b074460305024a00e4600c030094000c1c11a1850000020710b10000210718482c000c0300c0300720044020081111540c010300 = true := by decide +kernel

theorem S284 : BRFrame.sub P3 P4 TB 1680 MM 255 937048628 625 937048003 937048019
    0x1030213031401140910110f04061d060a020f0106091e0e0316030f090603050708061504 40
    0x600038100b11162501003205180c04078000010040c41c0c410220344c0c002401002c0d000380d5403507010700c001cac00824002d070556040418801800800f40744607030006011580400e5009006030414045403000940034060300700500103504042c40000e03090f0350325841d4048149443c040c0b0b01d456804075140320780c043c0b00311410011180400c0b600c072071650070f0103484010901d100d680014402c403400110b0034441c0c46017900880d121b41d10752950303864407410043d094414820703040800e18100070004181d0 = true := by decide +kernel

theorem S285 : BRFrame.sub P3 P4 TB 1680 MM 255 937049253 625 937048628 937048661
    0x30507060c0806101e03090218092d030301290309030a03060501030213031401 36
    0x10110311071004a0026000d01c0040d00b0b0030061240700c41c660341801001010f4112418202c0d070b00d000207034010103464100036400c54a03100e50500c82c04555640c880d02d6800c003824060b4640c120340c100401206000e80540b031035442c10500a201d41e01c0f0281c05503241d642449101e00d5952444458007031400317440c5c00c0d1a079844030f12100171881000101d025503118103201d00c008054800035444141094014010940c20b80480540c4900300e0342c0c025104080c1c04121f0910901401c00c080c0d9510050 = true := by decide +kernel

theorem S286 : BRFrame.sub P3 P4 TB 1680 MM 255 937049878 625 937049253 937049261
    0x2090a0b040204290a050423130c0315050315181f1a0a06050703050706 33
    0x43d22907440200c0880055025440b10039003120750001c0070709100440701c0103041c81e9031b01c2d41800e1500c107003900743c0581e07603401c0310050740048d070407981c5611141d0000100d01480407010a0718880f001010301264000f5182c0b13007609000050600c60380d01c1c005258880451202c081e05100e03036a001450111000f41070156160307004440010249035903c0c2e0b490310a440001508100d0843c800f152580020b02d218644c40e04210904803c001d401c0c0130b5806805114001e0403d50700d00841aa2290200e07 = true := by decide +kernel

theorem S287 : BRFrame.sub P3 P4 TB 1680 MM 255 937050359 481 937049878 937049887
    0x3030905091e0a1e0c0e090a052517010306020c06160c02090a0b0402 32
    0x2110441440002580900c500d0994500e441080c02517290301401280b910841600c10050350b4903014001411560200d82c001888500b06410303100608881c2a081164060b44c40d004045e40c0362018217418110003a8422030707086500242e0300d84210710500c1490780c00710b95840310f180041c41c5054080d0411940e0f05000f440750b424500040c8848680313a0040b411008058011900e5 = true := by decide +kernel

theorem cover : BRFrame.Cov 936870503 937050359 := by
  have h0 := BRFrame.cov_init 936870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  have h145 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S144 h144
  have h146 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S145 h145
  have h147 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S146 h146
  have h148 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S147 h147
  have h149 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S148 h148
  have h150 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S149 h149
  have h151 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S150 h150
  have h152 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S151 h151
  have h153 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S152 h152
  have h154 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S153 h153
  have h155 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S154 h154
  have h156 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S155 h155
  have h157 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S156 h156
  have h158 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S157 h157
  have h159 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S158 h158
  have h160 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S159 h159
  have h161 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S160 h160
  have h162 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S161 h161
  have h163 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S162 h162
  have h164 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S163 h163
  have h165 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S164 h164
  have h166 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S165 h165
  have h167 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S166 h166
  have h168 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S167 h167
  have h169 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S168 h168
  have h170 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S169 h169
  have h171 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S170 h170
  have h172 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S171 h171
  have h173 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S172 h172
  have h174 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S173 h173
  have h175 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S174 h174
  have h176 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S175 h175
  have h177 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S176 h176
  have h178 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S177 h177
  have h179 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S178 h178
  have h180 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S179 h179
  have h181 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S180 h180
  have h182 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S181 h181
  have h183 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S182 h182
  have h184 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S183 h183
  have h185 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S184 h184
  have h186 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S185 h185
  have h187 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S186 h186
  have h188 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S187 h187
  have h189 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S188 h188
  have h190 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S189 h189
  have h191 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S190 h190
  have h192 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S191 h191
  have h193 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S192 h192
  have h194 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S193 h193
  have h195 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S194 h194
  have h196 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S195 h195
  have h197 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S196 h196
  have h198 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S197 h197
  have h199 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S198 h198
  have h200 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S199 h199
  have h201 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S200 h200
  have h202 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S201 h201
  have h203 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S202 h202
  have h204 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S203 h203
  have h205 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S204 h204
  have h206 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S205 h205
  have h207 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S206 h206
  have h208 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S207 h207
  have h209 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S208 h208
  have h210 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S209 h209
  have h211 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S210 h210
  have h212 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S211 h211
  have h213 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S212 h212
  have h214 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S213 h213
  have h215 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S214 h214
  have h216 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S215 h215
  have h217 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S216 h216
  have h218 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S217 h217
  have h219 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S218 h218
  have h220 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S219 h219
  have h221 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S220 h220
  have h222 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S221 h221
  have h223 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S222 h222
  have h224 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S223 h223
  have h225 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S224 h224
  have h226 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S225 h225
  have h227 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S226 h226
  have h228 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S227 h227
  have h229 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S228 h228
  have h230 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S229 h229
  have h231 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S230 h230
  have h232 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S231 h231
  have h233 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S232 h232
  have h234 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S233 h233
  have h235 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S234 h234
  have h236 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S235 h235
  have h237 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S236 h236
  have h238 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S237 h237
  have h239 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S238 h238
  have h240 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S239 h239
  have h241 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S240 h240
  have h242 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S241 h241
  have h243 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S242 h242
  have h244 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S243 h243
  have h245 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S244 h244
  have h246 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S245 h245
  have h247 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S246 h246
  have h248 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S247 h247
  have h249 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S248 h248
  have h250 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S249 h249
  have h251 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S250 h250
  have h252 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S251 h251
  have h253 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S252 h252
  have h254 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S253 h253
  have h255 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S254 h254
  have h256 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S255 h255
  have h257 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S256 h256
  have h258 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S257 h257
  have h259 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S258 h258
  have h260 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S259 h259
  have h261 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S260 h260
  have h262 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S261 h261
  have h263 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S262 h262
  have h264 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S263 h263
  have h265 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S264 h264
  have h266 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S265 h265
  have h267 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S266 h266
  have h268 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S267 h267
  have h269 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S268 h268
  have h270 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S269 h269
  have h271 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S270 h270
  have h272 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S271 h271
  have h273 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S272 h272
  have h274 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S273 h273
  have h275 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S274 h274
  have h276 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S275 h275
  have h277 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S276 h276
  have h278 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S277 h277
  have h279 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S278 h278
  have h280 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S279 h279
  have h281 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S280 h280
  have h282 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S281 h281
  have h283 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S282 h282
  have h284 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S283 h283
  have h285 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S284 h284
  have h286 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S285 h285
  have h287 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S286 h286
  have h288 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936870503 _ _ _ _ _ _ P3OK P4OK TAB S287 h287
  exact h288

end BRData

theorem solution (n m : ℕ) (h1 : 936870503 ≤ n) (h2 : n < 937050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
