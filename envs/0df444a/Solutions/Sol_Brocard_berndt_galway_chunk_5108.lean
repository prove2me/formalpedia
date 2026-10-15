-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:46:30.858726+00:00
-- url     : https://prove2.me/submissions/b25d594f-7751-4a59-b30d-47182eed551e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 918525179 ≤ n < 918705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 918526429 1250 918525179 918525187
    0x2803200604080a12111002030906060d030906050a02100212090c0910121a070f0f0801030b060112060e1f1a0906161a04020f0d030212090a030f0c080d0306080705040f02 74
    0x850170f400c0001940f2503488040d00801800400c0c5010b005441c0c008004480c054a45a140d81e409001e6030154404e0300c050007804214540c41d10f000b8407981e081d40d400d180301159034142d44c180070a8416025641e8040c14400c1f481c511221f810011181801141c1c0840251609450300c00e00c0c8d0540b9500c0d504c2124201c88442081c2c0c80d0140e038aa14501030b0415880d41450800340b120000c101c1e04800c0145810045a07600400c00b0491003491075030804403c0c81c1009000388241f50a0303001d00b071164810403103104054204201075500c41900c0a80b5410040c002140d1941c41500d51740d08444817440f04035102c0100007040442c80e100e00100303411000760381c030507015050a44841001c82400d1092883d22706d100c3c030401003185002c48000f1b603046070403504110814410b0301e00a50b940381c0b0f15000c1c01c60385070008120301030750340f0799890600039075114841c0442c0025924188248600903c40e100c054803990701c2070400c41e4064017951054450102c000c12495207440200400380003002071100030580d00b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 918527679 1250 918526429 918526457
    0xb0601020a03051b1f2018040e012913020f04170f010908190f14031e0901060303082401030209040605180402030601080a050a022803200604080a12 65
    0x900e04419041c0c008400040d6441b844904e208000310b81e51201c030341d6090404c0800c04011084983d000490010388001455501c1e094466004180c1070482d0b000b4903250f0380304c0c03d45800e414100d04041842c2501d60081c04020b035510304050b070246e000c140c4605101400240100090214000389150741041213130016000341c40410300715030701c0c40000c0d1018480091400c4000f400070496940b0a20286060300c24810250340061840d8031740340c109400c808002002c2035400114034001c48030304000548130a401e040c0a0040381c02002140710072404151505e001441d21840007140d04880304a0800301d040c101d0314840118000e6000650869000e41da4800104035510f5101c242c032034401040b10078007820f04003170040500d00350b0305034008081940b10340030b1500050400300b1880542c0d80e064440001034040101120661038030480e540c0c0398901e00107000428003a600614500c1000301c46559020804500d00b031214500c983c0c09552840d500681c5a000080e102105100030034030280f8180d001d445483c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 918528929 1250 918527679 918527713
    0xb010e0402150f04050a240e1f0206060315040203030a26090c0102060c0306012106090e060106030c050910050307090314210403112101090b040b0601020a03051b 71
    0xd81c83c5007040078003c10148170600f4280b81102c060700030400c0c1c40340b40c4030442d41580385990201c010b4200304130440d418006180c0380c82c14900d60035410f8007640380600a0003a0000c0d541c0400300e82030b510a00c070b40074245408082c203034039040c001d43c0c01802071443c01c584030300d0030f0f2650104040d00035040303507061908202c0c40500c0e400d201e00401e1070710081c001414140000904e0b228026040d998800410420302c05542e81140c200f84404443e00302c0303050580c50403065a00101943c1e40003030b50351400c110f40c40320403e0006c614141a20819101086503a24076082100e103406800102c980042d80d85e0050045540030f0400745902244070314242030307007035200e603180702c020f0511070f0200344680d0003d00f10350550b4032110240202d400005025500b054595164510045c01250302c03640545581c2032042201c402911401c1900c1e030110b00244059100c40c0340c28494410b041381d00f56a008840070202d20150310115140004075050340d21503040c083e10342e2203803401078008103401d8001d2048001c03140b042400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 918530179 1250 918528929 918528937
    0x7120f0b1807110a030c02011d031c020309040603030c33090f120801650a1e090512030d051501080610020303041101110a0b060f0d0b010e040215 64
    0x400d43d82c40c46d4808080c4005030a4a51110907102c50b03000c090503a854648000907000128030840c030a0803a21030401a081e4150b06ca24000030b0740081c1401c40100905802c0100d40819a120302101500c2c862200781e50101030b160a0344040f0340704404030761000c4c02183c40d0404641c0354020006a40c1909c41684c40c0004201541100004078080e40010002c66101c85e038210020319055442d1880c1c0141721108004004440c200b001d403c0003842c0c188420119104585030180c000d208011200e024082000c2c51141c000000300b400050407604070052003030408190500008403500c44001c000e080104024500c01c21a18118075440180b1110cd00080d0a014845c0503201000c2485042d01c001000182540402007009010300301161402616507400012070ba80aa04042c2669500f4946030040f6580c4032511420384081c4100160441802800c1507628011070342210030171109100300d4184106030b12a05000b50402031808010007251064042c00d9034003a100400e00c5072445620b469004090b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 918531429 1250 918530179 918530183
    0x30c0714061501080106110717120a23041404050411190302040b030303040b0f1005210607080c0a14070c0e0415050f01120c03060507120f0b1807110a 66
    0x14a0b0010205a50300702d600640584101c0c5007050100e03280205c0036030b0700c455a1081504020000c040214503680911800880419011200d039444501c81002000f0388403901c4e003038a103084e04400c00515a080d41044900725108684500c00a42c008004c00c0020480140151603500400f186140590b07504164050705019082c81007107518114018401100c00144031103003c0e510400a000110b00c051100a903c5924240590b1855a40c50000c0381c8440c41a402690485040694242d4a0320202d0b10841c12441c418101c50b1243e031491b07011030301040c066404d1400d0880420003442e50314400c50702c4800c4150242001352805c10140c5d01c0c540e40c0d900903440500b402814800380020808400700300c041200784618203020302d040c01c000b41083d1120622488012500781c90140003040705020341e000041da0408800c014a14107154094091003c003030805c0001072606480441d15040c40c80342d18241a00900160b940044426040702014000b03081a42130106880e41300b080c2500400115001d64 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 918532679 1250 918531429 918531451
    0x12a211a090702030906220612051f120c0509161101020702060301120212070b090406050604181e060306091106031e100b1206180c030c071406 63
    0x111005003003403015a11240441c840d600c02424050410b80c00800e4416480c02102c82942d82c40f0000c980b2000c1c0f8101081500c41030f02081b00c0010714a0308a024280c18804032881030041d6030700c04400c29540c0801d010241c44050f0a40c50511515500c3c02d079004805101d180300341c480b2622100024101441211101803254611505c5c1e207001d54840000001d08258800035400e141203a8002175007030205009690041c42c00d5640c2400303658848000d0030406030a6000c1e5900d4940300c5821445960000b90741e280142c0c00e0090020722800d12008450444048580325400c078020054941c02030030703030a0306a05034180c222180c10b400c400c15104041c011480340c2c90000b500f07115481c0c03180c0399081d041c4aa07440790b4014010403444514044224240e52100310066000f66104280800900c21641001d1604100030915410003003115003824056034080701c102e080300f017000e502a01c0d030b240122020780c1d8120080c000319001e480c03c2409011500d124003860007204403000d180034900710013110725240d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 918533929 1250 918532679 918532691
    0xe0301050a090302010615140306010509120606010207080d1d010201090203100501050114040b07060507030e03220b250804150302031905010f030308041506060917012a21 75
    0x142c09104000042c2503441e0718401d900e24140c402342460703904c11081c422074440000001e0300703a03116000321010900c00034002404203081052295403150100c2c0d20070f01500c1158004901e80030300050038003400030700d5614103074980182c0860003101603800d11164195901c1d40700c00001642c040c028440c03500a01a8005587d600d044001840d80c00009103a440d80d110420042c02440000400c6412454006e040820075898904048009000030a03140105010200d00801a40d603040c40323040c0303400e620603460000c1719103030044200c051180842d0940c00070507060380a800d020303100400f40f01e00d13800350b0100b5082a6543d0103505c071214021a4500003e07500200704280b802946802200c40c0703100b0b44041080d507041102a107001d6001303003c0942841081e100260402c10f00f441080c0c46c100301c43c8018400c595070740350003401c4011180500c212408001840034980001481441c0410120700f89007101c0d040400b4103040120280b203596803c01441c510190304440100e0f040b11055840030400044d6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 918535179 1250 918533929 918533933
    0xf06070c0614011a071b140906031219180f080d0e011d040f0c03020702101b020d0303090b07020c0a06050c07030611070b0a050a14060a0303030c0e0301050a09 70
    0x4490074910341c0380340e4940420041c00805800042428001c03807051301a03682d00c40d142005c5d0001c2e0442d0710f054205c1300c136a6001003240f5a1418900028000170b46000b404e50303c5010400d500c500786883c400e07042c10b2083c040306803955082001044001c40c107013440068500301511900c5418002c1d00450700580544004018101d420410b8200c01d00192403d1071812034040d0008040542141d0394409400202e195020556219888400d941c805042c0401c4000c0200c030700680a0f4008005c1039106110351104cbc11045d50081e02c1c12605d100750345413150700e4854a9402c2110545ca020800c2d020107a4854000c800501c4082006001d5251230300181083d00d00340d4200001011703590440410840e00303000001d5450000600c000940350721031000310718640d8a880b02012405113407070180095500c4001d2044411aa9010f103000f480742c00f9081c410140b101b40c500440c4401502c203550012082c28003080820301c00d0b07202c402a45018906200c60083c503400017400d660003a21200c4440340e0316201802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 918536429 1250 918535179 918535181
    0x40308060f0d0209070f030f0603140601210f0f150608060a0c021b01030e06070503190c0e010c02040608010606110d080c1608040302150904140121050f06070c06 71
    0x9101c0c141107450024030201903001c04e100e5900a00071070300380074010900950b0107001ea0407040c004901500b0800001b0303620308100b054035058902c4411107000340d01c0081105800300e5031080117000503104881002d407032541e072440300c10500801992140071050144000030bc49001001c04140102d0010500c0f41c00d00c018039080c100c01515410030710f031411940700185a008540c8600c016094078000a01d0000000140e01401561030b010049025400c20018050f0f003000140d030091044c0e0b0000e082c00300100c0207140866a204200c1e1000c1074040c00c00070540d61080100342402c1e0f101420101b001941c0c1d24030071382500d000d6004000401c11f103490f0b0788103d8000300418003040100786007250700c41c104207070701e2100740c4500c1002c000710151480400c41444a60301c02c4178000d580c081c2c401d4100c3c070305446d0600725a0b0895407405204034204458071603500305c2d03603110134182c40a8400041d03006007110354960613020f0b5140d049809002e56840c02008034014401184a10002d4a45481003103092078520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 918537679 1250 918536429 918536449
    0x916020f0102250c2d140a03060c090801150302040b03072405070507090b031b0915031219090909080732030a110102030105240f0304030806 62
    0x3400580c418051085403003190996403050715403441510003842450b00b030084074403080c0e4010711964181d04030103107503800f160303ca145174200d516807003c1c95141c0c42d01011645600308140d2254407141d0380c04288049415507104c4da4590303511b030a103401c0c0039658084607030954004030101018442c07062804c10a500b028082c171542c1c214120060032055051030382105400c082505041c80c40ea00420000102c0d600600448080c240c10804480216540c0d0900c0c1c00074246484d201d50190181c203009000c5642416040d4441490040c031117001b55a9201c401c0c1d168903448048076030300d0312403104070841d002080401001207024204442d400181104006000c0c0c40301503003c804003e00c0c0c0402c1270082440e90040d40c408a9105c00041c0c503a103030030648114111440c0590403120703161a07a108460480000c01401c60103110340710940710206066006080340030911600d40c02c4a1810808000c803c1491110050025040000f0f42400c2c049d1180c1c2a0503002103408402144081c0188030841c5402d070395030b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 918538929 1250 918537679 918537703
    0x1020d0b010e031504030c0812010f0815060105090105070804121103072706030b071817071505071e1703060303160c05030a05010204030c0e01080312060f091602 71
    0x1c40c0b460400003080d540c8a0007021801001c49400100e010107214241080d08280c01004803500c0d40380440c1000d5014a0a120b1001e01101c260030015601201180c410078010090750006c131960765940064400f503004801450401c442040040d00003002c0e5030140028000085160307980fa10a4548050590103103507003035110746d026110070010020341d1541010b22880b003040e10410041000203010103403280d50402008001800f0801c100d25903c5401c1d2081441d1922810f426296188000c007184586ca0040b074529030461002440922019019a2820b10640c5001460516551904641040c201510300301174070a070b071818000d1100c12107444070000c154603c01e41c55800e1540c0001c0e6640302d400441d081e06640e000c60042441a04030b8903100900001d800d84040740304500d0524000d5016000843c0c8070000c414006c1040d842910394203069803121801503280c0790082c40d00302403920005007012303804403031042c0f444c4054440d401a180a100074070164001e200103801c0207814031844442c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 918540179 1250 918538929 918538937
    0x50309090c0c070315050c1c0213030b0c0a0e0402042607080f0616020d0512040f0618051603080403030503040c121101120506010915032702010810030b01031502090a0801020d0b01 79
    0x1007190580c8407042d1804223511501d60050361007601440d540a00c8100707620180218841c14204889020a600100982d2026903140c81564980da02004121302031401075408103000300d6813a00c0b8411044840e840680c1c18102102c60b0541ea480e11980352025a486c2d90745907800c24014030421180b01002580c022a1600291400c000d0085004005004810808002a4100c0c0100c2c0502c02000d0301140500d801140a00c8003c00072414001d148203c050100e516102c2d0101e107a0030f000d0300086040550f50700c00c0b20f252600389161400c490070b42020f0000d80392291810700005110a184120301060f500c1081d490b2000d51f02d000016102c008a811041d141030309003010083d6036130348141001d09440c50401d24000e0002100780880050100d1001c403282c2c031030446111000c10141c410001d0190303100342c0c1c4012031030360340560500f8051841d1000030904251000180002482801043c0018000322001403e200702d04000540b0001f40354004da0b102d950006503c460807a190141004001c02070074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 918541429 1250 918540179 918540187
    0x1c030f08181903180807050a09090803041b0f0609090c21021c02030f01080616120b2701060e2e020111040b1207030504050309090c0c070315050c 64
    0x40840d11161042c071800d4420a44a4407242054000d61880c1c0c80b8000340441584015101d441081d03890781c1c03600032107100c1c0003800f1000580b00c402d4011518140d910141480c10340d140c0b81d54003480005444407642c0403024100d03000c200314039000388a60052032595105d0044070b10700046001103418042c1c3c08400c0143c46000d012081c400c4091170403a40d0402400169150704210010220000100280305814000400c0c00780450b803000d81541038440c49415100789460310071172007480110041c0000c000c0b81c3c3c0300038001602c02c4c6a5000c81003044001e410ba00f0341d4001c1090040006d5a03014185481080820040c411541d0204418110310400d07210f0443c00340d941440c3d818461002903152100600b541c0c4040f003018402c2d0001e03a440080d9800c02c03034035541c84502d1222590841c0350020b612001c0c01c0e00040049110340100c50146800c100070314600440c000c1030103054140181401ca1864040101d812081e00401403140210b001e101400b100440c540f0b41801a1b4001070210240b0030303c180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 918542679 1250 918541429 918541471
    0xb07031e230405062806080606040605010504030308070507050118080705010b0102122a03032a040e06040207170a0201060602070e07050415020c18090d090b09040b1c030f08 76
    0x30342c42e0300840d12444107410012005c42c002d41300a070410742d0359412030030607500040c26080080e02c0341c0603007000c54080c000c10751540d0044605018038807018001031010404a02c3c01f80c014070050881c01d0094001090395003041640c40100da40c40c081c215107250b40042c803041400428402c07107800320024030241c103500e188050a80104c3c05041c1e0502ca0500402c4000b44003600c8000d001001100d040040c2c1b600ca2502403018000c0a107c01c04c0d51520704642c0e44801c965100d0042160195040c0c5030310340c0c4981c2c076030100340310085d00441007ca444941e80c0640c201c80b010f014020f0700141d1495400401c001e8100309000b401c190031a8003503103281c42d21800f130020341170304a400d880a44003101c01800d201d4090250407440c010624402d0768000d580c2e0f8110b2540350b0034000ca51481040030384111444a4204103003142d28030340a118804c41542c042c030010b0110300d0700b80c00000d00e002c8002d002218290404000d10140018003204401080c107070400d060009400c1400326502111b00385040100800715 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918543929 1250 918542679 918542683
    0x51914010c0921020405011401080a02030106090b31050a050f0612100b030403020325030c021509060c06010504051f0608070c08030f0702010f0b0a030b07031e230405 73
    0x240501002d542c078003080003c2d80a00c41c0e1510ba2441c0d0010b2050020356034844011002c11000031503140094010000108405a5030084034103c85450796201102803910072080e8180c0c2000348021000100c401c0a80384032041d000d01d000190540c10902d081540c41c1500700503802100ea4005030040a284815a07000d5072904280c8407802e10004004c076030340d540c03407090308444000b40e041044805808014403041c10360010281c00b051241a14250b03034451440200002e56420f41c60080000303003d00080740040c1006440011080e114208080c01c10490704002811600000c90403481c0d0350100c0c0040000d89014060381d601318086400041c151003e49040e1400385440703020340410301c030389200801d24203881794026860040d08aa05183c5a041542441c0b502200c16101000158240780c4031101c1d0381003611030510a60b40003072600802d60b1a6540707820514600918070020701d996000d027081009900f1303445111070300a08000282c5008442c05902030319060403a000101c0c0c00f2003040000007100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 918545179 1250 918543929 918543947
    0x2007031a060a0512010e010c0e100f02010b030304170c0d080f0a05040504050a02091f0c061a041404050d0c02130f0f0c0c0524180109051914010c 64
    0x203009920a16035940c0000700d0020540c1d0340c08241c12804440e0030100c13007403040d80060444500c500c0284002c00880174221500307681e4541986c0d0000d25084481e40e154000c0704100c14180c0e0038000480c141ea51540080d0854029922540790031072055030f00d8012640501c0b20400c146d030211402086a040342d202c1c00320320b0249001c401401c0b40c0004481030084d0081c410307600102002402441a8900242c1c18006500104041c80c0615001e014000302d2a0380c00f04a036141c04169a200c100045803505da85d006000c860220700403c5004108460b60b03a1202d0140c00065031181d80d005065080524141c1d00d0000c880800d8010400c20080100042c0d48046200154110000707010403482c04100050001b00301c001c043d0307100c1c689400d290071f8000f03401c60540c0c8000c0e4014002c0d07911082500780740c000d001d04421001d900d06c900380000190603240c0f518142250b100c600000007078960003540c801d0b02d0001c40e0400c0a060181c4035102d0303020018003000c0072203541c610340000d0082a0001001510701e0300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 918546429 1250 918545179 918545213
    0x303070f02120301031505060103052e18060611030316031a1f0906140313050703050601030803240d123c090e130201030e010c200703 59
    0x200300ca0000c81a51080200e00b8111502070030365a5a965a0b01c6c00c06054490481d50540140c00c00c000502a98068840c0a11550078103242c8030906070400d08205000c50f039041c4d01c480d180442c9001149980c10b0024600707103601045800600981030031009040c4030092400050301d0341c010020006e0b1480002800d0310491668103011640460b12610f260700300d04007042c080c1d0080314940d02c0185444103110b85078030156640c0c0f14aa070b100c3e141c80048401c4000700f40c94000740403040010641e0502d210088140312801a000e66054070380380d5440f507040140c2a070080c2c41c00e0344040140000207030000445201080c0840c2200c0350200010302192801c22010000740045a4080c0940141805888050520070b0030710407640078a440031086600c1000c2c00580814050701c24180c2200d058000da1012043e41d01720f0003604066a103500b02076640181041049041544502640d03910850900501210701c1c00740e169078640e070300c0c00c003100d5500b940508221289035010302e80801c08a00d480c844064140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 918547679 1250 918546429 918546437
    0x6010f030f080f070c0e060d0b13080c060408040e071e0e030c060403061b030603080d0f0908040e0403020d0815060f3f041e05071e2402030307 63
    0xa0641001c00b6240900200c0d02801403001546208102100702c06a0950788030740f40180107a01c41000b40084400c010308010314650143d070204d00074070110540c5040c0c00d03201d08822403509c84a41412400c06005407004c584c0034401203002d000e21416101c41c1a405646850030b25025805000f02590301c403c80c80003a01400250300030181591014080c01d074440c1d0018100e142d50f0b95880c03034000c00802058904034000503181c00c1310241d25100e4041c2408903500000d1050420300d1002200c40201307a01a2030020565a03146000300191608000d80010002c0c4200600c1b07e183c41d00300681041c440309594020810800200941070580c03280803001c542003a50865141c40e481e0b5031540c0d480c401c603040c2d402945200c0055071708440c4000c071091208901c06401d29070641504144035400182034030010000140d824082000752680c1d20601c081c180118100c1d40301c01c1e40c41d03240402e444101180f80b844040036040901080301c1020082c80004130055620100206a020084d00c0e4080a0a090200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 918548929 1250 918547679 918547703
    0x140601030f14162003040e1012080c101b03110405030a050d09090207030c02090606130306020406110606180c0f0415110c0102070e060d17030702010e06010f03 70
    0x82002d500800b2001445855400d4504050b080d8640d800d106020f9034000a014030010388107000310150481040940e440111b04290404810441d828070007071949a00c480071003800200503100105110a40b13000d0050b55a6403291924194100103004614150442c1892105015007080a00300e50824074249400240c03143c05400b540c64502c104d6100c0355141c031039580002d091000120f010150342d0583c1c0c41d065149d46d40c44a04405034003078102e0103000719001000c2040541484443c065020b400101203d141c080807a00340300519080d9002035030700542c0403030240400c81d0000d0840c034800620130018138a03458951b002a104041840030180d20100d04000f05007000d0590003500c0159210080141c2c5454441c4200ca0401d03580007a04000269800d0290300c128101243d084450001a4090f001550502e40d02604054014020344e0300170341880b2012011415000d034500c035040708036038115504c1c04c024000a080d501c41001007811504898010001807200841e00001c49034041c1c0c0001d54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 918550179 1250 918548929 918548951
    0x80f04030203060a060501080714190e0d03110111090321070b04030f09060503090606040903020708010c0507020f12030a08061801120209071d120c2e0314060103 71
    0x45014560000350984124802d0051850094010f41d0546000ba40e402145603a181c4c01140c10441025080701c100340b040003120800c0d50311800c420344095141c03c198112031854130105809003043e000030340001c0c60b8500c1e6205150301c00c0c0544c010000c2240d807041d040c060780000190326481441e08148403047d00200c400c00c030400c1e04007554540c0ba041988000c0c2481c2c40d080143c80801a03d10749000038050754008078038140104142d0b0b026030001030050a41d55944428031004050340c00c819000e500c01e40070009007010003400b5010100c01a95a9a41c544582d0320501c0301d003181240710984204003069810240200010a80b201641c403423130840329544815001c100140e01c05620b4120390500c042c00428040715100d503020200c0d10944141410fa0740300c4904540303200e81c80f2420550280081000c039258604134032142a0b0200e04c0d010348800008180001d08001900c006110708000e9010100390030b005d00c6145420030750020f04040c010301c01c6003600400303025002040301303040c15034682503100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 918551429 1250 918550179 918550207
    0xc03100e06030c04060f0306060806040818121c08060a080a030f09120606031a0114060702042c07060306181806050708090f15010303140f030406060f061b08 69
    0x100f9000080d0040104035280d1090b116405060300056841302e003010400581c00038000703403451213030340c000080906002160fa1814064103264840d076500c444036840c000c030502400d2207800b40b41003088204084c001c03240302c406001e0348001090548100006142002445c6000c10341c407561943c54980680b0340f140311901650058041c3e040340302070b079034030280c0c032020000550312074025207005000c03280c800ca82914450032621003d0280c1001c40f280350204600e113041010107040070f00d10041c4041a10940702c1703c5800e4039400106801d09000c818090001c2402d01442680094006440c050000e141410061810b0030011400c4000e11a0b0b10100c5980780010100081c003a40c0e440711080c0454285044010b080240950345a402030148581c0c0d5806100001a03640b00a00b648000b81090717843c40d1420340e4039407410046911281010030074009954110f200461040e445003000140850a11995031a00c03003041d000503084c02481c003200c08030700a08100700b2410380e501c5112581c0d218a8410305003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 918552679 1250 918551429 918551443
    0x21f0b010c05160e06060304120f260f07080c040509070e040e07051905011d0a030c0f241d010306091103040b06030304061e02120408150c03100e0603 66
    0x50100d014994200405000041050045135031080e4500703429141c00c410448280710035100102006d292140c00225140a406d040c031540c071050400c424034070010000d42e04e40c0401d0280315114040e10404000385040740068083e00a00c5c0c40c0b034000c03107a00e80b000b92013505d440745010300cd114040780740c001482d09105a43c0811316a00103001440310700034105d003290741d42c01c05004081c07241981c00d01c0c0001c0350001040240072194140d540e00840001405c0503d4045900c14506800a0754040c1c0800820400b070070070002071281c59603042c03940b40740840082c0c0c185d00d4144038103010204000c05c40c2226900076028803076696880c14005800860303600680040205a001c181181d0511615902d80d09040d0050b5100300c0c01003148000d642d81e500e04143c0c4a209e00d0080402090f4120742002c034132605101000c0b21040c1a004580c407e000c1070003504003a402c0f0b58007a1240e5804464540307000c2d50b003200e100b07400c0242d884c40907045080c50080d0408943c2503004050014440000040e040e90b401c21400e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 918553929 1250 918552679 918552683
    0x70e060702040204031a06011b15020702040c020708010e01180305090d0b0a1505040603050a0b0a020d02030f04050f01110904090309170d080f0f1b07210906021f0b010c 74
    0x11584c5903035a2800e440a0f80c4102c0b200c1e40d180c8070301000540e00b540108111203800c00d5a404643c1c61004079513640c400e50b0ba42c17503460310300c081e401c0c028080181c0340d41c07040c409000f140d900189007140c80d056035203027541e0540040c443c0c940d04154401b0a80290b07051910075665143c10081e032952403001c00f0070507005540a02030100041d40c01071040740b140076488641182c61007641c00c0d540b20745403005d22080d500d4a10004009503c007880d4140410a01c0b005543c00243c04240035107000c0c212008a81a40c20550741c1c04120b82e00c11044c0010040100407254a55180800034850003242d8507180c451400344120341802241c40300c0c1c882040601c1107000801510100c00348801c03e000580d0b0b00c6644184001007040816403003008a07a004801d1800180b080714401c0c03441001c0da9a03072101c0c0302c010621000c3d40c240002d0602c2071400003515580c1081051903172070110306051124181c000c00740c24159101074250f4103c0c180c40340901600740e41c030394074110004102140864541c0012036154281400c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 918555179 1250 918553929 918553931
    0x12040606050f060c2808041409060d0b040b0601020a0203070b0318150601030b01050d091a061c0206070c03021314010b160b060102191406070e09070e06070204 70
    0x104020844a5400401903800aa80ca5030342c5014110500419209040d20036181d41d120344048040411340031458040c0d204510150840507180b80e541e24010780241c0c0050b442000e010b01d402045044c440009540480100c1d0110a440e4440d202e03820701c03200203400502200388440c000354031039000f0080001c0311a13028040320505a554421841e05402c2650600301180e04408004d10151380050f4a1042d215501c41d580055120100151300400c0c4020010781801030a106008951a403842100f0286000b002103a02e02500c4085a801c11a00248114800c10141000392001c0007040107840c2c07110f505841607543c41d003241c108000f09501c142c0c0001e61041300441035800c02c205542019400f8441504600750503600e4a101700041d00840000d54283c0f90500003410124001404217900301c0e00600603140d104001401d09001101d5a0f042030302c182404540da54008a00ac01c80540c1c4003400c3d01d040c1134400c500d03070700017140880050702d13100c200404030308071041964400c0300f100c01103980108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 918556429 1250 918555179 918555181
    0x40b030304030f14062203090f080139080613021603080108070b0d050a06170c0a1d01330806030f061611030702031e1006051804050312 60
    0x141400141074a26001c49068105203495424044c001603070b07900514195040c02c0b104151081d01510181e101d02d01a01040080d55000828840040701680906040c00c00030904000450702081940000c41c2c42125100d412a960901c81d08001140d100044843c82d001c0b44a4039140001035070080d04c81c6090b403d4620000d8800c3c40340992403a0600c10a1003601c0f03030a183d03a40d90030080d8850540b8410429028810454000c2c1c165190740800c2e440b158004000918039282c03c65006005da0300d036440d60250b8400d07881003501c0d207441592803000344010190118400c000d18203081d640c0d001071003900c5235001a10b8840040b44103401400b168140c83c01c40300b4003401c001100040c58144103a98587c042e010301d000c40541c414000c551684585850448801480055082210714a40c030108640d92800207029243c01652f0a1001c0248800894075003007100b0361080d40c55051150035500c0300c01080c681082000640c640244604240100c421403100540d00d90824504600c04d54881c0b458811301c0358 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 918557679 1250 918556429 918556433
    0x10302090427021206100306050601110105070206100b09030304120f061a21061521060906370605041401090b010c03081303140301081f110304030c02040b03030403 72
    0x6104000e5690003140c0c2c4d085841ca140f9503007a01c0318000d552401005031505400d001007109604a01e41050062400c11069154405030f10f08640e015915040143c000c4000c0c04504600204000050003058004a107004d10302400a5501e02c03540c0300b009054103ca40d502c01c1809001000c00751010780000080c00b11001031070820f06603800501e86940305035030720300000c080c10340000303102040b1500f00d40041c551910788440c080400361a207500b00e5800036aa0070b030370304605610b0260b00c4080409200174001380c142100128100840103284161018003100c440d201813039032081074a481240c1c405584200c190600224010b002c26070817079030f00141080e440103090b5400340c0c0e02038102c1b070384507104020390a1110300441b04044070a9001d0001008040407a003030040c156190420b0510900340b200065529420800c00ca1b0026809035071342d904140340c1140c8012a1500700c00c14456807034010491a0000b0300c000400340009800502000042d048034411516030743d0010800500080440361100e0340d80c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 918558929 1250 918557679 918557741
    0x303110a080702010609020315012102120f1302030a0803091c020a05250b0309031e18030703031416021207060e060405030607080912040e0f06010c0b01050103020904 73
    0x54030341c00019885c1020019030110284252030242551032013103607108900780011038041195542c502104107804a80203001081440285001c48060002c4441450943c40503444c100c0d0003001c2c40c00c0085640740c40302c0165004140741010590050101d6101e40b40c80c103895103040c0c20071180340c104400340390880300c02c16000200a03e42c54810021900c8050003082d5446200d42e1180e141d810f03140d00c0c641d0030b100012442c1c02840d48007003801e04880c20071007404411110902c9100d240a6280e0001800210344480945e8080c00700000b50b0041076041c0c0b40d030f81c0c01801507900b1a2000644600802c07180e84144555443d0080e46400500c0700c40125032000a4a494881620a00011452081c0c0c1000541085010780e0704640d4010060701c1c19555042055a602000420001042c0240010045840b003d0b90281001d0142124040620316115412804a00024083c5414400e0b82100c0c07030000707191031f480981503403003e1a0158542c510719011030054040c12601c81080c00c00000c503003117800c2e48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 918560179 1250 918558929 918558931
    0x6090305071527020d3903020609060d09121116030819050f120103030f0206160311040305030414040b060a02030a0f050c0d0e09060f09130303110a08 66
    0x64030b0b41042040d56a6584030072948030700507030090000c0c0300d8925010030260003076580410740094240307005500c50740d403144010004045e0b06030000440c4460001213a0681a0320351500100c0f0a00d80e0f400e500b143c0010703542d8024040914407401000440440420a40d045504160b40c01180707080c0300401400c001e40010035010411030a44560141ca441d40a040e0180400b166001400c840c640643c0d0040ca40300540c04003a81814000c0400000c401d07090864000c103280012400c03044441c0d41145001460082e80d14240011544250248000009006030950764510f45040000d58405004592107050080d644007070b00c2e078000410002600e005920210300c0404d0b086904000d070210420801c40c82f40204204078005900902c000195280940c4d0844d4064803542001410096403030041464603c3c000d07241c400144004217900400d081260035150401c00072641826203072940c4001c2203a801e401880a100a560300e407040c818980250b000c00c40760050f24103581e030f641c4500310740a040004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 918561429 1250 918560179 918560183
    0x70609080c0604061a0a030206031b0423010e0f040e010f0e0309030d0f0206010314070b0a0f080a0e030f090d0b010e09070510082d1009061202030601120f0609030507 73
    0x41040500015080c50a104440e071110003801d54034947d09640034080c05800c002c2a1640120b40700d84038085c1404020003030720050507040710b240c8403450021154014100f17400f41c580c0c140162020205290340e5090340d981c2e1402820382d800954105c604102502400480f50100201407804501303240700301c3d0100007403218003015000c41700e00d0f4203030a80c201ca40e90381d0b089070180140c1255006000040c4c140c0020703448441003c003180c0c2c00c40e442c1d07030b40d018641c0c0c0051240400b24500d20b14140360b9a4110840303a9109030300c1c28041004e000c104400d40d4403807003110310100b0440e00001d14401c507651101c3c0605038540d04419140701c250707110365032250810804d8410301e6035445444000601890301582100e501205d03a6614056515140c1e400c00004040c81100041848944100a0303a21006905c05200785205d42d030000e015131602011100303c0b040b40e08034851804239140401e0142e14002b5925044800c081e882c2c14802c8a04e007401d00700c24113444002003080b03003000196000d0641c00405044014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 918562679 1250 918561429 918561431
    0x1811010c1b09200304020603130b0c041d0c041203020718060e091f0c110a0308061207030804030330020301210b181e01050405010c0f1202070609080c060406 69
    0x3e140014044001c1c0b0700e450300102444100005401070800001550300000c040d4002c000d503128955901302c90704000c4612103188000801c00700001a201c56900f11000303000c0415120604000307408003003d1086025007e500c580c40c1c1d05040400d4403c00810000701400804105450300001b40f42c0302030310302c0b840350012081d20039000c5401d0303038404244070101454000340c5110006000c10300300d02400050307024406001c140c0320b011030004014070008101d1846541c95001030715000c400c1281d070101040c8128001e071301c010740c24800174214004640c242c0740c050415215000c02c1c2100c3c4007003c4041300088000480d007007003a13101011241c02a5069a55008601c16140003c0348021013061002601404030242100450f0b10400050641c1000c1000b01065450722451080351502e5080006841c201c20ba65820802040c40307030038880c000d000b07203142c540204440d491010003032001022030500c514180e80019240108142c90788117107240c80d403110910380c840110944068980d84121019a00d207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 918563929 1250 918562679 918562691
    0x23313030e03150f0a02160b0412090605030f09120c010929070e041d16122f12010f200a0503040503040305160305101811010c1b09 58
    0x82c0780100b9504841c40620031010400c0c1d0314190040c8001034003504034980c2c0350382000301e441043d010b914010680d50103000b4030080c501701403401c0a12841c214408100300900400c1c1400000c0c0d01000b00d80d003040300c518002d00d5076203d0300c18050078481c0c11100030380c40b414000754075940124107411611806000d80341c40e4003c0b1312014000d45e500340c0401842409502c190001540050003104800e87e00c3d540070f0300001e21101a202c854400e81c200710320200c01948a4503940079003c10303a44642c0003408046140e9181c811459a8600b4000700c11809811049000300d601040340b54120300400b90140f00401c01d0f42d003050b8110741e40c4d00900701c2240180d907042c1402050a050402c00b01041c044c1c611020105261107a0440c0071945074001070f004444038003040100202003442000801181022060080d1b01d080ca189049450070304414600d441c01401c00c200c1c04070b010038944501c8642e0303401c030700742580c00d02d5070000481b800200000000c011301010f99452180b00503551352081a5449441c0401007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 918565179 1250 918563929 918563957
    0x807030c060f03152d080313050607020a05120a08070b0105010810030201082703030403032405030c0f01180e0912090603040807020d0605010902210702331303 70
    0x81ea00341102003602135402c0c0108200031800c03d048040c0f912000070032480c1c1000b4041c5c1803041000c5941c403210313840c4d00100703560300c2880c1c10040081c01020f044a80500c2c04140da804500e020b4501d01c55030f403180c540e24012240f41c040602c07111184950100303003d030341c4034190f1818056040082c024980042d8a40b80014120352050644a0940c1d4050312141d82e16500c0554003021241010f03140c0e405d90402681200b030340e01c410400b440c0034600c00d44011844454903e44030482c5c1060b014070050420140d2001c2046440100d01c81d0b0f401103003940d106298104850058802d1100304004e0084c00400d003000096283e0b003401214000d60710001a038000101c070310003500300740c001c4000c15507000b4801c00c007013000103107414000c0545030b102501c00c4404010741d0702c038042100c2c400d07480f54102076000110035445a4501e000782c451060861044003160410200007903648210100199071260381413204002407220703440c80f410700300b00d03043e984d80b542c588040400121180c41d4800c0b80441c01c3d002107499 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 918566429 1250 918565179 918565181
    0xd0507050706112a0102070c1202240403060b0f0d030f0e0111100b0316120c0e0702061801182907120b0f0607030e100305010b0d150807030c060f03 65
    0x402c2c0e28241a4054450010111300501c0020401600346640c20040900042d144082e810020003400c50034401031905801800b2019007901c0c0002c83c101c021075140c0c0304a4110805550980e0381090700020b1800001010800e07000d10319100780d03880600d1084ca1300405074401e18024844070b49039034442c046610b0740019101c10620840728507080c3c11441242d01c007412a0340c8455000d80c002170488440c2c00c905280e2a00c001c40daa042a02c0c004081074000313042c810b10f01d0701c800040c112805d80c08001d1810b1240203413200c4025154404941808104103206802500b21806c2080003154000380301210f80b90100c1c0d0108110342d402d45600e0541c05004107400c1150403148660b00a450b01188003503c1c00d0010014108003580b954030800010403800551143d0014ac40d0702d620a450340c5c40c45a0743d0404002d404040003803080105130500d4014403030a02c2620607664078040703441c40840c442c00b527030081c1c100c0c085144c0c0000c01140b2810400005000880311107500b100c4840d01c48080301d01c00b01400f10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 918567679 1250 918566429 918566437
    0x60512190504200301021611061201030516060c03320f0d0b04051303080a021314040b04050907050112020702060a020d08070c020d02010804230f0d091a030702030d050705070611 78
    0xc0b58203c0412254004500030f23080c5c0c0c4000c00c1c001010306290010707048401d10090401c1e003003034603e03901c8503054030559814240002d003c0c01d07860520701f00420055070700914400030310808814080052000050542c1400303052804040e000e015103032a10302c007000d1440c0c55000720300000b46903802d041c012801030a1501c5800d002c0c40c400010070002001c0c5880544c2c0e03c0101900100c0001c1d400c020215540d04090300b100050070664014015111500d4104000d803650814110b108034a417909100d42e5243c0011003000701c9500707007071100c102c42c079002100f0000c1c0203804020390020b00001c2da980c0040e9000c100700212030010349408140e41c43e191402c45a03085161380c003c0d00028a041c124000d580510811039003e8410200c00c18190045001c51001016440d00142c0d6a4041c1c902000c00715018481314015446038902510000e140207641e0b10620700d581d5040910300c2d0000045041c1910a0040b5428601c00e01c0051000703050402d0018041c0e0720103d010394445e0301e00312440800c0d41c0b44d00111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 918568929 1250 918567679 918567697
    0x2b050a06050604150309052802120f10180b01030c0303090f0e013b090645030a0806030106090207050d0305061909140a0606051219050420030102 64
    0x8101c0c55400a0203030300411006d10166154031030491782c040b1b07401c02e0f001c2c2c21801c5812007098038074500f2540306204030400022440b281d42e42200943d0001c035000011940760304084017002041010b46d4001d91240d40c40740380d074040c01a009084c008010310002e2801d00e800c40f4070950f106402903684c1e406103400c3c00c3c1c041c06038001c0e080171607004001000c07600e03985c003190100041d070341c1e001864400e040540b407085184181c0b43c080148010004070a0041c418264000b20071180340c40380020b00e44210125007d02e4400360807400c06244031800e2030508883d03507581561850304403a81c9000e440720180c5402d008454940c825801c081022890801c02c1c001c1d121174a5001c002044100e1000c42d05a0140100504040d004081d04800100221182d652030000346444480024680da010301c565107990002400e1300c14880c1440340400c952a880011105004035003a0b202901c1d84070001400c09030a0061040713502da60078001400148101051500f000d160180381c02d0010251500515083c1d01401d028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 918570179 1250 918568929 918568949
    0x60b1e03030d0b0a09050108150601020102031608101e091a010f0509030c03030d0b1201060b0f030405010b1f1d0f100c0f08040509100e0406022b050a06050604 70
    0x207410002900383c02044000200400111100362a2445241241d07000d0744210b000d03a00c0901c48094100c5060b806641000081c4000d41c078501e004a040031031218a40041f40401843d10700003220303d8a06100000900b0b081c014dc103103098028580744a81c010325000b486442841c180c41030f05201c1c12001c404480d0441070315200c2070701c1034145040e42c19030400c2c0c5000f034050142c4070200c80c482c0d81c184002d00b11110005d000040b40d000903010700242c81079404581c051680350840030301c500700f01c402c1a99449220320000507500e039164503045014200c88601c49400070340300c840742c2e030307454550005480421a0b15610300b51045842082040d580700c404c00c095401a8034403044118604241c2121466a00242000e0880c01c100d03507a1070b0716404440a083d50100000706046c1300601d000030029030001c40b040000081c09042444080d0f00c0c140260008000c4c50b0300040300604910200c2548070140e20b1203a95584406071005001d0140070125034103280e42e4035107003002c6418940102078074295035200c06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 918571429 1250 918570179 918570187
    0x60705040f061101090f0501020a031116020409020112140103030f0806090117010207050307140d090b09190e0a1a01020714040c170907080606040203070219080405030109060b1e0303 80
    0x1c0650740c8540d1503c40c41c0d05035413640086404200101c828103c0d0314819800180c1e18940315000a0484020782ea12407844a1b08020b0210720410405050020a4040324006400441840140e4180e15040c00c4400c03602d06006603041050b034170034507040c101c84c025190340b00000103808088500f070204880155001d2910001842071400084800441928480005260100c02d48802d80356803c483c1c401c40e000081c1804800005c54144034119003448030313042c03140e03a040c100002e116103402407040007801000c62020070f41b00311410404a200400c1d4041e01034203241412500000a4081c0c130042d20407404000329211800d5100003412030403070b550040c001c152a401c9108010103030205042d44420821640f0400c6101c5d0808006030b8040e03232094000b40313401c510b00411207040440c01805688604d10610801440c540c01051056003071b90102007549200310f081c60b114480b03015a4101035055881c0c103074820100400d580c08981089802c0314800c21050640604600a1504509654050308140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 918572679 1250 918571429 918571439
    0xa2d060305014208070905040c0b07030206010308072d0506070e01090302010302031f0b071205070314030603070e0a020408161a0c010603051002091801150509030102160c0503060705040f 82
    0x80e07440540d10f402800140d40035507603900c4c41c503d803a525412152006684030240410404d10120040c000c000300d18030039041c07000340d03240a5180d013014840a41101c1c40014042e042190f500c0f25144800786603a10224540394441004000074101c901c100d030940708100100f0030460103040c440713017600303416902c50992078115401107011b0f410203020401400142c550007680d0080307003448000513010107100d03140c40d040d2508000640c034603020010300038008100085004a0b500586503801c040c009a9900d80d240c407201c012a1500040d81d1154031b1010000047c0054501d50780c000b002200d040c1004c890360350b1404030151620a04500c00c0d03820700c48090003800381041d40c4101912000d00b0102c00081c2c07145c0c0d662200c07030502003404541404070345e000410a85c0c034600307a6400300c0c190b008840758948540c1441c00b9040010040c0110000340400070461107104d035800d404036145c20800760a40c040c072840d140340c450071441c1c06001e01440790080400040429100707206035002c0310070100307142d81c40307529007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 918573929 1250 918572679 918572771
    0x60313020301090f0311121204031b0b04060e430e0712051f29270102060c070605070e030a0b0709050a030b0a2d06030501 54
    0x90008a805540320f88020300071841c500c40c9045400e0082e02d800350307000c2038000c1c82d5060030010086024009424007072202000100080c850b4031560605001414000f100c1064131001c821a0300108265400000c10080083c207030051520700150a04840f0040b04495804a41da1074007000f100001c2107140261103080c445030780071602c43e1b0301e441c11003140d10745450501e180100110303002c5011a002a01401814405100f0503034001c150480c0302a001043c2d60f0b0110b00318a01d80714000c0380e0f4501c2c3d0880446061240c080500b20800040007654078403c6841602c03901d810b07400710000201214501c2c0c101075002140300c0d8801c07902e0740d190750700c0c05660b6603e41c070041002404017001c1042409040c04142c40070080e44400354018014208140f80021008000c075040d500024043c840d0403008100082015203147c2d00482d072500041a25128481c0307400c0c07040d2401c1c0d144150340c0314103d40c003034480080f60300941c1540e000c1c4009100391000c0c5c01c07071150301441c0e80b8001c00c0c00c82d00f50b0411007414091 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 918575179 1250 918573929 918573961
    0x21c030203161403120610080103050d1d120a0c0503070b03040f230a050d140d020d0b15070506240f0103090c09060f05240f07060507090e0906060603 66
    0x441c3d078039003000f040080390803403540d00400304400c84280301c0720030b022031850071074000e819031031903450040300b1581103543d52500d502019030320205006407405800c5071a48107140560000002900108041003900300640d903d45006000307841e001246000851700b81800b051080036940d130081010b145845654408880100d040740c00d48500d59a107015281c4111071f00c20009080080030001e0040740b109040050800d0140000c0d9070900c040b607120013003454543c41c10b40c0d0080700304000c0180c44020b20000400a40100b0061980c4015071908031000c0170000c1d00034140b400d0241d400c40750260f88005211451b0803041120003032240707104a01c1c50702441c11520a401040040c940416200e0707907540c4203008480150451000240c48103401d22030b00300132002200c01080100e440264400e041c0d201e42e080f00d4280382d0043e20789280001c018610320100c3e0201c2e02450340c440d204120600d0000d0000340940400c1c040c6484011040c00487c43d96000091403d000d0072000b031006140d915403592100401c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 918576429 1250 918575179 918575183
    0x230723061803090411030402130c08070e0f0a0303020106060801080604080702100509040e01020a1b020f042a02100b030c010906081b040807030b0f1e10030803090703021c03020316 79
    0x2000b0840a07482d130f1214003c001d44000e82c0566180c4074102841040002d501500c400100340b860035a002d08065440600c3c10b4000c19141403203543c01101801040000c000c4030303041500b103030000a0000816605621260803030340c16583e01540c990301c900090f62559000d68001d07058007020300c5041c0c00740ca403081e41d00e00380010508105240400000c0494282c80001b000310000b40d602140340c00c0c0d03903a00042c115000e800d03603034ac0714010384c0c01036030014841d4000000c080f4041c65440f000390120400700007941c014010900b6006000c2c0d211414001d50350f03490b1116600300a410260b8046660900148821b00f88070143c54a03c03005080500840c0c40e240c00401000070310100304800c041000d900d200900c080c2c00b6040c050225581541040c0807004406010712a46141900400600030806050a05290300341c40c1e10340e10300e88428000c0c8289203400e400c0034104d03500020a11840400029034035040f24400d4a1f2149521180e11160904403944080540941c00c108910a1a40048040300703001e14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 918577679 1250 918576429 918576433
    0x7050d0204051f0e1504092313060605060c100b03010f060f1406041a0a05191706241308071e08010b100f2307230618 52
    0x1a0b89500180c40c1c01225041080e003030840e101030600d50303035006420503c05401500d5203288002074103c02c1640d88500c3c030545100540c1c450300c0c1d04c0d0000180d02295100700c14403d040c401c90424460361416055000380444d001454100009418140130042d40e000c01c0608010b00314414041a004024003199405036038155a954040134001c015403003110301400200c220702c2043da081c001c2d440c644540100c00700c1d1080005100802c107504079400860580400d00c2003098944032480010350f8503024001d101c003086101208400000c03a0b010000038052180c454a07503a040d1210310600401800680540c3c2203541140ca0903065080c03d176001700710342d44950140303c00e0981e580d029a800c0500542001900142001018146450010460002c0d0400c40000c00c89501e01800048079407010081400c02e00104041c9103181a010700d103101c030106a11388411000280e1540c00700d220b03600c809400c881800da1004103400b50074032259100000440180140450b4551303d400d0201c10785070b440c00080c68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 918578929 1250 918577679 918577687
    0x4060c09080f150a02030c040b0f07081b06161b05070b12071103040b0712180e0109111e0c0735010b0d030e0402040b040b1b0d020607050d02 62
    0x4034010041e02d200c0c100c500c000f4102c4021844140365481201619240f6854014424004008407100c01c030740488030b000c1070b002c0e03035801c88148503200b600802ca0b000e0084280894010107030881c2c2141c908a01d0900030940d49150354540130125120200e240010004020b002c500402810307203074040210b40e000f08119811240e541c4284d4002d940402c50301d041801890041c000495000750010500076800c0026500300b906003901e0403160f00030910301516200b0313100ba98864590249c0001d00c0030b6002c061462240780d480303046e41038003094288140c0c44858540103801c4083c0c500b080075140820501d034428130042ca80d0b00380400d000e0300520300d04001c0d4018801d00040706181246041502c004c8a03c007640f180403028901c00032104500001c40b2241d0400c50000390310741d12035107040702c1c040e0b25081405525005c040410000d014541041c00c0e00240090b02103540301034400a402e1000000410139000010355651a4440400c0c002203000750340548017040301c079800381c2c0141036034045054005042c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 918580179 1250 918578929 918578939
    0x30a0e0303102402150a02090631140922060c1403040809150904090302011409010b150315090408090a06030204081b1504031b12080304060c09 63
    0x1503520588060008110300b40041000c81607050b240e50900201000e007108043c1d03540c80194888014240c152250325422001584015240e410f4070304840000d000b50b61901104a03128a0010100007900050382d98405540f4500c40c04c5801541038511400f1414501580c62003405140b40020f46610100c1d42c884c0c42c1600d804c42400c3c0c140440900a03000864887c112900290030480148002d0810800401c1040003160580c8111005000150303041044200c4c040011a61805045044d60380700342050180414145d0540103020202c5440051000540340c41d5007050894120221041d04810707040e42032030001c0d001c1c02c0034560002f001aa501e4000140038000b940110040700c2c00c840c104404a0080700300d04102042402402c0e00303040440c90103060a07681942c41611180d0780c920010020b48000094036031000c45003030b03503042420030307500ca645920308070792a40c60210814902245500c0005086c18402410398010380e0440c210910315112900c40d44040c010340604c44040c01084100060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 918581429 1250 918580179 918580183
    0xa02060c150f010f0e0c030402120f01021c0506030102070b0f0c0705031b0610081b1302032703160311030702030a05010f140412051c06030f03032f030a0e 68
    0xc880e04080c2c040e0300066051001d185400000b0f0381102545204001c10060024042001c4a0b042070701200c0201c0a540501c034814605002c0240e141840c0d400490741c41c5500c80204003101d02e08548e0007060209666030800c2c1400c0740035140c40a4200e01000307012815a6409011141c0c0008410180a1402e1070f02e444842ca158403a04680326117003000301c0c102d440101c09200c01d58124099003000b018441c5040f100703694590300c00c0b103074084040595a01c1700c090360301c803000040307021034080e1f055403240b90180c1c0d6680d40c15080390110389144c012150100840c0b6010007110a4140e890f900c982c10aaa41e88044441000090112400e071004010020149e5020804030010600c20380001c070300c41900843c84016a507119082485072041e030410310000994424480031513034030614003661076001c441d1120035074201d00c0080e403146629005c1c0100c01e00c980c0003641122680661014000c0c141078800c0340600600b014080000c070052200c99254142800d030046401448883c0042441101642418 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 918582679 1250 918581429 918581431
    0x61d0a0b0a091401060e18040206030a1d160e0c031303090504330b0910031d2116020d15020a03020c0705060901080708040507150507051b030a02060c15 67
    0x3c6455a018001001302d6a0f01201e40038100009545684030001170401c03d91081c0e41c0548000d108a0004c800607070840d04603400340e40050000340304044a00d42840215071100c44480408042200e0244042881c0340810060340c01207100b180385a2459886010030302181c120340e4011005c01080d00c4c0c1c0000c00d9903441c051401e0039080400c0203580248643c0481da56884c011500c4010000300107400c004013200c4e1019503410500646030740c5207504000c581200148004070312030017506840340d250300050200190100308052074115106403841811840ca031540034290800d50b5560002d040040103040501d401020799100715004140c6000d4906950180c2c0c02c6aa22500025804264000c00702800c0044000078041502c0743c0c2c0c070342242c24000078840ca00c02014002801600780c045020400104020307001440000d0600290310200780c00144540d10240f001e42d0203104052494481d220a441e0317880600c0001002083c510020760309020703554024205903100c5005036160101c0000c01c410f011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 918583929 1250 918582679 918582701
    0x203120412030506010905060405011202040f030305070308090a0c050d030c05010c02010b030709020a0e060f070c03060e0c0108070e011d0a060c0209070c15052203020d03061d0a0b0a09 81
    0x31010440c280d500400f1294000d107150f04125201204010315142c890848055510070702e8040c00d183c0402403010b000c1e1085a0042c1880e1800e03c1000050562043c046d044040c82a9a60049a210914807680c3c0c2c0807800c1c0c000e84030f5080b0150400003407401d044481d0b0703424801d0410b071032460b43d03940707650342112645041000503035140e0f03038440190f103002d10201c006442c125000314102005403900511080310308180780d020748000034200718100ca81d2000c0c1c902842d4801c1602500503280c0c9402400343c502114154500d2040c400b0f002900c1d13002d0510700c1e00c50003c40e608e0100f1040321500445600031400502040710300e80700c054111503202d80c003818000c0c080680707640107591081c0c17042c002d00c1800104460100b043e80d130b000741c0008603088204070a900b2003400104640c0c98100c0003119103902429031828141c0501c600c0f504142c2c000c103200d83d4284813914208200c5e551850b00e100c451458400d01e81c0d001c892107001650201c20751707003c00c00340e0801405a012403510313175201c83e0880b03100042c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 918585179 1250 918583929 918583943
    0x305060f13051b0310022802030d1a0a05100f0516051204080706080106050304061104120303050f15030a0602070302011401030804091b0203120601053007080601120b0102031204 78
    0x2400505050401005c0c840c5424035008500c0c0c4000024010218030100c00d808030494000c04800e80442d01c200103a494550030800d04210607400c1e25020142e881d171286032640200700382c140000341450801e40b000711801160b02c0d1108000407400c0111210380c480c0307101d1042c2a0078540d01902251040101c11900c81e4080760850341d0381e06200c0e40c145005120b9000104206c4a00011701c080daa0110580b604198020000704056183c19022403260085070004448941e40881c001d0030b00d42e041d0032890041d00e001e07400164549030380b18060312004244a0054040e441910f400700060715640c000c208090091000281200c40c46078409540306081c1d10513501707644046001d0080c03440c82e20415036080038080c40064016840c0002a490f8000c0e080c12001541204000810607400744045070300e0122100307100040c041d009506690070f10f031110410404510720000185c003040c041c0c01c0c014082d1105031640c0040303030814007802e40640003240c01541140000d110040707580c1c00898040e8011441911 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 918586429 1250 918585179 918585223
    0x60a05031b2805120d0c12200309120601050109060815032a01030506010801030201030509150115180302060702060a020a081204060c080c04150e0607030224010305060f1305 76
    0x2040011010309103081840c41e4214170032800070550001c00d0304e0070040d030002101078040c030071010a503002c1c7c200c10040880c4500501c0c10707044106020004203010071080319066000d1043c10700d00c903a0340a00f400f4150220f07401940034000a8012180b40380c0c0610301660003201c1202c01c0020908180500036000c9082c00c1c036030105104d240c0050311170884040280b07802c210701c3c5071180000b4002401807001070705040e6030304041408841c061180741e003104209802c1c4603240d659501c1e50b507480d42d8500000c0e000100b5081c514084c8051209100701141c0d002003160341001d0725602004083d6100b14820b00a5100300c076030400000315040061b00c01413441d03102d034400c9407600381022001e44114030003885c1000286800c00c81407000c0384050301e003900d4107019000e04c1205620010345041c2580841c0302d6110101140340c0b000c0660000c1c40308400350401c0c100840d00e08080200040343d500c2800000c0c00e030b400040002d130385108a03228242c1d1007406182260040380441e110382e0308128042054040d01302c0034007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 918587679 1250 918586429 918586439
    0x302011401080a0b0109020d0b0901030b060a060908030711060d09031206050102060702060403030e150c0d110a050a0309061814190503030a0504050a0b1905060a05031b28 75
    0x320035a030040910030040c110582e03480d503840e582080b05000301028180c2c040740c542d10028059100e000700c690064004c1506584a01381a102c1c0d41003220a54460019410017040c1c1d64170404505c03044901701c100441c10180146e0f02c4603409004110f9040d00000d0612420940000034080c2d41e1145001c0e44400b80d00290120080c02510302d580c1040b4155440001800b04443d400100103a0054061400144032800b812042d030074203280c002400c5141e00e10300144060280d51200400841381c05c05420003010407035000c601c1c9180180165180801c20912900107440c1c001e0300044030061103004005015200000c0009200d005103c0c01d6500645111020300952001c0085180e010014031404802c24025902c00740e4070302c40200101161900c80300880d080010400c8440c0d405680088003183d00d24094074415078030200c1602c5c000745d150820011946034244080b10348280e4001030f02500300b4514400c5010b2100c0043c410041d000341100520746031300c0f445000d03400780c038040e060050b2041510744 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 918588929 1250 918587679 918587711
    0x13060921021911190803071a060102010605030d0f090909051005010506031003021504090203070512130c0e1314070608180316241e060f06200703030201 67
    0x168040b44a41420b084154081071038144001c0e240c0104031030003400d0354051101c009030603040d940110224400420340404000650703002c100c54142203074603c0500d507120001282618114421241c050b00109490b9000c18400c01e1000d00074103680c00e020342c2050b03582c91581d04680741c070601560150000d8010394044200703409000c0c0180403c40e4840e0a604144c1840701c605501031200a11a008101047c0030400191094500400041100f19200e1600103c00791541d480210744802c101200340000c0c0d510690314228044980d08500d80007001030800342400380c12200035141c892407145046041000034004c0707030300108100c41c0b0409860a9490300f40082c20500000e001d0b00b2084120028950100200000ba10300c2c04040c1c0c0d00381000004681000c1074030450640340c42c0400d0001d41d101403c1c000b10340d0019000d4006c4280c00091864900d040e0200315000c6000740110400e00ca60200045841181d501000109090262136150183d4030403501e0840140d00440250351208400031a1601d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 918590179 1250 918588929 918588943
    0x50918060708010602120d0902132c0c010825030e0c03070812130e0a0501050f090601020a140c040504061413110918010c020c0301150e1306092102 65
    0x5942010541541800d0f40a03440b040780050225400d0404605a0820a60340d0018403925401074134100d00301d02036805101c06044041e00a4091810340cbe41905202c8442c034003c0d10140b00600003404050100900455100c030015240744034803003000c030a1010700c0307448a40301406002c1c030b52000203070030f50503040e4035003071607400f1454902c04c0c0c10980302000350100108200c00007100c001c5d589035039a41170444100b00c810940d00841e806004840c100804070000c1c0d80719505a0f94119a0505882c00020422515407000c07035030203005811012101e030004415850032684528140c0030794058241c0700022a00315582181c0079034040b6204c0c040d410305458020364490304005d07903140e461040c0300c0a03180c1e92001d00e15007240da80209a541c0c00076840b5500302c00e444040720b1003080240300180c181a00256984114840240b10303500c1e1200d00b20103044040700040454004d000000095590489003c0d070421a0100640344151034049041c00a481403680b011542000c1201d0522030040500003481c0c521 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 918591429 1250 918590179 918590191
    0xa09061d0f0f060a020705030f030424020f1b12160219030c0e0c190507020f0f130902030313080f15010b031807030c091a0604120f080405091806 64
    0x22403556020306010109000d13034040000c01003d41c5d680440e1424602c0c5100c4c0e10510540200003000744000c01a10f14080c04080d540490041d5407040000b00d6201284190020350300180d84c20400c80d07403800d000303050078003101c58860f00b6580d607008034008002c000d80c840d001802c403101000c68444114688000240c4024038480c0c0c4a6070150b00b0341d95540c960181ea4010041c00c80300c01000100454401c10844140d4034048420302020070304444054565000300c041248076071a181014200350504106801d00514002e15904401c182103242c44000c01c500311082c0c0e0140010001d5103079101c0c4030110500140b04c40710041841c041034401c00d07403c22035080126618480c80e03200403c0300100340d00990381c004241c182c21010040d43c911950f4034143d85948028560314095400040483c0b40e07600440050008051501074410714108024162149002d0f0034144c0c08401c24203008600e400e403400303607075921810103140341581307510000d2080041282c145100d5000c40c82000380080080c410260004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 918592679 1250 918591429 918591433
    0x80303060105071e0f03030207060e062a090a08060105011223130f050d090605040803040b0a11030309010c030c02031306110703140c03160b0d050a09061d0f 69
    0x204084000030818483c115001d072401c40703540c0511850030404a503801c01650b01a10810b410320080c500500a0340202006070b603041d1a110040310421008512103102e1880044e941d07400d181c2e044000358184148801305404101c051001007080c1d20382d400041c0140109200400f0b840d894140010300c0b0000d048000c4241b5802c0402039601000901444003044200c5030525001ea62404003c00000c46140b1014258403001400c1d4000d011020407040b9020f8071664030303901c2c601d48400701907030f0505ca1845545960780c07040108200101c0310b41c005e052a1103052400902a004825580745142c0065416a0080e5582c075916903e80d905481020b42904a41c00a90300f03041040100b400411400e1042e0310501589150120120350140180c1029590040f9120071100e071007103007541d84145240c0214020701c241140403c2c121407030b542d90700451f0303c210702e01072500c08401d920390090034000c2c0c4003402c0c003521030b0b40c3c11000403000e004480c0c041c6003000b2243c1c100d030385500d400d80c034000e440303190f1f01415 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 918593929 1250 918592679 918592681
    0x70311040c0f050f07022206080c01020312010b090a030206070c052110052d01031109040c090f0908040608040c090204050d0f020f04230702010c1d0d05010c0c0c080303 74
    0x65402070151444002e44d0300c406500d5003080d0020605100240c3c000e20900d00c0f400401d60342c0070544e07620500a96592004a40c5003048604c01640daa10810001c0042580c0043c010000303a44003a00078081800080c01c20400c09640e40c0c0401c005800c003900403245240d280d03d050110f1304004c0e0346800800c15803915440c0c095107108585440d5401886000c40d05629030001443d01194824100c0b5241000f59050840300200913039031401d07000a0000b16218070850040740030300c0c58400c000038050b41e0008003140e43c03145001400002004228100001130b911340407100d011a03030700d00180c00140000d0300c0d8040d070b510b054070302444001c0194101c003d00c288140b01c117010703d44880800b640c0711680042e91114034200d5000040e02d55040c1403400d80d009040070a511035407244203154018446080d05139203200c0c0c94002c0b081c0c1c241c94458203482c00050800968410b1002c1d0008510780c000005040c54402e0401516420300f91601c000145010a051071001420004100b00130002001c51a000d103080d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 918595179 1250 918593929 918593957
    0x18060f0403020d020411030108070905010b0901081617011410020a0b0a09031103030a0207030f03051311180901060815040b0402150c0304030b04141b04021b070311040c 74
    0x1060003980806401450001c0909003151030303540c0700e035030114400c9121035201e682d40c01c40955200e07824016501210b0800c0000a0000c00c0e140554541040507104d40e08155a1101003c8900d440c0381c85407410018103204500f4282e61030000c860280241d00c0c102803c0e800000280070800c40e401243c002154800c1c40310740007007010046081e800601c6144c0105060340c180c00e04846485004bd403070f40c011b00000061003880c440a500600c02d83e8420f40300c40c2caa8052848059007140ca0444e5000c100700500f04c080400541c1030308507a03004140052a02d488070148070140c81c10101c003142d107000039a41d29281440800c10800c010040501c8416829645e40740554414a00380300c0900000e010702c03504081e050041c3c0e40c60064540c2c885540c411070b07454a03600c1c1450321052105680945e1040501e08440281e158080350320705001c4008640c1c000c890301c030309051100a6000455921051800142c0c1c44a14481444042c005600600f08840800c070404200400c032761401801100380b020601902d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 918596429 1250 918595179 918595207
    0x3020712121b0f030e04060b04150305130503040306050406110c070513020a05120a06081209152701020c0d08030402090f13030c03050904022208070501172a1806 71
    0x76100c0c4c0c0362030300398101d0140202040c041d20b482d81002c0440c10010030041091080540e20401c02c01e5140e5090140782c81d01042c00a0b40f42d0002c0000d80240c1042005102052054101c250441e00c00c0c1400182d07901c2585403200c031908104044101d582000b8400c0260b86007a890707602050400000c2180b50886a10029105102d210003140c001c3d851a000101000302e281e0000c4028412a81940c50010b8200207100d1680d00580c0ca1900c40e03103903030604c03145c04c0c1c014400343d80700340c4203010b00421000103440081218890302e0310814110b10400103110020340345d81214606a900c02d200c0b450312402d0a1040040390880180007641c1c0003886010000c10345d4024003025891509410300c06244070b0642012660751080c0c150440d00503000099083c0d21300313040904074103202e8881010712420398440d2a00764441c00710384034841c0060701c003981c07060490506c070b15401d8000c0002c0c6006880d01e82101c20140c9010000070030b540584da000700d0048054100110410200102110b030301e40f801e444894240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 918597679 1250 918596429 918596453
    0x30c0a030314090a180c0201060e01030b0424140a0b100c06060905070c0203010c020f0303013b0711070e040f0602121914130f03020712121b 62
    0x40c04008615a01000d403042100c111810040c0103040c584105448215103114522540d040003040c51514500c61403447c4107110341d00585012600c01c802c1a440c58555a041c80c030302800c156500c0d0102405034110f007000c0700610000d80140000440c0b1000c0310710803003e030701c00020b2441e144a410807070008103541c0d69401c2070041c140c00d0300b010f02101e01c0700e081800041c00380e904800c0c8246d2400c03061048072908855108100c920881c02407140301e807003c10490b00c0c0d110788030386075140e58814001032000c94030000c5500380201130928808047c3e884444030200b4209005282d06180d0ba003081071103405948001d0070f40c02c0c101c04c140100411494810b0700091103000030009003c1c01024400042000f201d03404407810360031682c18041d01e504100300303034106d00104a0614898540750035800002c0c20404410b03d44996038800c6101003060a0b501d6240b15516281c20403011402011000b1070181140c070203a0180c0380c01103511102c103251080014050048003074440e80344900e0101d2460010310f4403040e207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 918598929 1250 918597679 918597683
    0x1031103180a0b0a05010f0b0705122d0403110907020312071e02060f1608041e05030d090203150108030d0e1903080901110306032a04020c0105070e030c0a03 69
    0x3000d01d8030410681401042c8500610620b03550302889043c4031107800081c16141c0354440412403590350811042c032881003590050154002407802408880460003404242e80c01c080001c2c0032100c98110015105000c0800c42050b00c0003040900031b010b003a4690030600c0c038080d5106a020b040c0070b00040d42d03a0140540b9081c01c00e00c03000014100c06e02c1441129084c5440c0350f85965038583d0560060746a0004440c150b401070800c200042c1030800f0b641c2428900051910740a515417590f40b81e2a401041002c2c091844070007031228040043c41c1007004240c0308010f07800000303410009104044c10400f4480740001c41d0008003005005da81c0c800301c1100d0b10050200000214008107500c0641000e0384a44910103400c56a6911402d040e0442c0d203091282500800804c07560a0101c180706080c00b040e5100d43d01640043ca0b02000006800703811075059500200c0806500021000107080c0d80c02a0251030407a5124000c0c0100a83c2100d0301d03014040046000c1c2210250440103e00000441c1c440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 918600179 1250 918598929 918598951
    0x60c0507091a10020d17060f060318120703030f09200a2d1d2e0605090f0a031113020c01021306080c27061306020d090501031103 57
    0x240c034159805a02021542c2c40b40076280009000801d407000e51208240c2c0160404a00545e0410002d42c02d50001c491145000030100341e01042c03880306014060304000d201c0f5a070b21410203000c0d400710074104481847d026105000c0e40c0e541a40e0301c0c1c024140d0b11000c0d0f418111a00744074030b620018100d5540c404108411081d003007003040c006000110300d248540c0c4402228510106a003d081d469800480c41c1170b42c0f00155485407564403170600110310302c1c141c1c055803e07610704070120344000110198010031503541e03030311401c41441860b194003200c12a035200e44040b0f5000115141c0038140340e00001d0b8907820440d240716020346181c0768820380d5001d08040500c646035503140308400d400a035041d5086050070000854584030380384501968000f0343c0c00340da0085071a680014070428220800c41c0c400c10090341c0303038102e4108800d1140940c210121420740d40a0401c0c00501e014400070040c003030041211394000c00904903c1400900030711440d0300310030704041c10662100040e0620300201c80c1c2000841c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 918601429 1250 918600179 918600191
    0x12070f0905150411090a0509060f060306130606050417060708010b090a0317092b0f2d032a0b0603030f0301030506010503100c0824060d020310060c050709 68
    0x1c00b00b08510151080990b01c01e1410b000f511070603001401412004009852140303c1c01e88600401030760007022205590311160281e902039403414140d01031600070201402915500d000110380c2c0b41652000d412013000942d02080400c00000d0a60031180300702d540310302420a43c107085800605421050090380004400050103070f61648410450400540d040000094041420b00200000740e00c00b0f241c45100701c1802c001c01859044041d940703403510080071040807100007580d0311034840d151034080541d4201a464411102c02d061a03525040c0b201c85520110641c24640c60080c0c5001d814030380c0d80e0414802400103061080c105e85ca4070600a40040c03d01c216546ca000019185119826280203046400300001041020009415041e110100e0035540c1310001030392120202c0c0c0c2c40350200d1002804440c041480900340e103040d0034100c0c2280310000e0810a070700f0301040c1168008a0111ba105a0002c100300400703030300303901180150001e403420301212903071522840da03188054020303020010f503115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 918602679 1250 918601429 918601441
    0xe1c03140c030d0f0c020106050102031804060308030408030612061e0408091c0b0f071d03011424120312280c0e12120702041d0c12070f0905 62
    0x80581d60018040000c5075030341c140404a01c030140c240d15800c610301c5420703d00c10001c100c0c0107020b10340030341d14103038021801c0142201c004403c26141200e030715040380d078030b00010001c1500600110305c01ca0040c603015542e400c2400901c022140742d1002c1c407145410200c248685c0080707000280c040b0f030119802c40728881d02c55061120481c480e80d41903a0b4031121140b49041e00c0000d540c0f200b200540100101c44080d61004840924240100c0f01c00d0000b40b820106400d201d110b14680303840240300a8000241010a002c501421203c20768103141d490401c103401c1c000c103407102400c0804580003680c3c0300f0001c0c0712807440e19640f40a024600c08030459120002800d00014032042c00d0b02d20b035624840e2005c590068511001480d4241003e4001464021010010304200c440c4c21340766140500104041c80000701c45481b25040340000300d81c0a81ca5036001403401000300c81806940d040c078406028912424410806807103d0840fa4042e69005190204007840b01103000320201c907080351000c1003a540300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 918603929 1250 918602679 918602717
    0x30b060f030304050a170601090204081c05091e10050403080909040212070905070905190504180b15011b03050412111f030e030412021504081005070e1c03 68
    0x150700300c1364101d04503c2c40003480200485002070450106401c1c1e030b41d01d98a03824041d040e88210f010301c11007580f001a200700021545000010034801034a44203003000b04140000d100c4403c90b04d600e4144c510032109070001c070b00c0c2402a00c85c1d403684a0600c1440c01e0325650720780f00d031802444416441445d40740001170541d190080b64035960b8014105072903105031220800402840180d4003400040c140d05404106420104a84240400c1c480e000d8500c00f8500010800a040480505264101c20345091400a900111321500420454040c0c0501c03028800004140302960428414903a03200350b2404082a0000e0499042d81d000f4503d942d001400c034241002c0400384440304a0700305103182402d82c403468403030300c4220440c41e95580074040c009001c24181e50f00c0c0210300a4092480540200c040145400c8040f0f480000010b00c3d183c1c2456a43e021103420b00c00000340b0380310354035110780410041580c81400840100300854403002d0610015807035100741d8889510080038400240d0307258200310302c0c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 918605179 1250 918603929 918603937
    0x30e0717030f0a120501050a081518010903020f011406091501030612060504060b0306010602030d0b12120d050a0203040f03120b13060302030c040e030306090c120a0603030810030b060f0303 83
    0x1440380e0b440c2e440b4a400c00041c000142c00400a41c9a46400300100726460050b604104403103610b002000014841102d00785d40740d1000e07010460100a40c0aa91103909081c000d00c03100c40d000f600a800440c108105482c01e5a00141044016288402c100141c950300c42c0c90b05904510a07502c11640c80400000680c020311407500900301541c0e03110650010842150003980c0304510802c0c00b07025a6a0724020b25988284c00c0c040c210240c2c0040c0080c009801c0564401620030380010180c002202c5182c00d42c0b81000d5040039000b4107064001444400d84c1c0d1a8042d0580003c1c8601e021172942c5040d44814407a1030080700e0003010060307840310440000c016600a403040340c80080105418514200440c40107024a01c022406802100c8100075580f8007441401c0030340000c04080e601c1c42d03990034100410103200600030b211410092000c0700010740440324161080389032000c0003403601d0450030040e0150340014840000c046500c2c10600c0013641000040f50061000e0305c8000343d200c4044002425809 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 918606429 1250 918605179 918605197
    0x1202030f0d0f0c08131212020607081602070f0b03090f0c0607030806010509041418120a080403090f030812090f070905070e1c02040c0203030925031208090d030e071703 74
    0x18171100c041162203502d40348a06e5030b0f1045440b0482e103100c1c034905a0303c40e20112400741c0814040f43c0003a44c0c0c00381803d01c41c00b04940510698094030b0310340c0c0b410f0700180016040984015008400c20054800400c03e0900c1800000000c0c88655010340c00208144075500c0e000f01040004404101140d00400654101281c024403d001007403029401c840c100310700310ba4055030001c1c0d40c500b5a403144030105281e8002e521010340c003807270300a80e110240c40c58203014200320100680550700003008030082d00c148000c0d500c1003014a50720400320301d100d0350001000e08900c0040d04200781a1610050001ea03aa080790032060001c078456480a0007602c141b21032026050304181c81120008000030fa052550a0a5108031801c2001c2404040226601d00013252a800b4650040d03651100c00545801001000320740f030f1115080154484c1d0b28688090a0703025038a0110701c204040c4000e40c0d03c03d001d07460703c0701843e01c2c042280c040e070a041255a0210740c8904a40c01c40c400c0316a840c0c2440c00e100b2140030b50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 918607679 1250 918606429 918606457
    0x2032208092b0f0c0510080412020c180f100509040b06030f0f16060c0f140a0f050607090b0a021228020709060509040809100210061202030f0d0f0c08 66
    0x82c015081114079a071000000b1110300354030b8000428036180100e460282d0082030b5603140a2a07485503201d00000103074804c0441540320b003000500c001d682c0c11600702d01c1224559010300c8141000c480f10000b00c40080d0204142504c410002d0000e0385032081c0c060750068201441c40416121000441c0c1000b6104030b62500b81d00071507d256a01810003d030f00028400d0304800d03419040c0e903c1400300c07a9110f400308024516910408100b01185400250006c0c20143d10b0540e4440c0f01c040d0b0701d030721105404050864030b641200040081e0542c110035020000e0126019891402a405900a4640a00f16044090840c1c041114000001d2240e5400034001c011441c40c1000012888040d6690380c05110f03100c0020308001c40811182001e6030480d0055503c03d0100e81444a075604000810751700c06000c6e021482050f2100341272002502841c8002d00300001c0310000442d0900502d0300702492420820342c580c2c8289100c1c60303600e501120024120400c0d20344461b0766003076403516801038850074030514110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 918608929 1250 918607679 918607759
    0x60d050406060b13060210020301050f062b0c031406240705060901021b12030a0b040e070612140906010b2107020706110c0f060c030405060403060203220809 69
    0x856181320b601c209840581d021140303c2d408220426040e03110074024980c002d401d442c1554041c1c20b00c07101500f0031030ba6402c000460741d031007420443c501040d000e510180c0b640e220054002c1c8540c0501c60001d80040340800c2d03944901e840408100780c460200000003940c0001d00a8907640940310b4151641b041e44802910785508140d101c0c00d01075040903031080201454040042c81a1900282c02d181c11010b6400840c11a0303166603281006040030300085401039124580d410305480300340180f41c081d01840d21201c080c030703280005d07034401c03510f500c1c00a100c210700c41402d22a540c10300044541c11501d1922401e40d807003900100303014500724003e8124010004020501c860190003095100a99000c2d0b541d090700000a104c0d0903544e10340e0b84003615049805804000740c01d0500c14000e20807004500203c0c1c0c0380c43d6807400440c0305a40a1f078426662180c3c044240074070304680003090b041250001c0c0c81d04000b41241d4480240610920456911030b44011041d800318035401c20000c2401c010180f0030b4050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 918610179 1250 918608929 918608947
    0x8180f1501140904032a021207060f030204030b04140a02060412030f1d04050901290a0801060b040b0309010f050721020f04090207020307360b060d050406060b 70
    0xd42080c000c04841240c0d01c40d540d682c2d410b054881500c0399400d9640c0141c0d0b0800c030320f9901401e904400c500f46404a0039100b05001d43c44003000b1040360301440d0000c0c0400c0d440e00300018090300c0041c40b61010180100410004640501d40071078009800c281d40144600084c000d1619004c0e0290009400960210300000c8421050758072072030705030190715080054401e1140c210f4003856030050b03501c2c2c7d948140650320598140350380142d40c418005000020300d0260891040700c040c15040740c1644401550b06a01c066042c40c2c00d0100050201000a114450038000c40f20700324040c50044c035490100100004401c0034094004044c11190040c041000e030600d130314010300500d4090800b4400c1d003541040d1014108061003107441c030041007424682014245103c40340617600101059a241c1700320704012500018240c034a01245510101810120300400c800b08400b0580c51045419a881d2400760406900c64004841e141010036034009020b41d29482e080c001085650403803440c1078004a80110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 918611429 1250 918610179 918610213
    0x72010050603062802120108070f0b09010c0308061909060501120b01170703090b1e06180c13030510050613060e04030516140c041815020a1704110f01030c08180f 71
    0x151000362220031000c607191994074800c4c1c850cc442c0c060005040510850129210720072150b00600010401024511702005290304580c642d04800020ba985000411a0307603040442040a4108150b041c04251080c5001034074000020742650241110940000d203282c7c8650310550501741d2100d07455029042c400004055085115507080340c5400b000b010481c0c83c6400d10102c82e01c050010480d00b0705a031040550343d956082803101100e159006070300031001030800d101d61410081032034000a801d04c6d2032801c00480d6401c43c15101c030079910f800005d0010030384031150070340e2094040c144181d84601c5400d41c40c030030104c140e80182240354203044211030f852000c01d42c000b1905044400744582d110362440107152000d400c01c0180014140004603d000616802410010701340b4113040c0030b01c40204802e1142e01d00204d07402c65540d07000843c4031810703141c0313049401456503007841c0c20000307658800006020f818000d4030141c100c08107030000300d4030f8030010401c01520300e00c1c03130044d60072003810106842 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 918612679 1250 918611429 918611443
    0x20f070e010f05011814060c1b0910210201050f070c050406150905150c0d050a02160e0420031002131502030f03072010050603062802120108 62
    0x46116481d810001074150f00c150240041d90001d041780441c0245000c11040f541401c0005503030304400140038607519150b062150004c0c50846000b203004800300b0344100560590018011400007804080610084202581a04070b08541001e0790301c00c82c0c107500058802e40100d445001030210300140c3c5d00c003000312004000d4119038040d0341c02d1042e0307900c40c1c407401c8800c045402c0701c800056820200708400d2800109030340f13840b0700020a00f45050345403020079003401540c01500c000b00d0030000d040841203504011007200741210760740f00540c40b07040070788003400f4100c00b1304050411020400002140d424210751013544002c01022a29080c421800240194100050499500880e504002030a0107244044850180203502851505102031440903031500081c14241c10001c0304624480b11004203401c540c64914400006d061004a86010100740c0340018030090094221200b4002954600401035405002c1148501d0b0310290b903404900090040796420400c0d0b060140000031200c102280740 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 918613929 1250 918612679 918612689
    0x210904052403010c0f030f11270307030f23070f0501171b070c09050f04060b0a06081b0c030f041d060f040c0c12030f0b011b1101020f070e01 62
    0x2052801092070209401c803030750a190300c000b04a880c10340c114018400c0c0c3c4009404110840005042010f20100400c00c5d044802e041554900540407c03994800d030a020555810381100140515070450b41e60b0003103640e2180c0010708039070780c420000d0b04142c01ca000c80d640392003d860864800c02e0352680c0c654184c00c5140726141c08911702070204070f05150200c003102e10401e401010a404c01003418101592a8002d000a542040b02400e0110f1100d00030700809000314072065030030606060a05100048684006665106034844e1208108890b000b1040c182d0107551541117550041c803042109200f0f10070618485002d000008004840c5480e2401601c155203e04020142c0c1600340b0000d01200786d02902c0844d07008ac01d140f070141080c40d058012818070301b858036040c079501840d50344140303d27000803a800b1070201e42ca40d0000c00307002d541c0d0700c64024404003d103000140f45003500d540d0107420f416044040d04000c0c2404980b10264002c001c000d00103003840c011580c0f801e42d50341da8485200028014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 918615179 1250 918613929 918613981
    0xd060c0f08040c050d08070803040303321b0c0a050a0b0f090318060f0307030e010b0a030201080c180a0b0a0807050a1b020a0b0705060f090105040521090405 69
    0x1548008520480c400c030711595002c0e0203d803640742000c0421041c0c0d00e02c1c001c2201d044c042085460300083c0740001544c0110711030b85002ca00f9240c0300c80144511000b02540c450641c80c980c803505001003003401480d8001080d00c04d62001c42c140c8044401c15841841100100c601c82c4101030400c0210008800b00024000d1210300300684079843c000740075442c00e6540306da41e030f40244482c00b020080c110040c110010014000ca2030080300034010042600300320760013004203a8511445c2e05a020038090015002000c072a0410a00e056a0003e0a43c65000e00031400c4407501048081850010800c07000c41100b0048c40344c00344c0c95441d11400c07241d03446007101c80c00240000c404200d81502580079202c504880d612822902041e6404041000c0300e0028103980c40884c00354001101c2401e6401002c00c64040d030b002d002c0c146880140608003020250200009038504010131020a8002c13880300e041091810317240c0400b030f800b0304480c0c035540540d803100e40e4042e03e40070610440e404036011242001032204a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 918616429 1250 918615179 918615197
    0x281203091805090601060e0402120106030b03010e120412021c0b0405100605060403060f0b060c0309030609030403030926120307110a021e0613030501060315021c18020d060c 76
    0xca030060340c10a841d072444541c0300384c0040c41540d02918412a90300c0015200508208400c420040391a00a902090200c0e60307403900e1205c04c0c1801e0045405054449004014064460311440900d110f584280411411122640c200f1580caa604103a816450031420003180005c50412381d00008080c3c908880b41d104440c41107005501c1405584202c40d0010455820245180c40b440003030a45180f240202969804032805242d40342400703407007840681c0c4003c1d6141d00b115070901d40f0700700020301403003003940c418081040000d5000000380b081e620401c3c0480040d40080d41c0c004101c0100800141c1c043c0204880c0913100142d030009944960060f60302c6c0a0351580c1048516158007a0450103034110301d0041600d0000c010410090400090180a00c0e19286500c1c1b2641c6509606800441d040c0c2d449020400501078402043c2000002c81c404c2145402105040c078803032105440514185103444074014003512001c0c10741d24440a4018051108e11001c80c641040106400d0780c0340400710f0709100b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 918617679 1250 918616429 918616469
    0xc03020744070504090204090204061e06080f01050d14010221130b0718030506160905030d020c04090c4209301109060d0228120309 58
    0x1c070012003041889000b4004940c10b10003030001401203404240c0c2c0281d200c0e2018001a11248110f0000b014100002e406800c1a9200c140442d0031592000c003c00c040002409204c0b8640401036045580407540311940012900c0d00c3c42c828608685c940d2000d51001c2540c00000000a82d074050302448608620050342d503509542c800144101005401c0d6540100000d141794080c0c5880d03001d1800000000084c02d40e6507488525014040340e000081220380c4240e00691034029051b000501400c4018240c0000b286200079a9194400c40c00ea1046844509210074400a10318040147c181880503001c0e071030382b030711040194054182424400308400d10300d5840c1540002074404010009a49400c100d5282c00b80300741038020004c1503580d4036000e80580c030040f000b1564404c0800c9115040750350800e20364408010071500c000300441e002e14070402d446c03401662843d00038001100312400c803400455098400c400090305507000044041e480c0c01100043c0754102140f070302264010390081140042c15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 918618929 1250 918617679 918617789
    0x90406090c02030a032a0c02030c030715031125050f0d0c081e070c0618030b0103080d0605040c0e04060506180915030706081e010e070c030207 63
    0x11040c0000180c01c04e101d41d10f400762098100020412118451052901d1505001612408104555408aa0b1032000841141824042c0e01c02010045025082d02c41c03030011172040700030b2801940010541c0c0d07062404240080c00d401d9402c0c03101c2e61071881c003840302c0900329050007603a409400d8949101d0441c117140000d100040d40700d8410400c0d62500d01c02002130b5a4511660802d5110710300818401508490201d0701502409540c2d0113407a40f900c0281c5000005000402c00100c09283ca03100700405101045421081034112540581c2403603a40c1c0350b012000e0300404981d00000e0380141000390039095154850b02c2210285411141008641e503a8002c00041e0311580e0350f5250000c0c20607291040c5c500e080008181d00c001c400284880c1d404404002904116554100e1030206440301e05000401c40c403110f109036154281c1b100c0c0c080035410700d041c011440c80000c0459041002008188040601c01d000c07000003001c40d030008044001a41d05030307200c82d00320352100c0003011401031600c01c800002c2d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 918620179 1250 918618929 918618941
    0xf0903080105030f0f07330c210206040f02120a1b0b07020f0103050606070b13150c0e21060405010507022b030209040905030a170903070321110a0509040609 69
    0x40e00c0014040d00d840d1401187e818042c0c0300c0c42c484802000348002a41d54504400b03090746440c42d07544c1060314a001c1c80c0280081180c0310043c501c03131a4071655544016000104990030030307045041109010400c0c8002020141035542d492258081d02c800c040400442c0c0300c0614206025000780c0715503d840b806070b568580990b40010754403680e1143c1280e01175020340c0c880c90b0071890240c00c141c03a02400f0384079031841c0e86050303a00d85160400c48881405000c0544180d01c0c1d0002402000e029030240300b14020804111006928407c140c0350f80030810301043c104035400d114400030182e954904e007508000d8000c1904031010000342c010352900071941d2800e008a0860300c1d03141c0c00c01410366515104210700030b401180d01c154000c1d41d9201500c011900820203000140040c0d6528280030380ea190021403040b10280043c17405078400c1c020103001030b4100c00c1c045034548052400725440101d034401d503005020661110340c0c1c0c0200020b802d1440700e6000303000b011403440c2980c090203407690310590310702100e40e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 918621429 1250 918620179 918620203
    0xa0e01030606110a0f2f09070825030615180b0c030409050a06231503190203191416090b0d15080f0102041403070509010611010f0903080105030f 64
    0x80058040c001403c840450005d02c1e0041104030301064580000428600c2400c46001ea655441e0882d41d803203142078030701e003076110a0030715100301d0300e0070245840303240b01151002200c81c00045c007030700080b44e910a0b80141d000701454122010414010032001d07120b003000c1c6402a00669442d4808140a41d1a400b182c090000e28002103182c180b41c40f10740f90041c07c002d404034002c680c560000260251140d031400522403c0c0000c050740c0c0500000030842c5d44101c941301c0c0441d0304418820015074024800d60303108460b41510b409a40c076603c0c0b20145076014041c42074055140e140008050400b1400003a280c40349404581900700354040c00d00c156508080b5201c0c01d64100420080e0b5984400b5603040b10380314115801b07030907440c06d803510307509800c1074984100340c0e01316940480c08014195058550702c51544007900580507003828080031901031441402600e0911010019442102d03e003588000c0e2505000c0c2c20400500c40e440c41c00038203505081c41218071038410f2403003000c080e510100700d00110740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 918622679 1250 918621429 918621433
    0x60e0405010e060d39090c020a030f0c030c061a1203070c0501210f021c0e0a030f0908010501090617010b09041b030803090a061503030c0f06060b0a0e0103060611 71
    0x1062940c410b815a003004000a8a6405d000d4000102c80540c0e000220380006500116801d1410107096204580301109100119801441400f000c2a001000110726441038038049001444900703040c0c072145c0c40310a00501d00d03803520495050026900c1c0c230040b18048100c500f26003000c0010b0040b80e50b800764150150285504c0e500030851507014081750301540b8103100f0603020203400101c005044640015102c242c540c2c000503d200e80110010103000400b03081d0b1803c00c80b80c1641c074081c541d1a40806001400c0c040720745004440c0c54002d103040c000808078000203015960b161810302c0e0107000c1c0c03032003800c501004c81c5c204401c0c40001030003138800302000030300541801c0da250b80720444158540e508105500e03494400100c0031900c0c0c000114801d001d040f000740545a004d1a0010031207000c01d111810b01c00c81c0040a2000035802040501c045402c50301805420300306041400c010f01c5164840c25825800052401031030342c01200744295890240c90400003d540d901e0240e440d1051444580d50036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 918623929 1250 918622679 918622699
    0x923010e150301050405060603060723030a1e0e0601061715041b170105010201140a0213050a121103030405010e090c120108030d05090c151b030301060e0405010e06 72
    0x3080115010590101240e4601e480340100d440200342124030594007905c0ca900608100825401c04100132a00007240c0d1805001c02ca035007222407080216849084001c0400020120794800e4140c2c10030b40d409010381480746160406420322100504503050145001d0050100000d070960080c09403400b4024034000c1028140c2c0d9066060954103071042400368841d64a601450380c01a910721403c4c01c1420315200c1503c170038162000c5021001c4140d200301d046a04110340f541c01000d8074808283c01100300c90001d03031251301441301d1626890341c81e0005130b04a0800c0c0c2c000205e0201d0034081c03c020a000704404030851481d00245038a80c4164024540400c601c40004c034001d080c101d00903035005440440540c100041050b0611586230b080c3c2c011900740d8030218511800354010702c07a864101003100001e11440402c000440e201301925960700c480110082500d03400603811383d000c0c403070206014080d2a80ea68545902806034030f545030300766003d1407401c0000309005800c1c1c90080d00481c4020f255402c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 918625179 1250 918623929 918623939
    0x60e010f050d151418270708010219120c140f090409061d0606030616120c1215050913140a0f060f051005130b0a0f092301 54
    0x70aa104030040c80c181965600740640194280804001400c013880102c582e141c00841000900c107400016102200100d00c18000d0b00a0395460102504590802c3c0051b03080b5030200c01402c01c01b40c2d40c80000154000503050801107007075106501c10000e41e484000d52a8a040ca034207040311103004002000ca8003591100c51000c404001510713200c0458000c0518180d040c0004c42c00f60b03030f070312401101d019468902d51003030030318410000c0d00300215090080995107820b00000b6900e00c405483c0e1000e502d000040c80305802e100e205440300c003080005051048140c0604000d00c4080d440c070905615510f4011041040780380d4031a040111040101145801c1e143e68541c0031640c60344820403a400c58a55548403890413050014490542c0600006080b0400a0420405840000d1203c3c141e20b490403081000340c810b2210010183d0720280c0f000c3c401d55407880382c204000d184078200d13158003c60390000000d0184944201d0030607901c01e00c605100300d448490b0380f0744c400f03480100c0b071010101e1140b0042c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 918626429 1250 918625179 918625187
    0x6051302030607050c03160b040c1d06090a09050d020708060a0207030e060c1c08011a0403390b031014030d0318080f2107020c01030e0f1f06060e010f 66
    0xf950400c00040d2071400c00791050181e08280040c80489230304c4c442c1000c00c0309101011610308004d001e0161100780d1754045940c03941ca41da400034270280c4140316400101d0f00c064225404108100d601c40209c40c200c0d042d10101070b550322110b11840c2024031900d000038503440c0c010300036520561792540f1205200001c0d0420001c0c1600003940d42d00b564410802c00a044410b84130030300000e040540c0b00c00855506200502c1c460652100524050390800c002c1040090000e4124024295043c5c1040f1101c0c00c807004201e0f4840000000403141101000b030100b1004034600045010300c44461020301001d58a0700031081030202502d0081c2e16410448994044902a402071003000100900c0d50b40c04490707039920042c031a040707640c50100d02030010030990003542c07450000300d0790501c401e00d00514601d401035000b551268100d802904040e22494102d005990030041113243e0105070094444410007000c2c0040d13160300c44003a440105080540003d0394900408035100c1c280300681d6042401e14914000752 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 918627679 1250 918626429 918626437
    0x71e0c081201060f0806040b0d060b01230a0e0a080601030b100801150503010c03140a090203010207050d020606130504080a0815030d1101060e010b040302121c0504030605130203060705 81
    0x19036031140801407948188118500203001c1d2070192504003002081041c010300800c2d0003440d0b18056441d14032942c3c125611549030300c0c01e8a600c850701144054403040103c1f07046070b074440d00085110140d52098a100e030404080c10003143d10313036201301080810300100845c42c0c4091086a01a4000c0e00040c4049003201088545c81302031922280f101e5641c0b0030006007103e0003094400300301703282ea000c1440145000e01460317510000d03074602840340041e00c1000030043d46018203541c001c15503a1400d4000c5413801e4042d40c0b811030700007041d9403816004540c007030744407941111040c7c03250359404503050049180b4441c50340150b802c07595a0381008a01c00d002c1d604080040c0141c1800340c0c18507140c1103d958104040640d0481e20f5039007903940208081050309480041d002090a0203084005210004590041d40c040381d40441d1151100d0000c145a64142402541c0079520420011200184990808010401c4a100d44010032541da1020410140c4000100f0002c0d81900500041150385111308060 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 918628929 1250 918627679 918627683
    0x5060d090201181d070f09090f0605031605180c07030e0a091e0614150f1e03220525210c06080402030d0807020a081809071e0c 56
    0x41c028440d401d4100f09034849a544180f4190b042000d04140d00040d9140c201c0d0840610b0400d2044d50000000c05040040d403809007903011641c600d02003080240680001c0000c14000d01500d50001070742945a242c8a49401030710b01880301900100642500340480e02c2c803905094140394185005503030100d82901e81614440d9028109102c040303440c103902d200d09066910a0b0010009000f5104404800d85000b944150301c1341200005030720037903c415100d00155140b50b02166a16400202040894000d00865480c0050540703c0340104410040096000d0240130004072500340004400304100a02d00c40c00400a4112001803046031101d40010302004840c003c0550810383c1320249074100c01d5040210743c10b00c0144803036030781c2484540003210f0050300daa4541810300c0d00d0a900401c1c0d03200712184171030b0200218640090416442030220035421a4444110b545d6040c0000d69401c4903240340000510400d03250000c107040714066061006c0724000f03030b40c82d4800030203440e506403100700106c001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 918630179 1250 918628929 918628937
    0x113303180a0302032d030f3c0a0207050f0708010e01021c0911040c1205060d2f040c0507061a0901170c100309030f0c020901090f0e1209010e0a05060d090201 69
    0x2c1d800c07012a101003d1842036902c80030300200e07441d04588141602012300d13000009524001010324030304082c2c02e501032180c00e610300e900f4040e89803c06064000e1268082c0075001d0f015401d400f0003c4000820b42c14201c411080082c003803c0607000b4254201d01c1424030405281d240c1e05140f009503c5143c0041001074020440000f80745007100101c3d094031242d40c401400503540c590026610000ca110395500071a06442c5120b914015035106e400c103002c00e00803480303040e060300260100d550006d405100e03050b60141007441854a41175014040783c01101040300c01e00d0904071212420b001c00031300400240c5008090200e241d2030b00710640d50006450741c4460303d40c015040149001d4480049110703039000107030346c001400c2d984c1c0c0c00c004000300c501c0c4810000300101c121140001d82d441004240c15a8000040002d13030340b44902c80da84c000c1032040440036a90294000c000418800c490103800f4202003a214403600c0c410007010070400c00058020f0660100c0144500e06d008046070348141d80791881810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 918631429 1250 918630179 918630247
    0xb1209010e06090c01120203010305030d0b030703050d020328020a031b020402030f060f011407060c090816080f010b1e0a0b040f09060e04113303180a030203 69
    0x4041424102e0841d44060b00e07034004d4a410405581c450500403d0b000841e00c01c40c1154115510240c0340c0c45003007003c042c41c1c1c0e00d039807003078071580d034140700c00b10003540d02000301c0362078080c149400307901c98004c04510180300b87c00e240f442c0b840701e116010000081e0110b074090501e0710703510707038040d00c41000c03d08001e04201c921600100043c0c0329840254007418240702c07900c0d003d141050401400312219605641000b20004240a9924404050703601c0558000d8006c00c00e0040c40c1e4044a1140701c070790060031107200316000f6500300c1d03a24081c80300a444058040c1d4452140260032182692280f180d1180c100c48a20000e40040070606084151590003e0540c50b4159444600c41025000750300a01c1d248080140308000c2b4515900c1540020030280761a00792906e055162584039203d82c01c00203019464001602c4240b80240200da1710f0001c41e42103071400c0d4032039600c145001d50812104400480c000000800c04280300160140109606500441c9040c94890000000c80c400d51142c0f002d51030a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 918632679 1250 918631429 918631451
    0x40b07020115092c070314030f040909050601091509022107050c010513020105091909180b340c1e0302100603020a0b07150501150f020102040b120901 66
    0x7010307034801480c610b400410390440640701024122102c260810700203420584d84440c2d02804602002260382020f040b8101011000340c10341144904419118460400100171894814641c4414406801541100d00b107a0301c2c1c408030f50440381c0b9030085013100054480200308100c006c0d001007100040f00828454500070402d90407a4610040c1e80c2c071400b1441c00300702c104424101b4860564010002d01141c2202c40040d0000b802d42c2c880c489583e4002e0881c11881d24502c140020290010702000c1020000c406807035a0360100e00ca80100100c40044901c1c000c201110801c40e51010b007494540300703110107599000c0490380d450070b242004005201c00ca5100e400800e0480c000f41114248a844545284000b844c00904100c8000000e0988510740541440945c07282c4010106942049680907030340c1c00a41000c5181c40c20345d0b010001d0041c02c1800126030a80e1703001041a4480c1240c9580403014a0b00600f64241e00483c02036410044040c0103019191000a20040d08400c1c001d0000070b80310004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 918633929 1250 918632679 918632711
    0x90315050903370804020907020c010c080702030114010605031b030411040903140304060f0f051324020f0a0e37080a050c0906010518060708041205060109050a14040b070201 76
    0x8248900e0204e600c200c1044250304000c1c1995130f00c18440c0c4050050440384400107084202e465074040e10911007c0782400c00c546095106856000d07800c08040400d40c0d56010003071042e4401c40300d5111414044185003240f84d0b034402528012070b80f00c6250010701c0010b1081c44007c10bc1603800b6002c00110b4029600001000b2005601807400380c0008035042c0e00c400c8903103040e1001d07003c206449519060400c450f0500902070410b00d20b07804040c903c0c05004081d0b1a8411380c2e80b071315410711140d20001d070b45100d0741040f000609801405841b40b02920141c542081004c5210720054a04015481c296004008252403c2c041000e1400e6003103409546a030380032031505480c0b8000316242d41c0000c4191103a440c000403125888002442d1051034400051006c02111036101107160003514041001800c2092007400c0d0790107000c00c03a4401184900070b0412582c0c801e020300c24a43d0162401c004102501e809019401d800c2040c6a07550409803200c0d03a440c4c17000301c8001c100c28115540d41e20303000b0340c0882c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 918635179 1250 918633929 918634027
    0x240105042117041806120203030316200c0406050108070503130512120703150b1803010204091e0b0d080901050c0c040501060309050f010e0706080c04080d090315050903 74
    0x40e10046180030b031000005a01205c0c20350f044480300508401c080f0300180d4000040301c0e48108029a400581200c0c620305a034654112803103140301c0c5503510402a003040f80001c000982ca0804c680c2445040e81c0d420040d41ca094050711100c0000d041080002c1d10b1b605a00040105640301720101c0310f8040c00c601207080282c00540300102d00c0844a0103001d012540b41c02294805a40540410003003407130900e2a41070b52190340d00442d0580e007103400100c03140c1c2d820750644004096550302841040d64039002ca2841c01c180d425590101803400011200f541000c80d42101c40302d5100103203a103045000070040d911500245900d018610551203480f40e15221030150034000c01d101c0d100441c0c101c078149030182c100f001c980b9080c1c0b01d50303241080700111000c00145100031110642820401c43e203450a615040748140e8110340070520414184c00000c0e684240c0000889008402c00300c28100d041030851700b40e0b4000da402004992050082403240c0a840355440f2a4035145000303082c9894508400040300d40c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 918636429 1250 918635179 918635189
    0x51e04030305030124020606040b011803050109050f0607141602120f07060c050309040c05280f0e01210e0703081e03040c0e070309060524010504211704 67
    0x102c007100400040441e50b5100024007049003815180715010071000390b40d02001484903206a88403040c03082c41764080d0f01c401440c2102c020b914030a81e0b4407800d14a000e0040810704852a00c108240c505160b0360103d5454021400380d601c4e441c0c04000114054151307045811219003450101e0310540043c0e58506000342c00b410040050141e03044680021400c0c14440ea10820601c1000742000c400030313a0110490342521000c55001485c7d50b800042140c1c540580710054140045030800c0c800901a0810003045a0fa884ea55141c030401d6003400441d01100030080f4680420b42c0c00309240049000100000c4460b04020400998100800301d410301d81401c603842030b2120f0301c000810101c1e044018107681c0c403220442c407059140d402c203070303450506008451055450071100c640103e20300380d100c1d400c940310440c0c115038140200e05081c2c03142001c0d80c20501852240e40e4040c40c2c03100d1103500803815107040b2120114440801c45071110f140344820307040001128604c104c43c0700c4294201010f0301a2010344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 918637679 1250 918636429 918636437
    0x91e010e040816061b180b0d11030a0b10050406121d031602030c06090a03031115090f0c10171003021206010617100312090509070f17070f051e040303 66
    0x85445c44511182e068903860810491440301c8101c2d80c1941400c2030045a44d503280722035541e44030706280c000600c00341908042c004000410301280005640001076a900103d0b40e4110fa20903c072001c0e211441103100d00790200f13004417554034130825180d20007484191104250b10303514101d4004141580d01c2900c0059055412034019401d5042c10811017094040981d012031410300710b0070004142c915140710040401410480781c2c00d000e035040c8010105420501c003041814240050b0050b140e410483c040301c25445000c00360103c501c4c02c01c1450b000e240d603940f10740c140b071000c0d0041507900000003405a4035010b20b8400000058071900602d9200140400103022a5410032800515030711203044000000c44111050106082800e85c2c444201c0360b002c1c105010b06290210107a42107805a07200b2039014400c1b004010005070040b0180500040994450000300124641e03240444015a0f00381c00092020a100c13240314000e50040085000076801c1b1032203003103940c00950595105800407000a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 918638929 1250 918637679 918637691
    0x90402042703031404020612040305070c030c031e081806071b0f090b011d0103090b010803031816060e0102030c1f0c020307050a02010e0a030b090a02091e010e04081606 74
    0xb140c0c0c90301c507112030341010200a400505064001506d14003032007410303c0310029602c1c08501014007410407a100c0c51b90001544800e1903490500d0000e06155100a5500b4440d040b45c144140600c1c0c1c2480d82c02c2980100d0740b908040d100700b81181006102c0110a41204080045002249106150951295010044102041c100140d801911940c6d03030006009a0a041c100e01140c0e800010025000c880340340200040105400100d000d403d800c0009841440c032080042440940407004610031400640f04030202051000c9071a0381e4034840c071842c6108008101c0a1088038030400700301600100c140f0449050410601c892401c150070b250240c6038003030b648080300102c4011805268081c0074240040d5052500e5500e4640e1200a80c1c00001d040041078040080b0581e10300700039030007444d00301c9007002140c070b0441c6070a5941d41e1000020f0703101b9a00c400001c2e00e4845408004003d00828000ca40d005034a00075160340720304005401202c503a03000b0302021400408024207800858084c0c0c01c04110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 918640179 1250 918638929 918638933
    0x709050411010e0d05030406050f1c0504030f090803040302060306040e0f150105040c08060f030709061818031d0102190b0601080c0903190c080a080d050a0b0f0904020427 75
    0x4010f0701100f500d4044c0b00080c07480c40c04940040151012134020381007041e66020001d060302000e1041c000c85259418488100c2d15a0b40006c2d400700d481281f0039214565030042655040e54494098071031181640d000704001c1c401418031304051034000c80040c00124201c0821007800b403d061192190300c500d60b015462010a81e00009021801030405450412a150300c03130000501015005007030301e018400d4810481d03080d4804001d03903401030910850400485464045440c1c0c8a40c42c100f0300788402e81040c000c0601152040d40780c0986540c075450301d0003140905440c030450000d50f060300030b0540c000c1a0b81041080440404440407a102c5e01c50a8a82d140520014180b0b50303006c0d03c150102081070048042da52800a01d102c0e503854200d240022a81c0f807864001001304c0180c0043c40d5601441003402e00300000c0750054410421504804e1040c0d44d00d444100b0b08403600c00c01c0081d44900c082408401c5410041303e65034201e80086d00214020780c0760302541e00506031100c0002c0c1d02c00350090341c3c541 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 918641429 1250 918640179 918640187
    0x15070c09091b1a030411153f04150216080307031a150d0e030c0616020d080606180907080a0b040b10050a120f060f082b02070905041101 60
    0x41c0c04283c003020440481081c0080460000030402003440300200340c551043e94038003903400c40c00005140341d282c0e2010254004074120003d0401045025080b4002030742030200c3c18410301c0c6485a00703031210441c1d941ca8031080036040c180b40500d00d20340d9003000805a8401994903074a050703402101c0081d82e0b81412f110040881e40385240000d000d140e0804443d5403a500d131030600c10256003d1005070380f16400041190b000304081041c0089501c00050000946003000c50340c20f01c10403924041c04800d4000d03030016600d862001c000340002a01c0c801c000b03040c07850460040d200d198500103440003010458008603c0c41d4000703a45140102c1e0b4a1420010200340901408610b550107071010700465403448017040c004080d04190340c0c2845004500700401502c1020b40eaa1105038082e4203028141c0342c81401001401ba600403101030040f8100c012078031101c0050f4007544005224000800340c511400240b00d050b400601810450007140000112003802c0d0080fa40a603010300d00120401ca45400054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 918642679 1250 918641429 918641483
    0x7110304080a032006060918070e180a0b0c03070c060c121b0c150b03060c09040c030e0a020f0a08011e0b0301050f401101080615070c0909 61
    0x10035004045145150884d4011a0b02030b00035101b41d810440a80741c80d124880348050790414000d0030f102e201d100041c1581c100201e00d000d009460303d0125a201c46844c4a07498402d072032005001040c2500226a0441c02c0c2c100841c0c1c40021490300c440b03d82110707502d56042d14079055481001030204045080d600c052440b4440c0d030101c602d0202a60031303071558000b41c00b2201844028014a101c1034401031201c841c1d80045505107001410b8460514001c4402c4105800113110310340158a01520841d031a4000d02c66560010005001840c0d282050b50030800c4000c0440e29498001801d000c0c000340c00c207001d00524090f400c015841c038441c40080e508410441d07623691001480fa81c1041d003071045841003601000d4211040084c01c100314a260455840d5103100e041c2c101d40c1101d000c101061051004200d4114210303c18443c00103490948001120014400c4d075189500040c551a0040030380c041000410183d442074411080c00390b03450100f1803c0351140e42c004c0c0e455000080282b1807203200c0b10885 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 918643929 1250 918642679 918642707
    0xb0601020717070905040f050703080403030f03140622060b091e10080a180609030e09190e01180c050a0905040c090515031204060f0915050307110304080a03 69
    0x1141a02c03402140c0c0d40b6526807045401c0940d5510100303050003056111600d440d50807404460181c0e0341c914044200358800d20042d000103100129421982d403184c02400c0c6000c5901007840c005498440400c8000e5245082c204080701d500d60080100c0e1200d409840700804130f0f509640d445901c49018404a907004110204201d01c60140050031a92501d565080800c0c1c00d20b40035606550f680c1400740104100184105400301c0c1e1100d04040140e25000843c0c5103100b50707181c00711403140909001003014259641501690078048800240341c0940c800044c2d03210190012032006d4220380035901c0c40f0000c05042d41c080040d4801800301c0c0c100001500002c008072081001203140a03202d02d101003946001b9095010b450381d011034040a22840c2c2c0541d03490004058503039032010364071504040ea01034030510300891a40408221143d00841c0c15404070f807030051004885845015044074694001452074080c0080c492084680b48010005072000d018014020180f5a0b100d080140500e1140c802e6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 918645179 1250 918643929 918643949
    0x6040c1a131a04091505040b0301141605070c080607030c1b031d030613170705030d151206020a0912020f0409021311090f0303190c0f06090b06010207 66
    0x711000200703070580e5901116640608444084805801e5920b1441558043d07a01031741483c86184082207464044401c403602110b08002041c0c0c00400c0c503080c4c840e0400480f4500c0c040303e0005e4001c03011102000c803240960b2426602d0481265550030b0282002d400541e4268081c000308200560184114031707164040d411311102080300c40020084002d500100101080041c50102900d06c0110000003010b40d4010243c030790360b1078044c1ca00307440d05030140d600f6900c0c900341c100c1c000e255005420031200007030b8010010718038250b18401e8401c084d040500c2941c42c900102000010301030002a42131104500c50b11015075185425003004100c1090f03030700400400b041850501006a0701c1d018180321749842a2008250982a030000840e01d0500202d04441242403034865508200f0a50042002c0d80c401c452801d0200581002d0694a004143d00302e910010036803d8001e00038011241d00d41e40328890660700710060300341c0e5990019079440100803200c10341080c060090383d49e0103006030005080c5c0c40d51 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 918646429 1250 918645179 918645187
    0x2031609030b0c0d0f020c0c0307060908070311060904020f0d0c0905010f1d09090c031014060603150301020d0903110c090a020903161502070e0c070b0601030e06040c1a 74
    0x10b464000d03200c00b07043c0c000b04003400108403030245200e4014105011010350115201c244407103070075458505c5110040e00c01d008600001c03d28600030360039071041da4803503801007640500719602d42c000705045220081d84000140110360140d61980001c10300710750010006038403035940a1703280781070f140c1e0700b2910ba0901104200901c03559a2100e05807403900e000340b5080001c600020f80e0080c0915121882035003100b40d40f8100b1032102000540c0440300c00080e4116482070400780e104204592004001d55504001103000c5401c074984503001e903801841e40100d0109040f04000080d00f280c1c0100302204010340c0b10320b000010316400580d1011480051800b91660010140c0099011701d002054004429030201e62915180c6041000180a65203104542d60343c0f03403110740349030751403050015060040c440d00f140850031540d0041c505014401c0103d00b617090103c0ca5588201101c0000d00090405680382e8071601c500c801000b4890089000b040b4142046060140000b1883d0400709071250782c1d0342c108 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 918647679 1250 918646429 918646433
    0x6092803142a070506030a090f060c020303061203031b0715090f020915010c0b0a0b0a080f0c100c060f020d020d0b0a050301090503030117120703020c0a06140702010f09090f0203160903 81
    0x5d085076405400706c0d074001000d294a1400449501d011280500f00c0d0f440d041204001540000c000d50040000306c0b0071702440e14040754910344e00e20048480503c0c1ca1807080c0c401c940b0001c44800b50041c2d9100b45420305803039080310344590403240444800d4038503445205c3c025040d82080340c5030b580c2007010baa5070641500003002c0007030658400444010a000d86800019120021560000300f8a01000b0301514215968446041d59501d10703100010071030042d0306442103645040304115542d4441c81c0c5030318510000b683c50b130800400650b81032146840d0204212518010079200400e60601c0050001603a1b0b81071030180402c181440d0459800b0343c3c0b40c40781b18004198004103507411190040300004180c42681007590808402c04030000070280042810020141c0100d281c2800f00780a441e5419070966442c012580b88981c00c900511241040042c0409948158507440c0b0982403414000b003e02d175110340c07000c11500960840840245e021003441a1140d003000521f043c1c80c40f070300d081c0c0040c5d800c1d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 918648929 1250 918647679 918647689
    0x21e0a0909050f0f0a230a060501020601080607050c0c130f0b030102040614130302030604120815010c14011509020d050109150e1810050103020306092803142a0705 72
    0xc0d000011340102c207030002c1e1071066550080b158100c6101e1602da02d41031a5520006030351000e03200403085d42d05006010440303500c00141c01e4100c406881c001e008a4444400903507941e4088031841041d802214010740642d25080c003045400c8070140c0d0300203132150000c1070840071071f401c1c10303200b6200364010402000510f078044014441800c1d40000e082e503843c807080c81524040c100d640300070f4141c020300081000f4468416069118801d06449034100c0d0780c0c3d0b030078514862001c01680140071441005050700071400d0040d928003000c1036500009100d04141e04161a4800d1640c0080c45003600050740032101e204502400b401400c80c5070040c01010146540d0b0341d40016180100e11602603007000140e8503d0980181c2c1501c24025030943d4401802c0c0c10b40c84000e84400d010036400f034403840c40821844c1c0e0002a950078444800752060303a04007900810114030080d0340c4416004c1100c06038900d03070038400b40c4000308110548916040d1007074000000b402c258070f040348080f00e240c0d00040c000300015150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 918650179 1250 918648929 918648931
    0x304020301141b130312050309060a09080a08070e0307080d230f090d0b0408030403140307021011040503070e060102070605040e0a1508010f050712090c050d02010201021e0a0909050f 80
    0x3d540d01c6880351141d410a280e03c0107240d10103480b6251044090f0500d0b50810029070141400005032200c598a624501040d211b025200501e184000c1201160443c4280f40c444c1d080a01d524046d020b00c0c0032040024545100c507042180d00e43c201440c4502c04d550480303030300d21103000c0c60021160710061031949514180200380510024100c0011844010b542d41c45804425076404070b041c24580c03e19003401d0502780c008aa08402194503002003101491081042e40c2c803c03441640204010307240440900d010b01800d20b464140c1100600001c20039540900140d000b0300442c40c0101110700d402c00009242c1180750b030100091001c01c102c00d12400800c1340585038844c01020011903015105942c40100b06400d6204051a52070a04104200703903da40015009407280d565025041c9030700d51514040b80e001000003011481140400c00c0181007260543c10b20500500006041862440002800009140741207501c03041c00030740f000c42c0b590000016406030035034907010089071804031038258160708 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 918651429 1250 918650179 918650221
    0x1d06091504020d030e0604030302030901021b240f180307150801032a0902070b10120f05250303090f0f140d0804090b12010b010203090d05011808030402030114 70
    0x43c4200786040c580600b01d40c9281c0ca0015049503135550f940d09009449820801000340140110032035858017941d106c80000d2079182c000c007403180e520f0b4400c4245c000e2409010f54070f040030f40e09004001034003c881000d0000340a40a145503001d8848004150405010350003c004012a94403042600da40c8101c040d4150b907444181a640312414612480e0300f10900542006a10000040810303800c80b5074014080d01407080e83c16013440d448000b411881c91905015a081d188107070408039001c210b14041008403c0c0c010801c0d9004410700090f116601014240200c04c1c2c244414000c00805030b00045040c001d007064103181050a0a1008400c46215a40b046d1003189104021080e800d50340c600c002c2000d0303a4401c003850383c3d0301d640b41181c0c1c011700300460945220f444030040d10202c810b810b028008408205a02444c90800004100042001c412809540d5036507101545503400240a8030201140d0103500040c1d00c81c54a403041500307507846020030310f8503800441c0a006084010380300c8099044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 918652679 1250 918651429 918651439
    0xf06040312090b100617160c0c350a0804060e01050c0a060e01110903060403051b0607080105120109050d0509010210140402042909040606091d0609150402 68
    0x125a0280c01405009082e60107481507031494203000b84046010321581c00c40784140c907800f0701086c0c8280741d481801421039800c0c025000c18845458110f1107049055003091140300e40001e299140c4201130b120107a1080460002d45041001040140000380740c000c1000321000100016031a0b503a0358185030040d4410b64083c441000c104180c1c03a801801034580c001d034100d0448070000d45504044020b841d045540080359407900580d00c0000c41d02000315500b00502070f00a01681d00c032603034210342d26400b04c1500f080d069100c3c9040d04059506108c890b000d070324182da400c0119410a000c00c010701161140100560f0b2504442c0000030314081000b10145905081c19510707650341800503424000c0c81c503d031001942c5040841c0f520200300158041c0514003c0e030703081141d8004070721520031131780300003245910b071107041003041c03000380760031002c1d554440c0c40303802c022903000e95403400c0b1030644032010b40081e4285c0401d903041e0300c84181002050f0340099068010714401c80201720a40035902c014001038055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 918653929 1250 918652679 918652697
    0xb070224190e040906091115030c03060d0f06020a021b18040213020c0618060121060b10030209010e040b061b03070b04030f11030405151e2a0f060403 66
    0x56008041500b4540e5018205116201da2032070585c004242008044800300c00c1903403103400c01d0034002000c144518031410703100e245882c2c10010308070a0700000c1080f0741c0121680d4142c000030300c40e100c0216415200c1d10015031600d805880c00b90405124441008400306103010400302982e503003c00c88072a10242041030030300d4999001255220468003110300040b400000c606580f03c1c000112030340b240da982130f102c040c0074400000c444c1d180c15082c41413003411004035200d0a48111540712214041e0700c540340c0011a82401000700c0c1d050b000280421000c42d901103031444031540c002446506080d01120b0070401c02d00800002840d41c002c01d54040e400c075420140c0c10034a88000c20441c9c00d4580c02818007009840c0074680102034411101c4103c001600b40120015032450020590b4290703030004062002c1c1176208041c2c048540c22400400303209420710002009003280d0b0320014425280004032030158510881c0c80390f2251003c3c00e6459001d0b902c0160f0b0410309520100c0c0c10381e00160715180448038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 918655179 1250 918653929 918653977
    0x70e0402131a040501081602060115211d012706020f0d02071b120f020d0b07020c1e0d03030b0613090207020f04140612030c070b070224 60
    0x7184007941151500b14a0480010b890802000c042c0044610036079030729680390303240900d0a050202028100015910080040c8604808003401da00d034810b083c90240c0c08030300560201c0e140a031000c501ca0b52038a07903030744036030300751614444c8521345c80c200d01002071000c1f102001200c0c60903d24002c140034507004440c0304030200000c0b50100d07191940b4030081c0a4a42146024500c0294001001100c81c1c0d0241d020245c07813100d0098400c0121200100b1840c0402c040351544a80c203526060101c2e0b0040441c800c800000c0c2c030308d101860045a26900400c1e0002c050414403007202e4000d00c0c1030040c0490315000c4800f40e645c0c495100c002e140c0c146008200850203c010808900403508244600341200c80c0c0030412000a60140592038021180800301110302020f0008607000c241805005021540010700c0c2400c00340800f911842c2c0c060308072131626484001d007500340880b9422090610400055050542c03030040030062901c0c44202415140250010720a10703103100c0c1074034401c0ea5045019001d51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 918656429 1250 918655179 918655207
    0x90e04052113090b09011d0429070c030909090507090c110a0305030f100806040201030e032205091006050307030e0718090b0a1e050414030a051b0303070e0402 70
    0x6400b2001e10034286241d26840c0140181c0060038a103401421000000106010f00400701803941d0070581865540f52215100c01c0908100303015104500f2150501404e42c0903007444507103104450a684001000340c0034640108294406c2c1d0002040c541040c200300007082010400e001154400e0400140c500b600013402c1d6003c01c1c1c4054000010b01501c0710030b100785070b040030066101d000106441d03102540e445904141d5400746020300714065103c1800280154080d504c92840307281d0660841b030800e0800d01205a07950b1a100c054000c04142c45010006402d0403001030303401103450300a00341040c0c00d102008106020081c1203908054480162901031a0140030b00340141c1341c0008030016540c84c40241c500170742461039007141d000b03000600040140301a03200d840c050601032408004007210b4454400094080580117484807a814220303900c0b030110400c0100306460850700c805403518003218030717035140d0281030b40c9018554100b001007081e0164420503108030034404a40050b01e551854403500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 918657679 1250 918656429 918656437
    0x1e110c09132f2404060503070806010f0807080a0b0603090a060f0513020d0c03060507270609170f0a03020c100903020303030f0a021b0102090f030c152107050901090e040521 76
    0xc00b408200013804500150b01400545c400d0445440ba40ea50f501d5444c01180c00c042d00e60100c5000480c00e4011070142c030320503100603800084042c0049045080c0600041041e40261444001b9900030f84140041044034082c0349204150b00b401000070303107050900340e004092080b0000b8404c03030800a080b0704101e44814888040c5400c03000401607440d0064015010107640b00a03c165181c0545000c410000c181784070009688035999910a40b500d041102d500c0d14001e040c40000074010401c6ca01407140082100080c41800780d40200541c40455042c442d2141c40c00d009442000740d150814030241c3c40000850b84c10454400c0142e800b0340d12074803000000c1c040c6045200112910241c104480d681c150040d00f030450f8101d941d0003500c11f2200425644070b1002c511030390460704980440100c92500c0c1c0181003640b24a003288c06000c3d40700074041302e61241c01c8908002051010840b6582540d200201c840641100420f20903242000e44545070b84603a074500b0074040c5000c1200749001c1c071044405403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 918658929 1250 918657679 918657739
    0x108150d150c030603030801120c1a090603100303030506030a1703040602070519051b130e07030c1e4e0c14011e110c09132f 55
    0x100503048240381c000f00a00204c0c4810b800041507035001090382c406000c42800a5948102300001d8603240c001e455603410b0f00040a042c40600c05d01550320a5182d01d80114424918008207402e10703411450b0103001c41c1e10280100303009a001c840d0240000741c038a00118a103403142c4200c10f8480ea181d20b0454082e22070080010018002e4a50741080c61041161076500300740b1030000d0311452000784940012160310081c1c01540020081001c1d40c54035800d5021101030107010f8184c0d402207403a41c58221140c0000d0740b2030080c5500c4041151303c00c040b2043c00b075018200700c0020b05901c500400750021a80c004844448544176000c50403144c5002c00c0d000d20540c0b0003000749080c04a0344604043c4c00e451900e1144481c0408072151030b006a41c41091a0703200710107466100001d0411034a01220401301d044031081440c820f0040560f01d41c5d43c6d801c1a00c0c4030758031600b01c1010807095498170010030841e030f1000f042c01c520440509004080300d465588001001940c2e81054100d41d40300401c0c0c10023160081d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 918660179 1250 918658929 918658931
    0x4110a050f07060b0a14030c0303030624251203050f04060209030f01051918080a0f1106190e0106050901090b03010b091501090f0806010311041d1b0108150d15 70
    0x1000c0ea42c01690008041e1b084095994a40c2114145516484116030240c0d0002c0300e081c44121041500f15400c203040c006141450802c1740300d40c200650700c0950540301140750070054043c400c000c2c941c0c00c88414400e071803074280a03500340522004840c0301d0182c002031006402060021003a1010014044082d0148000b8420f0b400d02201050202110404403c2494185010700a20040a00c4d411030034550205841e0f18108105100f1503065084c0c98018007080412410b49140800400c1101c1c0240b800d107072114007903102203506200f01e03510903407082010790421404122075590220002e044800c08403021905460602c0064010a540c1d84065400610700d001e00408002d070441c02c28400b83c0a88403030500039114481580d11250510800e40d05521020062000801c0300420010260001d8004200440785030207031090160342c5e900d100304950004540390021807251038182132000c820700306036001c0d0500b881200701030000c20103506c1c060b01d4030300004000c1103542240b54039082c0d00f00030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 918661429 1250 918660179 918660199
    0x9020a09150503010b1003022a03090a0e0f010303030c02031e0903011503150213030812070207060f14030402010c1e020f01080603061303180b0904110a050f07060b 72
    0x1003680c008040008441e040700402040105203800c0520a00018103402029045096030144080380a503000036155609400301d0300b43c800340c0c10500d002d07420a0301003040156072158400400d0015446450307004a0702c401191050250300f0000000075410f507500340c074001c1084039429400764607500c42d0480d001d0b245500000c1d0b82004241100191100322412802880114003440c4540c03413402e40e5000161090300400b2000c0c40100007940140181c81c807180d9080c015540d6900d8644554100610307403008510000c0030011820340c140000e5003e0841d9081041001c0b44100b4000c00d000c1d23a048004402620000124081d680181d025580070b562025030366480054205a030b00784584400390880c0549001d070000da00da580110382d2a44a0320005e4010001c1d80e0755401100e1580e02011020b400344411120311585900c856403964001d0310780c080c0007594404c020002e05c0704540969400400c003140902503012a542d01600b1200407128000f00b0769182d070071a01b40a0014821541003a0b800743e1001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 918662679 1250 918661429 918661439
    0xf0c0602040f0f1a2a070f060305040302070807081906020904050108070603051e1501030914160f1a0a03020c1b01021e0c120c09130b130308061309020a 67
    0x40341006440001410910940900b0000401d600072007410350781c5c03d03801589003992418001441d1500071685001c8446445c2e54120281402a40c0c1d005003000030345500801041c5501040140d0080c04103500800f02d8503e001c0d640c549404d0308640f90301000980856802c140302e0a078058a0722414000d2040000303580d142000c5994803610303c91000460b040100042c10b41c100c010b00c0d0001e50402841d003c0c49944d4040340d182423200803203903050600d55200c00040108044900c0342c1c00084c800c0c00282400b69042c42002d41401d92503000d4000403c0b007100602c03c0f0b007200c0981b440328089450006440f2030a0000560103070050481d8828603103d03c2d02e608011080b02200036074004c20030b03000d4400c400c00b80842248403503004032210400e540441d85045403401c0050340070083c540110160303115130400e000010b00855040c0c5032061744a10b0350b0700f40014072603603606440e000000424403c0060300d5655000d400b034400142000d104220318120410540c1554215040c000c5c0c0c02050003190325150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 918663929 1250 918662679 918662699
    0xe190e0f01030c0803040501080115121a040e120a08090f060a050403120903090b0906040b04090603030e1c060b060c10060e0c0c191403030a0915020a0f0c0602040f 72
    0x2d100581d62940c1000e800039403034030007004031800e4440607510b01c2c110340e08003200314801a1000f40c510080154040000c038010480e4800e0401104070728000000004200040105555a80c42000555006000302001441c2d404080b41c50311501c5042c058100d0303940c484041d0400d06d4110f240f00f4180907013010450350810b140e004901c140d1090302d4913074620480312034000441d1503005008000c2801003071300b0302c9110840c10180c4055580144030034035180c0c40d44142003040e003050b44540e0078580c03501024410150020710f824195402034818900d80008810091a0104802c8002d801607946050b40d588a855180031120740141c0c2100303c0348940035648c0301d00001c10b0b1511940c81c082252202040002e8043d13022143c4e82c0070110024204401d1084504015201c910000c0311100d85105001512501c2400075502c140d0580000080c8900142060980000b0100e40c2c0000302d8030411090b07581c01d0b0004c440960920311481c029104042d5031419100038030464212044d03120a020001442e0300d80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 918665179 1250 918663929 918663931
    0x1504080702041407050d110d09030c020306070c0b18120c0c0f0121110c0a080d0510030b0106030b1201050a2007120c03020c04050a0f1b0e190e0f 64
    0x10030b8904005a81d0b0492020940304026030b035060014000f04000740101d070320303138002e1000c80105491003464082510070303800480f00001000c402048589004c40c040d49800d01403654800d1a608104103604865079424610034401006d07060f00c40350051440c610300d4002c20800003007070040d460303c03581c0d0032983c807815951b030495007a0940314040c3d0203030b205d000707500c01d41c01222201c88a0b28402c020380e40b010310200c0a030001c600980080b0340103101e0903132130300f0040051542c954024100c1e40d6403042c803a042c210a4a80044ca0b200c0c83c1c0812070300410004910b80b44250460700b0350302c0d00281c440303031010000364004451460481290708280500a41c2d40d026408403001d01031a044101c0b031007074460006000340c0600c1001034486171191048205140c06410010f0556119106032488406201c00003030403180c00fa200c103500160b80701654480140d4070703c0340c4448003224404000d0540341e000382c0140200320421003180030300c5141007404001200c0a4480b0050b202c42121042d0505c0c202c2081910208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 918666429 1250 918665179 918665183
    0x130609031b0b03070c050a120314070c0f020d0f020d08090f040e0c0f03160e01150507110f0f0607050d03390c050d08010503010b060a020703110315040807 68
    0x34520481c9641e504035000c28004032400781586504503075510401341c500c1d00c1c140710252028007d6480340d000190030700e0b2061000041c5901c00203040c044840c02282a00f00c003c00b400140f02c80c821100010508200700c003611a50704071200c015081c22440d103038043c0e90320104001d40040c506c0f80c0c2442000710140150180340000c0d600c0b58107903c0450200025565050101c4080d500411901d90482c2401c3e411603001003406800c4401d900007121649161004950064424030100c0c4010712401500000700040305c0d050380381650074449a501c0c0d04074500f4000160501c40d007520b83c0c03100c45035191088046480c00b00208000d0300c0741443d081907034503044101c00c039800003450801664086c01c20041081e040380c00182c241c0709000c1500802042d12102155041d05110308441c0c06000540104030303a10700c0d141107035203010030755140ca402c0c103083d05d98106915101e06001d02040b04890f600180b2441240c0d0030641071207a00c00d41e031300800d051000c550a00000c00707170100100002d020115000303181c481c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 918667679 1250 918666429 918666443
    0x170a02030607020705010512130506131109042307090e0601080613050a0605061c120906050c2a1206070e191203090e1e010b030f1b13060903 62
    0x69600b520881e1203880b240a000e01064050080c4101d4a010328150b507884100c94000d004807800c1c60320b505107082e5044490144a0401d408001c08100350410215030750002130b41c102c103031418035540e011040d10b000000b1040101c2d00542503241c00074100a0000204851002002420a008007044e2120400d0180c000c0d0b81c031031040481d4620041c0c1115545164010707019085c1d0345955034a02020707240281c0500c1e8000c9000c11495003011907002941502c3c0d120b440c00c40141e0600f028040d1040106610000c180103044c4008400303828041400d144990119440810481c41210014800c08ca995161a0408841c18080145820004c1c1080c00fa4078161541c440705501c00c13041005a68100c5209604010100400c1086161259114500e80e02c07a080102d10580c5440d5904000030b0111580032a281311440d12000c404102c0e06070324050403c0103441071851401003541a40b8040152044542160f400034802001258800741c400001c104400e1400c0c803507503403400600d14813481c08140c0b450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 918668929 1250 918667679 918667681
    0x7031e06051f1205031c0501090f0b01020c1507082d16060b061210050f0f0a03032d05071a06030a0221060103080a020d08011a0a09170a020306 63
    0x207070806500c2c03880d0102c60340303080c8080390700b05007640b12070b061580800c4801d4803051242e1103000c1010020101e03900400800007585614203070010303082d140c09070380c0b6408041c54911200c0d0309980c0494120290401035840c070041010042c651082071092802c06015880b000c40c0d00002d1483d02c13007000d56090603203588000028800e004040251080ca184500301d184052a003a0001d0f8864018000b00c0400404041c100280f40400100099080f00d81a800f24a0b102c002d200524103034200f00c0158034180c4034504069001000f01d0340a112500001d001d004607280b907054100200011103080090010341d5401e0425440f8001c0c11581041c513044403400d006855610000001c0a03105105400003001000d0b808240d40078005003069001e080029441340d000030342e0306c1010400c4224029841201a99560428650020b00f0090707480c02010422a105004000f4080e044082040e0420100c44580c0c0d101030202c0150746120030392340b22341c2ca940004504064010350100300300c21780d24001e90036940d00d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 918670179 1250 918668929 918668941
    0x2c010204090617070e06010c0503130306050c040b18040e030c06061314130201030b18011e080a062403050303072a11040b06070818040209012007031e0605 68
    0x3c0704860312003480c010344c440d60040100c510b030005407680000c4181400c00d442910f940780c4a0a55000c030b00c802c0c201c0760110004004004452003483e500108040019003458104004040c45100f206000010150b180518100703554840d8004001d0751501411a561140c0c6004d6440d1259400c43d00035118140c1d00780c640700c02c1c890358091401c41c3c005e140d0f44018299155080885407102804081e0b0405658424134602500e401c520203010f1051000100c060b58580344414999000e0412800b0426069102c100203c44000540c81d08446d4010000300706410020424007074030901c84030340ba080c914005400010b100d004802903000e6015656002004903061009003100032031803103030040008104080f60081007048a21708000718004001080d0070401000080c002d412074182a5120000024a2842002203104070760f6020f10556066042001c1c4e00e00280c010344c0c0d15801044500201880c22103410f800780304a0020b144d01c0910a810000403d49102d1040c003020740441c0c2440c036110120302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 918671429 1250 918670179 918670199
    0x1205060a060902030708130c0812090310060803070f170a0c031209020306070f031d0618071d040f05060405030d0e06090d030c09152d0c062c0102040906 67
    0x110030b001c6612006e1303a0b80c44081001c16002109102035490700303a03420010030003d0050254007030701c1c007466680c16254038491040508200c0c2c40314400d10031501d0101c08000504010050b10407481d0007001e4124017a2705030a000d12889007900170800c25070301c0000c203609010741080740801104e00039038410f05040300000d0611300300c070381401c000ba5240c3e001030000741c200c1e8030611040d82280303403514010800f03010002403007601c1d07814640700118680004040000f401800c401071540180103000610846280001854804000700100e100b0440c1003030008040c85850708084001e1540030742259650714042c10030b0350700e0760804081411007505100804542010000d0101c0c016802031002d0584160004402c0c0c0c014211920034000740000028001441c0d0302a0420401c14051902c5100820f11003607641c101c1415202c2020011951400b00c01d42407541c80000403030100d512070300002d98a014580818145404215410305401640c0142c2a1104043d00584115500b4810601c03034207840d442c10503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 918672679 1250 918671429 918671431
    0x1201050f150a020f0a0609020f01170109021812011406100e0402071e0f030206011502031c270c080601080303040b041e1a0c1e0706061205060a06090203 67
    0x1a40045011000c03142035002070020800d02c00e05004031044104490405424410740030b00580b4599500e00c40ba0081d410078001a031011a000d10f80f444c805403581042e01e00c00307807042c060340c143e0a07404603080626000316003a01044140051924002c00043d607401c5010340f180300b03040c90001101c10080340b01c0341025003400c00342c2c5415494090340030100c0c44c14031000303410011003a0740c030040d9104070401131800550b102d03000302c1c05030520510528107400c01034a00362041e44111040309038101c440c2c03403003940801940d0031501c50102c5c0e003403040c58100282015081000f0421b8500003200400c3c0f6070200004098591284140060030215944140841e1281001d1040050703c1d0002c0002400003810462101c4d44a4840c0070591000000301440800204038200200c3c5c07407101062022030b01c4140c0158466000b140d110055107054010192603001c9a003401d600344806002090f0141001107540159000e42049a002d01052845040017aa10030040e0784488049150039004101d002d0240222 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 918673929 1250 918672679 918672709
    0x80c0115060311250b0709031a060a21050d090821070314040f12020102210f1b0105070509091b090d0203190c05030d0801180b0114040605120105 64
    0xe5400c2c030700031030340340d200200454007a20031303c8440c0e000290000342d03c5071055001d0403841c1e0b0b0307000c501c504504d4001c1d03601c40002920880e42c0e9880e03080040507070300c1852000c2074804021400701000903403d880a41c03a0003280004019003e10204d1801c2c6652100920341110000000c40f041d0300c0700300c105104415803141170b140d0985810054040402c0c0100e04003425020326000309480d050b500c40e1400305038201c0d41c000e00c45100c1205110000c2d0340e4100301d44107603143c0c0c01e10749481c4c0340f80c289166049441009190500c1c544003160000d44120a04041540014940300078801d0f0f14100350010320907805090314030b04c69010000071030150035688038143e800c0c8850648140c90880001c0410203c480d2011301241d26101d0036000c101d000725501111202070340304031701040c0c030541031204060420740b46551240410510302d00400141e0002034514511300c59100000816035290001254071901e031603680781e02d81b0340c0080c000a100d0b600030001d2508040c100300022851b40c0741c0d020002a51501042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 918675179 1250 918673929 918673961
    0x70807052a0118060315090e101410060f020114040807022b020d0606180501030203010c170a0203070c02031903030b0d080706150504110418110a0e0d080c01150603 72
    0x10901c0301c14026802005044240c141c150241b0b5a10101d00c4240c0b4a03181903405076800254506060b000c05001e0f5451209140c0812940e41c500404024000e0006105810030059800c910a02480c000c0d401464181c903610142d01c1c10f0326090400030600e90184400300c1c000c8e40103401c0009031202d81403089082401040524150454035002c00c204144516015680317503a594a0000704402c189200c0d25080034880e0000c034a640c903600405d421940710501c0442803020b0468070f8a0042c18050074503900c43d0400d00d0060312a298008126010803103100003c1d010302c6500300803110206488581810385120350b409100d0000d069061006010540d0001002d5040034012a80010441e0304114031101000400b0181c250791100090241d488004000715104030015040c0464069014550400b02d0a00801e011355444211452968468410380c1d0080000116041c40c1c44e64032400241250b5410401c00c80c3c49071400203100b80248002d01e252546d46007030450000b901402801142061810280 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 918676429 1250 918675179 918675227
    0x230603300f0d05090c0a12061d07030b09060912070b180105101e0f0b0304081e0301091b2102040f030627020a03020105070807052a01 59
    0x85024840340d9030482a002038041881038101c000741d1070015081142c0340550220f2541013240e0010b040041403180d45010382d080c5131052155500102c01031030102c1c0e1000340052144510400e61450044c6403144115600070540c002080c0140c030351030540183c9020090750810b40b5000501ea940d0506400000c1007400140698404140303006815641f1040c241460034000d12040c15450071035000301c3e091851811f41190501003444092901709100c1d0000381c4007c54141041212003844980344a10008504000b000904000415007691035040e0200250007070750f400c1d0030300890180c000b40a1054018900003c4009145142103420b0307006260352a240090764003880f40800b0b8100f1071401c2400680c08020001c1d00300c030036055420080d4011200040c000c4c120909103002c1c0b00d5021140e4250b20402c82e07112000d070303943c4040700007180c2d424207009940b920685408030590207171800181075805082e0701c015603465400c1c03502446179440f401007100c0d8158030005460a01e038940c8240b40300c0302516 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 918677679 1250 918676429 918676483
    0xb0703020702060c070b03090d09050a09110d020d091505130803270a0c0e16050a0311031315140a0504080903030403030f0e01030612110f04230603 65
    0x103030080030340c0e5001a00513490f140b018240035207082000c0e400080c5480d40002046003004043c00401001110b0786004a01280b0308000181c11002c54000d0102603a44d462a00f200310b9491310407901c822000c200155110040d0700b40d46001449040010b85601d00b1102004070310101d030f032140a00c181800105803043d18042c1c2c540f945150401002804e0f001034504100409140030b00f580d040e024030403001802c03003440c9460f1107443d085956012000c0c01d6424001c0c864107441c04900440604d540f483d04e1030300c2c1c03600e061084018240c00c1103c80204180002800860421b90072104030340ea029003240d03500e021940b800c100c00c503206104c0c5000c50340f072480d0205280d9005900540e03000b501070f08500d824080440002030440c1c1c001e5100301e01040060410100355030f082400c41c11444000d00b01002000d2600c04003c0070401c200100520110700d9032829402555042094a0b41a801500c200b015681e0700c00e020b00d080d450904500c2c07449480e180052402c0c60005034290311148000010410700c0060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 918678929 1250 918677679 918677681
    0x221503060501020a1115070609020f010f0804061517030909010b0f0906090f030f030a0801050102120316120e100f02180108040f330e1b041509050f090a0b0703 70
    0x6a44069031056204c80346d20307403005035600074148260044900184072909481001030100125050710306006c04408041070198100c014640c7c8503400001c0030510792481005014031468542044c0100ca100c8038101140f444004061703c0c022405071608110b50b600d03030003038007031074002c0c8000100903003410401c0400c1c0341882d502920704c0700c40241c40c6004e80003010000074104109011080c0f0f9a40c1301050038440d003540030341c5150041c1001c0c001350134010340d20181d04466102c0141601100d01c6220000c560480c070a070301a02d40f0a20032041000100541d18803c0e0300c0300c16200300b100400d828140185000d1850b03100b10b60800501180405030602d15000646015034000d20581d60010584840000f0030f24110a1046014211030400c03601144204142d000340308007141c81102d145001c0ca241d400000000b25150042d104031102da0480141c0c00010b4090001030081d103660700c041d060700042106868010b5400740000b0b46030f04040d80d6410007010358443c4071050181040101788042040d541c02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 918680179 1250 918678929 918678953
    0x9010f061a090a0f24080f060405071110050a0e061501031107140a14150109270501050702191725050f1209030c0f030102221503060501020a 62
    0x10241c914003d1070b640d0070450401075601ea210301d900c04402402c480b080030114a01107400d80041c03c1540e501e05145440713042c0a803000701a640078a5840c000b00d051180602050151003941d181180e802e58480814003010700f500b82c1d814029107007443c804480b08a004141175120b4010340b104481c03184c1040b40110040c20100001e5511207004002d030001003055401242440c03d03090380101929165454502c0408180c0000d4007480c0d0000d601448a0700c05091010f811145206000700d0b01d661100300c40d000801c82d4040d502074040c0101081700410506400180c4907112a4094074408400481c003513014501e8a903000b02061000301101c054a80504050701441e4070020341c000c0e420441040c0c2c860750120190068800e603012030b440400c1408108000d544002c8000c000345d00301100d16022039134270300078441e8051141c001c2640da8a4103032000d41c10758494000700888441c007142805000c00c105201405a041c0c01035140b000e0016072030182c018503007200c80680c02000010f5990320388000303000b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 918681429 1250 918680179 918680197
    0x203060c0d020906030c1e180d060e010f060806010b0405090a1806091a070e0a05041806060f0e34020c1f0e0d120503220b09010f061a 59
    0x2509201406444d2a030070040d602c41e40312616159524084003550001c10700f21400b10044a00d0104a15a0f10750621800007114001c00c1c1e481416001442c41c1c02805802d069400d5540b80d0b00e03106000b150609550400d404460380d40043c0c6241e640c1395030521511784580d009181c4c2182c01c05001c201031800682c03090074042c1441d4100c100101440d50340c20306440019000f0359210f40610511079264901c1400740f90410034500b0054200d032104808a401c10605100d072718882c59448441c041e02003046500c48404607440700080044a80341c42281c05103644602800303030034800720400a034044994030960250100e0701c0301101124194221105013030042d00b0304040444c0941d40d0014180c1d22a841c0150080c902000568140301000400034555441030b00359500c15910503010300e000ca50290007a4980200c07a05e400b6a40390703120000c81083d5230800c4521000c038007058528900707008907561020f00404e1000000d10901c80070413003044c10750708030780501001ca0103d0700589100f180b1400007014420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 918682679 1250 918681429 918681431
    0x50f0a020a0c03030807020607110c12010209060c0106030b1b030609040203031e030106260105060313080a02011b020c31020d05010303030b09070509010302030a0f0e1c0207030203060c0d 82
    0x40c0c09070785140c600e190b903078821408510448140010581c0501019034094001d00d0701141d040e40e91060380d41e490310702c02e01840c0119680040f03228503400a404903008140040d05042da119640f56085008020b0782c0f0080c2c0f81d10800001264801e880b804041401102e5611541d0640d1a9801040b008800150080340c0c940b00800c924011072917080d107424512041805902e48a40c03401c280a0983e02c1c03034950140c0ca2074040d000300c0490070584221303141900d509031440c03622035882c41c240c00d91360f409040000d0003210020440520880c0c2c1500161801500031a444499030301955007686e454a90450080e405404483c1c444031800742040c02d1445102e400b0078585a40030803040324000c03a808004500162901c880040c400c1c150140510146c150003640d0020203450051001041e600075441424109030b00000810480030140d08038046040c0c49800c00c2001d500628001e5540300284c5000100c0c103080c0c02c5c450b2420a0012a6400440790060040d184660720610819002d80c0118420340b011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 918683929 1250 918682679 918682693
    0x12115020c0a11091f1406250219060507061d10050601090506070b0703050604020910020c03070b040308030115030207080a020a030e030d050912102d05010f5f01050f0a02 75
    0x48408c085089942d00200b440c107044001c90f0050007008548810404034698a45a04010665000303040f2010740e50030a50026042c80d0382001c5140c02070340400000380e6440740740205c0c05d0702035560784243c1c0500c10989400101c1ca54940034001c1e50300541340045c10a450785c1e0000381d800342c026007003558030a03c02000103182983c0040050b40460009001900581c401d280c1d2000c1d6080030040240907000401c086e904080c5107641d041020b100500030307022210014114130100f02c0c0607405842c585a4000ca03a95140e1820000095880141c581d099000480c84d080e00b1a45d814045241c042c0c0c820075958541ca003039080c40c140300e102c500450030701e03005120310030350f070f120288141c45100c1c1c000b030034000c50701994803400c0b180208044c03888900e030040303e00d440c00400c22116000c030400215001d6190481205d1051802c240c0222406a41548207003031802c84103003003805030149544803220001c0302803c286003200301c03a031825004258042c0886c0080105a83e444010360262103400c03003500c120b038030f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 918685179 1250 918683929 918683947
    0x11090409110616021302091c0c080a0b0a1b050f0a050c010c051b0105090601050d02060c1006090c230f0c030403030201020d05012115020c0a11091f1406 67
    0x1d03d0b80104401191038284900401c04c600d41241d8106600c1178084007582403002010010314024545d111807170090910070f0f41602003108034154000201008015540400705504250400c0602240d0400d20309260890701030078460702580c0000800c2840d59187e040114042c0c1020b00d0740d204070484070a000007803110b072001d04024082c454500039076a41d40d585030907010342e60b01c0c0c19280507071407800243d06090801a140030300080c013a0440c0c10454040400c0449400410500d1050030000c4000b80902d8094034003200722a004802280e0f0b511004000c0381148000444e1240c07000e44103040200350105042c0701c041e684074003800c03848030540251450110780c50441c0340785038081d5204601503500071400840da00d401d8444e9034010a00c10601c43c0071590001c0b0035029054080310001c11a5044107422854410240e050b03500c0c040d08203044940d01e034594141f4052f01c00b11982c1840c4581a22000180c880b2140c001012198215803c03060b110f6042490703c005075000d00204540100c03003032004ea00c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 918686429 1250 918685179 918685189
    0x42a030c1503050612150703020d0c0306030201092c0402040615020601030b0105040c0c12110a05071505160f022b06060b09060d150b030103150f1109040911 69
    0x4000c00300008000702140416202030141c1d0002411644150690001d09400c1580854000c11510031043c8034a81c42d51003040640c000e019142c030a03921545044492002d0700d805074444d0047e24001d132285500c3d5a960b0401591850207a08900c00c0c580c140481020100c20140004d904588014004207640c0d4031002d0b40d800d0300c40c8244603140103034000360041040c0003031012a207000d4a4252018880030341200000b030211032484078000c05206645c0010300b540d610604102c80300c08a01c9098540031079040c1020355948083e8045c0d0a440d0381e052188111490240301100c42c080740450794850b001d42d035526892440e2076862070a0b43c10030003242c0303440380d112850501306071411258152100c0c80002800e084086525a403c070f8031200c41c0400458229070303169001d540318001000d0000c00c01c081300840142e002d0040758802419001c0c080004420046804503140100aa854042040b62030032204542612260980c5016640c801c210182090420740c0001c81d145004140311107042c424200851 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 918687679 1250 918686429 918686453
    0x60a0e0612100f090b0105040b090a08060114040e0a0f0305070501060f170c03060402011b0f080301081e12030601030c2001020a170103110409030c0b07020d0314042a03 74
    0x2c0e020004080144038142e410420007001d0000440108940000ca1001820702e1207540034148505c10041a5a081c41d030781e40c80000c0140140b074003582c8195940e0341c0c480045075445a03209100700d0409503080a4268000303036803810142c100d284074520700344680317060340c066008441c280c48035501c5010100710380d0303069541d000040c40515841003103c414031000b54140000013207454802d40098040c07002603030b80710b50083c030302d00d125003e1820b12380041d2811103840160620001e000c0c603004000000c00000204a003100713210800f03280720b19a112610b0240d01c503140d081c80c4204070001440402c0c0b86510a503c8840600d425041034071600201c0c3c1394102c4502c5140e04041582e81d000282c402006510a61405402d5200b078480c98095042d50b031110600d168032440c85000c1c40da109c282030103061040882c0101e10ba0041c0c82c3d4081410310100003910b4016605234500441e0511903048280e50442070410701c925044200c0c0c104c51f110710710403607511140d090f242c0b80c41000c0000303000c004150601039030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 918688929 1250 918687679 918687691
    0x30c140601030c0e1504020a03020405031506210a03030902060904151502030a021908070210181401021b04060803120f0604150e0408160f06110306060a0e0612 70
    0x246103962642c40c005040c40c2c055045104082c4511050001d0007040e8000705540d40005c54000d40c8583d11750700110001c0c00703550b10056261181090751040742480440040c0150170603038081100040c2a14841002190b4030b05801076680300d5034040010a1186d0700c581426071005004d246030802590004068079036014144081c1001a117041001c05031000305001c0c901d410340081c50600d00065006506c6000e984050420700d40104004030410000e901260b06069000788602c19040b041031000707044051003041070070300c04449000818113103d82c954003400c42c1c005a0003001d210900c00041b414055911700f16603001a2240300116414070144041d285400420080c042a894072410010449074041c09140c0201c2c80e1031040740111603142d1000054030f440d03845030161501d9a00c0c041006126846001c1c6080140304000b1081000003d14940218020740003400480074001c131200c2c4078802503550981c0a03404000d000038903401500c110b03810a0000701264240160300104488140084404e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 918690179 1250 918688929 918688933
    0x2070f12020f06090d1d0a030605072a0f142a090609060906090702150a06031109060604120f0203010c2007050901061d0d05030c0d05071a04030c14 65
    0x100394928010040b10b030b0300000c000000c0c00c1e01704008501074203424141140007000d10351802e0b255820380b01c1560110013954041410032551800740d00003001e10f44181c2003080498a000800c400c030301110b180000205400101c04140402d096072144c030501800b9000444a000325070101b4000d0081c0d0102008620400300b0038541161650104410014000d00180c818440d400c00d01806031281c0245550080090301e070101c0c20340b540a000c4e4a404424802000304244000030890010101c1e08076a080340e10403a0b82c04401c2104804001c440d801c02c4482d2134100c48140810090310400c0103120600314000d40302049401203c5d008a403e40f02da04c00450f01044000d03002d0100307800f1201e205400100d2810141c900c01d070502000407072100040c401c8004000308865684041c0d94100b505400301a0020000720001300c4a1a1a03520b98000146031412400b40365024501e060249044444003907000c4000030b403210700c2c2d8050406030702c0081c000780c0403c54000d41c00e10000750255840e4001ca074030000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 918691429 1250 918690179 918690193
    0x80402130f02090103060e010b07060203040302251818061d12070b09030403050309010e12030703090e070918050703110c030c071d0403030b060c07060905090105012102070f1202 78
    0x100150035502154004640c0d107411f980100218000742090b0340c5072940c044005640d944550030100c3c5090f00d1400c1c0040d02070005144251611044a010000c032421103500501c6905003064030400c90b0070750340c41c2e08003000da00301940001911540c4440581d00c1e64130400c02429500343d0790075151114180640e5581080050a0000d200c1e50030340c8668051004d82c00ac500e000d0955590341d03201c1c020f0b103070200e046c402c601003c004269103440c0d000600d0140081102c0d12150b080c02c00500003603103446150800d80301840454211845191480c0607130f45070000110900328140358100003000002c0030241010356400348501d001c40a00d0040151104010045460fa01c414981d81d00b044140d602085144034880007007950040c9208185900603014140002c0044112001c100d503840b9603a00766480e4001c408000c02d11175008074140e4142e48043d07031a55103a0782c840d40159000360f4180611314440d0010945a00b03800b07500d80081003c1b5114880e41144d01036140c0d00d645401008403200c00c09038004070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 918692679 1250 918691429 918691447
    0x601090f0e1e0403020703060519020307080411190620012405040b091305101509060503030306280f0b0a021006150c020609030307060510090204030b07080402130f02 73
    0x2902c10890b03185040c48010a8203040d0360283d030300e1941d4030008000c1c1d03440c0c0002822076a004817803488481110b80056569280035107000b0b00c006005c980403260760100071140d02190408440f65620000b0b8031207410891400e00105070f80221456500d0496441c840c0d0983e03206210a0240c1c540180d40c0300c5418a00505080400c90700511700d41200d03020342c1c0350200200150f56440d200c103802a100d60064103890341c660925505180c00d02c0b040071440c6082850301c6040f0940024444201d800034802000080d0f10340040603281e00c426240c0551000c40010010020058a003060f41c1c00c0c070b013024694090640e141451031802c0c0c82d5500007401d1f0700d008144500995010300c414201c2c1c191180e0204174071410031a901c006074989002c100208100fa40c030840842d00c54100300c84044500400f00e0317844d4946d80c500340010f4501202d08090034103803007030005403244950007580c060b81d07803200e0003001d2a9a00c400c2201c0c1e401c0024010fa0780500321090000d08107403a80300d14441042041c0b005070b501c03401a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 918693929 1250 918692679 918692701
    0x150e03030409110903060c16030f020a060507080a0b010305130311190b04030f02031e0309100e0c1002150601031a061b0d0e0603060f01090e090606010f0f0c0b0601090f0e 75
    0xc00690741c1f0350040003103120401090900883d41945800e050301c5940d50300f00101d28010010200510356403814080c00002604009528031581e0452030600c6490314603c01102525800d541c3c0e80041c11080c00d040300000c0c040c500703155001181c2c00c00c41e1000003e80a0210080014102c01d80781004c0c0b030360130b000506521190509525400340001c518055141101d0001c9080d0540040710094010003c64035919003031007900b520428881e0103019810010107010344a20f01c005c182c5200344490600321260a0000c10361380c400700d850340081681740e0b5601c401035018120256549854403806a034a0109a46640141c261416007505034400b5019651000d0b207451014000c180c18000013400781e403550350b04c8604503980040d0a450700d0180f01807580c0140c0e0400c4040d00100301d12196001009000e9200150b803034419070003603a5035600c80e4840c150030703100c070340440f090b04000070403c00c07004001c034241c1c1c250036801c20f0040c0b5006c0d046d01d5592209502ca401145c00070b1005c02811070602c1035410b10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 918695179 1250 918693929 918693931
    0x6120c09030c012f01060807091a01020c06040e0421201f110405060f030712020918060312030a060608090d0813030318030509011206150e0303040911090306 69
    0x1c20708040d4070745040d8904e40054010088004401c3e200c42c0410228625800c1d00b201d80280020801c580e90b0300d8035481090041c003100014491020407006050030030750f10020b00304242e118050b020701c3c5460300308595014040c0c40144240c0340070044180c000600301901070800c0c01002c0340c3d541c40c00380d02c5440c07540c100d0000b9295280100c0e030303002e40b80400151914040603003914403d40e40c00100101c00c2c0c0e00030202d5018590106a0158010444075480c5503110011481030010740d80b400e10038215101d10b04201e00418641b940c10a01040c400f00ba840c4c1e142281540000000301101c281d089042800c90181e48212038a44103039440300001c2008076040134005800a0310b21000d44050844c40344018600580145444030000c00060b408040c18080d074040310220442c02c1c0303440b110039420f090151060307000c0141b050005649005944e84004580301c0d410903229010034007211030620035012101d41103c441016890b000401c40018941e01501c40c0800c0d00001880b03407500c41002e60201401c1c103030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 918696429 1250 918695179 918695203
    0x60209120d0219020d0c0902030f010902070305040b0a031d01200c211306020606090901090b0406020a030b030604051b0307030b06060a090e130507051c020f06120c0903 74
    0x4480c0c9011441ca81c1c0110b40318481c0b4511000c00710700d011403400000c4112a030610090005c1561180100703540500e174000314890410038a00c1d107061791342e80f001041240302d9048003800040041c0011300003520000700816402030b8510703011a00f00c1d100e600c4a003180c09521000c5819a5540d003400910260f168600020001c120a50300c1c2011403400059888242e1805042300c07049090500c0c504020f0000f081d43c2c07030200285a1300341e0184e01c801000c1d5940400361100b610944100c400604164414021000ca29601c038140b07a1154440c0d556447c040e4100d92840c00034907480306036900b800d880400040348034500440003030119010844907403c2581c0003140c0b85001e83c10403e8184003245501c7c00d019001002668041d549041c1c041c0102d030107100540081c54076410200522045e40012500b26003414007400c2075414003030fa03c1003000344510240d1040c1241441e403081c10005440c100701300d4484210301600661500d0383d032120103001282e00f21404506220049084841400d00b00000c4070042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 918697679 1250 918696429 918696433
    0x31005030f0d05120601141b07050a03081911010e030d0c0503010b04270203040f0b010b040f090b0a0305010903023007110f190801141003031202120406020912 70
    0x910350000091551190080100c1c2000c08130010030300c16403144600b607d00805458007103490320900091244101c4401e111201c3c244118100032a4500d01904440202e81c5e0180d13420f450171400c541000e200c01240c980e00e00030b020010040344030711402800307042000889000034658801c00136003414201c1d00420002010040c0901c014002c102c40d64080701c0c1581c0d03840e05001558230303a07251042400c24420350584980c80c004002d2204104110b2203503244e46101d0035080c0c125a80315448078186002c4c81c03044c0068661160030400007110b641e4010000c01d6806004400c50780d440303888260950700c009038200c006900519600e0b002d04d0081c1a20400f505001404890310545141c1d6401c51b03015041d00a80710f581c0091541c8250b5171a102c41c400021400b0b0080c01e030041d0b070010012003528071b611a80340a0350034180c1200c808000c41e502030b445540380111b88104941991411280111180020045d0560812004140e403d0600e1120710845c442c29001d80d5441c19041070010240c050b44680ca015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 918698929 1250 918697679 918697693
    0x50906211c0f1202070f021e04110304032715090312090e011a0d0c031b020c10030e06070507020303041d01060e010c03020706120f05010e040b220305031506031005030f 74
    0x15013042846c3d42c100b60112001210825004651040003c441801e02d501c42c6c40c0c40e0900c600180c1140145d07100c2d9000c2e07100d040071080c000410074540382c1c16810442e070100f20141c09100742c03100b81224031860805071801c8100d4545980d00d03400a50712100301e1a02180c0e003000c08014420700e1841c85400344c084485c400100e521103805848070760094485810707400d911800d1505085109501003603c0c04402c101c4450302c0c03118580080e45425440301603e02881050700b0100e01c85000e030041e120706254407402421a552400002c0750290081c1c0d2081764075010800000400c6114805c1040420740e1801800705903500d4164041e02c152803907414241400742028004022980100e6a54101c900700c0c1014206203600a410800401018585880c09440c1c1400880c01d450b250603028419445502030803040c0c0c440050507180c0b01c0200385504840d1038080d00100010384030340302464104940086254500e41000d0005101e60000c0300e407480c7c1c00070040000c01151074104040508907114101500c48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 918700179 1250 918698929 918698933
    0xc060e0318120a33050106080703090c0b07031106010303180905070e0424030803011a1c230c070204050c040b0d1104080312010e01050906211c0f120207 67
    0x1aa40781c140003a2429144900044c000603940d90049200151103c03032060102d01600302c1c2c0c000300b4081c0503c200280c0c1c1c001c0000d400710301900c81c10000ca5003084d02080320501c0c00c07503814441c1c0d20068080741000b043e0450404e50380307020090107001e10712070f842d003d01c0b415000d08000d00080c0c0c0c591020941307905010500082903004501d8060310241990040344460102598907402440f008802402c12a8144000300707001006003e14141c0b854070034002070f83d00640d205205280200c00d0410031070344d12591110010300090f440aa54002c502070400540c0c59003128a0020841c1241d03070b40b031015000200f1004500e424440c071a031164811b038010707013000e090144000d46d601540d400c0b0564145c0c0c0c3c050003070400401d6001c0d2401003002e0003c50741c6d908181c43c0c005500071020701c1741c210b4050000b000843e0f9468020304140c415800078000041010100350712070261921648405a54000e2010b1500d03440b070004a0b00e02c108070700b6101c0090342e0140c960000e00c4005070000d4035066606c18002000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 918701429 1250 918700179 918700183
    0xf0207140c0105271809030c07080304050a0b07171603121b0f1707050c0d0e0607110415031101091706010e100803030703140601020109030c0b070c060e031812 70
    0xf080445490951300d6110b0310380124040107a045c400e07407484c501c241c082049064000009054014a107001d440280d03642c2e1710340716942d0286000d0550b002d0301508040c800d60720f00d1005845128012000700d051858400007000c4540c0c02900d1a40044118010013014150042825403505e03006c01400c1101003407803900300e041d1096450521040000b84920b2886040c85030004803954202c109001080f420200c802408076440504c03c1304903801031154020009002c1ca010f01141c10010304903e00d00100c590301c44400301c001441050380640c0da184000280102e081e80303880918032460a800c51100c410002401e5006182d008a8046079080c941101c2640f010031401d04642c0d143c01110f113242c40d90040c07414400042e4000255070301c004001c00566a034141c002681c0380c0c89022101c032180d00d40c03c004a00b40c40c91074402034045080c00381c8810006800010036036100c480307480c040b82900056580c5e1015a00440030b0280c45900228943d05070000203144544654000c489600c02020050f035415 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 918702679 1250 918701429 918701467
    0xb06090f0601050a0e2106071d040c03020d2309010b06090402160f03020d03050c0a1b14030d05011a0a2a080313050f0c0d0f05010f0207140c0105 64
    0x9810007070701003010451140a42603682c1703085070043c04400e14840c4442c10041c2501e0391600071041344540c80c0400d94031401350a0f1b02c04600460521500103601c25000e000291083c0101207040590800c504410882d00384900e8084002082170002845400b00b0720188000000e0200001d5914201c90105255034400c1110403000341500c0250702c07000541d0320101c0200d01c0000c00341c02e038402610003004050b80412020800011a10b0030005915961141d803c580180301300b210100390f07024800204d4000301c00b500c1c0c62192081c081468850054210325083d42c10042100c030700aa104e100510252961a03c0b031a000182d4a030050308103c50200c0013418400780550900c01c0440e00d0346240b81c0c1c1007824105259a40d0031600b001c2c2c0d80c0c00c0060080f9184051000260750300c0c0111100d440c20580b010540ca0009a070081002844506c1a00e0301d0305a08001a4219910348d41c440010b250503195002403ca5580a018000860003010b515181020100c4610741e041140130003210121b007266400003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 918703929 1250 918702679 918702691
    0x702010305040f080708030103050613030c110a17070501140703090611010b0d03212d0e0a060c14040b04090f1d03090a17030712021002040807030b06090f 68
    0x42915219402c020200712400c14001d4000000024801c061014000c0114120ad102c1e5003111426590000c26021180392084000c2c00982c9040c03004000c00d444a034400a6568010f06d08510381d60f03980f428821190050140840701e070000001000302d9a0003000c0300c2006805041001d20b0040155401851400c45000c0e060030f0003513002c00c0300e0b08640258451080c00501402c40c40c0e040d01c040c100a001580040b07800b48283c0d240a00303c030004171717003070280d2842603480c100100c2e200181c0000944038a10250010a10150f0318040000031200030824895212700039080000c11410079940100701203800b4000582032001000104040d04d481c0c01120119821040c00003100b0312504011409001d80c2005c0568001505910000e005030100003090241d03412103c40448030f40c4e4074034181c560b4070410100c400307a41003406484041524140300c03036140a414070681d29003805d11003846080360015008200b4580c062482802046072a1000070f8026404441201891401c950000c0030b1003001020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 918705035 1106 918703929 918703931
    0xa170f0f0c07030f050c01020d1503030206010e070e240706240e370c020c09040816020307050d080702090105100c1106040f0303051206040c0507020103 67
    0x840b200e40364107031103500340e1500414065031580c00c00962851195002c100c9092280d56a00c83c0d44469012085040174150031401d00901d00581600511140807519050246064104094680031034084840c2100203850981150107a100110480c18041d40855070004124a40d0031a070b0781200548104080c00b10b40b0141e1402046103031081c149041e120802191500294038500301007a480030000002140c01c903050310070141c54151750b000400b640c03680650030440c2d05226409545604444040590815860f5080a072151820000e0118811b80d4010b007107440902003000104001812044c9109013030030500ca41c0d40c440c5030101c0c49000d00d50004100b61a10a240d080342c8003150392400090001e564602505264248200368407101c18000001c1c0b014516001074040c43c8a981d980303440300d40c01c1d01440c641640c00340545200364240441c840c41c0c1c44c0d200f03050303414094092030 = true := by decide +kernel

theorem cover : BRFrame.Cov 918525179 918705035 := by
  have h0 := BRFrame.cov_init 918525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 918525179 ≤ n) (h2 : n < 918705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
