-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4637
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:15:39.579982+00:00
-- url     : https://prove2.me/submissions/4695cca6-ae67-4629-9b69-10a874cb0a4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 833812949 ≤ n < 833992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 833814199 1250 833812949 833812979
    0x6161805010f0804171612170c1c0911150a0c021302160c09060e01030803161e1110020403110607080f030709031101030603150e03070503071a01 64
    0x24007140c0c1524221894511032082184d200d4410070311004e1040b0703544904e00705c0307402c00b940f40000782c0c5106a00c00300304480306c0a04001f4194501341b400007107600300e20741c00200c4e00043c444100c4000100e14401c0e2240c0e500010f50824402c000c04100c00011403d01000f0058084582401040c4003800c80030144640021902d41c1c030026035600d60b9405043d400c200007802001c02c4602441c1c0c09102145844002507d12105240703e0341c14407200918103403287e410b8550315030180d801e450502c2c0040020400000840354000380603d42d0314840a4050300640302e18850070f000c00f0841e00c0396156051580e41040307108a10340d522504440817400200c0014040e84200d0100900344031055800c0c825038100200034000356071161200d06c2c00d090b00741d42c10001c560012103461000840001041003413012400400584010a280c140582e80c1142c0b998410b5801f078141720789210b651004070041d5030b50280242c802d000d07800000e49580341341c80c1c148200100f0920018068482c0441c000040f4172164440d04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 833815449 1250 833814199 833814209
    0x103030f0806090a090c0803030f06120705090a020c011b0201020307021513021009170705040b0102011b0e130e0106090b0303040807140a080f0703120c030e06030402030f061618 78
    0x14001d99030351416200064140017404035183e41c04402e0110782d60b00c0500140d485120082814402c82c40c00408010890059070b24400c03854016020078442c40c2c54520300c2d160b122051000160341c40402d80e02443c0105014140c5d8902c440d50400035079091a410f4000b54069012542221200c0d040c03030b6404080080d00741c4000511418113500c10005042c40c00c040c5801a083e800c24001180d500c00c818200b0b40d8451141d2030a40c0c00c8803a091101f071070180308107a045602031000300500c41e8428580c6d840b4019081c034150510803040e5440600d42c1d69207000602c048500c1205200e00c04880115501030010b03405611145030405240c8891420f0000646088582d018000c010301031a00101a0f031031245403000c190000070450000c2040d12081040a11030020303040101802851400d20b18121041c61040c042004001c2c2c092402280d0701000070308030000308407076140e0f0b2500c6500c002490401510000d070481e01818080103440040701c8104070310f00344070384c69994a4020000e18103070315200034020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 833816699 1250 833815449 833815459
    0x13020405010533160503122d0c09180105040c0512150a030f1505010f14060306031e060403080a0c050d02070c170102040603110301060e0112020d140103030f0806 71
    0x403001c50241d8030042c2e00c000d0403000041c0c0d864062141600c84038131074030803001e8641d640300140c41445800919131156012510302d003401c6080300f0420310030b0584803109900319450b2002001281014000304200e80c082140200092641d615651244c20403500c241b141500c40d81c42e10500350b4401c0c0c024000c640b1002d440c0300c0400f41c99503842000301103c201d051600c41d0021081180400010000260307290182d00501c211801c581c1010740042c00e840c016040b82e890200e115a0400500102c6812100102d00481d41192642c0c2c175003000c00e19084030418480ba0141c80c074180c141810b0700c003041c2280100c0c0240c0ea5138240e40d5a070740c0c620058030341c2803c090380081c400b0407005031880015030141c201540b01e0074607100425664001c041f6000c101c03050403076803654009401c2100a13014850308440d0307491060002d05644c900f20f0060400e02407980031505201181c0341803800c0103110780c120740340308201000c2001840d840c6141c854101c01c00340401c03004176540d0700503088020b004900302ca104000c020a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 833817949 1250 833816699 833816749
    0x3180c271e040c0905060415090b1507080403031103071a0c16051e01150e2208070b0c0c060705210112030201150e0105010507110405130204050105 65
    0x2014041164000d0500d40301d040c80c118450300d00c000d0200907900860007481001650b508000000c021200007504092181c0d02d00307030590200e01030000a080403100c80071400a00c010600f00803c5074000101c5c0c80400c0b070100019104100240e05001d801078074000e0362821103401110341075030b503a485110700240c800001c0040c0b100001c080b80c49816400304d1191000d41c103000c2c10301400c40d8500304200c0100c0d01a00050161140c5241c4040000307518170050000b4014071000c804d0759a03403602c4a0080c951402c00b40340018403150059103218a030b594845864447d44001803d115080e43c014000441d44c01c1e0051010132100d04001c1c05652a0304000809030215444600c41601c49900c114800360b030207051200d80180c51b030301d0401203038000c001540300012400310920b4001e0850300c0d02032031700d0000070161005010b002403144100e41554002c4c2040f0365908214101103c011582c2ca0400e503015060a04002c000c003e030302514801d0a100340e80a100390717601c0d07030200605040580400640008160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 833819199 1250 833817949 833818009
    0x40f09020325020705030616080f0604021c0b18090303180c0406090e0705010f0203121302060a0c06051803090108150301051006020d14030112110603180c 68
    0x94000d68006034500c041640c1c591000355070b180e603070302150010303809a009a14104028107081c4083c0d0307440b09062501c80070b040703030701000a0561540581a41d00808a00d40080c0b455100ca13411a00300501d8680c0340c1c2c040192000202c0050a91103449034001c8000002014582c2000b550395070040c4018805582940c0e52801941501000d440e4440d0780c502c81c0d401c0d140c2d11b580b5503100780800b40040c0c44003c5101e10070058024900402076000700c0c104514580400b00f46039010081e1155294616a0390f2000e8651141d00d04424501d280003943c45003001030320411080e00114500941c5110b54002e025564070700348201004500900c500c8056003041082d0342e0b4541c1309000c60b03a03000da044141300c2d00700485440440d00315134013141d46400c207000d01101403042540401080d00c4152aa20344640e100b840e01c410a4224001807089010381040c05029800f00f00c1d40200c60110f0b00c201404070b075101d01c0c1c07030308140e80c05491540b207001050160b160042040e0900d22480740c00011101c08484c2018020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 833820449 1250 833819199 833819201
    0x30503041706130f170f09040b03030a02031e0705010c030b120114011412060a200a09030b0414010515130e0a0b060319111c05460c0b040f09 62
    0xf00c102180c1c05400207440303d480252a1014141880700303d806c03d6110a042010b21080f1220f20700114801e0b4070511820310505c0e800001c64540303800200811100c200c41c080031007500d000d61302c0024102d50074000c088118642c0b41d440022444000c0390302d0841d4058190f403c5088a040000003210361030410018450030898400c0200020805032100c6840724400401504040f01543c1d00404540c50302e01d040d404946641c12818141e14508905144c0540c03540081d04c4807003a032000906074800c00001606000308111040c18160300034009016600c0c200b01100200601c04011034401d400200c01058034032410310030701c940114490010700280c100d83c4c07181500414014003903503052040e6003d8103085600704542c0003902f07105601c0700888100030010480c002561205910a2100d480392510208100007068214508140585000c9001c94010006e0340c01001c3c00b899000c40340b00811803002d0301e17911011103441c0d0150080d8840d036500c407021440148070f10310800300340f201080020b203c01426 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 833821699 1250 833820449 833820473
    0xa12050a081627030c0f06091d04201806030d02071a07020406081009030801140d0b070e0307030302030408010501090507050301060e0a0f0306020309010c1e0503041a0103050304170613 81
    0x3c54003950400b141d9039a102950344c011504180e010b00c0f101c200400440760130034082c4014040724070384984001e48400d0030715200d5000070409005540081c90880c068a0040781483d60058060940d46041801c82084401100c055840c14064844c003107080304614404111107058900340d100000c2c007044410754440c04c540040e40241ea21503514000001d4100040004003050140c50b01c01040400190030084d010401c142c1c8200c02e00040070407401c42603500c961400f180740ea40101c003103045445684d802ca8030913040b4010242c05110b000302c08401d04d50000701034000c0f100390800a00c1940e032600503000542e030f4107403620004903030140010b2050030302a400b04208a0340c0917040e42d042a6607500e54030b0542c22150720a030f49180e40002800705a04080c040c101844200d8201104c106801c090098521113400b00d0701400c00c00080301140811102d0f80010f00380c00454000e41c42c0c20b58403418802d489520034032855950b120080702000c83c451700400d210341708484007521602000b085840d88000201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 833822949 1250 833821699 833821757
    0x50910050c0d06080610090c1e030f0c020f101b05030c130e150d03050a0e040605121e0601121709040504030306061706061801020a12050a0816 63
    0x402401440e14840c0c0354850000200440340042045003006400881394a076942c0000349007e040c90012003103127411242080c0005002c000c100480c0041c268114010865a144100d5007070130b080a4494090380013499981c0181c00905584a050300340c1d221504451070700560782d050030588000c20031502e00420140d0381c44001c00e003005160401c5858480807403a4250000c0181031400018040e1050700c911402c0c101100580d01011900c2c201e84000d031850050342c0c809010082c149165400c1c589480c0c00150007480041c040003803140c130328000261510102c0c3c0030310b901d0617040b00011aa829001403564121501c3e101c007107000441c291100c21101c4200c0701ca40055110400899046444500c00d0521903402603400052507400d120b4010aa80340b816500320807100500140002c9507160012a0304008005100300060940200141d04050382c50b440a09541c144401802e4044c4e0088010080e9030f000343c0d5400c5c081c0e60780500d030400020a500c10140000d55800f40360079003030380c03682d0070080c0c041e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 833824199 1250 833822949 833822971
    0x6061b150b01050c10051605310b182706040b0d050a050a1209050f040b010c0c0308090a1a07030809010e0a0606090f060b0a180302040e010b0f01020105091005 70
    0x910b484130341403400d050091000d455507682c0042140032401c5c000c08600329699450b2061610812040200c0d010750351101161000fa040c088100d500d200009821000f0544a0440c50b220765884000a4141c800e42c0540381c01840090f40c103440b24a0300010710358030140c0e405080c0320161940000e120050041d41007517a00b004800c0c210202041c0c0030400c3c181e140e84035900a1043e1403031460300c00c0080c44018048024008151824040c070340c2c030f500e0820941c80c010394000840d04600c80c0100d954201041c0040c0240440700e8001c4288a1280018002920300303840394030110350f4503c11540300381302602d90456200c1c03013486606c0000e80f06038903560b0001d0588002213023014802502d203040c03c0004004035007003560ba41d41000101000d009054080241560801642c4e00d000c1c03da03584d030704c54546284104090b60011807040482400408040c64000d0170810102e801c401d88030340200902401248102c05003c446c480d10b42c03050042c54402e07481c40b070103007d075004060307819005000d0203031940e000e034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 833825449 1250 833824199 833824207
    0x10209220609111b07060f180f150e0102390618030615030d11030c0a030509030c0f0f06070f0b130b10030b0f1f0906061b150b0105 58
    0x4036102d40504810f0910440e074a0f56100b011008680132156401c0380c0c0800e40d0044c50040003000d0300030091a100c0c90582c1890100d08000100c03a0880031815000341c00001c070810710104000701c00e0300709110000c5403915070310203c07080e140040ea950349d0204d003e01080c28a80342c9540b03000030303003081c12454681d0b201040c8440700386440c000344031504840702c18440301782600c0741d626a42ca01006032035002540890380080010f416400f294171030301404008070901040e8030942c03503450410800c0780c0e404410001641d0034810300d03180c010180d174070030410f40d84030b40b003900b0f030041c446d240000c208010720f040113200315102c921080a00500b03810206041c0c4d01d07213884e4004640450b5500c922603120740e095010807801d0348264900454818409030450340c0c0a00301080510002d69018041d43d04074a0103039078480c040e0384801e21031050969180d107000d505c0a0719000058007150710f42000040e03070352a44524035640040c0c1c904d05981c2c0d036103800181c519041c6102ca030241c90007590180c0c0c0604ca040c0f50041c50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 833826699 1250 833825449 833825459
    0x50a0501061415031902031e010e0103060f051018090204050117060c0c100506270411040e070311370e0402060703030b0a170313080102092206 63
    0x8541103a40300c0c007004000c480e015003842c43d080c000c0d908095580300045095042c051450155100b809442c81e030740503800804502d0b14144004e80c41120008200007500d550307191102d10013841c1c820b01c001c46203941401da01201103021030042a00c181500801482454a44219907411400d980d41126580d40d44800440150701c8901419029040448400352081d5201890510f0a000104140216038080c001c02181c03020200f8485e60080400402240c2e6403105000120324040c0c81040d2a10b040a0296003e10203070214000b0380b0483c01850300c22400040c90043c001a52a0100c000c011904039038401c1c8002140c05101502d1580d003e491000c1c0141c616000d0203460840c0014421000001102503620030742c6284036201406000400350450b040550105060b409050001014961aa401c1d004d0320703100e2455100042c460b99071403024401441508940340c2c0c1c45070400140850625001040145050080303034000030307014001210207a4507000b01c0340b8140414440e88900381c0c81302d00000d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 833827949 1250 833826699 833826701
    0x308130210230a02030c10050906040f020a180911100c02130b150d0c0f080103020420031503071d0103031b050106091407140f0c0109080309070f0b0f030112050a0501 73
    0x10045166001176a5540300140214075000c0c520913402da8040c00d04082003650f040108510341c10541c0100410301c0708601f03200241c0007161030f0b0003030070745000b8034036600208000d40e4001c6010140100100a40c0541c80024003205000110189003c20700c114200d0005050000c0c40040013030001c3e40024414a503c0e001501442096204025804000c540b03000030400602c9402049100e6007040c1e290202c03036040107092031742d05200183c881eaa81d4820424010301d0060001901a10038041e1596403a05403060310080c00c6001886009202d02d601c0400c034150018a02541c401e18051400c151380c3c03950f5801c4a40d070080f000e90000703d00d001d081c3c00000540c24081e81c0701508074014081a1900140080c7c00c3e00f0000510300010007420180f400d0800d0100c900721443d601005921a80d11040b9001b83c2c1c2c094040a4801003880c2c000200704101c818001c101c040c00c0c2ea429a82c00403225507206030b0599503004803542010010b0741000104441c070b0360811900c01e024401d0f0103503400c51070184c0f00d41d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 833829199 1250 833827949 833827957
    0x1c06020403021903140309090a0207020303070c0303050d230c1b0a050703061a10080703150f0303031b0e0f150c0d0305061014030c070f030507030813021023 69
    0xd450442d10783e014000c2166201100208110500c01942010500b40c0001c55203100036151000c8070f680040c2100541d01e050003140c001a401010000c40e442e96441c00510030341c001c0c03c00b20505441d01450a130300c0104800300e16110181440240d032143c440c004071142990102100c055101d01c01c00e042e642c4d51a041c810420564050005400c00314030b103007407030004c0c3c0342007540c8940304070465841c00400d035607071001c060304600503407600c03002e41da68042003035000380101c010a0225010110340050501040c1c101101900d00c40d84d01403007241c200424001c0b90708107408c3c030074002c500e02003540101410302c5800194040d00c01450102140d0b42c1e0320719a4000d5001c0b0803c0b00c0b8075003215945038001c17031709801515004101a07a070020301581c10100203040310305800b203c90380a100007011401e00c0c402c84054a103442d405c100d010410780c00e14603019016a000c400110042800c50001230103607241003003001101c80d000350a00e8805c4000d50003c8401e5000d9010011290380c800f11560402101040a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 833830449 1250 833829199 833829229
    0x903030d0b030102070b15180919031803080d0b0906060304060921030203060f0a08121803010e0d142b11041d0105040e12131503060e060307051c0602040302 69
    0x400b040f421f2031020302c000c40603001d41c012001c640c00c0007805180c0c0d03000a583c428400b188800c2c40301162551804855442c1090000d8000d0411400044144203024004010310703408442e08101ca51120014424546000c03a0416030181d804e00006000c00c000390000302a0758070820082c0d0500b01c1205880c4001104140018000390380130040210702e05260418040c07220003101c000c01c00c5c0b454444200d55840c0d04242c0c1c041803240200780500d1207038500b500b10120b500000c0090042004060784156601d50030192200014040042504850052001c648e000002d064600b880400c0641c06030110200c280301d0a41802e5489490f140307000c40d55005400940f410744c986442452800403030401c030800c1070b01320a1040d441d011000285000c00240d001c01000d100003950b40b14012089c252a400381d03603034400c0c9000c4d82200c180c440102c0d0b16078003176404d5510300405a200307a04c0d45018035940d40564000ca9400c40414410300da80b0180b0302c40d9140c0034909c11000540f5058803a4081035a0198035108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 833831699 1250 833830449 833830471
    0x30703121401050915010309080a210203040c090e0c09250305060906090c07060609020a031a100810030c030b090f0a05070e100b0a0e03120903030d0b030102070b 71
    0x12200c0a800c03140541211080502108034003541014002800d00602401d00c00d01404070040d0a07001c1c0e4003d4001e03c0c4c940da0005006ca4a070504074a024104156440c250b841e80a00f026802c80300341043d00c242c034007564200c85001e4015050400395801400c22008400061150032404441617a941c8030b2244280d815207030714044d0344d40d5010070b150014892440c3c0c20070715044c103007041050b0301c030001d109500400c11600c440d101d80760500d009889108600003d08160f0601001140c1c0c0a11034009150044003903a007008040c42c2010700040022030220780c1540300c0b102d1418000c400b84960543c5070050b044145c904c10303d9a403030740c2d8030f00070f000c060f071007250400c0080c0b041201c030210034401c81c0300c0120907502401c95130b242035591586400b44c9000b1054040b003400041610008900040750140083d10320141e5210160200a0400344900d5200340c400d1040b89080ca4120310050281d40e58028041d0046082c8080403a8070b101901149004941540d402c0c844007010948541c003040c09a003213815 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 833832949 1250 833831699 833831717
    0x31614010c09080606060708090d1e0b2a070b07030b04020d0902100e030d141c1d0f0c21060103030c0308131e110316062712080903030703 61
    0x21034603080c041300802031380c4560b01c00d0102c0b8011417030020032109030f071300211142240e480795440c1440418110b44c40c40b40000410001007001c100c0120021070184d50000f10541c03248000801650910b400c1d01c4072000c811900340080c5000800100c202600201a030034046522011440030404a8200c0d483c80848039403a6081c19095091520305095251181c5c50030100140d20f810219640705100f14042e030130820b4860f00152000c504074159180200903100010a92041ca40e120014101c1390441c24002d81c8a5214422030a0380043c3d0716440c0c07600a006400f150105100700320340d68030001c0c189041d0b0200301400801050007488034030302841c80394584107240e41040c01d0007030000c84d00a240000a082d10a0b007280881c01142c040962400f40c40410601e4028034036001c1c005020007d03100f9058458091078108000c000705400040c0c8146980d04200d5024642400240c4150030b44281900e000954051020740c4201000d100b546026590461614800c9404070345541e1010300250001081d0388 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 833834199 1250 833832949 833832959
    0x1404020c0a021018172e090c0501030c080f071d040c0809061b03010513020705070f080d050424020319120c050c0c090a0e010204030807120c0302031614010c09 70
    0x9451000a051340c2090601c03a40d0030724417116945e00c4954a844408150400c11a40060781078012034a0f40030300103001d01c0801450b2070300c01c1d092105400f0300c0380800d05007413001070594881c0020b1807107108101c80710b2141d9261510250356054003140408401516901c680280762214000d40714070000d590342e500c03298030301104d900d405c0501c040c2410341010402020350301045068402d0320305542048a03444c40b4050003d0101c3c00070710070f05030000c0041c0034415001420321540022007044542c140281c0c1c01440454004441c0da02c168000e0110b0441e0124801f2000c81440070304003004c0300140112440c043c1c3c0d52009480312048415100005148810407010030f56590240760700070a403a0034194104110a464551581210307080d0754002ca602e0b800160784c6204a4008082c400010b20003151790341e4580c10705c0d20a41e404110705840381090b140509000382e1050701219045074141c2d01960400b481a070100401048400080c0c030700030440d8140129940d820700c10000c028000d6210403140910704 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 833835449 1250 833834199 833834237
    0xf0f060115020d0c1e12090311040204051815030f0a0221030d090c18020919030b07050705010219180603020f0906090d0813031103071404020c0a0210 66
    0x38441c000440d000301500c0311485400001601d4456440000007614400c02030316100d0004801001800e00619080f10111094000d001481500d000360502034000280703e0610090740300d284038a0790440c841c1007113811056620100c1c40d0b00f010143c0503140c1c095090b0b42c00a071030b00b03806c45c0307402c01c068210482e45e40442c07400c1313412a44056200c401084503420f01d10030640d180c0c00380e420349000c0340342c8a01e00b4400300000e8441500140c07400300481010410140102c000940001d1800390003070807010b801c60104040e9000b2034081720f0f030265241040341d803416800c4400d500700000c00c1319299002e01001f11000300e41c513400c26110030160382d07018568482003284c1d064031410781e110005140c8100414000070540c40d0407220011070036904140d4688500e0081014103155140c0a803a66a000c180001c84250350038004049030300400c01c1404220820080644828030780c481c003420701c9c0450903107002c1800c00d83c0107411a080c10300142c9035280b507030750045000c07605560700718400101c0001c2400184920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 833836699 1250 833835449 833835479
    0x2030c12150604061803050111040806150d03140c0118050105061e0f03070906081e01150608091c030c1116060503091204060f0f020a03200f0f0601 65
    0x118940d200c9001c0c2a6002041441c443c5001da14200304040e00e004102600c0484024000c641c414001c004803030036000d003140b65800602881e0f01502452001c030341a0381ea003a031072040a01c0300a0903010b00300c0075541c2c19112818074442441c0298014071201e4141d480a1040303456620b6003108c00c400f2401d1a251075070071180e0083c5014860711481d800b14507034a0f4426200800d190301a00d8034200320106000080c42d241d5550b0000490f14144031000c58000c1020a07070030070010320300c0c08000020f81403012413400c0e036081103c08004022070f02c1c402c10805224410140e000710800c0161458504040390755403500300940181d40c0802d44403600403c40b5944102000300b26050341c4040c294542c0700d007010003d002018860042045408408986c1c078101c1848801801640441d8481d03a65036100800ba254480f00a282c1010401c400c00e0004091700129078480350036415550f450391840d0100c0c1c4030707044014202610800d40b041030752044403080200454080074032000014040b96142c91013201280403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 833837949 1250 833836699 833836711
    0x3010518100308031314070806060a14040f020d1b0908030a0206010510030e15090d09050906221401090609020c060a0203130b0c07060e210f090402030c12 68
    0x30031004000071440d01e2002074041c0c0350b00041150340c0340c8440691541c0c0918030070000d0511070404e540e542d44034074006650002c69100c0000d4403c240d490030200f00300b1550501c154100114031403410f4015160aa0003225106500c100042c141000c040942c0115540700d130410201508181032030313450035046080705d4020100a0003c0d0f1404c0c1b1603060094030361030103100b84c0340a102c16000103000a0300a40000601d0b8600d07104944100944108104400c02c1c00c0c2d840c43c1c9a0b008400d85648030b00e209103038000944a01906a00c41500c0d0b41c02448001c084918601e8204d80381e01e0701c00141c61506019444000b0315178801d5034542d50501410008a034846d0f40285035451040005c15111100031070750660040303807145d0068803955502030101000c0921078006044840400030000b680c031400c8041c0030903d020760410400b80b030f4000320301c85c0e458603004124410007050405041300c07996a1402401d586e1800c002680c1008070403401b0a080c1d8100780c030703400d64011000c601580360b42d000e480c205921107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 833839199 1250 833837949 833837989
    0x1032d0b060a0b131806081204030b0907141c0b0a020c070e010e01051e03100f0c090b04090e031b1509150103060f09141e1c031d010207050102030105 66
    0x904c40790604880c0141522518600c039030005120041044964821002040d13580705462104000c80d40c8032140c3d074000d00045488180000105001000001c0d8140640d05105e905601c90080d2504000708081e05d012085205454003807424009500d4401c0580207940d052409a00d40742c015600c1c6040140507001504e01244503030042101040006401b81120300c140c0b0b54004e030090701c1060380c050b079054100d0701360036103c2d441c010713640a80a98014100c200b02c0d40420010058040303411140d08000c0e01c1004030025062100307016070b003241c0d0710109a042140302141d2134011000d18108403e0051103003076816401040f55002d03003822210400e0351200e51003014103c0300e20808510700c00e41a0600000e0b1040b541c820027a01d500d01107910004032190890070000349075020000d9150788000700c600e5041007140e902410803101c0c20004440c0407a00d00b407110002030440f9250100c005014180c48007151442e0300701682108002840103080070381c0070328005680c03507040c0401c2c856114500c0091881c41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 833840449 1250 833839199 833839207
    0xa2c15090c01182103030515030c060903150c0307090602060c2505010f060807050d020d0b0a0b15040906170d0309030315080a14030a0801032d0b060a0b 67
    0xa202140c0c000341c01d0002d090041d03894061070400000b01080c3d400907140600e9030f0403a90300c003e00e004020559a80304e44c2d4203200c29a54115180035560080c04c285406901c00001c0d16107915100380542400c24024040750318240700c00303402d15485030090b06c2c0041c40d050300100381300105902014001c003426450006140a051500c0d90041a2056000309a201c0f01e058610162546070302c4111424150040001e03c982281b0711100c0c0020142449042003130301c580d076800a15401c0c0007104205003074000f0014a02585a51601005050020140001c59540e04c034603055a80c0c417035178075042a014001007144c6030b508003007504084403065003049200e40040070484015031f00004411080c0502d6207800300d90b00c82c03e4036040d4090540006500000d124500e0082450900041c0d2815282d025041d000417403103260141c0380e168400d040f004000603c1400c01480494042102100720074a0110903100504148400d46424400c01c803040b05d4000c404001d100c00d030724060040a0103804940e164500d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 833841699 1250 833840449 833840461
    0x20190c02010c0b070249020c04050c2a24161206090c02190c0b070c120f14060108060a27030206010632030a2c15 50
    0x1202942c0c01c1c0106040c1c1d003000041d602c24801c0c401340c4035035042d506505008200c003072029036031142000a58007019034441510000d07098101b070b214204c13181c1500a401100c22801c280800b6150052410900103400c120042e000e402052071708402c1c8120541d119141105010f201c0d05099a0f0011076064410440403180000c004560a42d0051190010150480242002940c00d1080360414a841500d09480041c02142130b800ca0307450034056900752080041340c03103510100c01101c9080030300200130550341808003a1502004201060242c41986801c647d101444070710500e251104a40b0080416035680800030032070040303c126810040505441c0d81005080d5565a2004014541c400d03181d000c4103400004050004036200003460110010414500b03010f56900350130b108110010301c443e10040074000c8081e84030310303508510103041c1c02c000081700e0008410780c00160000c010150b0b10981c0541c00c074a49002c0010765101e4462001040b03580360005800c0040322003e940000da092810480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 833842949 1250 833841699 833841707
    0x91c02180601080a090f020d08031603020c030405012109110a0509060f041d070906170a03120b040204170106030308010b2514070b030a0b10120504020420190c0201 72
    0x44d0000150303c3c0040d0030b10090910030030701d010b040006500031040c0307040d140c18005880001c52164600200c02d4000d052007403030444c104e114160012507541c1043c441401341390701c07890076502084680410341c09402520f052100884003c483c0c100c03401c203002d91954611342401e8402c107004000403584a2500d00c1c2100100d83e881034203a010502c00d0369100901d152508100c4020f01030036a224046944650301c3c0d02c80500209100c2c000c62003d20507034180c4500d00c07000001c200ca002a4155100701704860001c0f00b01c40a401c010b00c3d03130b943c003507004e00022a244880038505020030f1465400031445624504010340f4001040e003182445e840c0401141c0440c8000210b4202d56921100d01d0b000d04403413a04007403264000c64041c40000b400b4000380040d01d00d51000c05103005480740c0030100145800e8600300510711900c0d140e9031001c240c0300c40303000382d014510b40e100c9940580041e2000c1440740150030102503000d012400550f1508000c2510103a50f008512074004408146c1060389903500341d900040c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 833844199 1250 833842949 833842951
    0x120907062c040f021b0f0f01110f03070e131d0607090b09130c020304170c0109060f11010c0c030e040209061902010b1306060e031c030e0102091c0218060108 69
    0x240103d0726500042080c169940c101c4404521416030444518100d511141d02d8144440ca400014822010306200e503c1040c400c0010a0407440000c906d44041c944482d809604000d0a00c02400b040c1d812450301901c0d2070030500d043c12910f900002e8680c41000100794501a000d003400d49690043c0d04211211390022080d40640b4103200712540c9600e514400645040e2602c41c80070340759030500b021210440e80000183c0709a542d1480c1e041c00030000c0f03440c4a03540341820108140050b44c03402d802c0040c03030b0146914502609161802400340401f80300c5880c250368984041c4400030f103d101054052580c80788034441030080890b015858954000001203050185c1e06803001d0300c000400c4402e83d050b0007540803040d04d0a01070040c2072140488422140104001c2c415440810030980746a6103914000c50394048066a103c0301d10026030300c2003402c40050540e00070140c900d66082212009964400340d51400c55140d000a03030101500c43d10501c580660301000030b90b58103141b1800e00005a0f0050089 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 833845449 1250 833844199 833844287
    0x10207090e01180c0503060121030e0301180c152102030c07060908030a0605040509100b0109091406041113051e0d050a0611040317030a0212090706 65
    0x3054200112903850700608960700d02c009921003855a0f2020020b5103015081111700840c1920301e540c0c9d0b21200c00ca0809070f05034081c1c400c2045e405840380064092039600c9014400540001610710000850801a00c8040d20556050212820410030710800c41006d940040840c40e10310081c04848103141c049080200070344101c142c010000810501c41e680940340450b130040c4040c440b0300c14a04103148103610a80f0b4403069903090201c007141d00d05103070043c41d020b5840300000344094500b20280200920001ca02181003000c0c0344000501000c03e4002c00b080c1421410b244a92414114208002c490150409508004090000066014007003400604842041c1c07583d28800170300208290710512206070780d41d84041441ca03218103201c80083d984841c1032040404004514150000c1c008030f00840c070004183e800070b611095141d1a10300040d580001700000003608044401a1040d403117042101c079010f80b80e0201d24100801540040f80c5810010002403080d00300035404542110191a4124 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 833846699 1250 833845449 833845451
    0xc05011103030c0f160c0f12210306050301021804050609061302030c0412030309050601060e030703021311032d01060f08181207022106012d0b04050103140601020709 73
    0x404c1d0300141e0310408681e070031021584030101000d41458250300c0d40f08103000c1c01e400c40000700004a05c20202000400ba404d412003a0b800c58040508040910045015410390816481d02c4001680d500c0900181111480c500001c11116014005000888000414403071054040b00c003404000c0d200d4000130300800252100c0581d4a60b941c09440142e446240d01c08801c0700c207224030035410b040c4d065104608007071055043e6546030341d03140d0080382c2e03440c83d80c00c40f0380d41900906002c01c018605400310441080d5075030740c00f05401d01402c4403e0020b40040340c4540704003105c140220070407803441b23400100300c45035a800c203106541000002810001140b52207000e00103624041001c850f03007500000306040600302100c030058401c54466000783c00c1680100d0281008540c4003503c80710060714060f114803440c000381550b80c40e11402110706603a400c1c100482139180000301e078001200c20040d10240002c2c4940319582c1c0d1500b0001002c5a0000240380c02003600341c01807003034a03a0701261040844001c0c1300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 833847949 1250 833846699 833846707
    0xb0708030a11040e011706041104090507031b031a0f06270103061505010302070503190c0812160201020304020a03030f050d29031b04150506160c05011103030c 70
    0x1c11403000b440d05650940001c1e9000c01c001424001c0e2420842c1a64079140c003a26104000704001c0f55500f000b0b940040416141c0c031340613003c900345a403282034964054011511610b41e03c0d00c43c0200501044002014481d0b421020300620200c1a00d0811590445d4410881460311480e40500400d000c0c007510303c81c107000080c5800003030080c24900e440c070040c0c1d20751020039656464890010441c80c18510000003e910000405600031310a680b442034100e005145480b00a1170307895000103801700800b0900074084482c8000ca00803d01903c0307280e00c006101c101d44d05003280e0989240142c9600d10b001c6a004004100c0180c40e00f4940c182141e40c50708055001c454070410541d0140a40c00304611028500b154040300e092007460581d00c02134000200003043c0d1542414035444442074041030848980c43c5113080c00038102948801114005425110803c2d91100c00240d0554400f15100b080320300d40313611003c20300512295040040c142400d180044002e42c1f2000394880c00010700700440d07074401103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 833849199 1250 833847949 833847961
    0x406030615050303031e070e03010f090302010b030c0901142407110a150e03010f020d0603110301150b0313020402030c030402091005030c130e01091202070f0506160219061d03070b070803 82
    0x40002346560008000f4440403180c03066000040500301c00560040d8242100380b6200e00780425407050120000d0700c41909a0b003005100045045c0b000070300350f000390225001c185480641c20340a180d41d001c101e0240c0e5601075508041c14824120b20f00300780300d080122401c000c40c0160300702d086a42d4141c2c0c1840030440c018440000e00506400c08110742840c00090840300000840d0f00010540f0702c9108682080c003c00c10500d401ca40070419014801a0342400c02d00110706440d025552080440d0301d6405048400e03804036084e0782042d2130801d4000381c003106000c118134001c200e05500210003070200554501d041c000039910f01c90b184855006101511542103009002e81210600000d400028442e200d480c0c9030216085c40441c2d0000014064000d01040590805440030101c81b80106a50b00341101401526940c02c1c03002000c0360f209a110030070690038003950014000400060f00c465514103251361400d100708492480d002c1c4250000350003440f200a0400a5131040f60304000c0340d54480c4d0b646 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 833850449 1250 833849199 833849207
    0x1e0f060605041e1a30030c060f04081917090f062701140702100204050a0b0a021c03020a0e060c0a0809270a0605090f0c0c0102090406030615050303031e07 68
    0x51144642c1000c184061076900402c1c003c4420fa80750036898150b200c03485c0c0407418503103e01461202004903003214006c949080c50303440d00150058001e841e290710b030080740624030b8000340b6110074583c007042e001d0903e1094502daa445030790f03006402e14007800340d5220554150351100002231000d1500c111520405103821101d07904513828000600c003c00107401980860003000804480d420010301c00c0c030180d01003800c014003c4d1012500c028044900c6d05003407002414443d00080318210451181e03501b0440a0002445682d280900a440040e56001c1810380201001400c07075215003d1750003003154411036807000500303200054000c030603291596003140c0014111380060403106005000d03d03036807080815243c000140036941a140400c00c403680c54060041a40007120b0700304408044100040595560200501e680c001d030074001850403441c0d000240884166400643d407080c1d4950000c60081c964003500005000c049000b1820341c64502c244080304403c08007c43c1c03da55107003010039100313809 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 833851699 1250 833850449 833850491
    0x20d1b0801061706100b03151c030804021c050705040e011401080c0108100b0a0c02210a02091806070f0302071203050f0105040e0c0d1e0f060605041e 66
    0x4a04020b20841d60b90b1104603c100e04800081c81840c0504404298180444c84901c02140c100c1c0c41c0c040d00395138585010101504024840c241c104485d111103d00c1c0010b0101c4550409100e034441600600f0240180300052000c5c0b041d600c038894207000540c0101e400004d690084401c01c44c0d02050100400000b907000d0458801d88072010215240046540b03400814104105942071f82d9400840d590040144207075101e0b4812020420302c1041040c62291103942420744860003e0890448041f484400003a490303c2020301c5655900500180300462424040e62908100500315441c0d01c0e10541c90500c1e2500c10242004090141c4091000b030001d009030142d83c00150003180309006001c4841c0040e01500048810310200d220710400499070349031622900c0c418464000c003c0800d090b4407012701c104584002c01c280d4030182d20300385801d0b100102c01800d0200900c00c001005080006203031071421f543c115000b00d0303c11070401001292a410b0500300c003a0400603640040b83d1000018410890400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 833852949 1250 833851699 833851709
    0x31e0c04120c0e1b0a03090c0e010b21070215101d0105030f0a05060a23090a120c050c0d03030f0515100903110907021f1b050304020d1b 60
    0x540514200d040c04207990519044501d803008003003150380d4131491220456008010340c04608810b10000032418400e5020701e00036881010710501d0780d41c84440e80309048000340d000341c0d420100055500c805000c5001d003842c0304a03050340b070022241401c080294844130078145282100c0000400640c0310380d0341082207002030078009a40140e0f0300035011491010b0109010301d60281c031414588840c41350000660000a68000000d041a5260360f4102005460301140d030840448246094510001110070650f0140403800c005000405062070002003d180d0840810288540810301801217000840c0c1c070402501d04540a00d0b180d403052030150b004018048500501070320700010005440490114560700100c02c403841107043c402c8100860701c404582c000108801a8580402854100449050703048000c50040d1403100b1520b048225070b100301d0034292600c182d1101d0156010359004641c1d0580400075103003580c503600c1c203500407800b4180302c140010007910100120707030f034049408103464006d80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 833854199 1250 833852949 833852969
    0x4141309061b0503090c09060a030203030c010605010e030706091404231b0c0a0f021203070b01091b0516050708070305030d060e240103140a15050303031e0c04 70
    0x104003414010001c01090701c0c079442c0c07503504484400c1c00c80d000d0402d80340705482d41d40080c42080c0c01d48040c0301c14104081d12540d005000448007000503501480940000c0c0101030000035000e103080001448900034490081c02a040f101c000d0210710751040341081aa0080c2c1c00e510010118413011800500e050400040e44101902c1d00c298030b1007082208038052680708502d0090461501d844c1c1d041d1780b04444044203981e00504800001440c0c1401503811640020b1020082da01c4442e4004c0c21036001030400c0700c2e0005035000612007450b8500c55050400700400145410440f030701d00c050100c1c030034400b0100c0300c505150344a01c2086400c22040d8050950f41041d80c00343c030b95900d011a0742c0d03004001c00b49405810f240d408601120080d80f064802d0500c00075a810f041e5103d1015a41d411124001504044d10707440040c055031000c4400900403214206d0018240e28204003440705d2044a404c1a8440c0d0020400c1c88003490560004281c0034ae4000500b004d1a221f8000c51280b40c131450703011038804 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 833855449 1250 833854199 833854211
    0x30f06060f03010e2707031b0f0e040c0f0e13260a09050d080f031905040c06030f0603260c01091a09030a050d020d0f0e01050a0b0402030903041413 65
    0x52200240c04e180129852003d010041300d000d000c40780c016800380f461003155440208100007040004e004d1340c11084002d071103000e000703845030714079034103002c99800c4402d0301140c1d030007844104828043e000340100920318060f81c0003828a188598040405020029643d00d004449814495103001c00007a00f810b107800403112030403010103035801d41c204407544008100350110008590802d150300100044d0f004031458900060440045600d410284c900c21007100441959256452135228013801103024541c1e0080040c5844001819500307103040d03074140d290802c0e0040001514080000c166000c0035003400c080d40c140010121481e0180c00100010396080c0030034070043c40038200030010009013000041003c0c0d0350f0409620355078403c0d81c0c501d10014604220140205d644c0e42d0240c0000c5541c0000818040c00c84101c0360242c2e050601d182000c0d9640c1c5090159001881c800c01c42084070903101981503207050134903030381c4900507403060000d80d6880b0b03040e400302c0c3c1d500d14541c0c40352101c10840030018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 833856699 1250 833855449 833855459
    0x250e12070f120c0b0a05070f080301090606020d0207090c050705011d01230c070f020d032a02010c06020c031606050907050d021c02131a041808030f06060f0301 70
    0x90350050344141c058040c850315001c00e141080c0001c000d00c035074003d00c0c2204500d00d8076a06480951100f00c1e4441041002c0c08608005407801030b500d000c242c0a00076094482d41000c0c12001141d031140e000c0710555200d1b002640c00c1c1900810310000b16000c210b00000e118100802c2603481d48280c02c0d00826551804280160f03d0403d68000c2042c500280002c0001d03200c85c01445000100c0f8800164201d401c2c2e00025004041c0d140003803c4d1030f0310410220491140c41d0307000c1400400550341c103c0c04500c4402e2056004c1000d80c0500a0000c00708126805411094001030a01c42c2030720005402e0030303000101c030000e51204000b1140961510310201c11101e140781841c0008001c1901c07984418041d0010000d40c82c9424024060707401c2e00104801d08030300c1019400946402c85010403030700f041c014040601400c800344504190031508402985520341904104400c49203101070b451a104030100d0450085452003040e664008206601403145d07403204400100a03004941c0400318940c030020003c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 833857949 1250 833856699 833856703
    0x10e0109060f0501080a0609021503090c0306060f060406050304050f07060504030b0901020901050d021803030a18050303070b0403120f0207060219320c030a0f021203250e12 76
    0xc06a000309010400710301c0751036481c0d0940300c080c4500c400d2039010309000c10118206501002c80248000d051030105c0d424032000744941d030002c032082d08403a0040340c40741544d81018008030354444c104842e05241c40c3d40ca9000500180224003c55003000804030004013003110030041c40c1d04216109080781e41d00e9603141c01c020469401030108a84213041740b408114062814000d4850210307051f1200c0d410441040055402500305410b148441090f113400e00d0001c0d03c043c40108007503000d542e42c2401c410348080c403041d4640751b5544a54000e070300401040c0f02142c039200403560015410310b003002d100003070282c1300703c05401861143c81c035051000074610304214245d4014413080c20030581000d00c04204110607904070a210300100a81404007003640c4200c5085409040505003969109003811440e039091071550304040290400b01e04440b03582041c0e641c040002c0e04254016a41c09455468080c2900d80060128001c61015203c40c1040701d84550103030070285686078021309500c00100204290a0f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 833859199 1250 833857949 833857961
    0x10f35010f06030203090703080a021014010f06081b1e0307020a0b070c1a06060d0f06050307170c0907050702032a040b1e0d05030d020a0f1715030f010e01 68
    0x101d06440180800140d1500a00a0b82c1c0308030801b501403c3d115265032a290015840941c20100318001e00f940080b03003525910540d0451011514142c40d40d41c10111168450400f90b009901801000010021007004040f5220740b0090b284024689502c0c4c022800d140b409200c0300b801d0301811001c800c2140340d580c001a4601414000c1c2442d44003034940f1801602c502c0810720b0040d10b4210302e0301801040d802121142d0fa00280046c14181c9416101c81d290130845406540340d02d121603c0740c42c01c01081c501000640060642103030301c0c5aa109400307801d1607807080c8000449003da1021400240c81d60f02070b0080c0e5018540140030784031420307005451180501682c0b8803054042c0d0080101c00102e00b45481852078400e0003411f05110308195454594031400c02e05440d5521203250105100004c80c140050404480c6001c805615070480e940c002d130442e17186101c01d0040281440c205580780d102a16041d400142e944d0500000d094040003080c2007500850f00c0340000d600300303c1c400300305050551042c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 833860449 1250 833859199 833859209
    0xe1b12120d060e0f060103111b0c030f0d0504120206160b0a05010602160b0f130f0e0a1404020603091e0c01022506080c0d09080a0e040b010f3501 64
    0x1045100c1d03c4891000d06041c00f5648042e0703030107020300000d42c5540680d1041c22503003200d44113981001d410715500c40007091442c1c20603c0750381003140750701d81d5802c040000ca0300d0315200c0b902900110001ea14010500d000b10703c2000da01403954140b00b411f64840f401110341c050b068050010784000706017440410040f003906e180050320b240000004240d0320110700441103482e04105080180c0c074101d800380c41500503110049607000100044032003d450200f819006002c1e0140a088280c07134440c0007000c00b24000c001556150408910f1090004409106948aa811280356440c0e0311900d950701e00c0c00065040c3d40d100b8480d449080341038517200181c40c0320355020980c03c039640200950b9608c0c01000c0960f80c0030310592044241404014010b0b00d030150300c5440c00b41220700b0301152a16902c25180108019a421200014421012a409045400c0640c82520f0900c10b440340301c80020300301803607200c1610411400c800051400c1c10400d4020741c5091075072118000d85036401e15051030103e000e00c070b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 833861699 1250 833860449 833860451
    0x10c05280f183209060f0105071a010f06020d0e030307020907050d09081e120f04031b080a08090f0d050a050c060a0606020f061b072109080706030e1b12120d 69
    0x210100c44c40d10001640c8141406881801800702c80001520a5000381c2000c980c0603a407500e01d42c0807030030524800d0340242101c450303407d84030786441c4d4041d00700781e0395186410400c045c02c03400c001c4c40d460000445100d254140c50103062030340d4000040303949003d10009401283d0814513500709000039000601201080086050400413003181041810701c2250160f04544144500180901900c6c1112984c0a40641060380e0400e504082c190920504a07204440d08080401d03c40c4505a01c50b031165403026909004100b40041f0b124103680e68004280721074200080003801e24126071044040c3c1e03401704003c9046070401c0c200360980c040642000e00818005114002d14000d004400041c09070040c4e8045d203146400808201210440f54032820043d00c07001251500c4007c81c2000307113103240c403032a41740d6240f0100600386014207042c00e0071540040704141c2400c65180d94a000418402081200b181c1c500e0a05220440800c41d54619820314582c14000c1454401440d40b4810040001c0500628 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 833862949 1250 833861699 833861789
    0xe0105071107053309090c040807120f11011e05120f160f0c29060427110a033e06070c030203010c05280f18 48
    0x180001041c184c6440c2051140b9269094400c0a0218040c2c00401e20000980d02d000d00042c04900d2440d0103652011151500003410054500240401c1d0040c26012139520284034860f00c0d04250500840005002404c0300d006000060703002d96244820400341201c42d8100380c0f500c00016060350440c52204103a40d034842d0000752108a00904d040c42805284801000000c07034042c1142d921400d440807105015050286202055011591000110b007000c0c141d010074186c8038410500200c0a003600307000700c0c280002c00317102d40081a204602c40103070702c40c00d442c0b128290130f20301003007a52210b1007504090341c054040248032804440b0711031209079525840446c0b41c4000107a041c04201070902c881554074580840e514607180005280c2940100350040300c40da105d4000030308594540d8403010100d00005405809848626040c4500802d503812030803641c60301e5103018101d00d0312008110f04020030601039282120300d5800600182040300707101801c84800d0411703586c940e441c0507008244640e00748 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 833864199 1250 833862949 833862959
    0xb030106210b0a111210210203010c020606010912030e040204090c02070f0e0f0c0c01060b0c0d020a0c171c0203030105041b090b03281b090f05010f030e0105071107 72
    0x1004030303d00100c80040f01480c220041a0210804001620300d01c1030f04044400040c0b241843e80d01e084074546000182203411b101f40c8101400c451502e4107800c10364000d8001c0141580c0c104201104a4a0b40401840d00d601c1525080390030320b94518001e940302e4800b00707010403803004660042012a44980840d40c40c030b0344a0352040c1882003140b240c00b8010315034a0005810316008007000d900900c5c2c04090600f400a008111402d46c3e4068005410700724000c540444841e00030007641e01060f9090000d00f81e9603800c3d44903641d1202040c041c049003010341c081c0c2000222001c004100140000e4400c0030121224a08003d403254420321a180c81603080c0800c0c5505101c1c2c07001000b0042c80c9a1f204c0342402842e002c0459069007006042620517080704000e03114145440c5188400c400007590005140404c82c80c00401d182e004211a000f004a62078080c01921502010740301a40c07000d09141402c490b2050084000d0009488500865420a002d0050080e08152145846001d81007610b16a03030300c0c0d0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 833865449 1250 833864199 833864201
    0x5010e06060a2108090a0306140a06050f0307050f060702030d0f0f090b1602240301170109080304030509031c051306020102160f06020903070e0a1808030402040b030106210b0a 77
    0x160f2245510303000c1d2403240001203d0000034042c0f844040c02000c422942ea44a900441d4544440010100351190401c210100c3e03034820003002c3c200864401e18942840c001017070781c4080d2402014040d400c640c140b0310044c1e603080166071a17554024103e5001c060101402800e0402403403c0b14040741404a041707a91030300900b491401d550140080c0d03400d090050720380480040030410240d8206562100040c905600b4400c640d0307003050a2407006030b507549000a0401d4521510b441002135900d41a040b80008002d5803c81e900542c0520b82207440e468014006810140c1d0f885140c6048032204e0001422140c010000e04480c080001d6130410241d518402a820f07407250072808101082048440c200084016000b031651900504005042003105030200e40781042580100010590407420042c2c0410782c0d000e5011190f12060642509090554880c0c6a80c040500020b10031921170500c15910f0300d095004d00024036101c21443c030904000c2c08000d600032005002925003100e80301c001803400c0302c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 833866699 1250 833865449 833865479
    0x201050702030a0518120105010f17070f2304050a060e07080108070512030705010203090303160c03020607080a0b030a030f0e0315040f170304061a18010b0d020705010e06060a 77
    0x61500d03000d150100741605550b400c41440300382030f40034801c0a0203401d02d0200b44108c0d80a031803014110081c0302e00f07200111101c0b080e40b4040c00c0c0a60712500c800e109004004201a048070107885101d150301e00d00c0c2d0f03481c80d11400c0441c40d01d90054600340030400f28203019000074040300c00407041c5007000d03110400100d6000b003007401041c900d94030110302006241003100c1c14041c0c07012014207072800c04800e82e80340e40c00e90b40141c585030030030f50012050282020180b50380c4485181ca07402c0c5101c1c0d10f25699070180d181c0300010200e8040c0100b00c00000d406d00c1040d00455401d0000805940f540c00f0725250151590100b02460703070000703003070200d680f0050800103a15050345400000c0764501e6030740d40c4e44c2c0740c0400d4181c1c0c03003c660729010301407140300c6800c0d20b0000e90300503803042c200811280007075210f0841e400e80385000340744030300484c551120300088501100b6054400807006113076a80c1c40c01083c040680304030310f8014025845d00b01320350b820410100e402806010b0407184000d00d07980d01d0054207031210b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 833867949 1250 833866699 833866717
    0xc1906140f010b1606060e011d071704060b040504380103021c0c0b041a0405090402040c05041802032a1603210e01050a05160c020d0b0c0703020105070203 68
    0xc001006018020b4050054006012100c244131600409907440900742c603c1035004400f403020840050009a00611090000c5081c0340034400151610580040000f5403405425010204807804541400703116044070000d4180a4000c0c05141040d19000c803400008814031300e90702400c030491842d0384180030702203a213040319102c0b2500e141e4256020080a4402031900d810a44400002500001c0c000c0e0844801496134040440e151403400407070795000380c805441454cc50200f00030038022551524292074001e90142c030009549010303144150303054455900201c146003081e00120f941545180c000b54880d00055440300c11044040518643c0d20f4074110040100640900000041d2031400fa0401da1060003850a440f03555140070f25550616000c50070300c80900d803129601305105a003400340319003141c40100c00300524503100316940c0d46d00750a1403c80381000740701623006041d0342c0d1741c102001215801180344003950621240c0f0030241e6001c241e085025508100014440398000700c2550702c902 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 833869199 1250 833867949 833867971
    0x1412130501050f0c070e04031407021507021801080c1807050307050c0c0907080a0e060f06190801020d0905100b090c0d1e0209152a030c190614 63
    0x60030200103684075080398450f60503804090041100801c001c21aa40c010940000d82c1d0980c1e0500e410001e2001c07408840e01035071107104201c0c2500503110003001080c03405504840a445056034400103042148003120814800038040010965110104c0e2802210710102c82c0300020fa0003000e2440ca82d00d1003103d1400100d0010700000d04128010b04c0244480803070350041c0d0f242018400001a10780c482a03030002d00054058080200401d403601c80ca4101100050080070789180420b42004c55007801040a40220b0358410300c2050035500c42d80183c0a451444025501c51041c04001c0005000c400b4003610248100301344d40040c02d542d8031800083c1c1e40003038018071070f90f5150407083d1041d610a0300070040c0a582d4101c1000c01c00030720382d90180c4e5103500441c0980d480125a04101c400c200c01c40070408944e8042001e0074404503070702d07900c55880c1042000f0260014840d04110f085018084107402c01e07006010101c03034124000a01d500c0700c20b110f41420410110490344032110b040c0100c9400c0004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 833870449 1250 833869199 833869237
    0x1f09050c01080c190201060611011401091d07080303071e0507030c0804080a140d0306080604060c211b050901020a030806040609020c0a02030f0309031c0e0406031412 73
    0x194428030030260300c8440301d00d65078582a00345402d407048401c0b40c130701680107075502d1314140721b5241d0054010007220a004000d100c0184d1516505540c603034188a00c10709980c0d18494160b514020f00342c0c00b1003948800b82620700081d900c603072040e203a500854070180003c01401d2506101c01c2e040c1d1101e0840c400d01d940e4142804a50395040c0c0342104414005e9403462002c0c44001074541c010400b0780309951044030005000840702680518100407942e06000707050426109116241c00012043d41c09030304081c0101b10000380340d009444034484038440301c8240345100704001084089401c100607110050040c40c4030a0345014007140c2d640201101d060050b00230641c0c00e030100b8403407040180c00c58002440041c0c25580c4000100c00c9a121306481c0c105604094100e406618007844004444040c0720702035890600c5101c00251254601d0024400100c0c4503600600720521030800c1426258010700300b000459102e00b00001a580c01c0180f520312407142240040c084211407066401d4201003103224003038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 833871699 1250 833870449 833870473
    0x21c0203130627140307060305060d11060705032b0902010c02281401080f040f150902090703020315031515150d060f0603020c150402030c0d03021f0905 67
    0xc003001d2200420035035a65640b02c8861000499a039030004c0294800302014040a2801d00d03040c14110f81c0003805052505003080001d448030468070784401d40c4120451903030f011600010f46540140c40c40900544804500400103802c05922094550004014002c03441c5128000b5416241354460081c000780d0488542c0340103080480b40140c00d0302c6940c1050708480030702c100d03250f4003140030792018001805841010243d075800900c41600a01c00b20340c0e50304189080d403206030310510240030080c50014001da458034a0f03121580701800459005103011418140140010080d4100f590a08a8030030040c02c0946036290008408801c0e8140151242c15940e9449101000d0040c010f1b0483e0807400f4640b03810b2a0303498030707c010001c1d44120312000132000e08100625050910ba60400c4084c10b10400c01e9109d01100041e81003084200e0721505c001c265a14400b00781040413602c8020b4004034425020004c050300400c0f04202148084800c50451f9529030400003907036201c0c1000b501c01c0c1c12400d10380386 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 833872949 1250 833871699 833871707
    0x507090909020f180703111e0708040e010b0702040608010509060610090b03090d0305091b10030605120607080702010c0504122402031027091110021c02031306 70
    0x50308a0000f843d200021401d000402c96182d09003410038040c04000c2e00b0004282e070907100741031a8041004c82e0a041c0b0007104c9101080c5001d110004401c02e02c04603485007000021700c00c071000380c00841c441c404156074850964085e0b4202c40c004900c268148600482c58030414172540e072046005800070802a11036606010803806c9080d80c00c0c0410039020350100792418584002c5001c0caa003800182001040e0101c01811241c01902240d955080b260a040e1403070260f1060b00f00e0000101c80540035140b90280c180c009040543c4000d4000c80804c50070740240d800440d130180700d21400c2d2aa10450340d40d00c6030032801c0780c006c0d1400780003042050205114100344404100c540910a00c04400940b81c901d40c100c401c01076841c03046841a80001c2002405070b41400d0381c0c4010104011400680c0c0c06d0418080c049025607483c903015280d85d0074484080c8001c5204d6074058603000b80003905008500c0340e009407211201c90902108580743d10303c020813284004211035207100c000f900f013140e40b420304000f00d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 833874199 1250 833872949 833872961
    0xd0b030c3c030f241e0a060e012601360609051b0901030b07030e070911091c0c0315092112061505070516090209010801080105070909 59
    0x801c0550840c4032800311038400b04958804001c101e0020403c4a0b0303400c0c4407850380c40f40c81c018000245400c07028030075a148814140038081d261301c0314405c166513956144c0310060826621000000001c80000289406c1002c11019180d0030402200b450241c1c2030300443c2610090301c1111b504160811035441603900a0b60007a4070746d070028100e0b64038040395403240380070703507083c51016500d40c2c00902d8440440340c3c1f40c4182201e48802680d00b452603614544801c03c44000c001d01080078151074943d0a0071065050020b81d0142600d00400c000700c1242d0841403080781c0101020380c3c0959102a08a000c40f0814009034241c0e90340a80402c000c2070544e9a030f480c0032800c07264145036550f10b558004002a25050015000008403001144200003480340140b17410000c0c40301c90a400d00c3c100741030021356040281d001e051481414001d03034441451900903c3c20801c2211a940500c0200c2c000c0741c050810380080020358026656030701e80c1d0b602c4109c000d08983c000e82d40c0c200480d0310580c0030009841030350440707 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 833875449 1250 833874199 833874289
    0x115030f090c031a0f0112380901060e150103020705150c0a0801140d1403120405030a08061c0b070509040c080f0a0b0d080c070b0d0b030c 61
    0x12806685903500d595a4030001d03041294000d02d03e50103070004800d04d82c3d105500007500e401c409540d5142c221b800100c0f104051003d40150009612401a140c940c140d562103034401e0110224040048114842c1541050f101e2030210f500304680040d40444441c1003078001c0070344440c007494601034840154001d40c01190f0440e500d004050403011b10084950780c0c148144040305a80e980c900f031045009010381b41c140c0020448041903c420031640d140e0301d0909260383d6014641e051358443c52000d051842c0280b518005003c400340342080f041203400300192520b8800c9480710101910360404010388030011190407041015010510404a2001d0100b5600103810f410300a1034410030102150070748210680203808107400c801448440d00780b544003554098148042006801c6140002501184841030b01414035580410782060222041c000070004103c03252001f5500c0140b10354440c05003040700325251280c081c443c601721460600180643d03044400040d920b80440d440081070800303107801c3c412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 833876699 1250 833875449 833875451
    0x3021c05011515090b030c0304060b120a050a0203070605030118020a050403060e0a0302160503030d022a0a0c09141f05040e0a2306010e09010e1902180115030f 70
    0x54984800d0b1031140014155075000c211044158076070103005101294400002c0030400c00400529052002c00c0d02e400c00d50041001c0399107109074001441002891444441ca4000c0d40d030040104000040e000c08124400c0e0142d41c0d42c20b98661094403980000d00c210002001d125014645c40103241e0300030840c400b41d5003400c50401da129241c2408460030300008021991001d0510400e040c0c042064500120010340e00350b0700d032420000803035143c0c06114807a0300a2500480d00003009021001c80041a42c2e02031080349200280d140340c55034440f034460007924002141c0e003010034600128001c01d030085d031004030f810240c0e8441701c01c518014141d00100703400720749028102103420b6580d401a5101a84540b0003044100414102502000400c0040d003600e0340e1100003101046101107060360442e81d00c00000841e40d603403003041a01500c210041c00f0f0b040c1c0580340600080c0487c611103500c07114000c2c0d0350381c090b14503087c0e50b000c48418280510242403584000c140b6400d40700b0b400600004d140310300c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 833877949 1250 833876699 833876711
    0x606050d0816061104090207050f06090c010f2601180c050301051c06140115020a170a110a0b0106080a0c140c0111120405010c0c03050f090604050607050c091003021c0501 75
    0x462139103504107130040180c0c4e540001e180000d1100411000d15038403007600140c0070351704041c200726650740c0da042111414407580c0142c440303820307002d00c6040384c490204052504031b045486401060440c801d01441803c800d844541075016003240c46042241c0915848040c6180d082904200b400c54007044846034040224080da00010310074051203050158021844000d0350500740310f0b16440c03000c0842c3c0c000f15405194004003190745d04038034840b000881107465039034000002045412260700408000036104014180c2d0401202d20b00301412a600c981e50500c00780c54031300d071080566404074142e10000da5104440d440381100c03140200ba8840495000150b4070141a9403925030342c000c003182520843e402030420041c41401c1c01400b014406a2500e00c89410050360054443e0142c2507d00c000100301150340303c80354443c513080301c1c00380c04000c1046466118501d402c640c1c8000e0403000745d000f620b05601003081c0e0103908007240700790b90380142100b22080c18140b101c9140040104203072655900c80d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 833879199 1250 833877949 833877971
    0x8131a040602071b0303020d02030f030414030f040b040302010e01030e150601021905010b10080f1503035d1f060c210905011b0b0a06030606050d081606 67
    0x90031580d080c80b81341c0030401515504000e8104054034408000350340041000c4c0c40c000644600301c1e944158051002d0481c1c03010318141c640b860107092556010190002030201341c4000150142049034400d03030760608602c84000044040e0707480066054850307401850949401e0204220b503991012041c8111050440114221903400d500d0301c100307490a1b59240004009814000350003d591400c0c0d01300f1640c1420509800291005c0080c684170a010041407094403696040c0300300c6420610031008d108507200140d0800d8080c0200a541000b4150140c1200c9108100021421145140419031a041d60940c400b000da20520080620074501d184002c80b1000641c2c0d0b0344042c01a180340da44034004800d662a1064042d5815403a1070f002045980380f500140d540074002c2d03001d80d002807900758403003400c00040032030041c00113038002c003444840300802100c0a210b03404041200e0060106024140c0e845003030100c071620110010700140350800c2025124100d03003202c44e120302d00c14200000c0601101c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 833880449 1250 833879199 833879213
    0xf030902061305010201050906040506010e070207050d060b0f1801140a0e04050d020d05030f070f03020d110c07050108010503030318030d02071a16081b0c01050a020a08131a04060207 80
    0x20820741c1c4102c0e20381d003082c00103517030920610b9801000d0000038041e604081e251180d490005100c1d01640c0d01c20071000030f80d43c130320078480c40004103c00340421000f0b06007032529101a021200d00240600f0791a030b161500c62901c5550b01c06031811800000030103034280700d03c5104800700140025001011020b001070055006461303103225038040d001400d20400401d86c02800c1c94102984c0004006090090041d00d144c4040321303d800040508109036503090400c0181c019000c1c103a86142c49901e01034030114250f80d407000925840340c1500c20b07522010380702d500540e50405e080c0191130b01503005000040744c404083c0020885c015088045074106400c00c000c81080c0d9001900032221218050f80301c482c2070300000c07130b2560031a201007460205c84030502d078000c02c0c040b801007034210302c8000030714024004a182c000710741d500d1942600071300c218a4035208800c00380d0300041200b00001c042500203403060480356450310095500a44110301e214107402e020714030310700c00b034029241507a081103d840003541c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 833881699 1250 833880449 833880457
    0x3140909390306010e06070803011809050f0604140a051b01020a020307140f0402040302010e01270f0e0709180c02100627050603300304050a05010b0f060a0f03090206 73
    0x1100302d66034a80040010f0101c0701400c6818043c2505100d01e200013403000c02a241544e800d01000b0006171460300e0790b540500306001d00030b4003034020307480130012030b0344040ba141d88158059200400070086280d089951100140b101a2141d081107814100c4070a1454005400350300501c112600307600180c001030b0800b483c0c0d501039084581c402144e030701c01d802c4c40080e00310000000c80b802c6082900e107800107024415240c14050401094a00c00882c11075440c60f040111500501c448460a0b120340f0100a505001c1c001c5034403c410400000354458855000102074464140404640c41c0604040c0b0002e0500c040d041010350040c8030300c2100000c0c072446000b0040000c54601c000310fa031a61842109881c40d4043e02010600389070070000c81d610002139405050f00d41580d88121402a04003024004c40c0e09100e2440c0c00b0400018030092140020b1041d0b40c140c00788008204240e95041005408402005420740103c0203025148400f409244485420000e9003404070b8038400a50003c0c1050380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 833882949 1250 833881699 833881801
    0x2004091d1c030b010306121e08210604180209091002161103010b060f090d080d1409061e0c0c010c0306090e03030121210302040303140909 61
    0x20307032110070080c2264180030b000d40f00d590a0074108080b41c1401d8645886da040c0a8002e041901c1040c15503140c001c5d0103101d42d07800d54100c10b040e038807603580c0642c90300f00300d4552006103a0400c40c500440d2051900348110604140260f035919110070b016802c0c800c404400408100c044d0040c280c540c1c9140d034490004101e5141040c1c9040c1c400a00c9140c41d666802d40610107034040e0385010481c0403180c8900040b1071103564400400d58645400c440000c407040700180700280a0382c4003003450040d41c11180c12403e581c3c2c206842c07140d115540c1001d01955250101e40812a41081c1091002c0e003070032169066400c6290910700c0c86c074040d2822006400c0d40c000307586400000e565001d00300414412031250190940601c1b019515651500c030805d030490f03100c45501c01800140d45660000c1061110407607000d181408030001c0704044448003e4000e401c54030042e030201e4090318882410240000c01c03548162401810030480d91586015981041d6001c402802c00003007444070000481c10403181107040324 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 833884199 1250 833882949 833882983
    0x623033d0e0c07150b0405010b0304211b0f031101020903030913090210030f0c081e1f030516090c020307030c030201020f1207032004091d 61
    0x104a03211129054011a03a0030340580100c40e810a205084080345800321810112070300101d4550007840c49076032050740c1c1d00802501c40c80480f580704c0344040e04803c61700e00080310104500e07a42d0301c048440d83d2108881c000c10401c249050303a024881400010a501c4246282c179030503410001c1c040c13070741405000d501515505c4408030b04508050780110100071051a01c0700a500300f00815000c40d07524080e99000511030081000c542d41800f6aa070f020411040c4c0040a0001d6420702d0b80c0c01030004d05180a29227129403c0070314080c81140203081050007040303120070440180706070315401250a4005840d500103003108001c00708015042e016514082c5026002034448201304100900354034586130302144403030303083c00c1402404d950044140e50410ba003500f446100d6071503919040340244240c2a0400d0741200201c0c4580001c4030b0b50341c046100c1d1815807400c001440503250344c003140001c000000411068100418021940160086100e80740d01c510b005003000c01120300c25007800c0122801d00b03010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 833885449 1250 833884199 833884231
    0x60b070203010b1c020d0512040608011d1b0c07092306030106030c030821010f080f01140a090510020703030e1b010c06050c07050a031e1404062303 65
    0x3618003803140a50600e000c84003401c01c0e00d401410003071410012140a403141c01c1c05040c52090040510501c54900d504000990340c0301c0d102c00001c0c00000d400e0042c0102402c10040c02d0308000354101f0424007071407100040450f0711101400d101551303070108050181c5800f40e10000100c801160040b802601c2140d444180b04003082001c0105c50f02c1e0080109210781e040603400c0020800c2107940400341d0390007900ca285d454082c1c00041880755110754030103070494140e03800020070144100511098030001c805072a120908911907900782c400c1c2400010901600101150b10080c05510862805200e00140d40c8000c041e9510302040743c11501d000d83c04680c40d01c58540d10500240545c0791940c2c400c2240c0c0404143c081e00080150407207001c02850140d0743c00200314801003400a032005141d20000300c0d60710500c9031600034086041500c010701d1003004140c060241074041c0e4140e00214202460780f0f814140b074824122515194240d1000550783c07429003408407040c00600851190030041c0307002440e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 833886699 1250 833885449 833885453
    0x90a03120b0d020a0e152e0c05070605042303071401090506131703040806191413030201060b0a0203070f020a030f0c23090402100e0d110406050f010f0c0312060b07 72
    0x76048146e07007407803160814104140c0082c611313850014201c4002288002040342c1d42c14241c3e50b201d0030901c040c00d60300c03a41000045182d17004000f801030f9503c00c004c140000400302c811049900e582003a85070706400c2001c040c424000303407040120514905142100c41d90303a8a901040880d80070b6200444100882001803000007481e42159080a906400940c070340380c500301c400d03521a24064000e441d01004403260400c401c50a8100956214508a42002c0b50402c09602c0103c2044008224055404c0c000c0002e15000d400e000c1d01c0b881d03071b400e03000fa500c0d000b2141c0d188030741c0782111082280e220081180103c0400c0710003041181031072250468801c82410050700284100704040e86654044010307141c000c8580b11004160342166060710078885c0103044d0360007660391801c0807d8140e003200c0446010030a111040e00702c2e510640c4103032002c0000540311400c3c4824071001d0f4140314007040800e11504c030340c20701c100d02c1503040901928002244200421035242a21003551000480000214550003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 833887949 1250 833886699 833886721
    0x92a010e132c0703020d03030e100e0a050d08011a0c0708010203180f07030c141206070309021c030c15090210053001050105160606120506090a03120b0d020a0e 70
    0x540c0040c40001000407074030759170006101d0001e01a0050805844e800c4600c491182004100c480c0c03405074109118150072200c1d207655980a500b0140d03000d2043e6a1794004860150b010107041c0d50707500c40c15000c188188421603c0c10b0788414802c0d011031040ca1000510b0388400e201842c013a03404041c194102c400320224aa01e0081c059002030341c42e801c40740b0100001507030b503010801101d510004555680b11213100140031010301d014403010a00a4100f008442907150b800311107524822200405003041d0311088600d0303404810390040224040554043c081101d1040c180303600c10301d0200118140b245035003c910817845002c902000325101103000040d550302c06040c800041c40c0b0b512280884803034900e0481c0455010700c900b0b414800000381c056100c0500901d078081e1705804c040c0600489a6559000103608503040b0705070b5403402240046441c4180c049005080940c159440d08240143d41c80341030010080303440c1c803a9108a02503180c1c030042c0c4034040c08074010001c0752041440361070b086840d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 833889199 1250 833887949 833888021
    0x5040f061701060203040602330a050603010606172a0a050307030b0306060a0512030904140709120308010302041e1401051c020102030711041e05092a010e13 69
    0xc002d5400511082c040203600080007100340b8011141c05422200c03001c500220809c3d000032221440d5044010052854456044940122002e070020024550384050413a80c8006000380301605044034000314098040c2604420b8511008002c02243d0001d0020428103650000c0c1010001c2034010080001c015014400c03003203258829000b0300904e00e00b100c001403944200d8018148215085240400000303000c1059604805c1c000c0e00c00c0000c08100d4402e114151011100c400014820354000b050310b5045000f01805643d15496984080e400d41e401c0001030300e445600341003200c450103c0ca502000b59800748440b01e0351101c600c203203c3c0d4106420301c404041444400c21038a5542d00b10000143d900208469040d074104942010f0584c1a400240141800d10b0340c0828141200040e20f40101180d0f000a0162580404540c100c20501802002d1805500421482803034829250145940610300c00e008030f410060000d00c001d001c060040c021105840e404502c55003800718071030360300d1803101c00301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 833890449 1250 833889199 833889209
    0xa080402090a0b060a0305180708011a0613170a080a050304063b0f0d02060108010c03051009090510150509060a1a0f253c0305040f061701 61
    0x3808840740043c00f1560303d00c135245810f820140d0b00c900291030340c0110000f65075107070a65401d4440b40d0b503840b0811806000301c0c5403d104072810311103172038070180740c02030454841c0003c1012a10030030307184c00500e003100606001701d00944d000d000d00c4280040c1d04103000388105440c0303031512a200d04044c10708608a41e07055403000b114402515500a030542460503003600045000c108000074a81440b00700d09010351074590700d003a0301c52240fa6620300c030707008214581aa44100020064500354490440c1511410354540480101806040c000d000107508020021405503040300c20600901c0f560004032078900d45204000c0c426036000348039610300b81c0d4040c1d800c02070840350031240a051041010b03182040c00f00352400e40000081c070601c000c00e040c0688403c070440c0d0208125010725041e100700c2c0d040d1141e004503180c1d15070b030b48080340c2d0741d01e03c00c01070711140850801104034800303030008a480106a0182a0141b100c00d010005420034480c084c50094030440c0d9500d5644101e10729880c11303861041e001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 833891699 1250 833890449 833890451
    0x904051e1308030a1d0a08190201061d040305070b0f15040b0303121305070603270f12030f050a020a020c0a06021b150c0a02030f1b21030a080402090a 66
    0x8424081036544043ea5000b41071382c01e00051440c040c28450390b8400c0280203072101405010380e95011301080101030000d140b02003403102c962180e000d034200d0072646039004503912100948091a10002d418001c158400e01ca070420754981100e5480b2614810421580040206400070402c181141401d100203104c050680d401d012002170840000c0d243c5c019028243c01d00e8031200005220055010a031442d060b4104040e212100d0301c0c1ca2004018200f03d800619030401c0c0c5040d182c3d083d80034031400c518480c3d004800141c51940543c0c8411908403c1d1020004054440d030750303040200d481d8811f0304d0280c0c001090040c0d1300c201498020b41400d0003103d0843c4651200f403030400406801040307132003000d20704420204000c211080001c0c1111081c030010802070740702080701e45407880300040c0d404042d802181100c8405d1440c00c10940d8034800c158401c3c0e1070b004d86407814841c3c0d0400c546900071504480000011180440c540c09185400c0150a50009002d40b0280030950030004810303504080b003460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 833892949 1250 833891699 833891731
    0x1608010b040c121104051005030f010b03160f20150c0c06040609080d140615030c1608040314070905010503011a09090a0c1217120106050705030904051e 67
    0x4001e084000740516000215841e140440012804007041358086c0134014403541a40e0703c58007006010b50800c80300c85014140140c004100c0800480030350303124a00e031615481d80c040c0340c0101101d0941000c590503003800190f5102050100c40c10303064860300024a0000c11116100c407150817504d0b03801428100802c14100400150780f4004603806a0254106001044c0d0000f5850078211a11985607801c403554648030500c8074608980e201c1c58040c010442d4600c5555035085458950752006aaa00c005a0820002c03120030101e07000000850501540e5607a05060303582d295404074090912506042d9007014505000340183c81c82018090700007500200418055aa602004052215405c5120342d03000400541040c03020001402e10b83c1c0c0c400070707581c605540c8801c8901844c98503103040714940904040d030344c04143c010301910f40c0c00c041010341100070303464000241e403164404102aa894001000360400e40c1d00c0d40d000c6e06009504280e225920002c481d600d0b0445907101a1294071301e416410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 833894199 1250 833892949 833892971
    0x1f0c050c0415051002070506120f060f3007080303160914040228020714062505030d1a0a050414010b0313020a1502070e01060c0807060b031608010b04 66
    0x2d0340801d4a0040e502c00c0d50f8a840a00203030315215161740041d42c84140080c1d880d9a41072207140240c0102c42c060010b18417911402c04004280e9000c000540e002102903500e003404120b245482c03100070006035190302241d0840d01c00ca03030804400750810324407540000b060164101103038050019001e0f80f40ba01042082c00d100380c5101388001482c0e82c6100703d4000c2002442d00b9042ca082502011001c1410400043c41580c06074550a0a12a644040174060a140454100321040310b04c0986140e503801c880101500915107403680c101010b880c1440180b0600385c00f80024810006241408170b0f2402c0f520f04280b042100304011a0080ca0041d800d0036449005902c1708111a81540e811460b41501d0b99101d00110200910640020307600c03c00704800051030b81c80c840040b0360900495400c4e6550301d82c40c1c9440c2c80304068284102d200240f401d20743e000114010748050003030b65120b4071000c2544005180060710701340ba00910881c00c810414420405004244103664282c032040e103060051103025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 833895449 1250 833894199 833894231
    0x2030c0d09050a110d0b150402190f080c0c03030105061e0301030605060a12050613020f0a1404050a0507021f0204030f110a081209011b0c0b031009020412060b1f0c050c04 75
    0x192403064101c041030728071002503031550180d0741425071410407095012b0b03003a18010324025026a00c4c2000c1030084020640310542d0408450b400f01a60780114a1a441d11041c00000d501000c1300b000703001d000520f006101d003071000095000314002e0201141038104801001000d0300b80e0b901070b8891440034030b5960300160700880c0e4194803011210048260b41da660000c55840310059039003c2e48000c42020105a1504104080c200a00151800c1010b907480b010410b0480310250307a44000350f13105c014159002d401c24420400e45400328a809424156650b54200101391100804c0701d2030100300c20071680740d06040c900d820003040400c000b0060b034001382040b482244504003407079040004c45590207081c0305c41900c1030180c0e1a4031828480d041ca50f900010750300c540064480300309140d0041000160130a46000781c1d416203030800c401c00544521603032000000c1c8010b04149400c203064048100350b01c00025084100d40d04543c960308003210451130700c80d08040388000d42e80c0c07055151108500c09000d003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 833896699 1250 833895449 833895451
    0x1801080f0c04051623211501050f03070c0b0103080a030c02070f0b0d0608060a0b1207080c0603060d0b0403081005091504150909030203040302010e01031404020402030c0d09050a110d0b 81
    0x5038241108008103d03601c006410071260169803d0b82000640d0407000c0060b900d070501e0030411064491070540b80c41d41f580c6c05201680c0c051600081e001d0040044c2410800700842d0030400504041d200e0301d400340c0e5240318600e409d901c144d62010022030301c2d02140d900350003081c030704c03202e0340c40646441801c0c58201e203d504d01c54010020929404103404403503035070f1b44e80410040d1186c80c0845101d8a40381d401040540441304800f801015991300030740c21004005441c2080c0c031480005070401c1120302082c41125000140001d034044d035042412400b1584140d04180650300a58888107a8030b46034081d030704140800d511980c080e800c05002c02c0520700c0c100901c085601c00446002c2040d000700b10b01d5071560030440d005403500d07074074215821003090b030000000d0084038400c2c2c8817001d1101038040154112007080100311100104040050010300e4294011070703000400c5500d1605041c5050f951004650041808407010f0380005071002c24046103035000700c040c074011241429054a16540c0201c5008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 833897949 1250 833896699 833896741
    0xe0603070b0d091416050306091009110607031d1e090405150c04091401060c02040e10061719030c060504030c1208040314090d080304021801080f0c0405 67
    0xd0114a200010015822026207503800039a03403002c0c0c0c1c0883d072410780c684080d0820100340741510040001e4504020840c184900c060744043c1010040004506025188403180cc0301c01c606841c4114055070b41703800180032218042d43d610300d90400d9003682e2001e4484e01d00050340c483e4603440c9480c12402c043c00c036900f10454040c0c6000b5055210303481d0151805141041080e0780544030f004022050104601030001c403030600400744841c0854103030912640c1003c0c007a80c4005100c4440050240c05c243d005030000c40c111740c1c00c0b01d2000f0380d1490408122030310b54000000c1130301540018182c4800801140b0100041c50000002030281070303402400102841c0d40007042140c0b19800501814061100b0168490b080020a8403028141100a000d210100c1e02140819035a24040500b0311303040c419650480000713040c4c1d14450300c050300c1e6540e45400040c02241c0c490401e01096000e0303c0c1c1800f0309802001444010008e85904414071400d0144a40c1900d015a00d40303c108610541c80c1007407107005503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 833899199 1250 833897949 833897969
    0x1050f0a270e15010912350403020a0f08150c1201090c020d0207060e061e0a2d141606091211060f040b19060e0f010e060307 55
    0xa00e1189442803845000d480c0500d0007441c0c1400000c0d11120010010320409068041c11081191a8015100b03101c0c82d0040981c100015140310300042c40208091140422050541c201041d81c281c0d9145000c0100c00c0c607484211010600308218104540703080041c2c510170082d607840500302001155155520300030461400703503603000305458410460445003014000845e8156540c5c455a604010b049510415001480b8800080f4203c4e840810400c0a40b000b03652805000c240717003800c00c116a02300d01e04181d041104e01440040d4400b145004014000d41500c800000c0c080603080c1c2c1040060854008161403000441d048207160304c28118540500c11607a000c4d10f48400c652600072501e1091030003810545084808003d11a044519404005655547c0704943d501c0280d040e480d04001d444c0b0945510061002c03034001204180202d62208500c11050301034281e0300d450400341c480d15840003140d0b0001e0400e000c1400034900c0c2c500d0261000d5080c0f0361540c00d040c000b10350340b5000d070707c42c0020907 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 833900449 1250 833899199 833899217
    0x60908120306040908040b0703021e011b1103250506011a03011203090302030a1104200706020d0b0a030605150a08100b0f041a040e0c01050430080a08010501050f0a 72
    0x1084001c282c40140c900080556100c8008e40350181d95081c050404881d0304070005c61050166005001d000030501003091005804860002d095480d044010100803103408140b0149050001002e050303014210241c044884808240c05d21ba4141401170f00b000c4000f80342c403407081c80034001507000c07681107401c07100c448510002d09090071588035245410086d407601a50000f04140f109400713096401d04000c4a0810112103941512003240002c698240d511b003005200300d40205025901411302040f1400010484102e03c0d000180111a035800031100c9940c4c80c010b000f90f548402581401e102c400740d4004c01440d05091000796034900303401006410030b0701c84a0700c406607101c005800c144020091710500c540c405444000c0c00040200d5001401185000c0c0b00303480c908000140300d0304114041e1566882c180c20180e4802d50b90001841c484001d554200c4c000b12745801442e00c01090600500c8401e88407a5240c500804c0c80740c060b030216042180c140300079020ba80c4840304a4038181340c5420f06800c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 833901699 1250 833900449 833900453
    0xd0f0b280e0c09010207140a050d06020403050f0607020709050f180c0618040509030412020613080318090f191d07090509060109110a0e03030904090c0609081203060409 74
    0x2121498000301d08050900c8244041e541e0a1030181c06140426020340e465940c07107920f100341094000803202e1703002e00c0d0148100b2140c1820300e189900a0b014110141c50141c6a0b1141481c0600380e4148144590201c41000b0761030b0fa060103400d019082241081c420707400e2a111a8013018009084031840444034506001004c208110010380d03850090032036500d590314280c0701d107007640c6601ca089005500b0720300000d02c505c501004413400d0300c0314074a00845036012602401714607000040300c0c41c091b89105101207003000e810409404141c54450041003a0800304c41400802c04000d015001400036800c284010040c880603864908800304000013111040f490501c050362900b1248007149000d0a0804218003400d034022034801e0302c40104844130341e6600d400800407500400843c40c4c8200c8240110740703d0500c102184842241d00408690800040c4000102240e40c0018100c4060702c03454410050301e0380001062005015000c0a45000b80f4000c4800c503880c400100228840c40c0c1c3c407844103003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 833902949 1250 833901699 833901769
    0x150910120207061103162316060f0207061d3706060306050c0414040b151b0c100504090903020f060a140610021011160303020d0f0b 58
    0x45043e001401401602041ca1911209034001c0d0384000740581307003c10041b20755000310f17408081d41d00c4800c441c08201c0040403120b0341030303040100781e0b030309103160450b8007408105680624104080c07107450050781c2d2502c924150084600d1981c060740d4010000100c025001c03004070b1103452246c03842c14041c03074048002d0014281890401c0c00701e0010044d11200750140082540f001c41540d10514040041d0b4039840700d10004d40c01140b142a40310039110300072501500f000d40014001050140c030100d205a840300d181c4000b50030140849003c9161070362603200000c81000740c01d0714510280c1d8074582503045035400801e02d10880c0600c440c01d03501d400525003014802c003c00e41e070920b417030420760300d0320300f0403008040207000c0407011200810803540201b1022314000344444014507494000f02240345d2240c0e1440c01910707004072a9191207909000c0c80039094040340c040c0090f140720340e40059850040754200c0c002ca840a202610707040f440c0018054640c0c403550030b4280c0700803484c50125065242100703900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 833904199 1250 833902949 833902957
    0x30308061509040f0203040203010501140a0b07060b040c0c0b0f0601140c0a020d0b0906090c2d13091a04051504080910031a01020a0510020c12040e061509101202 71
    0x1d80081c6410344407071303c0d042c0c19406140254421002480f150b41c2c4c030090504511501f580455204019041c05c211409244009040c1c3c184a11004070706054114001012160700d440584081440d04054408002d081d46159502103090701240d64541070420008090500c05201c40d0954503001404510f400400c20001d00300c19401080000d901c40f031490403210100090b50903003410710035a00450740f08040481c0d5440644409410f1140e0700001c41c8004001c618102d030341c150411401c4000440c25111640c114107808402840840e0580b090b00e400110b61800b182d50382c0c8101c03006014000010760105485140e2200c142c1c2e04400da445900f000e021500c42c500486a02c110041e0042c030342150160460841850980d154140003600d11005a0301c0d83d851100040803a0050351601c540a402c5601405174189500d00310741e401e03101480320340091307403050700500012201d10b0304000c10303443c0c003084002d000c414040301281014461004103541000d1006000b041c04984209000844000c1d8156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 833905449 1250 833904199 833904217
    0x810020f0d02210a020c0a11040e1e100506150f0d0911130506030d0305130506241509040f0f050411040e010e1f02041d011e0303080615 60
    0xc660b12507a4100c484400b010003d00b89452288520008081203520b01c2a10310400003840541618003a075555100b50100d825041580a07546040d40c10800714104103070401c5030031545901c030030001c101c0304191414000111000c0418102000c002c01a101c00304c1207024407214490107500e17402c4000c5034100c1806000741c0c50b5121071421080da4140240c6101d04400a00c00791184904e43c40380c0c140f00c500b503403021140c03507406078031040c403a4401b24441e82c041d5610602c07100100000d03000d030340c1c0c6142c10002c058034809076000113154560303200c01e00660f8201510307200300c540e01c52400b81d41e40e4558042c004c881c84144910340d00c8400750040403140c3c01940c4100c01c011010401381c6024505403111081e02d0702114000c525140b100300c1600c005100d40c6070104452001000980140c6115582c01241140d1103401c503a0240000140d5400090422005100100100110758101012858009007102c2039140b036505180007080440c1d006100680c0001091314003040e1000700080520952040c40d543c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 833906699 1250 833905449 833905451
    0x7270b09040c05151224040f0608071e090507020c0406030605040b10050609040b03150f010602191104181b18051005120c18060310060810020f0d 64
    0x104010051841841d01c255201141c50451444d410400750000b80180000008542c041c000440c000f640490403181c0c41542a5003a0044080c22002250036280e240d80c130411903a0316400148009141803000380d025291500104680303013013000c1c080001311003034840c2c0c000e402e80d03031000301c0c004038404d000c40901118094028080c0380c0c0e0324500003004000032503042da05201500301044038000d111a00704102d075801400750b8140404002000010661001455031603c1500c48150320000303503002c22413180b00d245264040ca0340c50322001078205540e4909545001010001d810f001480d400c1d000041030340c040d180011b9000041c0c3c10071030031400d0800058012140301810b015001d800401079000d0300c0c18200c5011100400c15035410565005450050003403070300140a02031820302c00165040d1240440403509034143c50008904250b2007007259032a214040710410001d400d08200004204207504c2d000c0200600e00000705488140704100d4014030f030740005120850705c2801c400c2d520118005c84e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 833907949 1250 833906699 833906701
    0x2a240307051b120a021504120e040204091103070807050918060303090a0f1a04180c051b0a02040e15060909160b190801030f060f0f050f150307270b09 66
    0x3e07549890b03070840c850341c00061040c64280d00849001101640c015540940f0304141c510f56903000b5111600d070f080d40c00e0b81143c2d0070300c40011090700c0c03401000030245049000d0307a62030402400092074808024100030511104020258444d15490381900d20703040c5901f56400e95844010019003184103602c035096228106504c0070031503c00c8129040e00f125002108100c201206a1152010380201e01ca40d104049032409405032a03842904548418556480c04c1c4d441d00e0655402e4000d0740e08140c8602c0340d2648589003940440c10a8072a8840014085000b0303c217601d20303003202206086004200d00d004232025004904484410000d00400758101c11aa20300c107074a540d91054240c00000c1f010800042c1c9658a40c1c1c41d601039520603041c0ca4009540034040d4a80c0e4490302d01400701c400341140490b0740c0360758103609601c4c0d910400303028401e4409000940c1c1090343e41030b402201e40b808820f1094000900030410048009401d000d84070b80940c142c900100c03d03c3c010b03002000480207003074001c00224 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 833909199 1250 833907949 833907973
    0x1170403090b0307210b0405070e01091401020304050303281b140c030a030305040c090c080a021806030705090111010c1b061506080106141206040b032a240307051b 72
    0x6d00300e03584d040002e480c2000039540f070000032506c40840040c1c6c140480e0320404140810f8012030024680060103004883c5031659a01c082840e5034450032081c00d590001d81d06420000d2641c11140300030301d40170720b00400500007040c446000908589001000d10041410305600c1c00018420800f15840c0107003030704d19820bd40c2c100070780038000c2100c04071645003180c94081780e001020b110f0303041c0b144000d41e29141d030b9680b80c11a00c0c0095010105484009490144c40a0b8903550b0a004520a03c1c460340c0d6103854449010000d40414081e90300d01c071030303a4184200032207190b92007451a00072060314681c19941140a04042c40100f00006c080e6803507513074203000403c88a400600543c1210410350f01e04034500c101a6800c0ba40b4090007480404168084020540030b14090300201540392000701582c110b45100c0500d110480c0094a015040c1541524544000c0c42c040f0b01940700582c0e540d500c1c003d24000d040c50b19070035110040c00d0200b0300001207410002c2c2402c401100000d1040441159030341e820350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 833910449 1250 833909199 833909201
    0x41514130e010509090c27041104051513180212030316050403110105211501030b010e0a030f1e1a060f090103020103021b03071101170403090b030721 66
    0x60180110742100350000054034140300401030303c40d000c1540a009480300020403c004000c00c4034081d582e40038140c90015800c40c1c51f01c20b0901991081c080c07001090440000c0c0000d58500404400c0c20444009003e6240d8407041c4480b0880c00c035a1100096610714040141c00211601074082c0d0450b499850200141e03000100030f50107080e84811904440d8080c0008581910880c0802064101c2c00c07840200c2d1540104007407c0e401c111900c41322012588820700b511600012035250540b2041600311034103658040c800e0b400d28400a1a203c260b065088020401442d01d0740b10060002001c6403012040c800038005074004404103110524020800d410440c00e031000d8200c007000c6040d4040003007445440d007900c1d11074800e40301400100d103036881c40e001174000b500b1400b81229601e209000307054025100b40020080c0c1407180340c0102c200034a01d0001452900650580c218070652001400301081d044a420000c81e0070f402c545950f0381d0346502d4100d40182c503900040c0c00002c40c0d800810150265 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 833911699 1250 833910449 833910487
    0x80f03010f0f030f020d11090709030c0801091e050a140a11060c10092307090608060105090c090a1511060703050c0919150513050405040305041514 65
    0x4800004041902c0c1c0d41c0101d0b03140a0352200070020b0408118400040c181021200c1c1014011444c02281d1354031040032a088000071211a00061402c05044c010031400e40340c0c080140803008000c20000c910342c1c4c0c1d00c0740203014400c8050700c084c0c2101a00d13010040104240101158000783e0009183c0c100f0b451542e640200c6074044404d01c003804c040384158204901613442d06882c5500811111000c10000d1004200c1a5400e5912220b40422000800003035042608560800002852031070700d01031800c0200c0e03a594012070280e4001400420290f42c13540801703a0041c031920301c0c150303440a803440000d03410b001070750100040e160580f050311801900600543c41c045401401d4505640da034120403012642d00f10b9428514500034018189141850b02030400c4481c082100c0825040c1c0381c0607a43c3e040c0894005400c00a440040e01010485d035401c2c00740d0041c0300c1520140500d09103503130054964083c03401780040920040a22010b035034031034481e10290494181e0300c65601e00303000c0651030b04004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 833912949 1250 833911699 833911709
    0xe0a02120322060801080d08040b060a030204051518010e010b0a110706050306040f0b15160501092a0503100203220c051c082a1221131101030603080f0301 68
    0x404034000141b604000b140c2c03406003042694501600756074a5580e42c166600207400c464228403816170210060300e851240500a2070a0b81076501240d00c0ea1041000208004e04008000c050700f400401070000078002490554000c56402500c61002c00e008a400354905108210325100d600c1c00001d2482d0844000d41c007400c0161403c1c0b04210345c01800300141c518202c0c0c3d454000e00c0e4020103400084420b0064900602081e45440b88000680c80b881c0c00d56030281c0094071403034031078039541d88100d69034050400c01400b10030101080034070f043c000a894070902c2d203018644640000c000ba04058080720070080e44441c2c00c1d0a8400e515032800c02003104280d42c0910b83c05403094880e002c080107503000341c2065031030344040050329014210304000c4880d4207c11103000d50071701c00a1554500941032204400c2c0c0c508070102d06840301c152841e00785901c4030317810400d000040804180f08081c0070000038040001d070006504868803003140b00490044c41940d002603d421400300d050141c0b0f03091100210704840d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 833914199 1250 833912949 833912957
    0xb1005030711010911120d020d0f0512010806180a0c0b0702010c0f0302060604061406030a0c0e1c0510050114010822080c0c060a0512040507090f0b030f010e0a0212032206 75
    0x703104400c1940d400d01f604c418405039008120046441c1d00c10342030140ca4841c94603245081c008e4034503100381e04160a03000280c03a90040310400c112803074200340d00741d20040d99134001c00c1c03404c01c5902e070f941c0c0303881c0a40918102110000787c00f8055900401e091503800307070b010015580b0202203007002501c1d40340c11303503c1c9841039003400e50005061403010484d00160380700810f03c61464450040c04070084c020041ea40c8184140d0500381c000d0741e500e000e58441c0d003200c1100704188411a501d0003508169030942d200a0380b601d4034005000e120469445e80c41c0e003034028244100e403918ac400384225404164664043d0300c00c00103000d4400c020070a40603001c0c0290100c115180d500c0301d01c0800606004500741480012001d001341500318000c400d5203504140600c06568140e41c9914024041e82d11007400e01c0c242d030f40c40301c15058160a0401003c5550f40011340208401101d8920750760710b904001e1000b0b446090701c4404940d154409004071031000c10b103400c182010070980c00f00d0003400900c0b403260340045 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 833915449 1250 833914199 833914219
    0x4030807030507063204051203010f06030b03030a0c031803020913030201050a050424020c190b070e0906040911060d1b0f020a080d0b0316090f0b1005030711010911 72
    0x405e048040103c0c80200300120003100094442d00d508a1490081c829209407258203282c1c0c6807410000000c0d4080d02c22185880d081a060070030181c2a60000f6070501d0180e2b0042000c21289030b400040c05906583c50310304441c0300e00d501101c2e10700e21101c1360000b0b5404103908050181c0400d40d050350100407807282d002071243d96a906c03000401c846003110090859150502481518181143c0c501950100070b00c0050401c0f840201c0c0519000c01800c0c05810442042003030720a00070440310240e840303070340c624000d000841c080340030a8a4040c082c00d840d01440e02c509260080281b082c4e44414a40c90192445454800e007480c0303000a8102d4081808011100d10001000c0c50304c60641444001c3c0c41303030014840d101140e0f840200d01d80c024070000045c1e43d40c5580400c0143c1d0140000c0014002c404400b10794242480540421140e0300309591800d01e24100f42c0548a4407120364407803004546040203a101e40e01d05400303031504440d54400c1540f5518003051b1408018160798802d036803640558041c01d01e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 833916699 1250 833915449 833915471
    0x6050a02130b0f0f0a1e09050108010905071e30050705160b130f0b070f1107120203010b1203180f010e041104050a0f080f0106030b0a110403080703050706 68
    0xc80c4603585200140036000c0140c2c01003503801d10f0003040103800e107140c07420658000524030f001b403501044004000418008007080290f920010301c03409884011820811414100c1d8003500e8a643c051220705000d0054480151460183c038420484c0c900031f84c01206020084800c2407a041c041e205005032052030b05000c100011720820a4560300b00004015580302c10790780c0c491f441e0001e801405d80c0c01480c508801800020f84c140000980b1620580c5c2d680000e0810340780180611032a100300c0d404005081405040718017000604104541007101c0d40c0007008074078000309000d011100140e0340c12a0143c426240740300f00010081c00c4c4001840d40001c018004d03e801c01c29a0041e030815035000031044001010702d413038240c0c040d202101c080c200c0c5603c2c0a96481c0400c0083e04564407084a00c6200384081101c0c9505100d088030f85c2110b44001c20465017103036100a8400030140c8003004190f6200c0c0030905132045103003164003071600000016103070711703003494018a035620000040300d6042c108400303506 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 833917949 1250 833916699 833916719
    0xa0c05010c050a090b030402030a060c0804060617030702042c160608040b060609181006095402041e0807061b0209040c171203010b090d06050a0213 65
    0x1c0c05242c80da1a01d40d00b0f0301d0844a0700803030701b0180050380c0c98004c0480210000b43d962003040040740079a01c0d01602460b044c107104048a030303d54080d84140c00740f2841482c00c094044200c03031140da07040b2000151590400861024400c81152101c14000c190b60f0303081d031040c400240d00b00f11146c0d440000c0040c9840d14012070f41598180c400a01800180d8080740c502d00e0070901501901a02074500e5090b009950510342c03981d407040e28040c0202610110078400c007580a12941c0103441c2010028041c0812200018034041075450500403103540c104542a03140c2400801500481e03916040c00202d07041c8a0b2070708029400340c8540140034000155680c0300201d0010b203241255080c0024010307803442c10600b5030b01c03410701c0001c445400254051000050707072415030743c60150b4007031410f22020a0400e15441c00014101108030780b9a404809000300c0b80d0340501c116819151503505181c1c0ba24880740104035584c241e8803004158070305042c1000301d40c00c5241d01600f2408141c4000141042e55400617032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 833919199 1250 833917949 833917957
    0xc09020a02030d18020a230105040506030a0914030f0331110a0e0123030a0b1b0c030c060901050709030c03110d05030a0f0215060d03080403050f0a0c05010c05 70
    0x350700305012180c2c8103102d940c442040400c0c541041d502081085d800981a4034480e00300740030440b050404500c207034562a690b40310051081c280b0f18945803d18001564038000104070010b541d40340c1000c8020004070440008038080340a04982c1c44401c40555400c058204880e4602c55440d40d29420028584159140d22032004a6065074072451340fa440e410180c003026550a0303080b40c91200001103001034501401e0080c2180d203aa4070410782c0c0700440c900007a1541206ca03219a00046114010440c1c0608407038004e040f511041500140c4898282d540d4001c110360f08055010101d000804a20f0110b44c6500c0703124810001c10684d55008810758400e61540005001c0c19a091010720026003840110816030200800440300c240350303555005c1c81c40d4880d102c52000610032509881c81a9010803101c500714200100420042c58210b01180c042c0d24601c1e00501040b880501280038103018208030b85182c00b407600c80c00c0d5582510388015010108018044079190700c1c0c1100c0b0450703148104261 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 833920449 1250 833919199 833919217
    0x30c0e090703151205010209030d03020a080c09010210021204050c27061c05030c010b041815091202010608070e090601051207180f1404151806060e040c0902 69
    0x10115440e400700890080034407060007140d244188102007003102c111020b4910316440354001690383c070407000031f00d4109001000c888003410300500000241603003200e03800b9446251704d4407550320750076002c00407843e11840510300301115100090a084281061700414803031401035003100c400c220302c1d0040c01044200811408005480000d50204035503240040d19000400200341c03400303022042884520340c030940d40084039194800250b0011a14080c06040c80003081110100201c021030146105c03501621803004100c2c800c0d0741001801e11140764002c0c4204c41e08110000381711074840502a0080401d0701480c01c0a03c104140020452659911984a01081d50240869910309000e0001000a800d50f00d40c070f5000d0701d100400c0c4a02c0b1305603c000409002c40000c203e8004d01e03804c100c11603404240c002c0c02089600d00300030114032070414029403c1000c04000480d881000304c1e00e401c0b07200003d0000c00701070030403c0005640502c080000d0083d4000d17420a02c2581d92116880e04a106106d46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 833921699 1250 833920449 833920459
    0x809040b1008071d1c051002031b0903030d11031008010527070b070803163b090a02090117010e130201090b0c0a03030e0a0c0b07081207080601030c0e 66
    0x10b01c42602c141105000c00040c4441040307813034000000110031984122102e004541d2070064003082c000100030f980710f494200326085107582800a40c400251400c0c0190556000340010884800e1324108200c8111074110340c1c027081034200103000e001181c0d00988000e44002250000840d600f0f9061207803078081d40c3c4423000b0190000b031010140c18072203111070304007070140203c103800103d90509a00502540340705540481c1e5034545481407420940030703801440100310300321002a45040007101038030100b210515040b554140d495100720010009480201e8200a4680c1400342010840d0046c06405500340c90710440404a10717080207190307509101d450b040c095094042030815251030508403405006260001d83c054603140d10701c15540c40818015200e5006036412418150325126281079061840054202e80c81143c4400f405405640502d00860100241040c1000010350840c1d000d20506500d140d0107150014000d80001011241c841c0400e05180312184840e118884070004a440149 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 833922949 1250 833921699 833921701
    0x12010b06090d08040302060c0708070e090d0315050607200d170d0b0924010206010b0d020c0f0f060103031112030a0c09030b130c0f050d02011202090901030809040b1008 74
    0x2c0180480b19540c2c19683c0081c200310200150311500b0082420015001c001c003000c600e02205d10f1300c0e0000c0d6500c0707080321040640a1120004c00820001e0801e0001c1c40c001c50000c0003a01802d00d01c0140341c1c03196911440019003841082000b400b00761030001c40784030208001141405002d603c2001310001040000300d140b8548a11000d913024215407040c500d00044c24040030b00104501c0d61058a8003000b00e5101044c03c48644042d010100303843c4020f101800c2254941018240107004000042d072819401041c0c0042d021010000d0f280408480401c031074044004001680c0c0f00c0c8428003003034000800140308441c0c4688001858004580c0b600d01c00c0389141e0f039001e20301c030040a140040104202c42410004080f4003a84400f42c0191818480d0580c0d0a0390341ca030450818410394820303654101000c400b0815a03490008603c0216020300303007000107200c000e54120007846003401c00b69110140d0781c00402800b40703030b90142005203000c0d501001541d13141806c12507601c1040d0103078400901c88030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 833924199 1250 833922949 833922967
    0x3030108070527010f080606010c0809011b0204060608090f070312030c0302070b07030b030f061302061b0723041503021e0d060b180108061611100b12010b06 69
    0x3860000c0690280000d40800810f21980c0c0c003640e6500303074002e2804101003c0140042c910034880b45070058400d0819040c0b40c1840d50383c0644c9030245101c81d6061020610348407a249901c000b144a203e0b0723005004100381a00c8540103006030b4400d5840c20000e204290111001c03100000d00403080d01c4e000184105880c1565100310040c2c1f40390301001c3c00300f40d020302c042c0f8001a840a6803500440c100e803004140481450185031405610035903240c02c90340814140181e419091880312102d07501030391569940c0383d1f41c034003100d6040c010b1601c401940c89160700008440104591005d403030001101008101300d07405040005591100c00d00603141c8c03041010170001840d00d50700ca2a06840e92512049101c3d013032500180003c102c1306d1003035a85a0701c68032480510314152000d03450114940c070f1009019418220035540d1003100030b0102844620440302544c005024410703102401600e0130889904e06c0442c00d40300047c10400e8903450045031500c03c8070000540600449840500160441d41010000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 833925449 1250 833924199 833924209
    0x40503030412090819062403110102030c0d02070e070f0f0806031618110a051803150403020c120d1b02040f06121e0210050d06210b0108030301080705 66
    0x240803560034443d21076000035040da001e11120301c04e80c0810341c1c851a95125410301109403035400c00949050081419026507044035071082109a0307030041e421166002038640140d2a500c240e070f2400c8500c0c441d1100c003a0b10385070700150581c15611a002241c00984489006030303449140380d901440030031003c4000c12a181d07c603c411a51100c8010110b03031003030101740048101c2c1c0b0000d422100b20b2208510300c4121150f0107000350b40c40b0080a802952501da540d0360000c206024450051007000e0140113669000da0b010441040c04400c1000c4500781e41c103140c500a0350701c42d0440700a82c0900740c40c0a04a22400d80411440c0d0819030984a03000804000b02a4400319012020b0882c1e20903900d000c21514400c2e03c0c4500000b03024454020305151085050119030b040040c6c250a88612400e252000180c95050310024603600d20b040c42078644400001100c041d000743c5d0801790310f40c0b0341002c3d0307501403038a11429050018081e40f0400004d0340c07668012070b103d00c001d020700b2a0030351020104020350700302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833926699 1250 833925449 833925473
    0x402090402121507120e12030c0703120203072d0e010f02030705011406150405151b060c030703060f0b0405010c0312051014060a0c1b080102070602040801060e0405030304 75
    0x956080e1440040c8450308540018000d84404c00003810840c160710b8868118850407100050600003001c2d14079182d03402d56000d110003803101c0d0440b0000b046c070340c0404d4021a00380242244102d03087d9180c0c5050712000b0320b9040703060721313403000180c04080158105e441400d040500040c1c6956182409840d1001034561002040017442188410440e03840481c2d000e110b00303030f015905659001d100d401d2290400500b00d82040c00b141035000100710421003030355070082c8030360003001d00ea40d420344034503411035a00315401c1e9402c801e111070700900c820001d03c800a00300961040289407004c101c01030700c1707501d0010300491b103025007003400204020600c410342c09102c0000c01d0074828985030800d4000c00c29243e064650581c0c0200d400c5907050414010008050000f1030110310a440103810301c003501303400605445040030080d201302414602c180c81082010380701c43c05059444002d55440104c2d10700300000b540507116a00043d4a481d01c00b2030a800c00c850f0032406160404019411602d55450355184004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 833927949 1250 833926699 833926729
    0x30501090b0931050115080622030909051e1308120a15030c091a030616050c03340201020a14070513020309060703181103120310060906080402090402 66
    0x2e16490885604041c0c0d583c0d00200b0300c16030000c82c10000003460160b010010342c2010f0f415030824002c009810070075600503507545c50055001910312a4a00341a0394020355600074880780380c284010000e16084030344450102c18101c00d0794120543d101400100f200e11001c100a14594007001440703007055035400043c0d00200b28500018013601c6010103412080c005a108a440001c00c3c002081040035900c0b41240040302c020461101800c104002621000d0080c0140601032907603d50310078840c840c2007615110392000d003c507641c4087c1c1c0032129458189080b04001c031020020300c0b114a004240320740c3ca01c03080d41a002002c403244180d0310f5a4240381010103c10003485104070002c0c0680e164144c030880c850181400580e2170900b0022141480401000c0d00207150500522a010b000030051085015402a9555286c014880002810005d04c2500414441004005d000182c1c0604201904440d06a161110102d580b0001940c140780b00300c03000703540004400c0003c1c0140c02d00c5a000e0000f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 833929199 1250 833927949 833928001
    0x10060b0d0906230106020c030303040c03290c04090e0111030c0f090a091e0b010504180605061321021815030d0e040c020304080601140d081603030501090b09 69
    0x80300d122001d1600f800002c2107072521040203801040a160103011030301800c40141e0241d0300d185840c5c1c84076050b24407540b00051107100a01d0b1055200d4200d1000c0f4002c07680d00c6000421282824030b01c2116580040c0510030413640f6100090301503c00512425018888e504140d45c2196101240c070001c641142801c5580040c0420840b6419641c1c500d520024006a403030002d82080404442c0401d52840b000d8000002c0c9040c02100043c2c1c2c00070140c1d03040b500c4207404c940700c1591491010b030203030031181d212a40010010482000001c1c110440405582514801010004020030f8000a007114a90080d400c0428544e1034141c40c031401c03010719400740c220225800f140d851840400d2606401006803800110b00318299055498240290600c0c45400e200079030600e810054000e48404040c440d114a8410b107150507442906d07451403d40000c0c0e00241c81a84404008aa009402201c003004800003880d0030300224112040c0d2056071076444000d0500c142650303c003008bc030500c0118010103043e41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 833930449 1250 833929199 833929211
    0xd1b0f0909120509180c0d06150c0b061c260412290f04060608030703080c0c1c0207060906080c09090604240e010501030509030a23120910060b0d0906 66
    0x82200480d1701d0144949980030790382c41094803503078421208950044440c5c0800a8252203125520061034100c46070458995000d03502d078400021140c22220810343c01c040c040e07200f00014031507801d16035500308204a02d1040c10f8202440c0345442c61041d8019507229a14484500010600d24035150f403841e894007100414010050910007074030901214a1811020844100000c100e0b803801458000d01002c2d0096003840c240c0e40c3c0c0a4400c070001002441d00302000f0500748609001008a0204000186400d41c00c890342d07290001d440301414020980031682c084000217007503218190440c07041c2d41c030807040781c140988401000008003024003000c0d0710603240c444c2c0d00b0f20000100c000039802c51400080c06880e42c43d107030814034400c2050340260305041c944020807001c960048111101c10305245020107c1c2c0d0381c0300512108850f010b20420b0201c82c00403640b00300c8090307a000614003656196044030114074480364807800341e92250159000d121403e01640f11b10503459081400d0b200d100d142e0120784 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 833931699 1250 833930449 833930479
    0x51608070c1101200a0510061202090903040f0b07110904030c120e0a080304031a060108130c0b070c06081b0d0c050d0c0201050f01170a0803060d1b0f0909120509 71
    0x410184400083c01303900800d003a0400c02504000d0181c508021010501030340d803400c040f100000407400c8019000740f802030700058006c00f0600032a0007074600b00540300c5801e91100301c3c241c03942c3c000b00c004a038001c0d11480f200c0c0703080c90309407141d070311695050f070368040301c2000b41d5034400c0b40809580c811010b000d071440c42d07001a595450740441c080c09140e402123869078a582054001000c00055490b900100d01c0f042c00f40e141d81c46a409070380300414400c1d941070300d40e40389000c1c8940502544040d1140001041e8042040185800e900440c1c4c819515101c0c90303180c45410010440100407825040102001031000c41e4100c1d0b044900740c030105007080e500381101d6900460035a06980c0040c40141d550710b0800010b106410b14040c090110f08400c9003180e0715903000306503602c2c2c03504030241002c0b4010002443c0c0380d40d450100040c40c4d41c0034140c100c0050050522041c1c0c1c2201e80248000d001c02000b0209600c181e03442182d10380d40d00a4101100c1004401c1e00799403d9022501d1a0340140c000c05803070f55 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 833932949 1250 833931699 833931737
    0x13020a02150f100603060e04031b051506120f0d030c110604060609141021020d0f0c0605090a0e0411030304030b060f0d020102100c030e10051608070c1101 68
    0x1119120500b02d100e11850310704015400c1c03c12681283c003e0600e004802d21140401c0654035502661500344510040654400d00292540c10701c1c2c000c0c854465012078692001c50076424500402f02514000c01c1103040303a12140c0c8030110480d01100c540d1001d18100142d600c070745c00c03041c0d01c101241000d408540d18034202908088003194255180c0751143c104200ca86c0c520311508450f110000511038040c100903171030004140c00383c4503001040c81c40104401982c0d0610184010b426402010800640080c3c50a0300c60000f03020425240042c2064001801900800071154840d8000b070241541e181082c0048400c1c07a00031b00296000201c81c0444542d6480070002040954080c1070300090b1440e284080081003280c24910340e001d120314004c07080040c3d8000968000c0300c10280c00209141020000440082440a203506058130500c8070101d4203592582c4018003800412a004e5a100e0041c003054400349426641c40780000c2544a100300407841d41e04c840d5006040501d485080c0600e00c8030303034070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 833934199 1250 833932949 833932951
    0xb040b0301142719030203040f090e070609060509190801090f05010b100c062018031e0d080c070c0e150904170f0d14010509090c13020a0215 62
    0x144a04806109014030010500414960403080041403c01546008002500e450040000e20708404c078003000102018020310558002c0e007268030020b11020394030300300203014101451100c40903000e00c09020400511074213041c170660b80c5a8480e40e24003061034061041d003002002e03020340110520140403442d0b01c2e0030300903aa400c17800741c40c150790405043d040c013a0840740c0500d001440703080054501c80c140d03034000c10301c921034982105000424a070b0040c50b82100c11490003184020400008101c0e92201d010b01c0074220240b015402c8442c401e05600c0001709004c441e42c901c0c0175a50201a860024900c5090080e9000fa84581072a04120003070ba50200d1440d083d800c0b0300785e060704140070070140201003864078000c003000315040c8a250601c1d49070640144840e444903d101140001c80c3d160340200101207401012864404014641c22041c810892074000e001e010710504500b0f000c5410034000281010518000604521040040ba00c1c4580254042d0480340154011444815400c0115800d42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 833935449 1250 833934199 833934221
    0xa0e0109061d0108150a1409071e12080310120609020117040f02090702030c070905180d14030a0f0207030e10030905210c03030108031312050d030b040b0301 69
    0x45401c0342090341442e182d9071101e450440c800000b500410005500081c10308024903c032070440029156240c49030080c00d91207005040e05100d48003070040d219800a4000129100348008002c7c5400340981450000061302c14521044455036841d00410015401141c119078640f4440d501695580000c5d16404200d41c42526203039600d05050042d0350b0840488c20000b000c83d01c5400d25443c265458070f41c80e00e00250080d020351006800240b510b8000c00c01c40d90080c880c0c03000c4480090f5a80c0510000d070108071030406610b17201e03400c09084200700003030044a0409030385522103109041e40f503040003a000101003030400c580300e00481c182d130406071000340302e158001d507211070800c102e80003400300b240c28914a00c02014034040c00d1801064001c40d030030000b5101c1503003c49034000010500c915500405801c01041c0c0000400020703131800c008001c05100868042184200e90780b10b10b02c814800c0c00600180c0703aa0028403411005610a60103807220300c100a10000d00440707000c0200742151403241d02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 833936699 1250 833935449 833935451
    0x3070624080c010305220f021215010f05010c0203030d051005061c060b0f0403020607080708220605130b030a0e07090f0501081903050a0e030a08041d0105031b0a0e0109 74
    0x289050320f5a040c09141d42c40400810034841c5000c401500d1080d185810101401100f04413400c0c4046583e14150065104103c0003107840d591420315120750526400e12403203101040a00002a0301d5014070040c0d201644c00502850510303030b031000b030320b80a08030052001014140012002c80c442e9203070000f510282c00d209119980b8020340388100c0044840503080702030a900f0602c203400c0c9410800d402c4030282e0f0343c10f84620742c41d02c12a140c807100758010705c2070040c658000407a480d1002200950303071542c0180d4010700d45032016910001515144500b96051514903080881405007411072401584c0010604a0005090074402011800c20f1250303080368200075200c0003a40b82c01c01c80d6010f96800b500c2480c2c068801034035900fa040c5403401030303140f005050010116940d44800e00507200700c02c4900000d001d903007a855240c640582d2582c050300035003542d40402c4091956103911024054141c490250082003103041c20301040700030341e0300c004526070b00c1480f003000801c01612840981e8028079403580 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 833937949 1250 833936699 833936713
    0x8090a0816030f0e06042304020309030c0706110607080403020a480510090f080d0f05160215130b0d0c0804110103050c090301051302040c02010606020307062408 71
    0x10340240385030811a5041e0400072401d510240c03030381d14041290100e03501c040e0387c9103100664902030003200940d520b04945c494404030400944e60004030051901c1c0742004203541c501c40c8c54050a0701c110160b20342029065001900050703185014421064000d40240115991030015640da00340343d00308210035003807065205007411126084505500030700c0e10600000e0041300b1480b504101c42820510440b441030200d94444d9440902a030050005800c11035100c0210903281c50005503a104800303009800900404051a13810b84504140d810f1014000703084a010f10305070302000814082c3c00c20240400d0b40070030085512444208040c07000b4200341210340d07120300c15100800129161501e958050111040070040060300031084d1110b410002d00780000c0984406180c801540034205c002a099840d000c00d0001c1052664000c0e10f0980c400c4a05000d9003001001c102e0980e1060720500000d40d10a20074a40043c2040d0000c8088074910400c58805d1800305207911607030084e030b602803051500820 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 833939199 1250 833937949 833937953
    0x18021c1202071a0307260103021503060f0405060310060608091005010e0c0711040903030902040b030f070506071e0f0501050a02090a031401060e1018140708090a0816 73
    0x24540c091040540d0010b8040945030124400b41801443e00c0d68881c0ca5001002032000d82c01200c44035a8040040d0301c00c481c00c0724070603e00c0c820356001c0c001a0b109809180340c0080e40415582200d12030907000e400c07000c0b60488030092002511020300345c40d9145c02031503d01d20715000b0901c200c0b0b00900c40c40d500c02480f410b0400c252401c4c1003240365401c420702e04140040c0000c01c0800c450b00e0b000004400500e030b4500981c03c2021b8613141a800c0300b5800360410070102d06240e4144c012400c4c0e280210780801c40d0500102c101030307480854005036202034116501c104003921740000035003005806050b0184a009008145c01266145c2036400c95a0858601c03640701032090074818194429940c20b411071800001c8400151001650b10008180d1200070348900711505c070030342104008000c0748041a000b8100032481c08115402401044038a640084011000b0b1880c0c1c002e0002c880030021681b8000d40319144203c445d44002005041c55128000051000600c503200900034400c81c503031000c2001d1814 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 833940449 1250 833939199 833939213
    0x4030303060e07020604030f1101050f071805030607051b030c0a0b07090302030613152c06040c09021e0a050a0909140f09010e06131e0f0618021c 64
    0x1d400c010400e80c1c0020420043c075800041083e00150035041c002d14400c02c10004544200018021145075401c00042c840b46807252a07115003e0b0400d5251a80c129841c0011031424880761b210b0141d040c1c1c48940440d00300e90241000300684440b00c90140b540e10100d00809144ae440b2060440055000d003031104284010700944a41000c12854001d202c1484d43d00000c1c0d580c400504081140100060f1a004100d0050125210f4102c0d070f400511500c034038071219980c0310007500740030054038130204d03021034101d4000300300140304a074840c200d45551418800700100079009031007042d171041d622000c007000c440300c1040039081c03820300c035074981e43d8581a440e00100081129409031000c6414000742c8900c02211102e82036002c0110740301511a50303991f0604c1409042060140d4280e8040c59007440802003c0030004646180a03514200101e0820103100c000020f0200300a001c0407400002900055a15041007c0816031403104c5032070b62081740c0000d07081041d07142d511002d010420070b44100300125 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 833941699 1250 833940449 833940461
    0x18060306060f08070b0f04031101030915090b011e0b03060d0c030813050a03020913060b04090305031f0e07180510110c01030e0a0b100b070b04110d12121d0304030303 73
    0x5c441001d0b41005038150060400713000754000102a880520041e1205074130940c4203d641c190086205001c3c0070603202554001c01702a0004c5d43ca001c0107030000b00351000341683c800c0c00c60212070444c030a51807034680701c03682c2a04083c000710b610800c8000c0f2131011900b04040e240245000c1e1510b075903900c400c040e01a07084201580614000c005944007000582d40350f00348160f01100078280d44c0f039000b0007460194014031743d00c43d00076445071408031201d082c5079000014503c11540c5094440008102c00c080d902a07420910a00b55542c61420010349000e204034029054020a0041c3c680c15988130300005000c1401d5900c036000240a044440742d40000030401d0010040007803d0400c070b00305130441c80d1500e8014008029024580107804035502c08103400c180c20080240b460459213a01e00d52910310940703581503805581c00b00251118150502d8040111125180e0109008502000306901500ca119800c1000c0b07034090342c0d0703800520941741c2c04485103194540e05409155521708615000d011104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 833942949 1250 833941699 833941709
    0x1a090f09010b0102120a030216080f0406110f1c02120a030b04180302061302030f060901090209100b0d1d0d0908010c0216050607050a1401061706090718060306060f0807 74
    0x70184585c0f0700008401c0d81243c100030040d107005640c40d0100030398240101d0072008010310a43d4001403640001010b04050400d98206980b04d108801250040e00e984916100112800b50480e01d900014044d048034101d8000c0c1240c0117441090321014107400701074000ca42c144000c60f485200c0888a0f14040c810072010303480c8078410311003032001d0b602c1c02507862400034080020205807180300410341da0104182c400840c03074036045411519001c0e80d0b03030b400307090300c0c8108a004d01a540e0114078801185041c4405590210b007a0742e08004100440d800507020181182e0b6559040d2a08005107000601189181d0540707600c1d500c840c10300c1c090503942100c010b00300050454114120f070106c141040c1c0d802c2011220112100d40d102c81d414281182402e080c444024060343d0440d0000704d1015040d04032600f1504858080e0b9883c0d0181840d46460304001c555550907504918001c0c0100c0014080308040e8031100e030000602140c80760b8914080319001d80110600804041040000740010812100a00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 833944199 1250 833942949 833942953
    0x30201091e15030b04020319060b120f10080a050a03090f12020f0a08191109010602060a1505060a02282d060f090204061e091a090f09010b0102 63
    0x30440118140a160542c0690203a8030303140b00024201c54880d800101503032000a000b15aa070070f2100f00b41840c90b05034124038581d5070810b240082c040145000381c855480580041006507500c1c25800c0203c071b9001040c03401040740101e004141f4940400204030414841c0e0300900c4102d5181c00d0240880c0701d140d11a0340640101c0105005c031f83e4401004544075079040d641c40d0158100d1800040340c0c00d906410290325485410788202506480d80d0020074800c4c001c0b003050790241c5a100078002d400c2d00034007401015a0244020a01d181e070a944030f1040381b019445245003468583c5d00060b010360044908c0001030b40107110440d1a400300c0c0340c00e006000000c075030803045403510795101050f11188160803030744445441450050800045902282c0d01d0b8000350410040040030f1003040100900007099003e0b0f450244081007660000100c18207000c00054144856844e02c1903031800723410b006c07400c4005811510112500d5803100c0d0059402480e14015040c800d14181580e142100c02c003149007070442d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 833945449 1250 833944199 833944229
    0x70c0605090606010305101401110703080f07030908011a0906150c03120a0b030703030c14061905130804092c0102030106170403090b09030c0d050c010905010302131202011209030903020109 83
    0x101d0f0442243c00d0452001b2b013091510402d181c0d500d0350400d11640c2c4060400c050009540e141c1d107907804000c1005604c40d86800c404140c446880900300c0d50001c911100d825509081401540383c046619039100900808001c495444200c80000c681c00850283c4001d50011589000d20784101e0301140d84002d03d0340e4200000107100700020740c0d07000c15100180c28007003e807010509004400c125080c01815000803240d46050010840d080342862440c0e44070030074504008600d291401d44151194113070407003843c0d4281400d152015004203007410a000f600d00643c51100350180304a902c0b18042c4030b0501c0010307225031600901600d983c89244004002c2c811810400c00000c0d082124070341965071091406807151030180201b440c000d520800c1c0d43d8030244c03804810f01002000200200c802c60203a07141907903a580c0d04019400da02581202811600e0103443c02c1c0a100d16001c03108107040e00516001b002240301c00742030800c4800003031060b0001380e0790450a00a65070041c51030b000400041c5900080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 833946699 1250 833945449 833945459
    0x50a030b090c12040c030c08060106170f0c16020904150507090b0d0c1716020d020703050a1119030602070303181a0402190e09010b060a08040b070c060509060601030510 74
    0x3480c816451000c05030f8124a02013004c0c8610100801d02440c0c2c441040e00319240c903402c02580c0c07540c0901ca007500084614101c0b0540703980c111070702801112440340c4e4044039115544041d00e90340000105012a420f112a00d0001d81d880c014000e00450082d004049031030003203d450b1094a9004200000f805a00441004414250f00494001c0e150b0b403100040d1107546840c04542e00c894125550504002500920084c1810f041c02c02807050903540072594601d02c01081070307888a865200241494105542d040c02088201b802e50085c040010105c0c01005040394102c512840346030015207006a0108564040541610800c2d02e046110a8450600d06940c4c0e00c0d091101081c0c9420080c0d01c001c013001c50115121540540454281d09100c080c05c01c4d161071600341041000c640440c4151f0a1444159860408400b01c42d070705949551551107942e0b581e101d00340c3c10300c0c001c0c2c000b07020402160400b50100b0420b108150185c107900014002a081040005054440217481480c03c7c41509030b00f000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 833947949 1250 833946699 833946721
    0x22e0c0207061416020a090b0307060905060d1109031e060603070b16150e1005132d05030f031608060f010f020c09270303090316060b0a06050a030b09 66
    0x83c03800300c0f0050984d90740240c042000d4203c00d041d00001c0d00900350010200320300c0040d81100ea100340c1e00b50f045030b0040759984011102e040281c03142641054081104500c284001d030407100100341801540c0d89003003002c8021a01e0007400c40c110899a000840c01c3d0112020300780701c25a00b0007011402049070030b080883c0342d50503209010810b551004d444928808000b0710140900507034a1000081000c00c69400d003c0340c40e062007640d140c0d0240d240c600001c4100c20a60030090500ba000340503c1c41c0c00e001482028103407010351b60700c000e4020001d0040000107504000600c3c050440c96400c584908144440284a4400a040500f4020340800300415611064184044804240b030121200f01200d5820b900b01b2031805d07560390304018100108175541144108100307402000e124414684514009915140d000c20344405c099600b0400c068010001d00890401c5980e0248400040134201100000e81d41070185d403044000c80c8012032016103840d014070030184840c0b402d40348a50246424a2296 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 833949199 1250 833947949 833947967
    0x90905100b0a3b040204030b0a090203070f030c240c060203131a010e0f04030c030c030e040203040501060f05120303040f0305042c181c022e0c020706 66
    0x41c240d440224140b44040e1180c05404048110360b0141c3d0100350b49007018070f1800c1c24800c08504030742c4080000984a05107482200d0071260860721032501921100505070241c80c0c0314400366417512038007030301080c1840c900c17500a0042d4455055050000c2c509480303038440d003940120103000f00305145001e030301d102e8100a00e80c1e90654400e0300140c0c0e90f40d90f03580c924171070187c54902500c0040150011064042c007816441d06032400c00300d801c44959030303a2102d20f61465084400400241104a2040000340125003440320386109040c00241d00f6200c00119049030022601607401d44e4652004010140802c6441006400c040c0c624050100711032180039568817010700020103202c0080c0c03481d0182341c8100c0a550241860007070782d007a4081204c402e413281c882d05418000b9010684004500103a150008040450420340040c0c8464150200b070002641c450940070800e500034442c04c030440c410f5264001c0d0f03100d0030030351628882840e92540c00044850035508281550300080c014800180c0203601d071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 833950449 1250 833949199 833949209
    0x100518010c051f0204080115050a0b0906070602030a090f061407050c0d05031302060a050a022b0c031403090d090503162102181e0408030106050c0123060109090510 72
    0x24085141004000c00080c1300d075500006d0603520740300c0320b1440100030303691003030861b8801c48a00c03052546030b0329000c00501ca000310741d0394845020001d880009442e50003850744030050310400518000b040c2c41e080c0300004000811200169106001519808401d48040d00303c44145401c0e400d0078900600103035180500e02e40c910601101000041713000814030008105158090401a1030300c3d40000d0141c560703002060b021003d070052684440080070030310721a00e4503100a01004030203659400e410b0302d8040030100309508009001b00303c8085a000c1c00e000314090034028005040c07240610000800340041504500e2081d08842e0382c0c8400c1207442c001400a48036860050346680760092000354001d810a800250400328a80004040d480c81c0c495581c8151802c17a82e03030380440045100c046131400c0440700148508028030040c00158884d0020b8242e0350022400060b102440c80306102140b0118000e08458031002c1c800c022503541d00c000240020103d051042c031142c28180c003061410a254051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 833951699 1250 833950449 833950483
    0x10b0f060c0703050f06190c0e0d151b090801050c0405041d0a031d010c05060703150807030501050103021005070c121a0f0106021c0503190b100518010c05 68
    0x200c0604004244841801160b100c13084403030301507000c1106034990004841210101c1180d0002c1241c01c0f04a004000d200d50281d56401e0701c0240001c100224003444c2002a2a01d000c07980e84d4151395403e510843c80700c0d05040082d450100d42c210f100504405041d04003030703220f134101824052003801d13142c1a1010f6030341c01c45000c145103005041001000000142000d076601c10385008005242c0c20107504608000f080400c125802001300041d1120040e03148010320582c8040c0000d14030912941c082c01e5055810980116115a120001441c1610a400548040c0d54a100400861601400c0c9003139505190805c5401d081c4070b51502010581607210f011030f4107061080303041c2004041040c1406202c40c00802c034500d0b0a0603e46c0c04442002401040058840d00303403001842009428007100d0b05015070703904c41c0341d5906d0007040c40d03c0c0800482608105601c402a0001c00d030b50320505100401d0250b9100ca07114103420b1072001405400c81c6016041c0010700713100318080b03980819138078245642d580c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 833952949 1250 833951699 833951707
    0x4020c010e0f160b03220b010806101511030c01060801020405040b04060b070305090312030403020d140f0a260c220e0406020304030210050c1c0e030301180f0f020912010b0f06 77
    0x19240b007460304000b000c0c50386001207080724810800c87c15103440c182c0d00c1940c1180e41503515030060700c0015116006444410801050741c0b50243e00c2007031a100d204031180181c80c10007000d00070300c50075180c9a40100c9620394002c1828003090a1034030034800007000c1103905101c1e640c90001861030310300c103d6002904201d80010702d1021602c0421940304620070100e01c09540f4034040c10000c1d1904125004c0d1400201ca4110034040640c1143c1584c403031200c8840c21610300842c0740d009551030003015040005440c0910340c4ca090340141810314501c152903034103003141e03101c0140c0a4102c10038420340c0302d044009900c400611031031090051b115401944903200607520b440d02d05050345400201c100e403655040c00d0204200c1003006100203800d40d801c0005045040e0b00f91002e001d81550214482032100d64001d20041180391907980c2c001c5081c280b00d0078006403010703204582e0030982d03802d0006062800e0700000d2528990030035010f4000054030403402009042410030018404420041d01e45100b848045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 833954199 1250 833952949 833952961
    0xe090c09210c01030e0304050103090c030204090311070b0c03040b071a0a0c030b030f0d0f110d030c0914030709050a0f0216020117070206131104020c010e0f160b03 72
    0x26003250a03100c401444101c0d070051450707030740d254464900200c1c0c4480c0616000c9814030350207070142402071900c1c00041c600301814480110002c20036031710180e440101000c00000135859900c40c08403003e0099460749003c042420b400c500d84401584141142e940c20408408840d0010044d1410f4a502c03c4502da55034920f4141002030200410708080011100d03814892a151603a01c5141d45181c0c548051140c029a901050b440d03804842154a0b140c214170044080d152054046808010172030400c40e003215032900480345003a41f0f80288601207030355000d6060459800c42c0d040320051603090000007002da9020302181e103a01d1240305041c000da4498010404008258200050b54184020110745554010140740c0c3c5202415070203074080f03401c4c1456030505c00e01c20030100e44a00c1d2140c0041c11a61034031700b4001c00b1050b000070140d4000e00705000f03617900b640d583d000804081000c00001308542c00c40e2103509040c943c410002d1310031980041c280703032601c40854044800712210450250740380d64942c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 833955449 1250 833954199 833954221
    0x503040305130b0d1e02040537030501140a02030103350a08060f0406051c0c030b09030705012d020c010204030c0e01030b220206210c0418020a0e09 65
    0x242c0201c3c01001e400300780801c01c6480c039880004030054818139041e41020104141c0220700c640d00546400ca01081a10002034100380e81103035070b45082076042001c600d2400314108400e4402d800882c1c269440d8004c0110030920711020b03681040b0222011032455140da0354441d18020440d5500201c009403048c80300110302c5071007010502000042407140c0e106182140140721480458165200350380b503450240c11420b1a1141c5029210007030325950402c0000709a9001007045180112120300030510044002410079a43e00d01541c0110700840d21040c1c075140c1142550400020301d5001000307012003514416003140359082c9510411001aa0360364250001da0180c45540c001804500250400042d2030303401c2050603040b01c4c0618070390311a90b00c8501810041c4404101d01c003104e04054081e40c4054036161000f40604480075102402a51600d64200228001100d03007480705035000c54108040d5603490007a969581c19000118540b00070a500071b0305001000c106e00e40981c40c1000084c1641c0c100d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 833956699 1250 833955449 833955487
    0xf1203143406060b04050301060815190b04020a0e030d08090c010c210203040303020d0503070903110f180a0f0618020a170a0209130b0d02120c040f02030105090c03070503040305 78
    0x1110b01480b00310b40702d48880c0025070040c070449000c2c0d07103020000034a1640200e58a0072290207012709010350348074103402c90304100c0c00055009132940d0b00d0003d8120b9584502c010560f030a8180c0f10010b00203103c508050611109003040d10500905074104105440e01160780c01000c12300742400464450303207007819410f48041d40804095480c00c982103808607500080030b002228825802c8404580c0584e0003151903000540300c45010039101c10091000544802c2c0c00e07042c00002405002400c600c03880051400d02c0c440c08451442c040d03410500c10b07400514090008880c66400040c4840d91600111805155000000c1d108550b130115840c01c200d440b400408290112506000c40a4100b4000a00c02503124403c20303885150502c2007200c25095900400401e020020080d4040400729000d0150050030000c00301d040f4001c9949680c06a9030700c0c800c0200300b5401c2800141c882d0b041a003070104020000d08040442e0b001481000358013640a412a6881507040c1340880d00c90070809038100001d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 833957949 1250 833956699 833956703
    0x20a06020c1b0a080d230724020c030d020306030f06161205220503042d0902070503180a051302120105040509150c040f12031434 57
    0x30000551514041c000185040b44962824103030405001d50310070454000414414000d20340c0103810b401c40e0705401568140e480c080440701049284441c8035891130913a00000d0121031400d0407120003840d180440f284c1141b41100d03201d0851a01c0c80d411000c644c2c0740102c101082403160000001a0251000d11291400c01000307421075030503061140c0c0d1000f00c02c03400011b0200060510b0900c05111030940035440c021001d1146042c00504480000c100354019041c00381c1d6280310801c0b00050000c040f400242038020405840441c1e4684c0e00000c188980c410340c495014240148a01e00101304c0100450748281c940150462030ba820b0000401c42c0400c042d401503522030b500d81554400c100c49600200798200380c5170400c44031aa01c84042004480c42601c00c024541d000f080144003c0b03d104107059003145001c00d106050075901c08081003103c0319038120348807ea1205c030088013010b80100f864192074204280d81401e004080b51084681600c000d40611000d2a8000c000d40c140415501c81079407503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 833959199 1250 833957949 833957951
    0x607050601030b042a0b0c0a120e040e0a11011101061a030402030f12031308090907050901140703051c020910020601170f030a03020a2a02040f090c15020a06 69
    0x581e59042c0f590309040b0444060720895044000c0380c45201076031402c03404180048030300710340040c1004502549a013004250110314410001c61001042d4501c26021100400e40c1c2c4044020118405102c1519001c83c090740b481d9000a0031903000580141c80216000c03400c2c03821415004008202c00c0c003420a0790b200a00e54000049605e00600b070349002188914029401c43e00000c0c8000c01c06a91141c251481c2c0101c41002d20119100c2e42042c105200194024a0308d50309010200700080d41c140d170255030210201d003000802400c1960020841d4030040c038445007050501d03002ea14091300c40d00c0f580a00e44000da08580c3c0d4070103c1d8000d40d0503200c00c41c1001e44024180400c1c4880659501028003840900000b000c4c841c048801e00080d0444920300301c0b41c0554100900c195050300030790000082c28050160050b5041011009010315649800b0740860602000703110380144012120103040325412107007005200c2022070340880c65001120070001364610213040442040f07090842c8808018011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 833960449 1250 833959199 833959201
    0x80405220e030403060501050904150f0207020915042711040f1518090302030d020a090503060c0d151203140f040e18010903120e0a080712020c0406061205040206070506 74
    0x20a07070010141c010f4a214000820069880f00c00b00050024111401010701d40116081c01161240d9048040340e01080e10015060060690000c3d5594200700c4450f0f800949074440030f801440e0034040c44100109485031400018030341e200000c6542c40750000581060404010070340c8607182c9611400a00300200800c110308450714890841840c01807040d0700030482046121011400d10b44609456603905400442c075140c18020820041d41002d0410401c0c090f01c1c1c5000541034509002e807611541c00401b429944846032030101c400c42c2c62080e500704030294555000e10036180d0b0031051808594060818000d402107505c8064428804c0d01c3c04851900d40220300010f44100b5101d805001e0704801d0f01d1000309454040b8650300b00c03600340d00c020b00000d040c0302803115031911300c5d4408080c001580e02600c14180b00360702d030415540d002d035000b186c26800d84814060300741d606201050440200f11014014285008801498039181d148020310969480000c102155510012180b00646c0002039400d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 833961699 1250 833960449 833960471
    0x1d01020a0c08011e05100311030703050102030c220b030403320a0e03060c03061207030f080c0d020607080106050a090513060f21060b030f1005061206010308040522 72
    0x2a02c1038030b942c0340407075002c61010b0b405044c2d40e001e620f02c221001c4001190306032654540c4988002d002e00541e0b0503004803400031000c038800380000e41c8604456262160b94924008064110034502d040300e041a842c10142848030602c0030701103a0700541c240c6801d00d520350420460012196020202240214040082503481c0528002030141c1d50519140d051f0040062001d040e05c410307046680320a040c1c01040000e0b03c7d8a4079078000b0520218000c11940066200da440d000b8692524030b0a44440e0000704030700307550413000c005c21840342e5041d04c0508000e0904841c0500290b00601400c8144000442c688501c1031080140d100205001000000043e04100340007008015900a80c000b52441c2c80000c030b00c2804091141c80e046003010312130344c0c402c02e003904c40000400a101015a01d0b004004c0000c59942040240f00e2643c440c07050005518245070b000c00582d00a081c44205e942e030840401040400c1c400401d4500301c1b441038444031040310410100c405050362100c0a440b91518000710262 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 833962949 1250 833961699 833961701
    0xb0a030237021005060303160f150504020907030c0c0803070c0b0f07200a380907091811010c02100815040e0606150d09051506101d01020a0c0801 64
    0x72441d1995000e0300e42e5102445150700584004460b0660141c0c010002510a0b201caa0206115603000740e41241800e010350755580201c880a03070300d81001c03a4884060200350300c0c045240310740100560034100070040703c000000d0500d02180d5006451f1901c00710020340d500b80904005c0c03403080e41c000d082c1511480c09004075410f150081d01d00c80700040ca20903002c806c1003d010b020300080b091941c02000150801c8e07030b41c0651009214078a69085c0c0c0c08003090980c0c080c140860010311500e020f000c9640f490403100440c030304181d66000d501c0c10b80c102828503006001d80300070745948a8001840301c01c4140d000e401030380d078030514080007500b0003290b4809130115588048810300441000e8112205048004200002c0d03030061081d008141d04100040381c980d01d0030582450302000039041040c01d210b520000b000032990003040c10358250f0454102c0c45151100001340039400b00c800ca8903a000c281180e08020000c1425502d640d040c65400d05118543d40e001f0000e03240a20381c0040844241900c07260494 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 833964199 1250 833962949 833963047
    0x12615031009150507021f150b0a020115051e060c1207030e030705060d020c010912020a0203060f0c0406051b160501110a080a2601080c09100b0a0302 66
    0x3071440c0343c2e0444101c500290b1800340382d010b5007003a4028184c5c0480070412402041c01400b80f040d01959030031115414034070500c1104028440c001ca1140c80324041c42001e42550b502c04d03017001019604000620030303581c800c0c26926203880048120600310418801203000e43c881c09240b0110b5104d00644062034600f1100145245032080e651804020841e8050540e5081603021340da902400901c161040b101c1294042c1171540700150011030b8195880d00c0310742c42c4500c40d104040068008000940a5040410002c0d4001645042001e46032900101e80c4d455405030f40a510100f0500243c8046c1180541d0741c0074404204400594846c6400001d8603c0030303c250388a03041c082140010b583c0342c190004a0180a9130ba044641e0614001e41003400b00d0300c1c90026030844a10300820f4101540501c100701c50315010b414207800902c1c41110780d5040103000d400040015040700d0180b0400d0240003980c0c400e407060840141800340e12070380c101901801e03032041d41c140c20140c8441101062100c144030b003807074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 833965449 1250 833964199 833964203
    0x1508060913140303100305150103080306100c0b010e07030c050306031b010903140304060e0d0b0103021005071a0f0c0c070e04030c12170603031615060b03070c0c05012615031009 78
    0x2c1d0315090203142c40b1008c900091101404080007031000803030728207200485091001da14902004850020303550130717a000000b070304001c644020b42c1c020071548035014800c402502c010390038064203520303280300002d960f141d007407880a4507400d08079007511041c1d003d181100041e690004030080000c40b42c10103140c1d0b0b900b0510850b03001904080c1d8100031402e101c801d0312149a00400340000907801c40c0c003440200003000c10b021040107020016400443c64400240400c0d0702c0003408400242420710b0b500c25841c80240c11802400c804000c061425040000d60304110b80d142c0d000342c00281da6034102a00c10320640307980a0481240359000281c140c1d400400c03000341c00c14118050206494070030034581d51340100c4140d42d101d020354110210100b04214112070035000441400b00d5000d841e0050700001e0382096030074401007203200c1024000c001e000000700000e0a02807030720031220f2004070b00400901840310312205458113160007290030004070010b00310103441c000d0102d5201005810035000180b85600b42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 833966699 1250 833965449 833965453
    0x17070e15090105010903080711061903091103070e010614130810060e240316080708150f0f06040e070b12091504080f040504151508060913140303100305 67
    0x803c43d58042c08040040ea50441522410941c180e030741c60751229140b080c0182e20110034060000c8007025881c0124100c1700c241e6005c01e00e603e05241c0105131089044006210390484c0d1000c1c0f24540e8443c0c95181140c8241c513101850181b00001200148103081440b4aa07120f01c100128280d1800182c12210500e480010003071259100500c454100003513594560807601c520b0160580040e50042d9402000e00405988540080d0369050800b80281d070302c00c05450b04540c3d0100a88042485403410081009146a6151034000801140301e580280504120000707240400c006485e0350344003600d0402100101d84a482e181d60390100c981d0001c0c3c80d611710041c1c41500103012000003080490300050b200300361a1040d11b0342d40d6000f4007500309004c407a1580200303010005041c0d44900503123000680042c0310b0700c03129040070102a82d002d4400e41a03418000510103100250b1102030041d40d009508a40811b040402c5140c034102920412945101c0341c40040705210040c0950304060003203030300c1201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 833967949 1250 833966699 833966701
    0x50106020c031204120302031c05070909090804060c05150a05091603050601030b04170a050d051e04120309050106082d070504022109060708090a0203060117070e1509 73
    0x10405994040d0510007504003d0284020041c400201019002c07143c4a80180c900302214454a000004e940f407c044641d130b6195000c1c840d8054020b04605c01404112a05001306921511584c0b03151189100301005c0004180301e1300144401800a52a404c0c2d60306a0130300b20f030404000380c1000d0310301640d2050850150b07080e1404500e24003a1818101c3e03521102410703441c1e00c0c5403a501064000208140c1c6c00b4002c0200080c0e103c0e5480c0000c00c0300d00d1040d29002c1e22140302c03040c64801c8840090681c042c1c6041c030764104400101c6084100c0c0e0150b4060b40701c0c0700100c00b400085014100000005103198200b020200342002c0100e04400e10903640030400045800050a494203203070a2400115540c0010300d06005504242e00200706107042c4401000901d280c1d501210003e19084461440941102092205213a40188026002a0042c0040c5039900702600002c0c1c40f40c5040c450390703070200112120440071880c180004c000420503020000e4491400415150021224505252103000004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 833969199 1250 833967949 833967973
    0xa0b04061107150c030207020607031119021f0e04090605162c0a05061c0b0906010e0415080109120807031109060a110d0905240a1b0203060a05010602 66
    0x1001d0b2614a90842030301c07105501d00c0740c02c09004102c04400907040540803c4100c0c003585a100044c642281719a075401d41880014141c2400c021819108840c103151400e007050141c2d51308074a480322441340290f0f28110b010b840c0d905480d980100c0e01042c1c1c025040100e0300051090750740c0018820b40c40e4440d401200f032500c62044407090544040040380240c500c4200b1b00b440c444191143c94500003a041014641c0c5400000b40141c100c403000040103480356140507803e00d410b014a01d8850001c3c1d5002c2d18a043c0b50001a00c005100d640f0140a5503485a15551480190340414020030103103008005616240c1040005410481c0074003002c0f4101034045118075100b44540d8020040703e52200f420b292441c020030015a11600203c010080d40e8000034050789d40c24006451521801d0311008004c1389480709000c0c261810015556400000b0948180c100d050202281c0000e6040d1900c4508890045c108a400040e107600280d054800c132010401c0f540890380c4424143c450640840760300700c03491 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 833970449 1250 833969199 833969231
    0xf1202130906080c28060c0c1805060f030a15020a1404030c0806090c15090415090204081b0a14031c02101407140a0318081305010804031704020607050a0b0406 70
    0x400d22201c205c4000300300803032440742100f07044003445107405c103c2040d50360701590081201c3c0f50714020060b81d22030500800d840d280340841c041c1c5600fa00542a10103440d1920310711081114011034a00e5000107442d46007074815000140d1103104c400105880316103d041c502c80820040c0101500c5204400c0810408000000e12900300700008240d5034016010f07400c418000d4205461464200d902c41c0b505e0b5124005a01800000e016650b00040e01c407440e00f00b4040c640104441c40d0b6030b51380320f0700d401c4900039200c2c5581c0c04161450346c043d040c066070542c03004c41c0c60004040c0001c0140d41e46112410b140e1640403409000c180710416003030010240c144110b80000304240e4801d40402c1d075880e16002c4a01d4440040d1810b5003880c10300160100c0040d102c3e25201d110a0012601d2071000528002c049e0404e1800340060b1800b071031704050600d00740d58090079108403010f903860109100000501159100022180c071141c0c4070080d54081042032815252449054408485507420482050201d06007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 833971699 1250 833970449 833970499
    0x60812180105040e01031509050607020f0c040908040504090c1509030c15020d0c03030f06080c1005040e010938090906060f04050624030a0c0f1202130906080c 70
    0x4074040199060f440d5a442c81f548000c3e4003410781b42c85446c0d21814003c1041484294403503240340e0094010340054a4000741455200100d076842031345002a69404121850240c40546400b035074000b8030100c0d103080103011070145a10208100f0245a0313402c0710160710003081421a880303910014065512014100d080e22401540d110040c1d108180800c059881406d003ca81c0303e0003030030000f5a0500000101c070503144141c01002075036000c0700700344a440c1001515541a40481d10704182400d0400c040006254018415280740c80c0d241c04040030354600c081c84600810400c05650354203040c800c211602103809082c0c0d031900c140c038000b0000305400c2d0041901c600c0f8804c0140110280e6070100100001080d0140449803c010744031400000d11030454072200d126031180d2a65912840c0c03280601040c0e90540341380c441001111488800503e42045400901c0c1101803009629560144010381c1076880b554441e0310424102040007480309d40100741e03e4541d40061f1040004410799400c0c04e202040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 833972949 1250 833971699 833971709
    0xc100f02060c09090a0c112d010203160c052506030b0a080d050d020c1009021c020108040204020711030706030f2409050c041206020901030612021806030106081218010504 75
    0x20010000174440b10340c0ba4415588409941071901846a40681062824581000e0031a100b03150a0489100d44526004440300714450b1000b90714518000300c40c00d0341d20540102e81d0b0248260020a00200035041c08900f4200c200c01c1000c01003402100762003880c84a262140c0c00100f0300e0859a4070050034108925001e41e03481800604829000381404c40d4070380d0001e02d03480c0c03005909004050004405100700000d15040d1a808a980743c0e150040205c210891a2001d0309804800d5280d801130342c002c450307242d11a070111001615205c0c03500f000100c52030810f030866407601510002191450700355201c16482c101c0385100300b2860040140014820503000da800100605820f020441400b04d0340110703a00c410318070601410240e40d100d0386110040410f41c100c07200f913000300385c05055580c1842110000c2202c1020704d41c030809680c0100e18180503a5a104000b0054400043c900d0348094001c08010641c180c01c4038044240c02d41030f00c0d00383e045101e1261600000c00018402e40d846a0107680c1aa5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 833974199 1250 833972949 833972959
    0x40210020a030e0603060a0509090601260a020d0606090c091a16080d060803070c0302100305070503060f012304090501050402071a071202120711160e04050c100f02060c09 75
    0xf020400402802d500000d000c140e10540d80000440c1ea500d80c06d200d40d000b0140a0000c01a650402c040c507180028110260051011b00e146180e0100d4000a003d008068050350035003010380d01410b10502030600c603000041d0142c101002003c090b0340c4a1007650444996080344c0001d001003c0f01a9403521800000c1c0e440e8616191106c408110380f01e0003080781d448015000625181e448031460b0840c0c2000c070050700c0340d4013641810010350801c07000d030030601880c0c0e140400c040c0c41e00d100c001d4140c6c00041d00a030301403092050070443c00c0c0d0064560010745e940c10300315642c180c850040c8012160b030260040481c0e403800c09000182500b082d000350340d845d59200054130041100c00e0b15412100d40001c0c015420402c14600c000043c8800d031008150301c0c1800504483c003454200700c00707000350704400340c0d1000603800003a0500d0000740310549a000d9070000d201c40c000f035071102c1c103010f407401951100e215481740c0c81c1d20050307400e140c2120181202c00615000ea814507640c2c4800309940b4092450041c1e040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 833975449 1250 833974199 833974217
    0x9030309140c0907020726070905180d02010623032e0f0e0309100504050a030c0303030b031f0b04020d110307021603050d0302090d060c1d06070c17100e0105040210020a03 75
    0x1103907100c09003c140b5a910341168401603032740d00c04009513201526155190003072075142c1a003401c0180606068200d00340024083e4a01c3c040c0d88840c1200381180d0404004440c9003452540d40e01070040c280d0264014902c240061104c00341c940c03e030b841c0c7e0351504042c5403402c5000060880e09009400c0706d40801c001131030800342d40d5000e0005406808250340c081010410022507599180403074040030358080c601b100d07921821458050704841d9100c1205d846940000c0000c00c805250051101240000f6030f03010481c0360010000c1130181c0244002089007904000c82c6011070502e5a000d5882041a603084980c68882c03026228152101ca01005c1d0543d00011800640280a50001c05400d140070304851402d50342070f00d0b04001c440c140c804810001d800d003c680d40030001c413003e003403007400030480c0e00364500174459441030000c040f40e10070071103410742d040303c8100d02d2402400f4440c0b51581c600c1082c41858000d52140e4020001103901301d102300c2c5441c22401841c0d200103200180c1a9043c1c41d5007210b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 833976699 1250 833975449 833975489
    0x40308090307030506010b090406080624150d02030405010b1e190e070206010f0807050319170f0405041b1d060c010f0f0501060f1209030309140c09070207 68
    0x19544482580307a09442030400000000c1c2c0c0810a5034024049852466101d503200d9041106440c140d91000040e85e1000c800d000918852400049441c1c020364040d81c0711030301d0701c0041004001140c1120305469004503802d54400e1b9540c006600c100d01c179000802801e5400001c01541c080342d00f0809440014000c0450340070b040c88949450224801e11014491590b81d024a04140c4004c0380e4220041c1c21002c010030440c001095184051300c0083d01800e0071505000100c3d540396100390b0750703050350074108400b0001c0c4650119180210550001c00300d5490041765050344040c0e02c90310419000d2464000c1c0312104200030500c1001080c090703591510000246c2005041c20440c9210042c1d0004040010040b03a00003442280d01200c500c81c40820000f40043c035007421910164041424088904c10220500360b02c40030404100c4d44100c400102c582103810110014140704000801c9500442c1003510240c1001411541040007210b0903003440e51140400ca03111034091081e241c1c3c050350f5a5120b03c4d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 833977949 1250 833976699 833976713
    0x3010e120414040f0e0313170a23010e0a0318060903020d150c020106050108011a0a081902070f0209060a0e0105120c030a300f080a0e070603240b0403 66
    0xa15a40d0007800410a400d00c4e41a50703040307a0310340a04890981c4009207403c030b000598400c9500500e240c5108140901c4a500300759181d1561b01c41c02040783c20b0740381c0307200f503890752050320b60b052a440c00700200403804040c205560741d074040030750542c04590215a2195054500b031400401d807402d075a201b042940c078603800e000344d038003c1070f600311101c81801040701242031841c0304100c1c11800d40d0340041001460312001402e10754068204801e0005410300650764260b20b0741c00c680602040e403800d01001d03522003070000c00c3c410310a2080031049000045c01d005000400c2da507039a030207008072490040780d203900c0108059000075118121080781404010003e0780303407424030805012001000c2e607003003001883c0003c1c1003100c1f00304101d80b0700307540501d1400c1c0c821032001d496800020201c04609c28a5280750090034404986985508000c0c412000800c02a039603000640005407200c101c0340c00503100c1d140900039010f410b500b16902001c0c581310640000d00c5003100411902134040c002e1401c0d0a54035111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 833979199 1250 833977949 833977979
    0x619210b16021e0c0301240f2d030b0103061506021c1b08030901061514070618151a010c1703060f030703060b030d080105031c1214010503010e1204 65
    0x8209010381c044c60000d0742c03000e0050343c0480e803c18406600340c0a0300f83c0d0080048000350052001040490300c180002c0d02042400300342c000986010b01c0d500d5028144951070210b16410080c04800f07040c00000400685130440e4600e9096401c0d42c1c8881c980f544000c9a035005107860840702c00c2c0507c1c9078100d400b4011281c0110b00d0504c5988400e189032580c4801043c1d40c03040d02d81640d181c0d56004108118403940e0040d8011214a24000e808541094640b50441c000d0b8500a80328640d031704c000d441d80e4801544e502c0790740b80e44403048541c1c107800e08013441c0c010500c1c1200026001c00304140210550300c55003603004801d9110b1781800c04845001c0d4000e2140e000284a180c11003514008842540e5003000140011885500d02080b165002018941000202c0703211400b481206001407065603008660701c4071210025004003112018200100c0c2d1046440201c0b1100c140781851107006841010161030503900280d0080c0030381d0040041c010f81c0d03085056001406070320248001e101c2c440048000e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 833980449 1250 833979199 833979253
    0xe040b16030b06040f0510140304110103060509040305190504081f060314060405101109040203041505011502070b071e1a0c1206040903080619210b1602 67
    0x380d400300b080200300140c2c030039002208044081102000302c1c2c906441c3e403a04d4004240342031410318042c07035100c50050202070b000401174034116180c1711142e44031303a108400a1900038480e9a6508240c14045d10b258000790703d111400c08200e4800510600580031a0100c0380300c2001005100c1c00c03411103103101404015a016195100c11000000c47c4801c40d0a035120101e050142c031444c00c140c5401494207440d4002d120126081c541c5030744400ea5904107482d05100f05503009a640e0b5118580f803400c0c0884074941d0001ca40c50000081145608015459502c1c8600e8080341d0040e500c1d01c41c041d06030f0082120081101c01c8091251861b5803c900c034100c80c5507c208460000c43c40305002180d400b00303084031000c0041e8800301d02c4a0002100c03660300754111005540c04c01c8150000d031001019101d004003024000c02d981c405450604940705d0741038000344107903d6440f030705404040c1d24205071380c010702c010740b4480781c6503021441310544021804403901c0d95030014280c041c40c41c3c400242940381e290b50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 833981699 1250 833980449 833980451
    0x1031e05191a04290c1b0c28050103020f0d0902010207080706021f1a0f060f0714010c17040b0c0403200a0f03051209030c0a060206040b010e040b1603 66
    0x800314900c8018149140900d20450004c070300864a030103002a100204109142c8100b000f00c1070044080041c42120302c6103082c03c00d00044d94886540061a203c03a000510380c0203070b1032500e070701c40c2a44464603803105002088907040400c1d075901e0044003070f800341240c4404119010445440c01e07150366442841424810b0042c0d131103855658243c103082080f40d6000c100941c00141000703156100d40c03d02d03848030720810f0f0030400c200e4101103c001028403600c10b40c103010b2034440d40008081e82d1010151200c1520f810f040641c2c0d40b0242c545807000e5500c10003045017642c06c00d03660141d4540112221310001e1002c0a031289a0364640d100d946005c40080c0c5104000c1c8400c02011000c0344111150521500710202645501c04140b410300860007a190b001c01e0041c000c0000900000e007000c41d0301c3c50400c0d21203c609448e8064900028201401444501c5c0d120362101c1000840b03d8011071954850341c058036001c0d01581e44c0356100c4650001c1200c0050424590000044005140c200b05078000320080c54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 833982949 1250 833981699 833981723
    0x8090a08040909260d06060504080d080703060b0a0c0b070905060708030402060d050115090506040602031b01061707030606150c03030e010e0706110f0c010f260f01031e0519 76
    0x2000b002e801413500c81d001881c43c0001340c00c1c07688440a01400f0005c1c5081d14010b4a0f01d864140b00c0ca031a0400c2d070300c41f10f0802800c0400b04920790f10a82202003d05040c003446903032140002400351202080c0d000c203d50482403c00080e440c00d01460300d0303008a42c0d0140c1414074080880c9c3e15044142c1c40100700720fa1100c0d040c040c56084081c24401c0764040e001d50520b104441d84105001f41030202c0c19404584100d10821003880010360220a60f0402410100300795a13404d054000c00b405402a0b40194000c9021118003440ea110005280b5080301c0c0112004c012040d140c507034100303840c05c0d00041400450050598400000e220b54490405041c0003c0002003146040502504000792503008400240d43c1c1c048207505154180072401c96044140010948100400b001034403290350013151300d06010780394408800148041858039003004010f00b80792410703c1d110286104409082c001030300c04840c0b50311154080d1000b0640c02c42c1254002000300420701d04c14125503203a0070800c40071a01440c0300d107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 833984199 1250 833982949 833982983
    0x6090c010c0b0a092013050c1e070227090304080606060306010e0405040b06102634090b0a020c1306170c03060906130b1b03150108090a08040909 64
    0x1142c01c240e05c2041c0b0740345622444501040113840014010407201040c43c2c9001c0c0301029040008594040c0d10350b40f5041083c090f074420821032405401c801940022a018008580d04a400300000c4a1070f016901c400c00c0e916482411581c9000d107009409450740b041021980525000026503840041450124074051a070800f00d001d407841940d00f11000c04142c024080300385040060120b42000d90714091180c881c11010030139060407040101301c510024039021414200c080403901d80702011040385000c001000c5010031104402030780c00f80300040c0d5150b20200302002e58104645820550303500910394a034242040000305a03d5034503940c401c540d2541e00050340e101031069080480600c0001e4000d001d03121090600b8000004d003c14240d4000404101140d800d0000300e00803580c200c1ba0001640c1d5515400200c07030100304101500501001c02008506841800d40c011102070a1b81c490300075071190f83d40315aa03a45a00c0d8002c080307000601c41480707030002917803040304558000c0c4174070a4000c043c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 833985449 1250 833984199 833984213
    0xa081009020c0c0307050105070c03060c2606012606120c040903030f0e0a0308041e0c0b220503030d0e0a0b0118180f082113030206090c010c0b0a09 65
    0xb0400b01c800b504010742d12085440c0a0205e00b00801c03080c01c00902c2c140ca10740e902c0902c1c000d0b50000905456a4442542c0e115210380340302c40d8010604c401d013411640b034407419005412811500c03070b40010040005020582d14000b41c404640c1e0610300c00c64001d0710f89000708421703020994900726940c4a0000020a40d81e602c2c000d442740140281c0740010000d049020b0750041c5c505101c0c02c10659440f588541c000254800c45c510b9001e5004256146080440e2001e92110001c00002a01409000d070001c10306c00c0c12400101b40244010b41c0d0140c8505442429641e0041b151007a171741e240e0820311044245000a07000b0071051030b0600142c0342e222000340c0d40c610407200700fa0080841103003030f140704501200440c0324000b81c050014003024855511541c0d203025070038880303e0041c8000340214550060050080c0c3d240105a010649506d00341f42003407079601520303000c0c2801d40041c4225000705100e004040360f1000c0f00401a0f480e007407031681c181c03546101481c0c05005001019a0751413140041942 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 833986699 1250 833985449 833985457
    0xf010c0503030a1401080c030c100c080a0306092315150a0306080708060103050307030e03010902090412021b13020c1204080a06110a0e09070306180603020a0e0c0a08100902 76
    0x40400107018001c0d002e181500000580181c0351b6907002c0c4401203442d9400081e0800301c894200c03510084111004011500c8808004000713080200c0466280f6100d50036411201c1900c0407400e041081c0c02c001c41c680209124180812541070380d01d2408107030b2540400c0d5030741c90040780180c100400301d03581c0d09803000141e00101480002a50304d94041c072035104144685402044145c009080e02d5045845650b1070b0b100e0000010280301c0600781c2c0d0440343d00c2c29001056000d030020030110a91610f400d020000040d01c800d80001405103100d074807010350b8103116002601401500380c0200c6440324640703900079406402030080c3e0f03124090351901418224030080001d00002e101920b0441420b140ca038040d9103401c0d01007400c1040501250034019803040341840c1d40003040b07894805544618400f0750082075517070800c06e585529004001e50a0f0810340180045900c2501c8254206a441d40301d000000e10903941d850741844100b0400203003038400e68101e40c019080c01c04a441d00c0da56003112204071380c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 833987949 1250 833986699 833986711
    0x30203130804080f0d0212040603020306041d010902040f0207150f0213170d03020301062f0a060b030d08060904060b0f060d09060c050c07050603040602040e0408070b010902090f0f010c050303 84
    0x4030840b09a41141c2c0b0600803400d00000c1c5e0f0005000d1480b200d18140b81070b0140380174603c20190b020000412641d0b0303942000901807458114410140710150700d540c040c110200060303000700d050100564140120f0310850781859040280030f07040c0c003400f41ca40741c040e1076030301640c00c0c030290207100720001d400005011000a2031909891041c007045400340604105001000d4000d140c410300c010414141c211110080300e140403d032803494a00580d0075924400b105448a42080c0316881120003007041a50140d003502404508446140c020031904646c0210301b100c6c001c0e040790409011800141c1d40b0740004a02e003800503c4032145490940c007051580d0040d030400c664264444050b01c003131040a200384c2000741094030300107142c0b594484001c0d43c2c4040c6031054502900000001509114096041e140036000a90403c141e500302403c2c4040b59401002c02524040704000000030300d204c1c0c43c03085508429000d000e44801641c0c030400c00400c6808003035040d06201c43d102961001800902c01148500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 833989199 1250 833987949 833987953
    0x12090503131701050601090b0a090b2703032506020f070b040b06090c0415141813151401021c05271806060706060603050a0c05070c0603020313080408 66
    0x1514000d44000900b6000c44450040d074034040074050b260343d001128071306440c43c01c10003541d20312904604555a01031540300b43c810a601003400114081c1c03406903616904011240d5100c004c03000400c0548900c50910711061405047c0c3e80440e002100c1d0800c00c003014050b0100604000314441080056030148604841082d40181040708010242110b5508603000b81c90403089441d20043c14162441180030b40b01400d1880d0300b50325600c81c886c42e41013460f007280140c0b07140c43c2c1500d0208443d82c01c0c1d814080c5c5116615042080ca003091080c443d07080e0840d80d10700300c0c81006151810070250b9403070070881141117001e00d00110b009055680c3c503812010900d50b858590b5080d4445912042d1a110005004072100c4180d44c0708290341c5000ca20720b400d0100601a0a558a401d00000c403184034040380100f10300c2c2002c8000440c1501580300c1449400300c2c4205016105410008072503605c0341c180010044010314500f405182e1080d8003642d13001c90f40da85090051000c83c0c03103a03401078005a0041d0091307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 833990449 1250 833989199 833989237
    0x304120c030312090f08090a05120c090f090304091802040c08010e0601030c08041104140a0203090c0108060612040606181e0c02190f08030415060506090604030312090503 75
    0x103602c001d91a07200d0f07004090411403d2041e84c1c8038484506503e101400c0520081010701d09551400c1038400202002800c0044001801040544508c0300410140c494200c0e640020300c64841c042040740300720302440255203010b0402410f4001054104506140340303009016140042e125841b905040c403039030f0303282c400d403640c5070004c2c008507140d00500060401d804c042031440c040d90059105600640d00c1204c071000705081902043c020a444c2400c00c801e001d4150038482881c0031540110f001c2d004010a41e1603290b4000c00541d15104c06694540d0402000c00000c030460b5034a03a00c041d040b5100354808120f5554550700d0724080b070107802e00c0d20f0a041c2da8a00811200d25000c01c1d80b1581a89080c1c00c1c003c1b01d0003420069207800028600001042c0d25005410030070103011880c42c03646030721150079501d030b080c94101441c13584164041d2542840c94210041220f02d03100e010f0700c218420050090749082e080d03580071100216690b4a41d4000c41d100d200c502c00080050001d40542c1c61001c0032a03440b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 833991699 1250 833990449 833990453
    0x501080f0c134716120810050102010b150711030303090106080106150c0b0403020c030d030506090f09031b072412050405191506090c0905011706010f020304120c03 72
    0x381c0c0c0b1011020001040740c01d40914200d0801c040381c108240c0e540518a841d05131070400104115225180240643d001251100c401e68000c90007a0051040041c1e41c840945c90703c00690880300e01c44039280d030144401c5100c8203c0d0302d541004110b803601c01c1212145030b460400119245030416588540d81c2d0b51110307020b004083e02403059200400d00006401c00081024002410703031205e040c4007400740e0784c400c000101814000c001e0102822070180884114002c1900d004008100039204907103d0420f01e40441c02516461001e01d00070116070b00a10310b40580b0030070030711a04c841424503c502d8040c40c1c000140116402800605139072f035550981e1842c407a101d200415044c50441d100e4a498644424813011800004807100b6005882c0d001001c1b10180e170401ea4103c140010f4000d424078240b401c04200a20141c0000081c0304054a44c03174902034840006480d02c0b00020380300001003540c2e5001404640c810902090103012a0051b00c2c40c1584414401c100d015a412003074404100301b07041001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 833992805 1106 833991699 833991749
    0x130605130e01060c0b010501020a021005180909070e060303031501120f0f1e020901080a1a100504150c030c031404050307030c090c090501080f0c13 65
    0x120660751560024440c1a0110017251405004400061254000620412083c3d40207003d02c54180000d98110307074035008200c60030074220f01062001c2d0706403501003d06000b6450000600300c01c40c208030501e20b6072034004d0b102ca4041d900800401403058190703032240300074100900e045400b010071013550201801c814075031494461315245000c6160603065000002c207410142845140c0c2240d41d811b1400c034090721a500e404244403400291170070802e1750108054100501c03d05071070204900c046017a030140e405c0a2004620005800d000910f42071202040c40d03001480c10a00741c460542c1e0017803154016000c024280014104600b8500360600c091f60003901e0f019085500c100d6981c1005500c1802510840e50240e180000611005115184030b80a0740ca040c1c44031150382e1502402d600c92034000034840411100d00f03020519070b00102c0300e9800002c02207014141e08550b80421128 = true := by decide +kernel

theorem cover : BRFrame.Cov 833812949 833992805 := by
  have h0 := BRFrame.cov_init 833812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 833812949 ≤ n) (h2 : n < 833992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
