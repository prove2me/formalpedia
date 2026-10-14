-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0731
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:28:06.677988+00:00
-- url     : https://prove2.me/submissions/e04b6d95-3703-4181-9579-33531bdf5b57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 131294964 ≤ n < 131474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 131296214 1250 131294964 131294983
    0x1f2a0903110609030303070c030c021003060305010f06150509210f06010603051306050717010602060105010219120f0908070b090405090105060f010819021306110607020a06021e070302 81
    0x2404514072103140c20a024860203040c15458059200b00040354010740075180f1400c0d002c0c4a0f01c0c05440b941d030154042016039075503100c040042074031440240100f00e020b0203444001000e0103810000c1c0d0f490700d000c104040006d10f03560800d01c0310024194240b0303150340d805110000b800c1050165003903003004681e5a2848681d140c42c105014641c004200d080c824040c440c0651000d1401a11802c00ca13100d17500180805840c03841405140310014601e2902c1f401e14500804064001d04420749c500000a07081001020050000700c442c00005c40c0054a0003e0240c0180c40919240111404480080e0391820325038002c00040c2c82000000030380007851100800c4003034010b40701031002d41c03a040c61b0b0341e081c1d81040c1d0b20f040c2d003c0c100315811449948a5610141d102250610f099000300a044445040768065840364120307050041c2e090001c503400c440d0b0083c0108044001b0425450079603402511001c0715000188560f03000500401404000c4017030303400308800301075420741c1c03403200b1301e0060b54951052 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 131297464 1250 131296214 131296223
    0x1201020f03010f080c100512060f03061503010501080a0201050f0a030e0f0a03090f030203031602010e1003090c0803040f0b071109130c080706050d05090102071e0605091f2a0903 78
    0x240800c0c174450901e0140140c5c0a64181c4805040c0b02c03d00300c4805c1c000740010000f940040c4a400032203020b0764200300c0f0500034280840c24203000c0070f1102c14182134500c16000382c0f08036030285801c9030043c0d0744101181d0020265072000c54540c6044201200504034203c0074188501c5161030707220b40c0703420104941030403511136240c0c071800316503810781ca01150640e403002030340c560018804881d03001003190305041920300c14036041c20306d0401403000890008190540b0700c001b0360b4840c8101304020003103105101420040000354186850402d0300c1c55100040e0049400521010130403200304084580d03a0a51040c00916960703a5250416034441400c10f40c0c030007510202840c0c4800104038a021a0708800c1d1181c9955039442e12040701e05c0c00010b010080d080e0300140d0b5007006200041155100305000c03481c081c4504034011041070400304152071000c1c2540c3c08540200700304100c42e99540004041031400341c1400301c0d41c0d0038074140d401c524800ea86010035a024420918003c460780c004034030310030b40340b00717 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 131298714 1250 131297464 131297473
    0x412140f030a1b0810061e0309240606090e1302120f1b01020c0d08180d06110c16080706110120090102010e0a0807110303130e04140c0a051201020f03010f08 69
    0x29950200c03a10441e001d591f485034421565034089841c42604404801401007503050070380c0c0452003008860182e107404405901e0341d5080c00340314569111402a00a01d250a80e15206041c0a04a220200c0802800a10800304144081101401072203807040e1320302590305607400e0000502004040505070040c41d4014041c140081000b46402450b5410081e0000e203054100410700742c0668441400c007008652025290f803807040002c8081c0140b5242c5140100d000b501c441d01c4402851505031080301c008980d5031702070383c00e01507442c001590702d0465100d403412110903002403040600500810504000c01081c0302c6882c48071045080041c101e00c0002c0c3d000704183c0e40d11700100780d10f8154420008000080c20864807020a660940e100110b44000b0f007034a103000386001c481c4401c844142d118000c032144600411080c0101c080d041101000d51402500021102000141121015003d840d02c1100d2104c04c07110700c1c8000354183c81e45035030201d0320a607413541c40300e600c000c510300301c1c2c80781c40c03c50b124 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 131299964 1250 131298714 131298719
    0x7080319090503160b0f071e060b09010e0f0c09040207030f0e0607050c09060105091c020405010f050d141e0606040c0203090a06030b0312030a050412140f030a1b0810 73
    0x7000200400c40050480d04d0b51115030800c604040b42e5480b505190942080130f00c0400040303203214105a8450240035146400c2c9102c0e85422426a000420340c1841070041c031004000b200301c07207101030b41d000d080107a10088170b0b82c694441e044035006500c0740b1a042031000c100c0508054000480340c07034030302c4c1c2da440b41a21504040104042440380450040103074124505449850400c05015034003c5014180035040c07030a4007008c02c40700b546958401c000700c1d8100703c00c0300030b6050030720a007805000d0518121000e5403e040102d00458502074004001c2c20440a840d1980c0d0030030321003d00700740203010201007000030754a4216038452007692101d204070700d400403602c0e0302c1e8000011104030b29006441c4003800b0b85041c40a9000301040c0100503054090b0b2a408035420150f44021403003000c0407140010a41407a040008104010501d90001d01c4441c884031f084403480b51040e1910b43c00e441040c42da176503851100c031001500b0324081405800307000c2e1094110f11500300342031070301c10314855040c41c10083c4d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 131301214 1250 131299964 131299969
    0x3140109021e06040915091e050114060306010503040317090d110601210c0306050f071d010827070306020a0219030e100e0306100f0503030702060306040e070803190905 74
    0x300c2e0340d80d004a0400c810460300d0f42681000c008490b040070030001c050b030303514039900503109402c1c11940c0c1052141080503c01200f4071803a409403642642d001e070400e501c000415400e01c401740c0101d040c810080005010144210103000001340071414159080c242040d4560781c2d2040ea0049102040c00303500d9130611b018002070000d0480d541a00300841d88458503ca0602c2c0100395481134030484c8100c00301001140c40c034080e0500031508121131120f185044040204071510b1b2400ca0110741c0141c42983d460360381c0c418a4280c0000d26500e60b814101c00500800c946035142050340c10035401071a00000030700c00c45a0141403016856000e5504100712040c0c1c05e201d1703411103c07008000c501040320352000c07400d00f40d006400d165000d0401904441c0f0290000c0e2a1620440d0301c50305a80751088103105660ba0034004000911060740103504003a4194001480d6010003400c8500481c0d55800c010082d1800304803280080640c0ca080d2540d40c8001c1c802c1070f121070039664000700410031a820025050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 131302464 1250 131301214 131301259
    0x2030d120605090c070212030c01020c06040c050910090b0310060b04060905060307120209040b0301091103010606020f060c16020a0b040305160b0a1220040e010506130e100314010902 80
    0x1d5101d01c841034175041c003036800c1100122400c1c0440754144414171084201c46002d02c000c007400c80604005009610f014680303c07000300201c1d013016001d40304035814000110620807280c0141c5002802c00b00724100140701113460300a81d695004115410300300c00241c04181000144140e42140e55000a51500e070b005000d00342c4000d480040c009500581c0e210603150311a03024001940d401403002c1500c400d500c0020303081d120b010905580102d12440600c01a10f000d2003010003c2000d40058005c0042d00017401391641d000034200511404001003080240020490100030b455004290321081c0c0d0b00c82c140d174030781c1da00540002c907180d108000f400c01500181c191402c080340c0c00345c12402d1404160303076000c495442c41d130310314220388036190060300000c0380b06210b842c403511701c2c1444002d031950710f484a0300000340f4040c0d02040c01181d08011074004080d02c40070601c141c403c03201e6a00c000717403a401c1900c80008900e90024061183d5815901800300c1e06402c801c4440303008503090428446092601d5100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 131303714 1250 131302464 131302471
    0x240406051c0603080d05130204090b0f101215110f0712020601121112011b0e0d02030303040b070e0301020a030207030e030c01091e030803070c17030c0a1b02030d12060509 75
    0x4e001c144000340c00407115401c00d0ba405a1128800c80302000369a003c1416607841c05400c4525140c0e140420600e1706082a81c0b80d4084c1425100f140301e01d10380704004111141998000d405084c200d0f008400b504010317000f40e00342c24002d207130b80ca0391891903513107982d1140c200c000101c2c0d480108142403180b6501c0012114140e40008540748100c40d80c0d5035660307154042c40d42000d8bc108138004400b003044842840340c032001000303500c500c130079400c401e590040a81150487c0c903441014072941035800b50714000281c950080d0b11410340881c948030b00c107007960b500039000142c907455070000a90080c0d03030f64940c02a046592007529081907008800f020903455014040f143da0008000c19130400550380c0b8596540241802102d90b004007075200e8440d1401c580c0101c1d20400400e11018001040200ca420300074080c04402540c1411414050710f001468416000c80c0401c001c4040e2200300740541e100c01030703003a255006040ba144003186000182007203041e201c0c4074003014a010800070385410b01c1d90f000c1d4403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 131304964 1250 131303714 131303723
    0x7080d05030f1f0902181c02010309081603180b031308160203031b0d0507080313020f0607060f0b010903020d060c030209060301030804030210110606240406051c0603 73
    0x35540c5900b194001c00c24020480c0e10002100001800d0040c110b201000141c01e1805016030f03503880c0b10a80080384d101d0348104c58021980300c801000303440100c02113810482e50919004c180001d40d400c04072454040d440c0103860840764124224200758200b01038201c685256064070441c03c0d40c4030100f21040c0000c440000700110b12007030901c0081c1d104030040460352049407032038980b85201e0300802d145810443c2002854540d9250740c0b11075038000c000d19424800203107421890306000d9074410b00300e1f010150086280e810038540d07250440d03440c080d845272961340182c02e07207448520074200030000d44600b00c00700d61260f24000c1e607450700754824200f0000703407030300039017610004407140d503c86005241310781084042550900608200c2c0c1c0e1010001c40c001c1d4055092691524254010440c000c0144100301c818010b00e01140400c1040c0402c0182d03100100702c1d0801104940307445115a045089104a0400b400004010840682200141c4030070040d05034283e510101c0903810b0320444030140805030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 131306214 1250 131304964 131304967
    0x110a02070503010f020307020c0f1306140f030601080a060b060d020d050703050601080112030818011815090201090302040209010207080d03020703110a050307120e03070608010504050a050c250c03060603030207080d05 95
    0x50b41c80c10400b80cac010580f040500624160703440e5800d000300b110065041462172002110046a8510700480152000c10048001d04815498540819524440aa0003c01d8a9100e83c17026030107035608403d880c0c5011124405654400145071428000c00c1d0031200348000c42d1808000c65035a501c1140014161400680314407551801502d080d101c0d018014400e0300d003007103142c41d01003070b1081c20b00030003d8900301ca600d000e43c0d0342c2c1585010103045805d01c100c01c0c6580c0c07410ba240700140c0e0303104200e40200c82c3c054800694070030301d0381d0040b41800d0f143c0d0480c410074410300c1001840300781d059004100c6c090203079603210300120450a1007903c58842e803130068507030f500500c581e43c003043c906028070005042506100194900090102e400c01c6550b0f0b00035804120150010446801c2c2030080d81c0c2c4c064502441080189814101d01650b801101d100520000317010800011074803074280350326541030b08500359544031039413454440058529800120010301030300200050480e00040d10740290021502d945 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 131307464 1250 131306214 131306233
    0xd0507030e011512060b030d0503061f0212220e0105150f07111f05040e06010206040c031205070f0804090b01050c100c0c080304030f03050c09091504110a02070503010f02030702 78
    0x703048070201300800c0c2c0f0032903528490103800e03903001c110480c1707101e4142d11599200c0c6081810016420261612504180001400380c0d290fa540866803d410005410805031120401030b9070f94186541e16070401241092680b01251791074000341e016040710011510395170031120302946000b103070082402c01c06440b00240700401c00100214030301a00483e0107000b074202c9000c001d042d080f02c1122141500003151000070180a40b4010b0148140d1144082c0000d0025041c56034401c210f0701d41502c009440348034000441d4203440c1c8503c00710b5001c913802080e0102c0600c03250601440e241e0080c800c070300700c6a2504400c0a610350141094503960300116020346203c1001c4034a40f8041c115501981c42007050602e000300000c0c441030042c50180d070007541c42d55082d1510b01005001c07103070b002d0088105c55509002074078455a48003020380d40704070a22490300315941c01201107030180c2918030981c145588082a0203d1059000440404a0703800310003c2c0507808c24880054220320080da00c140058000407100b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 131308714 1250 131307464 131307479
    0xd1a0c07020a03060e1c0e01030509010f020a021501140105040e060d08030903070b1810020c24100911040308091302031e010e0c0319060b0d0507030e0115 68
    0x195021461426161408016030700003020642260411683d40f985c1c1d9500ca5140c2408001c4250f403c61404203102c0b040845a001500300c0c402404510304141d182e0000408400e002c1d0001e03145030540341029911070b41c815401a4031203040f603801003115181c14000294070b111120300012038074030684910346028204042190b840c44001e080c2600071a000300c8280000d64002c005610034203048001e50b490b1074944c5440605804080c3c40080c83d08003020f40781e44071440100c0c0840300001d110f0001a51840c94540c007c0c108900c00c200c142c018106249103e045001205100e480707454100d143d40400ca45a24185013143c441000402c0b503000280000d1000881c41d20007807028101c010080b040002c00c112001081c0d92080390311010004504140d102440310380c4506074003610070003030124028034150302c1c4806503010003480a0200b0580740388500c583c007210780c040c0000d0684840c140e41d07503901403103070803000c1e000c207403040400240343c100c806903445010720505040c0408600302c22611850003d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 131309964 1250 131308714 131308763
    0x12050919120203040f090905011802011e0c02090709061403011a0a0e0a0305030d0e0f0a0b0627060909030901090b030c040803130e060316051017071d0d 67
    0x401c102503210801c070114100403120510802401d0741d07078000c544901c2030b1a1150a4074030760305204481c50417000c08800142e0b00170320301c1c1310f00c458500b000903c2d0311b5400d001202d0030302c05c070036010303400120702014402c0700c0d58481404003c0d070711640c0700d40c0100075040203e40800d100c01d200392420744269149810800840b88010680f011032032070062a903251284c000386450a04d9441104e4a510004070040700031064001e82d4030003403c0e0700241805d001d0714030290381c171030110f05402001014500300080041c0c1e16903440074211071240015610120151040005021059541a2103995014002801035000104803000f048060351600101403625141d1101600003030300b11856048148070216402c40100b015000b00000000d94401c401d00d06107107184d080c180544064000d80140511442c0010403d81403003c0318809d46100c0302d50a60204121580c2d50f000400392410000001131011455000b07001104440c21007130502c807039065030b13020090640c1004000400c00b1040ca01c1c2114038054805 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 131311214 1250 131309964 131309993
    0x60306010807050415080303100501020c0d080d020d06080a05070303090e090a1101030e030f070204110c0d0e040b0405090a0302060a0c17060402040b070305130509010b0301050402220612050919 85
    0x10328045e40641c0703407100103003103800c21036091701d40762103441d0100119a410000c52462500940e01045003100507110110340b4070a50281241064000800041d0181250704c0b8500070200c8a098600c49411403170141e03100e403107503c03080d40000c0b10241b010400c006a05039003401510303808010720840d04155a61041003101081c0c2505041e6140c581c146201020310042505119270b5907001e035189a180704010440d5083d501c9001000c40605c1559840300001604106914a0f410804444100322001030b010300304520740103800c80e08040603c0500180001c0094600d446502629107554071810f0600440c0d28401032900002d141d0008210007000020f1140e40041000c1c2000d40f03495101c41104202c4d07403110000b02e0016100144000b110a0001801005031808844c00300503545481c050401600060080c603210310740c0000c124800680801c0d04210b1061000e03c920012a80c920b80904200010012450185e0a160000d80500000b040e64000241d0b6040c1900c9284450b446a9144003900c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 131312464 1250 131311214 131311241
    0x30f040c030210020717061e0c070807060c0f32070b0c0408100b03060406020913050106020106180608120f0d050a060f0602010c0c03111f0b04050603060108070504 72
    0x3040c003101588070070300c03082095415a001010214940446c05951005ca0f0341c0703510858000e14184081c084100d5400c491166558181d100144c90b00101d11405118101c40180744010009195041000c1604240010746031030311030300d0002d1203042091b14529103195804040b05d8404030502c03400b054811844002072044000c3c0350402a044d80e0780c1c9025030065075040c2c8508404901004a80405c201541d66000c00003414090006040082682c1d120702500003040c4131307004158014603031529a010040c111020406000c103507035402c40030f03001f00b03c28090b02600b080c100302d2401d00c2c060345024800c04c1307400b900010215440d10403000401504090549030100c5810040c02001c20214040d980c060011444009080341ca4040701404811150f8005000c1d64108400e0049032500711800290301070301414201500d8118140050902031302a0803041403024245c0a6411400e4907881400c940b03070f05a0781002541c40e44810565961401d100f03881c540e40c03100c481070105c0c5c01e02d5000345444490b00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 131313714 1250 131312464 131312483
    0x203090c060c0304080606060a210e0a0303050106032d0902011b03090510031b0804020303210f060a08060112081603080a11091c1104060b071214030f04 67
    0x16a000a44030361045a18800580c00032400344040c0e407040c0403541d00907e00b107580c54a0f0480d03508024044010030201d50007244020010306019011a03000711040c4003011007030300c1100100380750140091000b801901d00007450700c0d56104030740c1005000212261651107072a084258400018400f034012100300300e0401c4903d040c0c1c1f030782d280d90400308044460310a80700d03c0c2c0c09030304182c01d014801f0401c0414038101820001d03c11030710b1201d05448450202c907450500840d0351140082440c52103808810302c100303140c01140c0340742c507a008400140620f0865000c500b260300c03a501040400341580c0903000c2c00e03801c0b28004014458030303c014007075014030465000e403c00c80c05004840f80c407001c401081e400700d4107000400c40702c2c11a074816080035401c41c0104608090031000400c80c01030125886141c05034883c030f030540503c5440030f030501c0c4000d00184140400c079142d41042e03c194010050469601c03900c6200413042c280114215a580c0740d9804407181180d13541001d0281c40c40c40500300b130340c0c0d003200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 131314964 1250 131313714 131313733
    0x1020a020d0c170a0302010b0102150f060d05060c0408121207180b0f03090d0305090606060a030e010203010f0312020a0803130f020315071b0f030f1707090512060f0109020309 77
    0x42a100c2c042452612405400ca1303201604003e420340d01101001c5045400c0220007440c03040131040c50701d410015102d001e00e1140d50b0709005ca08200c03505500030f00310744900d00400454540c0417000340295107510303007030b00d0035003455610f0002940540d90101d201c450850780050a42407103020750740e031001c60303005240c10b031541d41e071000740280c0c0c2c888001c824044500000300404207008120080d41016646030030081490001c6103251034500107000180318071000514480c1103031280d04400d1550a140008640e80e5035181d0644010b001c50344822a0549120030041c440580080b400404c0d00d034102c51220702e0b40d41c50004800d000070920108503200c103183e42e208000f68504102d4041405a4030101c1c2a403800c02240141201c014443c8100015502c1c00d0018001401c070074002d01141d80c9418500e40b541b504182c16210b069005006840790368403841001001980888440d0403128240ca182c09500c840c013400c140c80d50021540281e680e0180c0e001000a518154000c40e404849042550b15114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 131316214 1250 131314964 131314979
    0xf1602100e01020d0507081302060f09031504020312040806012106020a0206040209090d05340506010303080109050c09010f02030d06090e06060f010f030507090f15170601020a020d0c 80
    0x1c44040d842940d680d03010640c2c1041940c00c5c4205a0050f07828203280c010b51900042801c580101030350020f010389804501c41441e405071380241e036034041004083d2081c58668040002c130804c02280c05900c280f181103414015966000c0c11141a0b81307044028120304c0e820700b00012040c00303400321200d0b607040305401315101003582d600c054603403844598040c143d1401c203030041207480c480140203551150070449c0034280c0580c1180c11501125004581c0c064840810200c1c4618140340001c107120358414030300800200080071a502e03041c0c034460344449280366241d8504000700d0b6400c980505105c1c1007046446000d602982d6941001c046030304c12a441c20075000c2c504010340320340d82d020480d410b840c0c0d001c00d8080d5205109a82d0301040c00c0e04c2c08102019100002031260018000c21418150b86601059070076205d0202c00c40a80310351480d008149940c0e0403c110145040494a800600616122244c00040010702d90040300160b00802c447c030065001c10030b1400d808070048540b660b1000c1c2c00034144 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 131317464 1250 131316214 131316221
    0x1e050f01090908041a09100e0303040608060f03030406020a03031a01090b09040e1006090605040c08010605280e0909010b0a1503020408010507020a1205070f060906140c0d11030f160210 81
    0x1405c0381651651503031790f4401402040040201c050f0280003054205511980b000001c4d0340494019140c03031040c83d120480403421a4052020302c90b054040001c003c94825000034189141a00c660790030040980000840002849010140e41c0010750300b4004100e102580c81c05490301e10301c002c10015011800090b030382c0c90080310388031403451643c40300310412210f4407612602c4010502600d050080c1d00000178000c0c0401c0c4140154024000003103207140c40c0440383c00c500310322800d51500c1210f40d030f40100800b0707090b4800c050800d8403400c048400070b91081018050700f282c802d0092b00c000d107603a042c0179195440d04c1941d900002055802c1c0310000e03800101b40101d038040d00d036a4018001d440514204641c0882002d400601401420080e000001e854500608003154120400048100711440e100000d080208041d40d01548100284a100d50f444802842d041c01c4080c410441b10300c400001e0021800100e0314215600303281d80c000348101c00c25000c0f1181c414042c0c4180c8200c6542c500d0101d084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 131318714 1250 131317464 131317499
    0x902040b0a0e10060203130501180b12061e01020703020f061e0702040c090b190507060207320604110a03080418050c250c0906091e050f0109090804 65
    0x900042d00288220840d5248803940901900d1010758900601c11502405642d424800c260400440c0c24800780071100302c0d9040f501030f2010b0301c140d030ba60701a042000c00206105480482c455508a800c0042c200c94200a00c0c1d070f4020107801400c1e00510b55001c002d44020640540d0340c11902c10420706000c030781a40419200d84200c14806a110b84044c01030104850f000c148000c03d1151201060041030548000c0d116090142e00c203200e44102010b5088406000310040200380324000310f10305040000039500d803401c02c4440d00c50344a0801e4105004040c40c0303582c001044458108802140100d407040b40c04803030a00d070117040c41c62480d946e652654070982c0f10354130216440303540c81c0d041000000ca50140039002280d01d44003500342110704c070340103911424214400a100044406803c2041410b0190200402c480d1104020140d03545200c900904032403c0c5d894010160b005100c54068042e1240d680268001d260041d0140e0804070035030014680d104040e2101d8009010000b503400641210403030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 131319964 1250 131318714 131318729
    0x60b06070302010608010e03130b030606070c180c020105071710120f0302100c1b0c0902030106020f01240e190c11061510120902100512071b060902040b0a 68
    0x131340da480c00304118210b442c076130500c1515400400c49144a044c0e0309200d4400d13110a00b4403076951343c5650000417814803820b00000c0921035407007800100844041c104500c100c04104040c4060b5030818001c074225541102c5050215105181d40e501c80040134910640c80b110740c4840300399180e21907490341140180310703c08440c0c40034110303400410554140100456408114020305c0700b41703000c0c080681244001c09801c854207020704060750a2151416000008203281c0c14110356035611128000c3d1914100c0f0351900741503081240700c559482a0500302c0a038284151901042281044c1f130042c42003401070440781c420b0070503180c0008400032602c24001d40c911181c0380c402c0b01d030010040385410b182c001800c0d4008101000c410202d41d480309804aa00014249898004212090b20b603c004001c41c4e0000f039000066203015100560700301005140c500440f01d982000e90740da26404440902000035480200799102d045a00010061b03001981e9030391006001103070020740701c0302084101d2500c0e4002d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 131321214 1250 131319964 131319971
    0x20409020409051803120f092109010f02030c0304090e07090c03090204050a020307081512060a140f040302030a050d021204110f01050f12151002070f170604020d060b0607030201 78
    0x8203080c145013240c00c10100c00a1801c0030181b240d00021700314024001d84c1080c80c40e00025607282030038000c4c0c2c41042140c0910410310801140400400e03000500c645021400900c0b00170303240c50002080e1110b018041c0010351504d420318850720701800a50b004040349126101021540b80c0c3c150091a880480300d0350005108110f41c0104816550050400c01c0301c248100180071001e940000703580d84c40f107a01d040711040340c0346410204000060518803000709018034400d0040700319150300401014a4101710283c1c2c1038664441910301002c040e03e005015074002c01180c096a8000c00c0600440c0c030042c3c0006050403107400e100c00c2410800c0785c00701c43c01a0f40442000c43d41c54650b600c03910a010038a001418600c45100204551285d001e182c802102034000041001b081c54110fa201e0000282c44d00700401c048890103540d828440c000c00c40300800300720740801d0308011007031844e41d851044001031002c0c5d11281c090242103041c5040988801e034440da0340b6507817510f45000621540e4401d50000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 131322464 1250 131321214 131321221
    0x12030201061d090106090203150f12070e0a0c020c061207030f09080a0f0504061205060f0607080309150c04060f0c060219170402100f0203090a0311010e030d020d030207030302040902040905 83
    0xc0c00c4403040e0b0085000a0b20500c18402d440e46009c10f030030b09052054075140074210740d03040000c0201c0c0300401c010085105134140452013141102c0814054005010140032810128000380e80b900c0034610b527607401603005c1c4051840c800007101c3d8240c106006080002d04042850150425150302071401d132051040045d809030305a6000c4141444005d081c54218245400c043c4000c0c007003003101c803180300380c1621403012a40d283d0756255420311740c0a000300101d41e20005484c00803815041110754003c00c0c012850b5148007410b006021509c10b01c5260011441c8c0341c1002015220a00d5141e406000c000f000011a0005815071005000841c01340380300c50f11031003c18500400e03080710705003e6030425449105010045c0c0703c000795400405140e0401c03084240102c03030300b2451030081d45440c590007040800d0010a00c03a0f04100074050300720130b80e9449498100c1d1020b0554800280300c0442c0142d0044160182092090703000c1c02c0064424074000d880c01e55104444020303a00f0030b0b00002c45c06d56442051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 131323714 1250 131322464 131322481
    0x204150906020618060601050702040b0d0f02150703080f040f0c170c0a032013050f040308070813021210020d05090705100206010302090606040806090c01020c01031512030201061d 79
    0x401c0c0d0018141658a110b80d500042d04da8440c0c1c4094042410b0040100d40d540c11503990360082c046402001d400c141c07040340541040560710340101e0301079001f114000c17460401001c05008654209030982c651581d541c0307070708220a000381c0e402402555108401c1c9030b03000004034139001e090024284041e0300e0308500354400c1051308142d4284003251284003002402c100058403203c00102e041480d103a00c0803d145001c002c12401c60000e44182c944502e40f904000055215100c480e00440c029075800300180d40304942500d8800043d29001c40007041201000011f10741080c803c0c52040c2e0a205441c24401c1c00500c407400d0b60400480c0144d036984460411008100802550004120441d40c11008041a41d80651202c0040c00003034010f90342000011080d03140c24007114010103a940403103d980ca00600c0054460b40b05404040c0140555810090b0341e6209000e0302c0c040e40d160101d9a02c066142207420b00004841101c04c805554175817070001140f03201c54240700000d26507100e0208075468040349 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 131324964 1250 131323714 131323723
    0x90b0601110a0b061207050319060f0908090d0201050d1a090c120411030703120309150608030d0902030a0b0421030515120705030304090b090c04120305070303020415090602 76
    0x4034a4902d91108400002090415000a402020607900d22040c1d010105403a4140300c201e80007281c0500c500f0f01010a039055040020861034000c010030042907195100314400c3e104803503000303000c96030240075a6150340386c08401030340040d10504229150070000f4010701d06440c01c1401c509021041c3c00300421030341c10443c881c41d6120149140c0070781340500e00c581e07450300420043e1024200300348080143c541900c0411031080907640000c0c0051600c0c000c8140200901035070001140c48681c80ca940c4049017880303004580a640c1e00700c01030750510704c5c41e040c003c004040c0194141e1389807061035440c50100d080908081c0c010f90083d080c5955038a09220002254110031600400b05032078030042194080050b00300850085088031f1980004038081c500301c0c544902500810b5060000140002d81744e0340307551095501180a440507043d0f550b9801004c40e0a000d21321508150250b240c14074000640b0613801814000e119080050401e519000c40c98403441080c04a0700114007004018010390b83c0400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 131326214 1250 131324964 131324987
    0x5070203150702030715060503070b0c0118020312070206040308121806090601060c143012010920040305061b070203070b0d0207060e0303040c0602030c030922090b0601 74
    0xd00040c118100b5a070002e6891041e144041c10000301c40184210181c12a00303d4401808010201c4851a44034008100240d12914442d80079628014130466200c0c0491040380131150010b0190213a80c00402454101e075001003070803a44600b0030000030000130b0441010f4907130a07d8070f44d84510340740303441c4041610342c0300d600806800315401041005840c0400182c501d054401034a8251007503100d038500b00c1e1445080c01300000007401180c80212010314180a07051420440c840344580701250840e141841c1d1040c1881c00300c0b42c0c200c540047c0203041141c1c000c4081ca6080072452002d0301e4040c1c4031254141c0003900129811740009003404584103e82007481001040c00d20101d11b025110341c00256194520f1040c0344134081d02180c0484440d0940d8162a00d030344c2c021000307014040e2141012902da6004031802c440b189410800400c1c602e02c000180c8800003406030040d072500c0185000c01045091814009a80c400c15001d00110002b0f42e0065210181c0725034550b01c01401e005001411422007134 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 131327464 1250 131326214 131326243
    0x503060907030f020f040b060d050603011505010c1101020f15040201031413030e0f0a0e160504060f050f0702041817030907060804050a240606050901050405010f1205010605070203 79
    0x2481840483c100082c40c200895048401045404030a008140a010301d0626654400000b0800c901c4100390b6401961103038038105d001304407401d002440100c0350100380c00b909002440f11000180041c0340407603001000041401203504a40c4011031140ca01020401401072010004050008558060144102000803150b158140703103441076070860350700b09030b501c040c080181403818400030380c0f506c208038540383c480030f00030180850310358990618108080c5c80c03404c918009032507040060351290080d01c0545031036603200080140305510480b240c0d000281000320641d0200300700710050ba214441c40520f510440c0d5000030440303181c10a5114081c0c06146951702030004c20400400503070204820050707400e107040c802c285489a0401c1890a25050801441c030b00800c01d40713034400301c1c8440748041003669001c001e00507141c89450448842c0109004e09001c540140402c0c0125070141c880060a0001803a181102021140004060b90401e074003440208400083c0c000541c1800d101400208802d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 131328714 1250 131327464 131327473
    0x100b010504051008040609020a0f0f050910051e09071101050603150a09170c0303040212010207050d0c050307051002041d060a03080318060a05072c121906020405030609 74
    0x5280c003060f07039803058640719000c000781200060100029584510300250700135255101984d22050300d034020758202e024802040c0981a0000345520300102154403580103000700c03a503050714260034403821101d04203804000401010111010382c40d0052190f21400d0f60f551032545c00c2c030800d02140e08441024203880c0c001d03009960022003200341d204d00c9030f03000f2142103030004081a40303040075503039041160314040385e641000641c5203c26000002443c055030003203800d0345034042d1a01000b0300b02d10031408000e1050b0001040454401c0c00703040680c410b079000320240c910b458510398503c1d081012400701e01c1841540402c06001011007803824034142c428056a03204a414120f0000d280000300d803000500400001000071902d220001c40e4030f900704c000c2d03c00ca1b0514100151a500540400c403039440000305074031140c4800114002001d044020307151452200c4422400500c0300f0042284000303a00ca2141c8500040c085603403032000c5030180d0103030b000140c5071410001050308110001d03281c0c003800e500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 131329964 1250 131328714 131328719
    0x60c071205100b120d0503090a0602040e0402090f010305060a020915030906010e0a06080304120812070f1b030e010807030605100203070b090c01080a090f060f021803070614030a09020a0602100b010504 88
    0x41405c0078904c0c1d410055103030b40c0e6000307201d403400301c0200000304914008500002c504d400c141d46507004510032140d17100c80c4d5560461800307400b0f40174440504203600c8480030441d5901d095001b4800e0001c09003140c07103484070511840c0341e81e500c156041c541603441030004102070b010b03d0003102c0c3c02000d48581480410301c1c0c0505140d480c001c9000b10030001e441c2c03601c548100200b8030708039060008058440d41851515400103440304a1040e9080041034100f5182d41481486010884a043d410344a4804505c000f42c01169000d400605000c14140d8520740856595100244e1003c910f030780d07038001e43e03841b8058501544a028060011442e560041016200c281e812005890f40410321080015090071107080101e200040088082d154030b2078030640c00b10300c8030780303400809440180700010035180201754140740d5152194130541002030380c984034003060741001c10000c5800c01e43c100c40c0070894510079000103800b1440c41c2e00c80e0016901282c181e454502d124095803012a2003400d01606291 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 131331214 1250 131329964 131329999
    0x40f120c140d0b150a1d1003030c080a030b060417010b030705010f08040615061d090601050301050409052d1c080406020a0215042406050f060c071205100b 68
    0x200140e42c002c140e03481443c0020064050103d0640c0d9801008044076102540d806424180354000303589000b402a184001403032400d01003482d0310823aa0316945a540059650304c5003074903500314a045200305501c0c0c03c041d440d0340d030b034185c0644054640720300000302c010106035016084030130010509010f40c0040c00d04109a0f81c0120b40d8045078000ca05022005a40c0e0b450004010040c41d6610a0114501d02c1c000c0b80d00b40e8080451100318100031049000d00c1c078400100030385e0700e4085a89500040c01000140010b0500342c0240e0300461140048584104583c00c8a1742e07000c0201844106442e415001d5500844042100c003611024070301044a03038200190005100460061000d004070360001a41c5405601c03c00441180c1d415040c1524038a09240ca0412194041c0d1451060340e010b000301c070f2011500c0030b40705900840d003004200c3c0103264440c006002072038022035a40ba18601450400003080b2004641810456204002424040201010b540100c6030f00554590107407244009186100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 131332464 1250 131331214 131331229
    0x90d12030632010c050f0109110a0b07051f11160b16020a061112070906180807050d050a0206030703020903070f14011d130e010c0f020307080304020105040f120c14 72
    0x280b0038a40722200c1d69180c00d01d180f82504c264041c1c2e1240d881d191261041c8030781c11140690b0300700d00b1115203450964451401c01c0e03d0103a0340014109400002090300b0382405010701d04078000c0c0001e8081900c0272030b108035603696003080d184203144221092000d003c016071003c6071540107441d07402c0d61010640d5100002d503a90f0221300c00070f0000b81c1e2980c102d00c018080782c055422a03080720201070701034548540010300908040c4902d9010518203804001d81541004140040e80d4201d0010510945004204142054403078420b49044c00b807260014050f03110362000350b102d410b40d618050380d40d11040d014185000300c84d038814214154500c80501c413200030f42445121900302440c01c1d21406c60003080c184040b44480d92040c0d4011044114544242026008190118900c800030004840040320513244440308088950061300100700401c00191040c001d182c0050040c544035041940711100c9010701c00c180c4d08000c026486641818080200c3c00806002038004209160500c10b071001c04203000313 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 131333714 1250 131332464 131332559
    0x303010603150b0a020d020c03190320030c0303090d02120708070c09020c01231506030c040509040602040504150b0318010f0c0e010206070f0c08090d120306 69
    0x105a111030038107075600c2c0080e5002d4007405440d50010354a0120403800395503503115001c038070054010784441000500c1c0c0800d2500503242400b20241c2c00440356607049039124100002074140501c2d0302c5200445600400248c00e480001c24015640e90400300b5400e840c0c580d801050004540c8101600700100e42d81c101920b4180764040d920030380360340080c078002142c03070030075001407003001d10209424a100505401010407400c00b10540a50300001c404104a40001152502c1903114501b0300841d060a03d04001d44d4050490103000b81480e440f1400904090800d580035103400c2d401103400d2240d446c045c400d40103142076410022041f18500210030340b00d804001c001c0880701610040031204248290008007144080c840104440f241d41400905203240034401c03140144034200000740300502481003001d591407540c55241c110580b030381c0d603026a0307401f0304451038200e8002c481e6a80050140510100019616200426841c2c1800c00c42904450b07480d50200700c01040d075509000600c0b803299420780 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 131334964 1250 131333714 131333717
    0x140316080402010e180114150304080c10050c030103060c05190f0905031002040905060117040803061203070b09010506150d0b0105091201140105010309031b020307081516030e03030106 81
    0x4041d81c40380010b81d070030316509a40d01d40040c0c4502c00d910761035025450650503103d50034a070541c0010020b09000e4510315042903c5564001040460003180c0702d000501080740b110021100d02c070040c1c8030300c04165501650380c07442c240d10100050017000071500401400c072a8619041c0d04000c80221501a01c114050b5401c061040d070160010f88544500000070142c00090100c6808088000c5007100075407041c81500c95440ca0600440c24661040f41e412901c241c0500c2100c002d0344a035101c00c1c10a620160410744e101c5041c14880d94100c1d000e02c098043c603801a400345100b03141c28a001400c1d5003006064034450807002304002c2c0d40c004600140d40880340d20880000d600410000161542e128100b00c01d1341c0f010075030502072030a003415007005d0060940c0c0c41c0300084076661100154140c0d000c2c1c1c880100443c070f64264050400c43d0382c0011140c01c60000b012102d003540c4c2c81d0201c1c2e0030700007060f10720075100c14400c0420034180c120b44800242040580340402040030300c0100035452f4041030040c9070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 131336214 1250 131334964 131334977
    0x31209011d01050f0412150905030a1214040f12020f0a0f06022512080106140702040603140102120907030305040612060503030a03020706050a0504051c030213060306030201140316 79
    0x50b41d00c541c0c00e8445166010306481d540c1c507102e95049603c00b880703290444524103200850350740d100940c01a08403080e8000011818840031403415250b42e02c80b0401c074504d8659501d246007540c09a0700c1e8030b900440c0150541050042141400400ea03034034420b103141558042a42c030030710000001360522031a900071181e50703c3c1501504e0040003074800c42e0001c3c4515242e140707034a80b04401ca2000303920a54400c42d181c000e91006c414080d107044400348104c5002c5003001d803441080c29245070040200501c004c00009989443e5a01c0d442c4900e6444480203480e98046001d0303600c000004202c6d5040b0711702000800409103035550080146c411f81c02040100440b408172404002c40c150030280c090f00000301907a8940b11030350302c024000c0d0040203041e03400038180404200103043c90b00c11640030b160450050302c030801401d04908d03160020089110105030382049410b5138105411007105c081d09040da00032440618500006008401140340030203440e4040081c0b050301c1e448104140321411342c41c102034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 131337464 1250 131336214 131336267
    0xf01060e0109150f0809010e0309040230090d09030506041b0f030f120f0e09130f060e071d1f0306090311101104030803180d0c0203120901 61
    0x12a10301d10182c0c003c4100d03880240d070386050341d9004100e610038503d0f242e5480f40943c1c2d0780d214060a07203107a01c1c1c0d600e41c5508104404200c1d42801e80051060210429070115038030f0f00744000a28408944208880100100041c0803040b50300f44004100c1c0307001460002402ca0a64403456181d202c080e100030003000700c24420740d1490b10801c49400c014030314806218030107952801d1280d07100006c498100c03050030301d28424504885c0140e400e503403214081d03030360200038200c1c42c4140315800380c000d4400c0340c400c1d0f009a00200014480c0f407413840a144504804900c60345004207552400c03040f03030020070290005105210f06810a03001d51f6038400c648510042c481d008084124617481c845400181c079903418010280e0615421480f00009420000115503101007004000e42c2184c0d200042018040e008200c20004030b88400091600207000d80c40c490303031503100500014036100000c2c03000c1000c140701c02c4080f400d40c501802400b012020b000f140b41e03e0040041d0008150066107404da058402ca0711009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 131338714 1250 131337464 131337467
    0x80606240315010e0a0602060403080907120f05010c0807050d0b0411030708040314032701020d020a0206010e1e060402070f080313020f0d080a080c0c070e040204050603060f01060e01 80
    0x800c000e100340c124107652814114400d0b0b515000c02e000303150201e03000000103d018140400c4032401c450301540070308010b4071181d80485190740050704141ca24485c40c20045020f401001000301554030420342000501924039003d0b094030056041101801003600802410981140c00c440541c035004000089401c0b800c3c0c0000d005001c000100301d150203000c000c000a04da00074030740e0703400340d40aa04e030300c8000000781d460702066100481c4c10111808200b00e080b0b4000d00c4640759610940011000541402900c0816008a801501c0f828005900c81c1d00108001c3c3c2d00b111a2070f4000504c0380e11002000191190f405003401e000e1300e9039001d00e60015141042c003001ca840d40e110345620000140c0e41c1e0411460a215204a480e01030740b0415031018011301500d8804d41400ca0654040d1006003001000c1d1020b4900d148010a518500700040000e48807031001480f103030001d41103070352804442e0300785130040c8030440d0002410329000e5403005042c015003820010105044038154a0a440d25200f01c0c0700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 131339964 1250 131338714 131338759
    0xa02010608060f04060e0127020f060c01062909010f05090409050f010c020307050a03080709080a08180607050709022101090e010506010c0c060c0602040305150a0b010504080606 78
    0x503881c1c0d406050305103c0c401d041c2284040c0154010403061001c100e840b44017a08031200303000e0710440e240c181c560307403400d042204d01e41e05111070000708640000d1540502081640c2c0c0194489286a5520041031161840c20410180d00321a04500c802c040c208120140070035110710b080382c13030502010115428821344114212610014041d0086c0100b450a2901550f00e81d5000c1c1d4003034195091000c2451001e1001050360001c035044001440f20b0b1109840544130034201821a0381080f03d0790201148075213041003100d045620981060359100c4041000e98000ca0444005511440041040401180340040c1c01d005480d1103040059549140c0051140c10050140b029201240c400c000090440050741c131010305048144002d005556400d40116500c0c181d40b100201220741c1d010701841040d114944044809120f00401031420fa126142c0ca440c000341304200001c901c1203d400c000c155030260146884d00003081c20214141410119002c1d2681c100a110902a07402904440e100565482 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 131341214 1250 131339964 131339969
    0x210615050409030306090f091703090a051903140c060a0b03010b0d0501090b010506040510030c170a0b01020c1509010e0301090813090b090408270405150901090b0d080a020106 77
    0x140204a00b0002e45000b40250103d4861341074410f2818120142c00c05c401d0154403425130340607a04503007200c202c0420002942019041e60f41a1107411a4440040c00410002401c002c00d91685c601580080c50028072516048000382e16006041c0003c41d003050300082d00c0350700080c0c1c0e5000441c0080300440402d0050400c250f00a40c0138480c6000f00c418004103502c0114440d01540c0c10340c0d1544c1c0c80f0b0f418800284128803072180c12410f202d0710550000d209502c00200f4000300c1c07418100348654103070010f1060900346c03031062155942d00712994440d03030100f1508080000075140d030440d0800502c07071190715004039840e550600c55056003808481da02980821016a48090025150b007200a5000110a4140161500c29240144441d607914183c40014800d550003030010740340c03040b002d0848c950700d03581252500307107018400c00803071150342c03540186840f8600001401d000d0342202801c2052205069010700b8440d0715256088000d91150718100700c5c080d800c42001507548901400803801000c032076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 131342464 1250 131341214 131341219
    0x3190f060e0d0306030501050105090105061e16080a02060912041509050d0501050f1e01030f030c02030d120b0108010f170f0114070e03060f0106030b060f0d02120121061505 76
    0x280c002e9401d840d090340c40081900d00420082203141e03210020300913011401c2c050706601850038001b5065140e801180140c403c89011f4034681072044400c20101113040c1d404040703d10407808207001208590400030103910840c448004d20441102d844e006101d48114060040c0204c0b540b421400b0b481e01409015005041c054107040202c401400c0c103030700804040d118540035480c0f00c008184803c081c1070b49180b4032400c90441188907440c5039210050002003400407000d1254180c40000540da09110708603904456441e11080454450600c4046600000c80b40c2c3c1072019400c010300c000007400b0090420303554450014070307940d0360995420b0718240c682022001c056091000411944402c480598040c6581d5103035240d04940000805407a06812201c0c0c2003102011401000b43c42d1098016003450340e00941680d1500f044400d00e0405540449000c0c1465900000e9a81c406584105111300501040600118400111030340703c0000d2016440504101d8880d4104008a0300c0e1854800051000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 131343714 1250 131342464 131342473
    0xf090206030f0604050106082809140a0201030623060307030908070c05030d0305190c090b0a021513230309040612031404050102101107061806060503190f060e 70
    0x582d0760400e041c1226014011030a100000507840d00800319030303010b402d003101180000e54615500e40e0381c054403c034808407040c0d00c44c42200007080084500c01e04a50b0a40044c00010700390380000740584a0315448005003090a44545106200e2012040b881107400c4503003d03980c0d2a00c1000f1000340c00300040c080c0280500080d00f200300b006101d81e0000f110b00c180c0591350a21060350041e0221a400c8485c41c4400c050f20b5075181e024050399121208140701820035202a41d103078400d000c3c954024441c1c40026030b11801c240c02c9810702103406560f2008030114558684216a50303946446000e004009418591503c0030100e1500d0510071b443ca5108050000c204e1181d850362400381010382c20340150040750f100c02102140b42481c004440580d401070300109450505030400600038101000214210031050000400041450296840841440745000d00c01c05c3d480c20078000300d4a00d684018840d80c4403150f442d0309549120010640d40750040541c44401c1c3d03450078840c0c040c00c0c07503040d6480c0034001d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 131344964 1250 131343714 131343721
    0x1503011203020f010207030504210c080c0103050a1a011d041107031b0302121315021f0903170603010f050103031805010305010509040f080c12090f0103020304020a05040f09020603 79
    0x408056103200c840c0660300b19040303d2091000c1c28200d11400364083c1c00568100700602520448650701241c4d14541884440045596210790310f5400240d080701103940c1082403050800d6038140192501724150b40d00c10407441d02010a540041d126807944e180c107201103a42c1c43c0001c02c3c000d100d0f85402200140003446100c8040c080c4480945c0701c0035041b000b09018400c1c0c0000983d1a00e000c51015a05800030300e547c0740e200e40c01461a4006280401030b00840d800049060000c0000f001c90084035034004200300707c1100030540007402c1040c0800c01540c0f40241800109510501c1d40780036503e403d5a4081940310400417038050712504400c2c1620500b0000000300305684058003c0c005203480f40c00307291031601c032070044040e250203100e92a0b110b081c1c140440c001c030320201c0c034541c0e900b40b003094124507010020325060f0a0403525065101400e001040700030090070070700e500c04042c0e282480d0071443d601c0c04d5400911000500c2c0a0380c1d0103030381d94081e8a8a030007110382c0203e40c2540c0082c00c850f00c030324 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 131346214 1250 131344964 131344979
    0x1c0e100c0203070b07030504020901030209060f1f02150f06060a0e03060709030c080c010801150207031406060406150206071101060b0d0203010305010b0d03050a05030a0b0604081c02030a02070e06150301 89
    0x5000d5a030440d4010080000125100d2103031069038042c49d802454420300741d103140c0802c854490080c0000d80c2c03050b4035a465005540d41d864482120701c018299a0140701078100c1c000e414580c08150801c03d00d4240c3d01000860b10406039031580c455021500036807526100b02003100e01c2850342c070003190544141f000384481035800c481ca01c800c0f04d2048038070250090f21000f001d915900031511481c08504404014040c0048450301081d4660a0340704035401240e5030748401007191a5125011901e402890500074941805d00442d009008001d0154140780d80d0460001c0d65004020003010820560251540e078203882034112800508e80082e43e02d48895a052805001307502c28801182e65618040084855082c6070510350202c54141d01e609040903101001030341d6651000b000d840380c0035619000114290703101800340003d02500c500602d2460700e06804242424943c0d42c11805540c020b0180d03a814641c0060703050140c4456210902807030302c6040106010440b003c40019225802100106980 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 131347464 1250 131346214 131346217
    0x10512041e150501060f09121703040b01180203130803060409080415021b03070302060d0b03070603091b050901180b1023030106140307110109050c0a06051c0e100c0203 74
    0x401c2d40351040140781d0fa07584050b550b95020701c06140124031640300400ca83d482d04a10890010b00609000e4900d412810415000c0d0303004580c111b64058403600140100b060380304040d111581c1d00c110440c51070034140c1e06075036440001c1c000140714610000c0010f410f80c40d150003041440d544040c00c287c5454039003420350402d0032851a298014829642581445450f00c900410042c0c3d0140103030006500310f409200040d0710440c0205c1500b6141d41690b2032a4804000d8040240216540001d40091a143c0b032400c545c10506c0e090101c0d400d07d00c2c103011651720083c0c0f4038115407000605103041c42902400c5c0b070250a4607012694440e0007103243c24813a503009134465030303002d00421040c0054130641145408502003070080780000384002c3e0003030345800103030002590000382ea81049800b6200200c040b50942c0d00761403045480c0d80180180026505040f18900060403540c1800c42c182280002c000302d1554030400344803181b40d00d5106004100358140903040c03030100c148005004440003800041c1d80c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 131348714 1250 131347464 131347493
    0xf01061401020c01020601031109180d0503040b0105041a092a040302090906090307060902060c1911030c06070803041a01060504030308010f05030307060e070b0412050d0e010512041e 80
    0x141c040c1110003d095880452040c0c180e9600c002c0c0c50018a4085080c0094050000c0403405600c1c0300780b20020300741c00c08010941441d801555074941d0303446c1c9450100b14112060307028030700890405420754094030700100c1c485460501901e10200c9550bc490b000403070b104503600354840c8030304004004031080d03185c50010415240259003500035902d07104021a41d540040b601030105410a11801c3d00182441d040441701e280000c140c242010105d500301801d141000d9250201007011010345001c020940e14034040d40c2d00c0440151040380d6001c400319900d441900d100510610380040010100600b0030094050030400402d5041113603110f803000340095101e804283d0204d20302e0b000002d4a103000700420402c8d140042c0103103082c4003690766500701030010f03100c441c80580030300b50004c2141c140b1440500700a2000e4840303600482e100742410b03030030316944607000010030005601c84009640c001d030456901c9240340100b030b0b84540d11401c080c150280000f607903010701180e00c050f85003400040c4000c40107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 131349964 1250 131348714 131348717
    0x2102102030a18120c050a0c090509010608030307090303140409020f0d05010801110403060c090801020c15010b09061e040806040f20090109020a110a0b01080706110c09090f01061401 80
    0x400d109440103407442c050043d4010001d00c201c0c803900c0050740c4510101409140b0440031601c400c00595220100b45070700b604000304042e40d920400506c04004d00403100144a02c0001c0e40c95410032810040c0403101c1800050240507499001154401034074080b10003c1444607011901c81e54107070060859a8060401c0c050707114180300c000300d5140418444d0080400050381c045240520355a50f60001d40031502c2e4480901000040000d000741080c00102061540940605a80d0001d450452202401030b0403810700c02005000002050301c0358400c0311506c8401002481c01c1c4070502d0702c0f4207003e1003203030020042801030381d0a102c01c003c2c180c16150f070f00038406c3c003d500c0c603d0a5441e06240300070103881c09a6010071404010803100069500034042e070040c51078140c02c03520b81407101a16120111800320f4191440e1001006032190a07c0240003408040c40e0800184141d400016619490442018414010103001c101060810011039007a00366007002404915a140f50307411900500710700c0340c3d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 131351214 1250 131349964 131349971
    0x7060c02031308010507020a0209090a05062a03010810200409021306021b0105090a0302030708060403020d020313030209060109030204140405010b0411030a05040f08070803010501030b01030204030f02102102030a 93
    0x9090f25041c0a030303030310400040e4002e00c4034481d184c0822440d40d002614a56080c0500b19413480402d500b804464840d11403505003c0b000c00070301c0504030010500400324100c1c8842403005012946000c0b440408004807c034020031121248800c403007035848841d14484442c880010005105003968010f416a15801051044041c0e5610000d984900710700f003c2da8070b942c42c1d645a0a08541c002e1025103868503010344070003612926580420f01c0d06045801800056001004000405604004020000000c5e101031420b242034070300d094003211114007000b8411a140030004103c2c0c0d1064042c10000d5800038801d11025034440744408401105540c02d482950910341009410700303040c042d16500d403681080c12450766a030341a030b00c0001c02c00a44100c40c65903030501d1b0000400c80c0702010b006514041e0021070780e41e5240100160440310070040d6241414010712040000c86c001c502490780c002e4065403c104250521841114051030781180d24150b4217800040c40d1105003107501a40c8200000e00080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 131352464 1250 131351214 131351219
    0x2030f03102303030a12021306020307020328030804170d020904051006140706020408160e06090f01060e0f1009090f0605060702130906020a0e01180b0a0e0607060c020313 75
    0x204080c0b00a40c04941d0142c3c0100180103440340b00c2c034070034211040200d1005081108403034401d05024603540c0280e005a00110305081503250900018401d20b0300c1d076640001d0300302004a400c00c03000300071f40040e0900001d40001000d20509200b9007800c406800811035a6800c100304400c000e40100b240b040c010741c9018009074001c044615401d054401c0c548074800c01d851060709e24001030340a60400c0707071041d03028000055090420084a45191009a00b081c00b00341481184404007400801441c8102454401d1001500301403000707070706540c40c600d085522004844086920725111880703494200d14800820907520740c0c484602f9050341d0703004600b0b00c02e0f08988115541034034694040c0343e0307201800b0040400149080c1c011846114851600860455402d44500080b60000c81c070060200348990b0060b8025039011010142c169040c1704240035481c1071a401d014240601e002c510144000700c81c64108580c0c80d0429180c225034084820b211588448100945039081115082c000c0c601c0d40b80003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 131353714 1250 131352464 131352509
    0x20c0d0f03050a050f0a0902010c08030f040212120901050a030b13050a0b030109021c0c0e0c0301050907050711010e19091401080d1d040219031b0e1f02030f0310 71
    0x1e050045d0301403290340380b107610703500d184400900722400100e0501c00396821100000380020040c6105110718810049a45040c1c010f0101500c0c80c00c00c03c100680000107002030302d400c1c1d01c0668860304020300c0d00304d890707440c5078200b0b9000f07105c590b081c140d0180314140e031401003000e181c010901c40c4014007010b12012032400c00380341c00e85071510300003544640b14032a608100003003031001001d0a401400e00070015030759800846540302050320150030410b0000014845800d188187e260451524903001d0329183c401d48a42e080c000030440c0b241d0420144e0030302d0381c0180e070b2030440c81c030b0400d990f80142d8400b50703a40c0c88400004050b401c204050400c4c1c044000190034502261100f01e03044561219641000040c02200040c03000129072070b0703c141e09004510384040c8a0003139820094040c1c400040b4028142602c0440a001d0714100040110089110341251074020070b00d081d040d104840803d82600b4581c0580c150f00600c01c001400c031102000308024503e03101c20003402c0f00d500c03401140120780318041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 131354964 1250 131353714 131353721
    0x5090a12090e04080307170a0608070e0103031d01020708010e010e0c012c0a030807030203031e10060507020d050a050604120305071d040b0307090204090b04050105010e060d020c0d0f03050a 83
    0x303241c005010b00c50015010402c490029544501c95290114003009814150601401c0a94071500c1c0b46030384103c04d101c84082009000043c14005007545503a603d55074009107002c4d2181c0300b507580c12003034a0f100b01499000b044544081c0851100034021054410a514020088502c0703010091158610b0010700754050f0a03481006015615490000d41329800e44501c05c0d840008440d41000c4400f2001000c140a000a0f2041c684250f010356601d00f007200200c900c08010b40c40c088220141d640c10300140e02c0c3c01e9000c000c100c85043c02c10b642c41d41c400e400028a401d00040303000c0c009029900c0c08408015000c41d82c24429407041c0907803000d06400100460441d6404c4901401080c40c540039082040041c00f040c201c40b040040021030380c0703c10300d00030900b0609180d201d4800e854022500b03005001a078000d182d0304500585007000558544400204070600c003805043c0240e80009581c440424250101d8140c6010041100c00b0160301e460000c1030600d6070701420700024601804178105100710700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 131356214 1250 131354964 131354969
    0x1303022d10020a0b04110306071d0a0f060c06150f0f060507120c0203030d0e1b040b0d080304080706020708030f06120d050306010c050114090c03030705120f04050405090a1209 77
    0x1401800e05106941e41c1e5004a813000d80142c8003882c0350085407610b650b00b000490321442103580c0b24581c1010038200900c0118820070380324400c0700040000c2c4408002c0c01074500841e51540740c1121000a2420840b00070542101d16200440604c50041540000e421020b41240c0d580d1618070250ba0359044125981d0141d508020000901c0802290155100380e45072800d2a00007000d407450005080710800448603012400080ca80124180e009a640446920600441c06903402e00100004030002a8603803100003005000000100108040c0708060050b40c100c1e43d400300c402c55441240b414046103d4104071406210301c1c201800251f100d06020303120500c4a00c58030004d00e84400c3c501425520b9400c000c2c003240c10007a03201d201e040070480c00d01070000c9801d1844280c110398246441c144d401c02210b0241503000390f000700941c0c0d001601c0090741c400c80c403807511034983d1138020710707600d001d03140c03180307a20003580a070402c41031111200c00444e290109610440708503001d43d102c01002c1d1001c10031031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 131357464 1250 131356214 131356217
    0x3010504082206093506040c0b0f03160309021207090c03020c030d0b060d021b06070507030f0305060a03060c2c060409050a090b040515010e060603010306021303022d10 74
    0xe40302000000d800044401c5e0065400c0c1161500f044003e41c083c462100c03c0c0805003555000805010511041d8650840035004004005103001c40d1507002842d5480b0141c54070400c104d00e444034480c000d10a034041d8407102c0c4d00500b81010194007503000e0b0f645186500a28104034901001446094000c0c800c8034038250351a006981441c0043d800840213000309160036800645c05c00c03801c2c500b107126200a000024136103e21400041207004650324140008120700c003800420403030070003c2500b025035621031442c1860b0201c1c0c590349100200c3c80c1c05200d540000d001c10b0800400030182600a0050051078402c4e0f07402400303c0220342140e504158126031115000300e01040148080074041e00f105600000d10f80340850054810b580d28007088000b2034050343c0c0d94100c84c110380c6096a0204801e4010440e40c0d13183d401c80c0c14580b001031134900c0107100003099603a002452401c0704008580345001140c00410204003606045101140f06a201d102d084c0d0030f424410a40d24949003511401c01480c0c0907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 131358714 1250 131357464 131357477
    0xd05090c13020c0a0204050c040906090c0503010522020706140709211403030c0301030b0c0720010210060602030406121a0d1b15080f07020a120e03010504082206 71
    0x10340740a84001e50101c44801000e0090940c03510141c0c41d01d016190203805403826843d40e80346017800ba942210043e400c8400007509001c0070114142c3d224058a054600445040307a03403007411032018040c003a816550071205400862500c00307002e610b81c03250050a03a0001111025070711117000304d41c1c80380e180c041d04100c1801042c0c0c291444102c2504084520711403484a0390a00349501c0c10351651300112102442c1003800401441005600c104554204074103004a6003030008070b540d041070f0030f08001c208602c03920911500c5079042c0e108110340100d05451034400c1000903100c2030000d440398420b005440108000b01d80c1d941d00c40b04240315a046101c55180328800e00810b41040010380c80000b00280c55a801c4c64101200c2c3c4145580e4000040c445940008140c440111015009000017011034140030801c0d170402a0850700480d8241041d64021084640f00304c03007030030940710b8850b4030000d541c056281104010400400c40d000384001041031116140c0a00450404101c0c400f050003040c000074203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 131359964 1250 131358714 131358739
    0x140c07090203101805060301060b031504020906210108060105030d1d010302040b0a030c030b0904050a03082a0409050a1107080a2a060b03060714090f09040302030d05090c 75
    0xc00d074060358224003800e41100b000c9550b490020f040c00800ea155030301d425610014001d00f860248100001841d09118650543c900401c0131914002e01100f454095900060b240e001d56580703504555200515074035644005402c0c04500081c02c00901800c1c05500c1288004075682ca00000d0b20070140700c069880351112100102546440301801010034107044d02403001141075020640500341c0341405942c005101604988000c09403901c00d2190340c000c060000a000c04a000030030403040060305030508a650392101104076004001403040500c10403021810040d01c2b0042d9002032088902e0050700b0310070341d10b48a0100741114060058116114402c10200c00054409800303400d4940c0207003003050a000c2d112400e5010758404804691404000c0140300081018034480c19081400907001016a860407010103003a406400c8d04448000002040b100d0141c0d940c1444c2c0c1401c048003400c0090582003070300e0f01a5813a0403244c5d18884060800000550314040040c3c100c0c903043c0005c04030f040100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 131361214 1250 131359964 131359979
    0xf0e01110d090c050d05031e04140d03090801060b040503010b1e090907030b01090c03150612090501020403020604120b090c010f2105190f0510052e050703140c07 71
    0x70035880880d0300c1950f40780c00240d599a80781015a00c1806100999a6090700c410b41e242c11003803a00c2d02041c0c040d400c0c441407000c040c40014040c218602552101c20700c0d5442c2c101542c4c110742e954015030740da40c01c0060100c0c0e402507a002410445006038024018443c0c42010800300a204014039a400c0400602d140103070b14003010890380007000001518a055280c1d280c041a10009803c03140c0c4a80c0c843c18041016030307061103002c60b54144a440711101508015004207450010082c88450070b448000810a03c1001c0d4100d8000b103600901c4691b48a03541c00d0110300c07502060300c0c01d80701c00346200002225084c01184644203502c050703403100d66070002c81c803042d40c104903560f40ca42454241d102040341c1d20b00080c41998003450105840b40741550f480c201d0300c8151400200000c86032b5040c41d0501101400c2240000300b030702d404071410a1040b104c0c03e00c81c0000e4501170303d001d0546000500c40e100383c582200080c100d041c004c1c1c0d101d040351851103030700c444d291007403914202659120744001c00998 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 131362464 1250 131361214 131361221
    0x140301061d0f07210515060c07050402130b0313030e0303040b0409110d140907060f02060114180406060503060a020903030307030504031e0503090105090705030a08070201020705060c010f0e01110d 86
    0xa0590034640d80000307104100da444c1000c4409042d54580c0c0e20418840c0c0030034402c1a0007842c00b0121a03e0b841c1003014004281c440080b440341398002d81d004501710039502c3c2c0414039100507104001c2000d0300c030b01d400c1c40f0755000c801e4040c80c00d50114040740303829042c03403c005c4221420ba039076038408107180524082c0400000d00321510512104d26080c03203441c4175a0b22038005c40e88954400c1e00d0075081ca0801072503071401d1120690000c0240900c2023241905641c0125445044420110548021244140c045145104a04c81603000e50102004120400080303901c0071064950941c1200c2c10755031080450360480c801e9041d0943d05600600c009080b01c1d109030082d84c4e016210b07140105990040b00501d15030910340300340047c0420310200801c07008007030910503280d000d031750800149086483c0c200840d403075104a62000d05020340008032002175900800c0008008c1801a180e0795031131000419813030003003140000011146062000740304d400b510502404038280843c1002d50309d03100e402403001c8c4c004d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 131363714 1250 131362464 131362471
    0x30601150c0b01060c02040c0e030d1215060c1a0420030a020604091a0301060302060901140c0601031208090a02130903030b100c05060915190b0307140301061d0f 71
    0x400500303810141c001502c40401c98000c200c1c6444400200d003040c8100000c0d146820440c60801440705080c170360399a40026000e009081508001c1c600d8151070302c0c0c4901070080040312146404030041d000402c99800044402c00ca40a0b0351072802c0710200c05a5400f09642c00c2c0c801a00340c0c0300c007861296414000b02d401034603058004084804440c1e2079404564542c10503404401265030f41e01e01c4e403001e1072a0380c2d00860710240840003000b0003801d5a0002d51a0b0140e40da01504005020600d401c8441c0fa040032280c441c20000201ca04941e503914140c00110846540b440c001001d800206e40d038510005030504e2442d81c0185a191001c0107121800002d250501040d4100f6032a64000100c0b0346071a06000700c41301a03550b441c8101710080c1407040c5442800b0f800781e4480c4d80860410759000c10310148140e0403024890076103011404091001c0044e2070182507050341030203545000107803848011b08403040d000d4290000d102d002e54070340d8001c201560b03000400f2903004d0306c00000307400c180f494040281e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 131364964 1250 131363714 131363717
    0x1e0b0301050108070210060b0d3602120601080606130506101409060f040302030d02030f0708070f24050c0f0d0b061b0102210606071419050114090a0203060115 70
    0x10f90100403006d003420789503a41d00006410034005412070004915008083c0740800703c2c000442107024441765000101d4080040c1008003420035501c0d402c41d6100c9519003200d41c40d05040b56080d503102c0d0105070300c030760050301c03150311a111104a03040c003011540038851007240700400031179504813070a0003076480c410445807450100f101001345045a585000103405401c12a6880c55207803410340c410301d03141030666601081554000d004201d00d0003151011600e6240e800300905894039810300c1c0200c40c140080d0340090508442002442952195100340504085480800d005039194240000f605114000d55282018020000e1945280c1d20b82c0007000002000b82c401890650600303505050a003440421070616500041c500301ea0051400d2040320380012561700b45040d0802c0d10000345c1c0391003a00001448881300b4508246a1b00307040c003001c40c080c1e03944268071a40441d2460100d008140e00c0308000d10b440c050034080340c0d103103000089400b102c1c1d03809030050030741e6403c24051022102000301240c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 131366214 1250 131364964 131364973
    0xb0a05091504240311030307080304060e100f02030a0c09060909020309160f0303020106060f050414030703050613020a0f0302090103081803011a0f090606030610030b0301060f1e0b03010501080702 86
    0xd031072a590b6444110100601d504500c40ca0139854a10807040c04120706078403940c014000c81c0046503400d0f04603a00264064800295604480c0c10f41e42041842154110282d00e0002990305864054008521482824104000000c03026409030340498a500600c00000c08501043c050a00b966006640042e903100456a514040c04101e072402c0090786c00c0715440802443e820002c160302400381501402960408030949814040010442d024600c6010316550a0741040742c0d6584080c80800051a000401e4400341c3c58400b4841d400320811050803402144090130004a88070041044800c0d00c5c0d005100c0d005030f900c0c3d5147d101b00381e009400803001d18011064900d05554092080403d0044440850085070f065441000b8000801c103061900038a401d40410245980c2c0b003049036408601221810600c5507001d0084004000540b1a1a0035600e00040030562442a001050480c1c0c90f100300203911000078002d400201050784201d000140042c00103018940c00303500b109a001d00c0340d10444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 131367464 1250 131366214 131366231
    0x30d0e1203042411210d020d0507180608060d082506060611010203060f060a030f050103080711030f0a0b040809040c0e032806050703180b06040b0a05091504 69
    0x40c5403c5240020101c2c0921000410a0045030000c5901030040d0b0168042c20000c0f9000c0180400d101c0d00e460651040840011030301460007907641514507002e21484100303c07070301e070200b40642400710540d50885080340b00c09001540e180f0503ca20b07440340c9000742608491000c2c81d07842148a40101204080c18040c4101d14155204038941580440380102c5001c141c140c5080c40141000400003000c00569004004000ca9231329070316a001c2261801b40c0f0032540d07400d08060304030010400c10550703410041c1041c000005001c902005001418003801640c2009894203003055520700d80044160507607003000200c0700c0820311250400754001c4c000d4000511301000000041c04941515000101103490500402e82030b0a040000c9856078140310105180c0c0381c0b2100c96107004050b0050000d28860b19030f0005100c0a1003504a0614a914103e891044401d98a001c0392140c0c012913a9900451400c001019549040b465081c01c480700500020342076200c801d8694842103000a400d80c0083d202c1111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 131368714 1250 131367464 131367479
    0x201170c040305060403050d060e131401060506070602090a08030306090408030a02190302070c0b040501050d0f020d140a05060d11010804050c0a080703020f2b03020109050106061d030d0e120304 85
    0x90301d03ca240f00b0740ea01039807002110703182e10440340a80c0200c424ad46008080140b503501141c2d0850803650030800a01e440400b81c4903190140006800c601d8028001050074405c00200b074003d0701e1182011582c40710002d803185402a6a80011100903900c44006808500840c003200011500040c0080001d4a00709030071480d51009664201200c000a41c00a6a00107005031a00317200e0103040640002c40c40c1038a000002403c40c016411109503e9542e000c2806140035680d0441d00c01c4030117000180100072910018000881c4103ca800300d5403410840060b074245001030141c589a40d0107a11100d020303601a0044074443c4004000303c802d48502c22009860780d0f07407564060000c0c1050001031125500398814492891407215030580100c807c21112861541e102060000c560001d1800012211090034100d005d01f00441000e03003954a07004011550b80e60000a04517881902168021031580030804c0c15540c4900116000024840c040d00d002c15142602c1409000070010044038185921040b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 131369964 1250 131368714 131368723
    0x170703080f09060a090801050603010c0e040c020c0d061d061009050c09040f02030105210604020f0a0b0a02010b010806030a0309090203130b180d1701140109260c04090201170c040305 80
    0x66044c04109041000c1000d800c0900600d40e026505900078415001d2050024014555880c031503807045444240d00350000344200051001301c1ca00034250808180c050600c0002080200300d0810f0305240c1a0500802001c001807407400350b41001c000e200380c3c0d4984240000107010244c5004120001044040345556860040d503945500c407000c010790300c0d4900801c1081038600c0f0000c0340142402411440003541c0c005c0b518903401601621240102036080c0005040320a454200102c00d05001c107030108019815440303010302c40320170b032070f2001d99846d04010580d40c3c410242000b00001c2c06104240100069900a035411070901c101ea0071002441ea0307644050104115000411003541fa541170b43c2d001c504010300701d0b04080504100c401e0617810160030f18640c1050041003031252000749628410391040c00c8007401000d8441d480400c800750705000b00d850798182011507005201d48001a9039524241c07250750012035050b161000080d283c4215240a210020010b0820f00424800000403c1e014003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 131371214 1250 131369964 131369977
    0x80a0e060a1205010906050a05040f0b10030f050c030405030712120606020f060601080c0a1d060a0e010207062c04060911070b010f06050703030b0a080f0c0a170703080f0906 76
    0x102d414107101c2041e0900380446105a00c034002c0340d42041020856510303030542c0f0a00341c80b07085d1404119048840e03641c0002e08028800e0940140c0400100b440d1168176034410109034100380e206000315100c44082464500066401803d55042003240b1400901d100039000210384681c00c00000040140710003504580c100c3e884440560480c0503814242c0c14203201003076010340242009000c42c18903010720030890041803010f07000d0045108841450f001844803104060f08014200c1d640c40b003205d4001003401c00116403050140c0b04852002c0303562402035070300980300910788040d080803000b41c034409041c0b8140c21011a030840d0f5501c5004c180403c2d140600402c034440382e841603903245014a410a000c0405901c102580001d880c401d103c455402000c80e00440e4040c540800d0f1507000000080d503090587d803080031288507a5080c081c408001058118001004403481c46807070b0703070319141e921465000b4030800c0328603000090180b0008145170042d0901c41b8000d6003150400001e071022941c2e41d401350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 131372464 1250 131371214 131371217
    0x5040c0513090c2103081308070606090c140306012a030e120312010b0a1106090708100b0a05060703170f0a061203020d030209040906021204020901061b080a0e060a 72
    0x941d1071000340700141c3c1040004040c43c085001d00400c40c15911642c60810388001002c1000900c0480d1410051941c88940a50010a440d5480c403961030f044004207075500c200c1102034207004480c01200c0c090401c201d440300707082040754a10b41c1c039440110303410352070704070a141d09020780100c04113802c440d1141800700521980381c0d14040342001040104071015280128410b03801004016000b038520104d4604641d011841c8070346400c030b2280c056801400301040300000b8400d50040203102c402c0001c001081b1541d8400f622218414140b441c810350382443c0310540c00c580c1c5400e0401032801d05100030900e40340240380017117a80d0a072134100e590070301e0165481c046100a01041c00145011441802c008007500100b00055450700c0e500691502908507000c020305a010444c1d485644540d0050149140d02041c00c42d030755000803003104c1f10500b00392002e038042c1c0c10060000c120203000d1900e500706104009811102c4030b11554843e10b180e400f0160580c2000300d0070f80c0f4442d240e11008060403088005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 131373714 1250 131372464 131372471
    0x2102061e0d020c070e0129190804200a0b070302010e0a0b04050633062514070506070f05010609060b0a03050c0a0504050105090d050a030c0b1302060d05040c0513 71
    0x56240300b403500b030450b0410010848400010400b826451f06145002d0051145000004c452040b06d121180141041e080492400360900ca552a502c95640e40c40785208003040d6000b90500402c40840e0088181c019411191160303091180009200c00380c01d1191081c8001f0410041865a490408510f5442111800210f01c1400100102401155881042c1d0f40742c07000c001000d02540c48400000c4802c001141550800360074590303c0389801c5030071f20329500c6049506040400351944c2c0d9448100740030303940d54400207910206042c0100341c080803654020f11140c1404026111481540a169002c44956507100000146000c03203024980c000e05d071080c095516032803031070360240c2510030060984889040c1000448001600714056609880080ca8440c2d12442d040d00440d0a2400e0540c01030500d1180801450415500403200c44042d445215038048940728180c0c5442c80503551030300294088801e000c0e010b1407035034640c0007542c410300401840c1c0042d9034420104000c00014282561030036203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 131374964 1250 131373714 131373727
    0x90c030c060f0c02060301030609020f03010501061715030a2d06051503010528060b030903040513061211031603030806030705011706061c0f02132102061e0d02 70
    0x801c16106403140120f414200810b20140e030009602c0d100c14000100742a560b141c45209640b2012400303c00c094024000f0801940c5030a00074000c101c0c1910441c07146070411b070014107507400c403c08441035038201030005c20701d881b007950b54401020034020079146e070110f520001c010300c1c180741068400c10f28024000060300d070400c95481900c192021841038000e138184824810703000d01325901903a00764060130244c0e201000c0c111203240078080561140030f90b0100407007400f002c1c180102c020320864800300c0e40710801c2080780340043c090ba03150b4800c0b2050615140040c001140602c0456041440001c080c0d031081d0320040500448815550800d50005213050104905420204000c0340640740900341401e030401c08403440e6000241c001d0907103019210226900700710781c01650b266841103102040a00075841c0240c1c0320402908102001c03001c2c44420303880062240040034092900d80340001c046035010f180c5800780105a80040c000f81080703000e100d4480c5c110501070000c2c01075a002d0b035034056600c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 131376214 1250 131374964 131374967
    0x1208031f06050a0f110a120c05010608150708040c05040903030b0d0c0603051003020a0311030a12050c01050a06060c0204090c0f060809011b020303070f0c0b040302100606020601050d08030a090c030c06 88
    0x500d0104d00107001c00c80320040c00c041c00004001c068240d01031607012520440041c120345100401030300506944c04c0003000b040300c07840403a07011461a05541b01220700c2c0d44d810401c4130300c0c0c00169806031109044050030f0025042c075421448085009007001b08440c5030f000040b03852529152020703540d00c00f08017010b20100344d050160380d4012201d0060b40740c04c0781c25500011003d40d400c0c44000c11840d100c0740c151007262424401d034040c841e0858a039407a44c40d501c80001e400c940c40b50340302803480d502c0c082c00a80d904502d48960340903944690340303511074169140d003440024210300c0c2d416a50f5000d6801c000031321546040b149000390045958031041c5007050b0031020700b0765503070101040740c00c1c1c0c0e441c1d4105840c1d80d002081d41d07800305051410b0b0480500749075007034680109400c13001d02640c400b01c0c104400c2c15000611802c0c00d40c51030804000482d60741408a85519083c09600c1e80f000f541070a94022900883c00785400c200044400164021142d03240c0019490301e5200f02d840304030f803c0c420041036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 131377464 1250 131376214 131376227
    0x30312040308240312180a030b0124080c0901110613031107051810050310090b07030e0c0d050c040501080d080a060b07060528060503161208031f06050a 67
    0x10001510303e0741d0803240d00c40000e601d404032000f10003010400802c42040ba902c01c804a00070840b00076142400b03031500c1c2d00300020350020900940c100078099000c02415010450021700c1d40000580e5144890b840c0c03240050030b56400502040d04024060401000e404424070000c6d000e00c603d40c0f0cc1511903421464043e12011200c80d00c036072550001c2808003c15190b1107415880540e5650078441c3e140d0b90165419900e0f03001d50083e07a01441440a403400d5243e15600c484400ea01500b00f8983c282d440c0305080f82136880c6a4480b504c42e070801c65130400e06c3c0c140044104429032081064034148800140440d0858500341c0c030600081d400a400441d11075040781180341c0201c15240144a140d0404003d50494441c42c031004004035030b5217000503464109035844110f440c0741c8034403c1000c0300b8003ea19034050b0030103024a52082c081d40790108901c030405000c4004407441c20010010080c01c030b40310150981c1004240d45e114501c0f10707880c060410b5000700607801800c401d441b1103032903a40c04a401400c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 131378714 1250 131377464 131377501
    0x60c08090a0e0915041a060a0315090309081f020d090506090709051807050f18070e0405010605040e0a0e01060f0816060f12090602040506070c05031005070c030e030312040308 77
    0x1322000303e0030710000c2050030090606e400c482002c894550f0b21400041035007170712141d0003c4c00107100b000c0000070b0524640c1003400d105d03001f07039100030100703071a10100798070364585200101c00d001c00011810442e00310b07500600369403600400009003550300b03603e50702d040c05001c5a0301140d031307048010f091001c94110312809420188500b200b11a110b180c0b2282592290315011302d034840c52224095040740c2d40d036250380c41c8900075071050042c3c460610b04809030400300c500a000303219900300400442d080e80f1502c1510125142c01101d40035540712191030b48020041814001115501e466000c81e42c101c40d1070a510041c045100101626185062040c49025080c2c100314200501d120400a807a40c3c80600039201e03162043c0b00280c619990300c1c1050092296130712aa801c0400030034000144409006400111039043d019031f1400c1e01c240d82c0701070464000301e6104011605486078040480d1144461448103000502128038082201054640400c0100c030100e0004e0195020018091000141d00c4032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 131379964 1250 131378714 131378743
    0x301030210110d080903070804080102030402011106090304030f05010204030209130b010909020d02131b0e030f070b19120f0e0d08060a2706030c080d0513060c08090a0e09 75
    0xd01003000918907242d603c100402401c020b0f1345404200071403c00d008545003da881103045940b00d80e5036100c20b020390801c41c2c099000c200301001c005200700011500600c9000010041d41ca414116070b83c005101c80d6a90003514299801d11000c00142c980c1294240603d040300c880c1c084c06407051a0011103c00d0503041401818184080d101c010380b03d00109c03844480e4101c51200c61001176440510045c1005002c681004803a42da59400f010703000b4001400c9203600b5002d8440c188020031641782d0f140940d12507581c00e0306081020384160540300000d100304050500e40414000c0084103041c0075120800560a4407a030f5924030300880d8070040002e041842003a041080c024940b01000030b20700c485510134007044031010707105070030b8103140700420380624402200100484c940b2820100c11641150181c0e03655442001c81402c01c4900070415180d40d00c0000c092641c10702d04202d0125061110040f0446811800b40890308045d40c0d04044035024113410003145030207180010310720349401d544016802d07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 131381214 1250 131379964 131379977
    0xc02010216060603140109020d0f0f06050106050a0201150b070f02190f0f080c10030c0c0b090d030e0313050103020f070228120c05040908070b010303020c1f0c03080a0f0c050301030210 81
    0x7c0050b142c541c1ca20011980003007141145180509024010111411000705003034585400444c403c0d81020140924008039402006815620389011003846464080d500c408007091000000081c118018003845501c05044e05640300240d8030209451341d4142c000381180341da50201848031182d01c90a0000078010b100c0108200c507403d80206014000428100c403c26880d020031241c1d103030150340210a150b6012902c0daa07186050707540c858480b688020104002810000300311400038001056650341230202e15421040ca1421006400a60060000c400c0784141030202c030f000350361041d0314003015100f4007424401400024a54100010789500b0045101501c2400400412070b0b400f4914262001550000b51001032424040342d107020701c4000a00350843c04001100f0180d01143c0090052000e45a00344a40d1503110410082050310b400c50300000c0f84524441c0105e881074038000c0d00520000c100154038520389141c10240c404c20701c0d425000c81c000000400031801e0000022401c0d030550714100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 131382464 1250 131381214 131381231
    0x30c050405181b0f030603010c0c02031002030a060f0312030606140403020607140327011e0305070306080d0c2306010b03070e090109140603060f0a0c020102160606031401 75
    0x1e80303072440b60760000c803031840102c0054440745900d09012000c081441c00144c6070600710000c0c814650040320918020350030041c10300910303402100302c1c03501c031075004015002c0c503072030003000f2002904006c14041e86141c846000041039526640c160011710b006100c0300d1300310042040060300307440e490760140c010880d0b01a041c004c0c40302c10100b610f054a40c1201d599030b0b1030b502401c02084d5031400100425480c000017a204c110030141081e41e00c10344510b825100140f0301100f006541044080a199401d8020a08046a0b140c46030b401107602c4080c03410700090298a8007012481d20482410420110b081d40d00000240580405c092118800c80601c07840c080d44082402c90301d864040c869400900804400300d2881405074945942003034000d0214800c56940300c0c0620060072440c03420f280d800c0c14000c003150031410042281031241c81001c182100a444090000b0014440303110008110355003840001d650b00700f04080350b44400d001d6100425100d08508128440200758810b40007070368502900d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 131383714 1250 131382464 131382469
    0x1b03030c1b0f2108030f06031006050618010201090f03080711010509030405010e010c0605130b0601030209030c090c1b0c030d1e0e010306030609050615030a020a0b030c0c1002030106030c050405 85
    0x8000659007055400ca0b940e00030340384294510f00070030600078028800402040400b81c035508910384150303000ca0032694000c024000c000304854860043c1c07501300c0b00800c441f40e0090b10128801c6c2a15074188000140d10080b62955142c40c14650800c40020f4400e01c10300141f1680200100c80d01c0c0820402006142806510259a4800c0b4401c103410300c14420b09008403070380906003507008650010420310051034001c0071001050507010301103500a14801c0420481d500c0ba01c207a039113070358015000341004040d0300200000440c00410311556020100890105060f6080c0c50709025241c403401044035602c0d2100b01401c0218080d800000c1000103070710f10b4901a00d07a001640c141000b070070310920161411004a0280000d500003524a81c1020701030402c01030700040003441618210542c50317841c4500c404141d21403e41d6540a503220a130b0365005d20035a0701a4000710340102c00c1a400c9882c00340721500580c20b009410392009182c0c0e5001c001080842c3d01800340c00214020b40c54041d1925050200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 131384964 1250 131383714 131383739
    0x6050303030103151107050705010f050703120908040527010e100b0c01060b070537150f0c0f3009020d05030c010b0103110c03161b03030c1b 62
    0x90203c0010503a1045406030030391180c040030502e0346805c2e9803400182003480d81d5003243e00c80c0500080280b0b00681034180b19000f43c0342040e9041c1e955100400140e074112001c0e111a20084d5041c500c200000180c41e40c0700072205c0603400701103100340a6807607085080b84517030105130b000107000d0020004108202100c0039004099940d1160319548800c400c0f1000ea00401503a0814089000002541000d000300090307180e2086054803101c0701c0c00e0302c080119101030201c42d03100c822480b0301c4c0154134000881c002c030451010881460001011550001e0040540c1d96007840d80001c1429406000d4625034030418404902031400c449091480c25510780f00300da014040000c0b903000b9501c11010045540e11142c102d000d6070044201c03504c4403014885e1030300a240602c030003400310346820010b041e41e1138510260340300c40407402c001c1e40c14181800f50f601c803d0001d4950440c0d005c510817024501c608460b072103040265004e80d80c2c0343d10503422440d2018014150a0500d01d9030044010304006c01c111100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 131386214 1250 131384964 131384969
    0x3110a0b0307180506041a13030f03080114030a0c150c080708030108060c09030604021e03010f021305010306081002071b090204061709060601140d050a0911011d06030c0f030403020a0510060503030301 88
    0x700d01d659230f880c680040500034100e80000300070b501c808902c00c06156000c000c039410381e117540c1c10700c4100310309090400d40c1e0b40c01054002000380090100402070b103481c81c81114601003040c14030100c101c0f015a40d10440303601030746080f6941a40400107118000c0c0070403105c0c1d0701160401c2a14600101c0c0d00c0040d603207000040000340710301640c010700001840c40828050f001394015000f131103080d490040c01c001075045052a0b089406400500160340e40c8a8000c2c0301c21145090090105198140c08840182d03128000540340003002c41040c0048220310100b00c0e000740425000140c4490405000419840f403144038450142900b0050003000000418001c0d0000d10900700781c06090807082b180080b038012641500c06e00b030702d844208051683c0d150044c160f01c0b880303000302e2152002e03500015590541c000c10012800d14403143e2031030035410454003c50300404c00ea1401d5040c66005001240300d0341c0101c4046005800c280d0f00d4400300041080001c2034102040d50500c030050901d00480e0ba03a000c140b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 131387464 1250 131386214 131386259
    0x20603040201051b0705120706050301140604050a140405070e100e150406080f0a050c03070e01030b0a0315140108030a080402040906240f0e0103110a0b030718050604 73
    0x10124086a001d80c0c22205140c2403002c0000841e1000d650294481c0c0b146e1203050300515211010380507441c00410034006542050702c07946c4c1580d0a110030190717400c604200300d5411150400002c1255664032074224001d008002030050000300c804140815501d0103080c90050001842c10803015a40d400795038112210785240100d82c002504c1c0004a041e030542d0104440d501c0d0019010071459405480782e48241010300340303046240c40f400c0d4110101c8078100d540d20700144060010030034840c85400340c1c0c00b80034414503000c590307180410700249580909a00841e0030100454100c1d050b131105000c0c1906d54030000056150300d624050516440344120100f59081000440024045641d10340c0200041034200c0000c01c409480112460356110b80c00d01403454a0f0800c01d4006140782540007204180c3d205101042d2543c0d10759075440040000d02881d403540900f040c640401c100c012400950f1051490380e03520449180b016400d04400e0542e1742005006c9c0303c04100906c545244604e0010016148 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 131388714 1250 131387464 131387467
    0x11010b28030611070b1620030c060f060909010c050306010302070206160f051002190e040e100c11030c06060625030507021201052a1b0307110307120206 67
    0x64644000c0d540040d03000145142d1030003000410889402000e042030301d102e04062a040d8440e0721180c60382c1c0307071060414030000d4616515030380780001031110032055450041c12203081014902c0c1c41b609181c0c08132001c6105078082402c00c01d503858640c95054011069400170040320301c2210000b40240700040601e814950001828011511808212107188592294008500396580350084013440e0b10507060b503007441185406803180c00340303208658020b02898040c2200990088041e00c0d49800700c24102c4c0d1259131164218404c00e010300c190820145038040000300050180f4000e4886000030100f0440c590041c0801814241c0025080350002002c0b036240d500c90340c070b01d400c81e0900d04101d80c2d5818105c03070980d903c000b0550084d0207018090b100325040c0304130000c280100c500306c4408445211028042c080000325411100c017018848503907600100d85040d1308034500352041c00011990390040e520014a4174240140f469a2540d609012800350006901d030034000b07500c2c50000100a4801d240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 131389964 1250 131388714 131388769
    0x50304200111014113060b0303120103030207090c090b0f0c070305060f06090c0a030c05040504060e10060516061a091f08010501080d0305090120070311010b 69
    0x108500100a00c2040c001d010381d0560500c2c03403113095401c590015035001c80300042c1c140518040000540d60782005810700c016911184020201e1054010542c0c01310f03540d84007031002c0c0c0c40a10040c001d0b1450070080000b0f40d45140380081ca003040980c080740c0e10340c1c50040060026940811001d0496060165160302d41d040714411807018802d548600c0e52030311403080d0000c104103010030308500c1a404001c1c071000315542e0700140039140c03408071181503100004000007208540a68400540c0202c107290150410391210027090071240c507900031201500c0305008002105d170045910ba0007070103144c940789080c030801113032980030131341154001825a40c4803821006049080c0480d4401c003c00180410103c0c20401c00490203400c15480b00c15049a07105804222141c4c1400340c5030490345008001c12195114190840c01000080c0120400c0e548030030b403a0b010b86000c101040ea010a082c85c1182da0f800e07940c900038282969400074900702c4c0e410100c02d85402d6a03100c1540034110050960444c803000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 131391214 1250 131389964 131389967
    0x905102705031605060132060a2106030b060409030e01082d07020c19090b0301020c1c1715120c09090106140d1110090806090303160503042001 63
    0x10702004603c0ea03d607207041d0308040c80b4002418030b040380c140450303c0c034000b03a180203007005203e87c103880200400e03c00120701005042c0382c0000c0c090204285490b0310050340c01d000314044200440e00d5540070945614081c000d20004540f035903003181c0222010082c04c2c015036400340100309115080381c14050302000241010590107001000210380b0070741110300310302c04800c1d40c681e0310342658400010310400d000a2240d04008451074010002615244230403842d001c0500042e0140410182e05550280120082e090040203440c005841c1035010660380707442e5600050006e004005c02450186c14039041c07020003502d1100c444040c00081e81d501c1c0740ea41c00201031500e0300715411202074102d40c000e407c00c094038406600c100250b80c2005650404100c0786020440345000320b21000e4415012620f0400302e5160200d101c4203003541504004009596078101c203414080700302e80d0300d0382a402c000100401e6526082459090346290300f030050841c1850f4598065203440040290499010602d212006a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 131392464 1250 131391214 131391217
    0x51f0e04020108131a010608060402070506060609030a060f02121e070c030e030d08010f0b0a08060409050c060307030b03070909081204030e1002010603050d0906020a0b060607080409090510270503 86
    0x803038024080d801e4185c0c0c060569400d1803c248a128001400341c40400e80a1410b030084606503508040100500e40341c17202004400d0b80540b8506605204a5804c0c000041150240031122010900e0060b110082060030005800c001004a039102d0403100c001c4903401d24900c456500150b042c54900e013045050715080d00c1107040c1d19903081c0d0501c15981c20480899000b9406810f0742c05c561129540c4591321542603001707020b5801c00d000440c00700c0300041e03018207050b408060b40c280210700710f42c8034481200100d41554401d5908900103621030700b28003994102000100002c00360200104480702482d15007401501400e0b11084207083c0310b90110f01410721034601c0640e8148020600000c407444032071301900900b40e40c80219801d010716030050134814007810700c0504450080e0040d00c0710900c5513a424020440080415038840400d01c0001d0204520b2030180002c1c1c041d0403000180405941442860680340c0011800050309040102203030440b0100e000d640b8841d42c840a80c0e407454146000c9003507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 131393714 1250 131392464 131392501
    0x40e0d0f050d060b090102100501050109060c15020408030703020c0f060403020d1506080102070c051f05130902070f0201121e0207020a080609060718030203070b0c01091203051f0e04020108 83
    0x201400c01c400032070000131140040c0040a026001c540102c40340c12001c905991091180c14085441d440c2d0402826000c0e00c0b1221400d481851101a42104a0580c1c01203030000c0d00034202591000c0b5551007015010450540040f6046450342030496458001403414419808028007442545401c00c0402002c5022801d1602c2800000d218842d101c48640e8001e4000c07003025107901c5010003000949061104400d0065040c3c5031841510928001044da1030703601c00103402d10050b00045e00010f00d4282440139200592044400511080a0340001861101c036070880c011624642108903045090b002c91114450300e21180c05031711440980001100300243da885041300e40526801c00003940c5010075614032079080d50302c4000245100c034018080c21042400029095440510280212800000a01600444140089480246982e8140d0042d20311410080030a1b00d403420300103046000d4030800d5401c902810400700c094980080240c0911010b40041d05000340600030668908111240c3d100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 131394964 1250 131393714 131393737
    0x1050f072c0418060c0e09010b030f040c030524011706041b0f0f09111207033908010504020a020c10031116120c0b06040b060d060b0306040605040e0d0f05 68
    0x4000f412030901c02c02515030030088a00044e04c6c1d82d0b83e04080d01c0d140007002d041c0c8207000c0d40c46040d56104000c50702d284030050000c1d00e00282020300000080d60810003101c442010002d1224442d0b40440d154040442c107030402c2030360304004105010200c50008242d84e0090b00f140d03c02c4406450051807030120542900701d5040380426040210b2031210b2682030100310b500385072003000284ca103107103035084900503468813006448114020030580c0c2d1090b08171220788610800b40c05500000e00c0342251381940005416010500454143c4449030380100d41c4c207004140544040d407a210040d00d000751101c002c00a090700c03a01607910801101031181e881030f9001414401696641d80c1e007034030244071406050300b041386c0d48000010080844e9200d401510102075010910800c15100c070806c1201074101c4006481d04054103004400312100b02d802800010490041c1880c0d41e4145801132009a5242e500124080c41c24004020142c0400103a03811000d440b40c50408000010480106c82c0b922503066842c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 131396214 1250 131394964 131395001
    0x1505060108061908030a030614010e010207060e03031902060a0e0105130308040c171f020f030406020a020a151d0f031c1104030b0601030b01111905010209040e01050f072c04 76
    0x50229405030310032310644c0e903404801c1000a803c000111000180c401c0f01600503044400c0c20842c0c18004d00490040b54002400c0c4c0342000323002110241440d82058039200141d009200344496a401813141c080341c040f00d07130002d11241c50074803085041d11488140040030007581c68005400d00c010025080050240200c580d890701400341c164079600c403018244402070308400b14900a0f0103c4030701c221003031584010101401c50f40d0355120a00250411042c2c0c2c0150b0041c000350b64001216180c040c4a820703509500040c00d040203004042c002c10010190b84d000e940141445c0e024020004103440e03c524600c210b04064104800e4010060140c6132445806481c3c00318022040140491400b40318a00c207a80821003400c0c1c1200441c0c1183d04100b100002c0c0e0000d08000b0000d940b000c2000d10554080d000151400714410302150840349810b00045080e5520130920030342480306299650083e034103103000c2100313a14915210050200c4407048280000b540070b0300902c2034446420880b801d081414440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 131397464 1250 131396214 131396227
    0x409050705090924040b011107060503100b180f01180305030d0f020a090302060a0302120f0405010b030a03051207110a0b100f210206040b0408010603150506010806190803 75
    0x41d01603045819480e1090a0300d078001295000500100d5842c1100800e001c000074449606000051551030907050410084e013a01481011080003140c0003010030b640c070b030740d42ca10700042149005086a00703c516418410050140d0480e441c40074243d29044c115a007038801d0b01c500006a402104801900c2072703405074070100105028000c40500000710442c40240501c0b540e041c0b49100701c1c407a031014640440c1c0041e00c14030140c1001005800300c24024100140741051140005020b010211200841c84410000b080108a02030146009040d0145c004080b00340c40ca940181c41401401e0400d004403031400002444540720f148155410680813007612880d01040c1030940740f4202c1100c141104601e400000101100070b10110401c81d8014090882100741041e440175080d002c00c081641d100c103003401701241440200e40100f0051030024000030b4094038514060b803030343c40000115210715161004101050741c100c090298040c8e8100c0d004403489014400113040c900107034100c02410322011a24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 131398714 1250 131397464 131397467
    0x60e010e060406020c1501032102010e010204030c08070b03070c0803040609140303040624032301140103060506010306030b0c0304050a06240b07031403090316060b09090105090304060f020304090507 87
    0x10040ca4405d403041d290185d6aa4400c652101c00a2000400f00609484c0844028004c1c2031010080c0200d40300114100c11003100d800d099810542056580d120308000411214004100c0e60b4001c0c2092040c1c00c1c11480d045030b0107002c14401600140c4101000030018082208541c882d4800c0d6900c110380c222808500d02c045541d03a082164105c900c1da140101e800e890314100c1d007400309045150500c450b069070030b540d01d0700213480e00b1030f0508000c1c00b542c07841c0c56412482070081032644260302c44007900c15895401c103041600c00107807442e0f05246c6041814000b2a40401034103601c82085041d0b075039240c4a80c81e0107441c03c240d52901600c20303498843e01400c180c1c039820410807100c180c1040c4600307403900c0d24140401c0340b007542c4000300400c6800d120706c1c1d611442d44014690040242e030603642019458007034110f900c5d0b10900701300d0301e2641d5051000214074002d04440d41288030100200854540720041075542e1285005820901c20349442241c482e40c4200304541c05031144820502003801c0583d0b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 131399964 1250 131398714 131398717
    0x602070b0609190903020a0209070503040c06111e0c090c0a020c0306090303040210020703060609020a1e08010b0d0605130506090603061015032a1209030c060e010e06040602 76
    0x21221690200c000c1101441e286440328011942800ca842108100c400c00030002d10b0100300840030746c0034841d03000740543d461082040c42901691225640d0346428903100e4564191038004109000c1484c10414481000044021300c40d10704540c2030045034031001ea00d6161005041900ba8040d6180042000d07880c8140007409401034141c00300c4001c040481c04054a40000311805084c0307030310520000e80580b900d40314a40c1000c0490050311403250726034a540081c0c5081d90841cdc1884c58000604481d16a800000d0520598600c1001d460b03101c1c1140c002002c0031010322134051110740c003041c8803c1e8081d040d40828000c0c01c00030400e1000707041840c814000307420100c4440b40316044460000c1c66034103010913541e00c9101e8041c0f82810850805000010003811907428108045d596040301d0040c2046848070380c0800780584803104d90482d9000000c09200b202c0d104030740c145003001c0035034001a8000240b40c010710351260000c40c050380c4061360170780140114440289144180414041400243c3e130 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 131401214 1250 131399964 131399977
    0xb1303030908010b0904020d02060408030307030204030c0605041d0a1508060108010f0b0a12150501141002120d09080c121309060605030c03090709050c040618060c02010c0305090901030602 83
    0x71200c207111070703484503040d0803940b140c01202c4d003000071280003900514120b691000d00600c001c4c1100e05140d111241c09207150411107085020a500140038010301040c858044010309081c54101e10313090a00322203612801c0c1040c0c81050000c040c1005c5044000281c00c000e546180300503151911680d6181441da0707841b000c2c405c4090f40d503c0e00304185100c60007401007500c0c144c5c2c09040300900520782040048506540c48064408900754051040011440d020b094000c00c1c0102c800d08a180320039040120714460301e01d0203020740d401b80202881c0100c1040640721280400ca00029400f00ca03801e0082591040c5c820700c084c103002d854401c280c010242c20181c607218083c03180c0c5c0320304c007903e07021b0b541c04031000f6000d19000304a080c400079056003c040021a8004828019a18010b94991042054407421b681100c080a0080790601c030b00b942c0000b010612019020050055616001c400707400402c0030400603041000d17801e0440305040c003400480b03804510180c4417610030b60352410500000d402c004c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 131402464 1250 131401214 131401217
    0x50d051806030603030f030a1e0b010e0108040b060d05030f030f09060a02041202061b0d0e010e0109030b0f04050304031703070f030c20100f05060a050a0b0915040b130303 75
    0x220305000341c2800d5050368821000940214070f03050003100c1048498100510f145c07203103916400039034100100549807110a00031b9074008140030200c1000500440120f814290400114104000114a40703071543c0303801a000365640c0e1008180d80c00d005085204143c107070740100c031002060005100c000d01c82e2504c201020025240d89480ba10002016071090303200700400321062003000340161074200b00900c50300d1010341e0000e80007200a1400c5090032241003841e404a004600004002d5804c00b040703c40140c0c09281000d000d0381996582d5500c40400390480310641340740000035080040800855001d0360f0000d00403284950b00143c82100c680c021148000081c8907a84000c4000e030082c00780303000a880a403201105110000d07103251011042c450302c2c00c0e01d4400c07020300211007281441011114060140c011072030340751100c24003a00b8402036010714001d10100004205011050b81503d442400407988a0348102c00100307903180c0e9000740d422205221600150808562020403001c4040b41d01c41d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 131403714 1250 131402464 131402497
    0x201060503070e040b060d051c09060309081e0f0c061006050c3705010603020405151302090103022502040c0219031101060e1311100c030e0d050d05 65
    0x65009064840c05a44194070209030f640e004100000c00d4800c45030b51015006e0600d091484841d103405140c50f468900c0750840003291054101c4d01e691043c141d00151105041c14024204d165942803680d100f200d81e40a94102c2d503074106400d18024401b140e1031010a04002621040d5001105440b40800d07500a100c007500303400009802e500a200380d6801d071104801514546518880b0b04103102c0080d1800d60740b8104180308a0600c180c1d10b03040202850084000241050441c4140b000700c4001a01d00c4403401c00901c401011640c0f14154400260010b00d03015854820310707070050b00030f4043c000c0c3d202201c06401a513030715202421200f02c010140200e40c248480400281d080e42c640c01400c11410854006e0894040803a00a600e010f40368940c6400005110365900340308501810141c84100355005500500c00501c07080e405000305040086030510352802d0100e0b8040c1074070074010300007418030945a0a2109598880c0900141c10386c211003170b280580005500180f4030741c004424054250003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 131404964 1250 131403714 131403719
    0x21b0105090a030e010e210102131d010501120207050a03031b090f05060715020c010605031203130f14010504051f05040b04022e0c151406040c0c0212030a020106 71
    0xd08003240303a0140c50f9140320f1032a060044480030007054086c0e404c000c403440284001d058403041ca1003449040e000040e298030074030342c020104c80d01c160b004400c82000001c3e20100c012031424542d04494003400c00340240342d02ea49240001e4014000c2c0070b4954080c1c8503410044c550507402500e0010801004601c00e0704403840155100b1410b402007001488600905000c81d00340000105440b5000764140310040d01c9030950070b070980e40144980c900d941d441d9481081141820030503409000e005000c2c0904500c0d0410b03120302100102c2c00054040641d1000c030805201c290104102101c043c0c00083c0903600e8142042903407104110f03c03c0c14000403039070034040380034590700c541030080d640f085900c122910b4540070410b14802900341e0050303a0445040c1805042100e411040d0720b44100e1f02ca000c3c504001c1d04060586032444000c83d182c0c14140b0184c0b0207444039a50900343c2c000c0c0c04550006018080700800c45500009040007500440a142108854540003010701210780f49036000740072058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 131406214 1250 131404964 131404981
    0xa0803181f02070518090c210105041103070e0108190201050d0c0f080c0423011e0906021209090406090c0807171009051b01170c0d0509010e030a030b04020409021b0105 74
    0x341c2c00c8074441746540041c0d03010090b40c5001d11805040c502c2c0c8059100c440c40e0318420300342c00c480041e80d00f121022078015100cc898201404144004d201030440b007407140d8502283d01e5180c1504514902c00306103003480b40411a03002da030940307151076510b450400112202060191172511104111804100300d440040d1b00300c54070100f00d0b0156103512a8007450100c54507100a0079448020180d81400401e440481e0505141c030014802d024599846207100f902e05030b001380c2440c02e0311284490b00d140412201c0702a0b229031a050f50001ea2169000031502402e040103440c030307445600865100d01549900040410300010f141c02925400010340e1000c074038441c03d401c2181c4402c40020803a41000251000c82c45041001c00a001c0b0181440d03414103c07111007645040404680b030300c9000001043d0001c201c1c485124480e4012440b2000b00008212407505036502c1c01111001c00400d030320b0b985482c03040d48480d0107440041038921815034031000d0000f8116070481c00c20b49071074042d41c03925001030a00d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 131407464 1250 131406214 131406259
    0x120501060527030c130b090f0f160f0e0d05070b130504020304020109170a02090115030c0c02010503190f0207030f02060c0906030f040807020d06020405030106050a0803181f020705 79
    0x82d002401000381290900500c2582070f2495a0420216600c080010881d00ca641d07007144115074114101c405440d28080d0786500080290040200d040c1c03941c105400c090f040007104102c0102800c004400103130240020350f00b40c1b582100141940528000061300300c0c020b0002e0020104450721640d8519218020300c01280800c0718043d0015182c1041000f00e21420340e80c004245250303106640703a950194010480c08602a44020303043c1103000c04507040c499162055000c001c006103020b80188020790002001404040c01000404c500100b0760040da040036405142c62608401041d07465190718100600394424168590015000e404009551a0000c00444050b03110003858242917854980d070101101400901c120340610040100e1800740c0d42e0980700e1b80340e49100c0d03440540e585050505050a44c1d143e0703400a8001c01e181001801041c4011055030600c807480c1d040e141c0c2170b107500d030001048507403220343c0416084041111140e64035030100d070510a5480554030391906140703e828000e580d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 131408714 1250 131407464 131407537
    0x90b0f01020a0c1a1201030506100b19050309010204080604080301060809060907090f0b1903050c060901020a02040c020c060a02150106050304050c0d0c0b040e04060e0c060d05071205010605 83
    0x105501c3c02040c0400d10b00f81c10454440004140401d0801900c0010018070540c2a0004c1e184c1d03a021104202d6030051007a108801390107845110b90030103030b0b240642440d2a0751081030a092100c04800204454000d505070307401048841c0032120079040c01e00f48841181d1080c0070703913030001e8020000165800e00028080340646440030041c2401c03440c00260b0350003844c101d190121b07a19221241c100e03965946100714004111000d1b03e08a9031480c41c5000e5152140b00f4071580d004540500c100c0c0c1a036030b00842ca1500d11501038401061400310141c1c124200aa01025070f0b51040c00800e40600e1243d000a00384100340b1802c43c15080e40e600d82000b520103000441d001859a40704030300c03004817410949031684400d440340c025480001d440c0c5454100540064100280c1000e40a08004c24031005010350000c0004d42e502801c9003040e21008185070b13201da040440c00443d22000450581407003a504030341c038501800c408210740d5840700001091584405596003607a401421401e509d40303000540d0031403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 131409964 1250 131408714 131408723
    0x40b011107120201020115170f1b060c1006030f030305070e06040b0c2a010801050a0e0115020c091302041a010923040204030501090312091104090219090b0f01020a 72
    0x30041d1801c52500d41071040c03210b00701e04554a84038103100c0910345112400180102c000c0400c545002c1c140030600d030140a008040050780107144111011092111000c10314409684040e520020100002c0c604090704528101072850726400000b0f020100c04c25650440c0320750b4080c030241e10f074518101c55908501c00025842070041104220b2622081c0c010704040f155913050724810242d100076032420440e90002075805c0540260045000c4da41305100d03a014040444000000f203081000ca000014414000c800300c0d0384003140403c0d58a402003025800d01c020041c500e440303524202229603003070090004c049010303d0400100034009001824000e40c05801a950f0032062441d00c0c848a00d02c41c443c0310b8006060340000c03881a0f064569000800c051030041e000428a91142d240c0200b50300c54982203810001c2c6418210070024120b0b00d80000d1100c02102e000c2200015070000828408a80f810001c42ea9600400004d901a1035000300c007502d2011201600b44a03400790059880d007490707460040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 131411214 1250 131409964 131409973
    0x30504120201030b1009080706210216050109030903060b090402090c03070e0306040506070e030f030a260f012c01090c0903020d03110c010e090a0504060e0d0e040b0111 74
    0x48034030068150108014014035002c10039044500c04210740021031105400000c001c1c160038803101400b000318800409581c035100040c3d1000c4101c2c80e03004e01c2e9107400d00d0b810356000290003210603100786041109a41010003005111542c2c50003400001051208491890038990800e0580ca080440c0c40d110310f4002c1c00003881946c0c0c4000c0c101030341e80000e10710002d0140005004c1e0362500c081092921030303481417004207100d003070501002e0100050300b240c01c1d02c01e9018529a00780b0404c0881500c820450905003204020388880b0740303d1480b603446c08074080c4055400104004401d99480f1103040f03804160440709090b074a480f0340608000003d20030482e400da40801002000b519620400b620050751403c010a2070310381e40081c5c285540e41c28140c0c000344070303203c0c1491841c1d024000490202d0090820041c00c20f800804182c040c28004e00000a29540f50000740901c54590800c555101104054441c03c05038a1405010441034500c01402a23107014142d0441c0e500484803901d40400c0c1e0030041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 131412464 1250 131411214 131411219
    0x507080a0504050f07030524010501020a080c01020f070f0b0109020406090e0613020f03040b01060e10030f0b030d020318060f030127050114030609280f08030c0901090909030504 78
    0x25010740409031007100c56100340741507440742c80000c2c4100400b0b548240f02030208074140151841550f001141c0303180c40394640000401c0140e030005042e462066110100e29241c0320f80700b490038024015814a0f40c80a180015428200450318500c000391a1084002d0000c590f00c501588007240554001c00740400c41141c414460495400030556005030001c1090f00010308240c1c0b00740903a081000064070391000482480100705880d00a1405852103281c1208001f01e50070000f8248452204500c080c0355680e0003096207071015800901c4014005000c030b500c55400e01e5030080d50307580048210b680501140c5000c511600e4410100d0708451000404c00b411039003000b00c500d5000312600340708807421412018050f52444070740a114000c00c042248540380c4040f0401b41810f1050040401282c0e800100f0403a68400e1281759140000d001c00c07411030030021240c500766414040000d000fa00444001c020040001d501c04010185101d003a13a4551019a41c0c60902055415040009010890a002c103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 131413714 1250 131412464 131412481
    0x60902030a080c2a01030b030c0301020a0c2904030c02030f071811030c18061303060203060117070f14120c03101d010501031a1e0102011b0e0f03030c0d020d12050708 73
    0x80c14081c3c401009c2d150510690400242241e00c0201e2000120b259111074000340301d00f5a2f291592205d4141e0240058000890300c540c912400500050500c9241c06ca080159101080907074100d80c2591300315101c60340c540066550750001e0350b10010f1100d00701810800e085400c54140ca0043c0101840c0c1d50900440621126900702c0c415015a000030060084850240494004c10300440c0605001a503d003028400101241c2121201090550b4040140a18907a108204904554003841c214040902c0c203081100548190015048141e09040034841c442e449040118015011804101c0300707250b841030032105c1000041c00e081c05410030351004200e507500a400510000045406280c0381c902c03200006050305c1211042250f84028001c106540e9580911074801004e500c06e402c0c00301c801c1c401030000c01c401c6007010781a011307400190316150162800c1054407804200c20082d502400039500001b50340d6009040d40c4400140c03032816810824000740305190049900f0364502060b582c400d1207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 131414964 1250 131413714 131413721
    0x602010c171e131514040b251d0a030201050a03050a09020604060203070201090512030901030209120a050d0f05190f0c1b0f14010219060902030a080c2a0103 69
    0x9214040c840039001c00c00d92582c0b41d08203500c02ca03503038080c0c40f040d0f010a0420507401e02d00c5402c001181440c198003101409210021a81e1107688816050381c955110318454810800140001d8116650341c0103212519030801031341090440c00950848c466481c242c10040d412065120190100340100310800c41302c0c0c869005154010044400803d020406d0382c045030442d0302c150b01c60750040c0c00200f00c4c0011582e0040c410700060100300d458030b241d8142c3c4c481d8641c680c810700c003015062590020702038541d80c845169980c06564a03c003900e0182001c2d041042d2181106551000010000c000161480b40a58199201300b100106080031030f00620100340d03110131031200c900303080c0300030369443c0c0001441201003900820302100f040400c6603d08a80780ca108550fa42040a16903071228141540340d030b0006100030407944060301e00c0c5241c215801c110340100541d10002c0c1d050b000d0640e425091000c024010a895110441220710070082c0c200c0e07039501c4000714404440b141040e8a40100c09610030741 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 131416214 1250 131414964 131414971
    0x206030a0b1003020c16030809040905190501090213090302070e0c07120306080706050f07080a090308041412190312060f080f011104031127040515010602010c17 71
    0x84009a60441a000030b0140415803100e000003035000a00c41c1200c080502000c2c040f400380c0c49a03070150724216643c50503940254510306006c0c035524240e510620004110002c0020311040d142a000c0b840d46c20000d018040d448000d03409000002645600c101c0703540704401006030180d01a01c0e0842c07d01d110806090800b82100c01350607400d02c108004103800c1640c1c100426004e84000903028a8091240c1c00c2100c50381c8140d00b070000c20b0002c462040091000c44600305d03402030300c040d6074140004003a0f8030503802d9000070b448908041000302c0d85091030030007072080e54403c880c0ca00c103208000155039501c003076526003013420043c102100000030340900d100c410b80700000d040c08942c29032982c101d190300d180b050744106ca82c0c3d403240c4802c030342c000800c0c0b00c0c0c9080001c030f103880f8070b140900b192202000d148845604d02d01078020000d114401114040e24184900504a00407140f800c107414400d03910a055203075200502c89170800061365034014440e00d6120b00c01d03900d884040305100c01015002a2004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 131417464 1250 131416214 131416231
    0xf0206070209090703060e0f030d1d0f030408101b0f3c14030106050f090603040f020103051620100501080604050d021609090f120c02031204030f020603 67
    0xd004050069861041a62048103444010040070f45581400d1003510102d00750742183d50440d0410700d00e5403401000710781840352800300c0440d118804e00392a2102204101501446018404c6000c4050034048024011a03a040040781c500102000721032017210447c244165584040042d06454540102c1209a8071243c0d410b007013a1072080c070b411005420901c540c0a02d41301d842c62401d40c0c2d0040317800900341d00c007412902d040d054100c0340305401052440107021303e2050100104000b1640c1c0c400c1812148513900c003400c240c1c0c6908041c90405480008510220301183c10700d80043e41c40030b0548010a050b003440e50342d01c04054140c01414503080049400c1c048140605860314103106202d00540b070013003003000300901c0e9034942410058200800c01443c102150441c1c2c3c0510303d89001c0d440c80100741d41e480e1500061404552070403c0403102141d00c02003070901d0041500040c15008000c000300d5034000d9058440805112040e04924480c45c0002841c071050120f80b107015091443c051544400c55 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 131418714 1250 131417464 131417467
    0x8040201030609020d020a11160e1005100f020c031204270c0c020312030403021507110105010f08010605040207051203040f08041e0501031b050f090a09020d0b010203040609030f0206 80
    0x3200030f0b080030ba0380a8015009400d03000a1501c90003944004036448402490014141502401c801802c002e040b9114000e881509540401d51000302e5109580040070001d02c541000c110320880586911103102004004d4014150014010700b0040340c00b90a444045544500e081e05080d144035041d4002086042205800d8100018050b064440c02e200c4508035228002d400302c0600c1050b290042825230a440084c0c05d005201c0000d070000b46240840000d240140320300d5035030f503034100d803202c002c0c0308107500e00d43c2807400029036203031240350010640710034800074030180e9100c20901080e48503511005002c0c0d441520106e00202010018640103840707440e501113000b0791500c80c10129003068018420f11400a50380c10301404016118000405003801e080c0103034a909038409502c0100d00e640082840400a1030908603007191080b240c5051000b007a4089050700c407072220009410004407100c0391460a44150101c3d80004261012a412941c070203001d242142d41d0300c0c010100600081340c10250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 131419964 1250 131418714 131418719
    0x14040c06121e060f050a0f090c14070c0302030c0307030b241002010203011415070209060316080a050f011b05090d0803040b1608060d060e250e0a050c0a080402010306 73
    0x1030b002c41e007040c20201c0c80c081441824402103640700405540310512075441908200041c201c00c141d41411920480c00014200c1000801075403e01d4020346e0021011000140301c008210801d0142c2040d203009800301ea80d43c54085042c076a0303605641c00050b01a15407000021040203628040718814014200d1444158420744040351f280209216a0341c0940d40100062084048180103420b6800045506e4a050000c0e400c4480c914441d040000c1c4c041c51301c010018480b44c81c20402903800300103c4080d4110309584180080c0c4030512403008407560300070550301d0703210a1014012009040000060390070707004004031090307480d940700181c2607030003124209420021a40c0341020354840c2c4e010700901d05081ca0300ca440507448000c0c6800c03035410300410300d003070108589420442407449544818002607140c031096681d460200702c00c2c20101e44042c490614860299804510001ca41d40680400344075142d0504510582d00c040b40c0802000a062000003241403103a0001c03500140181400100582c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 131421214 1250 131419964 131419991
    0xa0204150504020a2c09040b04140f010b090c090a0e09070801050c041403070803040b1b10140f0c090103020703050d06030804060207060503010302300109051014040c0612 75
    0x20064144040841e5000024400d0025072a801c95014400304401c8011405c94000003074001030080d101400501c647c0d80060104003d0307140b038160803408442114041386401000301c2c081c3c81d4079103809000c1c500ea400410710700f8020809551a940c001400e10703280a09002410881000051003165144079100c00010031140038403400740504503440305c80da41c6908191300c5128400f050300c1d065009602110f01002101408020b07901544c5000b41007541d55070f00581f00c82a85034828000082601846004100800703295014501c50385010b00c130184540c0c0c0c3d0300384c0603400210842d942c045600e01080360899542c0301c0e50042c003456100b402c2c42402d100381c0c1d100b2881110810f401c211b030124000141800142d804211080040045240103444d6604541c041140ba00f0120420810820003620044000480710150344800e030042c4000c1104c001c50b42465550f401c2481c0340f900f540b526060150a80142405480e4843c2d500450701c1030350306280003400c50b1810300c9192400105a61140401500c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 131422464 1250 131421214 131421217
    0x9071404030524091f060504140601081003030c0f1e0b0601080c0901120c091d011505031e07031107080304120e011b0201020309130911060a020a020415050402 70
    0x29409007009042203019a00039052843c40303450340c00d403030a030480e0070441e0100c0300041c24550040c03a941c42e0a0707526491042c01001d40301c0e80d00096401814204001a00324109407540e104400076070b100203194032226503038010304800c0c0c04050001054031841d0804101155402c988251041800d803020804910480c035001101c2c142c00c8038240350042c1445aa580d100700703296008001d2880032031414540c01c0c00a00503a200307046445400c0d450301d4001c0340c4640540c445400801404042584c0c0501c0c840300300441d49024094890725514081038810a144180107881c850b03180440d0100500c1d105c110240d40c0b5a000508104c01c040d15000700070b0f1040307810350142c4521489480301c00c1c0c90b8182890b00600200c01501c04608002132041130341d04070b07179021151085070308422003210f00b02e964030b000407800e510610070181d03040b6020b800d203100030f0483c3d0390000c11b00d240503d0140d81124129000c1103090300c112002040103074000c1903407502615203503000a0758110500c0a032031106540c0c0012406a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 131423714 1250 131422464 131422469
    0x31e16140c09060f3a050f0a0b0c160804141804050304030b0c0d0c0c060c020601060e0609031005071e020304050303041815090204060f0e0d0209071404 67
    0x40342a000506896114104411898540c040b1200c944a2a0030f034041220702a0281c1c2041c03041641000e560507120402680c18224260624124441000c0d50070f0f41c1845a5503a804862034800d03032000700900078001c03030b000d108690320101d075050f241c4644c0130a42c810740080c01d491008190b050004000603c1450041009240310414100a61803039010071120403103021900710400100020400013980c04000c44090b250700c0f00720400c3d15144d8080c52040d0340100610b160480d460a074144031525040030300e002c80ca62181c0c500f84591800d031b0b035003240c444601303104090210305d050301d141c116440c1c04405031070701d50780107400c8900c07500b4444480300c10340c3c80542e00d000224801c4c511a0680b15000c240c0300442d4a15400258982450400841d949200314440c83c1ea460b0855418100250700c0b0790080d0300c4102920305480c90858035410706800035809403240401065908841243c4c25000d0b081d15550500024012246060700e502400300100e8010003c00c1003080c642503107129080c0340c0703001d08003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 131424964 1250 131423714 131423723
    0x41a0a050709081603080c071a030109110c07050f040e01090809040608030f070308060406150314070f050f070501020919060206010608090604121b060b1c020102031e16 74
    0x546050949010b810b40c01c40350080f00481e003046a082601031502228081200d50103041343d41c0e204070301e01400d401c1281640000030341812082c0010000344003c1c001c0c506a0307084010070440d051755140d81120a208080c41c01030250401c0b00304000f14a00440c10001c480b501510100b20780000b0700c042400c55401e44003c44003c14082080036003820304d03201d20006084100011494800b00103024240f0780200f034402401c200798140000d84a0311203411020041005141981c2c240966100c080c015054203144840519503000010398401c0c031401c2c85009080f0b59072503241c9010540100301491b5401248103503059074003040a40119107c03855030307641c2c1c10041081c020310b42e030074030200905101060307200b0010041204148011100301080c3d15410a50084840003800c0d48118240c900d401748882c14807400d1008a0010309014190f00000d018100403036010703050307909061101420045114010f40180d02c14028a4111a40150304240c03100d070001610b400e00307002032a0500111046c483c01c85 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131426214 1250 131424964 131424971
    0x1030e011514190902070203100606020f0d090f0e09010e070b25030e06090406030b0a020a0e0a081c0912080c0c0d0809100302131d0703020a020c010503041a0a 70
    0x14904003190403002c03103076080b205030840c08608028940d00c151203005140d08680e0006182c403c5680402024054030b0300203a0601c45181d482c00043d4550520590241d4a40207505401040c1e80c8131380d9511081d00c2a40d0810200c10303003072400d8445010401020070b0480d40da211038461801000300000c60080042d4258143c0d1060410b442c001880d050003d440d03401c62001c040b100002e0340050110940c04000e1341c555440301c01c954009405030215a00103020740721010b05004400c0c0f00c9030000d00c0380300d05945810f40b24001d51000d0203010b5030144151a40c58014084954011f25030702d501407507004e440d00c2c01e0801c9548811070108038052401e4102c1d0044400a0b01060890051118061920044640c2818190b503515040500d2042000c0103126011480c640c00060f03011394190f507040011341000c0d0002584400101e82c2c10345450303165504198460300003e0659201e4000c07600b014041d68060011900d02100548480d003016004858a502d8103441245d05c400c00c2058511a152851011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 131427464 1250 131426214 131426219
    0x50d0209030613120305060f01030f14010f170601080c011b051204030b06030c010e0616061b030513080405010c020d05010903022d0601051507150b030d03020405010f080601030e0115 80
    0x404840c403020308490181804c040030000c123a0345544600000074400e08010501d00c0500d10800d0040581d00315000701440c030b2900120780400c02d605081c0a9030005910340c03954542a154035940c6520911030050306030301402c003159465104403c001c003640c15200c03019040c138803256285424038540c107000b1074141e84045020418000070400c2c56400000a03006400846d140400003004008070440c024041c4000081c80380503c00f0401c0b0607100c01390416001c00419840020b0006a0340d4900c00e100300003410302010030342062707140104410790b9510148181c9058508401035030f0400006034144d92100411002a0105e0000e00400030f01500c030b0ba000d09000b06420300212810075180f408c1c4022214a2822825a00382c0010320a05440003118408500d103100b112140c034511800c034006011990082591411000c9a000b000003201e0460507101c18113900300c4200e0407402107105150000d5601011840028042c041c0c1c10382052040c540410080200c003e071358203480701c510104824100300c0004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 131428714 1250 131427464 131427473
    0x70b090a15090b06010315090f02091008070503010311040f0c051e0c0d03180206070510060603050f0402010e12060709031505100e07090e010f0905060f030d050d0209030613 76
    0x181607400c0410300308200781c182c1503c031000c0014004020700c1c1403640d1400403d560703007000c1e0308007070003400b10500c00e00c00c4108a420000103900807007a26400b074141c100562030894060352030b0511808051b03807400d096178a035890f8030160321102400c60740c025949110b103140d400828015120024002d0326043d0350307401d2040002c405d00c40c0c84d503015680d14a040c442041707503400100f030800300c0d880540740110300404021104503140c0003059000754404c0340000d40c101000404585401e001009800c2000710540d1000c0607020740d00100d03030100c51124003100180056004000341400428003402c100b8220204080b003914148041da40b103000316070800b104008102c030382083c616251030030714814002410003103c2c595451b111400384c1000f2208441c0003076038203807050400600419000032500c042e540c1d41d00415040b00c00381e000e04122181032900003200d43c10141a0b206031010007034000c1c08151070465044803d60030840721204102d401b001098056541040000e004501c800300d482c0703064845182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 131429964 1250 131428714 131428733
    0x7151118030106080c040f1d0d080106020601080c01030f0f090b060f1207031211160608090c0102060105010e1206090d17040b22050f0601030309060507081c02070b090a 74
    0x1440d510981c189003040c01062800b0500c0d4440410a4802250510001e4503d1001c2d1440411842e202c03d648904110108800201c0528020003502d40740c0080e42c80d91012601c90209000e00340701a405222400b059500c2540902400c40101c1800603a4080041c04003050350664081030310000b800c43e0500000c1e140842c0c034400c0b003802c02c4801c8059208041e1180e603d0350118400600000c500c0c0e80d0f0a001c9038007441d140114800b200c030540d03602c0d4000c03500440b6407400303500a00e000950500d002401c4164009800140340034140c0040c01a0303841e240044806003010510540c100010402c0500b81500810005008410300006801005041d00300140f0351001008142d084241c0042800007242c0e00c490350640207159503101010940303c81c80500006810040014254822283d01702462031000c201c56059070702c00d56440c002c10760f56000031540d80c042e441c4082c0018034104200950700c05155080e01420312002000b43c1449141d8030345a0003000f00302c654110540084a009040101004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 131431214 1250 131429964 131430007
    0xf0c110d0c030204050901020a090b0a020705150d140408120901020c0a03080f1302101d060a021501230103020309070b0a051c1a0f012304030303050a0b0108060105071511 75
    0xc50404109d40e600034400e100502c50000c14440020701d595000d8428030818003d00f8010b0404d58001c0c510301030341c0980d80d000d04054000d043c9801e5089490314403120001d40502c0c0c000d0305080c00d264801050b03008241000e4440350181d0342c200b207030301c180d20014042005090300a8990600e00d1030f1400c0c4c00c560a950090100a041d06c1e100d050030010b903100c408600181070f0500d040c04c98410b8030002c00d815810036165940e4410380103e4041c94940c2c0c0020581c005403004160341c031150760f03036010a4460343c00750107200781ca420041807210b680d035100c0e5000e0b40c3d001e012001102c2c111982c5108007142944106000000207000280c2c110b054105c1440041c0c826030038400410034a4501448019500c18100c4114480c004040040b1075036842098007060a032041c14500720780c91240010342045501c5848110003082c100740025104440a1003100ea1000b81a10355218598850004450581c40400d040f1001a04803524820101c668400e03200000000b084c0c3c01d82d1000c54966160340c10080302c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 131432464 1250 131431214 131431231
    0x2b05010b0a05150c210712030b03100b0604030b010b0a1e02071401030b030105090d030e01020309060612120a080402123705030d0b0901080d0f0c110d0c03020405 71
    0x100710402898466048101003400b1507034025484000000c2c0c090700708003000407908203114040314589901000c04004041c1544607440d0400d8172040690103400b65410b559001da0703d500310203240a6208030640003403e900390000c2c540c0345070031b8803507403503c3d12401c1c03c0e04000700600f800306a4404a6804c0304040092070341440a01c1220384002034001d66401180c0222096007410a03041042c0381d0003500400343c9103e00400a01540c5000002ca50f52240310000450000c0d05280d40300c03c010b40f0601c2202e02503180100a400e05c1c0d6a020300b40b1414140c40340d070003074040c4036500110151400c840081e12621090741c0e6143c03820304007801001074000d441c0405254030340040007540c28030f15000c1000c078014099030041c118041140c1c0c000252209000c0c4010781203000c0040d0303424800380680c1c0a03010081d400c4550980c642d0300c2d0600650b4a0801d10f8003034010610314804605d88a000e192200c1000d03100d1a102c8596080041c0403c6400c100002d0480d04c1360b000c00b0f024000c501e807074001d03d584009c88 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 131433714 1250 131432464 131432479
    0x2060906090a15060918020906060c0a11010203160501090c0504060b030a0906060b070f0b011406040909080d0c02160806061e040603020a03150605030d05030c092b05010b 75
    0x3006074403002c941c1401080c00c080d00e07078000142d100c2a04110300412a0342c3d020000068103400740040c0c0410310304220b1282403070340c0c00103102d490120151001422030000070030034041c560b500d0766601c410044030141036110030b1140d840c0e010b128030115181e040c0328200210b400b0300d040c41e00d01d00000a54005500c82d500700030b0180700c44204003095940c030240e203000c0480d04188a0500c60024680c1d034224401c20000000d190042c8250038902c1c9141c00d1140c440141c40780c0e031f07509540701000081c10100d07510040c2003108008061554210003001402a0062071034003084030454411a558486e0680168014901001d00d00000d446910014102c1502804161604400080c040000d48640e4150b0b2042e0014a090948542c0c1c0f008001d141d020b003601c103039070703459062420301b49404000c0c0d044a14284000450242808140e07811041d0003519094291f860f410100784982e0070141e900c0390060311080340f0301d10024081048440007000c03283e1400c8080d445041260955941c03c11050280a2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 131434964 1250 131433714 131433721
    0x170105070201050c180d02120d02100209060406120b03100e0c0d050d0f020f060a15080304050a0302040209120d0806030c0a030209010e04080409060b040501030c0810170304090f0203010602060906 86
    0x2c000202e903281c0a09400740c003a40800c802c00102d8030000002c0180d0001244801e803008c1e0280000d01c0c0c0d40d9020507400722280d4401e0f0a1842059102e403c0c21640c000c0d0341804100724041c003e001350a2900c510240124407034000801207842e02c000e46201c0001c841c2c40d00800c02001d5414010b086074842d0550321a4044440d6440f6079580c0c0d0500700080c410404680355949525200f40406060020f01c003007564500e050811a0b803001d04050013102c02c0d01d81000c18005501140042290100c603c041c00c0301c1c50043c0f441e02040004e402440e115600442c40d0303154040004024031103006441026100d444041c02c012092504c0c101c41420b140780103081ea06070610259a40315000c42c111045040780508642d82d52910a620340a5588128900d904006010400b40c07100e1010300203544007a40c0400410040d22000c5a0720741c010349500074400c039101d0052140034140c9150300603513203003407044a107010756800d0318104891014200308501903000c4018411664140403480d0800300741c000505403800e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 131436214 1250 131434964 131434981
    0x8060a0302151204050708070509041a0411040903080703110405011202030a0905060c09040f020924130e0f010608010b1603090e09010504050c041109010e0a03020a17010507020105 79
    0x490380006486a003401c1c00074840840c5040880302c0300712540f6401407050a0502c0c00c5595034005001c0d480181c06294030104040c104802c0f100d01c6140c21107041c2c0c3c0c8101a4004240341c1c100c002d0f10544921076018101b9400da119402442440c621903611104140307011080102180e0071000c03004480700c0200010401603078030542004900000240041c3c0d01e03120786107030000500c0080340084c0680542d4040060104044014002000302600c0c18002d40320714021071000c034410a801654041040c01c04901b0204643c000c1040942d000c1140030f1820822140d4684054010b502509504022100304800c1200b144481c40c0103048500300311601e541080d00005a500410400c1107034807200503010341c1454070594140c8001c103d84640c00c84a42490003240d07002c1c0400b01c800b56260302c034070b400100075030070a44200c01d060000000ea080c142090800112030507005403144c1a0702035040200400540da50b848458020840882e100c42210311042d100c03402d4070f80c01060301c070942e40b5080c10440c0c0c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 131437464 1250 131436214 131436229
    0x801091b05031905010e07120501051509031002031003050709020c12160c033e10020f0601080f0d17010b0a02100c02010b1203070c0b0319111201060806 67
    0x14545801c10549aa6070f44008a5014010a40c03880c403850411000140b104c5c803005080d400b0b4a49a40e480c1c001e4a076071a00711055450a100f420340110744030300c080d50566001c1c400350104c014002d040c0c83c0702d09900201203003660025546000c1411410b0420410007208010703110040201311010b5080004400c0c000d40c448480030088208100000340048011180764103092000344d00000c10707035034140caa080c040b803503058420325240e02c802c6014605420b200f442603080c0b1a40412500c410072000700109004003070310f01e42c40c690154845d00040101d80c580c1030001341c0c064400f40006164001c01041030519090002c0d20348003c1c407810b107401401d004c101803c200d0548105e011321503541c01070900c00701d10345114207900075642403516010b00c0069074107400100c041103007190301d17001d40390400d420f43c2d48a210f0403400130320940060504000010b400d101840e030003060140c440012920001c200f038243c610705480510031620008500c052146400080c50140215103010741c0c4d14a01140402c000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 131438714 1250 131437464 131437511
    0xa08031b040b0403050a170c0616090f031203200301030206160204090c0807050f010c0b1f03050708060f13110312070b01140303070b01030303050402030c1005030601080109 76
    0xe003180011608094600d1800c440c01042052015a0f4480d524100301c0d482d03100104040742c0e06a0f0071030a000d000000402610f007101c49140280003261517840c140358800041c45011010700064240c00114030380802080c900650040c400c0354446030701540b0003000c83d00800002c0c00040390319030b80200001040c03030a80781500d60590f60b6555802c010051405026611040294003e0134940c81ba420888243d0038801250b29010459202e1354560007000b4011074080c1d001800540c0008421011071881942d040e01300124003083c1c0180d104054816040c8450398000b650a82c3c4034910800507444100070060740000d8000c9045920b0400790b01220400c5901c010280400202d0000e5078225a01400440040d403284504a95540001d14024040d02c909108008000d40f901e040d01c5c0a0b81004400c481c0304541c8005a05451fa095030b509400600d8041c000707903014807a03481546020f448500c42c0300d905840e6911019200c0ca00b00c0001010042c05812004101d030a14552400d45103212a1907081d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 131439964 1250 131438714 131438731
    0x706020a0b09010906060602030a0e1012020304060b060a0503090d020616180504020c071d0705071b1206060302040b19060e0d051905150105100e010314090d020f0a0803 74
    0x14035240c0c0b2980ca030140c41030210241c0060b02e0064006012500000200140190340d11400303045580c00b01000025805091a4000309002e4400103540d41d01c0c1364002c0d03a005110303c0c0b000170404240c0e0082002600841c1809010903c00000e000d5401e0080092000800003032005144c00c2c40c101340005011080c0500300002e004038601e68100e220085025000605000703042103403900070403d603059441640c2d1040034000b4600d40650703100c1c1c01c044101c052107004e16032031785858600241d41302503d40f00e60701040701b19024040d00124040540202080c8481c0c06800080341060075401080100c0345d0301c4068074440d00c04202030101d03010a02490f0011140282000c00f10701c01d000010075402001664001c09074012111542080c15421103400c502e980204201c0700c0b50b035020901265188000e00403183e02501200ea8204414415440d40d030b185001071401141c0181d0300d8071840113018003511244059000705e1760030000b45504000c0c2c0c43c11004210b0040000ca1029111880c1c148009080e001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 131441214 1250 131439964 131439983
    0x10051f12020a033f1106090d0f180603050f070519110718091e05150601090905090604020306070c03090e0405070506040303051206120d08040c0b0d0605040e0706020a 73
    0x443e0308600140801804c8055200d0544151100c1c088880b40074448000d10041240c484401c4410030b07000820324400d030130110042c1280d41290301e082e5000c85030300030070340104029241c00900400040250740d00820103500c010416051074035190420f040010210b5003040000c1c00307010390b4619000e01405030100d00703040840c418154082900e042841030781200000b03d106060440c1000d006170321495001f80240c02062070001c01015200c480c4858010203031040e40444a00340c0d80140c60142981c10080504150030b03002c2c1d4401c074250950310210b03080600da42224041209508061001660040b65454403450311030045e0b0340541014001d0040d0440048240001003c001c020000d071406400010980c3d80c4442c0d403480c0080065114680507028200003d01241c13260510f9580d480307600b068040507091070038891804481d140c40c02081520400c43d4000001000b2a40100500018210340b4000c1000c0b030500040c0402da4100b900c2c800780c9540429010001036502103804aa2161f00c030b60060f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 131442464 1250 131441214 131441243
    0x3052116060b062703010b090a0e1c030b0406090b06070b06041d0604030311090916090504060f09050c16080708090604091a01020a0302060705090310051f12020a03 72
    0x184014001d0a01c40b50700b00b4000115016105805454483d6244a20351018102c90790807081c54286c801981c4110780108400c008a0300d0b0000c1a080481000b05140454040c03030103500c0c0800030954000c107080301181c1d4681d80504141011301800002d840c04a40034414204144080740b4544a0300d2070180030350748041c0104029a4442d0004100080158128040e00140200158030b400f015a422800300e498034a8403d00107450209903001e08138000e0406501c0d0f030702e6228410303491060380500801c0016494000c50240c0da0344c41100302030031140d60108081400c00c205d500449078080c203055140c0c1400c3c001c0c2c40d055461044400b40b51035202e41241e4480080c5c0c50b010446014000403da40904041008544d24001d03621100c042c80d030001030800140c50003c01a600c40700045005030041c1c0041c0001088140500024403451101800300e4038201e684608290071100e095442c5a000140b03902c07400d4146541032030010141c07070010080c0244640aa0000e01c600340d10f444010508540c03181003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 131443714 1250 131442464 131442473
    0x8040b1806071808030703170708040816020102160803130608042112060902090411070317090a06020f040503010c050a0f08060429040c050c06130501060f08030403052116 75
    0x3560000c0c031030038003203e840f00018603001d840103c8440d002010f08c05103100092a0b10710034003440307004641280c0880d2810031380301f154004600f0300b000141c2c1588515441c8030039501e0741c0c00348c0c1001460300c4000786455004a07021140986e480e540000104003206090001040030801103032095804500da00402032100402030711540240140c0c60075581c60504005100c1c141d42d0020310102604840400540d1260359068040b0b00502102130001400d4102d03842646201c641e0964108069a0132141c07051050b035200343c160303407180318191005100841d04001a00b000d016080e020601c90900500f86018100024440c01415804104000200c0d0100d1130703940b11640300e0720246100310301154503000000b810a00742c03020710707140f20300681c074001516252505c103409480b0120413400140407162034020512200c50b025182c10b4481c0e558482e00000c1124070013668038008c00c0d2910180d44c2303603447c40c14000d007400144c1c2d2040f00940c6054004076000303d8000300b1a10700c0c007444100d8100710b02460a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 131444964 1250 131443714 131443757
    0xc0307090c0e120a0c1203120b01050f0d06051f020d0503101a090310110d0906020d0c080f09011a0105131502070e0907030503090918070608040b180607 67
    0x5941201d4483c41d110200800400d03070180e0a0b009a82000145944201715041c440070084040c001410065501014145c540c0060009000515120303080c11040020144650f2212014a1055946076000c00c050b04008040410149000d045041c01003501180030307403180c4210814200708180000050805544014080b0140001055102c072111010800000719406002c42c10321078406d01860304c103070381c1081c001ca004031154105154180400360586401400b42890201e4000e5000d21284544032454450150b8104455442000c01d09100c0000e0009440140c2480041e074103150044080c0040c200c845419441d00b8078010ba9a5480d02c00702264505030381d0454030500c40104c07200c901c411760020b0000e0607030b000b07004000400d0710f800e509035a4400c2e007848011712640092248000314600f412800380e0000240000400c1d140c1c410b40401c0c01e04507960000400728a595003800b09008001001540c0503840000107000468050110356030780d18014480020044011901c041c200030080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 131446214 1250 131444964 131444987
    0x30c080d0203090c0406030804090b0a0b0c160b120f040206160503090102010b01020102090d110109030503072d05151806010905220f0f14030304050616020c0307090c 73
    0x525161504003205150000e90b00a441081c4584a440041d440c6441c0601c1140708a0342d001c28082d250030701d481c0300003014102480c20140e02c500d005400003950506903000703010b0810590017500d85d807104042c10810142c1c062301304c03100c0f503a414801840c1400000b0369082d00440803000401a59a44c4c1c8005180340c89a405004c0c00c00c5404000d02d001c021000028141a071401d0b00244484417030480124200d00030821001c3e4000c0c1540188008684212025000800107140c4410801e03140d46031103141d80d02c40b036811500110110782d0003070710040409003420711903030217142c034070114002d611070b265901d104100c403074102c0c421100070848581e030003203169102d0a03080040e40c0c055070355100c0d01c0d00280002c85450f0450382a000402d0031700040d0141038403046038003c9020200e40179a480703020310a01d003000101c0d011007402407620307d511401c0014600c100c1c800c100510b018606801c5c0b40000f9512100401c0a540c4070104c20700d0319540200e4000c01b50f074405d4134000744521414034115005003015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 131447464 1250 131446214 131446223
    0x3020f0a05130b101b06020903030f040303090501030c110a15180303090203060703150b25050d030b040204050a050d0501060e160207061e0c0c030b010f0306140609060607030c 77
    0x310b00b111540324194100c10b921030001c89000300d40c510156029509210840c102c2c03030342000c0f007140d9a40010441d50281c50803540182c00c40b0b08000043d2030180c4540d129030001e90101d40c03038210800c000d60303040c0280e0103a9035003898881c1c1e06c02219003000c1da88040e0424000c1807071001d2009640310911607402130309002c101680320b001924a0b401d02034024030700010180d000e80070b00d1001411950080c068007081c444c0c2c0d0841070681c1c0f1b14044402c28660004915100325544440030413608201d407001d0414454060700143c40c1000300810b0107012248005800c0c0e009500500c0104a0781d80d4074070002045602c01e41d0307400d959500500e00580105601c0d080540c1014800c424060181c0224010f900e034071411b070702150781c000c0c0c0368a8246d8004540c1075140001d4140320031684640da00c01e08000713100e90700c601c07041c0010a490340d40c3c80c40c0004c000d0300982100500300404200744504c5004400200300a588001000d042900202d500c003a00101454010030002855204062149260a0751103821 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 131448714 1250 131447464 131447479
    0x20105030601021f0230011211040f0506010809011109040c11030a17070305040b060f030f0708010e0d0305010806040209041a0f07030506030d0801030b1b0f04050306010602061003020f0a05 83
    0x16802094003d401c0f0f124004802040c0401450f405410f8480d000b40303103d06800380141d5a0322300501800c020000c41c0044803860042402c1c0d260a844074060408080c8030750001040d54540b041c00182025402803001a0700e0381407a04820030a4030140849024000646000c10811207185055901c6003085502c903110744000035109187d1a8010000301c00c00500f0064042c040e02c414400301c00303171101900e000d040000340501045480c81c10b001c00c7d00d0016000750941c0c08c100d0790003410504082042e8010412a5100c84c004d00c4404002e00020100c0d16003403c04100b2941800c0b08c803695100010070003402545102c0203d400e00c4084008050707841d0080002207041e14045445099642050303aa12000c00d0a080100e050f0780b4002c01c15644409a40e0380d03da269078a581c0350a01c40c00ca02070807441d490001d48a01a40c506200c000a28021106590f4259101d10705014980341140c16480b01d011900100144074050280e00e480e0700c122034044134428144c00b220340020301580f45641c00785600280c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 131449964 1250 131448714 131448763
    0x6100810030f05071d0f150d12030606120614040e0a0512070b0a1b082502150903030613090204111b011109060d020d090506010f0906060c0f02010503060102 69
    0x3c0050103000351444404c0c030b01210741c2c5c20105d14848401c203a40c2441602070110028203404424052920a1540141100c2d070062a940f144000178a115039903400003512038038180055500040c0e00070316025065001c018281c40e0510380c1100c0040d40d0090780c4915112005e80c120f0034400c112541045803c4020f40b4459030500019034410380c8134807000c4944211203000100f40c0a103034070517111115003100324a445850305110444840030010320f14020281a50034081641004100340206009240c004000d00303004586469003a01008240125aa10420070414507440309040d188604800220101c0c0441c40c5200003000f501900a0200010f0008190481d20b42c90007202d000d0041c113000020488107080700001d1050b4030902c1c0d001a0007035002c10005c84000c401e64018401c50b000e8010000b4070304015039a090810200381c1c8001c4115540341c0081c0601c1605104100040066040500007100c0301d41e07030400f603441040c1010707050000103c005120790b4001c0c84131034035850401030414203041d0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 131451214 1250 131449964 131449973
    0x706020f040807050d031403040f06020301060504081005070906180803131503050609060f0a05031507170403090b1c110a1205010e0f071202030c0a140306100810030f 73
    0x800900c16402c0318401c10100040d01d04000c8808014560140d0701c070355941c52a074210603a81d030720141c81141ca0241e0000300002140b498070145001e0300060340c8942d6118900a041c51804040703210441040f49420300b401042038001d1915802c07546241010071101e0141a000480400d032980220601d0000040d12001503e44501d030000703a5109007050940180c07051811000c03100d0071a42030b80c00070341c40e201154044c03400d04000d11407010010542c40031700e030321400420300746160104801e14104410040c400e42a42103a8808400c41540c1107131480d03407a140d11300800c075010324800e118803460b000688080c041c140403050820715291070b0003441528854841101c060740014403910000384803090b103061100c81e90062904803030000c40c202d105c03a200e403c4130450408020300008140060700640762403040507030000c0c1d40305454100b001a01c0724202c21000d0540580540320451155041042020355518202251f603900014500324145544070340030f041d11000305400242942111070640030800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 131452464 1250 131451214 131451217
    0x61c0903080901091502030c0412060207110907080f0c07050d0e130c050414010507120302192d0207050a091d060108070b070c0e011508060f010507060e030706020f 72
    0x9109580d0000c041d542d5003405800c8940c0300e0002043e004400101c00d4544080e5005940c0041002901d03034546036540c0f4400d0101080d080040341c01300c0e00890715a05101340d240000d880503900340c401104902c0c16000041c40807000822940d40f00078a040410703039400d010000d603644c0f26031060441e0704046844402802230f08004013202c0c4250910141c48a40c072102d4068202c1504082d201c542c2000e0800007090f44082ea0751380c2e41c5041010901c03940c3301280083c51184505c07801ca86005030398840d092028511a070300c14013410b00740000c010b81c0c4410920322041039449445403511200760300384a00300803410031050f41d1117503a0004c40400d02040f4480c942d0300918800020003140400200410040c03500c841c024810070070203030021401000058030704802804494400c64282d603a09490311000f071710500c42a0840055152803e190041c2c1d44d410a05541d009441143c04d0900c40100c040000c00d2442107500c0107000329291403060803100d00810680c1d209650180e0190b40390440d09900250a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 131453714 1250 131452464 131452481
    0x1603020319020c150904091a15150a030e070510020d030b0909030304140c04051602010c080c091504030506070201090516050607080307020f0703050105090d0513060e061c 75
    0x80c2403071040500980d50001030442d61402c40035040307881d0351044880712542e0b90800c981141d08542c440b2103050008903e10080c1484014059003030106041c400711602d20b9444d0440805d0080c09074036112100804000e09440040e8030074540413903801c0c481007800c3e0030a00180d2165802140d49401d00c1c40180c1c01040c030300f00070385843c1d50400022400000b0040c00700310135500075285800070008200400c0e168044ca00b010301c0948212040070140c4c001003070849404417400c0c16440318414400c08000d80c28080c80b1103000d0303640703050a61810700392114089480750007079a502c07542c42400c5210041c3c01440582e801540c010080d1480c80c6040c003c060b0281c500506d04a541c1c3c002c0c2241030790303074104074000030003a0380014240780e04003220703541c52000b0b5900c00341ca01802d502c11070740031048902040081a01661154001003040e003012031246203800d01041d21081804410f2004200001d00c0c10340c11021200b041c944203070485400300c082034580c07082841c83c00071940c018144458010b405e400c69881c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 131454964 1250 131453714 131453737
    0x206011403030711100203121513050912090102010905100207052b05071406040606080d1d060d1409010c02070b0304020f041508030417010b0a0e010e0c16030203 71
    0x85200030002019100d100b505030040020780041051119820003110303c0716403d0007801201d1800542001c81e00d4100030458696070840d1100c2680109404c0403640390060070042c2200b48121308101c0c01d410380b130740c0741d04c0d43c5004215000700b8150a40e80c400d4100d850f80d00d40050941b0181e01081210703001075070150405651a200c0c1030150303503080000d21140802203404d628001d195803d080c0c02103885070300104081e50180e03900078815012100030302519003c0c83c4a1400002d81501c0c0c0a6401d0030a26040401030034428541c0038541c196203920000c6000f080708407800c5580c0d0140b145003000802521880308400a080c404101e20480150b00800b50b0030350365000ca4903080d580d80b0900c40284130840700203400462000811040d401c058001d51104a020800703aa62a500c0d006035500e90f820a40c03041d2411601c09000ba40d01e00c10a10540e0491101a21540d0619080508162000d107045c1b107107501401d0f880001984400d084000d4031a4442034003041000c401460600a6a030340000c1c01800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 131456214 1250 131454964 131454989
    0x1f0305010807060507051504050a061802120c0609150c1603030e190509040501090b0c13080316030518041409010b0406080c04020906090a030308070f020303040506010e15040507020601 81
    0xc3c5080c002c2c4c041e205199030180062400f41241e0f040440c0480000c5c0007294148191806200000d4180c060314040c000030009507545000c1b54010400d54003070108020b11a034000180c2c003203440d2981001c840d205542604d0900901d07100a031449110311806002d10100e0060f14600304907280c460b81e5800480340179076038103031a10700301008124440703000c0ba16040180641020030051414503601d0654054098000080d208100e5154a500c085040316040307401c4400003000c2e66040c40100380d40010385101d01c02103080c0800c0c90a00700f0910449403014083c0440071400718400c45949440410144000c0d00034040d440040070f800481c0b5a040c0d49040d055402d080c19043d050402c0d00c182030484111400070f11034454403405000081d031060301d52581094040003081500d40310300600700c008511968078000b151420610003000101c40c0f178008404c64104105000104a00003a2103042d61100c00740a0402e490300101c0e49100040311150503085401c001c04c01040300c0e00400c0c440d048540380142e20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 131457464 1250 131456214 131456219
    0x7030f03020c030d1107020d0320030306060d090519050106090e19031d0603100806160f0e0d0f1101120209030601090506180108030c010b0603160e1f0305010807 71
    0x16800d9000d0700b0201e035031950061003006403a0049030060300b00300e10005411031810183c2c0c0c01161000f0205601500800c40114421040e0f03842803603048501c698a601071410760802800103443c1e0310480c2e9001d403075103842e65010020302c9400e01c0103030f0503452400201c480080305460218040d101b00d1180c11181883c201c42e26185110110791407901f243d50320220b000eaa80c50b070f0b5013555603d00c4c05503000200d4440e0034507960346454110007903029000182c1c1000d0043d241c40b02c09031801d032004104505c034101071103004011640044d0310010601d164181311111011210214242516000c400707814000450070f030740d052149991442988032002e9030f40c0c0c0b00030b00d04e0b40c054409a229132070781660164070080041180d030b4056404190003240003000740d021140c800c80d0030b8034003c000380c01c001096080007842070784c1c14209105801c9030305802c3e25040d04518081501e44001303506041c103281070042e8400c203010140d40d50350010140c1c00c0340710400140d9210400005004040c00d00031102c0e6032040801c003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 131458714 1250 131457464 131457467
    0x106030b030c012109110409080c010c2118080d020304020a060e030a06052502031306090e060103020d09320102040f15020c060406050909131707030c1707030f 70
    0x498011070360107540d100d1340e4044d0b84204002481021400e40301100e5070040482665528081c01000c58001d01b0300c0da0311490340300380d51383c00c44203c013400308280700354001030703107407041d0480641030180c1c100e020300185201c1816560f0b10050000c90004081c0440016145580c8540380d02035809071303000b9070f9103007403480d2150713419100c4100c4c072801103034140d00070000500040d03001d03001164020302008044144000b940c01c0e44940203040c5d00044d000da000455001c03404d5001902040080895181900a051812600c4601d000018000320304041c0c000a680d01803d5483d00414181a4000207585a202d214003044404c100c5401c4422001444018911002c3c5070500a6805031a60003200d03940390352a0400080041d48000340440650003006540e103080c1d0b8901000e040185a10780b11681e54007080340400c40000303402044041030351000141b4101044901590b200409442c885507940c07040e490800f07840b5001c02000c020110701400d51221188011503014060301440fa031654140081102ca0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 131459964 1250 131458714 131458727
    0x20406050723030d090614040614130807021528020106081605010f02071e09050106020d0206040b07180b0c0f0303011406030a2318010204030312050c0903060106030b030c01 76
    0xb80d250043c2c1c010302c000d242e42401544000c150a12440300043e20300304e006140ca0800305e08840a907070701ca94070341030581c80f5194260750f668441d4140101040d0421113981d0749146004400001e4041c4000d80810400007105908503400c10382c01e80350340c1c1d03086501c1c41e032028003e54068081200650070204009400701c0001013400600c00342d8200c502805080800444480100e002c0000444c030031170700d0009011030036050741c1380404206442401c0050402c1c0c0c0b9030090f143c0603808002158030002e0300802040c0d000c2200c640040c1d001c0300c2c0f4492a00c40040458009225489003404202c82c28000101c41c8000300080003003d50543c1540d4400c440a480b07a9140d002c2413184214407150b20880300d110703242c5030b002598455203030400000d01c00303000c001800110031202d200341d04440039035050008091491400c1e00609030300c0d400a5180c10304658008029009003079514075030544032004906074400399420f031410010045c044179034070369454a000307000d400045400c5000c2e01951030012890352180030b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 131461214 1250 131459964 131460023
    0x110301110a0504140103060b07030306051c030816030b03010c050903060106050304240f0f1e020c030a0c023601140901030201120f05070203070b0a0b090601120f0204060507 76
    0x300d0300383c1481e140c40c50941114a01c1d101160400d81e9800d000308807406200302905065010703a03400a06a401e240512101c0408014012986442040c150300025400340d0f1a981c401481000120310440c401e8043e00a0071030030f0541075040d4204042126804c0d0301801030300245200701d0031201a66600c1c40242e59510083e24068120424410840c02407a42c0310361820b664800303039400081c208004012002116007680e4103034442a02c52401c0b4542c8444905680021800c10108618204204100d80d66a22445110300d05008505451500b9990b07a404462002868030343c404001c100714401401c407441100a284203409440c20022912007845031001c82c3c0800042c140f18603036420b41c0c0042d10513400f180400e80700c1e07503203030860f98881d0460b600549000b02d03c83d800458617445640b50005283d100240340c100d40502c0d081e004a500d9580f1141140c0004083c04c050020315440500300d005468041d5a05000c1400010700088040c1c2c070030f00405031030380200d1904000e5401da641c85d0a40315142d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 131462464 1250 131461214 131461217
    0x30103030203091005160b16020622110415060906050f0403061d0d050301170c0d02060a090306020c0705130902150c07050306010306021b060106050f070309090207110301110a 77
    0xd1006442c1c40c00d00c0b130888070112000741003990904600910820284030032042c01c903069480e0009021400c0e50000e141c40c4000c82900140540d8913103d403403024500b15620244115042c1940f80c0c1c803d000100c43c6803141c00001900c10701249024158801104106c0e2203094006989a10b0018480740709800340c441c440000c01c01c0c10300d8245540c0341c1c200503080403c2181c0440c1020500203901c2c4108114000410031582c071030680340e40c50500703e100b400c1003250700d00b002c076040341211000d190388022403035110399030448560752540c2c0b25807002c80d400c0440350001844140300141d181e18604001505200329181107440386091503581c8013140076580d1000e002504694100d00b03c5440700300c00d001921500140c0c0c0101c411455903034000910b825020b034415229a980001c1341048010b011240352001a0413a00500c02540340c0040244244607002c400c1c3c3c0c2204002c22800c04247c4900107480c0181003100c410b54407029942088a50b2050030a2103521035860241201340150002c4156820040329 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 131463714 1250 131462464 131462467
    0x8071a1614040b0d090b0705041d0901020c0d0206010e01050d08090d050c060f07110402190c020604090e100518100e03131701180f030302070309030c120501060b030103030203 77
    0x6400c0155119040c40c0141e020040c030501001c142003074180b0107480d421019183c0440d6604039800c021045420240c01a410482e0030403043c440307208a10202584400300b80032044441e135030301a0590080c000c80c0b42080c070341d004030756001000c10307130014000741038604003042e181059036035104012034074400f45e1004100141c01d01041c2c1040c98180c80c1e42090324018003c1c5e810054105c40015484c1d84003200043c0c40c010041509424030400407101d9901c02c0b0207075030851610026200d0441907024440c400420400c4000d4401c0031520f036041980c00501130b4403424020941c411800c50b848a91581d10b528a00d464500001c10000c54032040081d01c94000c0040c00107115044401006840141041e07241803100308214000030241c04400030003080b028046035100c4410080240c02c0d80c800400f00111000031303080c0d5078041068640d40c01056076050800607901c01507450161a41c1102d07034009841006c03070720000905103050b61000c0f000c9901c904002c00c82552520b1001031175020030f02020b00140d20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 131464964 1250 131463714 131463751
    0x80609010e0604022d10030c0315080a1b090501142701060f1701060f021227040f050405061f0e060409050709060801020703030e06042001030207060908071a 69
    0x2600074004881c04c5e1036075030402c41c0c0f000e1101042031561402c1110f00060b03600c5a01c80c20069062141020314800001900c80d854a4201d456558003010350002d0700c0405908000c00706408518980001031210340e400b84004cbd0794400c245034520b01400052802190035a104080b007240c001850302c00c084030101031030f1046c1d003070020031101c83d103425070320b0018082c180d002c10000c00710b41c1010500810b610390b0388462803602c000d40281042c0000450b582d88010601c1440960001c11707840c030303c2c070810300509451011180000038001e004c044100901c0780b49802d040c0310610030701140300c40c440c1d0800420016118051108880200c3c4a8454024586005008a0842d243c503800c0144800e000f9422503920030303100c1a0a0044412342e62025846a42c0000c424041513058001e4440284030000549170034500b5486040700a8000590302501403003095201c041d40c0e010340c0c103648920340c00c11404c000c0d80c241c500e02403e00f5031015a06680c100080c81200d80c600305810701c07072031260b122110081418034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 131466214 1250 131464964 131464999
    0x30f061113090b010c082706070b010603050c0403060c27030b04020f0402072301271401110406030603020a12082203080729161404050901080609010e060402 69
    0x40240c6030f0604009203801c541d0b0100350004007622400034101c00d420030f803800d112854181201480a19406200144141130104901181c1c0305c0c1100d4550901107000e0344c450f0284611481180c0004203170318541000d03143c01c16031128054008540800003078003034181701c51850510708800e2200524494000d00003e0060421200c44505581c0141000d400c2241a42d540c132186070140350040f40080804080c0c410300b000c24003500c01d8070501c49140c400c041d180c000300c883c5031015054010348024006901c4841a210940c030401a56603000c85840c1c0301c40c0ca4080c0200a028248404e03403051149607408610b0039943c10202503655031202510745001c01c0300605005231440259800120412201c0001c04500500d00400c1c040348103d890f10049400c481201c4d50003d0b05607528445a4121010080c041e081165601c1103940c090a0070700c0b1481841849002c1131169810142d0049049000002c61000009050303000c0c40148009118608448070516070303800302101c1c003039808100080c0c20381c285c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 131467464 1250 131466214 131466221
    0xa1116020d020f0301020a0203180103090209040813030b090106051512070c0f0203072c04030e01030f020c070f030b090d12050901020915041401090e010902090613030f06111309 78
    0x1510151683e00c101e41c8540c002401ca0300301000c1c920240e0000141c003801c0b04070280b4406022182402d08001c4a041600030034401a00100009e00b2602c0c0081c00704440b41c2240c0515009681c08800c10503d4982001058040c00342c5104090080f1800c3e94504004140b14081c1c0783ea21080100a061036074941030126800d03610510180d40c6071965408400250301c0c2403109601400404203001c0382c071442c40e0903a15904002c100021410714480e400d200c00a580300c3d0f440c1e04407800910b00030889012171040b0707034020b200300c0003500d84500c504500090959801c0c508481100c0c0248c0081d4072581e40c1c11304003522007450a42c80b00c00111105001403040140d58400c2d500300071a00d00040c00c0c0b8404e0320200c1c07600002d010101c105900c2c040382c1003154401c4c405640b5429402841d00702000751030f01056507000c80042c00b40c40e11003500410017140a840c0c041c141e601e600c0c02007101e5080d01e81d690505d02c1043c40355a5060b955523007082800400c09030690100ca000f41c2e02c2000d00640c1500c2d0802e40d80c0107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 131468714 1250 131467464 131467489
    0x50403050c03041e080a120f110a050c0102010e030f030a020a030f020d0b13020414041d1606090501090302010c02010f0216030c15030e060115020c12060a111602 71
    0x91100c18003240d506254108094806002d499145081c81c07140c46000340202d4942d54015592940546407603000940515049103035101c081c14080e02c2034060a400f03840c00398103c101144148190b81c80002444400a01c2180040082c0c000700300e04940700501076121b01c90094444181c00080000c00c04a1103d503000f000e400398039140014518002d12110000c0e0b0340b19040c406080340e00e4082000c444c0c40c251820082c41d0820700c1b41103244c0f9140404070844582150345580c85940c2d0380c0314140081c01400c03005d44500c0030700c0701558600001c5001541c0c01007024010800094441100896503500603410301c0180ca0f0161180021000b00f98011600c48620010550860140380c400301607407117181202d90040d611803480c2800890400301003400da4940b40e1900c404040c1000d00e902e10381031000c1902410f46502ca04075a28408103020709074a0101520038040e0046d0341403901c04042000490031a02408240c041800f640741d628010540d18003828001d5905d01d100740d030704040145401ca40001c81d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 131469964 1250 131468714 131468717
    0x702090a06121a0c0a2001021e03070e0f150d0216030503070306050d03080c1305130c03050604090201080c07080708030a050103021f08010611160806060319050d12090c08160b040b030a050403 84
    0x1d0300400c2245508401c20351276105000b417401009118040382c21010040404c07900360380e40c03015602d4910004840c4000058000807030900051a62006100380c0c049800d01c4103600604004c60906142c0100300780d000701c90100001c1c2c60050f001c80c1e10700d40780c480310150681582d80e01c91192916100c581c0c003a400005801c104070b281303070030004042c0c541089100c21100a8000061350040360400941603410092105105620b00040800141c3c2c2005059801071724860196442e51801d20b005e08261056450180002c0400b00800c101e100c096001641600e10031350b80208400c900708005075109001040b1031001c905401d0042c00340702d208200c2100d50000d05011216400d14040c7c0c1760a41c9207994014441c02d400441c00c100305814200650151868402008510240d09480381500c8851720100042000a5800c8042d10025583c04c543c00080d003040014810a0317845e503d041da03854030444804502d200c0343d600080c0721a0400151001c40320f11084061640c0e031000b072600c0c000d1030000c10840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 131471214 1250 131469964 131469967
    0x1a0a02010902090f070f09080304120f0609081309020c0a02010509030c0a090614010801120303050403140d090c050d050606100c05030a1112040602030702090a06121a0c0a200102 78
    0x15070740f1503000034068007000d2103207040d42c1400c01c030040151100c0303c428000d0000c0414201720000e0000100c03400c40e843e140311207080c080c0510f0700e1208400008805400c1c1420070465006104000006204000c107040c0c155050607520024031059000300c044003260fa8100340407690165028900800c10410b0060030f4401c03100040c0001a102a0941c1003003031015038441041c000411120140d4600c0c5600b4240100598900a41800000c0c01c0711802001c061f182c0010408050065800c5101404001703405511484400c400700c0050a042e031054805181000c2d00095078180f0007190082076030040058a815600c4005110a916111480604200042042c04041074050024212203d400c0c0c0c1c45481c50410409030a140c00101403090710380d104100810084141c00108075440241e040e20191450755600c92002c00509c03459110030092800b10301840d081001c004080285640d00b0035204109803141040c20302d503030144d10f04210209207402d013910f440b4402e0f00e80300c40c50306103520b0016 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 131472464 1250 131471214 131471231
    0x20303130206091e03070e06060301090218090a020c060a06260a060e0d020714010801090f090203030c0a031b02090106360e07110c010c030203121518011a0a0201 71
    0x141056254130401c0c50b01e1000803c0380c9203145014841303400103282030f241c075030f19501708140003074440c1c401031080351107545d0300141050070851f0b0070392190000f000c020714106c1c5601d01a811030703000c2e6025411151481c024074002036940046c0d80300d038209880f02484036281d030028110548118141d8105001da15219404903507000074114082c00070054462009801441000c880c041d103804d480750404078800012000c0ca072050303688400f0386811100507060114840d40403c41c02c80082c0b01c01d8102941500001424818a2a00240c0003040f0751080d83e50110311002000300c0c038200341c864180294050008001001070310300c140c1d0a01a800150550b80780d4030802c24025041940030035280285140400c0010800e66451f0b080c25507010707149061075448203681c1d500c0300c0c0d01d40c01458106410721407455108000d16100700141c6640c0e09a01d81c0c0c08100d03040072400c108901c51500ba82600c1910080c0042082800b00f0b82c0d014121f0750318400e50b4aa0030034854081c511504100150001c6644e2240070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 131473714 1250 131472464 131472469
    0x7140409020d0f150e010b070b040609110a030803190b0a030308100b0d05061507030801030201110f06100503010e0a0305090f0d06050f09010c030e0c0907050c06010b090f1002030313020609 83
    0x60502c04c0c4080c1181d5580c10340750103085901224143d10000412030188000c1c80811203030350f50107034404e9000d840011583e01c58030307113914254000042103410090300e039004000c0081210003180109003428078111048401c6541e1000da484040f026500700b0401c1d941000081d001d406c140c3d4120b02c4003409044841d46031032004545812001403406883d840b0014003509091460f4041c40c2c049056030030901d0145c60751005044000180b0000b810003a42404c40c3e8420718041c400c00500805100c207407011403d10018032240c081c41402901c0c030a51034011071403565040000e0741003038550305840311402d04980004002c1c0c030b200e46403145600001443c201800040740c07441001e20800100003400c2a6050142c0f149084690030114242410316025040c20b19090002d40d43c00044d5040303131107000d10350320650100d60a0107000c0c03281078148034207800400d071405408068070758842c042d0340d0713125402030240c20003c4401c891500c030005608208049000550401040342e6180c0c0090800b91038100d11801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 131474820 1106 131473714 131473721
    0x9080711030304080f07080d02070f09050c160303020703030c0503090c040b0409020604060903050c01140307030f0905030a02070e0c0909010608191a01030507140409020d0f 76
    0x450385140d070104103d90141481900b51200c4c91059070400d643e880c01c2c2d020300760f00d6019900d0740c80341c41c6100292040454011241403201c1519003c182c00c010900a01880e0129100300240d640c4042940d6003002c0701ca12070364005903140843c2c2801400c8074620380f000c00401008000b4001130304400a60415540750031100051754103403010001c0e000300303201c207030081d04440c02040008000c4d410107141421070b4040c00550b11103944040045550740718009c1c10311280d03401070002c191424480d1340301c2070290041e40000541d000c0d40d600d405185801800c122001644032030418811441c1c640201034200241a521505000381c1100142d010350050080300304114641c070020303103058044c0324002c03000c1003000404c2210403403032011341030040c081400e1280400d00340404511164030944e514400050112912030a050038040c01070082e5128022000c04c040c0c076510a443d1469841c031 = true := by decide +kernel

theorem cover : BRFrame.Cov 131294964 131474820 := by
  have h0 := BRFrame.cov_init 131294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 131294964 ≤ n) (h2 : n < 131474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
