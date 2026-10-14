-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0208
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:28:22.223835+00:00
-- url     : https://prove2.me/submissions/7eb23d21-fa6e-4b54-88e8-558c94b92906

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 37230220 ≤ n < 37410076 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 37231470 1250 37230220 37230227
    0x50105010813020112090b1e0403080408030411060408060901050c0a020c0609040b06040e011503020304080301060f1e090608090a050d05030a0b03060a020714060f16021f0e070605030403 82
    0x50b007290004030318000308200c03403005030b81100c40100c3c2c100707030241031a00203810b21801c4a0840d2041d1105104000c1012041c000602042000c43d401408034146030040b402240c420700281d81c0c400c2c821001e00d510441d000001036aa504543d1040304564451001c000c8020350a0090350b410421030304907207051100000000e5120984114600d00540700880d540e22140e4458000307030000b44001e0b00980c0c0e955114800400c203da0240035610712800186c11010000d032291088a100310742005003182140d0800d00210b80c04130b41c800c002c41c20030201c0711302c5800a80c42c1e6039a1444070185e0361901402c06203040b20150803660000e083c03a415800c0b100115000c6200440d00e501e14002a14103580d40b0f60303442284000a00c4094412501481040204a92000c0070345c01003420713074020083d005c010b15240030702c2517a404c0200c8003e450310150071301040185968112001d00c074075190040c0c0e402c00105041c20b04820702206420404580c0b10310025041420a0003a0f40c00780000d8500280340d86000d48014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 37232720 1250 37231470 37231487
    0x7062a02060118020d05010b070528060b12010f06140a0e010b1b0d0f2703020103050903070b0f040b0105060703090b030a110711010e0406030519050309030d02060405010c0305010501 80
    0x2101e80041c00d81403031905425a504071803007040745140812465131286400c231041e40040b2000c4800d403203103184581d0b600741d890a082e114902c124070785070490152a40e405c0301404400000c02e420441d04040d0210b0b20b8401e0144809202000b000015640d28045050b4242c0e11a451440c6c01846d160109012138601c0c182801e0550300562111a03940c070514144000100c2c030540450210f0040c0140039207061fa028140c450118125a201e0320403c0b00004400e600c81c0c2045250b9509502210040005500070b8104951040d00032065905102e196201c1c24401d1008903403088103d10040104010402550340302c9000d094107481c0542080700d19a4060814040c0e40074415480d0703000310004003200ba0903048080500c24003101651a101c0074508400260404e0030141d0108060b504d04003d0340c20184201c03012660054001c28000780120301070207015101e08002d8900e170000700654502a1410000611490980d81c000c020914203400c1590031540d162120400301400c02c80100001da9000d40c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 37233970 1250 37232720 37232729
    0x21c0b040605091609030206040608070f0504050f040b1c060e0714030d0c0503090d03050a0806030309010210020d06080717100b0d0b070315060306050a1208040303050315030307062a020601 83
    0x120800359004c941c16200b0715a95807000b54003940009000c00d00d10381c403110b0240a0000d40e15406400c00c040c0f0400c1d03070385003d540120354029500801040031880d00350021146044003401c0d00038403102141c4450441100c200054800c580c40f10b84184160b031040141c60018140510400401c03403001c1c0002c1e440d8002c641e001c0c001c01c800f800c090800c1c04802c0c4202e40c00100000c01c01c0c044c82c0039501c2c0191079074004180c62000f140d40d410010729281004022610700e034105a003d4130a0410140d0f13008000d41010002040007940d0310400318500c00204680000303441c04010902d52025500c0a40e8901208410303406840c500384400d680e22500c0d200700603082c1c280e02c14000202a03890789412030003448045064401d500003000c00041741070709680030b4000d03580c0c181c5800407070702d8aa0000c0d6000c00c01032100104009020081000464820005540c1215121101d0441d00803000c4c0000d1958211500555100b40c3c1c6940c854514900c012071401d403100c0100f506071000b550002c010f51101d405109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 37235220 1250 37233970 37233991
    0x100c020d03090509040327050a090c020a06021201051302040e010e07021f0c020d05040806010b0a17010b030105130c020601090e01060305010911150c030901050703030e01021c0b04060509 82
    0x40c0c400c00c05025881070406880c0207081ca2000e0b141604006010720007200d45d060342a0400c6210b08207250303482c8110700550f1800780201d0741a0f0b14045522006299011000003140240d400300e10008600340020100c2c040e0501c00005503505140422144443d140d0070034200c188104000c00144643c00c09070b50445000f60b800003007658070818107030b08000540420302c5403503002502c410030310802a8440700340b4203403503402ca440c03c940016040c0c41e01d1107a03026a2002e6401040104004007110000b03200542181c0380000c40b0075230340c601000b1214820f0b009850851008401032085042510806442c2d00b507000003809540c40b030b540c0280d15100c06008002506884084c05070b1110007d4110f40c0003103a20074002c202001040c03e00c0c06000b5041c036001c0e0b1044102a0494410a8903d401d40740f01c08464000b0313514240c1e89400540b840d1f482003100314240b545404a01e200b081080c07014200d100c460f80342111041030081007260882d1020710104c3e10851501e1018003c0d0303111203606550040300d209 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 37236470 1250 37235220 37235239
    0xa0f020906130203090a0c0816050f0f09070906120204050904060506060c0f010204090c02060717100e0106020d030c030203010f031707080a0f030b1f0f031508010e0c100c02 76
    0x10041440403020010400c40b0300e000000b07200c03000301c0004c0d4030703041e8600a4a442400039140c40d549615200b10b000c040746445142c100c00e00813450000a0010080c5c1c00070f202c200240e4105020400c0300508990b1900401d004060820055400810103221b44550810031868a420840000c070ba940c00588050a40f640d180000b03141612140100c41180c0d8510007221f10409125041c0c1c1d020f54098051245a103042200c040d80003400043e0050054010303880b416070319210280a917402010007045080e0312010540000385000d1500f8289000c1e00350395019004004450902900344c0e507038451b0240070144100300400c040c203c014030f014107403584500e0202942e003501607158610300810074098000303c0009510200305401030800c6402400d82e03281801460800030802566052a0281582041c080220034034210310880046c00300c1c56042c00d00017038144a4282c48160402d243d004280c161f03540b40802803100004001031404001304a61003440c0c110349100c0108015180b0b04020b003c0c00611 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 37237720 1250 37236470 37236481
    0xa121101090c0f0603060b09030d0c031809240e01050409050c0310090c0905040506010b0912070305030901030608030408070311031f0504110103021801050306010c02150304050f0a0f0209 82
    0xa40196095903000721491a2054643c1c50180600c01140b0030100400d19144000640045e21000c4d2040301000038041d1050f6043c09100fa1404001a01d04070200854034904001c598617044409003c1c101014000880501e440d442c04200c00035510201e465100c1910100301c0361440080203410b5400503540400c1c5c00c40d461a200b03103800e9075013082c0c40d8507008010422801c04020341c01000c070a401101580300403951494500101c45043e0713030241464221000500c0080c0d000700042841c0c15016050560100800e50b60a04201c0b040e0801c40b101c0d003000503401450b46c1d05005100c05000800040d43c6131520709004241e90764000d1000030451610310010683c2603406100840076280c1104c1c14802c011100e84064004250848040b0740440b1000402c0ec4154428407d035440f20700c40803488842001c4600040d962500010401810400000401c000580b1000480c1101030320340700d01981c40f41858506a420041d815140304200d51290401c1000b044e21240d5000b104c0d50140c8403007040e6102d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 37238970 1250 37237720 37237723
    0x120124031b1808010638090603060105070203010c110c06091c0305070b070201150e060d0b090c1e090f040c030f061803180503060c1e0c0a0b070306080a1211 69
    0x80750f100004079403a00c2c100090354401c56200c0c07600240400310046c0003c0c0034405040904404c40b5210101107018850319405060600c0150307000a014140141000c996074002420350340340040d05030014024051a60682108020080030750704111001820011650049140540700c03103180e814591a03030182a0038140201c0440d100d242e00031002249600d080c0d10042c2c060520340718141d00701089242c0004c4c13040310800019009100040c103614801040703072105010064080c10741c80d2180140070b4562440e0742d40f008190702c1d000c035100a8019524684003040150030000b00401980300005040000007051008c1c1032058940c070203e4081450040e0a00300c0061590b40100040604042d540c0d034107041e0001c4403807040070814014212043d4407031080c95240e03202981c4100b40c058060024078511491402011090301c28084014105592030060300d290440e01403003514030244410a006145926000d0180030340207050042006058580d141c030307640c0c02c0d450700402c00c01125500e890480d210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 37240220 1250 37238970 37239017
    0x606090301050709031103060103030f030c170106031a030a0302070308030702010e06010b040305060901061802070201050903010609050105120105010b251b090b030106080c01080c120124031b 84
    0xa0000c000034a489100500b49000038003086d5188001203c41d105203141c0000c056050701d030700d0707510241d00b00c079180001e502529002140d881400306440f076a20710082800361650003880183d4011800c4050745d96503a6001000a11450194010003000030109800045090450707511503909a500da0b01e6400407401003840303404100c03103400780d04000510b600103400904152400b4900340c80b01601c0e403111640c01c854661240d0a5092840030010440540d10390180c0b10881c0181001c514000d10500043e003114070580041d24003542d00c0340180140d0610002480441440340001c020075410210f420300c0600840780f0300b18815010a0881003100c50b5501c0607000550310441e10106444200da1040c81101640901c0d40b10300e02c0c0140c40d00442c9414003c200440700d00c4805401c00030946001103a031260024011a002d513010845181c100801c020068020072500c1d070079503820001480141c180d0a01100140109410300020703580d41c0949020280c5207080c0c0b401c1c000d100703004500740750000d000b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 37241470 1250 37240220 37240237
    0x9060506040e0c1e13090e0a0210120e03030a020a0306080f06040204021309020a0804150603030c02090426070303150302060d05090f120d200304080c0a150b0a170d0302030606 77
    0x540200360081c041741d52007102411303500c543c03005000020000c0340c480e60f900040710010394003640b0307029290b4145010b180398104050050902040c092100c10b4240d1031640292280c9509941c00030704100c9480c0d051280101801c1c984000d4001c0310300781c0e14a00e40d00c050280000e8800d690004802e01c200d07200c40c00040003403595440c00d644507001d07001c010740041d004413000e88400640c00020590b1480c1403083c3e1041c0c0360315440310704000001d41c007409024000180201c0b0321148180b0101006801303103003e0040070360844400742e520030b803d141c010700b911420800600d1000c950030701840169644015200540d030501e200103280c2e510344030100d25002030101e40c0d1115004250f01c250500c0b40c1907006050006110605000386c0e0780044162800d95541d071a0311240d103809001040010340f40c0343c01404030042d46070803140021055200d00384940c01011010913101d9613250580710364104072a0036030007080280245080e03000b02801007070f22128840705403400c060b030000001d4444d9607800181c8074100e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 37242720 1250 37241470 37241527
    0x4090b040501020a03051609030b0a0204030501060e1008060705160c05040f140f0106020622080415080a09020307120203070909110102060c03070912030e030a030909060506040e0c 79
    0x900341400e006000754400d09100300020700303010024100c043e10310803013a0380e0f490946d070300f10459181d500e60b0170700003001601200995808110000200310309000796805040f0f42114040c0c0c0d4104110b12400030b0ac925480340032240c00520070403441903040002c0e140c00c408400681305003800c06141161003020746401403580710307250489980c02060309502164007030509040012254480b030f102c0004c140305c244135203001a8000d13400200c0c0d01e81c0307082e1340c004001d0424134803801413410707580c500b08076800580000b01c44407802ca1003200b006620004954110b0a655030401c01350400b130300801d4442041c0d00403209194400c040080454604016a400a00020307030308015101c00b9203050f2940105040300d80d4018803481700819000100201200e02400712603c44128031850001224a0310700c2103001a0248400c5081d803910380e0b201400f840b24083e04c07039524601802c0c01c00c0f501e036080b203070302d60000c40c0a0761082c401131100034400c84041e9000251444581e89440b070f01203203003080c0d80d081403102c04807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 37243970 1250 37242720 37242743
    0x1506120702010b010e040b0d0201050f0f0301030303020d05011221020c06030901020405010921060c1205040506060405130803150402090d0c0509010e09031b0c03070602060f0702070f140409 83
    0x1000c1d41036120942c8903801340c0e0307060300d241d08900030030003665801c0b0380c0158071055600c101c04c0150b004c1e00c001d1200c3c07003010044600f400603071044403041d500264829008650001038800c207001082c4500c40c090901018032038404166030f100c0e8044501101c22841c40380805c200c0c0701c10014000c100100c1c401c0301c020989552454034451450203034006120b000d003c140c0c800b5010034050041da0f024040c0e440300c0701c803011080c0c8841d00c0e00300103008004180c105210b22017400c8a404040c50042c103220f45d015000502e01402c110b03003480211400101442400e6820450712000161003408071390700700107400c040740c501402000c0050005d109100410354002c621004d03000401c080400c10600f1100c0458614485a985110540c030180c0d04440181140d00304000e4001c2400300c10001034000c03000300080300c04502030100441e250024503048103000d64000d008001502034440748090744034150b071010b0a103461900c5e400001c09030190040c20590341a941c100340d060707180c0341d00422080e900302000807032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 37245220 1250 37243970 37243981
    0x405030706020a1a09061909060207080c0709050106050904090215190305010b07020105040510120e0a0c12021f0203090d030504080d09030c0513020c010507030204180e06150612 78
    0x140c0b10041d810885440d40c10889103134103d5166002c05204803030b50300c0038140030ba44045000c0301c20902d05020a042c0c40d80c1c1d0910001285680c405001464480e80c5419521070101c0812441d0458542c418660b49003084014080340d58840e05030342c1a100c084d50080b54103070980c40011012a140030710081180c0000c03580c103400f0b0740b00c01e0300402c1c2c610003074404100a980394664140980b2a035280640819400c100401040c1494162201c1c11080c914000c4540d41d400904001600c0c03004680d2410743d40b02d10100c20601420a4084000304841520b0714450105540450011441c10180c040102e1005221a5105000740300301d41a44c8001495400502040d15000c0d0032900280a0074260b4807a0f100d01c111040e00030b001101c107490f0850b406030103062034041000410304200990701208c035028880c40084d00000d010b00c0c1e0280c0d815407005a160340c2004420448940c4440c10304200608000600c0c003206c4000c112140c001c5615091070403189054800315179540b18005c150030130140701c0401c115 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 37246470 1250 37245220 37245223
    0x7050312090c1002010b030c0d061b02010209030106050607170f04080d050415020c0a03060b06041211040b1c02130e060f06100f02120306010c050307050d08011d04110105040503070602 81
    0x414581c11900042c3c0a0043c40c0b00702e08035402c4240440e0140e000c40c41615451500c40c40030051944260b5001c074041c48100700100c1400d50482010b009030303401040e4040c0a180030300800c0090002502ca040c101840e94860359a81250030052594500000414403032000020341140e000d001645e04032002c41c011000e00030032551041c45106094404034484e050290b202040918801340028003141c036660441c4c4501008000c0c2148895000c1000c01000075508490162070a00c21b01803009020082600700910096034254002c0a2244100c2412280018207003007003d8079003070301556002054a50f000081d4001d1121001c00c802c144186030070020708480182d88a4450f00042c0c03800d0003c00ca11281c282c1d030180071000c01c1d01c0581c020701c10150a00c20756002a44e4000014500810140360301d4451030b045911002c4261525001240c000f00c940303411a01081c0100104164420aa0820344020004440140004009240399103030700d02c0b660f200744183c0d000341c40c005054611990751030310041d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 37247720 1250 37246470 37246483
    0x703050408100204050d03030c0e13050f07030e030d0c020a061e060504020307020c22020301061701060c2d02060301060e19030b01030201080c07120309110a08030a050705031209 78
    0x40c0d1071407003200391034190700c481402607400f11440902000745a207400e0f98180c01824009200c501000505911800a6520654008101da01b904c3d00000c00d4100050501c4600800829920030b0500744101d800c0050000812190301c80b40c128030002d441c00905c04200e040035a040009007646080c02554424008810078560110306035540030400b003035803a011b000503070004407903141c0580c1002c0d01070b6141d8201200c0c031003032003040c940310301b00880042032246d42207070000e801020000c3d4120000c202e4625200d0b400c4d07400b4142c01c0c20a150b0b1613900c0d81d00c0d1460290981d0840218800c0304a4184114003600c1800031a01d900601d415225030311150002c0015240c440310520a41002440032103124680d940d00040e44c0e00040203036450303030941c1c0042d2942d480c080d180303c018190170440d01d0701261020782200160003035a0fa0200f190405810f10060960711595014851024642c08100610307000003101c01d0640310341403681c1c5502c0a03042090940c001c1a00540c030640c0d140003081440c0e43c0100e060f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 37248970 1250 37247720 37247729
    0x3050a0305150f040b0d1509030912020603011802090d0311070906030b040f02030a0501020c01090209060909070504110f040816080a0503031b0d090506060109061404120602070807030504 82
    0x40000d681d0b1902c801d5078058021030429000240000c1080c6503003443c1c5c100d211032900c0a0712010700d6048640c0d4060b240292095050b1030303559220240740406a110289000030021500001070814081d0000394142c03006120300641c0c8030400e5400381000189405541ca07a00000b02203c0702c00b00c0b14280900f03c43d107441c1c1a1100c5006035080401c60805d540700c0c000030f4a030070901d010b040349e586544103000b1001891042c0e0340b41c4501020003000400900040c4030303880050001080c08106481440309800f00549201c2c451f03c00e0100304600b00e070002901c4001c48400300c8001c5a6044044100111841000b4420a1072080041d020400610008003d403084d01c141d50911002c5544581681d00c40d0907611009080d60410004203400380203641440098040c2d80b8640d501c1c01700c005c803240080790600c08045131207411060800510f5a00550201d00418590074100710080c11600900d519200702c3c05500b040c42d603121014414011294103440c081035011b1601685c03548142800740054100b40726 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 37250220 1250 37248970 37248977
    0x5030d0606020705010f17060612011401020105060d08090d0215130e010b0901081f09051510030b0109030f0507030503030108060a110a05070f060e011e050f0702030405060d06090903050a 82
    0x130705548101100c0b96000c007141d45040303107841c0072101075402c04001f9104607402101440030030008065104668024a441d1b154134030032040c540006030075240010089403140c0311100c140030209980e4422108144021911a00741c0e104a00c000307086904150441301c44400c01141404c000803185003d90156100c4801c0e1701080da98402203007403103110b554030320303030002d50400081407400b68050b10110680d504021284060b9450302d10754421230b038088440074500d0302c042000080710300701a0a022020242440d060109803507500010301603030710718031005000c1c0401d050400300b0302405100030b0300a964000e00380ea569580d103070307480e40d5150b80550340000c600d850b0a401052206143c0203c494066480c0c40301c508140700743d11118250300c6140010740c1c3c25a00d40d015500052420b01c604500c9084102e0a441c4842ca4100414112080240300c203858402d003205220300c2d1500041541c003120001c40b07800d91b43e9078501e41c214000d489140d100380b500d0b40c01c0056100405400074040d140c0703000c8540d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 37251470 1250 37250220 37250233
    0x105040c0324110a1706031c030603080a091e150e060903030d05010f060c11060a050c0a0b15040203090a23060c0403030f050a0e010f113003010b030606090d05030d060602 75
    0x5d02103900c030741503d10650540c03041d104421800041105035410020318240006c006684c1c0e10360322502d0340008070042c00200c000d0003e2020900ca01c0720845042289003201c1d84c0141850751490040c0012050201805801c0001045543d81c0e0021180c0d00d0030b0180990341c49079421024140a040d0038050750b1021300021601141c403510801401c4940794001007150b104080807014011781c0c0d8070107941001084820000141400800c10800400a100d00c15048071450b0001e6855103000d00071100c5803085004201f844020030000621802c107541243c081b00740c804107290b484604500c1c07407100c1e2586000300780c204503155024901800489009854040e400d1408650403501d6110f0705170001c0201d14011418005940b04100d00421038841c0c3c01c0100c00058000c0206203084629803c0030381e0245c0c0010502060b48a403003442e00011032100c400740c250350428603a15400c5c040149547e021ba1310108072003090340c0d5000c54403d0803c0d0840280d82c0d4070007294101e180540b03058016100584210f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 37252720 1250 37251470 37251497
    0xa022205091617040309030f050609060a020a08060603070c0203060108030403030f36090623060705060a09020301020708030109090c0632040803040f0303020f0105040c0324110a 78
    0x20b0342400711244143c1c0d1000080c0103840b2008400881c064820b8041029a55000c8001800044030a43c0c5600880c01003800d072a1200c0c0c90391034a000104010380c0140180107503090203801c02016600400d08455003500d903070b0741003401c0300c009421200180d4148a10000010b400782c005c0010401e40e401380d41c0c0c1c542640361031002918906800b80c4250004080d100500c24003d655200c02c0006050302c500b9903112990301c81c441001d030703000398200c40d040c0300c00503c4070407090026560308181c041055a0742800d106194942e640c85d080c00515900d1280d49890400702190b03000e40c115110103501400480c0c507940c50304018002003078441c1088612007800003011031000e000740251400c01e2452aa80314914485c8010002950b010b00510442e1180c1413201050520085c409000a0030001110407151495410020320300100048560100c0e450030050001003001400a403094a4001d540e0245000a800350007840c00c0381c1d405203011b0113241c240880c1403403820400508407a6115610700042c0400e8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 37253970 1250 37252720 37252741
    0x80105060f060304110409052a030706020d11030c070303050a0e090108070b070c050d030804051e0703240c110714060901230408060a05130215030a02220509 69
    0x5454a50108003480004c00140d0031420007101c00310058004501c0c020342c1c1e0b4600d450411001d62034007401d040103004010a0041820351884004110000c10b21207242c800041e45607100e860760141003140b00d4000380711003001001100e2080904408a5039010b540e130070b005066400610b03000c000145000c1c80d2100754505005014140c2d1a0000940307a0ba52502c0000c913000c1e48458011140141d00120004443c0d0301c015000031021300035107441019240c146080f9040c61a22085101c0c014031407101d25814060004104003a660b00003006424008260b80f40003940d283c0c05900b0f110341d400c2070340c0d01c030409034802d201d110306000741c40442e51981d4840c8004058054075119541e0810802e100700d25080d80304d1000c201034419212a50400c60900c94480b4201da4040c0e00305003515031141d0180200c01c05c1a10505910900d07030501407d15001d642e0024541c040c840309614500b000204c0420342502290341200c80c520112040d860902038000e130030600c51034003442554401c42c228000103104064 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 37255220 1250 37253970 37253989
    0xe060435040807180e070608190e0a050105090303090c0f010309050118050d0203120a090606120b09071208030a0504060608100b0312030c07060207050c060a020102090307140a090f1b05030108010506 87
    0x611002604406d0b00f0a001201c0954004101c03031741c42c8031082d1450900004501c1600d0b842112200174101229682c2410390039113001901d01d002d541e004104100034000086600f40414a0403034080310300480720ba004034094840c00c00c01030030a5282c180001d01500440110080c098420342c1a120f4450b0410400d82c0c4901452074005041c07070019001485030000f5500994256100b05000102c0030384549101c001c0c040034000844600041409002c0206c1042240f00c00074504500500b40c216034580c0d034681c0500000c0c00c9401c2c2552030b80042070400c803640d000b107130140c000403040701c0c80b40240742583d402a104420080380680101020b1044040c101c20440e4400c2e42503200c5a46000d02d207075200c000a41c403a450a4866001d000742030f120030343c2c03650010304a503a1130398000341e19001500304050901d41d8652041e1042e0207200600e50341c03626140100000c86208420002d1103200180060016114000c6c0855650740311700c8030b0296840c1c11001450581c0c511a00800940d40d600b002c0c009140f4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 37256470 1250 37255220 37255241
    0xc0e061003051519030b0403050319061505090f04050705070201030e0f060402100e060a0914010804021f0c0803010e01030b0f06060f09042406030e06043504080718 72
    0x20074500f0b4000c102d06001000d042c4903608040c040c0700040e40c0c1d03158840c0c60f050039503084000920006c00d100d400b40f481d0500b0100a9140481000310303600d81030071301d52142e003201022400d1210104805030f5a94075950b007850031404c00b9006104a1a0842c4010300a5001c190200d010901e0301000c243e403010700242c602c6201a0f5074009104c2600c940e020801020000c40084040081182e05141c0540701d43c00908501581a1504441a0700b440060704046035210f4005042214040802015035501c29100c8021104800740080c4242d000c0021508580c0000d800f0740041c400000000b007030702c3c0303204403076040782c0c0200314600d801c0e10f526071146891034081d194960301c0001440b0b0320003414190070040c80740d040d000f40002054001400c0b01710340303445c4610440700400350610003002a00c1e0140642007050032843c0c007800892815030f4603003151030030700780502c22807100c0070040c0765011180c0c0740d44d010702940042d4002c0c1c84075915200c456841e55140100c001900c0b400d019100d02c1107280c040d918044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 37257720 1250 37256470 37256491
    0x110301050a12050a080d020304060e06060d08030c090a030506040b18122a010b10030b06040b160218060a060f050d0f06090e0102090a141008060103090c0e06100305 72
    0x5078508505040380b090740c414140ea490084d41940703000500404014508003810110240c0c1b60b280a041410441300d07082100300c41a000b00f010018582e40709100303603149030b80c4401819226141c01c110310071f2a0041d0100c1c00c1c0c2001c075075480401842400036210740b013107124501c2e8190300d07505d000301681000e1202881041c2c1d0780c0315009600d00c3c0a50ba0024003205003502d40c40c0c2c2c0f8103000542c01100d0300368804c0503200c116503444202a0345418040f4403c0c1c4402c2a07410f00380650341c905008542c182c0301d0f40c4a603010341000130652001c6031790850406002181c00411880302000d18441303004904c01c0549181c0e02c901c0e0010000a01240074107050109981280c07034090610013901c0035540901b0000c5000031217256988808a441e1400e807141003074000c0c0d0000016105c4074101c061280303004a0350040052188036001906450303842182c4080030720381e58501611a611040c0040e0003030005058000d205103c000800300341c00014003003051080e841200c0620703c45100b68010350490b44160703088130a8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 37258970 1250 37257720 37257739
    0x708090406080a120f0203251a070c03030b181906050102070b0a05030702120c0307051018080c07030b15130c020304090e1603030509030f0d0203070204270c0911030105 74
    0xc0c002c0e40c40f100c40d81702c0c0d030050342e00c1c1009072401c212020400090503010300300810901c0090013135040680081c11260001500b40782041c42e0060840301200f00000e04040c6c80c0d42c0d0801082d10b800602445000461035a40ca540c2000700c441803003501c407505194509494080001801d41c80003c0346000c80e400c4040851400829043c115510b1340028503900c00c2d03100711203d85a80b10340741d000a01c802c01014000d15107034403003803070b1880c14000b406009007065414084c0c14401d180312100ca80c105030303070b2081d94680e441310040c50351030800300c20750b20207440721781c4000c204403000e001461841c14501080380c90b0b852519845044204540c100b00c4080016031080c0418400303040c80e90312110065001004440f0641d00e100075045150110703400890000e58040351413007640c1030400410050100040203000007220003d802517490282d458060300c26512a844c020401601103402801414010048040c0c40440d00b0714504000306403003800c003074a00c0d143c01400540f0002c0706503416100c0061000300b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 37260220 1250 37258970 37259003
    0x20105040b0c01020702090703021804090503041203110a08090405011d04150e0a050d02060601020a05100506040204150c110a03150c050906210604110a0f140708090406080a 76
    0x41d181c220350380e00c00240d9420031192000d680c1d0842c142c4c5c07103005240e5015a03180003100080c8000d0386401d2200b03000345d0902540d000024400b10070b5034140c40c04201c000c007120f0818103048170b07241401c9592440718081d00c02c406003030107115001041c04600c19101405a642d031552240103200c0300010701c1c1e18008030580490001515007881d4100c007114641c010a010600710100d070700340400510112142c0c0d200c20000300c03420342c041c0320181d40180240040c101020050b22442d0b154407d0411441640390f581c000206680da45905030f4000d8002107812400038280e4010191007a407804800342c0f16020b0750050b101d00ca2510701104000d50303621048103c0711000b280e402c80040c2400c1c50030740090050900c0032000f180c5030b140c0034210406e940040301d02c0d0b0100b8180b0900e1944400391100e030140b802c21312503101091369501101d6000d212441c0c0010440c446520440e081d51031000c0c40807281000040f424203120000016090361082254104006550f901c0902da59900c0540c00804843c51504030a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 37261470 1250 37260220 37260239
    0x1050a0f020c0a0f0e1005030a08070615030311010f05070e0d060605060c0d0f05070f1202070f08150603030c0c0105070602120703050702010509011a060a11010204060507051902010504 81
    0xc488000318011074411412103000260108556080000c086818040400110801008180e00300e05c904013180d0301e240c1801c3c00700f034541c00740480140c212180010004c08100c0d0691004032221a2101e41804054507031034001d081801c030941442540d070034a480c090400d84079214960041c4420340700d0250b2410714505212241c001c0390800c0d1a041e07a10180051705440780d40c010883c9104038805046803601c0814090318a441010301c501c00c0043c10b00601340020710101d5140d0595812000340494200c503038400320300e00351142e00701c0000118000340c00100c0c3d00001910300d815500010b10703007010f50744403c00e06587e8041d0303a00c0701d4461380c849614410254001e80040c01e140d406100050324040361544c10800271003040c0d81c03203c0040d03503440400212550a106890300303c0078440c001c0c041100991800d980351046080c201e0300c17842c1d000030303003100b0075002e01c1490341010104070081d03485a554542c090007982200c3c6080d07407035008100c080205941070603001d80d4050783c161503043c03c05044c011881c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 37262720 1250 37261470 37261487
    0x105030606042004151b020f0d0501020903010c050d0c02030319051306020f0304060507031e02030703020c06011e0b0c07120804031a24010e0405060a03020d15050106050901050a 78
    0x45064000010507541c0c0c1c010740100904c042c100301200300c0844991030f0b800900d43c000445021150b03400300340c18000181d403045420003e12504403500144240941040c070f0080c0705c0e034182243d04d586060030050003250003801911510a5100c001c010716400084141d881e44070488685042c4205101003528150181e8040d41e0403403910409500070724020f44c1c6038800c0b60311200e02d00280c0d00021007000108081c5000d06540501c1c3c030300c1c05200340792a00000b2154081000005658103030003100081c001e034031030382c15660441400011582596912500c3c85c0104000c0c0070b81c80242010314102140d200d0400c0100c0b94800301480081c003000b4644082404400034103070f0100d0305620700b08000004150312829041514048403080942410890459034500f04044e50072064014001c40480c0c0581e000308140d125104203403030124050341d1b4800011045600e64000a5008200348101424450030445121014a208400b042285d80310001950075005400350707a07000402c100001d00700984030b02401c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 37263970 1250 37262720 37262741
    0x6080a0507140d0501031e03050d050a150b0408150408040e040f02090906060103060f15051c0204060507031101091106160503220504020f04210b0103030c0515010503060604 76
    0x100c2e02000c803800e031204640d800300c507449210540700c0300180b0500071016a0075040300105d1055000c620f5995902a040703010359000300c40419a61000600c80200c1c68219010182c1c808909a0a507070300d843c602401da80241c0110311040c81824503040b021040d10070154011608601c4083c20a407601c0201c008032080280211600d01e02d104089006848801106000300502d07005172001d4a40718000600301d462a03403202106606018080203000340304100050145664030349140d6a0500c012642244c0654000302070b1864800a4001809580035025081c0c1d288260384100048079a01d025a0984100741c40143c01100c428420100074034002e070082084403440202c60800c0766a58941e541543c01046a045160011600620307500a410b010080544000c4030214140181c040c42d40005e40118085c0466002110000030342c0000c0c105000602164070000b44082507031079142c002c01c071140107081280e1504c500d400c0052035a01c0d2006580c1a00c00103001031415a0fa0a01008041d1a14500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 37265220 1250 37263970 37263977
    0x1308090904060504050d0e060a1202090a080a050d080105031b010c0b010e06010908150703110403200108060402030403080402210a080702010f09081b06040902070c1a0406080a0507 79
    0x2a45240c0310008154401c5004280004242c42c2506080741013035028402d020030444018640c03410b80d074902c01510807138000392402c001c0d1a00000c050a00034030070f018200b54440a98180042c920304001344008850f4400c800b50b0300c030a07030300000507203d2504c20300038943d040d000300a000c90380b6001945002c1488074140340c903a900140c2d50722030f030f10540020381180b0040302072882001070f46c4d42c009910030003d0001200030001450084145e5513443c01c0035156404044d1601b018040c0703151f038441a5000740d500001082c43c00c0b801c04140911070401034100078042050500040d0041c80c0910070f8a01c80c6030140c0300c01200e50b4641c1d0030000c2c0340c0e0746500c0000b2801803018411405480802c40303500024414034000e6a01c0001c0d00000d085440c101038070408010300107030107000840000c40c0503030300051100f152415162562001030f4a601440d0014180e480c804107040c400e011241d001c000c111358000000000d407204000b41c2171044c1c801c80c0107510201d072010f008122003550319402903038002000e14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 37266470 1250 37265220 37265227
    0x503190c0e040203041b080c09060915180109060906031203090311010e060a0e030306030a0b0403140a020d090609080d0c020607080313060b010e090109050405071502010c020601080c091308 83
    0x30700702d81064409a590b00c601019406c1d5005480e0405006085140300038131203400f041d800280c90400040090340126000d10201d5551890803482d01d2010500808121110002028490a414091054149607130502c900090082030701d00c5984c003030340d030401c5000703611402c229826005803160300e01c00c804104804d82c14200c100420b208803005450142d0103001e06042074042c0000f680e110300d0008980340c004105012080d900010902186035001c940c49416580e507040544a00c00348084500b4800c20005485048980c007040414107640c554450301c55180d2201d10840d81418103002d14002c907401a1159440740c2d004030485030302144018040e9191008035680c04401d074000740c5240414640302060042000401c0c000c0a500300020f1800224000b03203600001c2c030581c410320072045229074440c0410b080c86810b00c5140064401500050300070702815100a0080032102406801802600c0002c10310042c0030131600d03050310340201480302030384941111001e1007a00640441c0e10305402c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37267720 1250 37266470 37266497
    0x20c0a0c0807050112060503030306011110020301090902120f031c0b0a0f0f09020309060103020d0201020f070b030603070b040825030506070804060c020609120a0c08030c0304030306060503190c 85
    0x4a0360402902a41c0081d2200500e444009064103c16008401d0f01c1818200f00380036503140001902d5101c1024a4440c1c00060100030403420400e0b10480c803d6050b00000000c600101c4941103d48514030070341c0c5460700281011038564480c95032504d8510a82c004014282c00030a4401510301038101c6204d0001c3c008807400002000840da13941300420303000041408200c0c4440890044000340113000007940385180a00c1529102c55050000901c501d00d10504102503902c02c02c1044041220081110665902c0b945802d034150030440f4818440d1183c80800703e4005c00700d01c02d9030100c0d0b81d400002c103e01e030001e500a91781c0c104101c980e1001d404003604004045407040012900444403600e8000c000e04003400d01c0001c0e134030403410040c00c0d0340c80f03c03043c004590f01c0082d07103454603064002040e4490301d031001c0440790003d01d5080a05641f80100030300003101c6054000318080d0b403003a101000440d039550400c2c0d481d030204581c2826160480d207101c0c1c02483c0310780c100c11801c00c46850203450740d1300f04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 37268970 1250 37267720 37267733
    0x6071d0a05061306030e0f0a0305030a02070503031009050601050c210c060c0703180608151309050303100509010303140f0d1a010206010801051311030c1002210f030703020c0a 77
    0x180b012181000f211441000b1250705881000456961030000e0f00c00c2d44000c0d9019540c2e00500344008040040010018130042e00d0740e81524500765200083c0d0350350382003201e01905204c80078080e00d410070b490400400c00540c001c5c401c48020007811405081484541402608058190501da1401c400d04000004408005020403442401020b0611313441e00d105040092680d0f43c3ca80c0c800d213840b000a48203200305030300b013501c7c2940040b030350044243d00c2e0b110303401040040c000185400e61840c00d01070b48404004010014510404092100001103543c1c0c4080001035802840080c01081c045405a80c80743d80c000010074550f881805500c1c81d00090f910101d0455400b00f000e407007440c600321305d21640c84d03070b043c07202c5401003100780000d000780d08120011a03400c6100c0f040042400c0c01c10502c49056890901c004044088020100c2c91080d2900d040039440381c3d0310041c000c2c00200d44000864503001c603002035401d03e05d40318032441d045a8130800281c0080d846072504c550584565401d54000408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 37270220 1250 37268970 37268977
    0x7090207021f09030c090203010f0e0a110f0703080a02071a0903070f150c020f0d03020a02010e070b130803040e040f02120a0c0f050306010513021c020f0405090906071d0a0506 77
    0x10b503a64603459901e0342c2498513200c41107400084c0c10500401c01041a6100c0e00e4000c000e039045924480300e203403140702415006100c032080c01120b04038017150503d4008518030140c8081400794603201d036166038504c0c00408a1142c100018160450348101000d80c40d040c01034180c0c000c000004484c58004180c4412164040c410402c40303030f541c040320702d07580b0170903240c005d82c04086550b00040c52011a125080d40d25154201000401c05502291940e400380c1300f50041c120444401342515a410344071060103c4951042000d80e281c032000c8280000d59a00000440c1c0c01c039412a034003480d10b0f881c0d9546141200c0345a4000ba0323400040d18802c500f03102e2090111068892146480c5000e56180c140c6400e13490070240c2c0414405d8109000401141d142e480881d803100d00b51204c0142c0d228403c40d01005a240d05005200080b131012036403540502001d00240140c401c00c40d940d8500380c0c1c82110090b95082c04035041c500103075085001284040703001a84610f14007000b0003d400083d182c0007c55503c1c2c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 37271470 1250 37270220 37270279
    0x30510050403031407140f0d150906050612060112110a02010b1201090206190908030307030905060a11070f06020c10050f01120503040320130506030d030203090709020702 75
    0x35524001d00040503010700c1450011350001c4590f14151400f800050802461701074403060541000484045d1205141c08485000c0300b001c00c07c0098503107034540b004400c1e1180c003d82062901d00315010890f8075080040d652003100042d00348000303948a0b401100e401c40c400b01903001e82c640752941c3d003604c00b400702d0140400144550000400c0c925100c10400d40b030108900c41e002c5640340c4121500586c0ba044d040342c80381d100035940100c0035002c0c6842152580b84542c02211940000b1051024440d41900807038442c1c0c0c00350b402c84030303035132140c1c41c04901301d454103030140e20003403420000e0100190f20411b210300624000d820043c00c140070350f050780d0b04001c180e5007078805099464003009003644600030200e0140011030f00d800b00c10500c2e555826520320503400060541035100c10120a0f00006820031659008082c0070141d1400f02800444082c02040e81c01078800c0c01258510700b1428403030710a8a00c80c03809000104586868203172964002e5210103c180d8000c034107507600603200c0d01c840c1c140c0004013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 37272720 1250 37271470 37271503
    0x3020c0703060e0c0f060c030406030902030f0a050f0105010e060901090c0908070b0403140a17030a060503030403060c020c090709090e1011030712050f01050418050a21090312050f040305 82
    0x401c1144c204443c0740d12403d00c040c0701d8070040c00144084c0400000b82d80949005050000760a0344a00000c0d01e0903038160041c030040d01c101e203003880421202043e4071054450240090129980340c2a080c2c169010444160703810103001c030010030a00c0803d4208004c0321815003404403809440b20304150030022076402040c42890002010010080c4082c01012020810300c050119010140c0d44c5210030080c0320325a07401e056010000c24000072281d4000402400c008049955483d640d261400c041c200c9003c2c540c0c094040c90349003030a5410003100301440307583d1a9640c2406a402d0007280c800400c410130364405507218107550031000d8906482411240703a0300440503900c905e0881c4000300010060011945520f00300814000c1e158481e80f24030f41034070b0040f2804103d103441c0c00d880c030740108141e100140951007400f05400500c040f1080024005a07510450b844c1921a0007082e50641102d03c8014201101059103ea0540c460300c00f400140d000050f0382c41c0390550b0303900d03054680b9440d2019031111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 37273970 1250 37272720 37272733
    0x1309060608030309151905040219140117040302120d060801020f130f060503040b040807021e011d09010b090f1002100b120a151b08090609150703020c0703060e 70
    0x1300b95040008449032035903404050110300e4407054040c0405110590310300d8807034440c400314085603220709041860151402c80300c03007519038810740303207000110403c542c2d8041000808031041d4604520f00030362040781c258004104188800b03000805070340c0004c070091801035640d800464011002e0004002940741401c01a0f1201494049101d550303031507500284000c403948104208507074008094035880354010044a03a540c0e13036400c02156510810500a42c07007010f40c07101204115417442c00300076155003a610707029401e582c0840440f200b100c2c003100c50391001108004220000401000b007110290140000c42e074206070b18082840f60594589681c0980c214100145135440da510072860085da0868046030303055404800c06031960b500c5200540210842c0c2011502031256400001e030028046d080d4910008002030010543c01042e41c142140b030040b03501088244000141c0c000145c4002c9034920302036207407642c09900a41c04582c1e0b00003240a0100004046000c1e40314200651380c100010703000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 37275220 1250 37273970 37273981
    0x2101080105091903050c0a12050309010509030a0c08090a0f0f1a0f04030303020307020a0804081b09040302031b070503010f0605041514010e040b1203040e07030603050c13090606080303 81
    0x750303800103100c94601e07480020030840c0f45803060b09a0301c007243c2504005554500d0740c4140e9081209038080503000c03100e0710614580d4168094015881584c44000801068488150458591103542c2c19000094500e010240c0401c0b400001843c4000f002004502d803036546401d0b03110640180d610003902040203010421128011100402c01c2e540600320b0103141940001060003540103601015041642c0403000030b145a0003002085004c2e82c00901c070a40356079440c459565618079641c1441c01001150020500302d04048640c2406940d164020310b040215180c240c0f50700c2d84a9101c80105131058140000302c41d20207209404c109280c1c00e4001c10040d00b0142400b0698902c948010741c4040c11080401c44400d2900207403030209002d103002013982500000203000b13001c101d150b159014510100c00a000c04c1d00000800849145001c035100550b59424107034103c03079061102030701c1c6030000b2140e8051890007050448146a4101c1300084101040c2c4070701c1c00302c9007181c024950a9200009100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 37276470 1250 37275220 37275223
    0x4050705090a080106030b040b070201020c0708010606020c030606090112021507030e01030c0503070207060305060102031e0301050f090108211b06010608010b0c1504050a14010204092a0c0602210108 87
    0x10141c01d040009205c074a01d941d90340015004000c1c809441c1d411244007040780b281c400e4040f120341c008540c0803501c0b865180d999030f5009100c18482d400151043e41e007444107605010410b940b07c0c080052000c0216031800d0940e01100d489658201d80c01100c503942010511280d90281225500030340d107103007001174600b001401f2501c0010100302480401e00c108011302c1d50015800c0191031041c64081859160400103078a540582101540313840b02c0351001c2035905880002560480320200d4075050030819410078040c0f007a80a00030700581c3d40140d040da05500d00468130103005a8002c04c3c110345440252a2403600c5a01d03014840c2c002a08180010810564045241d501501444240a01d0b2001101a080c0d07201031949621655a0b00800002d06010061009201c0380c1c0e004100e10881d40c80d0000b08078000d42c41805111030840c540400d9494980b03060a0521102030f13004c8003061044c00341c5606461130b9114400854a040c0c00b0004191020350700c0003106240b00c0303402c1a8490030f504152005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 37277720 1250 37276470 37276489
    0x60307090603110f0f2e03060501020304140109090609021308060c22090c09080609010c080a0203061302040803090405090307030c02120f03041502011b0801060e06090405070509 78
    0x100d5055041890a1011907400c94601104040450340203144c00707200000700320300110002040f5408100300001585010a0045c02e200c5201c0c1c2c3d02201c0480c150070403041e02190704034011140160310900090201040029048242e801d05060280703541d5030329080c040a07034206400840d0b41580204202c1640d807d00d44270000030b40191400303442d140c903014102222500411440388540a603641072001c6000c205074920340030707001c0744406104811245c0d901604440062040c1c03c80c52007074000242d150701c418407422008548540e030b2908070303032560301c054406504054211035020301e0000c21012200301c0b0344020b20040001401071600d54000324100301c1100e00040110420f03820400c03030840000e03800320713180c451140d045a45a00d40985d0103000341c50000d01e010b2005c1c80784030000d004a440c00f41c83c501205000c0069000b031229011440c200e1101400c641d180e2000315005600500a03640501d2010b80c4c019400f82080c4d0900c0e611400040075250144d44002c04100c0006247c01c00e0300744014038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 37278970 1250 37277720 37277729
    0x301031416180c0c0203010f06030b0708040807060c02030904090311120304080a14070c0303020105100503010c0801150c06050c040302210a1101032301050301051b0405060d0204080a0308060307 85
    0xa40c9070324603158060605030005140014915030b03418885601a01401c2c000e029a50060000c11440205540e42401010240001e42d08080c1c0d82c1e000410007441001d1592003554030240603418a282562010301a2a2440c01e80e410343c0820701003412103840b944516900ca501035a15410880350101d046801d000f5030401c02a0f03090720800c2084042858602180c1200001d0302d002c00c070b144101c03806040a0700400e80d0090040b442c014001050603415000540645211803c8040d0306136100300b014200c1c1d4081f10b1040208600c64010800700500c2208030316400b071036040c90402c2c81c85a80e1614211502151442034806010400340154200994007206a01c074294a52030710005288406507255001c0300020300601c8000c50000b0316901c81d07084814801034404040450640392071201415400034015203009601e0300c00020201800042d0f003a20324607052001616103420201400003684c0031a90410071513408000014032024104a0100010300a80c4c0c3c182560402d4010103080032100e510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 37280220 1250 37278970 37279003
    0x30308070c051506180c04050a1202090612030904020d0219020d050d020703090f03050a05010c08100e09070819050c010801050f09060a0509070c02030f0607080f090c0603010314 78
    0x80010000300001400c0c8200e000300114911165181400100e0383c9034817540c4a44000c1642e82400a20380d000c1014000f9202e01715180c0c0c1d0b129032a802804a802000d0002940c40440c1402080716400c1000c0d28a150540c018240d07854000e400001c10180d0f842114841351481c0d000441c00543c0900034046620400c69102410141800c1d1000400070f01501514120f590790001714041018040d104500080155910702d2496540e241040d5490722600041a1a10350805441c1c4094901c240e00f105d100780d045a180c01c0020f81098680740d00007d00415004040c0300d0300c0760128141c40e0800c00c4514850362034450709604c03d0030742703000c030304203001800014180071403040144141d545035010542c451500b600c0341c0c409a80e031800010144980b541c40740b5001611841807220250b841402c0300b605c0d80c02501100d242003c1ea500a543d00c0208584000000d40c001e001300314a4444040540d4204400d00c08590b40d131030b41c01000038015442a40119130b185020a142c40300004107001c2000c60004404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 37281470 1250 37280220 37280237
    0x12090504110903030f0c0a1a220b0c0711090108010b011202070b010b0306010c060603030206011a1306030203070c17030f180607031d070909020f0919021b030c01050103030807 77
    0x240440c4c0c0c2c034000d248805000032808524088041c3c001c00101d03221a030450070545100380d1032558150310002c16500c00304140428509940d48200f00c600f2a0803440d030001442d942999001c8592000740c0144108a0f20300080b494403038100e580c3c440724107000e171201c4000040d61800540002d080c1034611010702c0c60043c0140518000b14040000c80c5d411581da094103d0354035a251001203801c1400740100403e56464143d02000b41540003505c40e059450303002d281411000081810540c1e40552080b5401d0a1458101481001d100380c025642001803802c029034006442d03079440c0110641002c400080050100070000d4000c0d041d070441d41c000c029801c4501c040c030403582d1203a480c1d01004202c1d9060548400d04200c10800c11102ea2039005c04540566910310b460740303003240c003a12044000f43c0c031075500e0103044c43e110f01e0050905402071845004100e640303c408400031019400003210325940c44010501a0130310001400100441d2000900003e859815031501506000010344584c04001c80c15 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 37282720 1250 37281470 37281487
    0x10e01051f050904020f09040c060207080307020a031b0b040303020f0c0108151908010c02071401080603030703030902040906110304150e030405060c0f07061701050f0904020402090a031209050411 86
    0x80d1415800c2e240b00743c40600c0c1a5550f40003140000c03016080242c0c000d000e08040100b40300c11080000300b070b20515400c2d501500c5d030712843c40755079020364136010b0742c82900800304000040200d4240c107003142c3d000304441082c42c1c5d82c41040364075070402e0f402540960458500102414000d1140b040ac150007400c0000f01c0b42803024011070780b10700114250380920840796031880041240400c081c010801c542c003d00c0750000c1d4950094440300c03140300e000d443c40300306c00001074190300920351588035040150003541401050389080300580503010007681c0140c0c1c1c03051301328007280603030103a015640b841c10202c03951703130900f4540300301c20340c190702401a500c40c6004214096510040b08840032030710708564068543c0706074220f5030308003213102c8401d51042c4520040000c02ca500491282c030014201daa604540307a90703400600c030b482c140c0700c60340d07a0340002050f000600526066024140200c0c001e01b00c2e030346444d00e96403480100b003030350310a0710086945504104600c3c80c09000c2c605403644201c81040c14090358 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 37283970 1250 37282720 37282771
    0x1009090c0f0f27090501020a0315050303040b0a0c0602040b030703091a0105211c0e030706030e031b031303060e010b040218010c050f0303041b050301090302070303050a02150108010e0105 82
    0x2c02c00e00c00400045800f82604410250014800282c01030002c41d40c84400f40c0303001d40240400040061440300b050b0300000c0910b404800c0e101120b2040308454600307140401c0c1141e900740d0801086581d030727074280b2004c21142880f002440c071801c4662000107084032142441c040502461169241a030649030042c803081e00c0d401640c1d000e1110450040b88030010b0b90344000c3c10174444d007841c005c140d0450741207541500c1d0b0014201c01c4003a419410364424503200c40c0210b003503c5035024142c0155104110900508001c100c20380140e69004c41640d040c085104084440341051354000d9603003649501b03007a081c00b0401e21502010711011901146080c5c4070042050704001034841c80780c1400224200c070000e21209004461850001d0815287c4c0e903e403030300d0240c0305410b2500c0451900c1030045e50204240c14144141110300f5015002801014507540e400c03a03c544c04010544c5c1107000b0310700700c0b411191013246154081e01d159000401c11651607004a03003110002010742140d0306001940d126115075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 37285220 1250 37283970 37283999
    0x60901081c120618020702090c03040b0105010c020d060f05060111011a0d0f02130207050106061110050a020913020702040b01020c0108010b070c0b18090c090303121009090c0f0f 78
    0x7640c2403142c1e01a10342203600380104459405a42c14183e000d6410411000e568000c00c981d510868586629450340c101c0048180422200101b03440703204e030014086913001e0141803200d240b0080a2503206189661198191080400a2140c2e651140c0c00d2201542c0c00100030254485004002c1107002280780849403451402d298490160700f101080109000e01e21b0603081c503258010b4810b0059804610303041c4000d520000c0152115440d00501003030f030f01e01ca04c0c4d4009454084c0401010000315009019006000103000f07201201e030308115205081e154415441a60843d02400584917906030040c802500c41c003d90060440d04190440310700390382c100c41ca0303505413076110105a0325081c5c51301e480954200d1680003042c442101254001c00b25007038110f0300d00102c1050300c03500d0a54640c017030300764054000e1480169042e00103002d00040d002e49281e500b40c0c00000179102d1585160b45900d00802c03143c1c82642a80c80c13200f411020710144654504180040102400e203c0001b032510000a84111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 37286470 1250 37285220 37285273
    0x10501020318040902060912030703030e0d171302040c05040305060a0b210a20040c02060103030206060625050607020d020f0a020402030c1e0307020d1e08060111010c030506090108 79
    0x203603136004c0c400c00d640390380b01910a100000341000b40c80000c0740942a03581d410041003280000c0c10316850140c00b0101003928900c90f021074030340512f032030701b200090302d8141c0c4000d260510365280200c90a000d69194000e4042101c5c00f61600c035925811420f10a00303150005041e404844c0c109000c0320203a4664005400345030111003c00d170b1000c0100c4040c2c50620844200103040002c0070710940c4221f002d001071a030281c1c2c2d4112000c00060680b1007083ea241c030800d10001d4050f8102070006646801e2260090440201d201a4030740740c01c090014007071000901c0d00d400d42d1198428410804055010070220000d1802400248028400403030b00340e41c0d4481040700240030743d4012010441d01120207040d48d00075204040040d144041101103000c040c0c0044030764034014490b0328490b0040900441d90900031410500052804a4506c08240e03109407000c3d0146040080d55082154207007002e00c00d071f85c03640c400d0356400b084031300700383d0200300c401c00041e000210b940d00408840c0c82e40b80d04e410003e101300e5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 37287720 1250 37286470 37286479
    0xb0406030f0504020f36070905030a020307091d030c06220803040f08270108012102060a0e0d08070203010b0108011d220f060f0212011403030f040617010501020318 72
    0x44040c00b02820802d101680b0401c0046c11108180003883c401803140c8910b0075540c42c04540350f40c88c1c081590366000d450f8040d4140e081401e00f484004c2140d04401040643c003407040c10400c000d0200c040c51079001070400c0040b50003820510040d02020451416491707482c1f50300c5205080300b03484520305840301a100501d9901440c29403002c000580090b81c00e6624080c8409a0b20388050301d48503440c4014003440d50000b00b02000200f1800d000010007010036083d071180704640ca185070f00344182c0e81d102400c031070203210310140041c405503550404d07000d885100703403e01340e00c5001910505080d60810f000352814050b450340180f280070014049818042c40c4030700c1850b0385456100c0d460001290700c0000103040c44a20b10144103001d1710700c0c4603012403886200100a080f0044c00142c0407030042c1c1a100003072584c09401001441800d2024002c14840242524079004c0145542c074817591156000c8004641c029032100030324101c0e0301d442401001d082c00910300e40f112528491a41e50300e4804010301c02c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 37288970 1250 37287720 37287739
    0x303030a1509050112020916090308071103070b040e1311190e0a020c060c03010510080702120706140601030b0102070504110906070804080d090609050907030e06010b0406030f0504020f 81
    0x44000007550001000400030402c42d03541c54424802d8180260801a8054142c2401244407104400c0020901c08103640d02d8503c01411643c035440c1d036503ca400c05485607401007401d0300d440d035020f100fa00020f081180304e00d5619450480c02020a03034004028980b84000e40c02440e0208041609211944400312001140f00007031009844030b104035500900741110262080120703081c0743c0e0b0300400903860010100c0c0c2007942d4641601d10f5611003400750b0394100c464030030b20302c02c614010005650030100b0707401620240c146040c18202c1a81040034284d82081d15994003050040c01c1450f00c0303411110a103814850701c41c80100203981e17901540308250003640e542c00340781854207426047c0c5a04240040074aa07036140c441c206606242c116000b1840740b4050300400f10ba1440c01a41d4003002c032006a101c5245ca24036290422043d210024200380034181c0390880a910154184150741c040d081c40d050030b54566007001401022039500700440b5203001c2c901014400960b85050200201c0c2c40101d0f1350511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 37290220 1250 37288970 37288991
    0x409090204091a071701030c030602030408190207090c0c170903121206010801150906051602040f05040c0611030403060203090a05060103050d021002070b190b060d02070c05030a020303030a 83
    0x145003030000500780351040450320700301c0d0000210f014054441e50b0b481800d00070720030b0860b003501c0c01c0031300c401401007000d10010000a141a0040c66110740649981c2e0708000c403248a0880340c2e21401c500c1c40060301300d094103201a01d094401c8014a25440c606a484180941c0c0d4079a84444180320055403410081028006030340d0801004015078074520300c00c1d4580c40060002c20030400c050702e0460124040500110300100c0c115942180c1903129503c88480501c0e150080c0d8040c2d000414008510120400340b03c00742c0c07680d01414547c40c4c02502c0c009520301c0c2c10f08000c200700d4480d400020030841409000141d820000041d0303000e9030740004005a0703e44030382c840c040c0342c0a01001c0040c002d020f00000001400340c00304010000c0f200a400791211b025115062000300d200e41d134030061890400703c1c007180c0c0460403015441c248510111001482500031000250342c0d41101c0050206903400007881000c000c0f08110040c01000150004e0507185510340c002616400b000340710000c407556a038003006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 37291470 1250 37290220 37290229
    0xe09070c15021204020906010c021822051605040203091e0307020909030c060a152303030316021908190e040c090e0601020606090c0904110c0a031409010504090902 72
    0x600501c1900011035036105015422a43c202d41250180c0c81521520002103076540070300092403401e0f900904400c00042149000458003202030b00701c0c001440320400924100700d01c1c00b1000101e0b80600000c2c03d0524400d10180c0ea13540f1241c2007240103d0040c0184164010001161800307510109079030004d0040840c85c003890350003051000780d030081d00e01e010b00050140100040186100081c1903500720b41e80d50650038243d64803000040703030f01e64046100304602c0f0015038928081004040d8441d03801e49020300003910b19082640c0c01034001a82c1142000f80f55010170049101f520b40d40803506040f134580d260328550780111556065840015040c0c0345080b44240985001400001c00420031640782c031000800c440300c02c2c003c03829001e034640c0200d8555800010407a1040000410501a0b0317910344803901c0040d0006004c01c5c0d082510303a074660105c0b42445024240401c028402071415225a0800402907015684140310240b000c10518256990140440701a264080300c0030440c0000c900c04079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 37292720 1250 37291470 37291493
    0x17010b0901120c060203040b090f130507030510050102150103030813050a0c03020a05010305060a14061612020607080c0306010e0111030307031e0204060219110a03080403020a060e09070c 82
    0x40d038410301440010511802000d160350806002d50405242d00da00d030310060369617101310b0242c68064a801d20003c00f00d440d00d50f45880e050f0341c0281008900c01e40701c03803020007a658140c0300c20010a84407402c00040d10300b10320ba258020300b4248000c2a00d403110b0f00030503030b81d51010300014042103481c40c00208036140e00c002841c4100d42c0030080780e101030942e00703014092881c9400100d02c01c00560000060640c07003801340300d000d003200800d0455414a80955103002c6415185680d0300040248003809518900c0484443c80e58004d90705507155000c540703002070400c1e07001031080e0700b40035400e4180000d0707407440c505590b4486c10038200341d0b007481c204000581c0d10182c507200c50140d51200000b000f04c000e906401c0080f0f884071010404104051030040d40080c1d025900903440160b200e0303002005480e0482c2900704000d0b025401b011130001c2c841c80031a1850302c1d03d4005507081040010308104504001d04942c008100500d04042c80102c42000150000c034046c14a40412014458400a018910044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 37293970 1250 37292720 37292741
    0x522060c0912121425050705040f05010503060604020322080f03011d07020f0a030c0206091008180703030c020d03200f0c060a05070314130b030a0e0d08011701 70
    0x450707100c40702e5490300c40d4001c0c2d4401c00280000c0d41c00c5003102c0e000c1956009580c00c907011584010314500d40302110140c689070004003926a0701ca01800080c140d201ca00c01c0036450001c0080200e019030404007490f02d0008094482c40c0102d20400400502d0944000805501d101d44141041107044a0414503194050f081c158410000008000114200300c08205100c4290aa032100035a5550507002c1e83c4030700000c0c8582c51250815003545000a1141780800200c0340700900a44c1003520381c00116800600d00c01e6110007003429142889012000386120341c0800c400c5200500030750307046650050a80741ca4000c002c0c004d5001c000c1e642c0c02c05024442800b20705a2040145141038540820b490342c840000340946014000c05042d803005051410880340c20034405d49440d840d00c040c03503808884050310044036552944050004d21070240d03407648603800030085d01e0310f510b860f4104032500e24102d5050422000140e80703c050081c0103e40c100b05882e045803d0004001400e2120651841c00340038151071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 37295220 1250 37293970 37293989
    0x190c0b070503071803080316050403120206010f0e0402100f050702090406060501120926040305060901060905090607120c020109051204060314150f0103060803070311010522060c09 79
    0x300400c150340080a94403400d46582e807815154120300605038002520700018001d98410400150015881c00484491403410315143e4503041e6603454104640c403045001d400107803c07003c0104820108404500b0140401000d40311031405e0540c0051002050812100284506a0180560b8030301400607501c90f40c2d005003510505140034504500200400d0065a020400c1c00f2925000300d4910711a4101443c4e014914001c94036410007682c2200042d80041d14841c0d600b00404400100705004081c01950010008606036080540350703420385030001c01a4548d40d01000c10010038662000840410f0318461400080c0120211012405844441c00180c441d01ca0501d00d00d090340740c00c40041080f00c1c503c1e42c00b0002c41c84c14840e09103210350107440b0112031b699091003090491400158111350a0814100012903030b943e80f080c581990003d85068011490303801d00760030107840030301a03607074001c1000048111142501103070050140a410f0060304c0c0300e6a54880195480c044d24410020701181c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 37296470 1250 37295220 37295243
    0x1504090b04060f020f0301030b040503132304090f02092e15030510030b0c12070e0a050907050f070606050d1212090b0c0a0909020a0e03010b030604020105190c 70
    0x611035a2414156412101c161a1110b06210148584280e621240d441c8a4081c07440e440c5851f81e840050000d0000d0b11076001c10840c1401010007260705000401509010113070120703000c0c42e202900c00700c61003018062030030b002413640090760388024080718990482c4c06602a880381c4400341024040301c240e01c11103012003c0c0c2c1c11031454603212240100d544c203c1602c0005180c60b40704405507030081d02e080410103480d078002e00c005040070404c140d0210806e0140c9013041d907041e1194208040659049020913a0680c016025081c1001c00c4401b60000f9502100b040c141030f40018001d104024620040d4003002c180001001040d820110042c0002420b020030300b0780743d00b0030f0000c125003a0a00d1010401310300242c0c1002000d8050701c04500d82000319091907644106050700385e60700440603203081111112020610b404d041c40549400e13003103075413100080220517003850308407414802518031035406a410000142ea1250454101d20928000d040c4211500c0c1c50a0f94460050003004041c040386d40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 37297720 1250 37296470 37296473
    0x9100e010b040605040e0607051602030a110306070f05040b0f04030f0303060e010905070903020103090201200c3102091302030106030209090a02091e010207031a01030318060f08150409 81
    0x150410301c446141200d082110540c0c80e810441101e131416070030f000a800620005034202d000302e010b01031084ca01301d480c080140c8242d00080c2820301c0900129000f62400400200c80c2c00e003000680d0380510135080c801032500f92000d0240c154040e45c03144d8181d8440000d610341c4140400030580d401503a000c00d0790500c02c2c07081c3c940a40a0007190062200702104240000380041150180d1070256100d40c64014115007160011405001005820790501c24580701d0602e80c010340302c1d145c0c0604d00300302003d0030540d0524000c1000c030a45001c914601100714150755031444241010149104800d0580103030740e412942c02052074074142e40d0824000c107101000003c3c000d5055002841c00d10b500302d854070003641e110004903040b402050013651300200d1641c4441201d580040f540c10304010140100c0d40704568a0b51049003070041c40c0035444440c40c0510042080640001e4010120200d0001144100d0304080c001012001621407650800c6a0080840c160302d0090303268200880c409001071120324500d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 37298970 1250 37297720 37297723
    0x20705060318060c2803090f060b010e01030c0e130603170c0c09070203030601030b04060b0c03180a05090705210c0a09060302090612041728020619020309100e 70
    0x41a842903458081c1c1d0000a0065000d101150302107400003050300e51102042440007002d06950610105140d507403484400441c00ea44800b41680c1d03c00d81e27010801c01c1c1036900040c80c0c0030b68480c560b03040c1030807c0440418240c22030040003440105a54915007000c4105600f406401b280d403004d01840c1031960307001c0310001030a00801d01d01e801c4004540000c0a04130510014910840301b42c401a0000e0000c90500c1d8030035001003032000350040001c40c0306a120210640c1d140d00100603140c25900c005209031818a0b410001c1d0748400048920490f81490714012480c0c21b00000c115504000d0300040340c1039203840ca16200348000b0242e1203035810502c0c1c01c0034501c0361a8055001311000c40c111010002d271081c403900841c0d88594028107202e04259000401d42d40e105000380080300c48c0c00304000001003100c6040054800d90041d034040c2c03441b4403074030040d06150760034003204202107410100820007503002c5000f50b0b01100502000059aa82c0c5040185041c61818010300c0165400d060200c100d1510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 37300220 1250 37298970 37299001
    0x20f0a021e0a0c120c05190509060603060306040b0a15060c140c030706050d020c060a05040b0901141504090b010602060a0b09041104090302071a04090c0c0b0105100207050603 77
    0x1a0003801e00101844126a81c1c2d0604030740080c8001d03c40d507410700070f140104084070a401d120300e105d036160036150350015a0b40c0c1400c80845076640c002010812052070444c5444d80c0100042d10380b01e00d1420441d003c29103c800c001e00240c0034070f0040000c600400e1059000703a042c00c10240300c03401e00d2900d174200205405080401503490101243c650240464045500d0f0302d01d820050041c42030a241480c2540d060f00300080481762583e00b4419218402c03402e00c0138a00c80d40c2c0e2140c000502c0d181074500a40e0390240500403a030107a25052204c041c0540c00b200d5180c10010000401d900202e47c180054081c1c00101c2e4020580c289103000066203d8000a4480c001ca0300c07a00c003440501030ba0700900400c1e480440e000341140b10405000245404c0517840074200702e00030f1065409440d1030303039155600d070001000c01c3c035a1150005420440d41c051440740c60f04081c564500598092019151900814418050035210b21082500404500d000700400307002841f020b00f5442e282e1030080c2424a007001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 37301470 1250 37300220 37300243
    0x204060305090313060807021501080c04060812030103061116030c050118030207030f03090803041815060c0b22050c0f01020706090b0901200a0201030b06040f03030c06020f0a02 78
    0x207090101048034a6030100070303a02c01503010700752202d8551074036a007110780880181401c0150701902443c1080c0c1c041c18201da60180184000038060342c0f42180c1800300300d9040b41d2002c1c0340c0f0340000d050203e070441c0c13180849044075041080450091745448002d00c8501ca84c0702140c40055181c0c941904164004a00c0c240e0340b4040c000070040001680c0881031503400c81880280107070420328041c0000340c182805581024000e03d8161842611251591302d140d20a80085214868222411b0020f03001c500680394000114640c4c8035180386020006040d64590b040f0080c100c0f104a00001e034041c00201680c00000c02000401112000354100740e0784401103100300c60702820010003503018035400040c800e070848031641c1d06c0b0b0b1011460160b034031049802c1408040c0c108203614000410a01c501002c8101c000c031104068490f8610501c0007500300c680d10281c060044c60248402c10121101102990440360507041c110101e02c2c075403130080024404c00c403200540000c00f0a0217001e0503400280b000c0001d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 37302720 1250 37301470 37301477
    0x30c040c02060a05150102030703051303020405040302030c0609030a090b07021203031009110316050313051e0d0c03020d0309030315120b07030902030304030f0219150e010c0c03120504030510020406 87
    0x60711241c0780001021700d0301c44c1007405039008020560000748a4001480032203021441e07241604e480341e00203800c1e1a025a01507005074408074900c8440c174000d12455800241100c011441d1103d600b001520855140c4a41c40c03840c540030a0b07003400d64845141d14840d0f104038200b42c0f41c0d2403801904100700014035000e40303402580751200b0100407058540850f0301488549500400c0a10040000c030f841d54801040803094840001c12400000c0b410411441110922024580360740d04520071149042d800850000070840c2c0000d03a00c000c00d07004a201d04091440c0e160100d40d12a441c10241c000c0e105003404440e440c1007001001600c611101f0002c044c403403140400081c02d44440c001181a1644010040d500d500100300400c00155040c141010703452002e00090841800c4041a00c52031000354440d03040020303410b081c1a080d0758808061032200c81d090a010850b82c1003516003e01220190000824400c1e500d00b110b408240604140e030007d42c4e006045844051000002401a4010703100d22400b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 37303970 1250 37302720 37302731
    0xc0d020f011406060702040e0f01060305010f050a050f01030305031513020901080c03010e011206110c0a0b01060f0c1104060315020406090f080606220c0903020a060908030a030506030c040c02060a 86
    0x10411054032243c01001d004060a0600701c403602080000d0034242d80345100c07445400c040501040c4203000f458011402100001040c4118000940640781b00401c0e14200724680303402c21008540400c41d0340d040d290107187c00303910780c2d07184072182e1f200c030b0340d41c90901d40c0c00200364403007440e007081640092500304420313039601026842d03603096141d01c1c0c002802103807a1030081d20018031910018064150125001e030001084884400420003544e038011411b09602c0c0c1c00c4001e6640602c030305180c4e49070044c062031a1180b100c034414200140941c01c0c18500a21001140354030075001d80d6140c10020203140c12101d40d02c030100c442d281c014025072103881000007140e001c1d0800180c01c0d001440050484240c0170180c046607a4540411074019032004642129208124114964003c1c0d445190031414070b5890f4006590704600402000540742d6100000300302d80c40c28244800c510100c160382c0c40020508002c1030548078000043c1c00e240c1a02400c4c1d401038941001c20015a81c009445401411400c27410071a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 37305220 1250 37303970 37303991
    0x1060b090102030304061a04090311010b03030c151e010611011119050903121b0712081603020a02040f05190908040b070303020f0c03031e0405060613020c0d020f01 72
    0x849014405005002da00b0600001d004200141c202101c1304281c1200710304106a02070004048520292043d000120000c001a10403070092045c3c10070002f045000b9400d250402d24182d60314559007410024450304003000c00c07200c02c1602c1c00741002d420401400c05696031251001003100d1380c41a405565982408144601c5040150413910340203200320a04c070507400505002d1b503040e0f00c040719940d058422501b442020610310006091160f003040380582181c0c0c101c42e01c4616245403070300f00340564040502071b000002c1a50f070843d259a00078100031a021000c6007800d070b04121101c6000b942050a06c00c20065070101a80a18402d214101e03c5414040308024094100e40c40d0745001420908100001d104071b00e805400350524910a14000d0320300340034941c4008260f08141c40d24440c0c3c0c2e03c0031040c0882c5500c1054803003901c03032072403a040086280585410381e4031003005e800e1500800001220300d140c00a580c04861600403504110707040035007112402983c8041d0310103a281a546440c85415 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 37306470 1250 37305220 37305239
    0x6090b040b100501050904020c0309031b0103060801051e130503030703050f13020102060c0306040608030705030301050103540b070e03031c0c2304050f06030f130809120f0106 77
    0xc00f950030603035445051038500c8003800006d607c010041d40b582c2c0b2090025107107030742d000c0001250007410b00c03007145641400c250015090b2480b075000491030364140001c20814012900a940410001d0500d206140e140c42203080c140018403040038155000c004204610319425420650298031004e90040c07403540c40d03800b00ca04803020050000e005030030074000b082c01044004090b58000744010000981e9503039900380d1702d02c2c5a000c04400c07180c83c3c20110041115603010700c80c90b01680603890050340c000361717514499608402403120440110610007a071540304d4801c2c5101d0f100e48130f40941e00000c01052814625003000089503200001003c0300c622131000c0c1404000da6030354107a014622280d40700285419005040301f07408070400c000380300c259401c0d003507010841c18281042d40000c2694860620086c041603648400140b4000c00003041404510343d403e0141399807182d024400e9044100e018681a103d600c0303030210080c2e001d000f210410f4a461b40c0401c002050626a10082184a035201c0d002c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 37307720 1250 37306470 37306501
    0x2190e09010b070b07030c030b10020106030b09060c0403060e010207080d020d0b0102240402030a020a150806030102040f050613050402040b0408100c0c0b07090306020d0516030506060912010906090b040b 89
    0x1010f221320b02c1d010400c428001e400c02c400101c5e081c200891005585004100070805100c00d06005039195041001403002e8014116048580070028000c5403614540c103840700c5c4114070000b0805070799160032030307002d9200f94155642141d020001654840e244a0054040d40086400da6103035840c5c607118003402c1d8000100c80d01c0310340c42c0844014114114003090120300c540208285c1e014015030a05c1401a500c2d144c111000c2c001002d650300750b2101ca1080200f84500080416000741c4c4100300922100c043c1021040071240220384940c0d91310313640c5030914a485402d42c4201c5c1c1140c004500400c03d00c41c110094070555030854100c41400c00324200d0710040c0d0300e41412501c08200403c11002c08112038045d0700ea80110141000c3c42c0d440d959a4400d01203030701620608181d15507a00c01d0110819448023418002100ca250520003420450700040c1d25218400d0a144103084004000c0c0c0c0c044400c1d0440512107420601c2042a0140c03420b10110400040b5411030b1400b84240c0016003450002011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 37308970 1250 37307720 37307723
    0x303050a1a040b1f23030402090a0507050702030114150f060301060305040201110a031d180a020d1805060103020f0904030503040b0a060509190507020d0c02100302190e09010b07 78
    0x154003110010402c0c40001e1601158164016500f0042442c50702c20f52103075105881303815034861040d0382c454500422403080c0c1d60b5004a030300d807042091001603a5080805a00110103d20006031900c80d9801a01e0610400c00025015400c1102880c410856415175a210b070090048403801c0103120b0040000d0301e2150040964410800d00041c000180719a000d1640548103041c010142c1022015032450410720b10011400506000394141d0601010b030040c3c0790107030b800e642c540424980b400075920038020040200d10350980c046014000366005070032040c0300c1900328040c0103490003103041440e15407900340403da005441c103008010103801d200c2d03a5984036980640c2d45078215102d80d5600721a0035801746c006c0004c0c2c0d0700c6d02008240c0350364402015000e1501d26001c0d041c1d0f41c1d030707040d42082520030040007201590040c0d0a03440145800c0200700303d080340e0440340380103040c2080000340c00038060f06007484080031100100c002c601303070080754000b11601c08035058195681e981c2081055403103000380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 37310220 1250 37308970 37309001
    0x8010e07030609020325030c050d1203050403180e060a06020703020105040b07020406031202010b0103050c04050a03150204080106060c0507090519090507030b07020307020f0901050f12100213030303050a 89
    0x1000842c240d503001c9244148000d09503a0100c04094588060210701900c804528600500070420040602c4811008001c00e9a0080142c036003a1075a240c4110040061400d254441c00001c04141c4030340900f20f1030032901d2409007062600c644c1903c1200c0c0341156018010f445100d80403400c40c0c000a080c40859034140e6407246001e0500307062a681d50001d00302241c000d0740301c1c5004400150039070064001c1c10b01641c00018009200c00c0010241da001070301035107801208000510842d115007150500703881d04910f440c0e00e2184141348440080c030955003c6400e07540b0f03048011034280c0e84500784008460045044a110703580f1800c50108072402610702c1d68140768102c02d00072220030750740c22100c9658060000d5401c45580d136104d607042c41008690b1100142c00004518045283c1414400091201611710807015030400c00480c0041183d12401403081c075a03120081140c440030008003203002c8003901c055465002c860a9148861388500080300841c0c03c01c00041d0b800c0c42c1d58850603410410921 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 37311470 1250 37310220 37310233
    0x160215010f031203060f0b09090f0115270602070608010b04150e030f0703080d060905010b07020603130f050a021206060108040212030d1418071202010f03090b04140708010e 76
    0x3510f04070380f46000c0300c641d03040c10f4403040e0011352010100c041000130250700d2180c503650b0002100700220a40005d141c440d4028045006001081d4008940c0c0102a8142480c1c0c0724800d02c035503c070300d03e00c80d0801041000940c01e00d01050b019404550f0f001224025120540307540d072142032072643c0f80242e0040204009036140b00640c402e10a0101d400c40c2d242c05420355280d000b00d118841e0400c4001c0c1c00588000c00d00041000349030405101d03100040c000710400300000d50411013100380ca0700c50400301174420b207000700120704151401c10307298400d40d62100b59005503508524181c1e40701c0c10030039030580c403649049061104608001c02c5080c4107079016500c0340e030140c0c0d5580c2040500b4000c0c0030001700d41d100a0003002c0448405105000001103490400c4a1a242400400c00c246498040200b04c540004004002485100d560506503e9090074408040b058540c0210300810120401610640b20001808203200c1a42880c03140d06e48190b0603180219120200c25080c0c51055140880302d901a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 37312720 1250 37311470 37311473
    0x305070f080f040f02060c01051501030b010522050a0909030206250c05120c06010312030204050307030308090102090a061101050108070503030a08180a031205090c0a09020c0c0306160215010f03 85
    0x503007a0b29030103481400020700a11060b000300b8020b410028070110b5a0303544a051080b07014280c160050303800310918043c40240102c0c400240b6600842d00d81c2200b003000707045010030030984025224080c1001400c40d034601551405148050207034284254050f02810000c22202001c118000110b90340800000802d400241c4c1c04903080043c444054900c0d014901103028414000001010f5118a0a000300b01d20750450900080c1c0c1460b610501042c54030400c4204003d8034081500401c6942504202841d59526200140a48984260103500601c0c00c4000700c0c074142c0100702c90700c070b10202038001c014076a00c1c0c1568a03038a401e24001d8903456407051000001e22031060300c90341d600c0440c0310007107181800307500303401c916000500c7d200310080b072400011038405403882c0c8209584016010700801c4011080004510101d4550145803174090b0000ba034172040c200300304024190803801a00f01c40c80c0349007204080d29203800302c0c4042d0005005030340d1020310034400c419502c1e0507102c040c101501c2ea103245 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 37313970 1250 37312720 37312741
    0x40e01030b0702120a090612061413020d0609140f010303080a020903030403020330040506030103030c0201020a151a0312191103030103060204031101050a141e16030305070f08 77
    0x3050b00045104010f0b191207440312200141c20364450310344030760301c0140c11301002500041e15114004075451a2810411500000c004403c0940d0001d40700c4500c160142c2403140b01a201c0c8840d40304803d807e1240015580050ba0701c00b070180c0001c00d04a100c41d444900e40a803240230b081c03001a00080300240814452500c0740d00400380078100400700c0b45055500e5000c01d062520b1407803031004410b031602400c0d00211040c50482d0080140035240c80c54503040500040b030740d001c1804007408106080204004690080000d02c00281e0020788044070340400610304401b40c952540b03180904031590a1003103143c10001600e01080901074041401d101c0001c200145861070b0300c0090b0200b000c10404000785070010300c0194040c40c003035000540d40794250b0a00080d80c0c0b000c42c8207139041080400c00d8041c0785a0294443c00c8800c4840700035079a440c03402000284546000281054000d00060100100c9240c0700340030340051310a480a100596900000351480c60003502608041100d07134001400c404032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 37315220 1250 37313970 37313993
    0x2030d0302030a090b0a020c010509070f060e0105251b0f05040209040207020901230a030209070c030302220f0605070c0b0319050403030902030c061c05090a0210020703030311040e0103 81
    0x7400c0000454518170344a61300016419644884056800101d08980711020b004141d4405070441c02802c4e06403918207100a0200980b0606040051180c41c8001d284e100300304a4030105010134048041400c500c07040c1e16603540e04081190030410f40f0303400c8400d10142340d01b041e0840b00070074840d03100949000244400f9600641829a01030340c00c1107640c0050b503501486602134140301c1e4003400403452074445105009000e1006911442e09114104010381d104002c3c0c2d5031140b018586000c0070f032507030b04d0141c020340114034040040386050054141c00d002c0441000086840610344485880c0d69400251402d100f030050152200c031800606204402034180116000000218030400242194203000c00701ca1040e902100000c1d20780800c1415481c00300045030030960120740c92803809894030050341e10301507a81c00c00c008094860700024541c01045c040462120707009050740d034403440d42ca0b00c001d42780c0310180022070101c4e1400d00469212203805040d40c0c02c1d02e00e076040c010b00d540d08688070940c0c81070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 37316470 1250 37315220 37315231
    0x1614120703060e1509061504020903151e0109020406050301030201140d0f1a041103060409140f06010e18070501110102071b170118030305090703050f100f0902030d030203 75
    0x822920004005802c501c140341c1d604800a01501c2c030041c4071800300c181d000c3d0240c503009480c0d000a051088401d100403040c510001e04a07030050395102d15001190900051900b418092a10078041020041400001054109040c640d1400507070300c4140e01c0d0101d000b580684400607200344012320065000b01c0f04407600d04c1540061034181840c41d412903080d0340c41403600f03600b80ca4458403214074582c000214880710a42c01c44083c4603440b09400ba54845010003031000f07204640314104042400550902c82008881c03000c2503c1c031035040410400d6032201c085c400c82c1560510580042c01d0031b030805062140b50560900502517031071400004482c1c9002d02c5034003032030955003001218001540d80151081c01c1c1800f0005540052628082100d03036000e40604101a9041845401041d0101e094030000c0d04d505090005894503049031880c07a002ca1030304020028410340d80400d0407214001440c08110021140910000d80300b100c10600b030700e2117800001d4066224044048001d4042d4000c0d6900c10b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 37317720 1250 37316470 37316473
    0x40f08091302040f0510020c13050c0c0105010b030402010905010809030a030507050d020c0f1216021e0315012603030f1801140405011a06070f031701031103161412 72
    0x15410301440070403a4490341c4018100b03050b082080000307051242a20841204a0024244044011005c02d08a1146c0280c00d01010ba8420010300f403440342c00f00b5502541020b90003000743c1d6868200b420b4241e4825a010b0f8041070701000002280c0d8890306810344990450000b4509101e08017906070007508000d0102c405004080c40350403640e0340107201500144003124001c020005010071100c1c1040c0b00000e15400c19041000761500300007803424600f05055060310008030340100d142d041040e5070350310148968107000d100c10a0b4140d500d0003c1941c181e40850381242e549510801a04030070110381a05403046800c20310020780250740c024081c3d548500c05509403804003641c130b0141401c50b1420440c501d900d19101081c0f200b0320034244110804100a809089004060f0900080841c000d0308002040d00c0b0040f4295130400d0b1243d02d40e0308403c518030511400c0c558592524201c85562094110300178481c1042007121082d10340e00000031107642e82403005c50f480756001030083d084841a004c8045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 37318970 1250 37317720 37317739
    0x8030604091a040210050306100e040b061b010c0903150903090b0f070501050f04031b0807020a0f140906010509041503050a06050702070b0703080708070c1208190203040f0809 77
    0x118214502c445464920686194901c0c9801d2042007185000010031604001041c800c01c1410780b134000350701000e001036040409030760040c58001406091142c411507046180441c2c5102140038006400b605485007800a005401a011048803141c0711444050084c240403000a17440304240d50045101c0341c080d20705907220948400160301c0c1c0d40e001e542d204c08049000580d03002401070070704c50160003c0ca4040101020b0410703403801041d071041a81c104940484015540007005200c00c100c8400c039902500c1c80040d561340711300a945404e0309e445101928000d20300102400c2c5006000c940c81b9010586881d4100b455003018440141413203204100860b51501d80031000c41e40401c004007030b440c031995011810b03190084d002800d000160f0301520306804188100c10010303400130900d41d4002128503001c1b00a54800c0030880f00c5100d040d20141880b1000c00b818002d103980860003d205010907403414601c00c030111100c104038402210301030107001103010084006442c620042c86601002441da054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 37320220 1250 37318970 37318973
    0x1140915070609020405090d09060201050103080307051c09080a030e0102090d170702060f090a080d0507060c030b060c0a0309050f060304020d02010203071505100905090d030b031002040303120608070f030803060409 94
    0x3c948060740c44030001e60004502c5510701740d01c000400060f0080f4400de2005515680e02e0780700340d010140c0014180400450282900c003820202c26100b4000c1c0d030750903c850042e90808a500d613205c19581d07000642000007511141805000b1101e40200c06407080c50b4030400e5455241c9c02d2a10100c1040468108000000150f502d02c2c1c06490f84e0b00b01550700581c0c1d140e0a80400c6081c59080e40102111f40120b18449107058020095407203071500203601084c030320f6121400701e0003002c1e01800640e2140010503440100711001900e100710398465202c828090f501c8504004c1200001e2445951003041040010300609004a81d10411441801124102049a6550034003030741c01c1e0315504042d550321400c009403846461000401840e5100d000c001034140081c803c0e84441c0380f002c0310020705440d044000f0b1140c800f0450851900340145d001c54903a41c480c90000c080c4ca50040c1c40c084203d04080c008075654202250001c2194181514410410718503076880b0400e0300b0040021350b03ca651000f0400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 37321470 1250 37320220 37320229
    0x31e1e0f020f010f0e060601020106030b04300c0b06030c03070603110d1b020d0c020a03020d030e0307090b1f02070e0c0904060b040501020d020c0f0d052a0114091507060902 76
    0x101c0d0407600d420200d13000d000007004030f107803006c000d00f01411a818040c013040411010280d03d604203411405203101c200d803100c10f02d00035503045e1805039205030801c83c10003d015402414610381314407a14501c000345c0c4400042542d500058800b45038182c000c1802002281c1c000d901100c2c11a0403150038900344414403c400c41200d8003545083e55402420300040181a4140000b68400070300b414409244005500491000344403400f00901982c0c1d44405441031602030a40f240d40104000d085890007a140c0c0042c5014143c0c8074519405095030f0f000002c80d02035020b21800304106a40d005006030742c500002c20070241d8014160305c00e000c4041101c090302d83c859025210103000107200a03907445d4500400249481001c08101e0b0840d041041c800d41c980e41c500340c401c506614203c0d8202d1000080b03080050601003d40b0108000c1941a00c0e00510202c19200c40740a4000c01d0b00d4040700f0130806071308030b081072003040003c683c0120a10390003c5a24580006071291074000c040000e054510366002c01e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 37322720 1250 37321470 37321481
    0x20a151a090406060602120a05030a090206090904051608030f030403140f040311011205060307180b04020c0106030b0106090305060606161407090513080304020f0d0f031e1e0f020f01 80
    0x103031943c0392200000d0041c0d0390100328810703000c4602e0204904c0c088020500038014040070b0840c92601d52107501c6034055685842c26030b01c80d18001401d04146041626080381c2d5020381a00049000002c1100040c1802002c000e0701c11008a070044c403132030741c0e5650344c0480d4401786443c0b03520220601400040000b2000202800255111b00200054880e0030f00015000c040c060100202044c100400c014203500c0218445040300c0d14441c4016040614010b1720010740719400c0007581140c4003007943e84240c503054011000b2a4041c1c0d0000d110750740c0319402252440341900025000707a1006010410b1400c1c884010400740c5a19400340340b440c0c5183c0c2d00e0704d6120080302000c40c0fa43d40015000d0145900a02ca810b42051a01c0c2c440c0c130850101d41e13501002408024000780c0f1900c0c04440d19010750300d44105100341c6507400310205050200e40e24014011014204846034803109500da00a8000d0098440703040f101001c091420000b10281c0c0c0071280914640c80d0a0214043c0d0451420b4100003402b81 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 37323970 1250 37322720 37322723
    0x10303050a03061211040f0b04090b060a05010302090102060f0709050a0602031201060908100207020402090301050115120b1e190602011d01050408071b030b07030207060507020a151a0904 82
    0x5203541c84001003402020340d44103400840348440112601d0002940c002c6003101c01000603640416503800e180c80b0704006100311700c2d8854100303080521030410881e0b405083d41c82420110344a42100d038645004400303c5c0640c07400310b030142c4d1081000c1150b40160b212042c2e44001246814282d20703031250042000b0343c00d04da02c241c02603400441c000007900704800d5250b002d00318a00e88003d4440c030b003103074203552400b415401e84546503001034420300359103e0750101c413800c00002e8024061942d50704611045500090b004400003111039800701c013100518000c140310080014201c400c5d881c1001d0001610b6041f428401c1e43c89950004561001d58644410324000d240715000001c2115440c0340703004031800c640a032400b8a034900301c02c1000064903401a9000d880d0894403003d03006c1130798980e00308000740c6500054a003070440300421000035815001885c1c0c2900c5000c09000646424005a0ba00c608120700200f103030021a2001000200913409207500c1d000314443e50f800c1a800b0004140c400b41305440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 37325220 1250 37323970 37323977
    0x40215031008011401080c151803160608011514120c0d0e01060614040305031b0a0b04050a110d0302061501030b18061005030f0403031107082a01020f0f21010303 71
    0x4005107401401f241182d4130090f01c08000302107e61030f00040038456082c40c4a8440c0800400348120345040154210b01030303004048982668441e603010305201c0d801d115510750101d11013068501d842c410784280d40105c0d0381e500f1042c10000000d080920b100d40c001c100503d0704030180803c0c20000c24a01513180090903c400004001c2d0908000902041c081012038041840401041000400c000111158940c0c801d031040000a440c03078400b070400780c2d00e1002030715400440007804140000401c225500c03520440050b01b1038913400041c030040c0c000149010303000d03801903000280221480d802c0203440080514001882e40c40074070001e00c2040d41a58154041002d080c10409941807014888849008034107005045240c1001c070303d00e422100500041c100354540c1d80700703404d20a070242550300d143c2d0310816158072020404000c1114000740b80c40300ca10740b5000c00d0080c00c041e5041c405c031070180749403d0303c0b80c1c6814003041d41c0340c010b64001d0300120b614035250113069118000c520789e1140038510030340e03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 37326470 1250 37325220 37325261
    0x2091807020c15030a09020102070e01140a06090501050a0f090b1303050c010c0203060106050c030f0f07120305100306090503160503030f01050a0e0106080a0f0203130302060c0304021503100801 85
    0x903802407030414010700742c03401180c40103032000f005080c2c0340c19a9400188401d011449810030300c0101c3c00c6c440a40c0c4910004041e480000c520005c000700100844841600c488062aa607031500315441c5c0511f204640c00b042041142003140707440340314802242c9840341401011996100007025069002c0120045000c1d0b02d107009100304041441800c0d4110302c01d03c1d18002d00c030b40c280c0000391181011321989051080c00034070000110418020f0780c20040768180302c1612140c4814601e8031651000e2070445003010000703840d40d452800392142c907020b01c0c1040290b031190744c00c5558050042c80142019102444240314441000f484110300c001107600c0764000c2c580303030b04020080c4039178140d068100e28854841d1010511001c130301d00d02c0f01c40c11200c1740c0c9045003039070f29116100401400301740355110b00c80380004100725580f03414100846410707209500721160340c8e6807a1945034080c003050300d0003580032142c07024a0400e11062006540c020001c500112a82965a800f4a00712500e0745200043d920092 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 37327720 1250 37326470 37326481
    0x90b0d0222150b09100c05070e060108240f0402070204020a020a03091205030306012105040b0105030709050f0408070c120606050a05061c0f060e090120180112020918 73
    0x14090b0440741060560504040d904080b4061040d000d02042031340114103100380700301c0d0a0300c40c820742885030740c026042d6043d0300e883c1c0f100305919000c1120700f1404980d2600200b500e8682112217200c2c02035002400810303941c510300401034a4410715660f154007980a0002001507070b80c0e03100400c0c500d0b0303241c0c0082003200e900d071401920240030740c2c2c0101051600107039480040340d40402242d911040911304401d0b0000d04400b140202054022003010031840c1c001040300300600c00134054140da1048043300c20840d40d98024009480044642205d603101d24000f0500084d032140182900031f11418412030b840361291401c0b680c264940c003090b1902511180b04000301e05106000c0c0300a01001c0d519285442d80307a9100404010b00c038442c80120320764503410049403030203a9001c01e02500491415000c0c2e4140511920701a1a001010b101c0c0181c0501900c1851074040045440c001055501054001c00c4c140054070208444000b1030120750f003c004260040ea40e000c0145a194019a461200e60905 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 37328970 1250 37327720 37327789
    0x501030b030a0b060405061201020c070501080a0c1b02180a020919061b05010b0a030f020406120f030807021006031b050103061a0c01060314030c0c0a050109090b0d02 73
    0x800351028082c0e00185280000304403010500340e800707001910049000e450310350101d13244107000c50411020307520214440c136046001103a0081211000d03070300c9014070744a840080c8119511140b40038003188001c040500ba5010801c06640018001018520107410380e4458521132801120620349450340021800050701d000301303140c441501702c0803a03c21510f04143c0050030760588081c400f0328004d041180300080000c25046050b001c1405000b4210865903031811806c00d07400d40384220b1059003014804201c0c07056140801d08090303000500c2880c2c4009540741600e0000026051400b140038144d5000380304111401001d00a520901c4202d03400030b030311224106c0227145908850f0403d81000e000300b08841c0c920b0324840705491200d020039039420a82d280d26004000030f52008008007101d1030010039615000c0094001400e01c041990010300e0782e40c2c00c20280c000180142800706010440522207000f40d907000d8101520003520041980002ea0000ba00714030b402918941c803407030751503c0200403181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 37330220 1250 37328970 37328981
    0x60712020601080d050316080402030c040f02070303060914071809050403050702032401090b0604031a06090a0e0a03080403020f060c0a02010b0319080a050f0c01020405040b1c02100203090316050103 87
    0xe03070715105d03045042098195041d9408040b05008105602d00401d00355a01488600d00810340100108680d008440d0307e036020b9000110241c02107440c141c000a00b100c124041c01d03460030711842e6105141d07540c2d00000c1d642c0780307001c8650158190aa44002c03403204001e200d807901139030003500c4494850965204040c513040340d542143c62101d42c001c494a507810003080c892410b445908401269052078030020504c0c170702171940050416010144400c440d415203005440c0505030a0301c2d00c2d903d030703a1101c076500103440000d00a65a164071003098400400d00c2404401d400c0340c41b0f4410786204001103c40c19103004000d5401c0c85200302c0000314502070703940900c2440180d041c00d9000e04000d110104080118442c1503601a1220b000000c0780040540301d4021560500405906551100c5002501c80d00035000b501a07030703000e1032801c1600c0074585011103c030f0116030150b05d50702c107000c0c0c03040c2d0a0046a01050fa4440c05500c0140f042c054141d5061286040e0350140b0000d04000360701d000001030540710f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 37331470 1250 37330220 37330243
    0x3020d1107020a0501050c03070b0a0b030115060e0d02041b030b040509010e0c09040c08070906050f0a05060d0c120207050f161203180518040c1a0405010c0206071202060108 76
    0x14200840401030303d4902c542403c403802400c0c4aa00d41c0402520030341180f1070100c0c0102401c0c164070030000c08044aa10440141000790020459080f4840c01908084210b01641000c41c40800c2c0c003543d18030b400f41e10056510f00c040e10201d9000310781403505801d6600e070104000800d488409044e000e013031a01c01d0607842402c0c1d4000740321481d10920307481d1300d4400443d1624044d4080a0000d0140300980420000801c1180d0440345015640da42d40c1c2d0082009004941c03203034941524106262030520302040031303103100070005441c003642024102e0003012548254030034010300b0300c0600c9120300c040c401f500e00240200050f107841000c4252090134020782180b0740300d0403d03039100184201903144101300a01c1d68076061001d40001502e803141500d801c654030295000c40c1c0b5109803a06504039041503070185200d401e084600e107840b101c00050729150003211040b200c000b40010040c561095208200081c0081c2144c0d20744070a40e1900030855600755400c134050790281004002201c42040846c1c1481d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 37332720 1250 37331470 37331501
    0x303030c030e030315130914030c1b0a0504020703020109020a120b011d070c03090f060f020c01030b060913060e01030602070b010801020a020c04050711070305010518070e0109091b0603020d 83
    0x18a40a51050110000c1c90f501c00d0060302041c034206d441d00c1003584000b0706150003e401001014034a0025031303407548070003403402d524080c0022403e034a0585030803515100c00010800d216890030001404029041410181c2c1199243c0d000c01e005a1a6071002c0005000d040d84d004403603850340e04000001d000c5c1079210040c01410480c0d85012401100000c5401c0b002502c0c16140c0f00d4002d007002c65100724079130002d0089100b11280014015040100d4000d00c01054081c2d451000301000103508a90301c0245580d0070080030410f180142c500540e07840e40d40d0724200340008180c5e489000841640170241c00481c0c010b940081c14000b0300411904080c01055004020761418401c890004e4275402c01c07107116801951500049085180118180c00300170b6035980458004980d241041d40c042c240c250307500302c0441c0c003617460340343e16400126040c0c0c103440024050000c00c0c0d107820242030041c904aa0142c4042d012044540b168034030410000c001450781c0d58000d601c03854000589411500315a40c8041c1d032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 37333970 1250 37332720 37332727
    0x60515040c0c11010c0f17030a0501050405070210050c0408012f03040c091e020a030605010f021203042012070e011205100c03020903070e090c0402030702030f030604020409060303030c030e03 84
    0x42c0e501802480c42c0f407080c40c00072451030346454171480000351501d00801c0d4003003e10b8200300c840040c00185103c2c2c40b101c102400b01d642d88500f0b220071140261203020050f001442c040384210be868000c617410038001d40402e0301e4295107100c09401c58000e04d440c00b607039003005100c02509150034050a10340d1a1040580ca1550805036920403210700c461007490060394440071214a000088559100d40400b454001c1d0b6680c8030202e001001072015006040c0031800c0105d852106600c00611040d000500d00300785881c5449a80700d1031080c0d000100c50b5800340500e00e001032000c0c0c48408504000d510504010075170113080184001407507205030094220341444116400c04250f00182c0c00c0b404000800000403660030181301100a4429040039503054465040700082c44003c0b05e42c524400d0345000103445a012026082105903c010b071500e03001640f061002455866000340210340003100204014541943d0360312160035107030240e000b503010942e980c50080e80940c25000d10042042ca07500030b10300c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 37335220 1250 37333970 37333973
    0x1a03100e060108070f050909010603020304051203011d04110a06021507020102030610110106210302011d03031605120109020415020a020306240301060806010512070501080f13060515040c0c 83
    0x400750010308150401885241c44441c06003d071080f07d03510706016006051540c0c40314000340103548190b400329414414452109020512181038034182ca4000742d00000000ca04441d14110a5002d042981d200814240c034032219a640c90b40c440003010320f40c0141c805905998010080c0b500018815020b43e4010010456199a0303c3c003035003142c43c6507003000b480d000000034285006040700d4000080c64000c080151280e10304810380d012486101c1da009001c084500546413008407070b21003119000d07030300a101140402c50a441e4240e00c5200b245401c9080c0165095607003c07180e02030b40403c60a0f540003a00340816043d000c3d4015004446000800c107038002603010a0740c07440001c01c88c14048041c504420300052000d1120401182c0080081c0550350310707060741c2511084288a102d02c61a0952040070014a022501204031501619119040d50315960300350b002c0c0070700418090140c1701d2101034000049103480760b540a916403000c4034000000e0300007848101c811500200e008e1010a030320000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 37336470 1250 37335220 37335227
    0xf03150a061409040f020904061e0503031206041107080304060207030e03060f071b1709030d090807060c0f02120a0210050c0c04020c03040e040602030411060c0309090c041a03100e0601 81
    0x20043e030000c1e1070002c2c10500c0445031a00a0080e80070f003603805400d002d40021264840c520721039810712441c1030900c18960305c10805a4900c207612400015050343c20000d069490503900c02c502040c0303a8400189000020350742c0070050350045600b1903e4503030200c2d200e0103066022103d00089242030300200500e040442422000c420014016010800c583d18012600700840d00c102c110550701030041c0b451899140c032403035002d4100752021070091080c0031020803c5031241e491041100d1192001d03020041c104101108c0e0180510420703038202d44d2150a940050300d038001d40f604030a950b6000352030315900910421010b0712009110780c041190502800250281c08038000c0d045070b00840d270059071110003d581038150300071684005072441527001003105001103900210702c039500c00c1d0740e003440c00b40c00501048042d0150005160b200d03807051201070f1007810007224498102031140740842c14165282a43d65003094880000000c1e0003010003888141c10b05800320320040c0004480041441c0343c1040000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 37337720 1250 37336470 37336477
    0x30201020c040c0e0a09020d0509030901090303050c0c061204150c021905070e09030408010506040218240406030204260a031b05030307030605010f02010509061306020f03150a0614 79
    0x8a2003980ea94608031041c50098070b1620b0081e801402c1a202555940b1030340002350001200b5081ca40d00b000e00144155501000310b680140050f1251504d41f4195201201e843e00101420034140c82003022080186e81e841010b09112010001c20319568945854612a81c1e181c41d0700301c4404c2c50800c0f4514211075004034040381403208150210785140d41a0526034989489503100c2c0c02c80d01d00c58002d210312582c0210003442510311f0322009200f26142d80060008034030811001400d6003002c0d92440301d00380b80034465040000a6006216402940042c06041503403007544018080707540080c0400010b00912455a40944403400c003901070a41503035865228a01c0305801410885404c9043c0044d0b01e400054000b02c45d00a4200c0780c803442c04040180c020f08181c000c003400b01310f4100d01c1004980c8140a5580320f1200240500b0240d129075044100000e48a4001c658082c0c0a0121003030b040d0100703019502ca800410546680140d01c507040c8007480010360000410801c0c44050140c00803510006c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 37338970 1250 37337720 37337743
    0x409150303020c0d241b030b090f0415020306031c11010b010302040311090417070303060e0c0703140d0612120e0603010b03010509070905030a0308010906060908060612070e070c060f0603020102 85
    0x1000d07400c0b0041c2c203904001c0946403003d900042400c9400050320340d1650144403249819500d0742c027541c40d035207a0030301c10358400c0b200200000d0a102040c1003c10303448e0003a40e00008042c0403990040c03071646194840d0066860804c000032a03621070700031b0b103040034042c0c401fa1038001e00b8214034003411a15110030032860700501030302400399100810304001c06c103011a1034100c48049400d45070b41443c9001405803140384502c0c00003040000100c0c58080049084820b09581500d8401902c0c02000980001d904a115180200d43d550400062501c1d0a0320410100138420074180945408164010300303600c1010794842d000304001d00c0148a1030306c10360210382c1516000c40e2007541c2a0303603108003290701042e030b45c0115416000300341000c400c00d031304407008605840307070a1414130143c1e4a4403400c83e055206881003070042d03800000810420300340602c170801c82c200b03070b54113030f94100352100796041d00c40b40152220000148040118001d10000384100e51603415241c0092165903c0e58000035a2142414803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 37340220 1250 37338970 37339013
    0x70305070803060d020d120f050f07110f0d0515090a0b0109090809120c040f0b01090b160516090f0510050f0a09060617060d0206030705030c0409150303020c0d 70
    0x41601595000303040d0340c1c04e9038002d00e80702c220000d40c50142e50007102010202e000c02d809240d40e4040078060b1013038500f05480038125500702406601c03400441a07840500c0b941045495000111170344409104900003070180c002410a1120744001c0c00c00008010503d90160f08036440c0742000a0b0b104800741d0450754405404502c802580c1010760143c0f1a03070030416800340640c0d414804202d40070403c038074074960450b4100a0307040f0940c1c0764010b0304e151070304150004040b11014030030002075901400100c054210400300b03103101e035685c1520345144141201c21840000c01c08003c100d016014951107150f812000f402142031045c0d02c030001802500440c1c0c850006003019400a0b141c911b80c1c00010b260324282407000c181d0320080a054010285a500c5504900070001229410040c1801107070301e6014100f103145030713603410b4101c546810207026400364010800c0b0008802141c0d01441e014940d0a5040280382455464086e203010585007806004142c4030112002050b0100001d0070082c2c3c0104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 37341470 1250 37340220 37340227
    0x6040b070f0905030d0903020f0111030307030c18080109020909151519060302031e1501140c010e030a11010b030604060e0c03060109140108070b0a0c030309021201050a110703050708 80
    0x8006840708152070f0001c640610600680c90340711540038003d24210790084c2d8041d400300700082d0044508030743c81c01110100794000c00c003107034031148207500c10780c900c1c102494080c000c5544c000340801c01c17550907800004140c0d1a0b400c91010752812030030140c0c000782400c0080480142c620b0a00d64108001400380c1100c420b0b00068003042e48402001d0040803c10203141a620758407144082c3c0203403c141d8080d0540e01542d0b40c0c00c40d41d2041000045d0107240c42c20381140009807501c2c011034401c8660b000500040d40184920181c1e403400f40219800140d034000610b48603402d44000801c80800103500038142da06100d2003204903100469a95001600304502058200d0700084041c0340080c208440754251141000000c2e04008507440046ca9442c907030b411500c1c0766650a150f56a07090b15001d5039410000402c03514110340d000c0c01c0c0301400309210307080104d451401c580001c4c03100c101400c641012651079008108984a00d0310400307010320781c0b11208078101801d580b40200b15004c1c981c0014100303180007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 37342720 1250 37341470 37341497
    0x30d020d141207030614060a02060a0b04110408060103050606010c0308070c03021c02071a0309061504110d0209010906081506030a0608010c050d1a01080c0d0905030c1b0306040b07 79
    0x10400c440c0066040c0300c02c0300d100d0070b20b0140100204140d02c00c0002120b0842c07150907a5241c88030407126000f0180d401400c403a00c0d11006980204103051406600565941c5403107a100302c0080640010038104002e42071542c9141030590400303030000c2440d810001032080741800207030004200741d0003175180c0ca802681c000702032030309070300c3c04c40c07440284048170844049110415900240f0b18041c0e40c003420820f89030008541c072008903400b040d1891349564008500051b80660075001496002c5401440419221100200c0108541c45000c07802c5d00d0b590002154451941c0000500c0e000b840c95240c004210302e0f02001e0031940240f11070213244070720780c0080400c41c1100c09402a402078401e001c0200900b4100440c041c1c259840761038078280040c09c089036100301c501980022422108181c403040d12541e1111504000d560020803000c040d181c1e11007001c00851720802c081c0015040316001000f10020502440218a10034404141300f80c0c021000c000010321488204d5421a070140dc040100d42840b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 37343970 1250 37342720 37342757
    0x8010506070b1f12050c04090503030118090b0a0501060305090c060d0e030c15040507060e0a1205210405030f0c060706020304020a120506011403010216120c0209010b030103050c030d020d 82
    0x281d80f03e032800080c07401c2c0042100d20001030b0300140c00784980c1c100e44ca41042c560900c404e4403400c2101030800e40003440100103010307034001c81543c2801602000650202590f4a125551500780c41020080b5078480041c000580c0500c51150006007240050005a03c2c0c480003d002d482050100b00300e4944400c548020b5101c10019190313041c1e2408141c401851440702900d5800a0403501903649d031107280000182c241c00b42c00012030080b00035102104280c100403d418101d946603c04031001c3c8161820800640d0000341100100000c0010075951203181104162508181280d90902e941101155003000d03658601162140342c0c3c40000541c030b944d294000180d5900c40c60f8000111040b50511031401c010010544d241a6402c0401c402c4010460070245400c074040d00d00c210009000040001c004240e100400d200c4004a900d0141903190844c1c5c04a46040400ea1101c0d1001c50080014005c0003424401014000029001402c406100d11002035507482d82500e48028008080c0350903900701c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 37345220 1250 37343970 37344001
    0x3030702033016060b0a0f0b070311031216050a2c060c060717190f0e030d0e0c010e0a15120c0e030c03070b040b1606090f050c0108010506070b 63
    0x8101103020380300c03400e121039985010f81081044503a240b920400101c00d2804071440010741d240352200810a506108485009030711a50082d42808610540c84181020400007000c1003022211803800b1820841c1040c803003800321131303900f80a10a050144000b2998404850342501044400031210340c003104a200c03038154107502d00d041e04a00c0020f00007001440010b00580200659070300c403074103400c0c208040094520300ba40d0100d003101c0e40201146400901d50032075289696a810009a4207916088481c078641c808841014ad00d61034100d8941001014440c4051041c000e0038184808841c10340011410459402003891a42e00740240c11040c80c0b04109542c13540701d030f00d102046940c0d0000c1e4041c1c0684020f07400c05210b80718400601c8014140800c1c00c4040780c110071240c1e410107040928020142c0c100c07138448004102a110210701065413405401d403a2405107904a54501c9241451070911640300145030612070140010041038075070108070381007181c011020344010340300c2d404011280b42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 37346470 1250 37345220 37345303
    0x2280f05030403030810050604050103090c0e070f11030a0504051306080102120603060a090305090d03140301171005070c0803040302010b0d080a02011d0601140a0e07030209010e0303070203 83
    0x110804000010000c001000740107890203070300d85000079035401c2d11000b110400741c0145600044248001c100550103a00401d02c854461400041001c1d210341800032a158100c401000180125009072003880c0c003c92500540b00c0e10801a5203400041c0e0f402810034403c0d032040900030001004a0818120564044009802c1c000001c2d5075548096101208050068800b10310034041c8002040103652030b480b814046540c503840d070340e003407107011010040040d1b890710080d0140442100564102d144860056019258141c440920b0f41c051610f494500000c09c20a9900246420b00b0301c20580d411444400000f580700820329541d40d1141307803c0b409000c17411b039450740018020200300c0030415054040c08010125600800c1554030741200d80d10b900b006540896210740003800140305507901e00040700395200d005400c8440c00c569441c00d640984100b250441d0002e58041410515581d204c0c1010180b08022401113040890303540000781c9407606100c1c1d040ca007a40c3d500c000e02c0400d0200d4200038920 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 37347720 1250 37346470 37346483
    0x3070e0402060f0c0a06060603020a0207060503090a050601030b09010507230703110303070e01020c03010b0f0d0302010209100c1703070f200106090609060b0708040b0306060d09060903110d0228 85
    0x10103001c454680d90305c49498003150000e0a1181c0803d01603ca842522030113580f550080009c5071506406444950024203c0030701c1e40940c1c1ca080c0c012840410505000710321036040c4001c03915200c01d0007401c50f40080c00d00703420004c165030281c1890880c518462a55100f03400081c0e940c40c103070302d016144205a4440c0700c509000210802500542004440b4216102030302a00d598440c031408042c00c0701c05405a10b0740c00546c411100d01c003420145040b00c8218882e000044c90080c03800e0000791071a00c0d0440b01d01c00140b40c84409010002141c5810711059109032078241181041000500750b40035000b41c40b02044111541d01c454100720118410041000308020820282c4640582010302814001d10300c005003420f0300010140000412200041d40106400e070400d0304025403a017042c1d1014105551000080c028128082458030841051920400001070202c420345409001a00404612030041e00000c4034443c409402007180010258010b02802480310801c0b02040c082c40d0180340503218 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 37348970 1250 37347720 37347727
    0x90e0705030412030c05040306090215070819020a0201050a03050a1508101503080a1101020403020405130201120c05091203040305010501260102090d0f06020d05040804210203070e0402060f 83
    0x554200c0e00641c001c1d409105030b8040c030b495548007542038403104240c85000641c204020030210310542e0103885082d00c01014030840420821440d0400d4200a50945410740c00003030b444004503100a52441c2000c0c540007034000003440f6000a0602c0c0550071045e07080c1a16000050060b40380c9130700103100300500c01c0c00c0d892215104c100c190341d00c198540183c0b4206140008180195080b01c070310604595225110320b03d000b9030a00100c6400f100010000d609640034880400141d40c7d502910b48583c40c10340d5a941d5a2180c0e0000401c121a600748443d030843c600694461000e60120445180c0b40059400746590400011f400345903106a52000e425940303000000f04006179a081103404510340e0a000030805544124414200c0c0700382009154440e13281441c50000a240028158000d03004000c010b00b05106000c0d00d40a80b03000f110101d03903201c0e00080c1408900d10842404101e800d0040d02c5072080800740d4003280da07a000301d0007a03400701021000007801315610101218841803001040588 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 37350220 1250 37348970 37348981
    0x1090203010c050306011106010e010302060a02070909050a020108060d0f0b060312070807020f061204110d080a030501050102070f0812070602070c03060b0906090702100e03040f0f05090a020325090e 87
    0x25030025585d4a001607100c181c0c0c001c41d40d6002400c1810317569051445900c59103107500704105035100320700404c01d60045071000248550188508200113010345e018025030400e0380700040400c80000c000a120b010078403400390106960701c0000f44403d500c00341030001521000c4c0000d02d0404046204044008005000020800204040d00c5420300c00d423000c03469640c254007000414003132010802a154000c42c0001d0100d080d0040e0003410200c064101c1c0c0c182d04142e2642c50082d40240501000319858200402071541d042110000514898030030f040001c5c10301d004291100202c4c0d0100bd11041c000c074074001400302550488035603951161a0041d02d50f900e2518501405100c0f080a1042c1c0e070b2100040d5040c01d0040015108030b48560107448110700c106804801032204904080701d5200038080410f80799000e003124400760007018003c41c142c5140c0010006c0300301004110701fa0385170051061012401030125181c1d036555003a0681d01310716079401d508440c030900684c07040441895502c00d110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 37351470 1250 37350220 37350227
    0x9030e030a2301060e0708040c03080f0a080901050c07030302031b13090c0807050909040f060c1206050a052202090402030411091320180108070f080c1005030901090203010c 76
    0x501401e20751010410603441040c500d00303d821612a040c40320055070000385400c2c0c894021241c8c0184514151a10642c0340e40340c1c01c0160700004c07a880e8040c100003c0c987c00c6c040c1c003c28000d07440100c1c070340203110a2418800080d5036004a003402000e15402201144000300c1201203082c0980804030450384410307000a540e011906140724808601d843d04440c001c1c0a841031411074814102d81c1c0f078203850800c00b402404603c890040c4181c0d00740d00e48a40b16400200035008042c40000d840c0e4949030021200e061141c116082036002503c213900406040103640c4600080b1400c0010a030040744011612a046801911891240d030b1703031280c8000100b00801c08a0150b020305654103032907070b074615a600900c2c41c00300522180003030041d2519224081d144c4810b41c00d650580180a0705803688400044e00010800710281c005420f0303900508014002c02071100800e10051803104000c000c18a031400100354a20080e800d1002048400000281d00340d0342500250303c829409002044242108803000303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 37352720 1250 37351470 37351493
    0x10c030c0906020601060e0603070e1f030b03070305070905072006070306060e090c0f090418020f060315040b150c0703031206050901051e0307120b0c040b07020409030e030a 76
    0x1c541d11110102e0b9151001407241c0c1a10302645819920b004041c04020913600000c285104001f0082811902511400c50380c556a07104e00c3e900c055001021a40030f8156081da8080c00e004c0e6102007020400705800007480c00403500041c80008268994410403110304410071a05003400400844c03070781c0c210300700281c00703481600590303810040a038640800301d400340044c281d0342d82c0c000c0564010499003100500104090800340100ea4039121109000c2000c0da24003001019803840e0482c0c40c03400390300307115440020444044805928600c0c24404d440c1d0305a049100080c012544d46034030803070307a84550360307180341d007019609089442e103800d02c0f1401d944182c280401c400048020348103452030703820f500580080c0d501c000c0001d030541e800c0800380142d5070301440507003200d00030b0b24098200030b88040c410040075041c414180c004d401500d0928032080c0c40d010b0194441c240081004004a005070f400f40d83c0c503207504860105500101d030070100c1d203994001e40c90661600440a0f000c04000221805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 37353970 1250 37352720 37352741
    0x302030310050f1806040204120803010f06030507051905040f0b0a020f01020a0c0201230a0c0303180c030b0910060801020405011b020a1205030c06040f0b0a050709060c03050c010c03 80
    0x103500100307480e00144181c1c01c2d0040a90f54118401c0540d2514901c10b000600794031100c042d0005081503602c852440e8540742c03480045d40c14440000040c0700e2480e51181c0b01d4054502070800f4043c80c2003000380106144108002c81c10b0204d40407027814640ea10400484004286500140c01020388403c16801c040d4410804000507104803040c0c81001d40f018029101d4030409500c13848a6099141c0040d210420400101074655184c1d0f51246548a1803102503c55080640d03079540070041b507854054100c464100e041b42524035034621100000c0d022009500540c1d60101a500c440c0d01d40640c1e140c5403219490f40032400a040841c0880c040c5015405403040b28402d981c0c400600f1511040c000706241151406500080384640c18042280040207501500b40305174104c03840c260000e00098140341c016502200d04041d003480e400144880c254015411052400040200d8240100d01038011045480785000780301c82a9840320515005000351005c0001080c004d005103100c41e08014000c04004d50b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 37355220 1250 37353970 37353991
    0x5030901050603060421030609020a02010203040b010e1501120b090108010b10180b0f070803150103141009050a0902090c0d0c020303071211041203030e01060518040b0402030a050a03020303 83
    0x42c0140c94000f490b20701980c0c200b84104240381641c0080c0440540e07501941c018140c444400282442c5188000c02c4c050750305070300058aa0810f8078000120b1031060707101c151407840308000c0c00504142d00304031046150007424051241341036aa080005011003021581e40611601c0000810420641050012001c2103034021341e001710345c1c642543c20b01a202d0f0355503283c2d9a078a00034803826903903500034000c82585c00f01203410300c41955908a040d0303004407040b402100c1d440c0070107901c3d96003600901010700b00d05403222415280c280402e0702d401e00303e8800d281c0d1050310344000c81d01e0030900e94482400c041d00a00b240285141c0f6180c5490075500021603c1e00642ca0b19507406141407004c41524000c1000b0703518603016030f20082074007028114007443c006652000704030000f21440f000b403800046c01c0c4a41c0b0041092540c06482500712100c0394402c5e40a903034501c5840c5414002807401d10380c425809660911030b6212030000ca841c008480100038030034803030341900605040d000406076202c2c0c41c2211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 37356470 1250 37355220 37355231
    0x61e0c01050a05060d050304120503041502010c030609020403030c030804030e100518060406020601030f02040f050703090c0e060120030909070503150301060302061603030e1c0809010510051302091005030901 91
    0x13800c2c0f102d440c208078005041ca030810311051000c14182100c126001d40201c08490519440e10100c2000100e048450800350b03548909001c207140d007500902c0028004420b0460400b840d52f2006048bc8031441001410449894001020540980c44503924841e0241c006110660483c2c0090020360210b01c0341d40001e44c0c031074400d0b00d062030510200c40c265196a8050700c1c4c0369185585080b80c00c8260709040340d1040e142d40000b80041118814980300d001c0035038000c90b076644107041c105241c846030340202880e0b6041d0810010966003111f0406e03c0c1603080b4003881d010101d2840290300798050b01c0034050380005c00c0340520030001c1d44500a10300032120740c148040070542e10070805007211080d00c0000d400900070300408903840311024040c42464043c1c107003c108149503414840c107044001c0c24506640c0030612407000140c2d442411960320030400d800810150400038524400401c1521440e40300b40365502c00b0000741802c0c0d80540712001009001d078505100038030b0014001e50001c4406403010340c03070003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 37357720 1250 37356470 37356481
    0x80703060b0603010305190f05370b01051009030512070b160906050903150f190e070512150a0b040e01140a0b01090b03040c03030801060206010f05061e0c01050a05 72
    0xb5040303c1c100c90703101c0b000301141c20107804071b071890304d43d603030300540c2c180900700b41203400300d4410301c01445003420780305d42202c85421101d0200b52403004030100d030b0100011428000c00160306426a07a06403a0b0450312012004041c003822180c000c5e00c1c2d0402456401200071010319209448080c00000e4032664020280756107140750716000c002c46200c03060024001000c2003008600900041c1140903010742516084440b80000c4903d07103d09550041d0940307071003000c2084170f05040001408071809000c043c01a041d044070070564407a40c5018091003502d40741903031642100100004510054640d03402d482a1801d860404010320040c143c90b0300860804d444d4014050041c49000840116458010401e48400b8201c400a20b80e8403400342c14001a20004100b40c6803080c09540310724461056481681e040d894000e01c15031040c0e02c4082076500001c0140613900d81404040c00344c80040d98100d454410a0740640c03e0300d42e00c6080040030780d80028508071030074010b400061041510b01024410303510340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 37358970 1250 37357720 37357729
    0x8090a03020304030206090a0504020a0908010507020d0c021003091a0103050c060f070605090115090f060509070c030507030e06030403030b03010b10140705070503011104030303060608071706030f0106080703060b 93
    0x11a40080040e0010001400145002c0c805403180726805040f0181c2c4a8540000c90100d9012188103c0450000031080149031002d0141e1503000d002da1000d020001b0b40c0786409400002c503400300911980c0445400c090041c4a42c0c0b01c3e03000c29030018001400000350302640340000c4000e00003624680103802d400342c1c1900707211048401c80540c8014451034005c442e1a260000c00016041c3e4440703540b0381043c202298080004000546100440000c041c010030b40c0e60340803180b090784054051b2000c0d00400000e580c2192500f1071254150078015624031492070b04a900c2680b0090140e4020701c08014001816032550201640c4107040e0020844213a48000b00800c03007010181d0100002d0504c0f0304078103015000d0020340683d62144003241c0310152510b0010703003512034107861003c04000110b000c0082c581c0c14000c40c00140310038100849a8201901c0040c01000030144401c40c0c07005a80c045481610100070301d001100c1c03824001c0000ca41c58000c80c03030300d41c64648400c0d280581081520402407a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 37360220 1250 37358970 37358983
    0xc0601031406010608040b0105010305100f0f050901090b010c1e05010912020f12030105130f0203041115030108060606210103030302031e090c1009090509070509070305040f0209060a030204020706020a0809 90
    0x100120341f846203070f00e00f000440290078010310511502820303090009100c0f403800366400203442d100b64804803580c10003041c0074008405a10500744981000300201c00e99030480c49034000c964200c0b82080401807601d103070048200c400b840040466107406400c8042c0051000b0001e081c3c2c106900ba1031440300f01a4402d076540c02d80305400d42a00004100400c01c0f40b41c901414807900620000104100b17034141c60400403038008403000c6c0d40f9030301c40c40074000052401c90b100d88000000c0030545819035040c002590307a5480c00804e01c1e80500d0000072000c140d070281e980c103500c03076080c4041c0d07a003813543e107925000340030b5001512400740d6450740200201c0b010f80390010b628800e04840d4006d210b4101e1803010003407201c040051400610040c1d5001044140d03560052600c21540d100040004a190405100d08803400504a10030140b615003800001242d61210b0742c2040c1e012240089541c03078400c005040c8069950000b0340c000e2001490000308401d40e00035110404158807081025070b49c0060303079a06c602 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 37361470 1250 37360220 37360223
    0x21050d0e012009030f070902070203010b0a081216050604030e01020c0d0308040206070314070501021903022d1c050105150301030302030340050d0519050f0c060103140601060804 78
    0x40102203100b02c0709495014181d044401801c49000955000440c0d00700072194000c0d0420b070380c0009a280c00d60500740500b1561036020341e02e0384030700d901d03100d40e243c1c075600844060242c841002030012100b42240b40c50006464006040c3e4040b030415140c003811658600440a01600403556030749042e140c14031070360301c450b80c05488200701a0b99a80c20410a60302a180450a101c0c40e9400310102d00e012401401500d48140001603035821405518000469861403480801d1b00420420800ca01400c04000716020b014a00746800d11125003006014007888075100c1e41408070360380e904281c0c2c510360019412608140c62841003025030001042e818882400040c01581c410800320b09003881d400944520542602c1010410650702895941b0106107d5003e03580c1c07920005a1105100e014001044400c949003042894010343d114104d40805020400700c041c44808030f14110400502000c0b9840a41c4030000c0d12115a100c3c07809065030000220150700512030a400815001d0150b40c000340582d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 37362720 1250 37361470 37361501
    0x4060203070308090a0f05060403112d0109060c05120108060609040f06060e160e0f10030915020f0c060a020f03010911120709150c08041221050d0e01 66
    0x410795841c2074401400290011101d07100e54013000b0046500300c07000c100110f1151001d80701a003040d050080042660145100280e005404a103042c46218441c55a40c40300c2445440300424144100310f00400b2000d1003d0440e60400354204d00c0c5c55400001000d0301c0100040908460f600c40102584e0b0302c03000c6581039001148200032034041130845442c071142512400c40801c81d2925015540c0c04c07200e0554050400710024206252055000b038558443c100e41992028519801000000c480492240404052550b60782c000024841064030742c800c520020001076598480c08200000d00b58003c40030441d05028a0001c101120524000c0b21040d040000c60b860550342010402c000520302c4e141c200f081e5401c00c018802c5040c2e10541300603c03400403610340c21440303480c0980200c600140c1c0da821004020306420307103500040c007032801d845c2a10305070341c104410f83c6101e14089109500b0340c80c01500d0400d00b405011b0407503500500410340120048800d2210f407010242c4c0a09a840280c0d094400303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 37363970 1250 37362720 37362727
    0xb0301060e060d06090c0e0102010507080103031103120c090406150c060f090506070206010f080705090c0d090215030603010b0d0f060b0f0d0b1608070203040b0a020106030b011e0503010204060203 86
    0x4651103104100c5407000d00078400c52519140b01840e90846415074051a01c490b204da512080054100f1046141d0150a000900103132405090042240c0c00500000b0700b0302054880100180f03c0420546281c00487e94054880d81040c003099107103900a05844c61240e03050000108440c0d40c1c0000043d540f5045482d010030203d01c85d503070304001c0c10031880c0303040744555101c0b003000202d001042020b01922550300602440d50424100b50015007d03078001036415401114100301a880724072106500c0380440321540d40b280d4100d52001c0207040c5014001e0750061101006c42c00f0f104040d8015400380e8400c80082060a0302a020300c440041403010141500c0e25015684000c2295600001c0075030000510308584080c4040002d01810060700043c0e81050b55801013001e2285204003000345403229060040d428541214000e560740310314002d0000404005ca568510725000f500110040c66204442d0a0303d903846441200705030b81d044c40300f207550f0140ea18001a50b4181842180e05560156000e1440c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 37365220 1250 37363970 37363979
    0x40f14130b010903060e10020706020306030708010209060901030b03160303020601090e0c0a0905130611040906091b0c03111506090709030b0a090f0203010c170a02160f050109150b01020f03040b0301 87
    0x8200154907120035010701f2005250040c1c5d20b100600c0224884c480040e180c0c1015010301d03141c0255500005056841041040a2580c641040c0c44002c2c00918000c0340165004010070f08000c6222445100c100081001008140d004900541a01c3e0481004c000c0c0d04100c0300765540da05000580250003031698035080c000d0004580260740c2c058142c214041481c0b0030355850400702d480a2051314203600b000301c0c080c0305d0403000c2c0c010b00b00108030b07265090080046800d2618003102e041b50b118020702400c40845c50030180030340e82c3e02c2240240780e401c2e2000410010910404250110b68051080b0400d100061155010b108000203a0f80c200d603001c01c0c5665241d27201c01c0146084003050ba19001345885c1003005070360901400440003c0d65807a40d0310500c0000601891303c4024011070101d42c014449007142c6200f0310f028861141d0000d001c160003002a040c414010710600d4005048038007101c000007103550294000900801c401c1e800c455295a021514680701d020717502400d281007508100422 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 37366470 1250 37365220 37365233
    0x1b0c0504020d0e07030804062c04051b070b100e13110d0203101401050105040b03070e0105070803070c030e0607050c0d0503090a0807180501080a0308070302040f14130b010903 77
    0x491418a0800010300c181243c4001d4030b000000e60041b00d25110000c0d050100650240c098289010000c000e071350280b20044905034482c0440c4000e81c0900d54410005500c030a1041140b031070515402c092a80d07a440e54100600440c0040740e8400304500580d070002480b4410032800c2e84150440082e48424040e15a1000f0303000e44100b01c5551700c030414140c8000035a0f81030241c0002d522141800040d140b19a1800501c1c40e90168006814042d040c4020898481c07240100caa0140981c640458501d001c0b60060751940035142c03000d0048200401007094103504003101c210f01754041d440700c41c1d1803c4200c04011a5202c1c03114010415004451520320b182000307500030995a119800303981c00c000b20749010440c606040d07031208034190300280d020000e141c21103c0b00d210345c1030440710501540d8185042035680340000e000060410451400082d5481d100c0c2c2d040d14003034006060495540c50b6250610300c0350301c0c071a041241c4a03812901801c0f840e100755115200d5241070686485010078a56120300d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 37367720 1250 37366470 37366477
    0x30803181c020102030a0b0f010504090f02070b040503070b0a0e07030204051b030f01090507030606051204020a0308030c09120a0c0e1003060c050c0c030f101a120606011b0c050402 79
    0x205403480384250340011039821040210207880c15500068a91404d59a064142c3d0700f903200850090b01d40ca110203640343d80c844120390940d0000e40c8041516407030880284000d1080c00c001610402d502c0b000c1c03004200c004030040500700c3c05201c01c044103440e40c0c001d41d0101c0d00b01d420304650781e81c8450003c20042c1400e800850b8040a00c3e0020031484600c0c40c2d03d13903582c2e4003c80c1c6d0240d5241c13100300103000c80c2c422071151940000c2545001c20030241082310240581c480c0900c81014911040300040466440c3c18810000d103900c01601c9460b82000c525000c0b00d0b400051503640314801c002a41e81c0c01510004200700240e400000c00920385240041c07c48010001415490701400c05500110207d0b0b158040c1c2d490801c0c150b40c2d034507641c01e00c80720b0803820034a610300b013203120380c003d4412020082e0b000a0304880d1314984807130004440e40143d0003030300c0180c14010615000804016214003419001c1011407107031400380c0710070103440201c0c002800c00c1000c500c0020720b50000a1810300c1740342496400b6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 37368970 1250 37367720 37367761
    0xe03010b0109170f061303080c09030601031e0614190213030f050f010513020f0607030801140d02180f060619081815060a08031201030219050d0c05040510030803 71
    0x80d540c401100c18045810050216a010115185032558200701f551160f099944001c24071803082c18152103000190300d904044c44094150311220303030000d001c05001003004402c141c0c844010000711480d0349842800c1d031401c480040032680000c0c000c100d0f10300a80201c84030403090307035242c4500d41c2c00c642d00c43c0418002400c05480902c01c441859034404000d12030f1238000c03503d00c100307041410404e20401422111040f640d901813182070214074000380d000304819040d5a50300454100c5840040d01260305c101c10000b0180d030100007101c03950608100303032682e80d000341003140000000da80c0e60018880726100d40c038021205c00c030716519141c0c52280304400c2250001b40044122000e0500410307003624202e24400140c0b5400040d1041c0a6a464605602c0000308450b902071802c204040d42004c0c1c4000e01440003074001c03c9007110704011800b840c00423402400c030040108070b500c00e00d4100300000c1055400f43c2c9010340e01c0d00e00481c03406030401850a08aa1303200208a1940c2c3c2c03044030015200d05a140d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 37370220 1250 37368970 37368973
    0x2060f04051503040c0b0c0c0d15110405040c260709090504050c0103050604054b0109060f0302101b050d0e031b1503100504020f0405010e03010b010917 67
    0x71405584030700d100000000c241c000561241020f080130390400f040c0c1d900c1840301c60030801000c4020000850b400b407810000b03d5404c140c80c50103041051106c0001a10b05140c0b46c500551042c02d070400340050070503990292804c00503a03d500f40286c805001e160581034803c0506283d0040e131048084000b54045000e15094001a41d54034003542500d0080d18100e0313076500080104400307941d0500c0350981c000c4d4100d905104e981801c550340304c0100c110012503607502218201000c45001c0d801c24061888200c101c5440150400301546d2808200078001c1010310b0f402d00f000059011000300a0100341e9400511000e4140342e800010703a4042c0400701058400c0d010306c0d6210001c50740c01c3c02071225504d09074499403590b9518004141c1028082c00180c204003119141024003510b882c6001c0d1074003001026110b0360303904c40d48003040c04020344e80d000661003800060502e80c81d1900801510496000780c940e0615650003000309400d0300e4200c45070600044550700d040102c0300184514075110840c140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 37371470 1250 37370220 37370227
    0x20c030d060806101716060801050102100501050f04090807020a120c06020109050d080604180b0712060305060f0910110d0c05031b0d0908030406051f03030e06070303060e0a090b01060f020a02060f 86
    0x19820664102c6c40d400603004c40c1200c0010000340d42c060000c9840382c1c20044080100358145000a40c50502e1101c05071b0245684403c02020000c000b421a10025001045021143d90381d844101c440c1180781412103514100460000302640140201d00040350702001402070036210800881d00c044005100b039911a403615401003906507404403030407005015000c00350492610310f401038580d800c8096060041860702d181000800c0d0081010f5070002071100e68a84d0075164004071528010004194203000c924145074080100005030023804108907080b03083c020040e0900c0141d0301804115420207250380704520341c0c1e9440a00c40c004000101d442400013520314625158400290001c44040b5003d568500a01000c401c030314040100c61018190f40c481c203641036076002403040c1c1c45020298000d89020542504050181d0850070141118001a024501d02003003581c000e04942c00c4150f50b0030146c40d0011075014440c0100b0154001c664000f407806280b0755003807000300c0c1d0110403000305e02503050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 37372720 1250 37371470 37371493
    0x6040302060705011538070c090501050112090506060d0212190606051005120402130f05040b07110706080901020d020309030a020114010501080412030906020c030d0608061017 77
    0x14405041e0300b5000d40b00000e2a0001a20310013000c010703a07004004480c000100014140f0403140c1415050710448156500601c416a6048010701a0300c20080640d00c03a18008180b80d8a00d81c007030b9040f100241d9540e03e40c402c0b18000901114000c69000d00a81c00260000720903082c408000b09045202510421946c00f11584050030306039403100d210990076040404000348216400380d1805090200c6158544000060002c0d142d44070320101e0300d25110b8a140040c041d075035040403603901b5420040c0d05104103501400d001008000840b001c17070302c0884007404038403864400c0c441c00c91542094001401c0c45400c0650a984d00d80008104529a42d02040009100c402c9800550b0149150200450b2038850b0440044e080d120030b42209200403010200401c9540c1e405880c1c1ca8005800c40009504110b81c1d0320114080c0020503406040c29000088035500c1030000402020504580c15003000b0103500d4560040c1c0303855090305c242c40900c1880e84144030801860b4030051000d0380348001c407404140c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 37373970 1250 37372720 37372729
    0xf030c04050a0902090109020f04050d0f050a0309030212070b030a020f07050111041a09030d030902040b150d060501030501080604030f020f0f0a0303140702071811031303030e030705030901030b06040302 89
    0x4807a02000b154803015184110705000103802c0c09403a00700d00941c200190394507152114051403003500e00c52076121064209110015140c41d002c1a0414140c1c0c0e440a05803c0c0a0100350276440128043c504c0c039000a5040040032400005036418055603d1954a89550880103074100101007003c0700010802d1000003102403083c0603400c1000e0038180e4480b80340910007030710501d160700d4120072414200305a6131b040c3e90208482843e090203090018040d003450021400604000c8a40c40e08145940c0f084200d668041018003c2500000400c0c00f465807290011810f580c0c0170711502c001c0394000740216000030300660501c2d080600c80e1045402c00307a00000d03424980440f64600440c5504020f42c42c0e000d041c0e1601804440700540d0300b80001c01c1c1070103c00295500300c0e902c6008801c6107a04201c4a000043e1b0b01721074007440c50410076a440e424080301104d03520b08042c504801103441d0100a9480c076001005590b00541c002024500f4050503100541c041c002e0321824a41c001c80400c070210041c1d0381d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 37375220 1250 37373970 37373981
    0x121515060d0212070f0206040b0705031003060c0306090c020106121103011803030b0306240907090b0c07140102060403080103080f040b0a0203030f181e0102040801090302030c10020301050604050f030c04 89
    0xc0074000c00d4608180307901400c08030005c000b40086400c80002c10010039070b0a10342c1908003030f0500d0110790303a548025905014100c6a0002041c00b03080c0020020b9060b85a0407010655034800010804e985000f00164201ca007903128400143c803011030b2071804280c281c160812841809000415901d190a01000d216003a030035049012a503180309003501400c00f0000b403070f8051442801c61945080b04c88054070410744000702180324884010009450a104030b40e180d00a1010105a0792141988a802c0313841c0c1e201401010054403011550300a13540c40025190302550f01500d61080f90b90840c0c5130700c45180d000c44025034040904000000718030100000070000300100758081c1d5146d003042124104400360142c00c0601503a00c4419007a450400401c0008902465541c00e47c0054000301009019001d2503010744029440e00d1940c0c000c2c50740110080c104a40141c1c10340d81006080d0014104a001c01e0040079017140c0d040c48184101e0130000070411050308004d045401070540040001c05694 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 37376470 1250 37375220 37375237
    0xb041d031209030f0423030f030901080a05070516051510141e0d020f03060a0204031208090d0305040204021209010f0e0312040605070c0f03020705121515060d02 71
    0x40c000101d10308004600300103150800625406903280c0014a040c1030802d0003180582901410f00c1034090a1080300703891a4400c1c0c89018065400c841402c403001d546a03004007403210f000c603048100241c8005803a201300351103044a13031140307400e1203698480e84920300d54000d0b084a4074820b4208049041c0d800d05821441180039241c0910942e040c00c2c060702c0c1e004045540c1c1401004051000701c0419542980d0424803141130314600620354450000402207100d9415454150045d6810300c03070651170395002001664021b00e080704045044010840c2d8001c012035201c2e580390400e200d1003c1e554030907000542c005000030310150401c0c8803840d5440c00c03c07000b84d604440740e0399207407080020403207107010701200c0c4103807a400b45040100142c01064a0307400100014000359440c000620f08500501d450403495801c0090021408590314001c2d41d01d24103806824460744030001e48241c0c50b08005201e1201d8110662110802d440e003a409003000d039509180c1070f074443c00510a511044003e480030384400d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 37377720 1250 37376470 37376473
    0xb04030513080102040f05040c020a0201080103020906030106051e0a060215060907030e03031609060507080f0a050f0714070b0703020d120b030a080d0b010302160f020d0618170c07090b041d 83
    0x3203141071f01b00402c98200030700305401d40d0414500500580e820400b002c1c1101d4050790490680d548000001c1d00609443d0030030340e80701068070b880340410070300b56a91b03814a41055400700919610341c0410380c0e80c4c40300c5070f5000d00c00c00c1c41000040d47d0b504140035020381000700381c00c0104030403240807245420b5400071200007043c1480c01d240e075864940d01c00b89035401440c944c00c08502e48411038485030b041d407060950002e01d0708000111003240510950840d101e00d08040b000941307440d51480c041c0007110301d5403640c208920800c0004500c2d60240c1c011241103a40c15002020f860000541c1903460b0b035552900808401e07034440b91b200c643c2d20b0610584441c548140c0d4480d035501c8603564101c0c12121421031450402d0700c14032800e28801e80c03018000c0c80c3c80f6000440804241e80c2c92001400d0600c5105000303042a06101e007000d448280054484501807142e06100240000f011592015005540c8a03a0309039101c804100120340055220507000300001c0c0c400700f04070003a08144550b44581d441d40c500c15 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 37378970 1250 37377720 37377749
    0x2003040204060b18010e0a08010204030f050c1c03031505030f150c04080a02121204170105070c02090703240e0907060905030a02040b01030e06090601080c0105070b0403051308010204 80
    0x11440c1510545000d0300501d1085424001e8940400b604d1980e686841414041507500b420b0403984e076894a00020041d92000b5035031292a440c02c00e4080e00141e004032143e10881d02400e0f000d1412100b040c0035150481c50604040c070154404601500318241c0104c00c00d00c509001041c6610705000440031600750000620892003141c0074143c403482c1c002d214000b8210244018050140046443c0c3c005a80444983c04000c2c921400e146c2800340d0802c0c04810a00f002070005015020341d100c009611060717000800a69440700000d641d1069070820095101018000090401c0e00035400150207494400310146110081f40071505580059004a05032008030750402403400c00420103003016100e41d03e04141083c2c90803022941e00c22100c140240308a40382c061559040e41b00703600808511044000321000e0b0b00b070102541d5241d03003080c02075241c1c030302440341e1030300c20b55001d80112020300303512020076006c5070b032161002c44850308005004404500b04001c000341d1070000b400a44003400184a40c00715 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 37380220 1250 37378970 37378973
    0x405090d0906090f060c031101020d1428020d020706050c07140304080706140c0312150d02210109120e010906031b0305070e060c0c0a0f031e06200304 66
    0xa5000507a100104228080f01c05100c0012441e000208560250504035003100040c0742c20307038101050309030068066201044200644480d50008004004424002403842d02c602e00300c0a0011954400c440c01c100e40030b0218242030341c40341d00078280c01c4c1603080010300f80720880d80c8a07025600d0582c1c0d0204002000710310081405154003031181540380c0321004603c1c00d4030344001644c40f12441e20603101813118208a0302c0300422440200c514460052040c0c81d0344405162101104910030742d146481803005100780030103400c09840640c3c01580042410308401d9141c45221460880c2001d40403881d5281d072514400100c00d0303025010340fa442c0744c8503034040102110006010380c400e903018004142c01c1c4103148c400024810030382e5074400320a150120781603441107400d445c0c9103294041c09401080006800014400204201040e44d00c1100c01c04200c43c5c1c4c0b00b82241d0400300600000e026114001803400e10050b103101c00c200614802c500220329018141c0301480c2d00c4414240400c03205800108000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 37381470 1250 37380220 37380227
    0x30801050f180a0c02010b0607081306050903030708070c050603090d11010903081518010807060e06120f04060e03030f0402040e0120070302030c01020313031b0b07030f0b0405090d 79
    0x741088081c0e40058000030012502c0103005805403110b07080c0c0b80d84290a60b1041e10030b4020031048900500400d55590b500d20381046d40c0e078031003810551240040c00c00441c4081c072941c00c807444003100500450034681c140e1a0080710b5800348108403003c900003403001a0710f4850b4000396200c5e40d00c160103010f90741700400004e8500402801d00b032200303034980310300170340000e80100f0708030740042c82002004403480c0c2d1000400c140b4503002511584891500740009240c0400045840a5400d16992154007840800a02005000303e1590806200c01d05c40000c811400c80040c1c168414059000401c200e24684401c07130440c1e100391030790020f41d00000f04000039418680102c585002650000300550710440488412007000c802c113488030b1900c00241c1c481407610800c2607403a21181321008541c1c90130325408081d40581c2c103100840100c1d10030091309035401c603190340004400d600000300e1140307076644003411030003030126159020545590741c0c94104180c85074070a0074420390b80b0000410b85c5100080700074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 37382720 1250 37381470 37381489
    0x50319020f0607050c07080705010903060b01020c0d060501080c0306010b1902030d02040807060e012c0105120a0c0f02030307021902040906090c09050a0209010909150e07020307021306061b020a0504020703080105 93
    0xc1f0031030b40080400c00003a68000600c10131250800c074002404a0b1080040381402a00d104107540240d07140340304001d01040f0782c0554100c0f4800011511030a22040034942c44541c244541d40e00d0440500518081e59501d10410702c840d100c2c1c0c415a403824010b507c0040407600715400c800b103243d0117104240002c0c1e03000f031103c4582003404d0030107141e051142c0803903410345917540b0b4070b0030302ca0b0000400341201d41c1d02401c2500d640c07104010390302040d445c02200e0320004003840c0c290040024404c0b003074154298004400c40340a4616503025201021a12020000b031005200b4101d8106607518180c002080319440f416104078401c42d10900d5041c0f409009000740d0b200500105011881048004600da070041c4140382241c845440103d908a00050b842140030581c1d4852003c4071002020080e01582c04001070480a108541d0b1401c0c4010480f00582200c400b40500004114454200c4031078400085611071110300c002c0003241a17a880b200454180e030042d1000700c02203840e40d0014480c520b01000e04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 37383970 1250 37382720 37382729
    0x3030f050f0a0c05010209040e01090c0e1303080405150c0901090f050f040f0b09010f090507050915090a080f01090203011a09180a080f03070e0d050319020f0607050c07 74
    0x6500744401d150804106129120403802845072101c41d00c1d0410001303405880c59a0300062041103121000000071f400780c0721030755080392400c01030100420054070010702140181c008100100707248103266000c0c1d03502e40300904151194440c01402c1d0300715076021801c6c140b06504110445407503200900c0003500843c002d40040402c0c3ca200d070018482610354100c0003030440e60032600851000d4200f031100000300381c120f11660300a800c8030000700301000d16050703003c1296141d600400c03860703440c00c0003101d1600410041e01e81c440b200340d020141241502c40900b410040c0107108006140d5680d1030a031074401e5082c2e0011582c0d446114100c19440c0a200b141c2142c43d40d0b1441161960206000405a1400805061103040040710f03000080008004441e902ca602c16003541d65102e900700002c003a900221401400580c4d01c0000b490141480184452115405070080d410004147c0f16840c0c1c40e400c0c40500c3d800c40c0b081d81201c8101101c1040326900a501940302c5a6407401820101410000b05410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 37385220 1250 37383970 37383977
    0x160302010e03070503030a140c03040b070510110901031109040507030605030d030905060c130306050c0306040e01020c0c060901030209030a08030103030f0f090603090c0801091505072313030b01030c03030f 90
    0xc041084d92008002c036114448180313030001c101c85a80314140b580c0d0083c90f483e038510f88004030740890481210402040010f00850485501140c0a004007040c0c500303c104030b903031310358080c000320f4101e5000c2c0d00000c415681540301d1034144a0310f100407074200c1d80d04403400e400003601e54600b0001403c0c20300810348002c2d082d00d010b001c0e1000c00e8a070b159580d040074040010102000880d943c022400125060203164408024401c42c00c001e040b0380602e80003907850502c11450042d100104200510880381e81ea08100c1c0506507043c030010800c44150400300c0300d43e041c150200003020b00c0c0c1da0b0a00c14011503a100e001e0b040c0e00d035415410020440f220340d007a19824441030644000c0010b81005074ae41c1100c54a1401103034403483c92402200e04111070340150f8440d802c0000308800c008400000111900303142504000a41d0780c0c1500700d07817140741c1c4807601c100c0274030030300b64407075050500750051100c00c01c1003805161840da40d070f80d43c94000101341e10030307102480000403e000f055445942641c4900c440d15 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 37386470 1250 37385220 37385233
    0x6090f060b04020a1d1203030906100605040302100804080d0207060f0b0301051b0702042009030c0109120816170c060708010612020304210315120f02060a02070305160302010e03 78
    0x640107032040000e01e42440d154580400e01c48401ea689105041c6c200c0e0200c0c0917a900ca0620f00c40440ea41c2c3d1058486100017201030001245e2a4841c00588084030f800401c088454004000140d1754468040d0003662050070400000360300620724001800b400d4440d0500080a02d1008034000403141d04100c60b81c0309905040502855045404400f10312a9101351090380d1480c4520008000b09202011b442c005042d02560250030306010001e0800e282082e0161940e03101b1400c01140c800b6501d01900c100f00d00d100d80280045004200034001c64801c200c6084640842910741d442c0e24020742c540030200441c00600d501c00c40005000c0182c004205092040242d4100140a0400940750002c880141e50100026040c0304131340e14102443d02109268041041c14290020003600a1440c000001255000009000d1626200d801c1c140e81e0007030080300c2280780d0f9500300001507022141041c11880340d83c20100c042a8207000030340408030080e88cc0c800851440c0300242041000c00f40461217034200d40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 37387720 1250 37386470 37386487
    0x8060a03020d0b090c03061512070605160606080610030c0e06100809010b040c080601030e060c19051201090f060b03131209030c1205060105031902060d060306090f060b0402 76
    0x51910702c0d1a55200c06610360903943d9032101031a2000700003005516210b00c0050001c040300d0400c031810104001e480c800f01c00880a60f0300d6584403002e1140c03c0005800304043d0403000c04802d034981d10148610800b01c1c00c0341d9034980c800c1c0f4194007030704c280c00a0800d8001c10020454201c44100040400400143d054984800042c141440000007142481202c40005038621020340c0204040310000340f081003881100e14005141e940c0440b0a41d0202e4030381071002030341c400e002400510561001c0c0c0e9503072030b101031400c070040c590403a07000c01004d211051181600c84803c419170503000e8003891000280070040c000e00340c4195950b039840803045100c00c00900c00803543c064503240c2c0c49038000400c140011200c4100311101c61480c0e0000d4400310411001080c3c0240407c1103000c03c5001e1400c55800c1d0b43c80d03c00705078480a0a00142c045022000b0101005081c4507014240503101030400040c4281e494884005481d00490100d4485034980744c500c04214251140c06010b20044e80c4c00c50400502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 37388970 1250 37387720 37387729
    0xd0206060a0e0403180801090302010c0e0d11060708040305030c030c011409030d091401060b0309010609060e19150303020f0f0705010e06090a0306090f05150606040b1804020f0a08060a0302 83
    0x50009130400c080c45005206401064001600030541c440007040700d5405424006e0003000300c08644030006800030400307a201d20b40400300a000c84c0d084038032407281d84070000c03c01c049503001c039400b203820384414000003022840c20f0003c1c0c918641d0107406103a803416021106800c4842031101c11044020034003d10403040c00000550f81c2c6510704500000f8080d03640d0508404030030600c080caa407658244038000c0340d44041180a180980e503040024095240ca41d05281e06840e501d0003a00880c01d25400010702c02100d0460703200d95a07299420002d9031041d00500e414409600d508181d0141e03200b102041d1a6040805c00e4526885000c400b0780303515414140000c4c101e650702c101c101e116003404514800741d45d0b03c0d0342c00100110ba00ca10100700b84009071516550880c8106021340e0f09010702d00001c0c1170040a100760521850009118030325140c2441d40d00f04403070304500c0403002c030101022071419640d2140c1c03006180300440110707119142c0349810002800e0203c02002c660181c0e00703c1c9010401600c1c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 37390220 1250 37388970 37388999
    0x5070c05010302030603010e120403140c15130911030108060f0105090105040e0f01060e061c020108061e0a0e010f0b070f0602030915040605010306051609030b09030403020d050d0206060a 82
    0x109180250360781d1204c0c2c002030302501003402003808c980988110088916111002402101d02c1a42c840b100b120f001222207403600000003070107030440d840501552413800c0c0c28006150000202000302c0304591181400d01c1216a410300e070684c9c8643c000014002c46500b0018035070300840090202056604190102c0c403840010b1080a004075243c42d0240703903481040c8001c010181e030b044001c02075155140040030f901c05c42a152180180381e41121204040e020740312081c2c0e66074040c1c540a85a071511028032800c591000d4000c1c219804080381841c6503650807210000400034403c0610255060041d00c00806215a0190300d0718141007000c20000366980c83d2650702145c10401c0140c03a030750b964501c10b0030b12a006409410113100401004108800c0740d1107103041c1c03030040e501044076a036100e58035031910121120320400f01d401c0e26020400145581409903000a80c60243e0742099520b90202c2c66414043c1405c0783c0035001f0100010307215504220310740d030011003101d000243e03510b0103404400258 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 37391470 1250 37390220 37390229
    0x3050a14010b010f110102040b0c0d09060203190c171602010e01020f060a020d02120a0608010f09032c0409080301080610050d080c070506040303120f020903070b03090a0503070b07090605070c 84
    0x40b2145e0000b1070140c01e41c19240101003503d003003550707019440f0440f500e038003141c4070700c401064190070046205840041501d074111202034400e40f00180400c4c043d5001c40b0b414000320f5102042c845585000041b500c00781209848041c0702034070540b401c2c800034100301b9060f20000e045500c49140c1c02140440000c42039004480001c00503500c0207106c4c4110007a00c900318000300d000c00300c0c00500c800d510b0540d015208072540c4900802c86800c0351501a419941e503440042d0000f01c11b40c0e0320b102c2084070140000d00380d10b0701d460f018180c1c0000001040a541010a05890101c5d012004100b0303004240302d29640809240c0310341e100ca6040100181d1807002400c4054959040411880700c105820003002c00903100041100343c131266a89030090890700350800880643d410001180281c0f00d00740261400c020000300900000c0741402081c2c0200e40005185072483d1050781c481c880421801d10003003510a0140300d1350000c0385011940540301103030507130010701004010041040429144440c800c241c0c2c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 37392720 1250 37391470 37391477
    0x510030f020f0a0308030703061a0a030c020a060609020405030613022803020d080319050106051e04030b01090501050a0b0c0601030b06030c030106080c01030c0302040b0702090c070501020403050a14010b010f 91
    0x10014008102007201c0380002c56007050401602100f0b011440c00a14800c4009560030704c4071a450b015146041c1e03100712001441904180583c2c3c1c4000d001341c0007a080311615104591840025450340c105554a5600c04100c4540c0098180120304042c098036504c0301c40340308442450719072a80494801c842c0e101005c20b21003000b241288240401c0e07801c031002141c004040b151004800e081c5000c5a90003589c0d0b0361040f47c903101c218103a590090250f01e040343c0780c030780742e031800c290008881c5070081c0c500b2107501011400c00c10010002681c00007010313000e881c21040005156041c01d0a0040c82c0d070715a04a4001c2c000180030004007038100080140c1901c0e40007002810a07125100032034078211400090503030550030158003084080001841c0d20080c0c0c403da03014441d0001c4d924060f0200d1180f0b00070300c1c0d8005002c204030009400c24800312a049074050308030516091842d00d0301408c80c2c100f600f04036429080b070060081404505c181280407403103090b000300701c10303c48a070001e41200c06140404052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 37393970 1250 37392720 37392743
    0x50f04050f0f0612060405010b010801050d1a0a020c06010b0c0f031615020d021801021209090406050c07080412060501050411120403050d0e0703020a09060b040618090c02060712051003 81
    0x10b44c40d002d041e001c000050740c00311001403d0615140e400f90042000d02800241c800f400000d00d450002481d4007440c1e001000e000c9061305812030080c1700721005000d880b1480e002c0203030510b0340004020250081c0300b5880f150383c8401d0b031500c01b01d042c00c1010120304900e07401406000d240c15441501001c2c465804403100c400280d0203c8140c3c042d008100b110040780e840821a8012010f012440c0c0f01c0d426404da09450311800d070030783d0030501402105600c1c1c0d00039860400150000d6001d900040d040801d5034509401d220701c0f5078841149a1041c0c2180c0c0200a895001c030f002c00c649030250602502044600380302090764102a0105401140501020050030350302203414140100c003200c0d80d44c04503070800d0000745d141e0004c3c0d641c0c1c0e81c1c080c403040b80150420329001601c0c4440344114000d9580040c401d40c5410315005045601c450409040d44c1901610313207000946886511560301504e00f141c02605052810030703406041004445403502c04182810b007000200c0d40469050070a40e80c2c08180c03440c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 37395220 1250 37393970 37393981
    0x411091c0201120c0806030706020708030a12181202010608060112031206170c09090303040c0312020c091e1506040909030e06070303020c0d0203040e0708041a0709050f04050f0f 78
    0x2650451403940b030030341d241380030120902c031544103c001d44904001e404888440b6034900301240c1e1180580b10f0700311103030170911071203030b1580c454011110502601d40010492a006021805240c002d09204407200c1c03084103012003010750280950001003e600001c2c040c13961500c0e4250004100340030380141000804025150b000c9d40b01d81c0400301801491039507a903c420b1840e090340c1c1e26040107081a20482d20400005c2000c0c100000301c07441903511040c0f4510381c03484c640e204502804280e503000c0950044402c4d05002e48c0780c0c8604544101d11203035525210b0004070f00c0d000e000c000c001d0252001c01e035000c2650b4010361517040c11101110482070001071000c4041c2802c0700e00e0460045030720b902c11000201b1600341603041e0050040b0b50f03021800c0d10001100c0000c181e03038a201d6841250722142141c000158490301a582c9241e10a000341c81d4001e413072000c0c00043c420080304484000c086801000188000c1c10030f11044207600c60705a40412035400e005d080700360310340c10080030600c03091126000100b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 37396470 1250 37395220 37395227
    0x81e0f0406091406040804090e03071a27060406051302150c1204080303062b0312020705010903090305070b0403080405120c06070b010e0a0506010804020904031e020307020411091c0201 81
    0x1040f803820f42650043d007014607040006600c20f1295840c2c550400c0450404140c0220480b044281d1102107121010303a0307545518410400200300030140d81101185403c1011a00702c580300c000d103290094989460107140c10401c8a03000340c43e13000c10300201100000140c841040f900c5401071407a040c3e58072006011001e6180404103041641441408030300003600706400009075000d080b04450f81c0c42211031503515076090100381c003075100700e401a002d02a404a4040c4107110b00c081e600300005031030840307140c40b250f0030340d01e6801c000c6001407115102003050103c02e102c08030140804c0c83d8550f01e001d03d191a82401030059002e105c1c4180c6244859900c440000c100307903128848058541c0b91100e030107080082103920240310300344070b1031140000543c9000c801c5c440e0a20510050b1604005c0c0e48840d0288582ca44c0020821403c1c031055031309601581c490880c13401c01c1d03000e10b5401156590313503510501040c0d44500312a00903101c001d204001c0e85e95122100000280c80d201000d4100f0482800102e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 37397720 1250 37396470 37396493
    0x815040e19050a050c01030b0102030d0504060209060711090901020a0c02042703080f01080111040e060111010203010807031406062101020d050c0301031e1707060615081e0f040609 79
    0x90a00c00c1c00280d1030810071502185459610f03000b0010b5820407030381680150b0594507040c1c0c8581c016041044840c889203032642c0700315003050240d50300600f03101d00b504c08900254000c080031307211420000ca45c00c4440c600b0500440d07000901c04001c0d4203209610f8030140c103400e00050028410341e110a2003130814008041009a0030074140c40070040c90501e41805014000c041c0d034900403030a01c003000480c6040050140400c0102e4121111385013510f040c800115240000e849141000712008810040d80e00074000f0f940680a00005420841d103107142920300c10812121010303007030708400c0c10040c2a80d00c070401c008141c0c0c00c0c40103d14511501c0880a4020f114030a4600c10591404081c00f900000d620040c5058a200d000c821704070703000c100700140c140e00400c08028040d810206e0b076080000394100203425400c1c031401700802d0142d2604802c0c03a40b0b0759200c103c1c000040001e820007901062007860840800c41d202500c00f03103414501110780300c5200080003d0071a07503d90030841e00f08050664071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 37398970 1250 37397720 37397743
    0x1302061b01090f0614010b03011a03060409021012060f0308041505070c0f0612020315010f0c020301060909030e0a030803040807020a03050f0d0221030105040e0f0a0308160815040e 79
    0x103c80990054a040d0005040d0584151000703d0b0240000c9080c035904002ca81c1070782e2100c1000320000300f1941401e240359000070052600140c40305e02d0040180c0320706031002c40e0651191a0104001c4058100c1012107070181c1c0031000074484c4442c1040420300721001c50341528150652102c618105083c1590503101d411001007011000c100001604060180c00d5000d5138070545d64850b408241c0e0601700305900007030b80c220811448a01e1001e56944c01903801c1040b015a0f4100b0038100e00d5640c001034211401076114030586912000084101640151400c00340350342165848086400c2d51110500c40c0002003005100c040000390070003e550342c01c0c4500740150340c004204e03000500d04520280d183c002c0c0d01c00c104090310401203442015078180090710f0b43c20b172001403164110380c60101044043e0040c680003207100c5c0a041c1d2210800c5e01c0078413086211a000740c0707810095003010361000c03002d0048007022001b0020800240403182000c10310720400304008480218200750306982403401c11110464 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 37400220 1250 37398970 37398983
    0x20109120b0f06040c0e0910080f01020405030606040c081308040504020408010b0f040c1713080a02061812030601200303091605040b030703120311030a060503061302061b0109 77
    0x806200300714900030700c00d00c6041141440b2540341c48210600040c1c0d02c950501502003a00d41011300c01c1404c0c69072249074000095401c040ba40760380c54101c5402c0040d420310030301150350001014899401d08000b100d4000805403420043c0081201c03006108075409403a0b1141c50711503414003418030041e04103803406850000c0003107545035600c1c01528028586401010f0103104034240c0e055003032615200e0b0400009980e10340700c0e150140340c2070088075480300400c2c03003005a0713091220304085200c000c0038104004c0c00740c009083e1410140e480185160380d54a203440302d82d001c6030120000c1d085140c00d07170350000c0d800e0030a42101c1e00041403480202c41084440401c5120100810129541c006001c8142d0b4a5840c0154480c586600c1404107444490150300d82540c0029010400100940c0c5000c0d01142d01345000038010b0403140c8a245190f000395a4801d000743c850b041400b10745014800c0720b0300030800205208190989074081001c034003400040c5078801900b1426290b120300e0030341020410036400070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 37401470 1250 37400220 37400249
    0x80319030605130b03060a090b01060c02010c06061202030f070f090b01110a0c050109050603040206070227070507020405090105090703020103020d140c0c0d11060a050402040e030c070e0c04060509060304020109 92
    0x1825000201310f00c0f501c00f446881000d000c15a0303c4102d1007011115508902da0381401da013810400d80c1d80105560381241008602e44101c000304890348500405007040c0c0b0980c01c030383c8980d4010180b600c16036011040003608881c0003003009141080c480001c4501c4090042403e01c119001a2601d41003404406240d0252400030030802000c02c20301d8065980c02d0300c42100e200c0d1503605010f181c0c0011103000b900700f68104180800762810411903400040522124040c0c0034060308c5100c4030000a03038000780840c0c4049844e1045260602a540d440070000000300010314100100369651680c6c1d102c040e0502d54000382039103000d02c940c2c0020041b000704841c4845203041c171042c24502ca6114510740c1c003482c0118503c854030680304015004482c0c5021008019036103504090303c00070080640201e90080ea146608007a20310140090211007940c207010b440c48915040c100d480b0750500400070b1408000801c8203012840c1c114060360100c48c4c00f03540315503c2e0703561440140c0b894401904148072048001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 37402720 1250 37401470 37401499
    0x20402120901110405030309090604061d09010c0503060904120504090606110f03030f0a1509050403020a03020c01030e0d031e0203101e0320010201140c070308010b04080319030605 79
    0xc0200c18001c0305107500800050030103c140307040d240140d00440d035060300100802955490000c0f22181c00440c000e2000440a50342e034126002911030703940d05031a40d05908204501c945082c81900c20003201c5040c03442c51803520100240d145000100002c00c280d0307800d012880000e2040c0c05480180030001020032005442e071402606800400b0150311042c4514405254181c10200640b4050600403801075080c1d251021110060f00d241c0c1c002c20f0444001d84400584503590340121790040d4000e401400c0e50710507a0800a0811100e000c034581450b080007605c0e8030141d00000c1280710110340380350006101000990068050080a42a1251030300100610a45031404400d48040342c4100c1d844c61118a02e2038051001440c0034072014140200c09084c0d04000d081030a40c0d01d09140b4144000110040c0c290b01d022082042900c881682000101d91503042640107c692400340000d0844030741002d180c5441140d0302d210740c1405000140c5c5500200e64064042d400200251000030701e44c1c6010f1071704 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 37403970 1250 37402720 37402747
    0xe150702011e062115060303030903030506030a030206070f020309120601061805062502130203091002070213180c09090b06010c0201120e030918010905010506030906010e04080403020402 82
    0x42403502082c40c03840d080b801c4484981d41c89a9011900c541c4510100951246100c001c000004041540d81c40b0518a80c4c0007444490712a01c0c018510031784000904036114140241140c200601d403d009520a0b0402404a40c000400561084d024501590b8401d07002100f24110300880070443c1e0005001d6402100d8003d012031400c0c1640c00c1d03a5075101807030841c0c2410740c080780e03460302c80c060f0822000c000f226100e00398081d0620b020024804151310000c041d07400324860394a11a080c000140e404402d200307101005103e8542d0382d18400f40c05500b090002d4000842d20788005a004103201c0d60f8200359955001c07850500301009400c41d01c01941e5960f20b450101c050701d4146812619000d507800043e030709600a5240000b01d9030182e5030603280b4411b102e007140080661311000480c034802401980c201c0d83d103031400c94280151140c91441c00754980b1108209545044c1c005510803102030041240301d200000b0b10604481010310511350780e48660401a01034400d541000e50041c1c00041d9044041ca103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 37405220 1250 37403970 37403981
    0x90f0903020105131a04031e03050103150209060904020706060b04090b03010b121c180807030501050714030a020307050708071b050303040501052a0a150c080f04060e15070201 77
    0xe90000d00c15a07540049151001401c1030000b01015050503407204c480e001036800740d901c544a82003640031501c251010b06410b6081c241c9400000b03882d01c0060041160b40f2081c0c0040494210703040d41007020740b0001401c180105254180140d50101d000e40601c03c15800035002428181400740d59542c0f02c1711118050000340404601a600341403500300d19040c000c210b1810b4824103000b4001e08071006031807100300c80d00c1d61104401c001d10060f030401c0201c1d404202d03800800300d0034014401d00785103103022402d440e802491642400340500d4698855140002180e51041c080304005070b0b00d80d109a02034465002e03c42c1e01074807458000c41e5030701c01c1200a0900791480c0f0300064032101002c2e0345504260740da201d030b401980d0000310300b07121041004540001c0c1c6541015030306010100200031030502440e0138001d010948845040d0b60051603100340a200e01c0c0c2218419251040c214500301c0b00300017441e00c0140008195a91b24144003241500a12919000d810f030451407900c203040c0000c000b0301a02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 37406470 1250 37405220 37405223
    0x3050a0b09040c2102010e011d03011e05010e06060403021c050105240405010501050d09020a0b0304081c0903020c15070f050d090602030c0c0906010507062a02010c0c020613090f09 79
    0x100001344040114040528880c0309905950301c0c1c40b08a4130000455002c1100703003440c4aa0300541c502c05246039030a000304071640340001e010800c0117401291070f00907100183e100117214502c403024050162501012103003075940503520250784501d000080400100c80b098040d11a500c4d00b0144141d403008020700300d103100700013155800305248460410044034802c0c420b00f030120f10b04110405210740035400801c00d090009000108261740d032010003603203500c202e40458080600080004140c2d546002c12201101c811104018001c55a54080c0d6242c01148540d8898103001c90420406240081200d58060f44a006c0d10350404441c98541d030f84104201d00b0002284600001085d0a8400026643c42c1c0f10000c00408054075550f081c4101104081e14240c10000100410008582c2d1030262842e0300e10489103425105011689209080d01da8404520440e4100f48251510170340c4149407610560701202c0349962141012425088103000d907010003111420490031090120b04c9901104071103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 37407720 1250 37406470 37406489
    0x81e030a020703090b12010e0603010e03030901090209010f030c0b0f040b0c070f091107020402070201090503060702030901030c0801080a150b100504050f060705030703080928050705030f0d03050a0b09040c 90
    0x301c1d10b0390744482c25806041b0100c0300c02c0440100400c80320107150f0700c20350402c3c0003800002d0380120110543d4110307482107a929080e41c1d1a0000e441c11414041c0a850041c00020f00f0f40401506698450480d0000e9118150440740080b41c1103015080703000032600100400191729590b005030300c20090b2240d09910503418402d001400000306081b06000c1c005240b680140705620b0107183c0c0d0308100c001d422501c4240d0410007058408555a201000b6450003800560000c0d5150307550980014151220a40307000100702c02000104006007000450041143e800900c43d491030950341e956400030549400000d502c00f442d034841c0c9500c150001d0060041d200150741d06d501d0390404001b40305003442008070007451580300b004840c000c07a1103800ca41d60807240c840280d44040500340c807001c480b1082a4020070003200803407003147c1045010030044004000950241405114011000752540300041c4d211080c103441d1000261445001d0340706807001c00340181010310f6030501d8207286215070a14003860000c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 37408970 1250 37407720 37407737
    0x313111e0a0b0306150705120406050706050a090305091c021003090308010905010f05010f0201020409020714010e0d120c0c0b0708090706020114011412060129090a03081e030a020703 80
    0xa07864603004582c03080c4c001501e45c00d0b50554010034003205030310600b42640c0d280030710341350401000e500d600107100074002c031780c0c80c251580c1d02411328004452011b48900b600c1440c3c4403000001076000010749012030001c0300e00c404050481c5405450041d042ca0000354002480b0303009001540c1c042d03000100c7d80d03010303a43d041c01e21383e2202c101b401121404c0c00740c1180d00700406003c0065610420031003000340e0151001600342130740d0b0040c85003a0f0704161000c8030403c80b00e0904070f0113200c00b44141890400e000b8014140d01021a070080e0204198034040414030340c82c0e905580c109802400910340056105620b1039807445c00640041003e0019240b02040b40108403000881030b03c140070301c040c0d103400c0310f00143d81a480c288520400d03e00d10421180c10140c100d1805a02d00c00504c01d8a00a05449082e403080303070446012001d0289103511080da02d42c0b4107006504541c2c0702e4140000949a104282d559076540e140340e01d255400e10b000c404200044004100840c0110a070080e1540f1407003500c41012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 37410076 1106 37408970 37408979
    0x203041e0804090f02030618060103110c03030a05100803040b090418030c020411130e040f051c0f1d0d03091508040b01090207080313111e0a 62
    0x20700d2880800c1c100100b240c280103804c0f22101602c0214694034004c000102081c100da80b0b002d06080c8584002841c99009511000c802d5600310644e5450740910003040b940c1e0342c030440340915114100004201000040da4100e425210840c018604040c1003104040c0c0d1074018444490b4001d4a900c9503500c00348100e5041c0031643c0c013035518210717822118010311003920400d662440c05808100402c0c042151311906140c151041c401e421095521035003005d80c034401d01c800d40600180189a0800c8002806842d100d98144050b1216180006020001e440744848800d00c500003000121302105149000c6003030400c03840c40b074240140920740304c1559106804500d0315210100d18030701c042c0720501444081d220f0040c22215019480c2a0881da00e0100d01d01000e01070f1104e54003a00c11241c100040303002030400740100600038052110b0b03041d10503000180000c00480c021006580e0209 = true := by decide +kernel

theorem cover : BRFrame.Cov 37230220 37410076 := by
  have h0 := BRFrame.cov_init 37230220
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37230220 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 37230220 ≤ n) (h2 : n < 37410076) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
