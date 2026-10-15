-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4754
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:37:37.127609+00:00
-- url     : https://prove2.me/submissions/1ef7be63-b252-4e75-9087-5571771f82bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 854856115 ≤ n < 855035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 854857365 1250 854856115 854856173
    0xa0306051005090f0a060827010507090f060e0310020904020c0111030601030605030a050c0d03120606050406030506010813060b0f060318121207050f0409150806150d 73
    0x960004140d04407900e41e602d060315050359070100500b02004184282c0f040700034882c1000540d03040304095500015072946007460f02079119001d1000c907011400718030203529110800c074525402204400941344a110500b41a035207a210945140038010031541d890740c440701d03107079080c42d070b140d001440d944802410144c100f204091440c0d0070365540e04004404060b01004100c5296818070942d002040201e009000c8c00c40d09031911500ca0312622402d0303004888481030030041c54040c54440c1d008220419080020f5a5600380c010a2030700140100c2c00000e00304804120150310a034a5940a074000f0740341e81c04d00e0b072104e9803600c0090100c2c04680b40c2094024030345254903030f110000345100d01d4900081e010070310600c6200c0d034106907010000f0ba42e120000d0100d480c001c20650f1080340d000070607091061352a580544410540c0c059907112100362418034a2210411000c2803001c421907044034100c8100741c0b6a0840300780d0000203042016044600c0d003440b0004070f03c81003e000f1b42542c0202400750a41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 854858615 1250 854857365 854857369
    0x50d14032211182a0715022101180b010e010f0912080702191a070f0803071d0a1a0d02070812011503050f011202030c040c030c1b0b06060a030605 64
    0xc0807110409140c03000600c00c003d2440d41d49080389010b240c210300503852407008859107804c1d6010305c14010f000321104008860f803d4803164100d03640c020103012030020706103441c150004a00703002d0281c0d180b40d108801d151541d91072140286109190140c680e0b165020218004492006c10103806c20100822031710b000444a50240046840720301070f143d41039550095006020410242003442042c003d108501040580003c90f582500035490400c0a55900b01c1130400c0171031520590005020340350b0001c10b00030f40f01d40000c0d030710f07901c000c050070309850a0340c1200801c90f82079414030070300c0686149d144050050016501c0100240c0344002001400d019107901c8404494100c59461200103503450300501c1800082c0c0d422103440d80079440c0501441c50040d1895481d0300040c403c40301c112400c4055101159028088a610344a014008021646200500030094048400083c020640a44144070144013070107040d91626003190701165903072540804e10040343e02644000e0b00f055940e80c8045869 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 854859865 1250 854858615 854858629
    0x2090d1b170304090e061317092706030c09010510030f0603060e060903090607060c02010f0e07060f110601030b1f0303031509020702180603030d09050d14032211 71
    0xe45501401192100e060401d0f1070304030b40d178014080a15610160400140708460045400c2c660741c40920700b00401300c0c00070314054034024043c0c403075070140c51307069000300400d5141420041214211070401442d21080b0030715407201c4a45030000c2d00440d01f00010b0003541004c40c000712030007078145400640c1d1600c150041c4d040715281d800880314a5203840c1ca407114000208089500103071400051031070300d5002c1d400107000d84075141005150075101c103003c10000f030003940800401100d5201c244100800766400343c0d2035020b0380c024400403801020f680c460391446804d901c8046a221401046287d0035912a0781e1102c80051928181c1c034198292503140da0150f40d9400010340c0310b034030007050a82d06100048000100b41d08006092441441036001503502c00c40035090070341e10720800445949920000c6804c521a0b00349448103039041519040c20040c0006106c0c0b5000e000d03035508102141000d106840743c1c4800d40e000c0c1204078200404030034042c5003824068526200d0600c00c0c05d500311b008007003012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 854861115 1250 854859865 854859899
    0x903100518070f140f0d0b0f09010e0309030c04021e0c0f0c040207030f080601140f2104020a060f020a060c0201200901050a1202041e03120302090d1b 66
    0x1010203032141c800000c500410244010708500e140311901142841d2a0a407419080c04e50a03103d0b40c0c50341040c1070341d515140c0204082a401140799907440c42c061500103924202a07642c00c005600e4039001c10300007140401070f102d00220040c05401e0390b41007102004044d41154290503240103c011030f88615525a80040540800c2140078040c00c51928401c94207162540c00100e0245004012180c000b0740d000081c201c0403503090528041079115000100d907504441c8441880745d0f0400145500780395071b160040e050800900c075980c4648121003030840b180c1030082d0b400a41143c5404424040c1d140100c0c2c11036400e4146104032014913100340c44c0c2d50140c075818410400581d40da442d0200103000c0c0f501e15241a1100c071442c0038a40489180020328078494202c50300c0801641d286880c40300220707a0100d0300140440c8403030b4901c0780401d8075400038501c014442214000031050101d905180030340262091181c1c02030107090300f092191a0b10381054000700804d80702c00703402d100105042001e1510710301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 854862365 1250 854861115 854861131
    0x70b060301061d0403120c0804080a12050901061403070e0c030c0d0227030d12020a0c0c030c05090f0103020a090b010e09101a03010f050d030203121609090e1209031005 74
    0x31305050801a00f0302d0b20000010310000e041c00d06500420f9004080190025400380010750b41e1312203c00111a0103112000d0301c15028142024041c201c00150402410349000c034412001083c0024209030380c82181c1e200f8a01100081c0e00003030305a4201e00d01a541c4441040342c11403600384d4090b9031600301d0307100d028048951680329007c040c00ca210150356200072007040d001004108801c1d40b020706031108c54400d0054254000500741480e62044d841c00031880d900001500026440e46003030410300034039028035400b400d807034400a6909490164054100d98000d0f0400710710500702708000c0040d01e4807486050510500298044040d25200441c81c4202d0310302119044580c02e1401505a080c040c111003040490240014401502c201c00704101b240d0b0211170320b40c0302000a241c1681503002c1d001e0001007a40201080284028001c41c1985090842d540d41d0113280d0b8507400c111040302c252400c03400320355110150304281500c00e0390081c29118002012075600401049901c02a600226103450f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 854863615 1250 854862365 854862419
    0x30601030f1412121509241c0b06100c0f1106120f0108010e070e1302030303100e0604020f07060903050c0106032f0306072f0a0201020709020f070b06030106 69
    0x21901803403c00c80c140c2125090440c80054170030f1100140e02900302600840034240180c0c1c6e42c0c001000e10b40030f10340c0c00c118060440351125100041e03458240320090710542d05508442d0000c2c1c840d00e000700744c2800ca02481d84400144429680310a414040c410400700d41c0911501c0f520012035682d20301500c0550600d052074600c034070344014000d541c820181e03c1081e0b030342c0c10805414030398030b00420f50740c2c10b41d0b031500344800d250380d0b414804c0c10954150ae680070b90140000028801201204c040c0b00042e50308802c0d0442c42511b80c141070000324414400d0b15050340c04e09000f00b00004007560080036406000741707045420032804040c01403c580c00ea40c021201608150380c001505401c1c09000040c411558a181e60101c0d0f444000c2921404000c14103000c001484c09505400c22a03803500341400218940b100c09503c1c5001e120a50384e142042043e800b51107210000500324006000302c40040c0300e0075417107a041084940c0d036040d04e0880034010035459522440e000c500000704440600d400031701c0b40703298 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 854864865 1250 854863615 854863627
    0x21c03060e18070807060912020a12080c0607080402010903060507110709060303020705040b0603010b071b030b011d07020d03020c0c0402030f0708180d0c030c0c181a030601030f1412 80
    0x114a000f08941c07002c081c1e0f401c0780c1810049660000c020808655043c901f00e0309050aa10004440a115400c5185980c1d60100c4042c1806004c0c07000c3c165405803001200c000751070f0f9000646403033f14101c900a0005600315014000a680d40e001550440424100306c0307442004042000d08050351600461882551844e040045c150b04000d820000c1c94165810021100301c2008100144414015100592030008054041082d00c0c4649900081e0000d01c070f00b110b58507480d0049140500784104080040544400c1148000500c4051301490098000380b150721620071094010b500f008982031710600030101c14030f020791500c0c00154450240400115607615100d1005010316001414144000d00000400d800f24100000c61144424540c00c000322200e085190845402240c0040101161401d40c00025540918104041c507043e00510601c650b52040350001006203100c410380d5030690100c0300400110b841d40001242c10b5014651008802c2c60b12203030035140010308a1020160700001840b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 854866115 1250 854864865 854864911
    0x60d0f0302011b030e15041a0c0f0412061d07170f01060920040602030702040f020f19020105070c0201081602070f06050316030b18180d05090406050a06021c03060e 72
    0x80c115882c141100304070b847c105510740700c02c4941c014014003155400c2d400464001c64091080d00d1000e00d074810f40e26a01c544924540a080340c24000c121201e9090044040100d0740c5420308048488454008142c1b00d031030070302a04114581700042c40c45501803050040c400300b00038012070001d8485c050000c130b01c000d1246070194070b08410501c0f2141e40c450030b001c00c1c00140e90200440700c5080c0c0481d4045128820078070f0f5080203104820751502091400226820405100d407209103c150701900200103030b94a5800954892100420090000381d124002804020f1f501000310300b80c4410b0b204458000d5120280810741108640100c0e0125001104114011000e600300740080342240c03500740043c40590002c41e0b0888400c01e074907140301640348000742c60000b500590a0721111000c040381e00d64946080040c02036030044a0950146061440100b51801e0103102170048906a50042c0308081021303000c8900101c1580020080588480001804042da812981d00801a80c1c1c152002000f21003a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 854867365 1250 854866115 854866123
    0x8031302060d11070b0c03061003050606090d030309111e06160c17060109060e0708040615090f050115020613060605100504080f0601050609040b031f0504021206060d0f0302011b030e 80
    0x80004495030070820080a6103851460308827035074041c100400c450700e9000c0000c0d010b02900e00d000d9000f0300070306840c0c0149989900020501801001540011081c0e10b040c000c4228007940e15044c50f100c26081d068150034800c0040c51400b5442002c000c40708243d540c0c80e40015455440403c0d588002007980300309060a001407801014021800c0104900c1c1c000c0782c0b00c03d200000d0000302800240b00004081c4051500440c80803050044940806c84d03ca940b000014200703541c00c0903c0d50315150020076000c494003050405500c1d1600241515509c00c41c561030508242c00d005c403800d6454500004843d11104107002007810070347c81d01926107081080b042e260080e24040303805940e01000040186480b0745088551400d8251004500320034401c000c00c0c035101d40140c000e884074049030075207000c240707690f032019014034421100000040d02141a07265901c8055441039030000d8100c01c0c201c0010544070cc5205494828000442d40400034813078242404400380d0003401203502e40b80f01c1108040148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 854868615 1250 854867365 854867371
    0xf15120609130c030605070513032604080307110a0b0f071a0f0606090105040b0c0307061803020c091819051606080a05150a0807090b060708031302060d11070b 70
    0x24801d425036503858003c40c81d100d40c44050015691740000c03510b0580f1400c22200341c00301d108030b020042942da18111150008000e051350a018501050304240e20000742100e04603080e941c015400d22941e1b445200b0803864000b11907510000c00d036000504007821001604085903040119501c03000d440c2044052584020380708a60203c00d00f08105003021011105d541004081d10040d861340404030040c0c4087c81150000100018080341400c466a4000010408580f00c0c07001440780c59007403186200400c1e1040700003009a044021840254204500059031010741c40c0f4968049540d61a60710342403115110b06d0205012100d0300c01d0050085c00c010749840c60401000c6000d09a182180003002c0e9036000c0e00c1d02c0307800f64a03807000c81c004920054509d0002c401c014081c901c0c1c5035803106440d96500c410311035000410b0504108a00c10b00e410400d0360b482c69040400a0700d141d80c5d07001e24040b40502d640080381e0000042c040d210303298031140b1071400703ca00e442c0035142e910503403810142e40d459001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 854869865 1250 854868615 854868631
    0x509030c090423010e0f0618070315020901090b07050d090b0a0c060e0c031501091a0d031b0611041a04080d051e12041101090803090f15120609 63
    0x1440c1400009107000b0b1049000043c02c100d5201d2000084851901520105e0f194844a2084200306e580b0400c003c94010300078110200c1d44078241c1081d1003a84e4840e0b48510018240301d01840c4180003144050b0000c12240344145004402907440d00c5030b030340243d0081c0405035650741c0503c03401442c49402145410142ca240e00b07680e0b00f007078407400b001050074283c2e04004005035140c04140301205410400c0e258040c60041c00d4a0300110017912048010209110740f580d51410000b035114542107140706680d07014400ba201c0b0700800010380301901e609000044544201601e00b0030038000c201c031481000c0018107503030002035440f80350a044d2a600c0c1d0510742c500d079a201c3c0801081046010000310801c1c14020350030724545480c854218041821145040c60344403400010342c000d24505074145a0344224800c6042020900011300119414603803406041d1a42d03100f00410300c4d1600e4500b00038012000001c1034400003070503546680400d604480c40c0352020321011803c0c05054606000042c5c4c0c84001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 854871115 1250 854869865 854869879
    0x303120711010915020f0f040602011b170411010c060507020d030b0613060804211809050618090c19050109051e0603060d0f1b08070b0f031f060509030c 67
    0x810f07125480009440c41042c1c1c1110360001b0040c0c0c909000d80f003502c058404640081c0e0702c4503650320000e4060704000c0c2ea200d04e09912a4000c0e862580a01c07095141152141d4a800d0a55a2070342c945c4a102c80081c000c50600c01468003040004031907014403032041042c0d501400040b0480c03030024095524206615201d0503040c492541d1880350801141d0860310540360440b02511581004c00c23005110505201989070400504100b09420200c0c8030302214106485942456403003403c282128800c0e50b61a0b40b10944981d48000442e072190410f4125103103502b5900e09001d01800902204c01000c50a03038070900c41c2c401084150303000700d001c0d0002c1c0420749800100e000c1090303545081d00820f0010903c1400048007290058030f03440c0d0300700710b610350000710004031007040c3c2000e035020b518030501d122902485030b0380403500741c8001c03a0420444215412132401d01e01c6400000707a5075000100301c119500c0943e004074205034100002c0e07030020203035521956524101074090500f4800000105400b60301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 854872365 1250 854871115 854871131
    0x10080d020d0516030e0d050c0a050603060105070311190c05030607030e07151214040212030c030d1802061c1a010e0402031906150905030a0305070201080c0405030312071101 76
    0x2411400319000c1152038283c61034841814901079401e00c4080c402190842071142c0218200000015800c10035502240c1908400341d80d8010020b080c8000c03030b001d50002e6400d11103038000038080c0c1000c1b0310100603203090720fa1894043d070b9001400500c0f100b0685151f101060100041c1c1418440340350888501e140074000380300c000000e10313512501803080401000c00e080d6a0f5442d14480e0122440e14508e02c0d600f84a940d0041d41481400d01d003d4600703a01c903081d5100d0100900b9030000031a44812883d401940c144800404080d0040001a807000703070403141001858010795884008040d0079034040071011141c455100030900f00c4000100c14121034205a041955580c0c0150a190840600b103c0240c0d80b59601c40040510840f10a4401107140c00d001000c52040e87d020240d0f10040303c3c65035141c2220343d4410401d03645509958000c5e000c92810025040994420740600d0740c0560340000261500e40d949011a28580c0310b00900c210512030a8140850150300400034454101d01c0b40080c04106 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 854873615 1250 854872365 854872367
    0x301090c05060705030c0106060908010e06010806060105090301090c06031d0115260d0905041401030c0909030c050d05070311030c0709021614010b090c0721140310080d020d 76
    0x10040c014140b1a410200e090f90402004004076045503000c00028010203507903500c080d11406050140001135400e101001c510b0010002c0d80c10304803290038006100303588400b00195081e602c6448240d8040d52140405008500f18031a01c0300200581e03640081d821109c0ca0341e4120020940d81159441c1c1d041242000c80702d98000e4980068440c1e004100d80c503c103107a03d40302c1060255081c8144140560b0348620781158110101c003044403400d42d414005825900441c2c05a01002d000050848100c9182402140c40c03d9004a0b41903102e4105a0080300554176000e103001c0107056044005000050401d080552001241c214181e1100046050a8100d8040c42d00c540072802254201c580c0891002d02c1c44030201000d203407251b0402d1243c01c0ba555000c101324040c248618186009140743c0f40840c0c000c21001049440f1035800c445401c014440c0010303000d00c981c2c600f400300d0080050381c0d407000d484400403500650154200180c0e10039468a404074507414204d0320020101950003159183d2151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 854874865 1250 854873615 854873633
    0xb0901110f0c0108070c020301090f02150f0316020102040305120408120301030b0a0504020a05060a0203040e01270905070b0c030711010305160e0a030507030510050c070f1203091b03060b030109 85
    0x80740c00d0904c21040d0342d81103800ca508500a6078040d6040d820701400e4803c0c08800c0c012400032500075940c0c1206421400c0d801110b41c4141d1049160401040000038600c0d88418034000c020748031807001519199907611003520b070a0781c400f201d62000741e001500f0800011700304210441e03591800032482c00e6600d1500c6502d1075190007030510801036280c600090440d501c0d9020b08002e010024600341c0c031079501c0385009640380c1141c041c403080907000c040042224950030102c52410001d40030800302032074003400554050901480211854440d0080204030001e96501405811655400843e22007100d424032502012440c0a4181030510303140920a40145080181c0700c0c1c1a01da0070070610305242c0002203001c0e08556840504240240600030040246c04200349074098825030b000e0140e41c40d00d090305261807043c40001024510500058000070701c0303241c10614261614140024958803944540c00510243c180803025490071400620070081d05200780310101400b50000c1103034400179075a80c100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 854876115 1250 854874865 854874883
    0x718110409150807140a050910060f090b07080d1b080109020a02070801330e0f0711151902032a13030c031103060708061203040b03010b0901110f 64
    0x401c1e032100d04212a14140741c002000a0450703004542210740d6441e0030100310355074400344d036104070b0001000003528900b442038603004000d40c02c03030402c416103000710598409500d50380c83d00903c44207900014946104001503c0e202e4011400c83e175940741c40c0b00c1101d044407071829450110380d542c0508050b000360302003011070544010140c010b07901c48910100341d00d84003659000d03c01c03c0d800d05c0f043c0b0310100c3c081d918032207824038569901d80e001810569102c10740d040500030710400e80002000245c291401415494001c0c00d50b09004c4151140812814142006444018211000102400b0054100b8880301c010740394004005c5040d400c0a01b8004050040750020031200c01d084c1c11081c005030019000c960403030024040c0602c1c1180c0d43d2a044280c1c3c222031000381c1c0c0c840d40101e004a618140820742a100781c2965403000d8143e540c8000b000850503200d03103601c1e0288424040464a1070000c0300075400380c40300c4444ca40d2a0b9442100050010200249142c0c46030014500c4020103600040d10b402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 854877365 1250 854876115 854876129
    0x8011d0130080c07052704170a0207061d030a080306061612032d0914011a09070c05061321030b130501061b17030907181104 55
    0x26010004071481c500c039960204000380d4070802044490400070300e00000e0900e58500400e440146558004102c410080292056a0f0007402c14103c01c8441c40170502d01e40c005e00c241022038600c19102003002c069084005c0c44400359008050034440c2c01e810035608200d000ca40401c092103d24180c000c203407500800ea400911208000c0049901a50b0b042d0903a00c08246403421420086c03036908060314081414241140400e18202c2540c0c10705100a15842e00244094842c00c225181041410000d00302e14600356a604181151030420400078050324501d43c00102c4405125900c8208200c00b41c100a0300080c14000405510310008102103207065001480c0111854942c2c20b40c01c0c06400419881c961140d040c000402c014002500366124440910081d20342d40c1c0c01e0800c5443d540c08983c0c080c054400440e100c0900e4402e401d0040e001c1c003003024810040c2c4104004c075007030b900400e50415240c0d039415801150041c40b0021181c80c010502c100083c405001c0140d240104030203038810740c01043c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 854878615 1250 854877365 854877389
    0x21e160611120a020d0f050304111905041e0b030d02120c0a150e010b09012405091207050909031314041b020c120f060115022b08011d01 60
    0x2194032102408000c040c1c10b2255107040c0c0d182e00520b4001c0d01c0304840e2969030085068030010080c6113100b9000c1d41d200303d030300c02400700c0c0300946c1e6030400404c14980004c1d2030600039202c0e0301007090f0310b82d4029801030104c20380c021442012529400c1080e941c0304a00d10f0702079842000d4548880d64005288205519590301503903a0345400e0043c1401d00781408000b6003002c50300054070844a843d41c0c4066181a403000c020411020b00c0307401c004054030203200b0304031602c0724203c03403003408110501000b5140580381499440c01070b1460120354100e20344078000d1001e81280c001000745003000c1c070035607511403d9030018518200d165900542020a28000c0006103820300c80203402548496100010b02116010a0242c508604100035903a00c42d196105000d84400e1400000780040010024000b52002018000306d80c06c008541c45030206c104040021881600c0f040d0b2180350781e406014401482c0b001c4100002404010068040201a401711210042c00782d5044440d900c00e120450554450005503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 854879865 1250 854878615 854878637
    0x2c0a0b0403050304020d0803040c0e07030207170a051209060f090d09150e0d050c0411040f030228090b01140c0d201e07090e0304030b060d060c021e1606 67
    0x8031b4808042c0c00c2008101d401c00206100a01541141801c1207820154002c10726a4401104809a0040600c018650701413460020172614600000d06610304180c036103d810300c04107600c040091030081c0c0e48070045400c00001d0005030080c0350b40b003640c4120403400070640c1d184028070080820100c1c1c41520160280059201451442003240120401008100091190f21403d10648502c602a02d692103645404c1e0303c0c4081d144002d0540b800c445000140308400751550302400244075940502001d0203a840f032035030038001d20928003203026003090640007650174003802c00945484102c00c4003480f0801c0c02d0040310315400000907060300780102c0b860a451000c22035100072440740c01d2049225000e006603043c250740322005084ca91a08101c8100300c640c5250b80d246840110394925095052a400030801840032518500320b080d0081d601402c402d1f05455030382c4a180868191741c40c03800040c0c01c00d60140301c100c0c3c0110a542034071072500d4003504070030240803c044041d82c0c90f48140d0044c820001b00c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 854881115 1250 854879865 854879869
    0x5011b080901030b060307030b0f0108090a03081b04030b01080c01081009020c011515021203040507060518041103010e0a050c03070e0607020a030507030c0b1903020714012c0a0b040305030402 84
    0xc41d804e07064010385210303101c1c2030050014000d01441201e660088480721480752541d881000003a0143d444600500404449a18115103903480249113031220305510080c50038148081c0020002140078240c40501541040880d40c10918107180340d504100407242403141544840c2ca080084541090006a40d03a92111ba040d0243ca04411404203d014002000844024444140c0d007a03150540c2583c81c0040b01d400c02210900082da40030344140d001d44428000e10380a68000c00b0210095014110341c070740c2c0100010180c82a511100108041c080010804001e00407031040c0c10041c0314005002e40e05d007881842e0320900004100d1400c1005201c0c4644051310f0f008100c40c265500a4501a03000740c032400c01039035039650b03480111000700002c6000622000705070180d501024001181d141c0e0850f9150b0b04070041e406c1080265142e803404101c004090700c0034800c42d2120001c0036061200e22000d00400740703404015202c600155008a60040c000540041850380c1c0158141003050326a1203c0c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 854882365 1250 854881115 854881121
    0x3040215032706090f0627030708070309050f04290109030501050a020403020907110c01051b15090c04060308030f0a02160b091b0f01120b040204170705011b08090103 73
    0x1000b801d02500034039107002180b0010450f20b201e50f134200c080b100020f1000800a030b81d2003080b81c007611300c03001c602c441d100003a4000b6030b8080c9001500003103d06140311a1203840d4107a014100480105110351410412400c0450030740f40c0345c08080310108401c090440b0407000758030644038002c03041c605c0f51030441c0c5140c0c01500144081c0d60454000c119078034041042500030350090105074820315800001580080c402c04a03500401c0c1d1203006001203802003030054545400081c3d9082003540d4425094081c0502003280e042e045484e04800340d401d040c4081c0c2c1e5400e1051041500e4082c500b08072050000c50320740310450303410855401003462103907682140342c2c000740911610784081c0c0084d60003510502c2810402d10340500d41039425543c10300511988034000040800002d40c01403806114200a58040c1e0681207095030000401b0401041c2c040c00a0101e90258000405210348105022500c100421021029090a0800110411140840c85038001e2000e100412000c0c0004980e000c076403082d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 854883615 1250 854882365 854882401
    0x20304080a060905010b24250b15151b100c17090c0d0b09010b0301050c1215030721051b09070e2805030321010b0304021503 55
    0x1030161405411246860000f82c40c840c1c5050752550300b8911b98125a180040c01e1000100c100c1060000c964103050707080c1c15036000b089040303411034076405001e1461900b50440b218058030a8151010030b02e400725040444440e0078035894081d0110200c050314420004040724a000c094800e44080081d84543c03044c80c000e4403e04000c4d599080202c800c003090703008031840c469803210880c03540095541d03561140d95114448640b60307202020340d0200b0f010400703070054660400d10180000c540001854040f07800d582d01664102d440700d8000414a00003203448500542026041146400300e0080000080c0d03601c105001720181c0507010600e8400c04c6440042002130b29610000fa07d002d180c18030410326a107501c2c4058240030f0b00c03840740000c500e140b107000c0d6104c021500034220b400780030843c0d00301505454400065074141d9042c0c1e0300491681e4081014015682c0540c5501001000d0490308908200042c1e201d030b41034950034018000141d4689a80b50081c12100317000c96260703543c9262052000c1041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 854884865 1250 854883615 854883629
    0x3032316080d090507081002090105251b0501020d05072105040e13170703090e06060f160c05090103171e0a020a0303110702010905040c0507170903010c0c05030a030c020304 76
    0x30060107010000003042e151700b00e03043c082c20b175801307080001c10381f905a10440032194005003080200c0250b00c00b8010750014134410008031080012a2552407020118420f40c69100145800c4010044c44d0303030401c103103010001103240040c2081c2caa591000540c5d5081d035404a03500100785c4c2c07040750851040003990010801c650392000d650500c4440100c0340012031409443e071a0f4171114100303a9054410440700413030750656a00300d07094030780318141d2410b030006004181d2114042254845c000c000300b02800c074860414641400004880c989401500d013550701039406000300b24010804101d01140301c441e08583e0280307280da94408407480c00480c4402481c6803009800c0481c0c03540c5e40700c0d40014003072120b074400d403010840c000714181c1006881c0561440280000c9519000344110b0800c2e80284d000085541419400d01e803060303680102228a464070822003480115000113136140c2402035602c0307980503003041c0d54003c00b1611840c1e220f11444c4907000030f050300c0340700c1c0600aa00c20001c8500408003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 854886115 1250 854884865 854884871
    0xf09020609060307031119090b0f090f1908071805090709020f091027080a020f03030c24130b060f010e10050a030e07052d060d0603032316080d 63
    0x358214101038445014040c0003c3c181c06800720b07104527050200c074031070602c08030707447e00b4400d901c1c0800200b050020081074200ca010030744d41101c0401d580c440313800780484070050314445081511900c500c0061040c110f05450800e070500c41103010215448041d550351350005070b0348011010400c4a54030401e140070b500304180b1140b42a03102d6001c41d10750084c00e4076440c0d0001010401c00900d24081d89409a40c40c19049807a40e80d00510b03203081030360b526520141c10340c1d080c01e0701402858105801c041010b00c1114469501629094142c2b603903c0c0d0080300c41e401c0c1c0c1214191521022900c01c001462580200480744007003800e40e0044807454940c4d00700031708001c941100b801c40206907400880415020034100210b5003000940400c4d4407084e10406001c1040b002c20300922050500b80c020120309a440010403032000c0c0e625400d008042e03070400c602000c14118a980780052081d1a50420000444001b5054503c41c0c07401000f101c03072240100011b00030107009410180310511403c1e0400d211a46 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 854887365 1250 854886115 854886127
    0xc0503061302161101020c09240a0f060201060614210c13080d0e0411030604051f08010204060801060e090a0203070e060d0e010c14030106030f09240f090206090603070311 75
    0x1104c3e600e540641c410030303400e40d44030070400300a000d10343c5415155540221291190582403005c402d074900140c500080c10000100e40e80d2401c00c8007404103400450040c0d4450f07800303012086d00310420f81c00f07144031a80601d162403a1050010140c881c10703101507070340e20807690100b403618a2110076100300518488810708502e5851416a5580c0c222020b26004901e00d56180451450f00f449115043c0078503089041c41c569038203040100524000300310111500080c55403d19005d040c3c0002400791510a0005a4aa09142d0054441201648000200b21710544403180715210340110940103030360b0420241c0c50fa20f9480f0180c2d0740754030440c0b426400550110721403a00c7c08164200c0c001c0708011100802c0b0034690031070220b400014026001e0b080407010001008100e200303070703c98010491220741c00503560303201e0b5941c0118080801c80c0300303402d072a0300b43c100c00b414051482040581c0c2c05080c2c0400c02c3d0045640801c3c0c1e20b0040d00241da100b5080400003480d528065001104001001c0c00170aa0b501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 854888615 1250 854887365 854887373
    0xa0201050106090b1602060304021801030c08391c03030504170c0a03050d110301090e1018030503100b031f06050909160c02210609010c050306130216 66
    0x40901c01e080000f2014000000d14494a108480b200a0410b0650b59850060340070300400c0d03800030300201d03040204000c2040208071a21036072400303980708450a01c0401e1034060030758070740364441100304210400c40c80855460b00000140c1510300c540e19038607178100b01c100300002d02017040c0c010340d5120303840300c86a0768400c1562650269100d1031103604208000b52003030b00c500c20380b4025801484030b039500100c1e4242c00300e03004802800c0000701854003c1040d441d140d00c08a1660030aa11560004d603c071030306d048104d5130501c1544001c201052080004d04003503502c17200d18142c05a0007809000700000400d0401c01803000c2ca1002e0000c0c4c84c507070365803402c059004140d10718170030b0f40070425951540d45c0070429a00c15400c032a01c1c01002020304100380c0301c0401002d089a90100918103000c0110140d0300141c4400d00141c0951300600360120720090300b007021a040001c010549041a454550301601142e0000181c80e048642610030b561005a00c420100083c811036184015426062180350104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 854889865 1250 854888615 854888621
    0x806150f0c010614012c03070617090105040302250f0b1e04050a090e1005180f0f0d0809070314010606030b0d2315090604030e0d0c26030a0201 63
    0x241c2218003c0140710340d1412540b00b0001541d5040e0b0000e40c1c3d420420500c40b6003200c50310031541a4138800e10b950080400007a140826640c000b80214000c950300c0c4001120708000582d10a407240000c0c0001c0c6410b6030029113442d034007503140c0090b0003429070505400d12001d940201524201155807405501d494643c03410342c1261070982c444407118080203520310684070903102103643c042d240644c10350074000d03500e0260100545c0010a0312075440940c0d1071070f500b80101801050614901c80c940700c410b1900c1410450400c0c0c9409455020f107001c00501d8034006520300790700001e0314103000c464844025890038060150b0010788200d41d001010001840d066001c0c01c129183c1c3e03101001103984031814000503500c9544d01a010015a0317444001030308042441c24045003450054580d8174540090801d9541015181200581e1040d01007100b05900443d101c03107401400c41d00040042000c2d0303565901400380d400b071041c45e83d500700c07401c80786201c00c07521144401d805c400940391141c019020090003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 854891115 1250 854889865 854889877
    0x4020a0e130b09161a0d1a03010f061a04080606091324140402010f180b161104090f030e06040e0c1201061425060603050604060c090e0105010806150f 66
    0x4c102400d01c0090300e0403400002442c20304c05600080d0420145000030f80c010700e220f80c1c00c20408061190700c1115641c007842000d40d40441c610000442509140a4401911403480c0d0418541d20400c02404074100000d21141d100008954041c815940e8101d51035450b52040801407000185105c0b10381240d008540e40d010800061100304206040c0c040c0b450104d400c00e4501a0214110740941c0038000d102d0701445a480e0050740c041d982155560319120501da0046055440000940e0259003c07c6464510080101d1045900740701b84003c54035201000d5401d0680141030000940d10002603840b084207950040240000c0e0381c1c41c3d450300d0740d2044103d5000c0060007a40c00b200c04004109607000d05120f10900d50580019070400c45484914010030903e0b03c6042101100c81c3c8100e0000794940c020300003e544502c02801007405c06262a5055503001c00d10321b001d1103690034081c003500314015800c9045a40903e04510f29844000104104007010030600e0f0352808001035071400ca505040003020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 854892365 1250 854891115 854891143
    0x11061207020613020d03260a0209090903090a15030609050a06090e0610150e1c0b07030e03030f130501051f0906080d0c080409090302061e04020a0e130b09 68
    0x2260b50350f0f00803258410003940742d000798010410002140032038820100f251002d880e0310303201d01c88100340da00103c1241000300d407002c4460b900094441030742d06005403900c1d0040a800003d504000d103a800180703181515000d02901c01040044842c002407080d0000d030000c0c061356004101a040503000d500141134103020b0f550803203080400c0e0041c08840010701f90301c1602040300c6548071030304105000300020b400030078080030007400407541041d65950111300b14090702c4040040c11910843e152842c1e03143c100801140901d4a0b200403250f01d450040110303036100c00a00301c015a9951516421509119441000342841d80780c00200300310550301401e0402c08100907044142001d0786c1c2ca03017031021780d14030b17014981c80c94016010300e05a00d805a010f440e032642c0b0903016181020b403916010000c03185000c4007a130040c0e1051302409152882d003060201c40e102410049a541e29064010821811040c4960942003c0c0354000900022041648255440d07100c58051032504107103181d587d407040d0064a4807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 854893615 1250 854892365 854892373
    0x70308040614060d02060318060a020307020706090320210c01030e010b06091009030f210f080f0709120b0a1107020108130204150b0a090b090109121106120702 70
    0xc0944038044005620803c80200200c1c0006038075403d200113500301402941c1003543c8241c3c11440080c0a03c501480395000080051300d03460582c0c3c4c02803822859510410038040d01c0441800802c110411072041103401c0140d1003a10801d4102090440703511621300007a0301402441d008030030300041413440e030f0004240d03003d021030401e400b055400c81e140b107022568000d00c1002901460300f061023030048809060b040c84003005a6a85a4202c0001e4150b0102d0b6503608131a0b4042d50040e64881042d04030445103418426517400d40005004040d001c0e00703130307410351948100045d0481d104145040107010b41c0d400c580700c400a10b181c100300c145c000381c8204014a040c0468061000ca2540564100ba90160354003c02c98940008042c0d0700c4100c0f06080e81c025468000c44002c41810101d500010f0178020210b0b80e03640005000240341e114581c00a061030f01c400c0015886603030380940114151a2014242c5543c411f447c0f4100141c603031210000b5400807008a40074422982c0d140a8a1042c0d4040c0c00b69 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 854894865 1250 854893615 854893631
    0x111e010e06072f03070203030c0a06050f040312020310050a06050a080f0c090607111e030d080c09010e030a020d12141303080d021b25080c040e10020703080406 70
    0x26109a2005010f8a01001c482003180c090582d29070106042d0703512080560b881c244040c0c0209041d1b038481056299154000038480003000142d00c28258854521603400c103d43c00c207035a0052000703018145e800d04003900800400e022340e005819a4000340001400107003803650f00d03031000d402604242c01140c0451103440000c4e00400c00d1603006882450304003030607460301c4910020090340b9000314005440c1c3c00050348481d119601d420000c00201f60400c00d5035180800800c0c10185007441c05c4030740d017040042402c00d00070504881c40c01e44955450074203007022400003c0022910f084c1d0b04500195008500c4490340060100c40088011101c025541301d04811412910115480c4030328021481c910b00d40705010004690604040c0031100c0800300003610300782555040c81d10a20a00142e40c1146d04154440140c03090080341e10f8000a48041a414403a46080c0c0040c3d120700301c81d00b0107405180c560300185d110100610401101400000b0210748a2000b81401081c01e441150100c3c5d85515002c44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 854896115 1250 854894865 854894867
    0x501060e040203010f150512090109060c031802150702030114010e07050705030316050d150602010b01030606200f0d020c0406060305061311040b0d0516030b0d03111e010e0607 77
    0x3c803030503100310410341c074007803840c0c10321a031160801400c043c001c0040502640410030f0407200c04078043c0903014000315408100d0306040e003c546c8070034205424075242c600320700203540794072440d051040c0d0102e62440000c412541030f14440e12600000a615500c1c1c4841c0e4459a16200b1405050390f01c1030000c0e07162541c440c2d906032074522440801070099441400002e810780340d07040f880401c0d800d062902c0383c2031501c601d04040036100c14070301c205a20550040280031070b9909200302806a1400d180a0016516000300900800135805c00d804a4201d05504100d05003001c0000c029039514001c00c48400ca1051714000b5150840a03056610132400e00c1c10000c0c1840c82400b80d140186802008402c503003464111200c000c03c14403515000741a0140320001d400c04805001d0103524004a0003c5442c0c64150014481c041c2500052014189421030321041e0742c1340d000c0d992104540c5410a102210f000c3c642151070021103420010f010850900301095040064100303e985881c881c0440b141c50700c070500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 854897365 1250 854896115 854896117
    0x1020a02010206010b1e2b0513080903011103091c0518120724090e0103031e0c050718150e07050d02160b09060906010308070803071b05010501060e0402 67
    0x180640160b01c00030050140700d40131002040000c00115481c10b0010801c8000708081c6c201800c08120107102c10191000d00701105c56450058a402200f0401d500c0c040ca019040b40751208005080300d1008180d01c640743d102503000006000d000e00580b81c80e4a408030380183d8a24a900507070400211041e483e0141314000c2d81640d040040166001d50304a48000500840d50305c110440e923030501c02c4003000108107151010021114140ba108010465290003000d45015400d5000000d02d44005004201082d0b0100d80c0394040d854032100c00c502841035240441e0241c040030401b616030300034014001404140e010300c403204003980b010184400402c510014010703540c640301d4a11544d1202c0d00242c801ba21500080002c0304075044014208884280410100c004412003240e055403800180310300000c0c1002055032111640c2d000300000e40c19641c508405020b40f20300182001408404100030718050181c20301d006076080f40104960700e0b18208a80a4031083c82000c02041c5c1d145000e08a5041c030340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 854898615 1250 854897365 854897383
    0x160902030415021303060e0c0a09020307031d190f0b07030f1a100f030f02040f03060b03160e13150911120a0b091c02070501020d030218040f06120f0b060102 69
    0x50261403913803035a22104041c2c480d0941b5054035008151146202d5642d00d2072209c05007420f00c07401a1249050741016017100c601c1402070701c46104001140c610035800041140d0703080400c0e60b09606c030744114500042e4950030300100400012101c41045106c3d681a88001e110f4650903805001c0408001269020031230070202c81600103240b03403403401820b030140a500c03044032060f1030009600d900c1d8400d104102c1e00300b80c00c6070742e80720141c075000c00a01c4100e009680e252007084020b0308010710b884648004003c2540f1030020040340240000b401001002640e83d042d64202e0701014a501c00c4135100360081c03500580403680c003045820560030038181580b000c0705084140c0e00424281440349c5840f41082c2004003404071600c1501c80f043c160204161403040040c4840e00105101410440060308200700581d03c1403c040c8103202002c00c40b901402810000c81040c0d030001845038007003136401c000d440e0701d030801012051490549410425203010f00c0d202d0b0ad000311086c40841c0c4641c001240c50392100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 854899865 1250 854898615 854898637
    0x60501081603050601050904060f17030f1e040314030a080a020901050d050a0e010c05070c08060c2a0102040f08060f0708070822060903080f040201050a030c0216090203041502 77
    0x402034001c0060b0080c0c1c002c42d000081410881d040a841500083c152402c5401040b0443c2d60b4040400040c88400d402d0b0300000100005142401c00a5038070030000d000300c1d00000404441000501c0f842030744a000ca501854003c000d010084007010481c0380e507503100781e407110000340c1284006040e01ca80c0740700350394500030169145480c150384207052001500000d0300d0540c8a5984001c00d03404044240310f04210000261100d41c0c50300841d0500c00f00e07071001d55000709220740241c010054148006403c40e0601410070300040f50901e5420455412000c003800100001d41c40010040790710000780c400c0e2021a402a0b0807624a80d032014921090540159289804180448045034400f800390a689901c08401c420a402201c1d03004860980030000400a80c1c42580e107450080615510103c05903000004100f40c40303103424103900090980c07040c41c00300f100300340da900303027822410348207103c84200c00c0e6010300b544c050f007612054244025401a1030444076000140c4030b031404c5010fa4004e4038130501107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 854901115 1250 854899865 854899891
    0x18070f0504020d111605100e0a02011101150b2515020f2701090e040c30060f0606080c0d0b0d0203010504060506040633090b0f0304030306050108 64
    0x1900c814040607400454100d00c10300c0d21150642000002030300588150b01d0300100000704400103040103400c02540202d0b1002c0c440c201510218203400000d80d820a280d428a071003100421010019801400300d560185034996020100003a40c40c5080041c12102452040d1208100d03154404002500554180104007081d1203003c10965041c50740035116408911204030b180c08031240320882c801e00c50035500040b260076020312400e00e580c00341308080509081c0b842d07203625090903100c6680e0b0b0621481500c0150440f0002c0303544c11107203040b0580d45050584c2000c0e001e4003880c5445006000ba5012092015182420000d0b03a98400c04205001e818825440e51406030700c1c40310b003000341c078081c0c0116812110080b0480016142440307550311444c090b80000076103081107820401501c1560741301c1c460110300082851840d02294403001d9810f00c002c41caa0103030714003005054501410940c0503030300081010500c1603504900d84015131095120741c3d0108080c945440042d40e000b1410346180315900c403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 854902365 1250 854901115 854901119
    0x80603011e05070c05031303030e040b06120405030405040e0a14031201120206090a060e03210f0c0a02060703122d05090703060e030a1d01080f0c0f0301090518070f 72
    0xc050341c442d607006001440e00030385901403500d50600e540d0103c0d4008040b0382c00200104241035001e18900f80c507032000c40f005d00ca20f06407500010018020410190706812000c1301007010001c081040f18014040507000384039000342601d01c00d407203d0f00c40200380c03100c00c00110340c40740564001c012070340e00450303865030245903074200400c80d01c990301c1e283e40c00c036003281c0200301060035940d50281500051100c0d40c1c6402d080c940840a040c00c2603070f0140c030403010f9010125680c42c0c41f05600103a4084800707100f04991100301400165140c00324452000c0c3d00003400003240303424181e21000d02c071001d410414003403003254003030014a180f410306208803410705400c00c00f54000602e4541c101c260884000c1d002c031085943c898907104200c903c903c52040c170681c00040d05822042c1c001442c02151800c1039031040214440d480085d00c0144000d08004a42c5c2814000a031160000810384500d044031320090760316503071034120040c0207007010f031103490100840184101d140c01000070488166034251194590140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 854903615 1250 854902365 854902421
    0x60901060c0c0e010e07030b0f010509010311091206060a120b18010b040501080318010201090803010512210a170618090124090c08010b03010b0f091f08060301 70
    0x1540072008444000e0400000609410002072003800707401c00c0807107070700e403030510070805005c840c807003040c150040c140076082c4442a0703041002d407100528207003800704c3c40d000325421001c0c0b81d210310310f070345507110100d0001000301400010b1481e2154400341c1d1030750308041d200c40c251404801880c3d4010701540c4450001620102080031000c00c3c02078003400803410101100004042d07440982204000d640003050b01146000c03c1245084860020b0008018001c1143c07100300041c41705008240c050b20820050419003001000703040c5010030310442c070100d010504994400c0c0d035413100c480340340021460f9419010345211170b6000c601500c001040c808400c1c001c010303040d111507001442e134074413175503a031090201603648911000c1107907800c0320001c180c4a0410540a040700c40004004041050b07050042c403203c50380c0390440341501c010814140c0c80d10b04d481c0c094810303132190300c2071541c0141c041100070b0300090400072156554907058450603500d50704c1c402410f0884103485c1001d0203219001d0600c905107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 854904865 1250 854903615 854903627
    0x1b14040207020a330e0d140a0804091a01031e05060406050d0f050d08040203210d020c161509052808030a0306061b020616170c1506090106 61
    0x8070b00c081e00e10034105aa482c00902603507000078001d08940c11141c14070f1911158100004100406414511740392135020001c1b031030080901500405504a0701c1d0819840c490030008110080d0744074501d140e440d929800114013420051420301c0f15840200d0f40c0c0d11070ba40c040e00034145441c087c5c00c403c4065020310741c041d40182070007603d00c0b9045541c864001c603103505c4040c8000072550152202c0340e403a8600b4a0041d183c400040304042c10091130500717000059801055100401e40d20b07028140050103008402c01c880d216010b1004206480040d4080c644500800c82011800e40514290186603071051100c6410300b80d00400000244c1c00c160070301007443e00c40205150b4840e0a00002450724544006080005181e040003c0d550b01c00b10304000601d0741801541d010b82400d160a414145141c1800c0809070b040c648020b00c500008070300c1c0c031400030048148200ba83d801c14107031582c15140d4038903240e00350700a0242000a0090b00f540d10b200003d51000c4900034540541492032981c078041c070440324 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 854906115 1250 854904865 854904877
    0xc0d03031a0918070909030806010804061103010306060815190c030b060309060f07020c010f12091703070e062d16030206070e0118060f1b080301031b140402 69
    0x404910806a001c1ea48810780740c80d210b15014409960050126403000703290034183c0c2c3c04402c8030307824851481d0010390700c101c034180c2012081c2440025a20b4500d460702c007078030540f508500a014080000414002540c00c800200c500580544542640d00c800e8980800b400b210100d1814407070a00448000e810765001c000055014500000d56540b0302c40050040d0b8010365034400540d0040040c40344030904201e98640182c9140014805c1c0304041b80080d00e5080700c02c40900c20b004100d0048851480c842d00070900240e841500000002c180d801c640c482900180c801e800003412426810045040c520112000b0380b250016001c803201c0c0a5051501503042400890300c203100600a0b0002000200c200320100740c469000750026107424140281044216402c81d4100203802180c4080c148190342d000d000e41c0e07521b2031302c18801d1140220590740b810f0350740e00b194140700120f20b07501c2c01c2c80041e101071410380348100303c00801200c21281c9078a01d49494001c0c583c151012602c3c910385441c040c1c1c02015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 854907365 1250 854906115 854906141
    0x7151a060a0e041802040c051c090309030203061303020607210504110a081c0305071d150408061f0503061603090b0906090c03030c0703081e0f040f0501020c0d0303 72
    0x1142e01000360102c0e054603010709583c0500070400f401442103141600130034403d0349607494003030304254000781e2540340c1d203000c283c46d849101d036280302074000d242c800c0340c068016507000b808448450408409007012444507903401e400501a000120304014411054501002c855808011280c01412807840041c80094400c9a0603065000c5050403515442840e100601080000d0403004810106200c40a0120602c2204140c50907041255454120341e007283ea0185800c606460300b110275005c500b46480503a09072003800b0000c200000c1b60100000e40300e1140d80800450303074113010b401c50600081c88960040a5068121000207150740c40115462240465140342c0801c2a0400f43c44d4a014000300780c42c81103287d008001080030b20781c1c04000107980c1c80c00c150019460009440c4079070741c80b1445404020500d210000e4020040c00300680d900038084410322615031380304031440c00240a988148518403814000c007000003000d60001c40d140642a40140503141c3c03c52056400710300500c54004103c0e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 854908615 1250 854907365 854907377
    0xa0501030e07030b1504111c1503080c12190306080d201f0b191404020d020c010608070f0608070503070309030c050106060305100e01121e1707151a060a 67
    0x800342d96191f0081010740018035020b607a030b94200b82810030b911800752078a8400c10f8140b0683c0317811500040c1103202105d8000d080c1580340c41d41d0400c0365082c542040048400c00388042101521441c940c03101021408071900c007000300c0395031200c45c00d4860641b982d0000c0800c0040410390f0300d02d6500715000e496291440203031000e4041400c881242c240088070701308038040d83d8001000340c03401d00b401d0450303480d004008445c420a1606d109000c0040b0f030a0080303406642c000c40c0908400c0c01c0c940590b20b20250a400a0005a8441d241c155a80c6541d110b20aa4140748410000304940134058190094505503195490b5984a000541c090442c84208804018080426602003031080c85407001410720307070b900494142082600f680c07288807160042c03032805c05207000400184c0852400c9170991580040703040300201200402c0e156040c00310001502d00400326a01342c80042144006001c80c81c4507552444800e2080388045003207480000c071201c03404c0c4200c0b80114a61800101500317010705986465 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 854909865 1250 854908615 854908651
    0xa0c050f0303130614241c0b0f130b312a05130c03060e01060207081204080a020d050f030c0606031225060207140604020a0501030e07030b 61
    0x2526581c02103401100032441c0c4050340b010808280620604e0850001702e00d0554101440070303802c2c8410000d82e03803c0800224260603200d48403000c0944040e00c120f0b40d114800001030030320a40341e0070304691407400e800b2034400040e84202d0b01000d12b4069500004200c8155a445241e0402044200703c034a05444c3d081d0920003911050701d1940242d144a014400e907201c0c584444d150050902c12302e404241e5103001c0c01030040c1e0300c0d940c41400004008001c0842c1154500400b90001c04a90b0820b1001c9031b4580004240650001051030455801804aa41506481403041c0c218016401180007542008266502524000403503840c010f008405031081c000440c004c1e503280d40e0040419445c55000501080078901c2c050143c28204030504461900e000340d125801449121b00041609603920348c0c0004a062201c2581600c0a2a030f203e000d5111031b078032a0080e030350384403400c84040b03110716108540451154802e020f49130b091002d55004040c41c0d4156640c04400784402400c0003640d460074904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 854911115 1250 854909865 854909893
    0x40308072409020108070e01050706050a0b0a08030a180e010e07030b04020408070e010504050c030610030b06040b092d010f020a050d0908060a181202030d0f0515010c05030a0c05 78
    0x71074200e1076060400058404851001400311140103114030203002d004583c8000076600001250a1286d006100050b1560381d1000e100c020140142216000110b00740c0104001d507000008204451300c0340c03200e921004000c1d0001659450718000e2005901058004000d480010307800c040d0066054100843c0e600712082c0858202c0e0455030003480709502040382080394550090030340d03000d480261410310551400341c802400a110280c0321602614105044c03400c00d51007a40703d0120681f000303019070795545c1d075101710300259040666050310640c46107401001c81c54603400c50043c2010005030389031003c80c111005640c03141171403031094250f003d00741d00d41d40052420300911303034921440e880e2100c02e9414903c4180ca0300d0001000f0864681c503100128002d034205003c19140a03034010203408181e030320540c0032030850041c0c00101441c01d041044245450449400840c464040102d42007140e0001d01e0045840340e48804014200d03400030800500d84034400c0013010b2501d0302070001c50b0110080042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 854912365 1250 854911115 854911163
    0x90603112101050a0909050615120f1f090209060411090a080304060305060105210618090705120a0305070221060a021306090b0913061a120c0301060504030807 70
    0x81c070030050742120380060106203090410304014010400b4208441082551800d95907607010300600d440c001c402c40705d078105946045801e0b01c0072510134241d03280c0c07840031000700344d8130000f4402044154003002504440c2c03403018414014130075001081a076250700c524041c0401014400c0a80303074100010020303100f080d01d401880c140203006440c0190352301c42ca4100024103d580180002d810014204039100081e5001e072001c0d000c0a8400c4110001a05c40000007001c0c1201100000b540c12071160030461035580108440e0110350068860b04910504402d80a495040031480200883c1d000e005050150411801c039070200c8034000d20346500c0f0400b901d41d86180c00c0e400c50740d41e42c4181e000640d007015160a43d6103500105000d0406015850a14082e44418099000320360302441081040c04188240b80c0c0200c4000d021000c0c00198140f0407054540c0c40d544031041400040d03503510301042c10002110222412241230703035900303402c0c01d05681c1c41100c00d50210b5400d03079120074922050703855440109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 854913615 1250 854912365 854912407
    0x18050307060b01110109050f0606041e0e03190c12080712050603011404050a03260601080402030106031704050414090304032a0b09100c051b0d05030d060f0801020a09060311 76
    0x170080002c40c82c2e40c8c2c045440e10a0081c81d0354010340c1410340d000c03000911f0190111741286034000214500b00c25103c641d1650042a8804030846c1c4024114080b59400c0154180001c0c024202d0840300c10710390b42c00390740c100b00907180ca41c001002e54107820503c0d40280e02840d0441d00c0103002003010b01d000c004254840e041039038150313143d03007040740c40204150700000100b40c100b80c200e50989016405200200f00c04800801041c1804104400981190340a40c00706000d103034480b060b201d11040d08100040d99820074021540258641009180448203290308a0312070101c40c0011840c0c6401c650341c0c2c089403100c42c032208100300840201c5104014104201d030024105400303150340c4604103c401c00000701a22608882400f800701065800700d42d0118508066038561000000d182e1b1903080850f040c8081c80d00e000d040350202080c03202850a090300880100c030101d074100c00e8040d0711840660b00701e2099080d41c90115130f01e800c1c20403107035001e600f0000c004c4425801d000e0400b44048440201c82c9508 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 854914865 1250 854913615 854913623
    0x110d060c080109060509220c0e060f0306061f05040b0c1f0b090f0903041706090106150e040906020d050901060f0b0a14070507030203031c18050307060b01110109 71
    0x14150390054640c40000c1900401c40ca0310103001c583c0ca0000854004680a401e102908055010040c0700058441c402c0000c60b40c004507005510341c0c0d458204611110549100344146844000014a031400040040c01010014040c0b000c3e803444004000040d0190100703002440400d00c00000e0481074038020344815400c85010b4801a4200c44042c00107000c074803990810f492600760003000d607481d13026505a00440e2054000400c0d00c60000c200d103540100c1d84204031040342c683c0d000b00403007004140f86002d01e4a910080c001ca9840b8500402d480600038524400107034004089401071a241d00300071511801030000524110180c1c0001081d03c0701141d081815039144c0d44104518100d0b00703040002400806610f03814848000d400406104003051641d0216001141d00c10601100b8011100250360083c01c40e650307200e605523402021012808441d03001450701c86540050021020b0001c0001e0388100510300c0c01e4242d42e41c00000703101c030b4061103041100745200e84262040c01d01c00c200b020750107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 854916115 1250 854914865 854914871
    0xd020603100311040504150c050d150f05030a0302030a05070305070c08030903100608030a0309021302070b0a05010801060b0d0c02070323070f03120c0510180210030b100c110d06 78
    0x3103080c107031407a08140c0d54980c0194078190030000451f20131040d88042c44d0114401082140ca501800c50301d40c014048050801c61616007074034152000030b101c51044501c040c448004141da150201501c810b440070b40a0701503082008000c00d418490001040c01e10b00c00d041181c18211907840d0080d40745166040949aa4030000d41c07102c03186030402141c2442406040c042c40f29900345400b594a9000c2c9040e841c06054844521100310742c0c4540d03c2c0701d0601c6008100310345a0201d0b0500b102d800c1c00076203154048514100001c00c01c40f42c18014482070394100301c2103d00c6c01e19603c103290020181d0091420031406560f1004c40007504500d00741c60301030400d08140b150880445541400c05900d40e1015403c00d078807040c200b0000780c091055100b14401d0b4206540744499500340796007403002c46900180d4940c6010365204041e1803000c003802d0035070b000b034038140216900c0c188182c0c210780311441f51f07551002e8070720040352080f0301c604103009100b03101c1ca440661030002c0c40007107007070032a403201e0842d21076403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 854917365 1250 854916115 854916119
    0x80f0412031e0e0f040204080f0c1207080604020d11030f010b10030b0a03081e07030f090b090f041505061b0f0a120503060402160c0e280504020d02060310 68
    0xd03000304440c840b0304150745454001280140e0280091005250b40b030f0196102801030340195880c0d03416a801003180100342c3c0c0c40d040040d03070031a484550a02e0521f116400740c0000002a07200001c00d50300390740e02d2038001c1010f91200c0d002c200601d03c16900c200c521010180560003030f503d0502081c041d100d0850008200e00e400d01d02040321409065000c1c030205490211104003a543d04c00b82c1c0f01c11281c002102a030340b20450042000d51000055003840440c0300082d600301003660001b41500c10b403006558015809844104c520518442ca841c0c0c035902030044011030b505464a98040900064150b001c004c0e8030307075281c010645503004111201c0718910858400c0c2c200340c03410302440b0807001443d40540300211440d43e0f51400c1003100c0001408104010001441c241c9442d4100c40d0307125105c1d401180001124640203a44450300d00495000b0900c6002017003581003c07050481c00304050030303403024600881614410080c5002402a41d1003000c415113100940c640d0310066015848125420034514 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 854918615 1250 854917365 854917367
    0xa0e011a0406140d06090507080a03020f070603020306031f0b152107140a14040306090302010f151e03061401030b0f071e140301090f050606090109060c080f041203 72
    0x6141d540004910f0390b190050000c1551221040040e043d03000000041d04a21420100e181c00c500c0d801c190494030440c851038080c5900041d4201802c2c0014080310210b64a0710422420780c00b080c0c80d22501076000380081e00103e00185641c1d00d080075241d0002036191407041c00500e59104200030f2152004001507401c0e03002908854a081688450202e103049040c8850001c12442809806074405000803603681e00c054403030400c4c020300c422031480d6143c640d516070500310014003985000b04d01641c60300142c0b2140001030300940300c401d09103020140070240344c07401c03016160f01c1d041c10341100f450f840c0c5030200004400b44112104181410b1100041d90304500d4801d074440b001070100f15a0000c684100000198840480c0700360900040000180c8090b401d07066402c44450011b0900d000004400814161803e902031880e0722a505014030150f110b05007400100d104190500d4001084000c05101c0e0900070060820854030824615140071200044880940c2054100303802e03210301101d80400781 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 854919865 1250 854918615 854918621
    0x714100207020a0b1204151806050f0a05060604050127030f02100302040f050d020102100504030f030b222408061005041817070507241107050103050a0e011a04 70
    0x5000c80d041c1c45032600a031515905d4503c0340c000d200400e085600f8035460309550040d048150f4611019000b0030780d04000c0d00d0214050182121040c161401e03150024144100340e029050040001030a040e292078200001140c00540320340503240c42c21141c58102d00f160b4540c0c10b5440c0294000e0100640d05425407041001c900c0b401c1510b0010940140014014004090046821504212012969402113100507400d240058180344c01c03480c81c100404c0b050540003078542021a10f956020041142540100440310320601401007405850a100211031402544000312120405004044800c1240400000c40b1840d401c1005560040c1c1c0910400c020821100c1001e0602214244807018203450700c034022802c098805010504414011240500ca440032074003407581060940c2e407103c1c3c5980c1641242000d0407501012103000c1442406158810030b040d040b45152080078025152400004401811001e03000b40d40c0030b50386050220545000b4810201d6081c84a501742e1f40340101c0138200412 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 854921115 1250 854919865 854919869
    0x120604230f0606010f03060305031605010f020a0512100e04030c05011a060910090f0807330c0c0b0d05090d020c0d030318080a0512160c080714100207020a 68
    0x181e50109400140c41a40407401590020302860031101003200d200007240038203511340c0060901d000008941456a040c1da2203c0502c502800007401004040b011410882c42840c006000182084c00f40d28401c660300c50035140c00c0045502c0821613203446415149a00d08250350403004500002d00300340c108442800f80022200402c52032602900d0b01070041031452159a0300036100b0715000300d242034a01d01034a07800c00a04400d0800690b05c4bc0c4803030816a580545000e42c42a9007040e007069005400b401041c041050010806500d03244041802511100d881c0c00007203522404400003c959500c241001e41100000c129004c03500342032407212503080c90307600580ba20031504a2031041c0d1041d141c4103214800e8940c1071400084212003014580c2441d00c480400038048000000c3c0c25002c6640f045c0a88004c0300c1503100304e00a6154850140e800380034588030380e00410f20711890080810030400103400d82c0e5004692000903001814143e505040d4801c00c0d108003e6030100d942c10640c2010040340340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 854922365 1250 854921115 854921183
    0xf12040c0608100605030a0621060513081605030d090602120708070207060f09030501240b2b090c03060e151b0304030c05010e03040e130b0f06120604 66
    0x2e50f400e2035041150b400009001e81e0042c0030001012510b005003d5209400070004c0d1035802229550920050703c201030184070030340b201c1d410130380070a428044110000c1c0c21242d11401c0c0d203240c41d013414240e0107a40340100044c0d0302c45c002444011903400740ca01600590320710a010040e0342d075013030070b0001c1124000608482c0400600f5400c11100980000d030450680707043e4240510701c0c5130212411201d207000c40c1c100070200d50820141402059403415804503440c132402c14800c2c2c15484a9403900c403800b0781a9200d81c0606c5490069079044000b05036400c064402c0800411626025100d07960900c12a43c821aa0503560f82401000c0d900306008040c94004030146001c000d043c500810100300c3e103001048409500300002240c2003601801d0074a01c0154400000e105680b56200c41c070362a608144200d0179207a280e44002150b40b03443c90304520125074450101800c1c6c1e00e508160300c2c3c008800a1034181c21100c42554a0000b44c401c10850384540d2040300c0d0141100c25030500d40e8002401030400d45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 854923615 1250 854922365 854922377
    0x50106030219180b0403050d0206130309090902040221090709020901090312020705120106180c080a05060f0d0804050f01050703090e04020d06020307031b0212040306050c0f12040c06 80
    0x6154001c2800c8001d140d4205403400c3e42d81200b840900d0380c62030aa65105640b0524001000000c02c003001c6542d44016a598003601c1c401c0c1d0b00c2c01603212001c1120040140010b86619003030041031020703841f426003140080c0c0018100354400000c580c251000032032125241a0000c04c11910920070004000034000c402c1c415030422090b00006004183d40307000003050882000c4545030341e1072080000781d0007880000d150810103000ca11740180200200c0c083c0e10711003c0c01d402c1080c0c0d038401c0303402101241c884559400c0d2040c1d0b41d05511a00500011308010b5000d600c0d140259a20b035030f0070140180080c00380c80182e0b40d40d072828003000401d1201d610110b05101091140c0404240c00002c404126601d101c40b2503060ba072030b031000400d10540120001c082510110510007820390541c0f104110704003a2946a5200325507a2085c0da9401c61040c0102240c0310421040c00040d94503040160800f20b007140103403c00205000b22111500200c0203241702d21119130400c400e0080c034608620050100341804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 854924865 1250 854923615 854923627
    0x4210c120e01051605012007030311030601050301090b010e0a080102040626220503120115210e070801061d010b0901020a061a1905040c0518010c03140a120501060302 73
    0x43d06034022000706144000c49a84084203000082d08140d80300c3c60b0400441c0800b12400380002c1994203c08030580000f481c0207020403400495000320b9010344816100c1500790313880c05a8a002502100590504201c0e01c84040007240d00c40000540280100034000358a0b503080c500001d01c0d43c2903030b90308854a100d102801c45d580e4445d80900765044900c2c4e06001c1400c0701c000011428045c40c0d118010304130b00c0006005c056070000707036031000d042c0c540607054581981c0c0c200100b222520400c082d007181d44080201c128134008525070005080010980654103183d684c2d011060845174070303030301400c02000e00c80344007004248020000c1d40900039100c90142000c00542c0002c0d95007074040001843c03543c2d07070000c0c0600c05c0b0b124017012038041002070a04504075804120100315a04038822a07010b1030034081e0420000307000f07400b62030740e07120340708503090700c91808800454101000781400c0c1c05118000c212a005000440c004141120342070701d44040e0780655030300802c12100143d1081003094814000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 854926115 1250 854924865 854924867
    0x4060912031b1b0b06030304120b0f0a091122090c050a05100c0201080a0207020927010b01020a0b07090803030708040c050a050612040219030f140d1704210c120e01 72
    0x842a401130300030441000300e684800c0030910314499500038015029401004c0b000700452041d5503486002d103036005514644480a071641501d030607000051885a100800ca81581404003e004a2140c4400c4070304043c031035017000c80e085501038202030721502c03140ca41c10300c0103007410514070008107400e031580413034540d0440c0018800864000003d04100a032008910754240580585800c80e0f0010142210781c105500501180301e00380802024649030fa12103000280d0040c455943c03401c40c1278028126422259036403da00719002031461043c0300d10400c0200d016001003010714807402c0e003600d440300242028209481c404a07164001e6106440760340c1c090149455030b0003901c911131949414502e02d6140c030b2000840b00141520401d03181d082c200800808c1c460a42680001039010382c0300c40c08083c043e043d03400e0b140d1004022840106c0c400c50445090750106e00d0105510a00405400c1c49040109050041c01c00341c5460b2000050311840c003802c2800509d01d9010045aa107007040c0a8050740100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 854927365 1250 854926115 854926157
    0x605090a060833041505060412080f070506040302060108070311010e0f120c040608030304020a06111c0504050907030519230106110f030f09060304060912031b 70
    0x280780810032a0800714625107407880d5203ca059034071000012042c1e0808540c080501c2d8480f5440d841542000c0c10401c604038280300310010703282c001d4172080c035017810401c1c84118000403000032118079104000001c941d0120501a00d0f9140c440e03805005103040c6030030000d20306201a040104130f034104250800001d00140c1c0701c1e1120860a09007206510100000641d948e89052911600800e009078a40c103202d00200b01c8a1f60584100c0b010040d00d51609003841e502d0000311002504264004001d110340d60160882503404200a0116003400d94451820503016082e03e9203070003c22000301b0300384124540003030996800100d5140c2013055140480c2011141400350703c108494643c0c40b24219030420070141d80c0005280120035444031541e480314001d24001c2320504200c014011403001019110300802206c10f46298121200c0c00d0900c0d8504100855201800840c0c0c4103903205c84c3d03500080d1054040382a10b0800743c84c00509031003282042c904d50382120406070104101d0031003407862644816 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 854928615 1250 854927365 854927369
    0x30a0e09070c0f03080604060b070b0403050702060720010e1008180a06020c0a030315140f130504060902030105180a060f02040807121a0601232b060605090a 69
    0x365654600d4440c06016180521240b6010340007080400401041c103401100f0180540c000f902c0401150356207510b4424036000d001e00040000e115540400e020900c1500601640c41c00281410700e04030b240d030344e112143d5440ca20380c0f84c006200d00c003440090350303081030102c1041034060700d80003904100c6450051446138020310004550041600c0041484d804000c1c0340c4516900100440d80c90009562180c4ea40c030350f00030308400190a01030100310011a81071041c0c11903100e0140754241442c44420030034000c2110901da600403a1800070142c50400724040c150080380500320004006039503006160941da0000c00c46040d030007030720300b508038084c60004145110303a800030030010b49500702c1c0042101a201d554468080c6114140001c01c4806c1100000d9480a1051900c00d01c00040002c044020060031039519000c90b001204008a40c0310101c181c038006543ca102c2b0350720380103480742500b909041101441c1408002c00600d004004803e22401014189606100b4144411140003c090309480c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 854929865 1250 854928615 854928619
    0x1109060603090d082502010501050f03031c0e030d390e040b0a03020d0b100621020d0b0a06120e03030112080d09020d080a0e0a050a0b090a0e1314030a0e 67
    0x540005a131444a0f00001780b80c444480c903080c11824807550300240a008203015461086600b0a401c05c030030f00d07000084070990140c00d201107080c05a19181031000b03210101d05c00410b80010170105609518502c20306140c1b01c041d030800d01c1404a29224002454200d280030203542140c84c001040c41c540164100701007800454021a0030000c60380400c2c602c0384161301c02034104001c500304900b04016404030034404c140c1b000e01044070755981c0c0070480c1e1012681c00c89490340018620012007458a5800801c2100260724004c1164150100415441f001580c4034000085104810354099a224090b40010003400d200942c11035051145250340c24003032800c02040c04800089001c00301c0e0442e0868172559400510380e6009618608042d0403581c0008040c00005002040042e4240f610011050590703070040d000585003806c00120f500c083c0d01c00001c465005840c00d0300000d1032542920510300c2101c24000d101100542841c0a81da005810303040d01030560410301c081a0030680c40300072810300c401c00b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 854931115 1250 854929865 854929877
    0x2010c082202030607030b03060903120f043e01140901260405150105090412031a03030f0d0533010903022d010c0b0a0c0207121109060603090d 63
    0x203241090712903620104402500b50103450300700504180c0641c8030700e8640c0303404c0d07043d20325658a503036905840b03108071010505465400000b05080c07581ca03e5885600601c140441c0841e0782003880c0e20060141c2e41451080881d0101071030100c80f030340040c414042c0e50700a081a04004090070180115070050310312490400c68030244840c0240105070956151441038820081e00c0e09240c1817954554942c008840040100341000240c0c80c148429250701c204c2e002840980075103a1f1b92400c0b0301030300c1c012080250342d500764101e140c0c07140c6d0144000c0c50301040480720503a82e5208464140280d5100a0102807082c0b40f503c4220f0017046000c803400d040c64500c0c4521400c200c600300044c0d40072221500040d401040042c0e08048000c016580702c2840d1044041f0000000701c0c00f401140c0c1c0c061a07000080044400c240400c002008903001003014031810300546652549890000f2130213440c0560076034001020141d46011820500351464020205807541403451825141644c1e0311080d981d000010440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 854932365 1250 854931115 854931151
    0x60f0403050702060403060207031d1008040c1d0a2d0c0201020d05041b08010c02032709090304180c0c030c020d061a010206090a050c090c360102010c08 67
    0xc4074004440415500510241d21a5200d040c25802500301c80f0007280800c013142100c07244041d0440500e1401d450042020202400a600840300c1100240c422075100300343d89000300300c08217101c188030303040a0a001c0c0c500103403602d807100205a440000780c0040c00802100c155000a1280207120702c010b0074400f0114a41c2072481089009104441c1c01d0205940350409100c1003148400480025580740300d081a251a02da240d90750803110b40100f59005030340200601c1c0c03c3c1e0f160610846459514684098180b480c07014041224010201c070140440d0304005414032080c0d0421090100f40c05000301c0801c042040780314054106131041c003010f0180443c944d248000c654600355080300d000d502160134000c5100010b21205001c1c0c0b2100f29a0142c000c03203000912950b0001440440650090f009044081a40040c0281210041d02c107149900b0100150029071703032080501510418850f51964000207190800701f00801102262411641048086140d15522030405a08698400200c5007001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 854933615 1250 854932365 854932367
    0x1c050a06060f0f0c0615060e030105011511190308100f0e01062d030b030706020c090c0a02071a07020f1804080c0708160920070b040609081b1608060f0403 68
    0x1461303051000380002e040c00507402c05d041d5109148802c44c0c8064450742d41c03504940702014240d5209000340b0450a0b0041d81d50b40c8241c0c41b0b5090025800f1090b010798410403000d5075146151610070000390040b6001c00706000d900c4502a4000c0010450403013569402d504141104882d00c4061103000100100b038101c000c01803110080080c000b0700d660440e0024219500c002802818602e0350f0184030303004035600010f020b0f00100300d40020400050045c9110399584c80d080f0110740164094608500c0f59040c0400c2074400c21802e1543d111154010a0b00d44a080c410041c40700c04104000b4014210354284101d070b20098502c40ea0440d83c4040d106484d070202d84a454070b4490b240e0702040c0311380b10703480f5010f021440b0aa00c10003aa00e05a27801c0c0010030402e01203001d0141076a0403600c090b0b800b0015900420180d0251a422a03c904c802003104015034640d0300c02234024210721040212440381a510969041002c1c180d406a4600c09021062a10105a4841c400101410a00148180010101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 854934865 1250 854933615 854933627
    0x80a0b13060e0d0f03150f030f03050f1809010b0f0703031a030d20060103051b01020c040e01020c1c0f03051306050106090602070504060e0424021c050a06060f0f 71
    0x591007042c11a0a071501c03e24008008441500c84100443c0c42c240c4804150070100746c000c81581c11804100c0c0346946580c0c0ca0200400e01500c0517410410240448040b0b0724214009020722000034903001d200e50440d90800444c1e00d0103a0200c15101300800500040c04446000d0311038258140c203000400320b91112003105100b0400070403e81c5070086641111030590041100c2d54668140d40c006c92a004c541404555650000e02026290340d00c0780c6400d0541c1100368003101a095010301c16220102c2420b00030406980050204d5810350b5004142411040c03410001031014030640d04003141000d054100150005048080706000c15440b80006a8051401350354080d80741c0e0701000801496179255401489500c4038080c0c08018042da00c1c0c001010320301400b88100741c4c0d0380c99640724143d48490751502d4403811411419080510a40e0390510300d42560f102501280c0c9103004100e01040028960a0455000030000818145080c3c0288a82680142c2c500020b0445040184480303507108030581e15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 854936115 1250 854934865 854934881
    0x228030203030c01020d0b0a06020307120e03030409060503010b010c02090a0f0207021203133312060f0f060c170903030d0501060309110103021206090a0204120803060901080a0b1306 80
    0x5100003e29000800415402000184000341c010000ca8a4102c104034007407d5510803580103900a004100210b0410340c015244242c06081c601c018400c0c400210f802c0d80c101d54402034205641308000c000d14202806005980d003401d180c084840001c60f40050304c02d41c00a071110403115565031079202001c0c0207030b04980030580c00400805100ba0b466a41f55a00d030302c2202e502c0c00301408000005140b06000c44e4841c940740040990941481412400801403881c0114900c02c02c90f56401955801c200c0f80301d403101522003824500e280900300284042484865800300041080e01131003503010852072000e9107041c0c825851250b40d58660709001920750b025100420004a14220000455a0301944580000d0744a120b40ca000000d405c4d005401324050411500c15031861500020300619150780501d42c04600c01380014201626101491940d844450382100d41900010500ca8607103071066603207005010000046c100300c2080ea503200c62030741c405010072144d84041012001041010340100c50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 854937365 1250 854936115 854936119
    0xe1e0411060c071e120305090402300414030f0f090a051c0302011d030a1440181107141005070801080c19030c0b04060f02010902280302 60
    0x54507446214007a00c00f1004084c220984031030707050000381d4041003200c40311015015200c407400c080c229418000a540b1259841000174900300925400720010608820700a519483d601c82034640b5150501d810f00d5001c01c804880d900c207000a001d0310720110212114401c03486405601c0704031142c007051030b40103650882903001c03502520200c6024524002c2410080c0294000d105803555031000499605203401e0034041900700b000310801e0a4002c4078019400d081d0320340601d14203050f0903824000c004941070000d075280381800010a0b1081403420b0440c1c512005e070620020145800c1d58104110b90000c440a071468032103810700740903d40c0005443c031b40c81d00a086c65100d081e239600340740d031a00c41c03040ca141c0c815031401c4c003c04d0b1528480d800142c180c4420600416a40a000080002c40711b034190444014004850000c000124014500c100904400203d1501c403410b2860103040702450350018411a0700d001d0164000d0f0f130380c01c030103c009080c0418900004404030b0513114074203012500065 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 854938615 1250 854937365 854937373
    0x150f03090d08061806040c140c0a02180907060f2c0306130203191506060903020a080607020d05091216090e0c0312220303090e1e0411060c 61
    0x10010040201e0903105428607030ba40c8040d981e507502c0030014020b60814429a402001c100010114241070b40701b81e0b6561a10b041185410380070000e800d42c0c540c800198949183c100b07207030346001c600f414140801c41e1008000b051103140b92540c0c0269452042e445883d00701b140706029483d509024111083c440d182c5202e4900c1c1c103071701d0b042e01800340609884185010748180c80c0040c185c0310420754a00c03040307a402000f0340b00c0076019004038041460034003401e45034400c1104d40b400c98030407903100b040020603640e115860041e2450041041e4080d25902821640d08038804214040340d0100d000e10f1210070038102a030f2034010402c0070400014401e40804020b10030108091082c1c424011002d08070f4152000910155402c0f9403a1500c4000001209405d83c2c444a9160100141c24000d400d1190b20303920122603040141850307903004a1303a075006a010654014083c401b045031041003640c4091031888a0421080340c2c001190440790007080a40020a071031102000c1e9a02c400131641e969036108129 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 854939865 1250 854938615 854938621
    0xa09080d021501090504020307030312060e04060b0a08030f040e15120f0c0103110f07060b0a150e011e120f06080106050a060e03060a0f02070804090207030201060603051005150f03 79
    0x1940d10b040640c10001030010740400010200518001c442c03040d03a0140c003800c801ea00c1c5580503141c1030703aa418410070490300d03000c0108100424064451045000c0e90b008540380901e4002d020420415400284560b0004c0140061015048080700d040300d00c40f0054203120340d41e031140f401d085c0101c2c400c0c85511461095403106c00b20340c0050608103020243c2d0075102040e60000040d07080350001012158a14414030a540c0201d209902810302c2a01403d400704040c3e060310006200200290045215480458030b04000a6401880f08070315400038200800d80702c8000c180b0313011000802841c2410448160303e243c08044054109003480c5044240520003181c86030500340c0641614054140038401d0b06000041c020b2041c00700c0440c41c00050701505550b01c9000b8003001078001d2913540001f041e02041a070300061813001c001c3c00240104400185c88400b1460001c0c00d482c402d40c0304030205400e00c41070140b55000c4400c101c08441003114200c402840a01262580307004654068003400008020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 854941115 1250 854939865 854939867
    0x91501031e050618071413030203010c020f06011e050906190611150717040602280e040605091503010e19051612120c020405150315010510050a09080d 66
    0x1c5008500c02c451084c0d85a0301d00d080744400100442d0710400107194070b80550642c180e140001d00340c00f4400e48030b80756650b4498000c80e0a40300d00110890043e405404080c800b0340007030081d00c0c050010901c18101e40503500c0d0fa140c5001588e4010741c2d200d549000c010a44031b03502c0741c1c510144002078582268a550780c810000d0710751024500184003500a0145001c08100350146152098071240c499002d20052600354804405005004072611903003005404100004880c3c4072410440c541e104900351200b045008007042d8601d011940203d0503d2801d1203650b035080102903004585000c0406503080d03000009c0c2c007420514240c000503014480c00c0b0003501c03a94a0008001c40d0040c01100c0344289030501c0702982144901c903854004a20074081000105084a4242c40b88411300d0a49084031070b036000901140c400741d075055050840c40f00c041809040038810008100d0707a90941c844198502404140640c1d080c500a204010000903021007550182c1d00000140150b03d0407203400c45a4954 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 854942365 1250 854941115 854941121
    0x312020d09150c0908030715050702030705100f0b010c0b0601080a180c06020d020f060106080a02070506090109120309030e0405100b030f07030f0c200708010c02011a0a05091501031e 80
    0x2900ca0014691300ca0204003050000704a070301d055070042400714800415961100101405031040b021804100070103030102d101000041400040180b000844086243c00c150848410044181c14030a08011420204d0415000c0301c0d448507081c200035006503214000d06d0010459000d068020141055085060042c40c20b449400d881da19001c0b500040007000c0c061781e2740c503180c0744064034683c080c80040c080d49e84a102140d400044910000d4100b000540d6064141380080701c40d0050b582d96000c0c2c11041c01070480d50001c02c004541000c0080b81007584004110403401c50006005a0704d800c04100d86110b000c18100041c0540c60354a9100d00300a040b900c941c050550b000c10000741001001111040203200d078a040d031200c0d490340300c01c00030010f00d200504402c40029040500070400d00040c24242800b07000b0725482c1a41c00010818401c9072809080813410149038010b03440540c09001c82c0c0c0320f0071900754001e90000c400030351036141729004030301403c0c100d040c0040b203120343d440458029200360 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 854943615 1250 854942365 854942381
    0xf120a020307240e03010b1f14181e03010606080a1506090527090313080c0a23150c0c010305060f040c02120c030a14070312020d0915 59
    0x5094440b11561281d1608803c0071100310b180440d40b400181c1860203016030910980710b103028001003855404600010742c0d80180c4d4040103002c0c0c2c030b030300341250140e94009c0303140c480a41c0d9645180e003004030601903488086c90341a0000c1c0510703000d0800d003855450341a640e20207070100070000e102481e1039410082200e001030325034074969401d000c030314107401403240c294800340c49aa41d03500f5403281c5048100080719011034045099007401811052152010074802882220604011075803200007101080c03051344d1b00c3d4040c039150780000030303589030b81e50b14014198100c6103050540000d0340101c40803402002403144180d644401d540e9040105c028205020b042030524081c1505c244090401c01074082d1001250440c0e440109820f03114071515041e07004140d2400b092041300e20594a007a880d00340356100c0c060100e0070303910104401c01015071088036160907007a6000c5243c10414207a40107000443c00200d04441a900817505a44806140d031140049070342080300d031502c02814621920040c41c0103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 854944865 1250 854943615 854943619
    0xe1b0d140102030c12070e010c0b070c0c06020d020c062a0f011401090c0503150919092d0b01091e0c09050a0b0f1b07080a0303020306011d03030a08060f120a02 70
    0xd0000364058014040003091f8681a141d22803485060790701c410349450001c182c0c1040c4101c0b0440400454076841c00d8601410280d0004d040c40444903d020f0b15050075240194030500301000071800c2960ba00841a0b02c1100d220031000f41c2c8604107503071031708114007005c2c036100740d40c03800000a000c2d243c0203001e94101d90752103800700900d96a00408031410320040350800d0181d000f4240450242c1800458950300141c00c10910020060403d1088182c99800e80240c80000a072045500a91140400e2681e40c8041d03038a40101d85002e566810400d500c14818001040ea8030b86004004c00c0301082c90102d881500c1c4001c01420348a4000644650450302580d405005c28180100c0c60141400c1240c41c82555100c1140c18214281881c41940f5130821151005014034100001e01c204100a4403004070320035200943c5a01d4440300040003610342d50841c1007084180e01164003281c401004440264a040c502081c0710340c0d4a50218907d4098035800c140c016494800000c4148404134812090703d02c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 854946115 1250 854944865 854944897
    0x1c091b1401030e1b1f0503180604030207180207020909060901050705030c0711030312040c090e12190201090210030f050906070905060307030f060909060e1b0d140102030c 75
    0xe40c0340110210390100110101e00e92010004207034100c40c42443c4001c3d0701c07008015100034040100c0b049400d5580e81d03090800315030003005001c000008141101a401d0000380104981d00e0140c500964a40d034610a5240194443c403c00c149405980c049030340b1507802400240b0a0f09000c01400c0d620641220415019480d0170003042400744201c1c110703401910301d548000e00b0b02c416074072001403030702c00d44090781c3d4907100400c0001110703446820401d101d2405010003003182c616201c400002e80c1c0e0703c1710800103550081c0c07034142c00c040b4000040d100405404080009202030038101030340108860480a58000880c00f02c1c0d0000c031740c0c1500200308200006805004130740720807000341e42c0c0d48000c2c1c40c2100414601c042c14011410000060744d0300c0159440c01203051a039807200c05045542d075800488400361205504020301110f405102c0c00104030704000c094031081c0c0c0c0c03403d4810508008410340300f44103c0f540034080c000c14103104014540140021540d0341081c80102d00c403684045078040c60869 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 854947365 1250 854946115 854946149
    0x70522140f03070b16060c0c120f05070303091401050f1806010b0a050c07090f0f0b090f19110f09010e030708030a0f0c1b05030c06040b1c091b 63
    0x201884001c0c64800090000e00180d0b041c110714003080e030861168080c00960f0030f040e540104d40d0600a00100150b240c40381e141c010010b08000b401c10b4001c02480c01400fa9010b5034010b159840f10880b4556a054a00002c0c148803071710307002c141c0190760804c1d01d840350708100602130006c0340e180c2d40074080c5201c00e0414012022803044c0d40e41b902400d00c80c0651313a443c1030080c459520f0080f0000c14110741900161441c039a00d542c44503040f1032443c103295a6095448141c0a003070100c42c41507280c3c2004c126200715861030101d001c0300c04003200900300c4400b100704107202c10b2a007642e0b0b00400d440f40548420103403501c0003070410103840d80240c00e10341e0014400300300d0a245418049022021346030b102000d103260800055003070394035810401040003000411a4540c02042d8a200a0b0b00207070340342c0c1410501079180c4000c0520300702c00845d265200319010041081211980000c44409500000c404054000382513000d00050000b0352003e08000d078003032420300307891b0070404e0840700b9214240c2055620342 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 854948615 1250 854947365 854947369
    0x306021314150708070c2d270e010b03100b09010504020702060f1e041502010b030303240315091c02010902060a03150b0c01020406030e0a0f080307052214 68
    0x3502c0149141c2c1503007000301c0d2002c0f501c1c3d1801080d0040c012565203d0003560354a024030380286644c0c100200c101580ca007058007107503803c003040003040594122841d20707040b6128841c4184414511041c40ea6070317008400b400340403e400c0003201050080903074004c007074000760b01d9001d001d101301c030584a42c05010001c100e503d0980b0a50301c9464010b04024103060807400301c0c00a9034004184c6000300d280100800d40e060058400510141441c0898802d0b021040300e000303030a448103249000e120703800610810180b40034081340c00c80240407005108410003540e10101c2e080804540030741c0d59481c107120070441c0200c00081c820100d00b0f014001082501490300d003c90032200001002944414100000790310b00d48280c000070001c0030f103410340d410015543c5900041c15440250700d6100c50350003081c02c108103505403041e0300c00d400a80010b059a1460796680c4290041102130050001030080007081c041886001079a04c4030340b00c10422003200010309105078504030a4400c280c50300d4003a9159500340c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 854949865 1250 854948615 854948629
    0x906021602030c100f08130f080d05090f0c04111b150a05010302090a0e190605090f03070b0a150807030606050a14031f0e1605011403040b0c0d02040306021314 70
    0x204046030380301040c04003005c10840c0c00000144c40d4040c2031181466490100d00040b0360b01900502c0b44950790b640d204680402e40540302c0041070140c190300004009030308078a0104201c40e000c0011540000d42c00840070440c0c0141c01841d542074185c181c0c0d42d0041807034010000340d402518802c01c0051b400c40d0703a68045081a64024023009401400c503c0101d482500c0b0364100700000c488080c00d50340c41000c40b07081410010b100c00c1042d80c03110307115001e1100c82e84060100081c10b8216001451034000d05403600d4560380c1d009411400c9981c0c0e07605412002031000307059940a00104000e44500541e0b034103100b000380c0300a0040724403030100c0d818000703000714010035894500c0341c014015090030a403041c41801e0318441c000b000c0b400b09440d50280d14140a05100103010255400351400c909403d1000041510b02c80000510003500c0400078007020403050040301e81d00c50185054140d448000c0c40b141e03c00303402036920080c8118004540b440c84e160902d050038013561580320344403151814020401440c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 854951115 1250 854949865 854949889
    0x5090a03141e1f1d03030a05010e06040c20011404030210050a020901020a170f040b0417010b030601123f020c0a0b1e12150406270906021602030c 64
    0x55500540c54003e01002c0c0e801086407002402c0e1080c541e00f05688000c0e0460384200c404416065664005001900c0d0242c070a0342c004c00140c2c1c04110001e002c8001822041a030f1004040c4070003040020110340d40c0c01d40140c3c0c5103140c202e000300300c103040c50301d00a50740300c0030100d070110200d04003000502c7d030000754030a072503009030168003c100c07103915030710b40100e4064045596144c11204004200000c06d660380140021304003200702035a034602d800210220089030f40c1507100750780d06280d0400e515550018001d41074407191285950484240d06d0b00268500c0f030600015000842c1c258120903601c0700e02407205494260000c20090901082800c03611503840e44546940208c01c40400e1204003030440241810307800e203195110200c180c003807500381c0b203401c01401c4210080b1210308110301142c200f05184a01042640c0602c005400c2401c1904d03203541c0480210001414103240081e4451190024242e8a4100038115aa0610700150310207a808d0701105034084d224a23620056241030040400070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 854952365 1250 854951115 854951143
    0xa15020136050f07062d050f031012030903110d120f02010b040608030421020913030c0f03030b180129130e180313050105090a03141e 59
    0x100894880d0491101d8110103206a82c1485003118035510075a081002001030005615000c0f06000c107a4651003144c8042d00746181d051412502c0c908459030400c05450390001c500007103e443e940e504003490007900c4581e0160703c07804810180c140c140742d0130022810030790b070280f03198800740c100315014044c00780301c1d8400c0245030b000c03244102a54940f1400e100f5501014910000c41c0007190100041d06a62a42e0030205168000041c1003069085a078004107010742c111f11610342d0081203800003600410020300c1c1c0e41c0d06940010900c070030944125858000c550717000318001400c4c8054203000700207040c903528441c02080b007207854400e04103a445c40d4034101c804204918029900e1650400030002c298107020b4201c0318180648460101c0e1020f9010142503510104d0f60246455801c0064541040c0090101a0000c0081d108181c600300c0e244030503110203003021a81d5009a50100e041d4480e250300180c0076002004004126160201d0700708010001c00ca0550310220b0002c3c000d648079591820180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 854953615 1250 854952365 854952431
    0x618070e090a111c270201140403060e0a0b0612030301030210090e010e070e060405060901030b0109080f10050f0f39090102011b020a060902030c0a150201 68
    0x1041032500c0030318664800510b14020034142001412410310b90420b102c1a40051655205542c11a400c0e1086004c03030000610070400e80d0154911501041d05030a00103410841000f1000344c0e85401c0790220303001943e0100041142c42e44c142c0c1038030784401c1e040c00b040301c583d000c40c00442c1551030300d214049a195413071006140b540c1d20f59401c000b240c0c1d41451032a81800080d40000030200c000380c11640c02011812401c1500c0d01e0000c9008001c0310b03601d8420762151105010901240d140c0b8000c2c0c800002003800c0c002642403941c0016503020780103034015110342c85107031030b5404114800310350201c0056600d001480140c9410420704c2c101d000880310f01615424650000d00301c408881080c0410310203032014045003140382130b2682d440c000070189400784500c3c0010080c0072940d09118210b1428640620904400d141400080d01c0c3d80c030b405000b90865450b0300000e019541c0070300042c11540b0000300303414006540c442000b88040c00000200c0050352910040010a1810391700c448c2a990500030b0310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 854954865 1250 854953615 854953637
    0x9030607020303071d1816030506060a120507020f070602030703090e0603063421060b0d09020105120906061306050609091e040305220e0c07080705010204030b061807 73
    0x7002100209075106d602204111036940c00f91041d03c481e1740035038140e14004288158200001e01510000f5000d5170081800300303c101c400e0380d8807044440d0b80a407034071004101034488040c12481d1081c88000c11186001300c200029120390000014060b83e403094903007040459503599003124140c1e0450720035401d604810006009440d01030080007803040c0c0e014541e07240c40303411960f2001c08014800c008021030310680000a852444080071030b031000301c0c51400d111280c2000301d00039003800f0b85040c40b242240c880c100e2408681c001d10070380d01140d10381e0006030722518016040e07a0f55410213850944c010786991a441a544542e40240402d03104040c10710b610700081c1d901030002c0441d009140c1802922156002001500111019400b49019986054907540c1118a90420030214400b405018603c2d00041241100841102d58401e10b040030094442c0c0c081d04140101e072080d000000c0c40d07944002400f008008044025602a542c1503580070320400071810100d8144000b0389035003000c15040d0b244 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 854956115 1250 854954865 854954897
    0x8030d02070305071407170a030c0314040b030c03070f0c170304020103110309010606180302030604022812031b02010e041a040609050411091909030e0a06050903060702030307 77
    0x81c0390291007440c0c50341c80c0c4000c644a4080104218401d1102c1c0d4001d1103003001045108180008014544800b400e0044000c0e81c01070140401500300400784140001040141910a010303100202a0200819564901501010706960003150160081901c0c40350161fa15403040c0412200a40d0101e14610089202981c03016580c2004008034101510b40075007660080d111005103005545030000400e607941421405403181f20100c0e0303d0001c940842404001607030f0002403c507000354056503880d6420b039292200400d02e6001848050b41c120307492400080b40d0071603061030425107002e9aa07400288030181400b14807800e0840c2c02a000480886002d0740929159104482800500040803c031403020b4010034103464440d03005520259480c401c00050107050281c0b21103013036080715150f403a803034544004803030343c40b2000020004035510700800d03003014040c551800720744c00c000708062141d59403404000c1150384182c00e02c501038018100810002c900010940c0e020740c00f07a40722800b409666260f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 854957365 1250 854956115 854956117
    0xa1104051e040908070501051b0c0705060309120316180b0f1602040f090312020f031306060806161101060e06190306090308090607091206020a23130602060108030d02 73
    0x10000758003a580f503401c0b000040e070b504000c2402a218100101d22440c0003c1a0b0800e00d03001b040f02da4009400f00400d01e0034080105011094038011252240c80392035600a0f03c0c43c0000c503603a15180f0300000400e1001e110707070741400c01022110303a070350f54051200d0150144144111521070900588418488546074100360700150154041084940f041b80f41181c00140c19580310381d012281d01c51703954603500249648480e01d00200c00e08100f0035498070b4004400500c852000604041d104c88065011f00201f11a17a00840000d1420310103c0e00d040c2405112010203d014480010104860012507504d407141802010129002d00c426030065540790f01c28072065084454a41d5040702e012040400000d006114000f40c2034002d03520408646031100c4070030328040001d031030b42082c803040d01e07020030560201100b458080f541c4000c001d07841e40d040004c1a1240210850a0140003440103070131105d1001d01c0d00039040d10800c04540400d450b42c1c4000690702c0d5a02801803514940042007640c0562046070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 854958615 1250 854957365 854957419
    0x9020c0c101106042a030206030406020304081204150507020c03060c0a1101050a0b0a270f11070605061f0503010b130506070c052407020f0103060503030c01050a110405 74
    0x400c0800c09490b081c00b40d541010001c5508035001100291407880002d0480080780c0215800c0000100702802c0d80c00050035400002c0c03000340296000800502005180801e41c3e1004c03070400102d0815003000e14140300742241c2e04100d86c0301c9c145000d0010f1101440040e2200b512000070300a1711880c0c079800e91072540c550183da0f062061000e0b24400b400e44007401d02c681e034032441e02c2c1800050461581000c00c4030740a0264070802820245002c48182c00c0e44035000842021070740740000946540344550400504502c181c2c150a0782c0d404501c040901c0f0345074200c544614001c1300c04d406085510f0b0010007651648803800c9001400500061007015882801402240c2e180c00d80141c003e07650b50002016544a4032084681400303d107400c10060a21920842a518212040051125800c0c508042703a0150b040701030b03c1200b210b14014201e90080d44007801522010b000e44e0799410002c410300d40601070580b04100c2c094501081000608040005c2d141035550050000784402810950703521409495 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 854959865 1250 854958615 854958617
    0x3030f031549230d02030f031e070201140c0a0509010809010609090c0306060f060509010f09051e0a15200f071d060316060c0501150b070b0109020c0c10 67
    0x4007142c0000c0c280809419290644038042d442025a8411245407010010078a0b00381d165004540c6900e10030380110a40b04d4440103c0d84407520784d6202a154051041080c451548182c1c0311400d0006096041d04080b0f0124501c4102c4406500d440b100405188285102c9030000703001400003000540c403400b542d9400220840c00440c0c80c546440e001c40c05c0f620102c40c100e03412400030508004101c0c0134041c3c1c0c4000c0410003580c0104524000f400745c090b110f8032480504200101e2440c030b0380140107241c000081e04014208504404001410b40d2001020308119441411180000600d00d80002c404018660080d030f80d0502c110b26080105544021601001c9010300032052064250001001b90000902154050300000304a003002b0598484001d4000c6000780c00c00f02060024011404100049414526040810030707200c1c2410b60040030070207400c41d01400e4070140090304a0300040a4500c40d4020f080b1360201d40daa40041d24103d1080c040032600c02d401800428407689420780c4004503448031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 854961115 1250 854959865 854959969
    0x1119050309010c020a0e180d080f04110d1202060106020705040506060a11070e19060e060f06131e1719060911100915020f060a0b01020c03030f0315 65
    0x6e44507021038100301110b40c152444100340c080d042042c8208035109040400c1c0c10014864201024104070446000b40080c16011089901c1c4869450741c00300c600817141c100405010000c42228000e440d02800c3c424800117108014011541e07181a118490040c840104054645609100d0031355a240080c460825a0b0107102c40005040d5410031009101e00d03030311312140e8000d900c13421075507040320010b03040004000094020010306031180d180001c00702c0000c407041521145100205210800207403c12011056144485402c507146c40c0004030a80e2410807500c540b01c107540c60095614410003000c00c003106840b01da2400070036201c1d805a580a80580300c6600c846032040040303400410b0b5085c000001800e003c03010080a1902503541d070051240d480602101c01303907048110364400024081d24085a6104202c0314181c0c002c206100c079400700901074039121202028a140d55802c1103a071825003010008000445250030740203010075000b106800060741407013040d4109540d10b9180e82451002c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 854962365 1250 854961115 854961119
    0x6040621080c030706021c020408100902060910020f06160c17090a1d060a15080603070e040c1815030b0604090c2909010e010804110d031119050309010c020a 69
    0x4018402826a13602402c00941d440718854050454602c581c3c003280405803060005020720140480d207611400319a1102027551107481c0006a15031140c2039140d98044a2143c140319000d4010032030140a03040501510303c25a154a8202c40212083c8414000070305000501000908085c2c080c03024210610440d504041c80c034408111001500d8000341d2040c48900e141c0104000403407400c5900c0302c1c040d101c0c2e143d82460260141c00300300003420004144204140020b82076101004a040102902140850130b41130500340609140d16901603030759a015131155900e401c041d580280c01c3c48000240d0318081e0a8a107890741c0700c0f602c00243c0040d501c5030b2648002d0022462452500c4041c107000141c1e1486090b99140d038602c00030000c0c14440a1308001d0003030004584c1c201c005503005040c2820140300075551840c1072410044c19a08003035000c451100c1031800d1650003003603a03c00145131801c82d1850134103240e03035038540404254003c04950003041001c0c1594400c440d45c0150b58805820b00701119 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 854963615 1250 854962365 854962387
    0x30606101e0306090e010e071406070602070602072a0b07081c0b12060f01090b06040312030203060906031f020f04090f0f05060d1230050106080604062108 68
    0x140d454000700000d895500520043c1c181d8815400e402c071300711000300400603c0c1040a600c407003c0c0d109000760400485800c04064a50008950580b98000000c640d0f903000c0c5d1900030003e410680c0c0c2612001c0720408101e00e000c0040c11130a480b44a0a452022554505a4841255032100380c08a4410109001c400d500d80802850b840002e00c4514011540406000910201a501d80b5086910341e02c03480074001c5000440036400d0640d40d540f480401c9a10340000410114812640002c4c90071820341c06001c0300c0d940c1980039501070304084541c50300c01d8941c0340802d5030340c080c035640742149400e4270b003440401c0156a41c014034520951051540c1003030b0f81c40f40c0e10340464021050000003580c58030001c01c204481485520b520150445044080c5695619000c00700e10004c04110180b042d10800038045a100c03144003444c01208181d01e140c071002899602c400381c6428403525020030311101c04665189014068030041d6004c174604070444400c0c0b10354116000e03c0e200016a860001080344c402c2c44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 854964865 1250 854963615 854963657
    0x603061315150e061b0f0a080c06060604050310150f08030c10020c0706180e0411010809010203160c0c050901030506010e130f1113050901090311060603060610 70
    0x440c1c030208002404500c0c21400c520700158019100c03041241c400a00c021070707518030003a60500e00d10844100d101001c4081c06514010001680001511410120b8020042000c000f4814001d0b200c041e552182c54a205000c6540510b000349a85a04009140300000c1c2003a841140001403204071a0101e9030f41d0140706103880e019410400003504001900c0754801810401105c400981c031200310f2601700c0030544c0c0ea86841c07850080c40100b02c4010b400c000d20000c19074508019002001c01203007076041c1413078a90125501f00031070601044061001480b400010310030741e4407418500c034400030407080489040391400da014004581c80030801d10049141d071202c0d0540f0f170103188100014445541482112241043c0044c21414800c40f104201000a08205c80312034100d64020100c1d0541d00520303001030310301181c10521111851138201000000001504215126802500e40c0601c2d05121a8505d881d040e0803140c080e0154403600c0030400c2c90500b0010340040c40b0703c0c3e00d451402c227090140c4900207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 854966115 1250 854964865 854964881
    0x180312010303031a0603070c2105030f04060b04020f0910030510050f03071e210807080c101e0b0a080c2709011b08090d05032205070f0e0903030606030613 68
    0x60140c200d1042008000b072044440f601d201c021500e1300c002112700041051000500b0018a0b216520108007080720360f810195801000070019510384482507400e00c01074005602c624804e5681c07d00105095009110b8580035200810b0410f01c840c1c2800309109844000c90100c035010300c2580d20010f4201503a4080d0061401a446c18282e510b280134405840751581c910290714200065000f43c0024a1010403110440d42c4007501503221408251000e091034041407200300400d00b001e10140c442d00c103200423122403d60031042003150031090424405002000d00504649500140b5020340384e2500020390a00743c0b55000890301c3d14824241800e50044003a29078040b142e44400045005a40140174501c0c041401d103054075851908240459a0b422001da025003401070000c0842d40342c95001d8151b80150407003540034028141946000c9075692520720410b130320310314100c001013003a240c8504c0e05802420032900540c2107440740380030060349510140c00740d41d00840304030700041d5801c014064024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 854967365 1250 854966115 854966117
    0x20f071a0406060501050c1b0a0314100c05040515130b07050a210203070b180706202a01030b040504030f11030c0d080417030906180312010303031a060307 68
    0x409401e0526207078040d10000c1d00540d050210071704c0303902c0318900c0000b4a00355403440c10b003000240301e0090011440c0103515400107444201c407060104881e403000640301d030046c0c5030300c001084012260310003120302d40694011075621407a103203585124001400060b0a4810010704070345103081e9298284420741d40420412a00394105045181c1444a4890241100c2d94030341500b1252841c0c440000b9128818914000d00c4815a031000ca0000b070110b68201036003101b2213007281c040a456550190005010f00e2003034406d2021820200c283c1040820302c107600d100c804070100085424820542103070200411107904141d0303103a00b01e0503d6075441c02594001d034040d440700c26290034031410051000c5503003c00c250542d4020000340306002400164105564550f240c00310323068078ad0340b404022503c60780710b00c0300308140003000784200d600000c5495401000c03200070985c5032903a100401601c0f8020884034110000300e05004002090003a0000b0200760b203d0f450084030800140d0010705141c0003641c0200c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 854968615 1250 854967365 854967413
    0x905010303110c0406050112020309100f02040905090c0901180f060303120b040b1c1a0a0e070e0c0d0f0b030a0b01060e0d0206180d05010e030702090c0901020c04020f07 74
    0x140342c100e0600124070721140036241440450b09050010700180d00000a4448460b400000205005424000c00802800d049018001c00c082da1400001a400600803800035525200c0031400c0c0032000100c0031031100c80504004880d07840e0804812008610036011804a0f407108d0b20411107000c1c6200340780156100ea1906c5050442c0e5090f0fa03002ca82c00361140314000c525141e201903644d0382d178941e030b14550880c01c00d0049007841e04d4900042881d030a071510404c019000424003010200070f4000b0403d504042048408140c0e85621442005600343d50741c1c0300051003001550b44420458000d4241c09044800c04140c81d04440d010a00c0d0218558080d10300c0120040180100c582c05a03140303840100c1115940c420300f000f074000429605c030790480e020711146012654605601d44c1c044072a409070b0020000c0003c0710100b400d0390707201e40c001d0348100d1207001640002078070300b00c00340b00791380c50100180e004200c4907001e001400000d601030b504100c0701c40c0084c02841c0000e07020450020710360080700801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 854969865 1250 854968615 854968637
    0x1b0b0c030301170a240f060f03050127030e010e060a0905040c03020c0322050a060201050702060c04030f03081f090f0605010201060501122a080906070906090303080405070905010303 80
    0xf80760480700c0c040c01001500314201850210f00034251004c0508515040c5071503422444280c1002408540003114085081c494006510741c2220102c00449e40100c00a00200c580c03021062409203494616110b640400350070038000c0b911510382221041010b0410b0500100074600061440e0000ca80c0d040000e00420000d202a0505000d4400f1704c1c1c11a0034154240f07400c920041e5282d00424024401d41e449841040402c1c3c0707202c0d82600300406020340140d00035030321444001d010b4202143d0703201c0548100f1010030810326040d4200c0d01100c0c2c2000d1300c21040e40090381c040701c05060250101c804032251020080c400303a203001f2070000030000b41d1400a84201c5074070103001611140d501030b5046da413415a0412403030360801203007007510300042400184600c5104808603210702c0da440301404001c100f0801d020568100500e00d010782503035411912281d545c68021a0401c1487c040d0a00054106204000003406058103640192081c01954082034031808cc42085070001d83c004d4001030416141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 854971115 1250 854969865 854969879
    0x13030203090d080712020316080f043219030b130b090a0506010f0e0105090717010f030b0901203f010905060604060509031c20070302030a1b0b0c030301 67
    0x6075a4617407600f400558100700c00252100c210340d51603100680080b03400100260786080703410407a0f02610003030380b00c1d22803881942120035000c003105007061501107074013031018854640815118041285d21641981507401c60f0b40b42c441042001e00300004190840c025200040c1e00ca01d1010321400000b001011515660300b4400d180c030708103a012201000c04620148103e100c46401181514819103602806e070b12006812188120b84050380c940f1500f07080b0022a011000c21007082c2201d010740c1000d500303078a031060031f1802c0b1011310026031940c8500b0340c1d071000c40b403998001620405004104e0004151140e491200710002c03560b01e181070003070600b100d00c80241203800c080e40c050001ca600811091a00b000400c0080c0319500502040c0240803d03100c007507a804002e015081c109400c000c900030800c1e00300c00342800c1741803911951301650ba0110f100207040c0001e107803821260010002c240b030202d1511104096140d103600450403813808007022418640c0c0c1002020480310281c02107036290b1600306 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 854972365 1250 854971115 854971133
    0xa0201150b0a1715040c0903050a0803010509070516030311040b0c06011d010f0b071415040510020f030f0606040b04140415050906010807020c0d0807210813030203090d0807 76
    0x1d820740c80145000340040181c242d45413410356002610300143d101034111042d40e6441003035100420038458400d0034004c002888000c3d50403114140c0316024a516600d206464500503040c02140843c400810213010a2003500680c0380d4000010041e8074054560040382480d030f0121190b14601e901141c0100009100080c1d800c4e040d81d03199210300c07840e50411840c0100c0d615a0311a1030400c0c6004504102400080024101074554581c219a000601304007031711300818084606444500452144880c903024038001c4410302c2503059441031440d07441c8110b40500701c00151007580c00000c140004140340c486507000b40064071802424005024a4004100c2a9507080160314420201100c0810803a110080650380080b0242000d08039a0380342e130000c030300e0910015003055011909030500320611040200030800c071401160080000108040800c0c91201c25900401c0000e28100c0050590341e115103d400d1414030920550f4604510320000800710000c2410965289030f0000c1d00d9420004126 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 854973615 1250 854972365 854972387
    0x30a060614040b100e0316080a0b0906090c01120e12041406040e130620091302030c0702010c030c0f03031e06030b060f030a0b01080601031e020607080a0201150b0a 72
    0x2c60a01c081000240420143d6a201e10040c0034401c400404401c5607809010008421920180318810281e0340d00c0000d03074405065009403001ea0146001c98120341000ca0000d101c0e00c000d0b4010310000d450308004407140d512400c0217040443d69051800b88291051242ca88022440c44609856030b040003800007031910018002403142c3d03010001044680c000c07604280d030110603488003e9440c012403c0680c00350484100c50004000c200b07400302403d444440c00343c00d4101e420754401d4082028816108120300c82914041910707030091151754015841082445242d5100b07140004204025a513075414620746a0011400309455500001000600c082d8220b03003800c10200c188a01c03451600c030003403a4040030300101e0040c2204100f035101901c04000002c800307030f071110f0b003a0740c030f5a5110030380ea4803a0005e01044800d030000d4020b80c80e82c003440c00703080200c1d5a0028802460714040340d80e000425400b01c00d40700199503c0780e040c03902c10038400d0080300040c40308d0604140c1d030340d2144000a0512080c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 854974865 1250 854973615 854973619
    0xa0803090f0d03020a0e0103021c1104090e070e180307050709021e0a0e0108090102160501021803070812071103010c020f0601060f08190902060a18050d030f0e040b030a060614 77
    0x40c015403040342d6101010306ca0401003801c0043c0da4203113018802d07070111590340c10704200301d05103160038a42c105202e005200310703070f44840c0070070801c24641c03a85500c0c1c00302446004290801c140101d40c0c96100501c90030490160041201c0ca46211031382c03941d0405016511aa0016501240ca40c001140c03c2c4d20701000681185400f514004580710044c00420400c0d01003410861040b0010303004c0d070310942c12169179a50706641c40e00d4080280c58441d000c0d40c0b1061070741c10000404901501542000070341d820a403041500a031800c00451000340032070760400d04083d2100032461003051100e071800c0c4220388021410f54054800f62003c0c03200f2520f8800182d06c40e4042080c041403007200940d0142034150822400951150201c0100540c00040e1000304806580100f002a007010200d401809c0c1100f5a6802c03000d000d85a941c0c5d40400c0600f085421000d07020038460891904c000d071040c0d1031003c5941c1e0007000040d02030a004040303807a020034000c0c100c84c856a5144180f000303039241ca02800f510501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 854976115 1250 854974865 854974867
    0xc0206010b042412020d020405210a0f05010209040515030d180b07152406080408070f06150b070302070902070201021203100302090412120b09070f020a0803090f0d0302 74
    0x80c100400c01d81045454580c050000003c1240c1e030700d98410141400c0d000c1140c0e60554480035482c0300c10300258007a00c10240b040e00200b07020301d482403164001030301d4015140050302d1016020b88840c4030341011908100d802e5582000000c80c150b0392485a980159038441d6001030340510041414942054050b48a0601c09020319010145c82d03a0301090043d6402040b04648230841b03482e011280b01c010380d824100031410100c04441900c25417080240e0014840005400250395500a039034403c400e0360003a00e084410001600842d12140031841e80b28072802c00000c040e01c0007201a0394246079a000684140000503031081070640c10485400503143ca08011450403256500103076695106003014141c0c1070022001503480c13040603d1000013103401406070034561170640b400104003442002c050b00031801100c02d84613050300900c03d0f051054000ba141e40c00607203851006850410580c542d0b20210301c90040c1070701c006050400075500605100e07004008845001864500f44a02c0348101001c0502c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 854977365 1250 854976115 854976119
    0x10050411030c0a0b0a0302040b03070503101211040b180c0d0b1c0303091a0405150c090117090f150106200a12111c12061211040219030c0206010b04 65
    0x6100040d11084424401403240d880402c445d0070b6020780a20780c45880420004020488250342000045110301c8501d80004042929a40391100c188120f80c40034241403207a0740040c8031810a5480105484401480d5a01d400130803080100c8004003110b510b43c0352400411018211183d500070b030b60800604032147c040b106209540818201e4a0000c05820036031107050340c01c180100c40d0f103003917895040040340c0c017103a2030303d410310698542c080042e921806c80c462000404100742c14040c2c07034111005a548030440303401c10399082c0360180050424605402525907210f4120001c02030245402d044252040c0158035140740640354200300511000280b2818810501424000c64130038003065014114111050940c2d4085401405486000806202e00c82c0c001c0c4207803aa12a02e840200701650b1101201200045c0c04001d55005106030416805a04030500000340d022022542c040800390006007850310480f03182c1604104000700101103550f40c01c001d0705a41d414440c00340506942c2d10440d24283c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 854978615 1250 854977365 854977369
    0x16030e150a050705160c050112050c22050a030c0e01120f0f23060f090d0c11042403110102060c191e02010f05010801230a06030510050411030c 63
    0x428001d0000442960700c1000414881c02a800d0701ca42141c684489011600c41c6c0c038100c0c41c1d10350503001d0303140407860241c1d1002c2148450300070b0750710816107504e690b4100035103c104541e840544040d4869400c2c0e6020b0040317002d48074211f1210096000b000703031510061801100e1500300358107070440150780301c2d44a81c41c004124600c1044040c40d6010070514003540c41420304e580c01c421403010b0281994100c0640014120001800703c0c0141801c1c209103410703403035501b2290340d512910241a800f18000d00042408580000c2182d0642d1501038004107500ca1a0070106000c850034109236105220300c140107109000001220910094080c0010f1420381071040c40d48205010b00c03441150800303440f031907412540344544102410410f0f40031055580040305200079018000001d40543d00900d040000100f0381c00c1400f0b2046030040801861020100000181d00c010800500c51100162030b85000400507000308421101200300c044005124201454400d11060282556034460342c005206008a5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 854979865 1250 854978615 854978653
    0x3061302010c080f03010e0405100e0606040c052802060f070818011e02220518070203040f08060714070c171e0105100b040b0405040b040905010516030e 67
    0x18680908048200c141246804200c5124055410b8000300c80440000307034800c1501c04160180344100c1c20f403956440c5209401d0201c400c61082c1007010703400a0007180301420103a008202258452410310324140d4000401000b0000400c51241200001d1441c3c402d0f041d8140081c0e50009044003850080d8100414014040700014000c1501c001d8940644412040c0941c05442d00c040c2120910038402d0400b4402c0e0025045400d070b03911045101c6100d1104806045002c4042d110002c00405c620044200010b0110a0050074481984410000404c41e50b00054a4200820586c001000c09140c071510050002c6084880b81e482070405001c49000903101002c080d06070b035982212514040000c0145601c0c02c030301008001035204070011205000d042c10b400c40381c80f0300c0c0029a10181282d40d032209400512592084a404490601080c0301a1030705400c06002e40b0707001040864884000c0d110075003118001d4502a0a040c408407800740c24a405000b1600344060b11005850350a401e04015410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 854981115 1250 854979865 854979901
    0x4031415010b430303050103050706020f031602220c0f050703050904050423030909180a1101050f04180509070f03080715020403080301170a17072a140306 68
    0x20b50f040f0f08524801415060480c0d1902c103c4800a5240780c0c3c402d040c080c000f05002c0c00169443e0041c188081261400009d0401c80100030f50000c500d484a0401c03240d1007420b004200300e030f000450201c03d24282c0102040720703021402012001032104100f030000780c07444101c050082e00b88807046c00501e01091b0040c003520204201618081825561403400303411074101103514000c025071981c0d07034580000002000d0220721005550318102620380e000701e0b0b001c14282580c030f0a0306078440c00300034001070b1024030014030040e0706051060400f0350010700e07a0503580050700300c0c07240584415281004440c480c003c0a8009544101805040d81042c001d41914031642c00042c10016002480300c0410204c051491a9000750840464440e038591400781d5580d4004c1c46280200408040c18100185000c601405100e500c440064480c840f9440f4030042c0b90007580301600c000c035040082d18540e00d038080f070408258420b9500714050318104007080d10200010102c460099200208201404040f1001f50003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 854982365 1250 854981115 854981167
    0x10050a0b060d0906150f05040f05010b0910020a21020c01080912130f0305150a02040e2e0608010f06030e030406080c04030f03020105061309050d03020a0504031415010b 74
    0x325403c00d8101600541680401d851001604020014052503480c84030320555504075002d201c104541440303107080e55001c3c018042149400c001d0030b0030600d004407880940340414015905001071a03154984998404100da00440a01c02549034005c3e40c1401420005042409c3c23001160400d0103009640d146092090317071054000040c00d40c0c1d03e0f00c2d059141c1c4001d0030600d40610841e501c1c1e240094440050000c0001002032490100d0107560203802502e055070100ca5607031005a0fa5100c0c4010402009030b4808200f80404e040100e2042ca44500c07070025100310b0f11105070340c1d45040c4140e45000019803083c81014903101001c0405d0402004a604892503450061555142c002d8400042d1042d40d00080075410040030520030180c042d007005120750800c68942020840204082096800140f0000c1c29600304510490340c0754080d0b0701600480c1035500c1c0143c2400e4076603980c868144801c0d20524566031000b038849100c1408101841c0c00340100c190814100b0480d400c0306005080300e204a01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 854983615 1250 854982365 854982371
    0x30604030e0928141311060d0b0405040b04122d111b031c120507030e010f0615050c0706050f191e0509010518040b0a0810050a0b060d 59
    0x60650001491070003202c4007600b01e450040c1c03000c5041e040101030f44a244044902d2100001341860b507151103424402e90089401b40c0060303005000c02c0307010b034411405003d2143d591090f90078113031118421507118611901a11031981828104480c5240c1c0542090003000001c0b00c10b00e145c823080c001801b820301509076001540304540790702503510b2951011050b40d0780c0304084200c040b100000000070704664040c0d003503d195038105410528134400d28a0300101082c1c2d01d80c991003003039070b4942c002c560051007440c0010b0744d8a070980109080d00e90000b03040d80001c5d10b8280038000d0071058200d10305903807024103200d4a081110140c90713032201c0e03207880341c14140500812600c080c03c0c8690200c5401c0541c07030030f500d14a00e2800344090540c00800b401380c0c802205030b140141c40300b03010304100c540c0c1c100c058643c913052400540401040d004030011035a0420340b940000c21054507404008000740c84590b010702094039603048010200d800052001411608040220080e500d85100b01c907043c4031194004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 854984865 1250 854983615 854983621
    0x605040812072303011a030a110a021501061b1202011d070e0606070218090109080d0e06090115051306080703060203071e080a050414060106021011040e0106030207033b030604030e09 80
    0x8c00024072102c0d00502c170ba0380c4001080400300f607000c51300010b20201d015414080380d0b03c5120458042d9a1142c00310307100c10300500c1c0c03007000c5140c2d4104003440314240e10010900d82d0040d40d0350601042c0074071400d442a440f0000a1062044030b0002d254020410740d507031030410269800140b04503401c031200980003020b40001c260180429008002c1e240d8100b1482581c030916118210000c0c42d584014040b640510f50102e110544107000382d01e80408100c0c0c00050050030b1000704003403d54100000c081e47c40d42c43c1d4000840d2a000e10080c0011030207a600140c80c2d00e008207001e001d02c0d01e02d19010304600c02c080080690b0350381040c006134015990769000119030f03075070f8640002070344601ca0140016106a400001e20306500084001e104200e0003020b02061030703118146030040c0910f0050b40d50340a180401400314038440c0d4042c0c2100e078040c0c03a00007000590704822504040164502003220303a000f00d2490468424086d1940641c0401d9006008902e02500c0c000c10320710a03008520f05c650307490404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 854986115 1250 854984865 854984881
    0x9170c10021e0a02100239090108011508030708040612060302180105030c10021b010309140615010806101101020408330103020306040605040812072303011a03 70
    0x8000700e5400b58002e110b8580d040c0c03140c01d5035407082010803071140101c01d41300c450513880030502c45175000c2a001c0c1021024541810720840c5100c2404031511000342084400c001c2e42d400104074001c040d10703000000c0202036140e10203c54409500f100201340d004022440c00a8440011a03080341d100c1c0ca0840e1000e8031081d00c04002d40880c1c1e01c040d41c001c6014451038040c0707031200404d504850742181180c862045030002d102d0b9504501c41050050b070040003010042641c3e2183c43c180ea03010515000560100c079030380d80c40f00241011440261079008030300700304400301d100d0b00c5504049024240078003107140810000c0c10003075140f429030040001c1c80c01c5001c0420025016500940380c500c0030340f003e100d800008450074505205060040c848050341d41220010110040c0707058903000707800341c21280c2e96611440080c3c000070340211b4001008000b1102c1c038643c1c21054a005200c0c3d640c90520001050b6100a16501c807101c9005540c0b5003000100320b005108107541e807209104541d410703201e81c0e994007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 854987365 1250 854986115 854986123
    0x210706111303081c23090316031e020106210c0b180f040e060414030d1a0108090606060306010f0210060303030203062d011b0c0b0a09170c1002 63
    0x78141c10562801c00c040b003041100710203441510701c4010710100e0510301c400c0403419a603400d00d00e049010403041101002e41d40d4841060741c81400c910449192100404901d00e04074a84242980011844903554405076060300c01004841d0040c40284411410001d0030401101e0048801c0e2040044103192020406420010401040c03036003500c07038541c6900c00303030001d60942c01c89241d4424546041c242200d071a0078440e00c0e81840d560001010745d9652662a1402c0840d50030b612242031005200307070844040f4600076030300022079003003540c040d10801000260039500090161091a00a0010040c0644503142680e030b1000d000d20b440b4042400d00c0030141d04281500a51142e20b0b414284e0200c10705406400950159030150741070310340390030700c1a41180c030310341c0700c095214560100346000300c182c0d8800c8010104911b10780c13480800e280e170030395200a0010607540c01602d03440700200b240101903400c91041c40c024035520000b4520030411098040c1c0325060305074060712888080c0410000144200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 854988615 1250 854987365 854987377
    0x80f0735040b0a11041d040201090305160501120b0102281a01080c0d08180a09020a0c02040510060e0d1703090f01060506090d12050904090b060321070611 68
    0x40e101035403400c050600d021100403c480d510403041c1042101d00c84e1040c01800c0f1021680c4002421034641401101c404100d14003034403c2e810044c42850100105905104440400140c0e82c0302d08425450200050154580070307a690a1403031a10102d02c0c02660042026814410903004d09070003030201c9c401c40b080340e01e41d42c0d5005c0c142d40c00450480d268400a1007e140c1a55041800c95219148840400a1980c500c8400174090366061000042d10080c1da600c4969040e40200070844107a101c040707000490f0020164500043c01e222001d0040d42824410302d41c0021500007040012410303d40080d100007450600140a443d071007011806200980041c1c00480b03d503c03801558900b0b1140d0015542c0301c0d1008102e64951034503200195030719244040b121107102c007528106e8a441c41d915000075910540e80f104041c0710082041d001180e440e807050b01070341b03403080c4070340501c40c140502450714100300d8441c0e1940c48550400e50000f141d5800c0240c400c07241c0e0001c00801c41d00404200380c10340d80200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 854989865 1250 854988615 854988707
    0x15090f04020f04031a131a0a0b040f02030a0e060106051e090a03050601031415070c11091f051203030414010b030313150806060409020711150406080f07 67
    0x3c50044200440038520300140c514400741c0d01140c0d00c2e2083c0590a4203800749001b80704000c62444050a07908021134164000c64035200043e880c0c010b0004079041d140000b1109144039400420440b612406128040454100307070001c1442e0b42c1003c101070868841d44d03800703044c03420130801d07408010000b400071070f6225400a08840034107640d900d4181d580f00003e000c2120388002d01540d1100c4800001841c4260000b0703440303209001c0e1111031040d281e41c0400001070f95140c0320b141c0c41c0303240d945524024034010f540b100084040c1954041822050036070a80043d0710079040f5011a1135508400410b49801c02d401222030700c10040b41c1d000707060052911541440c1c1500012600c0811010452886001c8452040d2814200303640b883c006c0b94140c404840c1175074080c10070b00003403080302e40c141d0181240b24402c00c000f4011040140000d14a1080e604d40a4228000003a00f4840caa500c940f00742c0c0c000c071715900b51b590507041000c07000d4000c112244001281401641520b403801c40d100d0501c420b04025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854991115 1250 854989865 854989867
    0x71409030f0a0b0f040f022215060e011115060a03060e240402030604142113051e060f0f07111207180518070f0302040b15090f04020f 59
    0x18004050340380d031400d042c10740700f035400100040d0b100740c200c200541c03082d81e001d60f14100302c0310301c0e03401c100c00d1806140700f90a18080501d00369039031440510981c1a4421501100a205464a4001002000c4d5152143c0c1007000302c0405101080300090102401140c1a407049441da440c0f0020481e455081e5101a0425040003e0300340b140e0b4011aa00c2444615624800e5803800a04040440148152030003501648501e0004020542d14800719000411840a4802c040d1a00b4080c1e00141010b02400596180003d2101e80307c42801510303400170203003503079a42c1001d59604110720901883d00383d86802198005000c0f07040b10040b20850700c00c031000100a80c1c43c2c4e801e6040c610440c8034814101ca02600108100168288002500382c0480e1142c1031001020a2403c0c03041002e040040d21410a0400c03601c800707415018244034100c00f60996401e400d40d5545540108411340c0e241c1c6140751b0003000c502440c40514100c481c200c5141100541c3d000c06000e4014022030700901c074054000c018114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 854992365 1250 854991115 854991133
    0x18020706020f0f0d15061710120c050a06140a0509031005071101110f160507080a051b1909151809020306090105070f140409110919030b07140903 64
    0x1480c03c050602c440341c2240410400214824a01d00706415001b140c000c20050740418000d003e81c0e40c059584a11203808180c8440d5942c1182604400d1152044440700c000040074421800c050500100418280c500b0700d80c61050700060f1451803056000002c03c0110020b007281c010b440400c80b150341409040341c100024034100400400044040c1030400381542800880d0102e13401e075805480809585503503a81c9840d4403440581c503103000840b1f0480b45800752040000c2c11203400c1c802c10100ea4080c1c4003502c4441c02c94552031280142810741e0070300c50030404940c901c884800c45140c2c002e4590240b0001362541200074001180c140300c1d40000340c0360150b80084002d100c1150401141a8401d40032610b03107442e1801c4203420394504540b032800042c10f41880e205894403e05400840207041d20031503140070388500000040c0e811901d0000d4854900251541c054140f80020064100113209883d89080c21955403e10b1100050000010001c0310354102c139038541e010040300c9094200604440a040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 854993615 1250 854992365 854992387
    0x1202070510051e01050307180b030709050601180b0f0d0b0a06050a02070b0f12060a031703100e0702060a0c030f020c06060f01140702010507080c191101020718020706020f 75
    0x3000ca0b0b03440c541002d103c1c003851840d007003d1010760582c2c2004010704030441c240021000390003512032021490342d07221004d070855901e050022001520007a9070115403880c15500142c40420080240c0e180c0c02c0d6150001c00500790b04609545155002003c11036648495441241c054142c40c040b041d27211500780400144181c000d4020301618480c0d8098440040d51460001403500034140340b05090700082044900f1070700ea415a0366072000c1c0040c458464907859803035005003903404024040308000700005000d031012940d0500c500800d02c4454000c041e02e01070200940304e10014080001843e1900301c0c45a805020750000520031034003400454035460040c80166455600ba2181070241030101080070840d48581031460481c0f01d102404d6182048581c011a0b0a504c11101900d91007030074402c40343c4100d4240b002c8644150200e000c50f10852071800c04c000c185095404540c15940f010b401001612035180060030601290000140c840ca05405c100000c3c0c0314040f001c0d10790440c0051070301400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 854994865 1250 854993615 854993621
    0x61c08030705091e0108090d0c020f0d120509040f0612060b030f030d021c0204030c0605210c07032706030b031023060a03020603151807030b01080a1503031202070510 73
    0x81d00991b03c0641d00c1d1900c1002075200c3e0700c4004c284000582c5505100c004d07041504e80c8211200000d000d24400e5619901c50341d568402e2406103800107507000402803400e2074030b030150440c42444050f0400080f40740005002224410500081c091a110303118203080da6014045801c840d240030703080e00c5d51446030a150340025030007074121441100b848500082d900c1c29a1083d1020b80b5031040c203400480d400d000003a100c94000d40c030120b414401c0c19030113002505e014030300c0c0c0e801900c1407990181c40b94894500504029201d441074010403000000741d40b0300351b543e40f5203a400c0790703c982000a2101c4550010a00b04204280703000307030b441e00b80030f1504441020031803840c010074406c0c0308d400b50b261115420009401414400a50310400038030114050315525022a90508002401405007130643c3d200b20b03450f154220ba4003030100f503440700c1151465070010046580309400583c10098640c0b12000300703052103104c0c0405800c200c80300140c440032034110360442d000b60350402d08881c50364141e04011005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 854996115 1250 854994865 854994919
    0x402011112031303081e0c480105040b011215020c15090c0303071e02030106080c030d08011a0f0c0f0106050a08460609030305061c0803070509 63
    0x7810f440c0004410096114090746e0181c61105040300544070307006000e4198118501001d540c4010760300c44218500d800c03108121514640b089030003104400051468080310341500c00c91582d040c04100400a510003120038151801981046413440340c40c248483d00705840c98031180a81c1c030005405603a2400060002e45c048903040344842140d07100c144042e2100760b032200c0350b90143d0082c0b00c2d420000d201c510080324003054000d8120400e0390550000390a44406500c40781d00e90308551091083d6060500190017040740c00e0500800c1d95251a032a400700c15a100402c018510000c1036036411a28079404075071007420320030111030f18010b80d1b06005001300850302c145071041003520000204140d01003034000c40c00c2910291010b030300545a0700c100311a03810100030b12443e0801002c003910250f400580141d940e014500005040001c0d240c06421500c01408007403103544405046000b000d41948141401980b0072130264407911828416601c40c001d00c40c080b684205111088000ea81083e9103c0e41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 854997365 1250 854996115 854996117
    0x302041109130c110304031a06010c1e0f080703090905070912060e0a0b0c0418050c2a151b0c0304090c0909090b071403010530030c0f10050106080402011112031303 72
    0x202030702c4c0c3d0f030300544030308044400040c088165607004114cc0186080240c03030803070080351100d03a801312550f200d0080f5441244100c000c2408500240500c21181c482c00d90b2210540c10128516030610301400321816034841d005000588458220424500c10300c000c0c6079940d400000c542c0d50703040541c1c02620310307045801104003210f500b004a9000c10024015580543c8071001d100745069211080304a640040410b8201307900703000a80780342054400c020440d2840401e2403074032214200a000d2000000200c131025403802c6091050000621003c003c41e02100c183e0b40c00080e0340ba0040d4401d41e01d0400c1540003110f107600c0c0030346000c18070240d1142148100120759440400c6408405560032901007800303150f822107280041c4c0311341407118050754000c4008400240c14400d49060b00286194002c0c038101c10796030042030140d0601002001071303030301608001c0001d000030342c10010000d2420100070800b134100250744046091180040c000c0300129a541920207a8910f0301f180d9010032aa0381510440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 854998615 1250 854997365 854997413
    0x4060806040603200102010b030f0318120d0f021906020a03050a1505130b060a02010903120c0f0318140601060e04140c30010302041109130c11030403 66
    0x640300786001e10508083c1c0b070740300014403541c8105081100e035200004042e00e040d0344d40d8810704c2010796020005c1c1c04004980381c0c02555140307280c641448412004c806070301d01075008040707a0130722110080b8104c507541c50580b422402c2601c1003201249090145660016070882d200ca030101408415002404003503d5070702e05015646854002400702e480c40100d9000d0702c40380001c107018902c3c241e10300740b500306100000031441800c50f00009100e544400e6072000540e668054280400d03800050441031908100340810a00f644030502501c1c00d40c201d4000000c1503070b01d812451120b02d424003080610784d00301c200f0004401c40340814595411303003805404086520b0a45551f5580307003034000c015035a0f82e0400303620302c19141c1310411a044d41000c071005402e050184060001401c401c034440c00c1c9480d0316500c00320709500d140144411a80c1c030300441800150304108a16558981051014441c80c2107000080c405176003c00886480c004004100c440d4000050300005022070245a1050800240805 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 854999865 1250 854998615 854998621
    0x20705190314040e010f17100c09051203090a08150a0c12231612051509100515070b1f0f06030f0606090f030809030304150f11010c0c1b05090c040608 66
    0x7c0054640c2d100c0100407190302c811246810070803a60401000c4100e06d04005030804d45800010f0140b8495480c0b441e04c9900100340d800051900d40054401400c00c40c014001c0000030714498650614010800c0d5485030b1601c20000303130340c1e10132030f010712801246540c20040d4418a407d00c800828507100c007100000d0389880805d00b507045502207920101e0304ea44502c043c02ca500d813103482c003a01004100f10070803150310602800c6030321030080980c41110700020601d1050300345402c0007500c0d0f0142030b00c81800c45003031143c500000e201006040c0c100700c020040c0482501e144407810090109900f00c41407402c08010001038103901600005000410600107102a5446074022605013070184242c2c601e500760744208201286c540d000410311800090b054a203056103594040c4081c0c00d0310403500e0b0009000024810425a000300c0c01c0c078601c580b4000a109441504500408a101309900501644003071030441d400400c03072b6404a001414082c0c2424424a041c0444140769001440b4140c0814221301c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 855001115 1250 854999865 854999879
    0x603060a360906062106050a06030c170d03060b03060103051b0c0a0c09151e091e0e1218012f0f060907090c030f09060b0f04020705190314040e010f 65
    0x413010900c42075140c0f0915800e0071b0745400c0f0141c98080c0c142c4400310b5885070040003040b00140008090403061400b061640003980030503203001e1132440d00e0001c2600d4140c0034402400c2c0f000403a90040340929001c030302e40d04c0344080c05090b04a01c008505030001c0001d0080a4084007040450045001c2c155444403256a12145419034000020110382e000100c0e00c10f10001681c84240d904415102d10009440c030344550310041150b440030a5681440741c003030351010440d82d9500030000a41e07482e9000d070070100c0c0c800d81040e4160043c400c49203c00d42406002c910207900c108001c001030414005030704140d000c3c1241001040310700e900e010f020350040c6000c4400ca20307800100c030307401500306400602000f0319080c507010051480c100080209a201d511025840420b2701800758510700601c00000c00003503031800c215a2a180316074043c0505d00511680003c11400304604884a40000c0e980c41c00902d0f03840e04595003401150810041203000c5000b0509501082d802c5040c1c82e003407000c2000704c45c1c4400c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 855002365 1250 855001115 855001139
    0x2041d07050a0e2203050f0a0816030e0c010311090307090207030f0c1703060103140708010618030803040816050a1406060406180c021c1205060603060a36090606 71
    0xd5110002c1c555220b40201d604852884c201d046030103842e2450a02d401c002c0002099030000880f040007840f00c100740001030001e202041c030520158202045103d85c0000b80c0354071043c40c2480181810b503650404420014102c048541804008060342c5601c0c1c3c507007968000a4200103001c1d800904410048108217025684c0700c250383d9080a50118251000c1c280860305600c014440c604040e110709261090a811542c17081c0148541e8403101c41540c181a401071040007034501682c090f03045a442000401c0c40c140031607030400c0e080040141d032a40c81480d0000010713650348008000d4031613a51480103200080078401008042401a00c00c20303154802000162903684c0030341d0b503141c2e8082161322042030081c2c1c090b0000c0f50180c0140d801000060b0441c00c1010004e100304008107403070054201c107414003840340f194410303401c441a170f0a40c10160080350b8416a2801030210310100e100d00740c1d00d00d41c081004540b00b04481c61508400340006080f66001d4903c2410855000b8100744e00460450b080c07031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 855003615 1250 855002365 855002371
    0xa09080d1107090c0302070818181509040c0b19030501090b09070e03010902040618051014120c0301110c100911040f0618232202041d07050a0e 63
    0x4009012103820a642030f8000c0944924140c24580c0c200a000300180340040513181145100c03044c8400714145c0414031410104140c000180c905030b100411140d0411a40c0b010007072101662441420381e2a45061a600340d11600030b51128007020400300c0668246004100310452141d8090201b42d90300c84d00e40e41074484e0040030030340c010802400181240e21500000c581000014008102a02117030080340840380c0c55001030342642889100560240b22178003032a50008225007044140a1802080b92614407a028109104210864540141d080704006036030140500030001c06c482c0d000c0100c000200da01031224040a40a0028003101003071140c415400e0b0b0b50b400c04561030040040c042000700038440c00c03054489099503007078040303103a00c80d601c49a03003900c0041c500000c5442030401450340f0000501803001c1c41541d05000c005030303001c4444001c3e800f508082c40802d0101240d00c005806071a4002c115448041061015903410800040c24400c0320401da0780c9103d601e07200c1e074608080400071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 855004865 1250 855003615 855003647
    0x15080a051c020c0609220c021c050403210210060b18030f061b040803040b090f0922171804110f040b0a0c0512070b06061612050d020a09080d 62
    0x780409030442c02c00850f24141b8034840d0980090703414040c0c2c0001c00303c401a424070b00059001c1700c09620590410405000c00d10100e05080f400c003480d5980d08840d840c0c00b401072039184076480500a036224002c219400c51880003400600c551130b1115000481a04103800700c1c0d1701c00307014160f020700e1410007140d010700340c0c5000000780c00381d599511012100c810104a542168a404100000300c5040c140f01030710140984410302580da0180d03004000300c0c02614100c0e00e200d03a8159051108121154100e00140c071502481c148590100b4104039000b49104645182500d200084a20034200010110310301d4201c12101008400098003203490503004040c0481601002040705104600101e009030248001529012006003c91740e182414000c2c45220348404c40c40c0403585000f00682c00c600f0541c0b00388260f94150808501100f0314030a07111108c0050031411541c4819000584180c0c115041000c607020300755615182c601005103024164840c18807180541101070510303a208100b000c0d021500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 855006115 1250 855004865 855004867
    0x2010c082d04081314040614060a030504030c02041406010f110d0c1b0b0c010507021b0108060d0803180f030a09230a091a01020607090915080a051c020c06 68
    0x791029894111001d07106442d190401c0c88044d0700351800e40c44240c080e02c00300500f041c3c01c400d4030f4107100a44000340c10036558124030030030300400750b00c941f0182c44c021015480c0115583c1c0340d0b400d041d50714191b071042c00f0b0b4015003840543c140029902508a000d40400e0b0b80c2c00d000020701720303002c1b14005025174014402d9001200b140205521900399210210700a00c0081d90600740314500b81c2d4604515440001c02c450042501e000303c41742032113034581c401e03c46c0c0040d0440d42e080340024190f600508030750344d041c000710030040750759030f1561600714802d180e00100195480c2401c4c04000b42840c1e00da46985000c4c4240c400d10050b450000c41542c03c6020f603030f180d03083d80605100c92030402560385102d4141403a8030186104039030740c03006d0344400140245c840014101c8503503500311403501071010003141550f00c548244941c0c5c1d98020203910480300002c80002c0d07213000c1e0200706a150440d81d408240d40e40308840c1804103100d00441c0203215982c2c0307059540c2e900102c408041ea203c0201212242e80004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 855007365 1250 855006115 855006181
    0xd02070b0f0c16080d020a020f01030e160b091c020f04091a0a09031b0213150b0c0d0305010f0806071209060c0801050a05040b06041211090702010c08 66
    0x200d164080d0240aa580c0d0049040400100c50309181010740796019008014000301008103c205100054003122148060100c50f0101c0d000309150b005482c0d40c0c58109561031000ad040c8a40030301c0303a0041c0c0700d003da00c0ca07003009a442e82d08580c55000381c3c500c0c910540411841c43c021000da8401d4030300d81c40e800b9101e9020344051000300001450540380540b41c2400b0840032140d8030400006130341c03089840003400502d907009400c00030207102d50401c800070143c100c0741d048809640d030140f50711206091680702103071004410740213402c0a03405600503e030000d00803400c00303d1850082181404602c40c1d98042205a0380d0382003441a40250384a1100f40d81c10140100e12180e20814107008054002c0e2004180300d086542c80314100c81d440d0b005480000c80000050060389024002400104400c1310b0a00410007242c00264507032203988135940e40d41030464503400030002c030014017100c0d190b0014602407040c41c100801a000e0300c400304048001440c11000192800810340522078135509140c20303c21405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 855008615 1250 855007365 855007379
    0x3150902092d18070f0905150d0f110d03120c020106060f0f0c0c0b0c0615030d1b0206040f0305251e09020f0904060803160201120603021f0f020d0207 66
    0x1500283c0850741520141059108030300c0208482d200030070380603a410140c18a80501001120401f03002c040c0c0c9842c1c0c001c003075201a80e48440c165415070f040800300d00d01c07502c54034200e9054420b4882403900841d0300c41401c0d00345504440601e1303040082d68810b20400d841040200c1c03c95020740964070108000315850003540e8861905080a07038807901703103da41e807541a221682407003da03911400040d04002148551644103100c0c0782d802c1900c400314001b902400d50300098840390b0004443c01040300c1e04200070301c03008503074202c442d10310340203011141e0329601c480e084607500405000c1075490344904a00d448004680070210722415012142c0788540c541000c048024005080311a456642d14007000400e4402c802e200620f00d0b640c148030340030744e41d04042080c0300a9400030350040c41141c0061061082144042d030b42540300c9582484d2540080000807450001070a050b00060b4111449420400f80c80c0445020320010520302c1c1c42d0980d21500b00d0f60101e030f44e2008010360780d0068000c0c6a08014030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 855009865 1250 855008615 855008701
    0x60405030f0d0612140d090e07181e0807060804030e041d100e0c0604030c090506010203430f08030603010b060d0b01230319060315090209 61
    0x1000e01c020701043e02503039081c1641204aa00009a40758441111000a00300042001c040f1920f20f500f85500000d1400d1550700b03162070f00400315401e00140340c202007082c048a4001e0000340444020350b810f80003400d0242c00070864103002c1d08030188285079000c039145000b483c1241c855a03160351601c0d52070b070200c0e05020103080c00a40c030000d030800d46500f09412400070f00005040d00d9058400080343ca03801c5542c189844020314007a1b0007070307804120902c003040d01c0c184410151281602d000c035054a450700100e185118224403031020a001e02c041c44c0255403140c001d1000c124640200307070103007248011480301b241c501100081c42d030b180d400b84600000755400301440c1d100400400010302c1d0841c140106486500410000c0d440c00d80d2022000110340c0c00080031503044610030343c3c00785884501d1041418511000d4408541c03400315084212114119411020181d644001280310540c0980701c4d10000e0001400100c0c401c00d0018009040808090365090028440c1c0003290890680810081d000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 855011115 1250 855009865 855009877
    0xe060f04060806040b2a0909040c0f0f081006060e0d05030d0908040e070c0308040b04020f060c010b0915030c04020d0e0d020304080c010c020a0e061f20060405030f 72
    0x2040e00e918000448107000d110840c444c500580c0d1642d0240b07007038100c2102d5400940011916202640c0c1d01d56000034040056904003a000e07122449a900c0d9818070882c55152684084001200030001140c0d0071010020103007101c1c9060226100c1030b600f010b5120550b0840c0c05400c6c0010306084281b809031a00c800106080c0e030094094926000d103214820040d10782c180f13000e644d45240058100314501a0f000815071190030781c6401001c04885590040504a0180000c1d003024640c1d0040b07415995111440f04031070000804596030390340d51880c40d9018013040d10b0610310460040300044c00f66581e58803605045100240945503003002c1c0c032304000082d000b005013404806d030780d0362000402400401800e004040d040d001161110301c1d1246017450b203200400b8031410041c0c2e2150400c01601c80c000c0d110141c810010300015203a8a4001183d92040000702c1c030f0071742d00b49018070390302050382114408100c81212210b031400f100120b19a0340e6188810349005113168820021401c14030b5040000d001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 855012365 1250 855011115 855011119
    0xb04051e010b0919060b0c010b011107032f04050a0b010f0809071e030f0812011d0c0c030d0c031b0309050c27010306060e0f130602090f0312030109060f0e060f 70
    0x904961110031b2182c0b1030f0410620007440b0780d565a03581c1170543e0041c0e402c0c513204807400d004008290460340c41700300c55000d010140d1110280081c41c0d002400084c0403d00600b20064030800a5280841411000e4290558554003180c11a6a0b40020398070500301d4911640b401801801c81d00c3c0350180402c0c2c03081d000602c0f00d403c0c20700e51f04003000140314040d10011306409501c01d95128200c0c0c280e4443c00300c2c0c06034050b00c0c60414803083c1c0c034156441e9102e0554860350200d103ca0b118640303c41024214400e6800f15a280e6203031400611819405500274205074102030b40c02d040048002e00280d04980c1600800b4059902842c0c0c001c405e80f80c50514511034001600500048551103201160fa4001c01e03082212140c0c1ca41e0018440c81451100b4a035111000510404e03942c100540020300e210070990b0080d01171500051003161a496028140204501c050110350b14982244020101c5400c00e0055400e4203041c0070340040c10303400c148440303401e61301c004015040c03a84072001008010098121019 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 855013615 1250 855012365 855012371
    0x315010809120d0510060203040f0303030506040b04091a1608010e0702030c0f06091b100f030e07090504060b06190c022403090c06040f03021203070b04051e010b0919 73
    0x4a00b505100c060490707404110400b18440c2882e98004202800d103800440440d4000d100810451414a9090b411240c06080000c3c2d42d4603100e020501a1001410340d58000e0b040c904c41004104541d07059894185070b0606006554a40c208170001e50b52424041800269152006002d00b001d680c460076005407150040728540307a40f08150505140da202414407441e001201084041441070004040180d1020f4650044080d820005a40b41c01c1c8483c4150402001c0882961142c1c040e43c8034180e003000e407030200d0707225071361300e030104000740800712030807956a400c1064051160030f00d80d0a8901c1d11109019a0842c54081d020440307001c280000103907030010002d60464591034042c02200c1d045100118140d6507480c1c074000440c9806200c44960f401480100302c200051203c0880c0b65050765811166143c10610080200d0302d54090044003500c0c0d2541d036014402040740000e46e0940b82002054012100d40c80802120300b00c03000c0e42c00c4260410a00000201a0810489203854441c6224000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 855014865 1250 855013615 855013633
    0x41d060303041d07080f10180605042d02070c1a130608150a0609061101150b0720032d1501230616080d0213090f020315010809 56
    0x401207003460721445000076001d03d000d006030b2541c0002c0b41944500c50701c0308004c1600703004c80c4507503000c411889140c80392905506000030b042501c3e08080d0041c10010b006010708480071400d04413814541c00076200d41c2c81c40d040c0c12499503005000b0380d81c1c0e080c0c00040c1c440721203150007045072514981100a041055007084080c14403221054410080c0c0749a030380f060400e150036407101c24102210752032036104c2e00d8403c404002e12540300716074409551613032400300862070302004802d0160a41071100c1d02002c0c65404042800034208001c1c00000380608540a20a104e8111603007105c0d8060f06150b4164200c603e070010000c06c0900c0245200746008103642105c14003c0d95542805030712511043e4100e0700f03c004001003041100c40c1d6100c0006034403e070040840e40c1000814911030b043c401b44040c0300d040720304024407103181c083c0d5400c0c00c40c180b010755a4148015116181c043c02d801024161860100c410240c10030311f2003640d10070018407080e007941804080c01540c0c00c40e00240f030428140704000c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 855016115 1250 855014865 855014879
    0x10b0a153b01090801090f11060706140603011b02071401120510090f02120f062202070c060309020306060906060d1a1f020d030207050313060e030c0105041d06030304 73
    0x100d034020a01a82181d0820034601e400100708480c1603100f40c45030783c18500c000d030114541da00c017010043c1d4445000d17104002d01e50007107800740c0542d60003e06a01d160043c00020040c4447c8560310402084008008800311040b10481c0ca001d1442e41d400180c0c010301c4140440d104014000e001c0d04414104610b031521105054400d40b00100d42d04004602c40d410704201007455402220002c5414150550411482c8031440308200d100a11403058040d40c24041510b036100c00c0c402c04440c00000079034800d1611a0440907000c1e5000101c200d4056100c1ea5000490b14441d21820004560040c043c0c042a1180c10404c0581e4201034034199003c0310400000c1e0401003130344901019101e0b00052405212200020480c0c000d50030748010701d0544206134944c1e082d5030b0105070861207106074140180c4902031400c0c840d03c0d50103400d80c03030403c981400a01064103034220218186110048040741c00072580400112841d005030701c188500080c00c40195005070b881d040d0007030fa010302c0190840b0300b01551195 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 855017365 1250 855016115 855016187
    0x30818061611090c120612010207050703260901030b0f0405090d201e0c0306040b01081b010207060e1203180901151209140f0609010b0a15 61
    0x4110a05481d0141030000c20603040081603109808980300c0c1e0b01e03440c25035244000c80c800d4400812180c11214001030341590388200c0d008146510900071900c51280d807038250b42c0c606140c00103589894202c0a4501049032040b503100140089001050a10303088000540191007441c0602d0340c0141122510900c5032524802c407032040005074001c0070044408040a0841c0e070410882003191104241c591b6101440040e14074249130045003200c0c40100b00104550801924603d000e070705001d100180000c0c010480305160580390a542900c1e0070110b0898403044580642010602503084110108961406484c030301c1c904900240500240c11000641c1c06e0569103d0b40c0f1140740c04501c100e0b003201c6400c002540d240980904900c03040484040700f00a0311900c0d9210002c5030250f10785500c0d100b0401542d00d6041003081140c101c614403141e41c0842d1341c031050100c84612056191644102c02d0746050064001201c42d601041c500b801c01d00b240495404071807a8000c0603c0580740152440070004079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 855018615 1250 855017365 855017377
    0x81207060b0303090310201201150c0b09010507080c0a090e0714030c0a0f0908030f07060b0306090604060e1f151a0a0f050403230709020c07090e070f03081806 70
    0x20b800042c000d00c10a82c0b42d071040f060b05109007c41e04180900008844110300b501c0c15155003041000360100c2503401203d0100015000615220710b14040c003c1000054010303074020499030b2a03400d000c6d42e40400c5038505004101641000806100040105a134000d01541d001040340c9803036001183c24405152903a40199404c0610000c00070b41032812550110180c035505c240c030729207209818640711a00d9901d0240c004ae0f1100200001a501d0412906501048070031b10040d0907030340c851900c40002901c42e2401c1700e0540702d040c184002c01e00040c0b40462080c49406103000408000b0301c41e080c50000074154114807a120310006040440c00801d0b582419101c03209000c0e03100e6460032101c00082c100740c21801903505103c07043c8414000203c50300c1c7e079003445005000000c0d40c40902c8601040c5045030b076510020049200080d8000304000204507402a6000342d4000e00c15012410f003015907480082c03140d03900705001c020081c0005104030f8024140003042d652403429000b5010700040041d4800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 855019865 1250 855018615 855018643
    0x50d08092406180708070509240306040506090c270319050709020a0507030c02010e1c0212030406050f070c18050703241e030812060307081207060b03030903 69
    0x401c1085990700c0e040c1806041280800c5404200b400e20355000b40a240003d0002018014082030007000c50316824601301444415070001c90201144078550071803913009641150141d820701c03000640e207043c0300c1d041034001c3e00d04100e47c82c5800d028a00c402c0742f81c03c02c044040050340703056030111641e550400c81c00c005483c00e03007109540d02e9007070714225107800200d07031191401d58010710440ca1131613001000d031107440360035060030326042c150f91004a030b03a000c03207140013a845406410407038070092074050300700202071081e03030240181605403240580c2c0b401148078a000040341009442d0382e984403a8043c10703c5c0c40c032403070447c0c05041d154140130920b60500340454a06c282c0c0c403070400c000c00b6851700854003949040750304c41490305500b8041c0340c59101e0303038040d1100540d0286480070310050455500c02c0110b420014068841c4041c1d45020558101030310820700ca403188507004039080101144805100e50f00c10440d070310b48406e036501c035005004070740d00e420340c14041806140c0542d1010b00100300c138a00c213 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 855021115 1250 855019865 855019933
    0xb0607080a080f090c120115060201020301060906021506040e28020405011d0f1008030705030c07080d080114040b0303070302070e09031303080d06080a0803071b050d0809 75
    0x45003a004042440042c00c0c2c000700440f03107090155180e40070603014110603041c3e400413000801028850301600f0890505640c501103600b0000d40343d5419400740d416900181c0d5030b00d0b51643d036102c0883c0da0f80e60301002c100ca03954000000c90001e19041d809184e00c4546a4250340c0780c40b200812640302d0910030032903481c22074002250281145000c2c40350a000d400841110960481311550041107520f0003091741d40403006150104040c60440a4184020107440c4112a550040d6242403a16034110b02c920390154890380602003801c1c2c50108a0b265035128030b50360b6840c0c0fa8a442804150340c245424283c0d007007a9180301004480c0c80078801840c82c24001d400800c0964500000f111040100929404540e08140302c03141401004194880031a50401415074440c0f64001035180104480c3e4404a11881004500020004903101940c4100704549070340c2411180b150140c034070b08400312030082c415084040c20247c024014105550040c1218080301e969204403c64041076603070300801165a910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 855022365 1250 855021115 855021127
    0x5094503070f1505040506061504051011060a050c0319090611120a0501060e090a06050a120b070309030e0919020d06180c0e100c0209010f060206090c0f060d0b060708 73
    0x2c0d2440703e500d00d03684484100501c0c5081d0703c40a84826010304001d2103118051005480141c00100762009000020182c802080a8000c060020981c96900100600030107001821120151280500c00c2e00584c071107514540c3c4603080045030407500c0d00d074001c1d11955071003080082400f0384200d100c01030400503482e54440c40740d020f10722907540080c50400d056050800510801350303c90b030110207940707042c1c84041054a440c1e24810242a0b02c2d000f50350410800f030300008402120701c500040d0300e809400000c099132203161301101941d10011001e000303ea41d8a407000207070304100c0c49075031740700384288042903e55003585a1a0281da12443c079081c41a81c40b1b0000380031120a14000c02114110b807002003020b08030056002d0040098160924803d081951100b01d16900518031401e5443e0700800e480119a10303260b912982c8006801054010701c15000081da8089002600d140103103002011403940b02c82c3c0c401044040d070300034140180142c0e124894202c50b40c070360138043c2109900c51402561245 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 855023615 1250 855022365 855022373
    0xc0d030209121609021b0607030b10020a030e06030c1b03040503100605090604050c0403052a0603040f121206081b090c0409050a0b130605094503070f 66
    0x42c444031070401c0103400c500100802e00b65004028412500b502c0e80c0980c8480182c81c03640521002e10103104800e00510080000c1542e255105441074003086034170b5104006800801ca0395400a96401000300f42158407840c035500e04200a1035000303c091130240e103001c450001c00d007043c02400c1c4c680091607102107001d003c00e10302030044446085c070010082250a26200000305c032800d0280005026a603507001080450940d40e0844003d1904501142c0c000104901100713004403401841d1423000646a51180d8103140c020102d0340100c2d0800070550103040b05440f100c0c80418590000070901008101c040c0c00103c070750082c44001d001032400b802c2c4a4182104c00c1020b200800303401407083c46000200100d19201006440079200f03000340014041e41d84030054030080c5521110164046440014800b646115411200903a06c09440b02c164548409041102e0b00760f40d010b089a455444807202c0201824020402003645102d041451400035580c01107407d5900c040019140000100c00d940c041c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 855024865 1250 855023615 855023629
    0x2040e0f0f010209011b02011416110a03050c0f0415061106130528060f020a09060509280b0a09080706090e070302280c0605060f0306060d06020c0d030209 68
    0xe081103500030f520b0b1510820001b1b0110018142c03105860200c40341c0502564070581a9441c0801a26070142c0e45240c0d00e0681483c280302c01c1011644201900c890380c0b940c0c2802603803441104da01000a0078007116007420010001c00d8107001036040366540c0354602601001680000c02011a501c810b80b00402c80e082c03407400c0c408018070340a5000c0c1e2a00e00400003402c00100c1003010050000d0030242c1c031603042d80041c50383e2440c1c6409044141011015182c900301071b402131041c03003829100d1440ea2941c40d44180c41d1030141e24200e983c841620203040703103211002035080c04503c500010301e541e03d5444141c0b00481d40c101e5030f54000010000c0f4401d21118004120b01e8001d4441d90820200c251700d80000c8160446004100c6405c2607000714a501303820b200d81e8042810b96240e01c03000480c411320207900810b4009851001d81c0c1550801e008580c140c20070342c0c070a580091000d4091f01ca030355038401c05e12180241c43e510481d006a400c102c040d040721014014010f504130b4564016a69030482030401c00f01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 855026115 1250 855024865 855024883
    0x6030a18170705010617060403050310080624092404060504050c130f0e1b16030e03010c090b09060327012c061603020c0627150106180302040e0f 64
    0x400310961b40d6580300400005201507003e0b6161404654035641c0103031101000085901501b4648240b2007404801d2140b584c110086400f20010a031400290608014400030156000880100c070b00d9180030030040c20b2814901c8003100900040b580580d590045021200c046072400c1750028003245501000c5007a04040000340520201c00c101207003051200c034111400985098503001d2807002d070014218192040d185030030f41d0308038110100c4185040281403a0804000c03203102c0e5180480001c08940140035081c00d9030342d110050f41c1001d10400500503513610150000c0b0221088144501808071003000c100c8841107994001302d05131100384100400784100c1d40c0d0400d8141714030395442600c2d031790006800750321443c2900303050303c1d03003a2204081d4000e20a0354040c0516018000400070211070400c09480740304190350415140c0046028495105c280c41d088010019200100401c000b522411174242d40c0d4410505016005a4a40c00141120044042c246958100b451100d4000f030701803280c010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 855027365 1250 855026115 855026129
    0x8040f080706050c12070311030d0603030e030a080904050c1303060b010e010806010f0e0609040e061b090603040b0c13030f03030e0607020a0228081c0302040506030a181707050106 79
    0xb080248850b01c10b920344402d00c00c002c91110006c034190051610540e1070108194224054954442070300980102405c82400190b0203e1201400c41030541000100b40c100d03150400700c2c45003406040b100b000098000a003924500c88424007a07042100c00c8400e10320300440c401c0100040400e640e01c0003510041d1600c0a041c1840740301c1d0104051a40c04c50f4440c0a0394606181001404410800249280c000c12891607081441d1042058981c00000340b4140a200281003401d800074915880600078803c030751101c0e130022001c0c80440d0004000d00e05058004d2400440c041c1000140400448a024a030f031040d00c1e903604241780340c42819014880c0c03c03c0341d095480070301440d103000d0101035680e00415400a000d41450f400d12820052a100b20351421002c1c0040e1119203981c03080c0d02c03030366140444142d40f109031650346a404458040d01c222801c0303035030141c90315085070703101d025040c01003259000b10003540703031070490140000d40d8401811103004442c2070724640300c15036404c0080c01c441060300300c24 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 855028615 1250 855027365 855027367
    0x6030f060f090504050f0105090d03060b030106021f0e0a060501060806090402150702040e0319110106230102030c120307030f0911060a020f010510031712040602090a0308040f08070605 81
    0x10164661280c0ca6a0582e41002030104280c0c0703440c5019441d1000e0500185501c0d4a05000e00440e040b02091051f50342c191a6000c0c0176007620717802d00544a21080c882e00c00581d0008920b448a080c00c952a4000c1c0c01c0e028034001070124840b00e40e282019100340086452a582c0e0006101c09c0c0d41000d03c0d2030300700a0030f40718507841c0c0c40c169010840d00c10511201e4031031110041002e00465449800542c082c0000718203586d11943d41c41010741000142051070b4001c2900700c14403480034201446003004582c850038451030082c0040301c019101d544201c0c0b0450440c00b007000034107203500081100c0c411000c1d040380c240e6501c0c44c041c00018110341e040c01540700300d02d08280b0382e540816045401c890700c44800300d818075554103211109900c0c0c91259881304645500300402c0014810b20742034900112400364000d01501c03038081000300342907c00c024000c02103101d4000071501007802e0b40d001c1c0c842108041d00c0120596102d8644400350b40007540326400519195905210303500e001c3c40701d10000e091130f0401c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 855029865 1250 855028615 855028619
    0x308070c02180c090d0807051903051206010903080307091518030213060e04031d06040608130c1806081e030a05030406090b19060f061418030d0906030f06 68
    0xa02d42c001070000d518a80c84850046032002e00d4510844001d80c0b40100340d000d000000345420682604544010355150113003130501701d031668902d1901078038540e043d512a40780041e00d120404040d0710160286040121024001c00021744e284019806079401c0d8480b000d80b81d1510822500c80d0f0001c002c448104804005800c03039410014440c00c00b6241d04070b030819840f41011140d132000340700c103078030904030080d1850500c410300d504908403100207448280c00c40d50301c2010b24207001d082d10a0b407080c8800261910001144d40741c07644410030b6001e22900078640c40ca5038402c01042c20846414007002d54035038480042040c0d2808100754800d9a101040c861494841d00e54026100d014a0000606009c0000000380401c802a40407052465001d0f0800045080c4074031010080c0007019080346240d03240c1080860036001d120001e0781150041d584480c200c0218610420b070640080409404012885614520503542400401c2040410317a58030031142d843c00030000c3c10350320a080c60110007483c0001c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 855031115 1250 855029865 855029869
    0x90109020f040e1302090622020c0a24111314010c02190f05030106080309090c0c010207033606140d0924021306050c0322050f1225170a0308070c02 65
    0x14101c08e0000c0046c0050b1101c44c03141c030307050034052400001082c900034151002c11422141c0621389490010f00d40c20444020b80c8519219140f05802130340c0c0784120203010400054140803420128624185848401c20b035480e80440c0400488896080650840c05000d0040110240030b400050104030000e024040c80e01c50300d243caa10030990064080c88007000041c003000c9180b4100c0340b0f8144020021595552941001045000000d41903c2c80d08a15046000c1948440d480c200344c12400503103800f0f4403407a1070300550302c1c0c0321075000039101c600b03003800002d1010219110b02c5140714018581c131481c1c0c2c0d00c8900900e00050300308490548461062084440d5450041503240944007107080140d03550340100100c901d140100603180036203018940d50725001d85560325162045920075285110590760800401001454030220140103522140400d40040c200042c100c6900342c802e220900301c6521a82040c0020f0300e4a640140035a000003114810182d10802c0d540d03020300750746010700400d0354540c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 855032365 1250 855031115 855031159
    0x3110304020a03060506150705011a0d0b01090c11071202100f230706020c160803070b1314030a0c031706060901080c0405100e04050a0b090109020f040e13020906 71
    0x28105598905c002a1507855000c03401f90b004112445013526541c0ea0719045001c2c069500500041150818004400782095451341d510a07a00c0134024141d40e00f8114140018906440d0440400c101c2002c1001c0c0820705000e40300c050300b2180d41d0903040300c0b0980140310400c81c18403009820486402c404085266000d240308607008103c0468400c2c3c001e800b600c0311400e001e43c41c4050315940c80060400301203100001c000c20344400c528156184183c1d40d4139025240d000c0c40401a03d4409aa400115034403405000700d1f560750712404100310003680b6105000d00e1a0040422600803c0d0010580b000b0b01d500982c0840011100c1c0080550038600300300400c1107402022403140c180000d240c08070350074801c01015500609005481100040d449250003407405000c0c1080390302961801002c1001c501d481d0294190442c00582603070866403a01031040020351014851041c0e03030506100100304d1402c0b000c00d09004400007282d400700010705004000b85010040c103600d1003000440a1400900c5c0c03104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 855033615 1250 855032365 855032369
    0x1060c08030f07021c030b0330090a0b070c0303080c040b0703120603170a1d09010501201005040204140601201f140c040308180102011508060703110304020a 69
    0x2e84030810503200c011042e8030301100800c01d82041e500c01400705c4e40f45681079001200c6810101c08035401480740f41700030281c003071444100706e038030081c1101001d10000240d4010608401d0145c072061b216540da00c0c0000c40c0340c00c14001210022050380c4108281580480e5140d040380c00b58000c035103817514040030000039114460005050002031456a0707440023140d80700100a6804c000c050600310803480701030200782d008004940104049440c3c0b1035180c0d40e8440300c01094040645580380a034241801519503181100f602c1c2000c1e02801070704004400244400400101040808101d6040a10411042d100f00030040005d100103001000016a8040d5481c0c41c40d0080391400043e500100142c103082c014282d80880e898201801040b458030340326801310140002041200c036141e2100070181c4503500c81c074440902003d00134011303008505c0302d443c4500320030f001c1400009400c8200c0091040d09001691140c4101d4010303404000d903440c0c06010380d0311100302c240c44082c9140380950001d00028514 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 855034865 1250 855033615 855033631
    0x309032b0e0a0501030c0e0901080c18091905030712020106170f0d030b040e010603080a08060904030c12050c06040c060201151d0402012606180123040609060609090501060c0803 78
    0x142c441d01c10021f0041481800a00c00903140311055a180c0141300e9681c60804211802642e0b44800c3c4000003100030411130041d03030000060301d2403030300340c0b44000c0500c03100000c2903a02e400304102c00000a40713510151048081940c0020441c40d1500244181104010074490000d4000c4421411480b001040440c06030310f030360600040200744240403030000c021403100c0c24125841c19030040107115101c0042d10382c00805645140c0140d0390401401070100301038500401003540020000300140202c003102c11074003001d00e80b05042c640101000c0c1d00d003800c1074605465014844005000540d03080c09007418800c52500400d0a080c58029200025007043d00010701d003a003800c010404580c4118201001c0c0c0e443c4003030081d21000c100c60300c0c181d0108190341840c4501c040c03064901c510100002400c0c125411129064044e0000e401141c49070380b415030501d98040d6603010003140342480303441500050100e0f80d0b14140c80340d05117a40d001c100d44040c0c000000340000521403a00159020741165840218 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 855035971 1106 855034865 855034871
    0x90b040b03070503061302060d05070507020a0f0b0a140c0a0821040f0f030c0b0a060303090b09030a02100c080409050a0515061b0309032b0e0a050103 66
    0x200e11880782c154000c0c2e00090604000d001d1070301b0405002501c0c4501d001c07080c107041c5041710001c441203008500081100c2c0706505246141c2c5015040301c0c403045040c00e0808034054540d0143c0000700b000c10040000d0a07070358400300419900c0381c0001a007154001b44148c0784c448550340250003c2c40c00316085075103042d80046841011401550071429412980515442e500c0d02e80b01400c0f01901445080b001c04030000740c105200500c00c0c540000d0010b50b01e425464000c0c800210765001802140052080700c140741d50104000c0d000c2d0ba4111904014015a0b0f030381034075298090301c40a800c903000440c0c0060001c050b038103e20b20443d298242044180e55209121107002c04c0e800065402c6181400007280c40200391030b468100042d03140480f07081201c0e4800003460004d41d076440001107251a20f210072410b4041c02a002e00302520b040402e0b03250700120108940040b00d00c201410591 = true := by decide +kernel

theorem cover : BRFrame.Cov 854856115 855035971 := by
  have h0 := BRFrame.cov_init 854856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 854856115 ≤ n) (h2 : n < 855035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
