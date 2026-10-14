-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:50:42.820025+00:00
-- url     : https://prove2.me/submissions/53017807-7af0-42b6-8961-b7deea76d5a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 182553956 ≤ n < 182733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 182555206 1250 182553956 182553983
    0x30c0304030c060c03020706150e010e0a0906050403080a0f0c120e0c040c080916060c030c02030c0d1b0b0c031b0a060f090c05060313140f03070c090c050f0403 70
    0x500c00e01d402c01c2e0442d4402d2062110201c24280100650820541924031034a03201080c40303101e45a94100381160743d801c1101d01d82da0320b4070369110645a0001c04002e44503480e0282c10001400380c0c401d030b40c86188640c071004107908201b00960101c40003106009450b82c42c0010000c0940d4100103000d041d14113150300440d02020010308a4100380300e4004440c1c01c07a04003080c02548581010005220b041c4c94001c40e0482d5890710090321440880d84039810100e9844200000441e22441240480c2800030b412151607034101c0010520941e04003c0c1a110b440652844d0000304030181c98070001010152000f90810b100000c48507141d1041c0d009110700d1202c059070901c0c154409108044100d03410000420910140c90428005000c0024003250428100800466103185c00010380703000c0d90345048441d541c04000e80d1039801c0c40c075000052603500e04c9441c03601c0c0751f00c0000f0001400c550b0302c03490328200c01c540792803280c4060700c95101510307080c0b140510a1108110a50059504480c2c00885040d41130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182556456 1250 182555206 182555213
    0x9030901080606031017030304140601060c0f0f050d0809160605090409061113090b04110304122007030209010501020a02092a0706020711041104090515100f020f070b030c0304 77
    0x20865a20540130404c4560151a0010b1b01001440c440c0c1c0c0a04000e24142d80802000c0e906c9034000d0281001081d50442404042030300407174610700e07480c468401c0c000d000080c0c1c0c0f911882e025029000d40000380081c01040b558501c01e102130544036208400b003180c0c6508041e006044c501820ba16280159564842e00c0e041c00f003540c00041c2082c440802c00340c1d0714103c442d00303004824001d0084000f80782c104001e096160a0500c00e43e04490700214802d811a1501e03079403c8225202d401c910420442401045000441090110805204c1d0400140b80040c603610510001410584c4058150340003041d1510150301d07041000ca03488480b04042d50902500d607402610204040074aa42042e0720110340a010004035a00a0450034054090402c000321110300b000141c4505819100b8110014482001880840e030032054200c0c030301036400000d000fa075201040440d80e035100808000ba542102c1d113a601501440080022150b40d0058000f40307090049039041403102402a02e5003000000009091 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 182557706 1250 182556456 182556481
    0xb060f09040e030405040905160e0609190e0303010f05181b03040c15030c030e010c0203040504090510020d02120a05040201092304050c041509030c1203050f130e0903090108060603 79
    0x17901e001042003001d401e003820a00c0e9114141141c40d00101c82e00000800d4403803403140c1c0c80d48a120014084c0446681c2d000c041400f001a550003445030039211054144030300c1d024805140a0031100031035000c100e1500042141a000e10020100c1c0d802d01542885a6640e200302c0021050040c85445036580d11149803120313403080710b41d00152289269500703490b440f650507000000092402d640510010640c0144c0908032074ad45c442c4180540c4c01000100007500701070301700400d500d0088054031311030346070b000803002079174008240742d6203142d030004603e91f264411464068000c91564020415403805900103041c0011038054966040b9202c0290600f4070480c0d020702c61100c1c0c01920034440d40c20a4600c4aa45400038001c542c0c0e00d0a600010400c1d00b441842c51008482d0800c82c00c1210340c0c603103142c4161030044420241c04020080200d0045e21110744000e00c00211402d1401c5030309450319049501c080c0c8064100501600104072602a5a0340700003a5078101104486003692070b156038404060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 182558956 1250 182557706 182557709
    0x903150403021509010b01170a1401090b10050f070b0a0612050a0c0b09090115020304050d0f0201030f0b0603061323010e0a060602060106030b010507060203190b060f09040e0304 78
    0x49440400040108241c1d0106400c501d040b00c2180070f41090311002406800d13a408005072a0024822400001d030100b1840c003450707000400b640b0006030342c0244451b07410407000243c1103960340c1d9440c1e012000950410800c0940000030600d001d500f0402e50a400203171620400c00040d20501c6640c0103c2c5500a49912003402850300c01000c801d00d680070701d4050307120305912209031400721a04400065000e16982107a425180c010a0559240c0c00c0c141c0721040c006d0031042030411444140300c040f8650300e8a03410080468015056031301e040d01181b000400343d8881d20f803127810b90b030b0508640810940f507200583e9000501200c5052820482c404850300825680040c4245000d00b045d0700000350424002149c1a076030341243d400b0855407008110020703a000c51003880c1c0140e0040004101c040e100354082d41e4000414501349151503802d4070703540160303003040d1920b020b10748103441300040440030b600c00d03d0508101514042d062000154000c50b0724068150594022a1281605002020180b00700d40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 182560206 1250 182558956 182558983
    0x426060f013606091409031c0e01060506040803071106180405071812060506060310032d0605190902030606040c0c0b0f070206071106060f0102011509021e0313080903 73
    0x100d001d90f136141500c081c0107910884245042e105000c070b40620b9002c001c17036800f000b070004da84c245681170215000c0185100440c10425559402d00400d2a989120041000342101c90046484022a041c03d01884a841c095144900010003004d011400740c0c0003001c6070344000b12000030384c40c4e40c0c003581602c1c66401c07482100c203c0c2e4030548000c1803905070a0b42d440b40c0c1e94090b0790200f0550f640c0c00180700c10f42c8400c0e02c034010300c85030660003000000c41c2c00703411065040800010403200740d4291a011850505414200c40164480c000c005070081201e200740c10740c2903001011f00c020180b54022035105c88025041c03d014070307218501c6080450142e00a5503000fa4030102040c09032801101007022424241d900030018000c80c0f012a10075481418030340154000000500340302d8a481003041007010076503214074195503c4401c0f108106544070400402416000005a5283e80b02c409040c800ca42c40301c10503414540920034040e0b000300280d800d000c0035510580a41d078032124400020718003c40006d044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 182561456 1250 182560206 182560211
    0x70311060106050a02010e01050c160201140d05041403090a0303030209030f0f0c0901050111100c03110a03060807150203121e010f05090c0403260426060f0136 70
    0x2542e0354054000c0007001d20580c020003030503948a51490a139401038803050580f01080c0006000c40b04240302c42e1040900c14105100c0041c601344c0072441d42c0c1c0003125229407041c0d503101088140040e0b843c40d1040b418224001d036160041140021f442110b16010140805a000c1030b210314a460400c82d11446000e88000c8508140070412a10355030303200313601c4490068030310342c0c00060254011244111f40340e071000c02800c000c02e42901801e00800100c9007200425886140f4082c0711110240240040310031581d0106019060860061030100194010003044084120003a440340d80402035500604040100e10720540714420a03480300b0b001c1d80c1e065403103040350324000151b0911101e2034004030b44040c1c903098041c2d03440313a5400c103c50040e0710014001800e51a004582074140070038250944213580c4d0054105503c031001d0321500c200c42c0d4031107a01c00c0184038884080003400c00800da03000898184400d8a98188000c010081030010841c841401d02800341000d0400c401c000514650b244203002c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 182562706 1250 182561456 182561459
    0xa060b0c10140402030307030e0307050a08010203180303060d0308130203030f031f05010504030204050402011106071110050702190503040902270f0616020f0301330f03080703110601 80
    0x1038503119001c40c00044030491400300750340001000c08010350700c1150000c014508004542e1400e0741c0b01c0100001c4c070707585400b502e00086905e50744e10100d503010740101400161280303410311721410340500f0111200c0741c2c0d03071040c170410440d80c0d42c1192440403280e16180c010015200c181840e00e00020030907000354140400326290b80d04182c0d400140d8403070104083c1900a0303028000c41d10b04070320014003410380007031020001807026081c00d400142d00705206140403024155210402820104166041000a03044803403008801208000840c2c400308162010011820040f40103075444003446800c0c062002d4034208078007804001c2c8207480040a47d00b409641d02c824400010310482c1e06a001d00146035108a0342d0100c80c1000b0300c0c3d1281c0d4800141402d4070308501000540003180644908a91020704000ca00c3c1d140e031020b0291440a001d16000100300c00040340c0c94070348503420300d1031080c1d4810310030008020f1107441102590840e0f42125005540300d182d41400c559114602c0903a03035880c400c0400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 182563956 1250 182562706 182562727
    0x20906090904050d0906080f010603180c030c0609050604050f01230a031401060503090d03020c0a05070e04110d050316110d030c02240403021002070305071202130902030a0b0a060b 79
    0x4501480021030f0fa107645c8a00e840700001c1d00c0041e01600c00c00800002e41005000050295004843d41001c0000000c024072841c0d030b40007814036442d0011142c1c00300c905401c01c20303140c1080040307014020484140e81407600b0000860003090311003c0150421201030350510101031000080e200404ca4a264a550b541c0d50a00c041d002d0503c034a40a441d0600c044000140948a030f0141c034000d00301c0c035010b0468210040411006508444e660440d01d01030341c0b82c4400040c008001441c0100580070400c24145000e04012031090002c01c081350182c03100a4001000801c04811a9074410181c08134a00c61240390404280402820315402c0d080311a004040080c142c005009944c3d2520851354240b4240c02640600c0881d5035030fa80e1002c100009010920040c64542c461120855061044809190b540c0d22400e04d04a620340c000790100010085101c15800c03c0005400882c007040f6051180030b00720790200f0381e202e02e00d81c2c0262051403200301040c40c65040d600042c0083c09440f240ba6201e400400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 182565206 1250 182563956 182563963
    0x23100f03060b090a0b0d020d170408100605030115030b0a060b0c15090313060c080f04181104051309050106080d03140f041707140105010f060e0d110402090609090405 73
    0x19070f12030030041c40084d40b80c00309402400c01c0358402a0001c43c1c00d110356420f11007401185181110202c03a0780e00111200030310b1031b0241c40280540f60040a158001041c2c2d94101e80c02504114000d905105840700034a40e46941501284c1d403240704d6000d40e0f5200c517030000081003990041c581c0c810b80000d0003d11704000140206600d180c800100021307489208909640c1c0c803072000c1b0300c200010741c4c0d4001c1080320f02542c0e00c4444140189030040c035249a030000d41c5503da00613088451554060030068041e51483d10540d00e90000c00b210711450b050600e40094500100f5241e00044207440784010807c1220a40080005048a2080b501c00341c2841d82e002c2c000d0507928809040b000320641c0080c007800c19040d0320758015500f0481122074690a0351110f0495806070400391004c0000030003c564100f400d201d45402020300c402c03031440d1035083c0303a170090418540c503040a1062050304901c0010501c1489800b001407000c940c016070746c0f00c2800100ba00742c0031b89600f580d4030a0204040206010380030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 182566456 1250 182565206 182565221
    0x403080703080601080411120a06020a09030512030106090e040312050703290a0605160b1608090309090a0c0c02030102070c140102030304031b06090803160206070323100f0306 77
    0x351940c880a95030b20b001144c07180c03406c0341c010b4040c0c1c2945042900504020f0400100102d820080d11005881c1d61503010903079100c80042c82c001004040b00304284a414041d02100101011085246516241009190003080c2c0951084425804007040c01c060082800d04007a1600140620043c608840d010300280f102c0b40030034020952a2041d09402c148068117100245402001e00440030309007a0202c0d035540019829031a00c201e8090311a0108200300318091160140ca440d01082d40b014910082001a002e45070480d00c0e40188584c80483da1000c0c0800c0e809554507400240c0022003500480d0036011250019406501c00030f50001800103440351902681c0c0300e0321160b40c0103031020004a9891104031000b500040070200301164540811400c5002a400740c00e000c0340070b051680b200e4045034405c1d140b02d0f070100310a02004105903014400280d0051403800d040000c20310f40c1426014021410348420105840c6400280c0c107030481d540024044c0c2413900d09014241d0f00c0385002d20051140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 182567706 1250 182566456 182566463
    0x8040b070c0f0c050f0d0c1518080102040303030c05040e04171c05041a010605030c0d0b12030315030601081e2e0f02030106050405090a090b07020a0209090304270207060204030807 79
    0x134020b01020501b0030b030140700c0d152580000050456407030b059031040c02d50341d041c000030100070f000c4224030400130400c41142c015001200005070784900d503250281c100c480f150500741c03c2c04401c1c00100f0800c0124540503502580089810103150300d0080011032074841e6850401f18a4000c210000701e4800d203134072a521841c4564803100315800d003104a0003c60509100f0f0388001007042000801910404024200038075020310003244c242519800a8250301c18141012a00e62000c4101b00000d00040200000203400307a01506195042c242d84949400900760072407503040352200100e411840801c81c002e1292000f4543c28104084804070b118402c0307007001c40c42800f0707040080b200420002407003200c0c102c2d810f50301c1e02440d00b0304d407409014040000411640c0003640d00c4084001103002044600c1c450f48041d8050541d24210b0b2040100802025004460950090005001180c04250284046041d2080b500c1c11507003540c07200000b134401d0f480e000b880903001007000170421000f207016088203440f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 182568956 1250 182567706 182567719
    0x507060b030304080a26030c0f09091315060303050306040207022707020609010e0607030b030a200321030406240906031703070c03080a060509010f05010806030a0308040b070c0f0c05 80
    0x140103076400032861641080030301b200b0082020906101c155001020300c28500c2c04c3c07890901110b00001000c2c040200c40341a01c60340003001003070400040c43e00305800107040c490b0170801386066450052060000070a000e01842c0d001591600f0766030341342c4a000c90400403a68031030384003080810240d800d40050710040058852100482c0300c0035010b000303140501c405100204500c1c5d94012088016003e02c03000c00784c042c0107070408400800c40402c041d113120440346040e4040c490111041c54074020400c1c00c010303420368400c0500840c02c03040034126a0895000100420192048104110080d00900f0700f003091120300080024800343e20f4215000b128040d880181402d4800c401198403840116030440000d1040010000060700031032a141e00850354110008030244c640700418821034003038110310052920780b0410881136a1040c0081e60100742035025205070140c41ea00a020b01201030401018020002d00250380e1328411022800c1442e0041d40000d0807040c60309046207416a02d006050180d00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 182570206 1250 182568956 182568983
    0x13150e06040608161e0206060a0504060b090405040516060c0c09090503030420061c110a08150301091707030207061107030611091206100f0f060507060b030304080a 72
    0x1400005807002c032a403548520540355601c0c080401c2c10081e070000203041c40301110140c0d030910001580d03012045050340040001c3d0402100300314445519a00c45403099040c0302060024400c1041503c1102100351408209502d441c0703400d60030104011300079aa0100c605200207031072648466060714560103000032030030300c0f901c03295940d090b01d20051003e0120360007007000c1400500c00800f1041d01c0b00c01c1c1c0031000080903c2c100020030a62081c12840550324003031000c00290b41461050328610035659504d6490129145009405103000410031003c0c00c410340903440507078a007900103084650b0b000206481c1611840c3c404480d582154034190010303c5400d40208080d03018540c542c0d6850040f00080c4191440c60350360001401c48034001000c41e000c1404851441c0d15400840004505801c020b0119481d04c0e0301440124290b40c3d01103420342c070380324108106440050107544261401880c2072a03481e04941400c0c1c0c041e02d0105c60050705840b001500207030711034010540394140c41c800c003102c80501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 182571456 1250 182570206 182570209
    0x10503010203060f0108070215100303080f0106020a03050d060504020d05041a04031b0212060c1b010504030504090f09020a080607020114091b0a080a06020318030a0c020105090613150e 81
    0x1e002c101c0e216074015400310b0803408150700960510360301a039144110340341d8009030306030045540b0342a5461030144c501008140100340d007018481d58081141c106018140d0f00d8514004e6a5030744c1c60f04050300b4010002400c005800780b58001c070f0044c2c400640103640e526503500ea01c1009201c211010389001002c0b2441955107020001c100d4060b540507965800058143d210101d9020141e1108a901c41d00d0442d4003040c1030014028684203851b44446a1b8030340c00340014800660110310190800c1d41d1502e01001300280e00203007a1800e031005400c001078401112810400144030000000e58440c190540c002070303c483c00101c03644540d00c158000d01081080c10a0220790300c0d010b0703030040c0b440d80106d00485040e521042d281080c1c07110050000e50401d550720411070521500050a542c0950004104445099079142098400740082c00540c0741c0b9a0310741000f040b00008060007410880c000540180a55944081d80c020300e29500070703244050b81c0c80d4a00524440c802c1000b00220f0007e50341c2c1c0e9183d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 182572706 1250 182571456 182571461
    0x203011e080a030905011103130b031008070b0a05030a06091b0f0302040b16020307170303041b05100e04020c0d030b040b0f060703030b01020a06020a0c021201020418150806070c030801050301 84
    0x1031070f419102c0039a42c5003003100540e10081d001c160085030f0310080c010b81d07510145030f002d618000d02020850f10703a02d00348004d40c09021101e6407c500110352003014100b0002e11058210380e21039005141075a1030340c651240e09806000103602c101d01007400e11130304004441c5980715070003188003180c550000c2656020303819400d81c001c601c644030481600b484060300340541c0804c1c2501c0c862004060380e400ca61100310310b40c0c0d04c0d240011035681c20350011040104000c295040001030390355003d00c056031a403408000410300c0f904000080c08010100c0304400441e25140c05980c400c0b1489800e403440d1003c4100b000f0000d00c954464184a10b082908000792030414003800f40310b9810150600e407030315500c1c1c0c6080c2c0103400118070003411407003000030540115040e48050a0403004659541031094080c3c01001000401c250503282140d10402c81003100b4290300340d5848100c10301c09030100d280700b10459032900803112075000702e00718081c440801c100c0c0c50740040301c10345a600c46d4941c42903d98030f44092508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 182573956 1250 182572706 182572723
    0x150501020703020f03190305070b1003080f0a020115080d0e0d030f080c090d060e011a1c020303070b10050108090f03090d2301020d0c023c010203011e08 67
    0x258200031002d01c054185120016110b0002508640003802004868901032241d004183c0004101044034020007002c019141d030809401807801141c14156201c009441c4101514030419280008281511318002c0d00708201c003000991034284080c5d40c0b08202c41e101e42d2520020400140200880320366454076100707070054980c240e43c42c5108050794140a807640c0a0142590b08002d10500c200d41042d6116044d002c100d0b40b08450206130300a842c0401c2d402d50f0303a40401d0026044603508042c8041d01c0d210400d50110000d003c0100b00f1740580e0010a08511418501410780840c030000c2186048540f40f0714000c0b291300303a0340c2e040329941c1c1c0140d8588a204a1490480c00e0b0410060f58540380380c0030344400000340c0189001c908405060715074a11180c1d1034240000c659401044505601d00c651164000c290403900180c0031141d5403035002134034a80041241e05140a9500758690046100354003400d42e1103441001319940d584807807503100d01e03e40d9070071480c001c03a03030788000800c04c0d140c04541000b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 182575206 1250 182573956 182573959
    0xf051f06081b21040c090c080708060609060409090c17030703140315030102070303060305061509041202010b030303040507030507050a0608060d110604060504030c08010c02060c03060d0b07020f011505 88
    0xc2c103088098003441e841d804050342c08400c0c0c00703844007004000d6000391941e000ba4400d184040c0382c5072800c1e40b40401d452080103980284440c0b501044070298100c0207030b540c01341040315000d6984820400003000380c09990444900031780b5140c08881040180d411010a40c0c032221074811b52002d074514025500e01c10000c00400065180d0380d407424035074181000c0c582040413032035a14411844400424226000a14203a0001c0c0d04d6100070001c1c84010b20605404c0406250b1642c401c0c0d0050b80070035540000600000e04880c09c19403560b4206e4070130351003013000c0200181502c0d500d0900c2e04007a40e885165005c00d80c3e0b98041c0850009480c03500f225018112072450722031030200e0340c8450400c5502c03d0310a00a0f980c940d1071078000010b81e600c0c200100040e00454442540b0b8504504002c0300785015504030b118075038904401c1014940d00080c1c0541c3c40328002925507901d54409000c6400101c0004004142c0703841d500c02c1c821042e030082040343c05680f401000300054030214180d00d1f0b05030024130480d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 182576456 1250 182575206 182575231
    0xa1b02011412040c09021e070204090f0302011a030c150c0a060510030b0106051204030e0d0204050a0f150506190e030105011512050f0613022203020112020c150405010f051f0608 78
    0x10042c1444e201811b2351301d0008000140720b0129403281c40600026800840060b50b4134850081002030110b0380c0c28900c0425030081c01190051404142d0f100c9151011284144000c20f08401c0050100408610f652340003105010b5411300b00e40c40c036011451030000700e034030620b010b0011414a10842c16074544250600d141903c64460341c03002e403412040c803a9240d410964010114000d82c4640c004c50740248001b20f000200e408d6100c0f40c602c11140720340314002c4010740001c0704010598400090720100b000b28416404143c1c00183c00b0340d24052780b61006505942014000a4480c4090070281e00440300d03612804032290b240a072080c03c0f100121025900c07000c400010a01904094001c100d409200d400300500d00300c0380720f400d0611508200718501454035060001d00865900031410102107690f88801d5040c03059069883d920340480704400f0740801e0224000400b804400d4008119043d00c0c4081003001e03090504910843c85560380c4451105885480c0010700c00e440703031038558800d00c00080e10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 182577706 1250 182576456 182576497
    0x10b0a0504090b0d050109080901031a03070b0c07030f0c09050c07050a12050f1b0f210901030b060c0a0b16080a0f0e1c0201110a1b02011412040c0902 66
    0x1600010280d5805507508013110707001040015909200306585903000d01800c1d51610b0000000400b583c80348418401004603807491100e150f10005102d4066411200180b502e5940d0111120318040f60ba60018000d060024812424000c07401e0f040c0040da500c03854180481c0e41d82251418107440741d114002c200e0340c07240390043c020415558078804510854900390b403426581ea840420780f50481a40c400207507028003240d41c01860200100044150501c0240015a10b0b80d207140c0f8058004a0100240050010344a08568425031101c026004001c10b49a06d5a1507070150036910140007004031080c0c80c041e401f08a084405000c035105403a1180d41ea2803296884844540181c00c20305401842107032070b1100b440300306605011020045948050807150301014190007429111400e00d040081041000025409580300f14003903103100324038240044a034600d20048403002124030b143c0200d4a000704190218076075051020340181d006100c190800da4407412604c1c2280b05403003440c0700c01c1d44001d14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 182578956 1250 182577706 182577719
    0x901080402011202040824100e060a0b030a0c030e010e0c01051b0706050705010b0108040c0b0913060909050132040f021c290109020c030f071a010b0a0504 68
    0x516660061040c9040d40200c00f24408410913600640c00c4920550805c00391105034514051100780d0710080f400060b400c40c1041c513041301e1504c1150003103100300090100040d0640d00e0f0102600d005100d009a055500e1600000b80d0004154190007000002d0034004c9290041c00b050040540c9909104060403030782c0540001960350380c0c400b801050204104202d4851201414080d0b40024540c035225036554507941d19044d421280f40d81d02d5541071041078410710001c214000514002da894038000135581e5040140060094440300494810980c02c00c503000c01c20f8040c58001450440c8114005e003c5018052050145e5105542041120352804500c028040300c0900382190130034000c0e1401e0820840c2a00480c2158a00c1044008200d12a06491040004c0c0c401c000c8048011a0350380ca658200c1c502c0042d50035a418400d0005560f000b14054081d5003061040f201a84100c12400356903038218070708101c1c20010301c0701d50307265242c5100c00050b500c0c0e10b400403603240500c182d0303400d460503080c002e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 182580206 1250 182578956 182578967
    0x11407171b030c1e0f0705060f01031e1b030303060f050d05150c0c010501060512090a030806091012050a23060703020a0908060f01090b0102010b030c0409021804080418020f0901 78
    0x13080710603c48807181c40340000707185400240007200c1846601d0b5512880c509060349007003006000c403400b410340b0070010008070f65483c41f0102c2402d4283c0b4402c0c060441810248078013400300d0014611401001c0b000800c0641650240342125120094900044d82c1d80003080034a50b00100003508503085099561042118030300043c3d4048004519941060701924611742110426080314003c11400102d503081d2140f403071910380d40100714030001d020a100a80d030050050704080e1066000301c0fa441d020482c5914240700b40c42c090240081c034112140200e0800b190740ba80d1010058910820502d08a1101200602428499110702c00105803e484440741140203601882d079010800c0500c0c0320104040105120403405050507226510107541003120a41c22100240015419a0724240c001400f82d10082000d0071080e504840008403607003103001081204000d8990000742411490400c400c0101041c0904180c035030024110608208680c42c910492182c2d401c0465400014400c2c48655031044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 182581456 1250 182580206 182580217
    0xc0108042a0b0406120207030f030522050604060e0303090604080d0609061206110c101116050a0302060f0601120507030e0f0f061302060912011407171b030c 69
    0x200329181c0403107000c90003038105807001d800040300715000003020082c0c90303440034000140280d07240c000c42c07910740255005800010004c20f9a4107150304d52002503400385401e11044043c68082c0410580b0f0301081c5096070702d0303050489044400c1850500c45c05c50075003002069034480ca02c04402004181c68030f440b80845600406400020592500e0011886e001c107405650006c08058030b01a2107030005140000c01c1d2100b078800110000f02c01c2c000e810f1030000002d00034041c0b480c0144001103003007044040321079030f200d60f1032141808040301e4410710400034009644402c0700e0282e401d0b11103507160102b280710001002e41d030250010f026601c10180000b035036800300390400840d08000603d403844c07003821810040038861148141c0c100010f0b0f020f241009001079a80304a100d0340741140d141460b40001c1060096044203802481d02100e103800d540b40950100100480c6092941694a8080710050110740c1741a204802e40f0340c900c01140054811240150340d20348044601829542d9100100000d43c124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 182582706 1250 182581456 182581493
    0x403020a0501110c040f090201020c030a0809010f0504050d0f0c140312030c21090106060e090112050703080f0424170604060e0c0c010510182c0c030106080c010804 72
    0x3e24030211442e680d58486c441411442d08400701e06002c543c000a804e020083c10f10502940181d150040010110b0048864000003400e1900e91110209400c0303600707016a030841c40e0000348282215050164290071a80000d2007441c0404045850b4800403070300040d006001901340e0b1124070040d03400e41030040590b520444001450b81044100491039401c502c0711003103203014100310804d10400c5070082c040e1304003034205070405603c0f110b8004045a010303101413043d034036040a08e410400800c4030602030803000b1500419015181c00c010403101a0b1075200d80320703d02c0d00c002c0d10240100d00c000c0c204181240400c07180c8542a0501351003d401803038840090200d940a55a80c0000c181c100b00040194061450603443e030b86c4600380711402d9402c480004e4070901c41c140881c9020020b00c00d503600800c1560803051004911022081e030003015220ba40c1c0800f80d9140f8100680e048030304030001e0b5085d15140c0c1203000340440d03a6142c24558075129580e48050010f0700e080c0004011071401c40350041c200e0030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 182583956 1250 182582706 182582713
    0xf0e180a1e05010c11010e03070f02240f09100807050d05040c080a03050910081b070606051507151a1207030b0906070306050303040b03180718021e0403020a050111 72
    0x22a0780c40e58215103120070108042012901c0c0b2445c0c0c03403002d12440186048001c011403410250f503e0b240d02e030802d0000d00a219011101404603941440940c0d03002d0241c0c0203600d036445d891980c000d40d016030003400350580241a1030080d03440d403a205840841c01188a83c95041c6441290076512025041c0240241c9000004010000c0c64680400000801601941c0c80b141c40e0b421203820071505034400d44e584003c0150010610100d03d00c40d00080a14030029208140d60311141d15000d00603140750b60290b07505c501100c164101c452040c100607c071180c40b400001e901000051424411900c0302c0b0b5841604400041080216007817a03804010044a01421140303075558a035100601e680c022902c4141c190850000d0014440d054003859010340401c90266051500707248504609000042100203414a1544040c0034080107103d40b1026100745040d15420000c00031038a80a940300e03500c034089103000e10346410314014030340e800d42d0f0a23130340d0080c54401c045240100444812a454800980501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 182585206 1250 182583956 182584013
    0x801150e060c01020702010e04050411010c03021c0807110114070e01090306060b09150c0c1314090615010e031507020712051b010c0b010e07180f0e180a 67
    0x141e40d603000d00b5219020000142c1c0e0b4a0180c07000502c00c21000c02c506010301d050030b0611001404554010120080c02c0c42c21800341d4096007004c80c546080b90b10007129000b20709080707022059010404510032007403500d8000f600d01c20004203500300c8921b15a00d101c2c6001d05004103100350b00c9094406148081458407420280d03c81c0c55031412102158000014408002006c907000c0c204281c918041502c4507807103a00f80039441c41041d44410322150910721a0040c590f40555076440c3c1d0740600c42595002480c1c91081c5400c429a82d50f502003a41c140c00540e01c901007079141c542c80341c0100214a0030283c007400070761080c56481c0720b01d410040c105a041d80075882c404141c814980d80d0050b0024090f0008280d0a07944100e40754644c0d5540821504201c031030b500035404642d48001c118110781c103d10200e41c01d60703540e50b02115800c040c0504100d0681c1070380d100040200b260740c2650151840001305101c0f540b10150880b00c900400840e00d05203402280c0e0341741c003003000003403135a030710703611010b107942e0f074070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 182586456 1250 182585206 182585209
    0x1a070b010b09040f1107050706050705030405012001050a0c020c03070f05130b0306070f080703022503300c05120c031b2b05061507060b0307060f0e01050a0801150e 72
    0x5501d0720070360174014440429200240318080240600610030340c2426854000d0b01d489090f02c0303104d14000c01c0d0500441e2545962200900120800d41e06080c5000700424100500c4034006001400e00b0800148160a0b0031000b0b40340c00f1030550100c2d1030b40300302201010b01d40418880c07034032004252507400683d9240e414603103403000e005980c030803c0180e84544e245000c49502030000040071740300304100340c4148008020700002d074003500c00740d411407140215240803038601110702c1207a509009802241c00040712860400742c80d041c4100c10a100e01c1030091050003142211746005100be003840c8034001d08082110b60000000960304a4030150910243c81c181c03000c04001da41c00800d0003483d02c0c5800c080400e010001c40e1881c107000c0505602804076083c0341000440495051450107411980064a10300b04a410fa02040385040060705580040c0d0362000d015069054a135007400110b036040421280b15032260084900032140394494001c16402d06440301c10a11303003100e410003071060a42201815 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 182587706 1250 182586456 182586461
    0xe0a08030d050a021b15010f0501080a0e0a050313050307080a02060f0705070308160b071103220e0a0c020f01020304031e020a0f0506010f0506071104020a1202131a070b010b09040f 79
    0x2505d14807401400001c00e410300c08040010140c2c08170350900e0900d282840580e030f10001c4550800e09460000c02c140007600401c40c100404e4410080403440000b031089600b98104403990308035002281038078843d640c0d074445203482ea000080001d43c0101c00700060040d042c0d01c44085c00310140601e00700d98005449503036040f80307680f00800c050000031081107050b08100a514445034030105600d807218900503a01e503190360b0790040104400200720030288007445000360020140082036098101c03500c0d410424294402059040701a10060048a90040411405000311703800755606a80700d0110046a40c28044c0303241d41c80c0c0c502001c41c05039550b0300c03021840240f4210059401000949103d51400f1280c0c0c00c2c400c0c00d0361189029903404d00c0300314040b64001801a80880e000d503805039840d900c0280c1250100034a141c2ca415940c4041001e925049208504805682c3c14803085405050407a056200300d000b03c50000380204a050300501055901c00060114680094400b049020b02c000100c0706 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 182588956 1250 182587706 182587747
    0x5121c0e010510051f030c05090d06020702030105090a0f0f0305040503160e01050307030c150e1e040b0103050105090a09110402071b0501030e070b0f130b0a0e0a08030d050a02 77
    0x1280c0e4480c810b00800c0c45003c0f00c11401000c045a010740b180000e040708101040d002c0c03400d4000e044d5901d600084842c080d40c1214a40c2c0c0008006520f0030703410303250040094001450583c001d600e03220008020a600080307040d00107800401e80d6503183d05507500d210011034005011000c11005000004003a00e08001010900ea07102a02c12011828040b141c9882d020507071150780b007940500c004001081e100d000034800d85503440c1d420316110032003403029203688003061440e035003207024000030651510550040c40840041110700348400800c0800450544030f003030069581c40440039010403612041603000304005449903c10282010304100080c0403a0001481604d407103e24902804058a0240c4100003801c0c0900b400c2086d0f42c6a0b00302c80707551300f02038050610b04510000b19500510f0401040c3c440e100d400d400300c10074240d110f55403a2030030b40107180880c7c04500d120480310450701d868000d000644580d01c001f0750501d41a984460090440641781c0d1061503420841240083c111440010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 182590206 1250 182588956 182588981
    0x2060c0c03131202100f0e060c0c1f020601050d1104050907030605100602010608030c0606090c0403080708040e070e100c0c08030a030c0f0e0a1401110607030f060b040305121c 77
    0x1103e089240c018040e59040b01035442c010083c1203c003034012141c001ca454407103040251500c5890b080000c0c0d0551a100b2030303103000392f8011900e80240400c0e0b0060154100c098030030381c3c00e03101240daa0340300703202c0340b074030341620040c0100c0c403204070907000d8207096010590190840e001c0b24101507070f9440e40c0085400c15103808004880210050206036024000d4200038800312009518003105070b2007ea4603510f01400c1d40744107501050104516004450950b00a5a000a691b558403026841c0c1a40c8a9100e40300712110400c03103030000307030455028103810217420b64060080c1600c09480c003011200b0f98840e401c1181c00600018011904000c20406400c01020a460000751907055000141c18034014520341000c11243da40302c40c28940320000322504451600300303a000346889020044e20907440c04010311880d481032900300106c141c0d150708000900c00c1c40e000b08100300b6880b035101003064465130001030029800928040c1c0e0b07160340c84009001100c1c0001c4505940d0345800403b50503240c0e03552115 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 182591456 1250 182590206 182590229
    0x406142a07060c08070209190f02031e0603060406020d090c090609050c0408070b09011e0305101a1905040b0406020d0e0f01020c0409051603150510050102060c0c0313 73
    0x841003000100080c0000e00200d0030010340314a0b5035a02e28109214040d80240104c14040200b00e5400d07180088409100512409000302c1c1e504045d001c0094000b21280c06000b41003448402c0f1110714142c11a00a04000d4043c1c841c0e541d07070b40c494401079448105000d641c1076542e840c00c004110346c1d11200d0041d00c441140850340340e1800d0315030010341e04003410103500e202c0300300000c008288000403e101261075130065940c03203005010042c0c49005c240d00b150880713400d039800c41d41c0e0860740c0365110318410702420b40501102c0e51101070700c239060a544840f01101000412849070041d1031744091400d041c81c24076000e482e0a498004408560308070354005000350f0700846c07031804501c0e000801221080320030346041042c3c10081000035604e401c2d00004501437640ca84c00c400900409101c0100210000c071206000d807a903c1c98030b808008030303071103091030940d2034a0007140e0a0007001a01100f1100143d000b000d007074845c61a407a6590b841800c05100d60311041080725806007400c0d041c035000700402c114a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 182592706 1250 182591456 182591527
    0xa030906050f010815071b050f0607051c091103010e0303070206010524030613020406020a05251a070507060903031d060301091a0a030b060123040614 66
    0x4801d8640182124924041d03010060009441c00101078403100c0700283e180c00d0944403840240c03038403110130308910711a920306c0100405011000402d20b204030b185008560b0240c2d68103e0466042c002d00c844100080b4105c5101020041160050030401d4000d002d442c1b0502d590341d000a084881460710b400c0345400c0442005441901030022500608040d1a50141d80710010b12200301d04402660003c03010101002040c4240c40e031028213091100b50790021551aa2103c0000e55244075800084a06204011042d9010701044d140100c081c0c1c1d4501d000b0030110700b8450028401e900308004104c02d85414011305001c550108180c100410340c0362a078501590440c14010f02820318400a01c0c8800b21402210a140e160241102e044400c2800300003048040e0003544c8400070a02c11905074030601d918000700038441c0300b00d0011b00406003605c07a81200c5070354120240340e10701400d2000c500c10b9801e020801a15008036070081c3e00e000c00c0589103292400c401d0440c800c04010807128810030401514 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 182593956 1250 182592706 182592713
    0xb0a02010e1902031b01210906090b15150d091b0e07080a0203040308071b05120405040e070b0d05060604120c1a0c03030a0209040608150405070902030f0402010815060a0309 76
    0x5c1c00d409003912408003607549030001801c070020041b00081489812114405084070070740c0701c07500059000e1800d000151260812513129042520350070302e490300c0301c552101d0038588044080c81c2035808a442e10b06020791100480000d01c0d01c0b4806071072135001004415403440c02d1484c04405041403038a83c0c141410080c0c070040241200401c0602d44510420a00010036049800b099100303159240003001f40c0c135036004842074101c0d1500e004050307102e0300840c0c0701013080e00d0b0302a000340c40c000d8404010b080c443c1071100c3d42c3d070030759845428291207003000150300c084d9007504031582c0201301414040c9440e40d00d00a10304801d0200c0e90507121340c56022418841800ba1501c0811501600740446080440010504d80c80e84030203000b00030780540c00202d440403074503180c04c601e000b441b000040d69480054824110141101118111024090f2000118141c10140b0035030f4000c0f2092001c1d5100d50340d41e03500642d00d10b2409000780c0078440c481209232125039039090003844034405595011420760700618 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 182595206 1250 182593956 182593963
    0x1118040c060e13050619141f0f0f0302040f03060b150306210f031306030f05040f02011101060306020a020d170402090c0a0302040506070309081b0a0b0a02010e190203 73
    0x8202108102c500d404a1500356200020034030303810300182c0d000540340c86001c00522068985040191021241c500010b20316240b600d03245481901a81c0d80001070110750202d200680f4400b0b02c0341c000c50314050031065a14812490020707504840c0c18010b2425031103e0f0b00488940d2198000c4900517180c00948260b410420450700007500c440c90104d0a41c2441f07000181c0605100302e0340611700c070307202209070f144100400180d50010340a201f80c0b9903990312803402d48002c00090140d000440d00700b8040c1c101d050743c1032044500c102c0d0048002d000301c01140d8011101804450083e000c0d0f90340f1400048040740c0c5600c000e00c400c095a070000c012a0310001c0c0050a01014140181010303044802044007607110001d02030b40c002d00c0182e406a07071300d07200541035000b4061a00f09542020010401400f0507400c0501042601c0060f0308940e501c0e007003030307032031000a415a0981542040101100300180c064900c080c14110300c1c0390002040d4401c0400160b45440e070840039217211114510304460641c00d0a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 182596456 1250 182595206 182595209
    0x1e091b090d122d0311090a06080603070807030c0e0601020f06010b0a140405090105090408070c0f0608091902120307150506042909220308070e030106050310091118040c 74
    0x400c0355034034600e001c0d183d008051032014803009241e01d81e6144406600e04000722400b0403401032000303e4068031490000c110100403101c15019100e212800b0642680c0041c0c480304588c1d001c10800e40c07207810075212112420010340300e5419803080076040400c000041c842c1c14060030030314608075224041d854000b0071420b03681c10034440c069030810080c0200d03120300d62030318155003090310b114649484514101c00070b0300c03e24801901e21b0000c5000854140c501c401410201c8103941c1d03501d0700b0360310340c012200c3e2503c020f07408018082500d40c0c00c28006081c40c0070600c003010015402e49080120544520b0301d00307104042c0040c0c4e142da4900420201d850b1900c500410700c045858044a1602d080005403d0405140d103d1071165040c08002082d0b0722510100400d01801c28041c05056001c0340f4025024a800f039629101040018440107498281403049408880c4002c0040207140341e12043c00d8010251024140e44825000d2824641c43d1a0825070000405008100500514141c10030f05140c015a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 182597706 1250 182596456 182596487
    0xa030614220203060c0f040510050a0329090402010210020d09060c09050a060c1110030e0114061c11090403090f05090402060d02030a06051903021e091b090d12 70
    0x8040c4074101588001070815440f150010f40d041da01c0c00000c0312224140120360102e0740c032112501602c6d4140340e02102800815405446c140700c0d1103408051a074888059a10400300e032800c64100407160b1501c006695000f0b8010b00540d04440030001c0680b090741d002c080c240c0d4190307840354891410042148900c541030304a91070b0503003c00303041000142e984126880355000b089240328201c1d00340705584d8044840743c5130040c2540c80301c60130041d01402034500450781d48059440c158581c801c20f088210810700c0743c030005140c510601ca40c2a81d056036018580307000d80c0c00860312010920a03854800300b01d40500c1c084d40b14042d0007854628400b64040e1180c00a5005e96400014000161100815030345084814600540c495a07414001e80084c8580da01c4254810790720815140706000c0b682c4140d054a00990300d41508030504035890408001040c503903034000404d14000b0300c3d18a0290080559118045012031800040d40005000c010f0340d04401d5a88031a038110324a0300076040445d0710603107070700c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 182598956 1250 182597706 182597761
    0x102031b0711040c030f150302031f0204080d021e16090216050d0503090c0f030c0904140601182f0309010f0e030a090b0313020f0a030614 61
    0x9210218445541003040c6611544a02040440401c000c21900224400000d0810410301c108a040107014120a00104108038a040040a1020b45d000e0340350003901c0c0c01400174000d0030f5507212400c516141c21038480304488c0d403d11000c260f01c8400d006818407130400707900a0001c40c03c02c058201c200030469544aa0350703880f241d076420f13009043c0105030044687c084001a00c5080d4030360700c0c08500c0d120b42c000501c40e01584080c2496190420302940c000c60008003140c40d0b03007450b40705120324240d50018a640c140c4c054503000c0c3e910314091041c03a90043c405c4403407407a1071054001d140d2400c9800c1e0884a0103a81d00300482010405074810807050100c011076110900070f4200740c42000400803620440c22400000c0001c000b000250003800c0300c0381214a0402070902d821455a4aa0700107140c5040003a142d100c0000d0400303822001d5034041c8600320754620441c1c280b07500300541c4900154426401c001130b08400800700f4254403504098821b03010b10061145030064400010300d00541c200c0001a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 182600206 1250 182598956 182598961
    0x9010b03150a03051509160e0604060b0d200c03030c0c030403050d11060a0603020612041407091d06041505041a0a020a03061a0403030e0402040503070f030b0f040f033603020909010203 81
    0x40140a021240c2288c08100c6649540b00400d010b404150494500d8003400100140510207079400101801d0300f0080c24001585ca1011040d101e1040300140d20140d401840820040c4105900030614040b0003800ca901e002e9072560342c1801e0824084111010804c2400c0400201c102800040d0340000301c0704c41048000c0c1940e002480380d000d402c90b4160404450130008040101c0e80a089201d0407001003100d881650b030340c0080c4083c1103011402e0a45248a48450083c18000038805001d550310150783c3d607020150b048041d009000091003540c8000303541c1001600c00b441117420314022103604402584e03075042c6241c00341c155040d1350312034400c625006c01c900404c96039601c01c0c5c0c0c0940b03a051078a0041e0139014400500640526004558903014150000a5100104410b84222403007200120003581d1010362000c103106013103034041c210301080d41c210380000b8800c074002c07141040180281d80c183c030000180709041411702e581003501801e0040b0b0610540c42d0141c14542c2c401c000600035403651 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 182601456 1250 182600206 182600233
    0x100801051003120e03160315020a050a1407060603080702041406060a0e0102120f030435090103140108060a1103090c0d0804090e060a050604020909010b03150a03051509 74
    0x8490701c2c40040c0122000c1e14118aa407442900c0c0f07002c2c00c000060131a1010900c140c42e00400c0c52207031004a55040449800c88a51101d81c000c0e81c0d004405070721418103013600c107042580e8640383c0d6032134190b1000b42001000e000038a80e1180e03002441c011050261200000d2041c030003100e20b000341c013060246207030041009035130b55403046a0100c11140b030641d102c4289500141d10b800041c0f44d140503940780101d10000341502d860044d521583c020480c22032408031301010f00040304070200900c00d030071034426040c182d224040002001c0b1050180350005e54240951805560041d00fa048803040350408020320166a041c0c0c050340704a605084d980318650306000310066541c0c1d11158019000e40210003a036410300000d60140c4005002581040c04480c00328400552220703011101182040e00d84804103055052501c00c0e1030445202030f02c040b0160342007640c9407285400082c40c5403036003020640d0029403030322600d05103402184078800801f01c0891000d90f03944502c6004124469581c080d07110350401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 182602706 1250 182601456 182601481
    0xc06050c0a06020c031c0504120906020303010614120a090b220605071103070303020301050a1703070b061c030c0b011a030403030b15190f0201050c090906130606020610080105 77
    0x1580d40242e00581e14500c1c0542c00741035000b900081080b00b0b6020541e0b00405150b500607038440d034032031003e2403012901c120051b03522507018090b1400582c01032005000440c0982c0f160307076032034034a082124181203030042c9170460010b003299814a81601c44550008001745c2c802c0480c0c00001c01100380052404400342c4190070b0000760406400a40c54402003010b00d8025003400400301c400750203503aa0f030021400d001e8080c1d48203100b40d0b402542c4d0100001003c000d851521000f40700e40341d000c0c0d480c01308a501c1c1c0000d1a1800341c8000d510009015070101c0c6203141d2803910200c24400c0d00d038101006c11a062117000044d05901c4602c48006400009008030048407c4a60045d40f50600144484005020551001844042140a52000454601618050104501b401c000d6620200408440b400803400e90708181c65000002105126420702d5240002001c1c1d4448009040c1d40c0111203280810400c1d6070666110602582007001808101241c009401001e0a1100700a106030300f07000000011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 182603956 1250 182602706 182602723
    0x30f05030118090c0302100908120a0f0e03123009030715060b070c091a13090326010e0907061b030302090a06020c030f150105010f020f190c06050c 65
    0x107900383e031070412104000c0540203400285802078540200f8400106016198800d00d00540225200b44550010b500b1502000c42e103500c1c205598600d4101e10314101960042c00340074905605008040c0044501c060300c0018004600821552203114264081444101c400c00088000c06003055000c01440c45030000440324400c2e400340c8008005900c0b91650310080580d600028a4900d0000303030b00d4280010a100c0e0401e50301180e404100d10514451004008189545a190001c800041c00b03c4180069030151540038081c0c01c040c0248035000002440307c80d180316021010701030000050215004032581580d2190740f0000804420b803c265005e40001007400c54165411500d00745101090b20035015a100013401503c10400305864103000b07915075892102060081c0300b19812101c08a4000038040021000c02c4200107190b42000011903e800010102005520404064501e42c400400002d116a8448145081c400e1403078074003000000140c0d4801c2c0c04000c8203001607a008480881ca401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 182605206 1250 182603956 182603999
    0x30c120603051e0f1209040501050603070e2407050a05150c1909030f030e03011107080d0504050a0b09010501030c0902040b0306010e01030f060b120906010e010e070302070b040f030f050301 83
    0x42928000c040c965103080605001c4c55580d006060b03241074030110f100c025040b09041264284440d0f80c980040c0152030000315030940014046100d040290704008809407201420309c100d15454920b00c9107686982c1c1d014540486055200084c0c1009210003445404507214811200c01d130030341030040c2011030f80d018030b0782c0780308880044001c101e00a9004055a400850b40080018417140e0301c0d0030050b0400381c280006038000c1d42004550261315264608a8050301d50040d8404c3c10f000707000c0003410041c0300c01441200c1611a9040d2400801ca004040768420317401c40001050b65030440c507003802d14400a0340140c0c802401404140100303d005410340750720031020710308030590a0301440103c0260450b40300e0189202e1070804d000c1007001159000f02040120741c400702d0a25101e80c090349950301c409119081035509024014017041100506150304240ea41c0341c05418982203881d42d40110006990499010000c48000030400d0b03040b1542c40b025203480c0c140750b03041d9072400305290b1010f0010303039490 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 182606456 1250 182605206 182605243
    0x703120b220c02010612030201020c15090304030303022505070801140f1503120a0207050103200405091f24030c0e10020a0c080304260a0201030209030c0d03030c12060305 75
    0x70300f0310035441030005040841d010100c0d4243d41c10003074001d512105120300107020f4514001007030104032020343d0007682090002e61400e40f4584084000b5002059080218800d844a40780030592a03c3c44580243c091005088860310b401901400c680c100a05c1940842800c01000b6420b500c0c060840d500030006095402d019081a00007402e0101007903d900c454230001c101c1540385540010744e030099840c00c0c0c07400c011940c00411030740861200c0c00a011241c10040105100600b40304d04101d800c0b041e400403000032260110204c0c4020302c81d43e0498002954100000c0340405103030324103030600c9505030404200b41c1840000c024044002c40c503125004047e9918030101e298070130401d80e550190400390440020381c41d200700c1d80d103e81c4a442a07160300c031007440c0d064140b1094880b8030402881010010f05805e030310b90f40103402942010505680c10300400035040c0d80c90b1111002100303850310907035000034079208254005d00364291480d040b2515071300d000c40920000300e00040c045c5038804a40c104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 182607706 1250 182606456 182606471
    0x50117070c0203010c180806060a17070f09020a0e220b0f09090a0b070807082a030406050f130c12022701050a060f020a20060703120b22 60
    0x355525000c81400039015071078402c4905e0806d41c0900802d41003469031039040c12003030b174488242d03603548030039907010340c0c000a003000030484a900d0040e405401540d41090302d00f15a561015280d0746040342c2c0c056011142c00140308103540d07a0092182c121080125400d0040030341d41c0d400d41741100c0106440c0c8e0b40c45613441140d00f25035940d07200c4c1d40d081340d100100040c69510f0513050301501c503c1d040b40102c5460703c0200104030854099031209101d03e003117654101007540c03504041400c04d2842542c0c4005010903411165020549200451040d40112004907842c200840c09002d030100040902165440d007a40c40b42c000340486003032a044030030b2140e031501e111900d0f000052200034280111310141383c850201d80f042c01c05000c8058100c400c1214014600f41c2d036007100f40c0d450601c07400c241d40141c0100c8020300c0040c0082282540313040180140c2c2c8040c4209a000c42c1165002c850305501080c401403401803110035074000e40c5c030801403d80e144105190859100c008a40241c1500e8806903240c070314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 182608956 1250 182607706 182607721
    0x6010807121203200d0204150302070525052e090612090804080106080f010b0315060d030c1e050f070303050708030a0f0501120b07020601061209060e0331050117 71
    0xb1604120501007408603907805c10906124025403140c8545541001800400400c050191090304c03072041d0000c01501c4c4141040c0302d041c1240418402d08103020303080010124030303901c6588040c1d41900c50528541101180c42e0b0800301c8225020001904200c4240c809100c050780c0507005079480320340e0510104500b0550b103405125030080f03401c21601503107051b90003c0c070381d01c000031450f00d0003504000801c0054210002d040c1c0700d10384100703181e4640e010f100c0400c400781016142030700c1301070007071801102ea203a00e591600820100054601740740165541490203112013070010102d0030040310300600c512803850b9001b500b80d002da02c2e03000e0200b0001100144450030503410680b10071390f44110812496071241c902c0a501c5040e40c2c2d0546c0d1443c030307850000b40c20f240000781740e505842c04d03515500f0103071002c0c0d021080034080c640d0085507071a8841001c80c251a8041001d407403075070b030240b80c900038803402c091008103107030810400790a0320380140e04100403992704000440c14032031030482c115085654402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 182610206 1250 182608956 182608991
    0xd0509040207050109030c0201140f07020603061f0315120c0e041a040503041d040203100e0309120c100f0c02060d0212100807050f060f03040c050901030506010807121203 75
    0x960143c015400c0a40103001c140d030110411820a100743c9858000082100d18400e9900800328082c080380c408200303181c007500c0d203080555880200181141002c254440082003c0c60f66a0104000f103601c03803103240e01800c0480101400b0b085034007182c00c0403030704540350f090400c030b26807082100752820741001c1000d0040a030900d2020408500040e221410300d4a0803075070b030707600510a05d112070b001580300b80045640d4a8a6a0045400400034001d03010480003410042552242c6031650b84020412280540c403010310714074403400d0074070203000c1104107501409090007070b441d0807008001c3c41030064045241c0103021040ba442d0191880360b110500200d008000b8800c3c2002a051114035008000703007802e891000b42d086e036454005482d14159100d007444400e104801000d5031202c0f003406000680400c04018650150040031200307041507850b008911007440a80083d52150848401488900420404070b00140f00402d00e4003601541a104c0760300202d8140000c07010151654801401c02c056803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 182611456 1250 182610206 182610217
    0x120f060115170117070f03020907032a020703050c04061203050705210d0e030c07030b090c06120f07020a0c0306020a0e03191401020901090302060d020d020d0e0105060306090d05090402 81
    0x203041d042e895840d248072804180d0502500d514034032500b0004a400c00001e014082140d03405880010240c81e51b40050f4040d00040d2030203180f007221101840d03880355031900e6400702e02c04160090000c0d14110700f8039030300306040451124003850801c03608200110268401180264052030256180e1070540382c4a03003482181e0410321a02c42c2e448940340202401b4100400b541442e072501000303c4c03d4007528490b180d000b02c0c85503010ba60051001080440d2010242c070780c0c030203403450654032480c150300300080305604025591081500990100030b10701414104084e0440014002400c2c10031041d80c80c10445400c41c0401030200340c0104242d038125001d03203400d03002c4d0701c03004003580c94806401194120a0590842c2607c0c180c00b4144041300c540c106108681240a060751024011419074080c0100f0783e1000c6100e078482a420895024251901d20203448000a08403000c00d08248103190242516805081d45200741c200d03505024005100052550202c0b000d4104907454064890004000780140b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 182612706 1250 182611456 182611487
    0x14030a080d020c2e0606090b220e01060914030c1003140403080604060b090f060a0c0813031103030306030d031a15040303021c051c2306120f060115 65
    0x14040e076401c20000701c03070030341c0241e0b0031040d010b94049521300806000c1e14a40d1180030301160501c01c084c014406001c0c0241041c0210803035490200e550750f8441c0d40b500001c1d07440300c1e00c1d0b01600030040c01002e92044c24034001713100c0d141c8041038210070300d0000780e00c52521403022882260000d0600542c9402600030300d00c08030f0003c9060342c040c6000d0401401d0140c04407030b000c0c881d6141c0341005c50380c5600b60060b16008078000d40007a140e82c1c00a81441255400402c1c40700074400d40500f14000120b4400040505203503524100740310f03900e0340c500120310303e0400700b00c60710a4005104200c0075440002c1e444000e42d4861030041001041c40900b040300e0070f03940f0225078004018521181204141c2401001280e100c0d80c00c5461040481c100400f803400c80344002000142c3c20000124a40d01001039002c580c048690000f0b20004c180c05941c0a1100c1050000d03909000d517803c220346450300d4008800b81c00c0581c805003211034607510300645ca416050003003044003090440c1410004d0300c60118046480f40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 182613956 1250 182612706 182612713
    0x8070e060307020a11010c030e0603041b06050d061a07020d0606050303040602010b0f1207030807050304090c170c0901171b030907171906021c0c050c0714030a080d020c 74
    0xc140c00b00075161004600c054462920180716110703654810810241482e8059491b0210600e04804100081d030015109640f01054400b240101a148200724402040d841c1c9460707944581c00c0c601c0c2e000340d030455172100c007007103600c0005208207000507005c03512200c1d0f0403203210985011510f00040101807603000990103101c0480d010070140d40546c00040c8461048178200c9407520801c082200c142d0080c451038000350055801000090706003006017100c1d0780300e1070070340342826150b40c00c0c50101c0c0c54003804180020345882d543d01c81704682000c40c3c6e8100c00c0d50801c95190840440c006400b1407507850200d2105a003800004074400706525003075241a100f03115513540c03820301c01c40381d9550b202e045c0070b090080c1140c2d001076100f01c000010146407010400f1090740101d90940c075140004e4102d00da030030000015402d04001422a24030410140a60304c1d101c4036103451143c1c1146182680a07000b074401c030b542d208003220040e5000603046103030a078407000c2c80340ea274003c000400020b4090650007589510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 182615206 1250 182613956 182613961
    0x6060d11040b07030e030a170f120c071406010806010611010207060203040f0512041409060102010b03070609140102012703020724080702160312020f060a1d0d09050108070e0603 78
    0x1d81c0c01c00140f824900030750700d182d080c2140304200b584480c01e0032030040c40006844105020412401c0c040c0085203e409900c90806e24070281998410300f0444140245410001e4160108524031030340032003050b10200200401e60501682550b100c006008120504c0f2a10064100f0103070309404507103c260b4045800c2d5164103007490f00302441d5840d00012281c600a04048081d001c2c0804140c2d01115003400d2900c050381c0d11041400038000d03018102e64119500c8600d081c10b16142086100d005107810781c1c070542031034508501d0030780720001840145e045904000020910312031030180d40340507505200175900b000b01c1900e4141e140c4001c56018004601c0408180da20744000400860f951040c26204c204480d61015000c907103034086044009000f40b92500c050000c41e26210548948032071034011909081351007a044c40c6400000c642c0004c0031501c440544c8500444402210400d021000080c4448404110080c1c00300d51540206410090180005a08030703205034a21488480094076255490 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 182616456 1250 182615206 182615219
    0x80c0109081329041a0d0e06100f14090a020903060901060612020307080f04050c0301090503091e0303041a1e0307030605011107090504081210151706060d1104 70
    0x641c101d128203900c45203c2d000090b40c4140d00070b48043c6400c0f030591007510b0b00d42408056440000308040741070083d08280b02d51400c04400f40f065182154500b8001d20b00351070007442d5801d0303980054000c82c03040552030100f00009103042004524140049484a11a69a03030104000a0081c00c3c0c005030305202e0078050011410040d40b00d2001c0d10f1681d44c1304142d6100e01400e85099204c207031800301c00500040d00291242401c40302d0340350024420700070703200c40f00001c800090079a98120025200b07500001080411403401c41c4141000c0800b04882d02c0d98850000002a100d000341d210f21075a400444600503030810204046421040b03581042c0c0c101040f903a215021217405c00c640c034001091a0880200b1301d580100010030000360600010710740d41c0e042c00640400f420b4042d0044812100c10301c414011100e406000c01c1c82000c01a0030816010300e800b640c015824480e000b8502448210001d40c0c1640c03c0b090580d41d0300190645604d9542c20741400e0030002004c3c0c040c2c132240046c20200d40401c1c207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 182617706 1250 182616456 182616487
    0x209060402070f0c0303020f06070c060c02010e010f0e010e06010302030d0f020109050d05041806030804140d0204020408010c08010e15040c05090909010f0e010216030e19060f0f030b010903080c010908 88
    0x252806039088408c5800c1c4120044e03510f40050718100c002c6071400008d80c00045041e000480f031144da600c000700d40323401c008030481d0954030981c103859806a169400d5100c414402d20443c076101542c04002c14465156070003094841c0000400350040140c02c42c0307445c555900035003102051a50020841d9605036080c04020100d811900845501110754074480410400c28007607407040c3c0c0e800035a41454503141460084c0b101c41001e5410343c0000c080c182e00d00c0075a4541c130181008000680002c41c951803441b40040904005800035189400402c090010350017a0b8207840504100507140050680e0700e0701030581d80c0c0c5c064265555440701e9002c0411940010640010317004408502061004045c10034000c0d0903070140c0149504070030030900382c540109104212040d203443c00503041c0541d90901c5910040b685983d40c12a20208207598220301265501009084a090faa0300c7d0400c03200b441f0703100080c007005403840060150440843c201420610a520101140707600008091382c51a00300040c211 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 182618956 1250 182617706 182617709
    0x7081303150f090b0c032208040504050c0313020402130503060901090311120d0b0402091002012903060402010e15040807080d020f0d03150302121f180209060402070f0c 74
    0x60500380b03040380c070416815015002003640e104071aa1010f503165000e04429410040c0519085698600c0e000140054020f402c041c240c01011032a503610b04203410301066030009041350003139600800420281440e43d6000300700b00341c1c0c11540941d407103459a11801d064100764202035898086c00e001d11142c040d0540c06410100d08ca910b8604c4c540301d0103020541c99402200540542001c20040c5199040c8180d1009202400080c40141084096008130385429240282440036039074504101c0840140c2c1c000c0e44064a240100040740c00d03000c0350200343c8a01c400f400003414401880004486070f07a440d4040c06031098440740f1a81c4581d81c0e00702c100c0e036610140c82080d02c9400360044140e103203071010030802384010101e070041100074049002200209544089419101d01001e00407006030f0303e96440789400d088000040040342240e480320511210664a46d8203890702e013445540b1600046400003020340c0c2c0489a0400d20390310305001c14041d1069090082c1407412000e0803104014240000c1070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 182620206 1250 182618956 182618993
    0x1109011202090612131106090f01030e0f1515030703170913051315050403020706110a02090f0601180f05010c140f011b090e0c0d020d0e01050106020c0405040b0a0207081303 76
    0x95106d450000b808044c0c0b040440c0290001500a1101903c2d40241c01c40a242c0020404075440c4201542100d802c040341074034259401c44940081c00200c2500d03203c285840d40044003d01a0940740d0703560306904818255400360202804641941c46030741d4403c6200131445d24a07401d21079890300e080d07024920920010220317150340403024007240d010441c1c89141d104a80c5600103061981c103040c07080e1007107c4d0704601b25400e80308614074400141c55070031200d80a0f04090b100d821607170603c0000941f40c50724040e40801650b0b6181e00030080743d40202d00010484100b82812610409c8a00f40b000d41c4210604104949218581d0201d000e100c0550001d040310413400700d16890082400c0048503826624400c4000c8400c4080110301248007000050660b03183d1103000525004e5248907800075503907210500c4072681d40d030b14010403200da0107004500e844001154200020325081d079482c02000005001000e800794049060030401210004443c2c8407121400340303c80d00d564902d0804030040a070803010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 182621456 1250 182620206 182620223
    0x906031107020d1419060f1d07092c0604020306100807141815090108240601050c030c01020301091d0604061e060b040306110901120209061213 63
    0xc42050015000d0754540c075030080070000881e20640b91138201c0d4101d800c064216004d1600071038103895203240c151400741d220b2600400c40c00c6101131050f08039294503a19101c00c441c80c601030400b4041c04a10b0030166061540d0024050f0a110b0400982703080514408400c501318070110b1600c0880041c0c41403040c4d00c01c50032540e0550341d100603400080380b0b5220710500b0b40c1c0110b10070b0080004099410745185005031550460f4400081c00503810305050700c91840c80d004000300600d8600309004a43d016140d103900404003000716140b4071031442020080308504034100000300b500c42e0320640440c0c1e5410140401c6a0b00c52032400d284900139071081c4625400c0d070f454040000028081003180403019800300300506001c0c0d03203036100da1019042c03201e402c01d449940a03001d2820070071b840c41000040c00301c0c0c0664680316421407400208441c0e40300c48044560a0a000d0031342145c1c1c1c015848480010041d40150301c07146484040703400e9000f4034001000340d0389640204052100742c88100c5900b04e00590a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 182622706 1250 182621456 182621471
    0x812030a0e070503150a4a0c0409020a082a1e21060106020a031101020c0d0c06110d0203090d090302090c07050304030f030f02070e060108160203090a0303090603 71
    0x16598100718403c25405421410080d50080a41c0e0309865004000b04404106115169811811100d0039240b04190380e00125502c2141191040c44160440c01d41d00c1c620098420b1000303041c5d942222501e001e2140e5210120101152916650b090003011041c0460782905128480d84c040f4a02e404041c032490140c00402810b40c3c5020740c400103040d500e40c9500d8603490300708014440240c0042d0f02c0c007210000c5c000c01d111442d03c1c0401280c0c2c02002c4a601820602c030140c50001c203e0400f401d560300b4240e0040c0610803002c4408150a440c3c44a941000903058101e860b1a41c0a8030340e1080c10002030501203881056400240c00540c1304401e540e09580400e204001c0681d11649603010103504a180343c0e0000e00b4540e900c00007050300314000c0044a05040c2e9a40e902c0207d01084002240000e90600c3e804220f642c04000410140c0328450747ca6100d80b07050b80000704104c00080c02001d0225240c0070b030a054034020720486420982c0903056440c02d0b40c030b030304000e496003c0350700c0b4020000c3d01e042c12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 182623956 1250 182622706 182622731
    0x1030b0c030c0703030b0301090c0b091009051e01020f0a120f0c030f0f0903050703060902040b180a020d0605100801170c01020307081e0403061505010302030702150403090812030a 79
    0x450b8810105240c81d2400d002103038400b140280724001001d601507503201003240c08160200000402040083e00f21951485135600b400305c40c2250000d07003400c0c0400325a0600c00341ea46c40c0400c0c60385884017070290a4250143c40104c2c0740000d02403e0f00703068051a0720080900044542c0e140c20701c2c109480303000c44103a0000040f03c06042110002e0005400c1d031a460003603500c0340b0300c943d125070503528140ca641c45e22601ca80d800c02d89582d008030b44450703560680c801141031a0040a40c605412680340100240d128a0010b9516004141d41001580020b5020300a5000e500c004060300005d403003c918541d40c044050f20b001c4e002e010b001ca07034050745080030315030000000f01e00d0360861040c2e0181d03040801130360301c078110382d0008000300c0d40701150603101000e1250b00c1e0010b00021805030401081c2200c040818034010000c42d001981014010001c01c500070f50001805d2a5003002e131083c03c00c180c2e031542001c50300c2d0090764000403040d01800038100320201c919805507014140b203079810041600030b1b46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 182625206 1250 182623956 182623981
    0xf020411030705070f031817010e0c10030c12050112060b06030601020705061e120103060c090e0103150b03030f090102060a0b010e100e0d150533130905010501030b 72
    0x182c0d00400583c0c1082020005100900a810b40c107200e824602064000d0300400509150160013803085669003915200d1513800034020319040090310000b416100c8200320104d00e440c821401c28400345602c0304048511688207898202808811102c10403c0303584038950f10f2000107030344c18142c1d1100c0c01d100b46003013a403416000b240c0c0648016002080d05030f1504043c40160f4004040c085160101030036800060000000244000c60001e0080310a88d130551911804645c12141c10000300200100c05128045050a403141501c0c1c2001030140c04940185104000d04854001b142d0540008a1b080e41424a80e601501075a0401d03001d40d05c440c0d81e02c2503118101c80001240500095076601d0b064000d00340350741c41d901200b23600d140030180d14904101044031000710480450f1101c0705000b015204581034030030f280d00800e140c0e40702c507120b07644a05600f07100c404820001c42c5080e50419400120b41d2041d200304144c02d4100010700030020203040c101d00800c000d110903900c1002d0440000c440c035403031a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 182626456 1250 182625206 182625211
    0x2041805060414190207140601080d080702030301050402160f1212050c0a03021b0111040e0a05060a051908240f091005040c0503100608100911060306010504030804030f02041103 78
    0xd0703c0302c1c1595030381c48003520b0601071010301d52105582002a0000300341c401024042c020001001007090394035266190340303021002e1280341e04014070f403014841426070103c02c076411210200d07030258803900102c13204e0010a100c0d0100901c41e84082049104100084016103c008204e450340c404800002110f8001c0c0d84046901b2031901d4000c2104415060181d03000e800c101d045503074501c16906690051500f1104000034003010900081820001400112820b41c0e0040d60124184001d00b071410101e00340c013520340140761049494410b500b00d00c2e040715100c0c40040c000d140444084100700c000010040601074400d80f1604074200005285c1c07098064181d00481c2104002c241c01e15041d07880d0002400050402c459115a15800196541d42081001d03642c81311000002801440d101040d0300d403000c81c49584c0d2850342028245404905000c2c1080d082a1043c1c0700c00f42e496550b0341c0121401d2095410091000f000481d0100500064600d00e031a510320940b010800084c6400380450a800f08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 182627706 1250 182626456 182626481
    0xa0b07140f010207210c0b01090906050c0406081924082404060510090501080318100f050705030904060303020a0c0504020708030c07061b022409070b03090a020301020418050604 78
    0x2286039007103100313413085440005017103481d001607038514540d02c1e540ba0481c03c0c0e0000300303026190a00340050100170310640c3d800a46405001d031070289003200c050042240207003803070724a206d8070880f1220340c400b90704000c1e4104107480950708100c0c80b1141c09440380b00c4030b0183d5030240c82542c054002c0d0b60801013030700c0c0403c0031942102e0300660360350381c514024060007030140380d000345514000125121b2a010b10383c040c092004c061901d90030304c01d8650002e400c1c0c20f2075041c13060802002c9458000d1300200001d000c48041d2400d00da403110142410391461081005042c4c00a10b800c00000138554040740809205215813041008030740d4440c200800c2e0b024038103024001c1282040402e0208008100400b44a40303d0740d0302141c0c01c05980c02c4a42c001459010741000b6030880d030060703010990705402810312000203510b0341c1c1181c188851019038414490003039030302a0100201080905504001076000c0d00d500600940d42e440d10307000790200c4000a032050350145401e00000c60203600d031a02482ca60a540f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 182628956 1250 182627706 182627723
    0x433060810090507150306050402030a02040905060f01080c0702041b0207060908010c05040b0a02010e01050f010f050a140103090309080a060f0e0a021305070e0a032d0804090504020a0b07140f010207 87
    0x40080344810320903400d5044003451f81e01d010019258a032030001e10b2248a4104006071114580b0f1034003070540d078000385410310036111080d008206a0b040035481da040729103058611f0300c0300f1783c901c0400e004101d18a0301202d0020080303003500c40700f035002800b0016074880c0c0c0d64070304000d42d0380c0580500340c0f8140c8000001081c001c0c0300c01e028030f80a00001c0c110308c010b81d1001041c220b064640c05403c4410a803a84280709400c1c100522041c002d07000d4400040c603007a22003c41007854009002c040ca09656181130405403901081024944542d0116015180c614141c9810166625041009121118400700c9040c217103c44c400a80c4408a00302e4442d0350040e10a0320200343c14250880100030040000c800c0c84001d104600daa511408c01820145100d401c02590441b58282202061146502e0921082400108020001d0074420554040701e007619404109616070703100050580c025a0130800480b4408581070040c040c02140403500e081c101b60070354031039940c1103ca0a00380d204d0200090010300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 182630206 1250 182628956 182628959
    0x301080a15110a081006020d0c0f02040902031b01030f050108060601030527030d0510061d0d02060705160e0702280204020f0301090b01090302090433060810090507 72
    0xc0324400c04070445201c8501c0020a1003540e2800951504400150b0340026640e000304642e84031020342020180016000500180d03941660040c01581b0b0326000400300c00503000b241d41152516049000b10550041c15120301c0c4107811001c5c1180443c11450900280c186582410b42a22a00c00c582c1658001d00141c10b49039914030056029100c0a854a0341e00100d01d1a0604201c50030041c8013142c034414000b4580c0c92083c8284042a107130080c1040b004003084080800035590401c1070713213141107144680714070021015030001e0202c50716101c029402440001e0302c20100100820b00610784031120b2450f038420750319140040c1409404840300005603004110380c0c0101c4540c0100c0281007c2c05610050580e10a0740c00721b400e0740c00c80f0214034060300b008401440500214001c09070542420310380307555030b146140c000500c1c400307000d00f000d000e80b03041400111260154283c20500c606400054001c2035640b802100e00a028600c10280030780500410096281124007030340c1250364110006003c644e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 182631456 1250 182630206 182630213
    0x30709060804030c0219090e0312040210090812031f080d03021303020604031b06030c0c031101020d2c010902130b0d060606090504050604020901120f020409020c10110301080a 77
    0x70340028000340c042c4000c81c0e40010069440c904c0315881c501c40055035201c502c1c60490800d050b00c40034401a100703500244071091147c0201e4801d10f601c40c2d01114071f0740484405d920151002810380c0c01805441c0201038141001e919000f00031402450030308040f01ea6114030125125000f042c601800c03266801a10140c0e0600b4032a0b000380903400214040c03058060f039280e0020b052036100c0e40c01104c6020842100b07402e14031031844000010205800c0600050b0030860008113240d07010240241449524240480920400d42c1682d03e103a48444040180424041805101e0701d14288802e41c0211b00c9a000104c042c0107014007814154003078061070030710301082c4156000d00700040b10542c1000b200314042e00401d8040c014003008180c0380c0c0340c0300c03103003414101440150f92004040b1409103004000004803640c3c00420118007220072840007801107110703507000d0701900c215030042c0950303400803e001c2c03a041404a401a040307040806d0402003200c41c030103129102d000900c111881a041816800c010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 182632706 1250 182631456 182631467
    0x1205060f0405100803030f07020706081003080a170405010e070b120a0e0309030d0309030806060a120e010f09060b0a090902030304060c020f09041208070206010f050111150903070b06040203070906 86
    0x881d0f070ba640702d0941e8450400030300c0d680040701c02a1302d1039801800d1110312501800f01c04041e01d0503140c00040782c80d00c459480c095a142c0d2100a0603e0720026180c5111449009040e040c0c00313024100c42010f04150404078040c00004140e403581e80584100000c8008008084900d00d4081070070291407651405c410100034001c2280b1a009800201f240300190341d000d100364269001103807000504982a810000e15010000707181034050001000350032000c5800c00c10040b400b5480da0b00c0800c48454902401d800b40c4402c2c612410828104000841000340e02d030480106008242c40c6400341741d0765581e80c101a540c0300c0e5400307501074100308402c0c00002d11919140e11041d0000e0200c540986501010500b0801c0c101c4040d01d61149006030300e401260700c5248070350441034600c01001d45504005140d4a151882c0c4101c038144406000086000303101449200010000c0d113036007482500d0005c3c03445880380c0c0300e0042120428440c2000688500d828800d0324080d09190b500c28000702e00f03000b0103982 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 182633956 1250 182632706 182632711
    0xb0903100b030c0d0b09070b03010e0411122409061e220b01090b0405151011010504030f1103040806040f151109010315050d0206090622061205060f0405 67
    0xc040c0074103100b0030b4094580f0941444100d00c21031104c0b01768500901e6050034500650090030b090380c0e04200403c2042e0105880d940c2213500411921400b9000100041800e02c0c0c440910b61507002e101c01c04400121302c0b9400070045541614649041e99072a0740541d294038085070004c01580c114070f640032450061600389980950301005001c82c503022000d10101c15610b000e400c84d00300c40d88c5001440b00099034010b81000b9801540c040c4118280341c0d034580841e208400c081801680e80c0ea4110030390354490340b4010840301d086d030000c1219090900700101096031500c00d484c0891a18480451840d00c00411101200e00000c00340030961180e0b6075114030004161300560b807001000001c142010301030311130010194111010143c2d0741d01550000f4081d28181000d80200028030b0500304102d4030340c2d4650b08052075044514681d102c0703071400001c2c410302403008854024004144110380f000a1408510180c920395283e1031a00030034a043c55007a610b0444800d80c021440002074641404c00e9040f068 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 182635206 1250 182633956 182633959
    0x50304050f010e0703061404030e06030604061a030a0c080c0403121215030219030507050f21150c07030e0103110f0c010212011202010c1b0e010611070b0903100b 71
    0x1c0c00400072140050039184009140c404a4001d03060400c2044141c0c03081c092607480103d00600c0d58030781614080c02d03d039011b105150044e8400000121282d403680d200034040d040c0030440c000e00003c500d081001d560011500c04510924050210f080f071b03409001c1d02031041404028503490070313045944e4401c032032688600a4050041c030080b1705030000c20b140203007648176282d4620050501d14600402c007411008102d03c1c007004c1e4a82100b800030440114140082d99030070790340134261140e80d002084074826880c2880c21f542803802c0060100d2030010031000c0001c030754042d03403c65a4444141c80801c9104514000b0045100c801c1411141c0d4041e80200c12402c02560805080a51035501da0b4030704ea00003a41102280d40c002141014044221071301805810500c840c1058024541e0003c0c184c01110340002d480040803241f605d00c2d07891804180009441c810450300b000356512500a01a03100030707035900e0824082d030403020602803010070980b00d42d00c0e8020300410a4042451504006200ba410103d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 182636456 1250 182635206 182635213
    0x30c060914010e1204060504060806270403020d030b1f120509010b03071523130306090b0601020f07150c0516030c06020705010c06020d0e07080c010f0207030c0605030405 75
    0x3402150804a00e2488402800000f15050030b08410203820b03d00101c070a02c1d45014244014000a81d2080070fa0f401c0d40c031345082c1540e01c0d032115000034001000c5021010300030122080003801405031240101d009902c83c2c1c0840301e580d003c115080e410394218a0030f054104e80410503000c5a807654000420ba120005c0c00d244101c2c1418041150544030211640d80c0d00d030713440d40d50003001400d08005242c002c00c5940c0380e818240c0c031450710007440f132400d80c00e2030882c440381d007980e421810020a00312650003804107211004c80b50b072441e1900150040e0702c1c0c25504214084001040c3c3d50010500c0104410356001030300440b400c0086160508000d01440307010080d05060200000e0700412031810407820401007903000900e5441c181c1221b1003550440c3e021900610030401c13103641c10050300d00d4600d52200c0d025860f120b0300d000720802445100503514240c0315548c3d00088404c1d02240c1682c0c1030000380c1e50400048403001d4203036039a01d0a840010010682000c0400a8520600146410520a4094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 182637706 1250 182636456 182636471
    0xc0a23090d140f0c1512010b09012616050c0c100c0f1b0f18020703050903060403080403030f02040b1c060f0305060f0a0b0d0219050402040b0318010603020d030c06 72
    0x9a850055960007000050313000b10403103056803034804102d00100300640c2c10103140c800c051903281e481880600c03a62500c0701000c1500042a030052444800c800c00f008452448640c0e80e0030340c00303817001045c3c41008403003200d9441004001e1190049480380c68086004010703090080d0140001c2441054101c003c01c1b101d0744202c800502e6040940c00c016005510100d01800c01100f541c4142c032543d80003e001000041c1d041042894400305030b0822a44140010380307d5400c0c1c241500e0510034401090390500070402000105500145140c0c0036a0096808001b00408003104078100e204a0041e8a220f10007884200d05840f200108505244e5803030314080f401c035550311050300003501035401c202c0c2e840d009081080501c0e90f01c0510705502161740c1c00e051214001010100701c9281130300d500030340101600100d00303408411192404004000c0580115941c550300c410f03080c0d06400c1541c6115140094002110702500c0500610041d00d4004152059a412030354041d5844c0200500c01c407600c8d40c48512 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 182638956 1250 182637706 182637743
    0xf050a0c0201050d0212090d050a0207030b06031002040611010b04060f05040209060c0a03020a11010504230111060a020408010b060405031905070306021602030d020d0807030f140c0a23090d 83
    0x241040091b4480350000724204000c610381088441321f289000c200b01070007800c81041d800503410080329041109406d0300e450f5580071900b8042a15818510b040c00020000398141d4031004803071100c607141c0000c01403000a04200001d4500500c2522401e625803078080c8254601540100740c06100103200500e0204080d181078141052001c0c20b1340943c00510b1081c2c2030007250054902c3c120801d1802074541800c000d04040b07448800000d8500b903500f09030740203245034017409940c9000200c0c0c1041b9102e41c60f00d4200c480c040c3d80103004446043d4209003141d002c9052000030340b41552070003405400c40201880a0005140c0540e1058610784030300c10002000c602544000c0105240c4a046c1c0c00251440b401031528081c070503001c02003190300484c900d0f100f10340d0010440e5088040b40c50040f510288503050074025090211203462850300400c14481e50050b6540100001c04031901c1e20342007281209550030005052050800a036942003110343c20500d01000d00102140c401c2c4000e9058101c03000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 182640206 1250 182638956 182638961
    0x6030c15090a050a030b1603090209040303091109091b090915060a090207060609051e0106080a02090a080c211903090b0d05040203060606091c050f1515010f050a0c0201050d 76
    0x20320507240302c071b40c420610042c1c0341c69146e40d043c101580e060500c4140d03050341c0881c0c141345c001070001d404c0680c3d510071541000059102e80c2003204005110041504051412a0f1203d256071504214036150840c601c0301d5003001016a44104104809010781800d401c581c9117034404010b200691048280c00e000c54061041d1000d4809a4065040081c2c01420140802c00310b5a000e0000c4020b4a9031036184402080c0c28401c0364159020340c90f0402c9140c4075801668007900900c00c80719440b80c4040f9001c02d404d140002c600d42144012a8400f20311180c1e51408101c80c01d0801c40421303560080180248005480a545011917129203400c4850f15502d0401240c603801100d0443c482d0381d291014003003175240400101c3c0e080b00085a0356490003600341c000075480900c0402c1c0070000e5490b00301101c2444814890200c0c040c02040960b0340700c0350002590391079184201c4030710320001143c0080c44c01035480b4640402035004180c40e101d1030710100d210140c504498404003207041100800c0118180022070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 182641456 1250 182640206 182640209
    0x9031202060906011215090201050c010c03050402100504060c12020a0b090d020708010501050307031118041b060804020d020402071b0b0408011404080316050c1c0806030c15090a050a 80
    0x280d0103040c80341081442c090504106921680c3d01e001d41c2190305000c20a0a0780300342c55100c0c0041d0000388001c0328030060366a409840e40800055182c40805519280c146d00254855442202c2d40c006c40c0080e00d40a44450066000d484001002c00c1c1e05100040e00d040ba10350080800d074012582900042d0303a0310041d101d42294444029000804180c1820750100060b4001d420300500a00c90f545c1800003090392507100303110240c03200da06d84071100017548403054400244030300b2904d24115071510f420455014441440003104624039203030005050f500c01e0a20754051a40203042c90f040d08243d80800010390003442c015144c450390321a545800b04030141d081d07001072241500c69620f551500c0302d040d08442e41f4203507400008081c8810000085c1c48001201c0c3c1c801c003031a405030204d950580b0210b849010300700e018441c0b8881c8440c40c08030724090380010050301100750707950b16140e507035401410380702c5940d001c07100d42103220024002c01e2040c4120203072004080150100700e80654990008280722050b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 182642706 1250 182641456 182641493
    0x9091f0e16060509040c050d0203040b071d0904030c0614012904050a03020103091e080304020a08010212070518150d0b060705030d05040c120b070914060d0c0903 71
    0x100d4000106408081c08410740d40300d00030141c04142031030701d10050b003c0d00c201c00d20703103104613910780c20019039034040d8081d2012500d221404640321301e018a070001d80048140c8920011400e8107440b030b10f280000c110507900015025040007010740307a941d07040d242e8001d400c008031141c5883d022041204554540e0b11402449190380781c0c04c1c0703900410360303080d54416016000209072504020500080c0c9131410344178100c030341c2031070300207000e040301d05100a040c00948c00100811030101c680c03034103211404c2c028500580c000c881544071036556410140c00c03813103002c1200311140910f2001911246c05100544420041403800d80c0c010440c50740060030410820010f080049008600c402007020107208042c014013040d00e185151995a4540700ea490040480c41075806131100700207800c00480c00012401841150240c48500c460351138071740003280b01140d640001580c1581c0000390b0b041d0040d10004c42d090050091854030034804414000303002500014000d02044080000015285c010000c1d54441c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 182643956 1250 182642706 182642711
    0x30c0e030a030e100306060c02091b030a091509050c040f020903070605070606080c030a1514070e030d02031305040f0e160914061003050a090206040602010603030806120c09091f 78
    0x21078004001300811909203e80c200b502c1d002c3c0501030903401c15464881150100d85a441a0359049514046000b60346110b250201022092024440700da40150070600d200340c0e030b01406246981061f000301c550810000e0304039440307540350f0003160416502a080007584036402601e400511808030303103005940d0340000b0000c1c1000a45030107020592082034003a00c8600c0180c09400700580000341c0d12810305101514a03a0310302c0d94005078107a181d00c0003c10f00c80301c908020452034100390107031000e245030b01b41d80c0c021302440400320091803011040f02c0c5580c00b00051785462504000500004000740c014903074032555501810001600200481d14906420083c03001085042c03003406000d07200344c0c01c1a40d6401590b403042c010660f540104c08201606c0c14074002803250742d1071800030b0245c140c0c042c01940042e000103001c501242c0c19080131040e40d001e074883c205207448240c10722061550b803900d41c2511340c01401e01180c0383e01d0030104154100d1144d5044404846541500c02c101c0c1280071030081d007042d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 182645206 1250 182643956 182643977
    0x4020705011b05120903040806010605220f0806100806070c021309060501050a0603050408030c212d09030a0e180c0702010807020102071115041706061c0305040501030c0e030a03 78
    0x1c1c0c02c0c3e4881540b117406040a5418985040b00c0382e0f607100c806000d088103200d800310303400d11405202c1c0c43c80149600704221004619039034100b030105a205070302508c8014040d1f200000d02c96000c107601c080889051b00700625880c1d070341c098111443d90783c041003284d000c8001c00100300b00240d03d02071100c5080c02850001040d503d0401000444813103548410181414a0100004258403500340e96100d00c07441019552554007a5007281c2010000f4222000700c410b0400f84038034030764800340342940018882d480e410701090042401c440700100f01d9661400f54401c0016480b014842c0c0a002914100030700018041d060141a5041640701243c00916500e0301181c100203642e4031140381500f011013400210300e020f0983e2282c0c3c0040e0302c03401c44140a40141200c0c16614800c4104580080103412804041c2516148501d030302d4010079185184647c00c43c000320b400002c03030b0039001c11455a140d1113041c84e151405c00150081c04200c00400280051494000502d44080c0304404816120359103040341035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 182646456 1250 182645206 182645227
    0x3040906090b030d020d0503040c0305011d070503070b0d0237020106050901060c1113150e0610080103110109090903080412050c0304030f08071b1d0f010504020705011b05 75
    0x110860516148650701c040130000d14a40c0108512184819501e0065500d0f501c50070f1182c2c02c90400e0340001d000d58640010915500e444100c0d208522148000751140684c0d00c1c0c04040d90340019000700c481143d010000300c46400581d0b80200004640210504208411910072102c8052400d26950010303407100c603600d408039420b00c00c1c80041c010498890800e941086001041c460740c1c44001054101000d0b240348050791480303116000c4540960051242a035403040c1c3c500580700034410010000400344c003003004d91170110035802c001581e030307a240a07840c0e2940e1170305000302e995149600d040c031011940c089161003160007240344483c06911940c4841c00c051030710075841c0055924031020480c00f40720720101554084202c80449400c090f50701000c2c0c6c02820000f80510441074014401c001c40203a164201d041029103404981d161000742c5038090252a2448000101300d80c840c0b0b01400200c014031041ca003c0c5c0c0540710303003030180e0b00002d8a154204280c0c25008154007411010941c00705840c00742 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 182647706 1250 182646456 182646461
    0xa1506180e150d0629041104061b030c02060708030f0601090807140315010e0106021902090403081905250507120507380601020d0f080a020c0304090609 67
    0x40502021080041c94801110305215242c0714000384510000b18544041c403031160031111550141c5110140d2292040110001c6144082c80c2c190040c2d040c0142e0380c0a4015903002d903030895405031a038a1000e01003c0152001845000084050080b20000c48001d610b800303004e04109072007981603980d20700b0034072902d0b6046140186040e04121802a045c800802e011407040102e8031401300d10b0140c5c001100010742031803800f884120714002c40100000344035551000740c5048400d40c2c0c0030b44880c0040c1041042d01c0d6034100801039007080054010070b0000340f1400074194000c2421082c9180f8070841200c18090750300c1901c40c0c1c00002c0305154400901034000e4104c9403002a242001071814495996081841510b00062010701c01e0104920040c442a212244810840d1401d03000364061035180e00d907a00d020403240c100c1a1307000c540014906500004800031861660740381d488030a0b01c406421a41c0c811300510b68008140c0910500d0b517400010070250000c0e0842e00d401207076050a08050404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 182648956 1250 182647706 182647709
    0x7020303190e0a02131d0a03031b0e060a1e02010504020a2c06010905032a0d08180303210f090109080415020c0904080a120b060f030a150618 62
    0x74600c0c034114112062800c000784021095030705840f221a284094048a0010444198025242d04010003d100000c0d004036004103194800d0700c04011544141e0021040d0062010401c2c020030050740d5a41010b140c4000507090900c80342c60f01d84040103014a0718002200c020800310050303034403030040c041113151400b40c4c58040e181202070040844800b04050108000074030101c0c2011060310b020600e0b41c1d200301c1c8078002500c1c0c080c04403a40c005003200b4007032403810342114110784c0a036845040c07c064944096000d1140760441041802c05907030505040c90449480300b540e92511007009000c2c00810044604407403007031010204070403807400c040000c0012400800940c542d914019095002581e1401901c0c03da80b00d48042c040c1280d82c401e03041e03261092244665512038030481c104410042d40c607009010007040e941d1141000081d400359801642c40301090302d54040c505002d80f00641c0c1c1290080c0d58021200f101c041015000d81d0b43c20b80c0c40036815004040002e01447c2c011040042a001810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 182650206 1250 182648956 182649001
    0x9150606170708090a080c0c060a021b010302030c070201030b030c150a0201050a0207081207090b07120e120606060a0311070c050909060f04020607080712090518040804120c080607020303 82
    0x207001c4c50142041c54440c903c40b04c00030038420021812481e0130700704000510707040b10040c150350759441e18960041d41e071740c4050040701c84a850f034901c03042e1154441e00a132030180c42103000440c10f21942c0d50064001e404d40c4885c40e034061080a000203141e554034400c002002e05100982669400400002030070f441c402008103d103280108501d40010b00c50004403902c1886c400812a9207032103c200445003201542d00c0582c402c000400d8071300070312046509080c8a000f46448003403a800518007032040d501e644d0b400040550f08003000050b03481c20f00c100141040f01181c0b40029400403480c501c030200d41c01ca40429035840a24030002d02082c10f200440b5904010b0200c0140341d20700d005001190a0100100020700411010640d403041015840c10b41d1041907010b842803003040941d4030010940c16940c82254400c142590314540e440310f8485c01a4052500300404034606810022050100a00c90a04507011900024005140c0605102c55800b13000303194047c42d600d003054844c00035110350014465 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 182651456 1250 182650206 182650217
    0x60b28060c0804030f0c18020a0f170a0c0201020405060c0304030c051509010e0f04091a0a06030506130f0b070201020301090501050f101d030f100c02010b06040306091506061707 78
    0x907808141d041040c0e0f8100c0790301490540c11040c01d454002d003c2d20342a80440c0220070010710404094503290082c1c40f205015940c0c00e40e62075203101c07044891800303203411100340c490907501242104806402c0000020090f000151505a81e0070204446520200b2804604d401c00305040c01080160039045004083c1100c0207079100005814007d242d21131003032854103101603951111160344030f9070105822204024810440c044c0341d402d0440c2c42100c4a030f0354041c0b42460100182c0d60b00030500c104c00540782c100000300301c0d968820f00c0203011440c5c0d05205a500444200c80c800001e0752020030144070b06d00d1580096103a51600c8800816110107800c41c1c4e11404078410700740c600d9203400c454144181e0491502156403003140312107940ba41540e1440c0d6426026000c0b15221760000083c2018100701e580c80c0c1000300d840c42200c100e007220204a141a400300040000300007042280e04026003a900600c039004080140e000c815003101c00c01e900c2036003c0351a464080b0b280a0100d12a16400744850821 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 182652706 1250 182651456 182651477
    0x50103060b0118210f05030304020102010e0f03040608040224120105040c050f03060d050105090109020319030c021210180203150f07050c03041205150a090f0f060b2806 74
    0x6500050078580140c00100701c1a0040c1080945505000c04d00184c210078401507030415803c3c500d4490b4421a0147d015600740b264243e82e01500058040880d0040c4003e14105030900304102d48040002d041a41e000710595204000314101002d2144442062101207546954040d61502420016400540700303610300790310501195080811900500e1090071056a03030340d150341c0012900c118480c4c0240080d86400700700616414158070821140380202d0880300d10743d423500a05e018171a0483d01c01000600d054481c00f005081203604020709002030300550f10b400d40e04640c004100c505510708150080ba401c464203065007070511064040303400310f12500c00d80c0d141038101d804e0201d4014007400100038002840310100078050055402500524080048002e464105175503a0b03e560030040003c14198030108210107130500c2000d41c0c040d4072414007007140606444040200113484030540300c9071749440180c0456525a0903003000391416140e69116003441d58041c41c80c5120329007140081c0003c07442c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 182653956 1250 182652706 182652737
    0x40f0b090904030e01020a0609060c090f0f060e150c0a0314030403081501231213110409030905030d090806070e0d11010203090a03080c100c08060f040b0a09050103060b01 75
    0x81841c0e2154044c142107503903026000040b85840c01c440b80150241d440c00300a80b04000054000380e468914595880c1102901d4445415800d880d034440c2450210080104110b5103001c0c030304112541100400400400c0c0700c1e008043c1c2e81e03a210241c000f0144e00070f440080109078010180703420040851207840d081d07280542d40541041c6000d003181c40e4245000c0f40c01e1001d40e20070340384102c40d5001090301c3e6135001c1c2c3e000c60000c0150442c00d50555a4ac82150000c2d0000041c100b0400105ea045540d44030514800ca050100411890f00181c0821008000c08070303040e14100302d03004280000c0c2daa141155450040c079281807010242c4003404001e2001c0700c1004a40c0e0714038a40c5152500700d0080300c508000100141c0c80c40c812621240c1d0401c131484000014403800b08094a55171044500343c5450198499502003240e440f440100080780981001c9901402c06140749030104001420000301d1084000018a03880290780c8900b5401d03480d00014420884540117503003c02e4403c1c2400f1070032151144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 182655206 1250 182653956 182653969
    0xd0503090d080405070b0d0e01050105010c0f0b0a0902040203010b0d0c0906021213030605240a0302010512130506090a030e09060a0303050a0203090a0b280503180102041703040f0b09 80
    0x10241c030700b009031940c041020f0000a1120600a003409420b4a030794200301c101200c0030b041c511ba10803245500e010000034055004050380e0315215480404404480007942d42c03441c2215000d08100d04190381c81040380c0c0180c5a6100540c064500b0880281e11002b0b104c1501c02038800ea0304001c006c120101000f004001d80005107100c50004002c160350319002c1e40300c043c2101d40f02d5075001412450510003400b03805020b990400c24200080328014070b0f2612120248941e0000300d1000a0018400704096402042a620043c0d0801400400d001004032641c445620f0003409440b04512a0003025000080542120507099040010388200b006880e2043c006115503003e0b10000d014480c000505030b076a80c3c42801159459a4002e09406c4007607180da116031480d4001ca010691421004a03c08081c040040103002008200e50380c0c161566940b0259518803156401a12120f0740d000e002c08194051040013004c1d00b074401c44011070b00e40d46420384c000e491a011358040e0101c00d1040000d6405900c554 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 182656456 1250 182655206 182655223
    0x30605041514100309020d060605010807030c08010506160b04060f150f030206090d0f1110022d1002071a1303080406090212030d0f0b0f0a03020904030507020a0b04080d050309 77
    0x203c550048140600005070084c01c00040025032010303850601c03100700142603200205680c1c081e030b9610840c2d038403960245c0440e8992002107000ca550200100404c2c50100000c0003409030a130f04801c07841e00e0380d42c1c0e5159942400e0750200c41c0281c4803110103201560522610241e007500c0e040005c0680d14002070100842c0080c00083d0040c0c2c40060700c000191283d0044d514041d40c410b10a90ba04c40841c240783c008909246c0e003007489820004601081346100003503880041034010350722190103640d01900c103512549040040400d0180c0082034510036000e1015041c00ca00450070148844440f0494000441c0018107800030300c0c0c000404007007c2503200c0c04903a84141d00c00c0b4000358071640d40c0001240501c085046440134030000a0310400310000350803901005a8070b040c28040c100803403040003d0f103807141e042e00d60804480c1c9420409490107420300c50b000780c020708082d45005c1e82a004145164001d030000102241e0000d01044109401c000c0c004503071440349809800c41c18001c605035101c0304007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 182657706 1250 182656456 182656459
    0x1090c140904050a0612030509130509150402190803180103020a091418070c0b070206090a0605040c0b0f0c060105040b06040302040e010e0d0e0f06092d040606030605041514 76
    0x80f480090318050305944040050030041d00b0310382641b121031038004c00a178060699075020f0070401c00c0044d10304416000701c0f030003421140040d058107951007070302d841d0060b0014002d030f03800240841011010964a1541c9000c0d2081401031565006684000c1e0019201081240e0400d44100000f60006038041a00002d64118501c0d06900281c000c0004103500c0711640d000142520040c01c0c0950036030422071007441c8901c10004501c90b50754071801030b43c650b60112603200041d00484150030014449501140d8030a104620040c0740e01e072140c45145407900401c1d003240340c5820000e00d00d00c0c1301c4810040e00d40181030441e005e015100c0c4400109506001c2da20000b8021900c680f020300c0748001c207400c07080d000882041150168206050020072a101c6c10825900880890500c0704050624004542c0401030182200b000c10803040c00700e840c4040c565100003000070b41c40700d401034640da9601560009098503500400d5603402c060400c030890384510040058404003203000c03c1100040040d10042860 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 182658956 1250 182657706 182657711
    0x3181506050a150519050d110306210606010c0f0614090f0c010903080d0209040c0e15040806070f11060c03072a0311011103040c0f0b280e040c0801090c140904 70
    0x8005c0c1e0305582c80e01075038018a940e80e0600c140e05c50700c2140c072409141f00c0d50088420700b09000300903041a0311100b203200080d10a4120a00080d040c0d4042c40c104500140b0461202604800e9a162002210134160b040708000041a0502100701000c02c002004a4000005407d1a000000020380584506d110040c00254040303600110609243c0c191800450040c00c2440311250f0050014507004ca84084a807080b4900c0c100c291840e000841524113440c4528000c02081e00d92000503192586031584010800242c0700086c110b041e4103001aa019000e1581d20360707202d0900c40d5014007401d0307404201404040014001c1c07001800100c14114030aa05800c080d410000f00150090160841c1c080d400d5001c20000280420460360507c44400c880a010440090303e80714a9030304918442c0d41241d007902841568282a800c410001c20f404905150800c044d07400c7c00100804d040d07800d1400804003150201d80100620441401440007190311841e01d02c2c003946074041c00074620f01821480354004c0342e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 182660206 1250 182658956 182658997
    0x907020312131a0f06030714150702030a0c0902030405100c0806191203020703020f010906090e13060c0507060b0616060509070b12010303090603150603181506050a1505 74
    0x11041c007002c84140c200d4081d001c902e141a400070100000103403017044c02031080010014400701c40c00ca03283c0340c104000b0300c41c0c80f19030b513042c44070301c1030303400451090b0b0381801030710f102600080711080203000074950301d01c026071207250a040190822a11b4201c90414608211404aa00e644035601583c81a41200c8d040140c080c030790203003240d9050310740040e082042c21014010a03d078000030402c044903c00c032240d500c040d00c980f0044841d048988100300110380d8440c0140700c00305c1c04050580e4010950b01d819500d850b499154202512a03280d408804200000b80d0700091040d14002c04440040540c1e009140c000d02c81c044c01d0450f82030010103001d0710358035808100292001d100180c002c01c84885c0e0a61030308007040e003061500c402840220b0104050503000252035000340907454500d20f5401114900500d0007205074007074a0540d440c00c0f0040f02a04009000440207144107480c50126100060901d040600b03002440343c1d04cad0048220344045402c03070141c1d00e62002c01c80b80300c4140b000b10f04d07030341a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 182661456 1250 182660206 182660213
    0x2708240604020a0e1c020a1d18070303110a2f01020f030d0c021207060204061106280b180a0c08190b0a09091101081302012c030a11090702031213 64
    0x41c0181c40c03009600101d00440044d66201c000c03038111903942c0052804640d27480d00b04040d43c021084079034510305500f000c030701080400c0c0503070039032034000750b13140190303069000c480e030310580d6681c007100b2000303840c141c0003c1c0804111031520f207628000d0300c04e000900b00d01d59082a00ca9490081c0341d484a0240c0d169403050034150300c00c2c80706144803408200815120002850030724065006400780c1d60010301446190503000b030300040d41901038079800001388040d40c0aa1401040c3c00c40b480302400d505038989007285515210000810783d500c2050704094000d00b4003155075000c1c0c0724280c00035810400707036100707102120500e5400d01256856010b030020710003540f0000703d40e240e29940d00031040c15160200079014080514040d842500d400d9845889556420a040108003c004000b90000c4d030108010850042d600d00611580c886020f00800403050703040001c0c0c985440c100c011200400b2100004000e41003181a840d00030481b8006142000341012110550140003802d903000040941c0c454400d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 182662706 1250 182661456 182661499
    0x5070207180e03040801020306100825050f190f020703032a0f0303050a0b01050408032b060b0c070609150302160614060906060a2708240604020a0e 65
    0xc60b642001625150340d61240654004d4104a034258040c072400f034040142c1500c2040c6591180440509035480411004e0304507542804841e0340005004e41001b0910f00385042401a0aa002c4c90810105c00a91a000c0041051061400c3d00381554086401440042d800410480c81e0f503480304810999141c908185401354202c4000250020b10313176100d8081032503419000940b046a00340d106001c0051900011100f900c241d20403e9100d0b001030010420258030052140d2031030407903c020108800035180c49004941c52a40503450f00c0d6000241e00c0580c090038050311000303104500b0008201407400e100c0d0060a0344108072141010b900280400c0f80c020101c007290115a001001001003032491101c5642c950000d8a130584641c041c080022207070b107010300c01c0314021000b5507100880c901001c02c00340c24000e640c0740e84980c004403085000c02c14440810600e008015400b03282c0b033308000f0f807295a151615015000c030303000d103004000c03c03002640c03c082031422001d0143c3d840ca100290071f4150038207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 182663956 1250 182662706 182662721
    0x1503010c1d060d1506200601030b0a02030a09050607020f06010f050109030b07050706140f16050d111e0a081f0b28110f0a050a1202070f09060f08010507020718 70
    0x13844d151500118107594008846242148034002c0d580500183c6520a65294000d21000b401c51a600300080c0c1001c06a4000d0341c2c024070489000300c2c0040ca55035400342003407801c0301c074803006a0150800441d042d00070800e040c010704495080c2a401800d00000800c860868000900310020800c082030800c0e00c10070032104c14a820060400c41c0280300e0341302d6200b491080d11500e10740101c410200301584d94800c041c050000c001c4c4c40709071401011820356806040e0340d0541c04101901440f551020f20b4080048174415004403130015070b0b07030740c00c084007418110001c0e20031900b100c408000c4102030071031118810f05541e06411160340303070500e1440012094401e241c41e602c46880b11608140c0740e5403c0702d201c101d9140e01c8401d4802e82881004050795414000c5000340c0141d000c0518100862420400d2640d0104517105588aa5484201c501c2e208039456018404e000e83c3e0710320402c51205010448005403e020000f4410f90401220081d9104524090700c036a030ba14002070100485202c0c2d12851 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 182665206 1250 182663956 182663981
    0x13091502030a020d0e0d08011703091201050f0907060518040e0109050601050102060612120702150a091e06020d0f0e3102090306011502070e1503010c1d060d 69
    0x6640789806802c1001940101400d50502d5040405200781c0c010081100c401026060390f40c4100350b03103010046540c070005105a560b45000c200400081074903107201c008090343e04500041a542803014507141e0502004002c01000d0300441c4042c820507078458216880700326a4541110705094540001e401040310b0700e10180d066107422110070400001040c1103040f61f0091b001e64800b503803041d0a021171201d0a10001e21142c00a4074101c044500300c3c005030550f01c0c00902a09150303040b402400e10342e0b0340701d2001c90f004204024070800074110f16034110000380c2c0201162a85003440c1040180d601d40382012141c0030310500354107094680c1e219009011a1300d40c0203100e401a0071134008000d8412141d2040c00c00c40c0411581062070101850085031100b07030016005158aa10340030030320300103900014409085001c0e00400040f140c04046150380076124040c001c2c0c00030700711081007608417045880c1060600c000030042e054107030500e20702a0007010b4142c54050f6104020908500205901e1540c41d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 182666456 1250 182665206 182665211
    0x109021e010201061706071101060f050909100234021008070c080414011202040501050906030a060305030a030b09060a05150904020d0c020f0f01060f090f0207120513090b130915 78
    0x20220540d000854034011115503d8414501238141e10702c50980d0524007070a83c4800001e0340800860604001d002d031310002da03400f81ca141c0102001c84030b050341d11581355400d80c00f02604d048002c1c0740c4014421203658010124208030354480c0d0b804506407106c00107a0f1030600c070500340015091801025a0a441076202c02626615a06e0b90a030300742e580040300c8441d00003890803004138503060f241c0c401c4405451050311454140a560001c00c0000c0c0c0c4010300340000151140c400200285042002c1d20b101411902e001c41c1c128111070503c00120743c000c003c02e2081e070f1024402c10103030312070300d48410400d020784000c40d07a2801c42d00d021801030b20440c0c501c0200346280c1030a40018540c045142000e5180c08020b0310400807140035458243c0b08980251184c0303400302a0200a0807003594080c0c5c1c41f50300c490364054206980c0351600c2150400c11340b107040100d280042c2d4681a030201c07601100203003444020820401d98488041401e0264681c4e0916869540d074400609010210340701c10204641c00c0410f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 182667706 1250 182666456 182666489
    0x40b04020d050a1a030a020315180d02033402100521091203100b03071e0206010501090906030b0408090303040302100e0102160e060f220902090106020109021e01020106 74
    0x6001045100358103030446100c6100c0113010f20340400c0700ea0106400034000c2a5802810301e01c2000718201070510000034880d048a04100d01c1d05109214194456070055520b4422000c12071410700c0101d0007540c0d43e9400071926003013003602c841d03201425540540d03618264803070940c01a035062041c1c00c411907402c5601e10322000d0703110020711810720030040f000c191402030300c0ba40425503990006070f80340388400da5109010b001c10308400001c0c6034025480d00c2d100ea407580340c00c0d02c91115040c21460250060f0000300040c41503581010380e039002090305403010040246140c0700ca500814025000070000c40c00026103161560f010000e880146400610460020311050170207042c0003c0e03440828003501428a16034502c441c10107d0780210340988240c0021580c5103401c000d80c5240005d540c55001101291500010208050100b031881044800159000d41c50040044030381d01680035000716814810201c0050319006800c4003080b090886042e410b94082e030040c0e01402c2c03503030481030356a1108082c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 182668956 1250 182667706 182667721
    0xe010b0d05330a0905060108042d120e120a0f020604030203060705030109050f010609290f040f0b07020f01050f070f0303020a080a2f190f020d1d040b04020d05 70
    0x341d50014401210601c3c2034654840d086400c1c1e610071608640860b001200080c0410f000b08a200401d1a0300e05c500c050b800159250203c01801903035058826040e56803000b481181c000e0f0134850340b24070407940d5543c203007030481005d03a50340c0180c40c00038404120060000c0454407074030285c1d130295600078165001464440c400600640092186034071150400307003c03920103551200e0703450580da0030b5070f201071066080080d11b8240d12401a402d040d17074422283e40d0348014040401500a4103241e181450350b5624008880807c103101d0742000d032440703400304084401079a940d01081d42e40142820040d03211385038001741200c179014284002e81440c12200c005010554180d008004103552a01d8058040e258041d00303400700c5164400e00c800031240b00071100085054036a9000d04000c8a051851802c1c103002c00c0b0000c0d80c0f146010103800314080f12400b20605405203c9000c100d0013510706035000118040300c880801c0c03a03c02c0c005001d15903599411590f0303102d54049442c510b121103001d0040707003004174 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 182670206 1250 182668956 182669041
    0xc010207030510020903011503050f1b06070b0c12090607110f0c0108100306020f03010905010b03070c08090616081b120f300f01060c051002090f0a060302040f0e010b0d05 75
    0x1612030f03640245182e69000c1048040d001c0d200003070140420340ec20b102c41d50340c0340300440043c0881d010030f20700344058148a8924980d29201c0e4a403c00540070f103040040e4060310b0100e0385e203804241504004401c070044440050030400b03141c82464140101e8495030108500c0758401d8002070520343c000144d4030041c480040044d030407100000c600700800d81e603a203813124240c0400c0d5403000c001078429000c40049000840a800c0c000001400c00f880d01d03007282e8540c5103106005c1d900b00c440c1d000120300809041c1000300b000c032814410401603c1500d00c14800075941d889503100e002c0d6090000306104c0e080703500403211545100c0c1c001c0d00341140c0103590b440d4280d0720601203851080400c984800480d110784601c0c07101c0c80c2d4561020081c811000103280c640081e400414859810542e040e002500355924203040e034009000d1510016591410b0001030558060725420018081c8581d03801005168001400c60381c900511003c0003c070746c3c55039600b603000700301c0308130406003000304444002c1d8540171b201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 182671456 1250 182670206 182670223
    0xa1d0f010b0f060702060304032a0c090c032f0d050a0207050d1b080306060910050a021009030504120c0906080718230c09030d0804050c01020703051002090301150305 73
    0x1110780b03480d68034400302006414420080025082a801c5c8045400680900c000325890322040b01603001840c005154400e2384c1002583c151800380545504010400c1c0610070741d00c185010740b43c24007082442100c1295038001c02c1d02c1d407420400764281c0c00000e8038402426500780301c0c0069004d1003e81042100300e000394101680507030b46d600072013140e00b500038003ca07020000c03404000c406030001d27109511512000d81005000720781101c0c0c20082c00c40c603550341804071944204182c4495807185100c078030080c507004500110b40d80700b616140c40c2ca00803c0c2c100d030070769040720405400516090034074900000d4440c021351160202d10b04000c8081015803011854100b82c50601d00d952600c001d1800e4420180d88900031080640170151150112070321342c0c06d030320503800044035451902d0a80580040f906e451810400c1500003807100043c4820013206000c00c103110802440101102811900c0d0251500841103042e03c1c05640055140c4058400390031500781c0f140d80918010426543e030410720340390100c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 182672706 1250 182671456 182671459
    0xe1807020c03010c0806150409050c042103080606090315010308030117120f070804030c12140102090f0f030a0803090601030c0e0103050307032a050109020901090c080a1d0f010b 78
    0x40c6401d00c815402c0c144180009900d90b0703682c405464a80318103124204519031f408825006003004007180d0203509000b418020807a010320790b40d0b1940b0f82140300c2100c131211007892900c01000c60719900403d0b40140d10680100c000c480082d81d51450b400013900d82407041341c1d05008850668000014042902d0156040b82c2010703403806005104601c0380c0e5110a406001860320207424232264549201e408040c10000384900150303858961a070311080070b0b241c103c1d44416046c0421030402420400c070070300050380c5034164000075401d1030b03007113000601d504240c3c040050082d0100c089405d480d030f90402c111010070760841200f596070f007400004980c4400c0d00340410381d5450415403000907000e01021900b4100c0380c10002a60811000e50340440c0c4099002c0340340f0030804200201008465140c5203d810ba1a2292000284d007442c54030500c1400101640416071300d51803c141d40e0f0000350480943c550000b140100010a00350070102507141402403d203000702032044803a000c0b1860b10560200403107050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 182673956 1250 182672706 182672713
    0x5010f0c0f02211e0d05010503120c0a0201030b1903110a0608010608041b0b0f0d0b01031e0216080a0807020f070501140a0210020f07021c0f120e180702 67
    0x2041ca8182d03550100d21000d840e0654980c1407900368800c2d07a2000d888030121015440c0000e9105450000c0d00f030300101c0d40f80130115541c4004016a160030401040c12455102d0381d5810700c051480c0d09510364071340c200081d05241c0c4407141010030b5580c2507030201e11102981d440e03800294490501064054185403604d006485007070012410720f000b8204d5504031111076940c103416583c1c1e666442422a480c844040c524a0400c0c00440d100d010728010b04070115071070305020b4440c40c0300c0030f8280c1038540c40d404aa061601e001d1601c1003008001c1c0c40d00540380e55120000da5980407502c0b100200014803000a4910040032a0a46205910071300450058402d603007142d080f403820881107a01c07102c1c0303480f489021405426440e0200300c1c110300a01007000b01401644c0d050644005881c0c1641d005900004540100044c40d00440c605170b444140c08101c3d4104405404615035503411a400e2940409070440d40300c22500c0781e6051207100d42411540300541015107400c0c03629810301c000e450681d43c4202600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 182675206 1250 182673956 182673977
    0x60c26040303080c030c0415020304030c0612050703140705071b0b0309060c0301060203070f02010e030601030507150c020a03060209030a0f111c020109090b030a020d0b0f061002030405060a090305010f0c 89
    0x7504c50b09490140701c104e408586014075000207148540010080c3c801540402d000003c040b5000c0100f0030000c2c121515102c2d8156440900001103e00050140c4141468482e102c10395041c00da4280d903001440d030404507a54400e508107104d030b00d040d0016007070000078071003000b0644041c101701850103000214100c46040d00c4011400308a40000d0241c2401a8028004030001c02d4240459245050041c14180c0c0e01c030500c00080b0781449026001074610741e1120b9820803c034034201056a03c20701d01464618610603143e40000ca484501e480050304443c0c02113050f291954080c420f008296510221901c105815450444445003d05071030910600c40d015002f0f100b035001c050410b980650596a031002c0500b41803080c00207294035691160503100350780407040142c40b9031a1205501c2d01810354424903103400d00c0040c200e0040103120718045c80d100c141021006070000140d1301a00d000b10385c0d003500c0e661803003411070790050250f00141081d800c240084640003090f510803018068250b60b100c4040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 182676456 1250 182675206 182675221
    0xe100c110604060506060702030312040302070501020d0e0d081201151403151005160b040c0b090d1709060d02120604020c191103010207032115060c2604030308 70
    0x6100e0100e261415008400098002405580166801080204400c3c02d020340c03500400c2ca540c0050000451318807001c0140014941c0412900c4003c14091008000200581038020002e0030b881c003485000f40240302d500b8040040350800e032400d960201c01c07501d40302d6075500308021240070261080d40c003282c842d04e1040e1172a4000001c0b41d105162101d84100f007807400340140300b0010355444610f000c210080c0b082d0320142158405001c84540142112601800d090500c088010126801000000000c10100d650340e202c060804d0f0015402904411242115100e0720406100b19101a80d0200c80007500c1030a416280d405429030f0314401002180550b5a001071104a1041c50840c0369654410241e100640c020124005140c0384600000a00924484007180c2681c002040c01c0300401c104031242504900c03c502c882c84a00c41401c1c00b131120403904000d075040c280340b500581b820002010424030500014162010100c0c440c007804000e45440300059410720f4100c0d000403400581e8600104800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 182677706 1250 182676456 182676467
    0x20d06092a1409060c0f011104090b0f01080f360f01090213020c0102040f030c15030902130c0e09040c050301150e0a0b0a0b0307030f1b020c0906040608010e100c 71
    0xd10407503040c818600b610f65810801e070350308240b6140e803551103090389000ea102d50030b0042020002e192401c10385c54a040c060f20205441070b1009182c090807601c1101c3d101d40c3c3c0d00044a07a004003000c100009141c6600302c2d1000c0b1f66041c0c0074525001c030345107041c0311480c81038a1030802c4032103000d60955101d08507001841d82692b00c03040b0043e40c07128054082c100409600d078014102504018001440c1039505c00d10708119038003079071041c0c510004170b0000300021340881203848600c3c141e5140030040400e183d400a155200750f488011240c0d41d6410b01044880c1c0180c480c403600380d03001468134030207140c58a400320210180c0e0003014042c0d42001c04080a4840c21421001038a9040d4007903025681c900000c80c002740300e03222480758411500c1200103003c01c015001140501010342e4007003604020380c1c8010040d00c3e080d41211580c0301015440406103a80070460002400f01110414100d40728400041c010301200c1d00031a546500c1d00449851010b000180f43c0e0002031442d500b803180c0101c14a09507003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 182678956 1250 182677706 182677727
    0x109080105041a07020c04061509050a060912020111031201030507080a050a110303040f06080906180a0b040302100c08040b06061c020c0a0602070f0204140c0904020d06092a 76
    0x1540103d26591240320b075a160240ea20460b5481202d14946080c00040c007035828580c400101e08108940c003444503a40300701041e01501d02540d10728012898208002c3c0740d04035611880312035201034082002161711500840346410b10b08011203464421442e92008214803c0c48120760f58841d1000010b041000801d01c414216080b601601e010030241d00c508a0340f068580110350300d800300700404a64107440170500009010186d6500c1e449242c100202c0d0300e04200a48086507018000400c0104000b0016000c044180e100c103135004203880b1494168504220342e81c2030712520341442100155a1f6000e01400d1259001d0710b5001c1d50713900c4103c10700281c2d22413051500c1c1803995a4420100d408695001050001e240c0343c220340040c5242d8540304120307000000e00711094032003003c112040d0720b018020149103d034001c0d840e0a4a08112a00220074407882c0c810600650700816440c8902505500410043c08110f000b4490030303142040038110420150640c2074410700044441c0c513914450100e120 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 182680206 1250 182678956 182678963
    0x40c0f0e01080402040b090903070c080316022709010903020c2b0503040312111b060d0c0c050102070b1801060311060f0c0f01060f05010c0b06090405030409050f06010908010504 78
    0x1408050320801100c0090006005036001501c030b400e12402500c1302da42c1d0fa0f101700301c4180a19203030401403421074400f2481e80d01c80c3c906540203010314400c64002c52204142150304403100038114050103101114411084103003444800701404002070480103400c2032605601c25400d942c3e022964004000c00c100b2080074600319084000300500840b42a986401d26890040c41183c0c2416542c0d078500341c5040b01d040b502400a00004d92044440320300700304151440c00d00349180f42181c10390300007081c20f501440300c00d164110340791402910900d010b0b20740c0c1c00d40d49401000070365542425041c0610aa00107031040404200b02c44541556043d043c4503c0040d48c0c0d20042103922110400100074050b042007011240c0920b040020710f81140e03040182d0035080d43c010002080603898100700c907984180c2c2c1d40c40030381881404209900000c1c003003090750350b00601c200c451442c0c0340c982e414854170310300580d00448200e40c80d15007030044052000f000a846004240c0c1e1323240e0b4007601ca880241c01e031039060320000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 182681456 1250 182680206 182680217
    0x804060212070c0b031003151a10021b06210621060f0c210f09030a020309060d060807090228021504030302090d03230301050306010b0915040e06040c0f 67
    0x1c0c024902c611307008503003140c2040203226500361251210120081d0307406900b240c459a8102c4d01e5607290b1540d0a09948110490382d800c00036041d5140a5100e04914500981440e4040c0c40c0240580ea0030382580c0300385040c40f030f43c003042d40700c5407520840d000c0c0c042e51600c1c450400051800c1e401d029985800c3e00d5030603120301034501c0f5141d0100c02c249001000c1c1101f100303504107202000b00034281c600307035900c51040014041110f0900c0c403030b404958400a40000c040390401c020b4104e010341c000003103550103401600d144d9503590100c01620000c3c192504000d50310f01400500290100003074002c6c0c1400e407015074401040c07004d000242c205500c00200c0b8040584c0102a441000b110030610781507001e4000e0401503d400241c2c0c1c00548000140c003002c030081400c1c03036050828106002540c071200c803510b4519600c0e41d410400003995a640512600c09100d0340010341004580703480324810f40c2c0415900c903107500c0301d4075406902c4401c0c00840762103009074540414040d40600c204811180424070340c550 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 182682706 1250 182681456 182681459
    0xb03011b05030f16230904090b06040b190e090c030d09090e03090a03120c02120703171612030f0f0b030d09050f04020c0f030d020a1803020109060c050f0601030804060212070c 77
    0x12007824400c041c501105c08803040c86145903a80790b034001c036485688aa0401400c44c42c008082004a03140d500300c090261070f40154001c04144460500c0c41a6852012401d1056407904845450000c1800c05150503008090007200c2041d00700604900f900d41401c41030055512070300006030359002c1d250045505c4168003004001040d485460388182040c1031800d0140b40d151600456491840080c194629070700150003003082c001104d94503030a020a41e94110b140c40340c04522004201d02411016080d040301d50a5480f005000742d02c02800402c14100034001c801148095100500010000300d000313000310b0f90f00da501c4d0340c41540300364242d81e40207080b0040030740040184030081d00b024021034034a1240c40510280b103407007000600301c407244100003d81d40708902100184400d41092205820700186081400183e0b0480c4c52002030f100f1034600905410564100b491510001800346c064034040d403000401804403d10050050ba0702d00e0302140d45a03400100380c01401d03c0360303100c0a802030070380850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 182683956 1250 182682706 182682737
    0x70f030f1101110306150f03061c0605070309140a0c140103020702060705012309150c12071806050c060604020906040503060c0706060e090604060b03011b05030f16 72
    0x40c0080c2200e036615140031050400007009084404600e50b141c503035500030040103807a1405605507070b803503005440303070a040910280680716980009030145d8407855141e080b03002c10010070300002d00869040bc40030700c5a420004406030040010413411784800001b4007031820316480c00503070b4035072940d403040300c02200d246081c541840c901250403030241050303001c02425000d80c0d00d400103003d10764007807000021101c81c04c10b080c3c2810722882c0f101c5950401ca201c1007001484000c42c947c081d49641c0c10020342560359103c02d10203603204507015a152080003d05010031a0760203007800d08500441d94182c4070750380e1992003d440501815900e105250300c0800010340e2030800e50094121520701401c1907040070b840d040000c0c10107030111656080600045170313110078440b06015800c01020012458003183c184080525220200104054009515084031100f02d0303c0075484000c0c0890355030f8804008510001c4014110760040d201078401c80d01c203034007003042e240e80042041c1803072601380c82e0440b60a50300f15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 182685206 1250 182683956 182683967
    0x91306050c0f040e0906010911030112030504050a03031d0a1422050f07140a0e0d0c0918030921030809011e02040303021006031e0c0305151b070f03 65
    0x30580c6500784800e01412007094000e50150000e401c030710441c07890030715201072440d2904505a02120955042941e64484a044002140d06456042c01100000301c2141000d5450707200d698080354004410f4040001490f6020a041442c4440c4945000180c0400420441e050803603001d100c4000f80100e45800710b502e0070744412009070292410030000d41c1130101c640000c03160210748a000340030b010001c0081840c0d11070305240b040080401150304181c0407107030080440c0b005605540c001d260205054041c0501e800b034250007404040d030f0074403008221040403040e1240705c500450114220b45d9012900503c4800d28168040e03045049140d001c48640b8100c3d03019801509100d60381d50380390a9617000b0750324070701e403229102c44214001d60364603e14a4001c1c1342ca5440503007241043d1900b5001c3c0b0002d84000d44001858040c44d201c41c28510960401075061181070f88010030fa8498859261071544065101600c42e1a540c002403040105200c0c0c501854403400c42c0003001003544481e810002400355 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 182686456 1250 182685206 182685211
    0x15090e01090506010e090609070305150403030b100909060806060603070c0f062c1911010e1908062a0d060b030718050103061a0c010b0d11030c09130605 67
    0x200d001d40440e00c989007400d02c281c214441500c0b0500800500034800c10029410903040d41c0203001c09442c549801c1d840303480f881e40380312103081c0b81d4010a0030306100350009800110002e02c150030101c518103018200fa0954400c0088443c1422030010f680480070a5031841002c010301001c0c61680c5400086610001405003280c60421035003116000c2a01403140340a0152044c40040680e284826082e58041c0205011011517022012414012171194102600341d9403140324001034a000c0c00050391f80c0d090a000040d00031705660348200b510508003000c4811500c0d01c00a480840d02c80714400b842e2031002051005100b5034100ba5a0f8807403902c10001d012100302c59034002589078a40b4003075101507105445000001d0208408040303850110b00c2d00f10001c140909082226500e09400e0b0840510000c1500d01c000c038003c02c500c0700d000020b410108050400601c42843e005292a00c245c444501902c1940207102e4440c100c091420b2444055018130840351004a50304141c0e40d0340c0001c5d0000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 182687706 1250 182686456 182686481
    0x309110d08120403090311040203042310020f09120304060512090106030803010b09040e07050a05041d010606020a03030f2715020a0914180414030903070e040b07031509 74
    0x41003110b20182404440502540c4039555012a032850b41c1000341c111080c51408030b108601c104207000000c0d4001e550100c000010001042c0b51145042400d07003014800d4014040041c00000c40d03540e2601d0036030003851500700465040381161074841404e13940380940d004020100b0000c02c40c1c000f607182c0c48880c1541c0402c40030000f00c0d5aa0300d035036600d170240d08282e02142e908500881d0300e0001e840c181c01042041010000100000c515040000381580d01034842c1d2401159a0281e204a21040c04510070f500c0320418003c0c0300140e52900c000703656140c030b0317501500081d00d0300c0c003030540c040e9250103201e450900a0140d480441d543e0305e0721002084080f03800301c4101c070344440070305036444032400034161941140d203445511601d00700450844c00031026541d4819055440d408000c52003105d0207540041c1c000e44c20003044882c2c0003959185109441050f0741c10b1140a00000d450783c4a4450640f0451240c3c080303800307030f4460712415070940d2a240c1400658120f01c9006000300119913002c100c14070007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 182688956 1250 182687706 182687723
    0x702030406111009030e120609190203012301031505101a0904091b0b03130b060d1a04030f0201021306031e0603050606010807050a050415050408101401060309110d 72
    0x8000c540c0f00121000c062040780410401c084144191034103400d1007000080c180007030441444d000b031885e40c40d070407ca43c0c00c0c0c1d641e012201490041d0b480c25031000c415a10100c0d0341626801140c0c0020100300401d20086404200c02015240c070001e40b40115030040c01d034080e03041c40c05418000c80c002100c90040715461550001d001d0000b40307986a006205030580109824140300c103da5110003040125a008414000010014840c6082c0c0c5a5030b007909041d04a800c080c15a101d52002856051400c50b0107490003c40c20903004100b860030300c910b40128400d85a8102040e086102a400e03405607d01e000380d1a823184c0e00811110740644c0223503000782c080500303103000464a0a00da0302110000d4009507083c1e0710030410030250b1758020b9401608120542001420030006181c02001c80c03181d40543e00e548640496070204182c0a05c06480140c231180090b2007415480740201001402c0c0a44110f0503035021100000c2e0b284d0091260f40c4081d84c204076650034540c0e10509201084c03501000403240c000c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 182690206 1250 182688956 182688973
    0x1a030615031f050d2301061701050a0c1707030e011e0605100903020904060c2309030c0f010c060e1c1106060402090d0b2e05031005070203040611 64
    0x303004011031040441c1481001e6101c0310071440720700007400340c000034000e0300500d20389008500e203000070f00b0818145510540d03130044a0303540035025104592210324109546040408100410340145200e14038021042111600d5408111a968000c6032044070458509020500c424400d402903103005804400114000c520322030303061440c0c001d0a03103071b001c51680d5050501c001d242c403a021385200549440c0c48000107056400251003400d01400007090550703074078005070110340188075103c42d00c0384000840410034074021040000c0d82c81a04100c2c40303801020650196403a0281c2010103101d0107075140d19814586545c0e45005202c0390184558a200381194071005080c1520482584102640c52103151242d0010503440d2801c0546410300c11030060021401c25180c0c0b0451101c200e801039403000d415180c4114980e0042040c20800081c00103e07103a102000c41ca1a000d6422203100740c088880010000120004441e030a89070b80c40140c004000401c000b9200e244010030a064580c2511074030b2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 182691456 1250 182690206 182690239
    0x15020a12090f080705030303061207030506010e090105060406270b03030c0114010906050607020f040b1203090a12050c09060604090f06051509030715050408010603150b0a1a0306 78
    0x1000800598001007024100703100301c00d0300c00b1002008140d41c200500e40e050038080002c1d181e00000344900d00905030a4401a660501013090302c00031038004040d10281d50b12441718440c80a01102e000000d90308000c042042400c0601c6010112262400a44104000000001c0408401d401400121501c4900f02e002c2039600f803005049201c254400043c850452410304400d07110164480d0400918000d010811500c54100710760351503074101c0304001d80142c141c0c0018014090492901d41058208641040440b400801003440b460202e0b01810300c15601c0044030201c015031940141b150b0058104003080d4106400001d8210348001c003043e00302074480f280d000840d410803448000c503648440c020002d90074092076074a541a121400c02e89003005c0c040110b43d5585c511f100e0140e1491100d12411813681c401c078140c0d4081c00e0b420340240525541c0c1c0c01c0c030040c00100c0c1c3c506850400c0c9001003041c900d10b804400601121040e0042c80c89120519006c2c00113504010a119005600204a000c48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 182692706 1250 182691456 182691473
    0x160509040213090902040605030d0903060504060f09052107030e0d020d0209040809041a09160203190302090a09021608090d0f050d020d090b0f0304050111031009050a02040501050415020a 82
    0x2500383e00c03c00090001c40380c0100300a4800d540e10650090704508500f602c40c0b940004604266500b1035000710304c58565103040002018600140c86070315181040f00400c12501081009446203400c5000c4452100c689446140e880387d460b004020480344070748078105007080d00e030000c0c42038002060201900016008100c06440485d0125980300340000c031150149000d1140d84024021010381503015920f0700c0c0801d800b0580984112890050280030400f584c0c0f080045440014038011449034840203990080c019400c03c5c10740c503105041c400c0001c2580e910360300c01d0350700300b891044020550311402d4a0302d41d441d502c01404035030007800052454020903800c060200300b2a00c0740000703141510405000034101848100f8000c01c1285a034020004202054281c2d0746c0d0682405242d5541e17215031074003038010070600310809a0000040200b154240082800c00100e6400d01c0301401259203440403031003244180e002c0c0343d010403800c0c4000e10121003100140181500d1030300440342802003580340e030200d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 182693956 1250 182692706 182692709
    0x52107050a0b0c1002091305090f0f03070c050f061617040b0a020c01110616120c03051f180b060904111b0105062407080c060402040b09160509040213 66
    0x402c80d001440d40c07600c6008012000182003441c008508122203a00045c3c00240880000c884960702c400100300d03080707001e02c15400b03c031840208480d03182032552a80c0b41c0301c0d000003800b0307503200071269000151030034407000c03d10300c00d5030042c0340501c0c2c503980000c00640e4280d4200c0c00d0318015602038400022000c1403000748044c041d004e03001d54480c143d88800a2800c0544066181000b21a4074246c04440300044c5440e04518a24850502c00d034616204682294110340134943c0305003081500c1d01a1901a44034038010000e09182e01030201561b00386040d082041d220b041005d8170a040442c40c0c0e000c0540c88402c41c454020440d61505050700001000e94038450a151504c910000d180344200b00d102c603001a440007100003d200c04d01d031900c00907080a2402034000000144145415403801c03500c012192082d81c08082c540c0c6884248490641d982c0c01120128000d0f4a0460284000d20b0440480d41c0301d106401502132410f400c11500f2109900718090700c076081a000e020083c03039050396044640 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 182695206 1250 182693956 182693969
    0x40b030c0706052208090d0605150a05030a080a030513020d2a030f0f0809030d031401060504150f180329090703060507180315060f052107050a 63
    0x1500d8038602e003082011103001030200701c10711070000190108100c03c040d424202e02c0d000140c3c9520b172000740380440c180e012000c1004120034500030070007100c80385c03001c2e203a00c40950a6400e0560691544203066466062140c082d0600005008540600e4401d401c015030101110b4032041400002c2d41c0403d81043c613540003160300000e401c1419648080403c1039090701c00c0d03001325003201e1500e5510707074154150f040000a8100707046542000c041c04950001c0f211001e60140c101d421407144404003c00801c10040c000724030380304410000440d103201d84280d42c10707141860f04101002c1e40d03440c020780e01c0c2c1d0500d100e0300041c814600c441048a02024000f0030082d800b0b54a03030a22880c1a0747c400c0c82070001c1c228440c4c00c1c5410142401940080090594144c96000100203a0740d111420b080c3c03804000890001c0006040038408410012a90880d4801e404d40741d0051241a440d040405100d040c0f60050541058547c074445d01207480d03008801c010a01801d0940780e250b41c0301c402180280d44c4640021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 182696456 1250 182695206 182695231
    0x13020103180f1401020901050a03091b0b070c1a092106070e03060c0a08040b040f080d02091206070f23130501090602070602061503151611010b06040515040b03 70
    0x140030f11080d0a041e00d0700b40d40340070085190802402c00030300340d0700a1104010425a81c0c6800c1820003c000703828843c00f54020301c58031007860360b80100ca02d09a0103000e0481d658680003c0000d40401158114541c842d88001203d08092a21061040c81c4901925207181078080340580d900001080c0440380c041d802c03030781e600d0360000c444209051520304050f042440c080301c104840c1c81c0b1103900c4041d0540003688051113990a4880d81408101903030f050002078240500062101e030302d40080c0d401880340703284c10b5440e01503030f6401d840740540751202200c0d84004104e0030640696010310440c2c1c1d0030204098100d1a12114850064580c81a0028030070060050040c240500c02c07580c110042c140280003034801014002c1c02c14000035101d42d005040c000c07138072030707880c0b21166a41d03814052081c90940041100101e0f00c0c00e038550b10071004d82542c0950106800c99000340e0443d20600600c103054001401c034920f0145008c040c0200421512494401e0038020b10001c03038a0041ccc0d40c000d40c060f41146805 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 182697706 1250 182696456 182696483
    0xd0f0504050322030210050f0c0f0a0b010e0421050c01140106110f0c1903150c0815011e0207030b041118010e04150f0207080408060606030606031302010318 69
    0x1076000c0819040f40c2a81c4804201c03000f080140d640c43d0104d0b00000140c0780c2a0344603600301582503080d014028824245000314209070f50901c2c00000d050124138010741103a002640c0c0c46078126401d40e816100900858203511901c45404024003110801a0313030380c0380441c41e0001d1741c02c0c1d0908542c020700c031142413051104010080d4a0b070000e01d06400038241b00c0500f480b8403001452a40c0d81c000c00c06a640240d06000c045010b400180240d08000c40d0071100010889003120000d0380100408240300340482c8414020507a110007000c06d81c0a0341c1410784929a40d10031411040c4541c140d10503400c400c48c800c4910110015030f1070290705002c1c83c86035800d082c01040b50402c0141c9220202e51058104c03602500402c0b50300c605135401034129811910065a500c0c002c4d0f00760303000d03002840d44030145900000d40c0d1010454130720004e2048480107801d40313003ea103c0c02c1c10851607100584580e5070201c014804100c040c000994110320151050400103602c400c260413602d201400040261b542120b036418 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 182698956 1250 182697706 182697727
    0xc040f09060c030b090703110906030405031210060e060d0e010e0f0c0d11010807090806010f03050c040219051c0516031d0d23161203050114060d0f05040503 69
    0x102078102c64142414054040c2e0f65000c6181036034014082402c140d00c07a102c0c20403808189049420036803000c0c2010380d8900e82410060b5807640704200422003a03152100265100b0305010549013a503d81c2c1c0c1d01c480c04169801c0410006420071059034a11503502c10840180c444c091027070b51401c2040c140900016004001120b0502c09040390150180c00d00054000002e503842c0300096045e002400e003080c1070f858984c07003100c04018a402440301c0303228a000220742106500500e00440348900203c0785940352040c1070205038016031808204a00025410104007801040a404c1c14048503110840d4203090343c1040080c1c0d8029903145604410030820300039095454020b8007500e4a92082040394007420262403950303003054000010030040c0381d409005039460b15088101e81e010301003041d20344030803514a06848030800200101c40c005e00101007110298000c0c0601412160106089003400004c0c00a2004551201800200700395448603140c0e2015110f2180034003075800782009645071811a01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 182700206 1250 182698956 182698961
    0x10b061809011a0a03020309010b0d1b09150504050702030705100c111b01140c01090c1d071b031202030a1a0303040513020a020f07060302120a0908070f050c040f0906 73
    0x3c00070b514000f81481540008140781e0103c51202c142842c00507541c1d80d4060500703004244803501075510010400101c4140304604808100c500100c0c4c01d8510056685c140980481d4030210800d100b45642407003c204502d06a4802d542c003001e2801601d2900410341d8805003801c03412024520704541e41d46030301d030425602415121400100c00001c040c11504410140c0064500701c88080c100000010a0000009041c0c25288000310b1316000348456100d51800f0380c0014124020700d6011b1070345044032420351460b0381185028071802c0c1c548500546030300204156142c1518415070500c44040c04510311680e0303a20082d07108164100001410b25040d45107038034505500c00605101750300521080c0420b075109540350303528002d0a540141d41d40e0101c08107a08011a0319400300b0103020356440028445d8142c0c0081201c98912600003103140e0322446c0038400c035901800082c1c4405410f110403400604082a80e111060250040b181c003407a4000004043d02c919041d0100d80350b48818003001004002d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 182701456 1250 182700206 182700209
    0x3120216081015030803040605040804080d080a0b1008070804080403080a080709060201060b0a030207051203131a0c0a0f0212030112150b01080f040309030b100501020d09032102010b06180901 84
    0x111004003e501d035454074005404064009480f082ea6034004c80d00704545841100c005041d403400781c1d109400c402c5000360510344100c8030300e002c01c1c0c249191100145804400c0b00d802054075114018240c0711070f4000c0755800b030f0003481200c04090400020003c80c104a006c4d01070030314266217445982c5031503040104a0389181e803000055a0605130140043c16607041643c4c030301080c0307241c0142c0356216070030001e15041c4460f0800f42c1c146000014490900408a003201020307014541c50f5550180000310b078040080200c1300c5d40d81d4104180000340c5c8141c0f04942007060042e1600c101c40c0e100000c202d000e0301a0b0b00a9000c8443c5031a9131200c0030400041030814152149a8030302000300d40e88a000180103041c00800060206040c84009010540220040300156070001038540e5185044407101220b00180e001e820301612419900c1d94045214840a505590b48240440c90300b6900c403141944030189166480203554907034582030119180c09019003c035444042c1003603a142d588400b400842c1006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 182702706 1250 182701456 182701481
    0x1e0d15050f040603171305040c0503041a0c0703030b180114040c05040f052206030b040b06031f150e09030717030702030f07030c08070510060b0a0801031202160810 72
    0xf8107000b040484c3d4031a0f482c1032100303a0002d00e00d5503240e111492440c00e4400e03400a5500c1850111000c101640c01006117110381c2c41503050b0f06100300c41e107110300e001c8001102c0e60844030604116400000c0d01c00d410451440e0b05c00717414059191403050400c100200240c01c04800c3c0c0c0c0702403142801d145014040c1c000307401c60078100b16180901302680301c81d00c40d0041c0981401124900c403010b4449014000d2940310031a80582004619120310f811034407254280e80c2503d00e1400380c80410001c1c900491031000b41e11508458032030b14108075617944054101d03151010780310900704100061070340706d101e03030b05218007501c6003e5550b9592524112a042002140841102c103080c810450074503000030460b0256105110f03103c0d00d4055030318007201d0b4440d251704010070780c0a0110b410020071400098036680183e5241c2c0a0240986401c0500060f00404500074000703040100100041258200362406000041c41a11044000000121100314043d4048140c0354080c005c130600d207041500c1003c0d00340d6903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 182703956 1250 182702706 182702711
    0x201050a090b06190b04080d02071d04060b03070b040314010507080721020f0403061b030b01050909091908040611061e090a021302040315050105061e0d15050f04 71
    0x4645036203000e0b840082449020320307503024415580c0500e520f0400001e006051146075910388070000142c071000107007211405440703040004903480c400070060a40c400c00030502e007002c95440d522003070046d081e0b001c2c42607018014160081510040d550051000d54020802544c04940c01d244407400c40c2c000603c0b8104000b6000d090142c100d50000605d0300c524081184901e000a031007500030024841c0700301c1000b0320301c4001000010042c0c20f800c8039801158144520000610401098081e209141c800030300060781084407010901d00051126000003200003203d84402d00c0881c0c000f00e4040d0303900c080d641340c1004241040340d680d1220b603c034001c14030080601803030b00304400c1010002188042c0780d15580c1d89080007841c1d007a0308026541e0040d800906403208401a0741d5682c000390710074007055500c84541c4200382215041c03401483d04032100a00250f10384414158640c4645170300c2c030040c507640a800c1100d005400514041c034600b42030245501c0b91030724545000c202400340040340c40c9000c0d0b030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 182705206 1250 182703956 182703971
    0x50601090b130806040b0603010e06010501050f0a1b0b06120111090136060e060309030a0c0807060509060105010f0c05060103110f15030709080f1b0a030f11010201050a 74
    0x240d1200d88a0101c80c515008161100c040c4030381981c0020564100801a02c0b03030300200028009118081402200c095001304102001c032811079864800074010940855402c0007400885c0403410001c00051402e0318001c240008113869088120000d40d03019654030f0241010b101d458a04000c004210203600002003040b1303180000c0c402c001d8000c010b00b0b00d061005a40c110386000079280c081484800c251740c80028a01e0544a00401c030450390b008800000c1d5101c0e480ca0302c2d900f00807003200d010f804c5a100560501030303112000c80344a00507240803100480c0c00c1c002c1034001881401500d00452809002e402550b060000050403044c1281a41040080303290340a07020403c00700310b0074107503500000b40380003145071503000c280861110074a103078012044100400b410304400c4003031070141e265603461301070031030b40c4402c52a0b50741255243c601443d0042003070401c0d0b103c0001101e0128510141080d005987e894a660203481a209425074401814805001d019a42882110f9005407100d10410644 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 182706456 1250 182705206 182705209
    0x3040c05030712061107021003050a0b030a08271c050105150d020d0204021e0702040c020f0303070f091a0a48080c070f06051e1602060f0901120506 65
    0x324100015084e40e1751a1001c01c010480903003100c0c9403540150003100c0c1c01c035004000400070801124070f40200d45c03a001c1060706510b404200180c14641200500d0708282d102d12150020500369005030a85824823603030307084151615400c0202d8480d1100e2848000703c0182455400e4890007894084c03a0300340c40c0b01d8899075643c0d4118116080e90143c40c0070710760050510200e030092007241c40b500031002d014864050024400710080202501c00c1d01d0a00c80c1f41d640f030409a941d03951006c4c032030040d40c000b48005410765200b40c0b0300f80c40f403076804d2920304034031640d802d00b03c8501800c2d007503002d1400800240c83c104860300036070b03800f20403015420b1111422442c040c90100210400700205c2c240c2c207602110702081894881c1c42c80d0550f411110841d642da40c51047c10f650380040344103052200402a0700090403500178000e98035841410070f8154090708007050130361040e500c0707440c0c00c03404140d038020480b0258444002070007194030340040071540c5108501c0050f00940031400e00500a42c10b10003000b01c3d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 182707706 1250 182706456 182706479
    0x30c07140f060c0c010e010e06060d11060301090c0305090d050a1202070b10060f020a120e010203120c030105040b121908190905090f0f0118020f03010b03040c050307 73
    0xa00e80152a800e40d140111010905104003000d81d021184508400e10003045900b40040031882000002004003688050380d050a80c0e403a44100c140315007100c0c000a00364203005081041d1944640c007401c0c0299020800640140c01c203030402040c0701e0f0b0715103110600b00d41500c2419000010138005001104803400001c1c0709105903220345c403c00010010010800c80c1e140c0564410a6020641c2904c5192400c4d10310700000e0741d4418000094805811100301078000709030f030002c194000303204d9440d40752824400c2e02d161421400c0941117102c03c100140d15a00070208041c05110004911030f40c80d4035110400080d58040c1c0403062080c05205100c0090100008101d8104000f0703041d18000f0350100d0170160594020200c0b65075010b01780b416034042590340000660203481084840309999218500d0340c44001c24212000b6a02003902c0005121151a40049446440c621007000d460424802c0c001820303500280e004c01c8065101000384010010688503050140c0400e1340103103c59440d00a19100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 182708956 1250 182707706 182707717
    0x6050a0b0d060c1101020403050309150301030c050628020a02031c0203030118090f12020706050304050c041e06080601050f0d03120203040318080a0308060915060c250602060a02030c 80
    0x128540d40c26251460f03a003d40c1e044c1c41e00c05018402152144d40e0390a0080c0c40768820200c4c688038a51100d0300f090701d0100d08060301d0603682c00c1002401241e0804091204980c000385103c1d86100750a4480318214411402411100340c40b030b40940400c14040c81414509454003400c2c44140420340640503106a000040e82d0441c0c01e20140140808208494180203081800303000c0d01c1b030886800f13000188900ba21000e080f04005501712810a5610041112540001e480051040d04150100480d038581341d005448005004004541a5130400031107808a0703841e0b034898100750300301100401081c680300880781e1030400284d407480441c80e155500240a002c45481d090020b9501002103018540b00d680348583c000c250583c0e03855007a49601d80d841d9200d02d103480481c00101c0b01000981c80c2d051030030600380518440d98a8a050803828402c10440c0c1d0000004603d080c40745a82e800090b03000c2e41105140b41100940c10202c2c1800e0102c000e040071030052404050314010402d014643c0000720444c0c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 182710206 1250 182708956 182708963
    0x140106020d200d05040806060d1208041b120314032707050301050c0d0c03140a020706090605010e01030302100603050715020a0c060206061801030f030509060f070b0406050a0b0d 78
    0x484552014059112000300c5003407540091080f000440c1c0c2141e00701c0003d005032440001140c000366165010000e02c00c00e0f001004049070b038104242020b01d0700812640745c0180c41026100c04140083c0c00b18461b41d40c0130380c8039842c1c2d410341c02c51503001e040d00440016011041c1d6000c10f403035440d20303c1203820110110400042022070840484058030000c0c00482e01403d0000d000788181d00345000b03016030700d4000030250603402e0315001a85a140740a44140c1c0190460307100341821558440c48000300a41005d40c05403140c6403207180100c00a6180e116407030107407482c40840e826035411405d00a2505918a0002e04a145085018000304500083d40b00844035034a00444075103824100c101e04024480d00001c200701c01126001c6140354000c100782d132050b082994103c082040d0744503103150f442c0003840040c2c1038034510100407001c01e210384010003040c040905040c0c07406816640c0d001d443c4d0702035401074520080709014003041080324000c0d0385e04200740f640c040c0003840804c00001d21011a08034000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 182711456 1250 182710206 182710217
    0x2070b071214030702070905070f0c1704030516030b180a02040902010c12030c0f030c050f030a090807050a060f02070b150102010b0d0b01032604060509030c0904031101140106020d 79
    0x7107624841c4005980360348410900c10385a040209021755501c4003401030040d02801d0100107036038640704205100011449a0718845032410315250f0b1000c00b0100d0b440345814900800000c004540204000201c100d40000b40c03604051071030400c40030107e0041c1403901a01c25850800340324290004e03a88080e030b501128001218a814030060360705400085000701200442c9a00c01e0040c0d0305030f07000f06214070f01915400311541c00d100049080350301402205000c14018810508110758060141d80d020f8803800001600407200d455407d4a500b228000b00d540c0e43c010190308080005034020300c8084111200290308260b440c0c0c0e550910840024a940300355129030040d004268070075000420a2100035140400c01c22450600e00400702d0240802d64140345200394540410784111981c080320001502d1060515041c000c0c1102e150f4021000c1640c940304030072a0500540e01d19500a001d540f007901c0320207010000a01e4103003901c94210805008951400041180d03580119840252410500d0b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 182712706 1250 182711456 182711483
    0xf050901030302032704110c0106061115100302060c030a0906020a03090605130504050901020a02010b0609011b080712030b0f03010501030c09021b030a0507021e030c04020f22051002070b07 83
    0x208901803107075005061b4800d04004080c240640200000e10700c10880c1c0e002400004d840d40c000303460000d00c41848414a9000d0440d52548103d180c441e0743c0c01c1482c250041c50001c0e40e90300090595000200420416040043c0b008015500045000700810741c500242080d5161500d01801c1005a48a00402c3c04000583c3c1c40b4907a64090b004002307454014810809400c201901c24000d410009000d00907621700988030000745028402d0320003030301050b51032131000b903031500b02d42910742900c03035007264030040c2440114000ba05e910f00c0204501c40c540e0780000c50075100320420404440389100c89002c1c0c0d1400d401400801c003282865019074000d4130000d80d0759940e4030b000740e401400300c0d45200381e640808241600b03941d0380180102200ca000320341084010003003040c03154070b902d420503029501d035209149012441c1820b03005092221040b2100c64104000d4102c40d4030210095540c07921200381c01003050099250282134401e03501040d10081c2107032406c0c00c20400c3c1c02c0c840d5400c09007042500608 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 182713956 1250 182712706 182712757
    0x20307030e0f0c010201140105090604091e0f0218070807030209060c1203040309082a01050405040c090e070e0a230d0605010906090e030307110f030a08010f05090103030203 76
    0x201c1d2100003505400c55800082445405440d103840c00e030214011350034410304001c489003207070302d050590700b0040c04042c4c02c0d241c000801000b4a100b10307007156403803102552442400110b00020044900604600464400503c10003405600d041c280011140d411001e01c0f411660203111198010464100181c1e00ca522900058650141202c0030100e813003816000c14951300e43c0000b540c01584030b40ca807104290345405145403100354403840388564070740030003e5070030848103000c1c1512083c4042c1009480c0540b10f0b00858181d48180c0050404907a81c0c45080000080340b111140e405040d031329000f44e801c03840500040e802d04851080ca0103c0400b80001c0003d040c00704101c2110030002000e0300000301191400c1c0f8050700c0309100c0d0150749c600d040320004070907085001c1c0d40405c0c40d51728081d500d140d540140c151090100c06917101c5d180e2003100350200380540f00b00000d2045010b00e488104a540c94100b5555441c0e000ba0482c0340992145401000060703000016500c0c2107805c0c0030060400c034024072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 182715206 1250 182713956 182713961
    0x503041a0705160804150207080303240414041a09150402130c020610080a08071b05060d09020301061410110c060d090224040b070602090301050f01080f0a1502030703 73
    0xb00c02d0300240c5540f100348801c02c141c0000804c02c45501644101c401b129000c13090343c0750306151145450359041040064801d10034141d01d000c44110198241503070402550104040700d206092031541090170105100501103000c0f507000d090003c107465829240b5000c60880e4490100d980c01041c031101d14808a8110341c0d40b11002040410404420001e182c40b41c44020b64488044c2c4600010030f2526401152046000c00c810007501d41014925240c003030555100180c2401d9180d0b03c68410511000103c0c80c0d82e10030000305000d40d43d10b14040746508040c010542107402d035910000c03171141d80b11a00d04031500c1c1e00010030500c80311401d00e8200340d110a9001410941c030518402d6101c0740008410450000355401401c00d240280c03281c402241d5418041c201703040301d900c000c08009030180410000d082c0703c44014013040b446401c000d4100740c9000082400d4800503203801900f8050346005200d0078608000440082c9100e1000740450300b81501c80d00c69034032041840b01501070700000081c5903507000c1e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 182716456 1250 182715206 182715217
    0x1e1003020f070615080d170702030c010911040f02070b0a2f120108160b09150313120c030503040f0c0308030420010f02070e0a110c0a0201080105010503041a0705 71
    0x3500d403140d842c05946003d10050900f920340f60924907840300041801400007490000b04006034640c1c0c500d4130356005003035801c52801060f000c00c40c84208110503110800380500982248a05a07200400505000b00002d840c254130412014500c1408800045800040541e80280c100741000031130048d450b03101000d5041c1d10959041100c08181c1c0740d02c4503680d000040060204c076020070f60030703662100d070102d0300c441032002c01304074100020f42e00380000c0d1007400c001c05280400504c8207a0040c440c2410984541040b0b8100c1a8400c0300780b425000c0c00383d050036040c040d514524050541c43d10641d80600240000380014040c010665400e2041051250000010b5900101c032182c0fa40f03014608019102c0b100d030385040810500d00001c201d41c2d4025201d0b61340000040d0040e004a40c1003404001c41503100070101001c00f40c42c1c0c0741c4260015039180080803000403000140600d50b0150001504c0f10300c06900007410490100704100200704448034600c29120324045418264441200489207070040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 182717706 1250 182716456 182716477
    0x10806090703230103050606060a020a0215041502060411030a33020c010f0608010b011209063b1212150312070302150f010b1e0f0a020c1e100302 64
    0xc0b50f0984044844111401d4101c030312400c12942c20b0f644510038096180a62101c4001603405212103800500d0711019240f08441182c1100782810340e180300880200e008501240c01680051041c802030009031821a90205400d134020081203c2039520410090410060322038810031204101400030100300000d00001c038419415500c45030540380c003a00808610004001c0c5c0c0b450003100090070003040c0110021044140c480090443c40c291410000e0300c030a00301240e51503500c8581c060601002c10700400d0700300003960b007a2624018020340c40b5440f0410b011807100380d0310016240f42181405000c8503495003c4415400340360312100075500c1041c0740740c4103403603142c0119664a04401c45800140055500039422604d07014440f54a404129a042d2594000c412a440060009a164200034042405c41075564900c40300c0000c840300440c1c00500300f9400102d000100d01902540c104407a082064040b40e0300303051690342c0704118421060580045020f03000c00e002d546481c900035416600200725 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 182718956 1250 182717706 182717741
    0xc0715020c041b0806040b01050f0c010204091b1205010807120318091b2c01020a0f03080412031a130603020405040c090c0503160e150a0e0f0609010806090703 70
    0x140c0c043c0c01450752007074864000840c110006071017480c09026010030b0030b40685546203400c01e00000101258409a0f075000b0b20341d003c200000310303600544a01034010404000f50310207500401801441013006070744981a9a040c5001408a80c034081000801c0b10098140c2c4211501c0318501650301d1481c55083d2620301c2040301000592240c40e400c4401032100f4001c0070204100106401d07600d551100c295501c1a07809680e4100b20070740c5120803c0d40e8401c1c14012a26404041d81c0c070b48201280d80d4a00710005203189081c0000c0044500d5909820007250805200401281c2c031011560502660b0f850305c10b40900d845c11030002030a900002c0030756000b403c188094600742c10243d00948003441200f0607070303180100d044059840340094901a444c640d81008108a404408803001c801e40103207590700040b14200002400041d000030801ca1030183c5070b0400003140c4104010303601007120b1125004540c20032110342186e80c02215684c5c445000c81e4140d0154a40c01c20481c010310308414150030540c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 182720206 1250 182718956 182718971
    0xf08010c050724140f04030906020a150b030312090f0c0a050904120306081e0606040b0604090b0f090925050d0320070303080a0b010e130203181b12030c0715020c04 72
    0x90250300c08506c00d60003a00d076000d102e40c0d510303000c0f680e407810808040d15291a0712014840c1e03140c6034000c01003095005007124140f041e0560b0000c0c0c00082a10403c90961000325a100207010a01000004040454030004a2460b190104089442c000c0c40140581e0002083d422624040d9001c500038111010444940399070822a00044500c4507030f80b125a8814100000d240345803500582c0d58005000d070441e400e00d40303005040409400d0060803903600034480b684040c2180c44440d219441400400003c2139180a00d00030306008404125403080d0070340400f070003400142c071548001841582c0c145400040c01e021078113440d038402d810412211407801109000801d059004180500640346480c04000e441c030040c0040d111901c6c1000354942015a54030440c1a242041c2c0c06154000c0d6446a80242200307070044060500001c030904012051a003040c03042e140c2404050408800b00c0340005501e402140300002d66951301c140f01e40c890a001c42c2589502c01d5109200200024ad4054010710496 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 182721456 1250 182720206 182720221
    0x21509070303020f01020f040512010603080d0203010510020703210e1314070516030e031e06070314060604090905070902040305030301210f0201270f08010c05072414 73
    0x2490300c0d11040d401442600101c04090506100721984000b0b5186410f18180c0f0305014420110100d0004405d25541c0b072000002140f00309006000000f4109030059980d81050300304030302c0e18034600411301154031505043c40042c0b51034200c42c0314020681000c02c00101410b1084a0074100e051801e40c100000d18485250001e50307401003400322560500c121f201c0e43e41c100301214a8040c4080d20030481140d02c40c0030000c24010074560350700c0c030005030036502d001c21500814480000f1800b0359292940c410070400814592501c03c0016100341d0902c0d100c101d04000c0c0024541e4003c030f000d4214119900c490070020001d04014000051803140004d6449954074101385803a9002449803409040c6445500010301f01d42c00240f040c001d51090414142c00c00da074004480b2011003982001c078a20f00c00040800440900010000500d0b052600d14400c604281d00d00342540c001044038028000203004d80000180046d4450b071104176814401100e000c900444240a441480c01100e07030504001c0910002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 182722706 1250 182721456 182721463
    0xf090a03080a090608041e060609051003050c041a060306060412050703112d0111121305010e0a090b0402070f121418010503040203010b03030a020304090f0c0c12021509 74
    0x1072000030f848500b03080c1d5403601c055941c45070480b0001c00d500048001d090100007076aa00c0301c0801d00034000000c10980b0303821504126141501d45d015250030b840420800c021003080318000900058030140100c140c0254442c14403185c020a6074807640780800040c0560b00c50700b0a80e0300a0003034400c032001d081c5081c10076a80383d2505d4081030b1603d1a1400c0c6450b0203052046d40c0d1907902004c3c03090b0550302c0800c02c0006400100e001405810442c0d250034100007442c017040f14610707180389408119a1105241c180807003121899101c0e82c14401d0400981003035a035071071001c1c403c513400c0150101e00c040f90040018001d10448500509080514012038140710a5554039090001783d515030913440d807492656040f80c8c1c0529009a41c0742c02c500140170100d94460009142c0092020300003040903d41000001d04580000e01c004005910126003000a4101c1c1d01039100c4594084004200303604103003070003c00080a042e4082c014001a84000002038403c0001560300c84405101400e01c0c20300041365900d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 182723956 1250 182722706 182722717
    0x807300f1a070c02061317011508010606050a121404060903020d08060303090f01051201032d03080106080c09120d140c060402091e09011508010b0112020f090a0308 72
    0x501d2403090340c00300c00104021403624040d031040c2e00c500329100c2d2960b08000380342c0e01c00342050791590030042000030980c61030344441c3c41c8604100b0011421465482d030141c031218582d40b040c0d4603070381041010058150410120f60000742c01340341802c0620456643c4038050004280350b2080503241c0c008020903c03100798402000180300781d0035150342000c0d040048501c01070940e00385515405c00c00400080745844000401d5000d010b05140b810055900c03961240c1c039030260300954541003903000c1c0707542c1e190558442e0328120340f10803d032940b000010f44000b002100305000301400e102e0402c01180314007881c18140d07221201e00034030101000208130490342d10313244001c1d078982c0400c1e5403201d43d410b042c1da003000303492001003480018074041e43c0f607808001c0320300e0025090113008036000c8141d156119440461500c150981400401d482e000281c1e0300301d031040315a104a038964905102200d0581e4802c039501615003c0f00409610707001d525403841c01c04e200d00c0340480c1d0302a0441c2c80010402c80250003038071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 182725206 1250 182723956 182723963
    0x903040b1309110319020a17040b0702010b0105160308250e0406050f03031c020f03090c1804030f08043305160f03180215030615040807300f 62
    0x429200c002e60f0aa0502081d1140d00303481c400340c240d202080680d035003d45100c10941c0750040300c40714545056900c8001c1900c00395691005142040100c0340c09000d000c1817040c0a00e401c03460300030820301d0140b240403070640003410416040c010400081e1072a401041c0034080900d0070200ca4400c940c0640981d501d07651140c016410600005040e02d00340740c0741b03129408040c015619214140c401c1070395511034015840461503081c000020490340401c007a6101f011400d00500070000340608000c00f440050800724140b242c01801c0000080d480b0400003600005c40c2403070090754a582c5407903541c50001e074801c4003000c15804059609048584d0140c0c1d01c12c12400c10400154681c0650001d0050040c50050045039035151480541072080d4000004281c04042d41e0400818542c0011183d404542400041c41c0c6c021040c84010321701809109160501d00212a241c1480e00121548170415849860411104c071802255244501c900030518104400308101c2c0455951400c4214001281d100341c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 182726456 1250 182725206 182725211
    0x10f0b03030c03120c04090612060f0903090e15030303071701051e1306030203100b01030b120705010c03090905090105011802070c260f0c01020f0105040f0206030903040b1309 77
    0x66582004011202c0d104070982c05185000c42068051500e02006803d200740ca0104100014118941d03100740c40107003845080707105990113241002c03419614240d10410110785081c1c403810000c0d4010702c00300101d64601c443c00c0e0503035880008881e140e50302c4488040d00350100100304081c00390301810051032007000e030140c003503180d0f01c60013802110003c051102918205040700c01510b8a03020508a803081c0b00c540c0c2c04514140c803540800d007030500590121880680744d180c0003075250f8150081440b003090a43d80a40701660012105076500b005100d05410b01101070800000d242c801c1e90801c01400d0083c509205a04210340154001c0109200d4011090010450841214801c0c02118042070b0805c0c0c40743c04090520200b2081441401a03022401659841c0c0c0403d15005100c00003483c1901c0b809403003000c008100190802c680d240e503001c1a81d240404000c0019010151440801d4054490a85980e02c5040039469407066070058541424046103c524811910741140183e50108005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 182727706 1250 182726456 182726471
    0x3010b040905061b0c0a061d01090c14091e06060708160210051206010f050c100b01090f051c0501150b03160e1e041503230f060c090a0302060309010f 66
    0x1008660141c1940703d0f91302e40240c0d1b903480100b01540c020380d41025480140740c41c0030b1a000d20080c02c44a82c24021111240404810000380c038803821404030f00c1a098410312a50302d08944400407400d11461542c0c4d4940d4420080381a80d04c0d40010349003802d62180e09243c3c4c8800d20f0810140e42501414101d224200003180b445006105e5404d4401042c132014041c5200d40b50f0000540e160f10120450000308002400300b054100802c00080a42103030541c00003965407413806c00140039601c190060490101011020802502d80814010501640c03c60b40741410b0304901e001c40c09420380b0902000612202240825000f1045004602070f10307103240c8010501000407025256800301c406c041e40d2040d10403c40d03104130050340841c5038100600510000319890b49120400403c42c05800a59102503000c0c01e810703010003e101034101c04420b01009220320034114403d665244801070580c00800c00120303010b00e080e200d040b03040e006103500a000b186ca078580714010341c0c028401c280e50a050f0a050440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 182728956 1250 182727706 182727751
    0x3051b0d0e0d0e0604060e03330109020a0c0609080405030a0c180506011b150539090d05010e06040b070f0f0207150e09070e12030f120603010b04090506 67
    0x841c1c0300103c0000d0400f50800e490300780182d881d014880c85a907014024003414211242e4807040007000400c480e480b204000169441c2c116121030140c000003c2203204000035059245c0151150704010351150700031030000d03070601d86075109002c0c5074051074040c03084000c030360100001051220242d42641014010310802c0b509441e081e9407040c1c41c1180031400306004440b000c0c2400180e032002500a40c070520028044100b07420441c2c03402c90b400504000e56032014078042c0640385220b21300c00755501c0c1c042e504020103803c40943c4e11524449a105500100801b01001020740050581c00115429540d50b031905040c10031020303c00f00d42400000307060150140d4010b010382c074817007000c2d802a80140080e03401c10661414142014401606116808485044c60350313a18500310f11a02c0d060f9907405076080404140010307952090080e502a0700700380141891803200ca025101c20881c2d02143c003509440348004030340100340c048c00d0301d80c005003004685070902c0030010f1018021949426100d00ca80305000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 182730206 1250 182728956 182728967
    0x30103020616052b020c061e1308060c13080f10150504090f02010305070807050f07060906051003110103060509060f01200706080a1b03051b0d0e0d 65
    0x1009612081c1484034005030b1400e0440d1850341441074080b90b400d04010850390b1914403010300c070341512007040124899101e07414402c0c4030300d5001c1541c0c038a04166210b11100b980d005450264040520040761610700c6c00c81250354213000b0b00403030041d541d0504021030340e11300da9400800040f510000014000951500004940645002420140c0403401c000e001c4036000e00648030f8121001a0544004142ea0751640b14561003140300f00940441e2684501c000342c240c51004100c3d41c00e00118001b04044a608281118940e0071408212a900d590764070300310004140000c0d015103503915007020010390b4080464624192401182e10b40301401e001401101521b4660003403c0d0488000000304415044c80084603d100703505040040c07410700b84d41c54800c5d060151582c1500d0719801401c04100703003508040c6190700400310007800d01044107155501058008122545d4040603510340c0001c0d03a0790f01002c0c026031110300c00c0f0815030745c034045404501d01070482ca10791506940542204094018040d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 182731456 1250 182730206 182730209
    0xc03060b0f0a0305040201050c030d0209100906020601060c0528150e0d1b080309030d0605010e100503270a1b0e0408033c13020a211202010e060a020301 67
    0x91140310b2500103010011409400c010300200d040c480c0c1448003800401d824806405001c203003947c010781311a00c00d400c0110080c4000021001d21800c0081440603507404166141519450f0420a000101616020307151400d0481c0d480c00a0a1880060200740e100c0c0c0c420345000380c000c0031302c10548240040000b00300c1e031007805060400c6e0b0020b0350108580c4c0c02884020742c500700c1c0d01407800e014050f0b629190700b036610840f83e01e4001e03080084c0061029041d842598050403082c40d00322004000301c004101e90240d10200c12081c400013000180c0c4403001c50104580387c0f0040c424500115a041d1a032595031103603848100d402d2410007901c7c8e004149006e1003841107506031300c00382195440716218840594805496028034020039180c09490140d041c84810711540010700034900300e40c400c0020309a032840a01054242d14a903158a0003603511051880192000d0641000701b041c61166610305055040e03200414410f003031801e80b64290380661008001012100994113640d4509111408a03c000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 182732706 1250 182731456 182731477
    0x40b0f010e010510050c010f06030c1a0a05070602070204060605041703030f010b070201052b0507020c030606010e04090507260601060c06020708040915050109140d0b09031209010c03060b 82
    0x50000410851a24598000f000340381405c1551401c4111529282903402151034404119240d550800410030070101ca60020f0540000303030540d8106001c0c02c90014881c00075544100103001c14074406200141c1d044900c4c0c240d00400801c40035566640141143d04144648403da0500c820100b2100d400841200d1082c1c120790b000d902d05030f081084031180c58201c0c1700c1c1a4104107081c0441031800422120302180f040d0401d128010401400140c1c0095481c01480c2000719004005050030507200081c0090700844242092039812000da40490000c14516501a01510948000150b07880740d20815451300c6103041402e9000403066045607075944020f228140024010032a4080400c1180e80600307949031203034a10b54a0943da4455050a403540e403141d61600c1410400104415070b00010533030014940d0946002034203c103000014504081c4080c050258041a4001100c00c10180229155074101510700651814440700140c006d196410001c80424030f410320204031124a01c05548400c1071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 182733812 1106 182732706 182732729
    0x9070305120405190803070201080a110d1e15030605040305041a0a030614150f160503180102071512060b0d020702042016030e040212040b0f01 63
    0x50403501044d03180798a2104001011000c000e40d07a1031502400d103030301c2c565980c3c40d00302d001c0c100306c00c0d414010b5500018414481000c0b6400113802d43e00504070300c141a42801d080750110380741c400b4014610310300081d04100140540e00f03d070398484d11a141a80c20207a403000f5901840662410f40e181400000c48d813201c1c0d46606120340c0b4020a2298015409510280041003080614985c07034502d10200083c500e0a2944d0441240c1924120902c1d9051707080c6941402500c0381c109001185405c5040314694200c2e41c40054420107039034103040304040201b54084151000c3d141c513003000300602e4513420f00113651a2000007809007075070780394809039440e0304920400c0122510071850103804442a00c5025103c100701c01681c00201a84500b010804c02d1410103941d0700d070808070202d41c01800040c0d412400328403006d07140e000350301c00c0a40c0300b002c2d12002c46e44201080c00740035030603000c103 = true := by decide +kernel

theorem cover : BRFrame.Cov 182553956 182733812 := by
  have h0 := BRFrame.cov_init 182553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 182553956 ≤ n) (h2 : n < 182733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
