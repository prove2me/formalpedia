-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:55.785983+00:00
-- url     : https://prove2.me/submissions/0dcca6c9-3cb7-4d43-b14c-5455f0b86e94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 366906474 ≤ n < 367086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 366907724 1250 366906474 366906481
    0x12150907121109060a02010209030c09040506160e0901090902010e01050a17060a050405091e030a0f05130f0603020a17041a0a180c030b130308070f030906060e0105150c06 75
    0x18a90b101c800c01c221010071440c58114100000340d1550400ca08000050b0740014072142c481c00c00f03101600100d01e050f1a5a4070368100346c2c0d20981c41c0c0800501d004883d5080b582640800b40c4100104c500c00103018043c0801c40d619035038040054078418000f40d0100390303284000366482d4401d00441c0c2049920741d640005c1551035000c0454000005450320703a02c160707100c8000c01e55541d144030701c600948203a0020248901e00845608540e070364503c500119800900c081410b154105684e4040e00907103180180d640c1d082c050132203183c140a9040043c06c0031b03050360b000c00c900350981d008004a94544c1c0f01c9406410400c50b9051000c02d044400a02d10b00c2c0840080540407030441ca510340024070700b80081500d95006800c009581265402590804d200038001c00038000070300180c41e0002404900d0001c0f0002644016041c800050b06010800c441403c2031840180300b5880450150740c000c0c0180a180e0351900e02c40503280003809050702c228414440483c119120380200c40c4c8110580024040390b65 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 366908974 1250 366907724 366907757
    0xb091617070e15040905070c0506010b0c0c0609011701260f03070f08070f1209050d0c0e060310141f080c040203040201090801050412020613050604080c1212150907 72
    0x1160800740e043c1115040c00041640c030321600409200d0083e558403845c80c82c49034103100d8030304601030b1300c83c04014408010f071070075030070001c60854513210781511440e90390644000102c0301c10607841c0c0c90300602c03101000080340001c01b00c0c03030070806c080804600040340000079031000d807180c1c200501e070a41a88200010400614668180300419024044503820541e07a41c07a224908101070b0340c00c48024102180000c10355800c48007020180030306445100700f800d400c6d944c0c041d40c1c00c494042c0c03050782ca8440d00050443c1e54100180b4011000d01d440600041d110710445c60102c034410f82d85181c107840c80c0420f42d8462403a8101c03000450701701da802030680240a10901009500280090f41000701c5c41e071010402031024050036009522039882a01c07241c03142900241404800350030500901c214005900109100040c0d46070896000301d00959924015480c41e450030200700c224040c005808074000410349800408140701d08030003910210409500c501300b00c012401101c4200115940c55100d078041e9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 366910224 1250 366908974 366908989
    0x6090b12040c1e08060a02090612090c0301090f0203250e220308160302040828020315040537050709020301140a12030c1202010b091617070e 62
    0x5029480c1007007419120301526002c80031410303216003801e110003001c005150301000200d1b40301d05d401c80d0841c10420581c0c0001e0a40c850101d035480012016000301c1c3c29148184401155140018000c0040c84420700e480700050800d4038040e48203002700c12502d61136881c0080d4003224004034101c11036043d4244081c0801941000c2d248401e04004c006141c000340c042000401d522501907140c0400601e0004803180e42c44400c14284000c06005100800140400240069031030040d0441283d8010310100c40301c94203403004c18040d615100e94640c0051961184a48038002d901a0041d03451520720fa9912164a01042c0c4a0075650700b421610141c40090340c039513036002c00d84244140c0342e1050380c031fa12100c10b9030000e8000000c00d9205940c5039000c4e103000c0d89024000c0441a0002d810401580ca015200f4110008003500f4000650401501d86200390310048032000d0040c0780000ca070424043c032101000e0714010071004101140c0344400f07004d8800703035239074401c5035030740d4990404001c00d00c00e21140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 366911474 1250 366910224 366910231
    0xf0b030601171f0303031d0c060406050703140d0209120102250510050a0b0102101803050702180a0f050a090f03050c010204030b0f060f180106051c09030c0c06090b12 73
    0x40f0348809140003154041d10440342e00540c025540410022039085283c00000e04d911030410265014003d4884640c0303565055a045801d20b0602c10340b80c158600f02900c0c00512000f82072644040026024000c40f1580d02800d1403110039510701d200a080312840130700700d120345458051101e40c42044001c0311800c0000c1552000e10600a40b42c00c038100c0c03880f03503065400c260f4110f0340c80c81c4c03540350440155070704020881600d80300c07a80501c4900d0300982c2d15229484501c1010742008000110001552614224540d00e54034600b426155803401a000c400244401c00303903000c40c14105804908020014000c01042075004007000440e90f081b0f650643d895400780d2024120365400340310000100c3d40c1460b6042c82106104680c03075803854407804100300203045900e4a0300c41c1008902e007d604008040103c1c0c15a06541051036640d0b601320b000d8130703520a507492081d9400341002010020564007041c0005640c5c8188840740c0707800e8840c0b8056079010007070f000304040300b1342c18820550745085400c0034540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 366912724 1250 366911474 366911491
    0x706050702220f0905010507051c050c0f1605010c08010b031612020a0309050c09100e06041409160b0901050901051c0908030403090602010b0f0d03030e10060f0b03060117 75
    0x100d02e000c82c81103040c0c40100443c518001e40d103a08400900a003030082c5a48071205150552030041680010b04518500360104070784555540005000b04111070101d4000e8048072100795200e011181200800000d81c0c48112070079402c000100210f2809039030303424181c03541c0056045c02d660b00d105c506c10488021071250000c00c0710102060a0244603440180b010841075980811020313041c2c10042c3ca0301440200080c010254074041092200e02ca14031076040e80c59030310f03030300c0410b44400000501800d41c1c2452803054201042c10300c004003600040303036400004910314800615a0311500c08045009100803503011801c200103108241d03104000400a0800030250300c40d486541001e10750072203030860b00865408100200340820705030040c0b0098000c00c07491000348027906003000421443d8059503415400f82c0b0500d0582c40406009800a40b014824441140c589100c1c011086015112030f206030115024604000700e040078911044034842c0310181c55401912002810071031204600406645 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 366913974 1250 366912724 366912769
    0xf060c030f1b140304090501150c0b0c190509090a060302010539150f041a0c0706050c0306100905062215020303060406090e060c0d0f02160c05030706050702 69
    0x800140000700c0f140030085118000c548440c10103043c1012240c2c107070448150742c00d1031541d8030b20312a808140a078030f83d944a4164500390f107600320300140c14000c640030780c0085440e0740040400d403a8400050002a2070071111514561542c0103420b040b0307982404048d00003031003041074261494410025611441200c80b843d003006401c0300210030b0440540300000c074140c1002810b0200b00702c0c04c0e190f04e500046020951919410142d4982140d41c4a4810425001c290f240c0040c0c0480204003d40e4441c40d04a075040c002c0e407401d03000c40e500039441101c00c0d51007078000900d030310201c40c4194070803001d9a030043d11403807034410300301c0800d0804804101d51034200d0070400004100c1c008440380c00c004e0840340740c0085449090a2003000151030023038001401d8146441148c02680400203011500325210b9010701c0d0b600c5002c448880c024100b0400c40510380382c000201019030300429a0381c4240c0a000b002c06816590b01c4104050302d900c0c1030b100b528000b840a0181002614126000e98516400510080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 366915224 1250 366913974 366914027
    0x516112b12021614042403032a03090305121806030406180506040303050a14062116150314180a061d010b04020f070b130803040803010f060c030f 64
    0xc3e80030310250824000c1c025508074002d0581440d00409651400c103003c01582054455181010024588409420010360340d44c400d0f2684040f5407082c2c0c2982d10780000107503000035814003400c01f0b01c00c0d1000700c035240306403405000114541c0080ea140c02d40240131010209106108105080c0c0001d80141d9403140e94801d44989a402102601c2400f44a00064102854a4180a021503100819000796142851820242c0340000804540e0000e4111900c1440c07405002c0803041c400507601004a16110307801101000061401c0721004071001408103440170345250600b1001d0701c000c1d0714500d0741e10042501044a45020a0210103400c001400700d46d5034948544402e400d8840707a440e000c08100400c200042e031000d0a005901d24544203030780540c83d08032a088014506d00c1031500c00b5058040c2d000100b5500e01c000001c2c400c215400000b1240c0b80d0409043c68011a40b003846503101e0481c401000059a9005003940150380b43c264407404024500d900080c4d40004104031130303142e03a034903200c041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 366916474 1250 366915224 366915253
    0x60b030304080102031f0602030a09061206030501020a0309232d010213061205190e0304080601031a1b073009060f0302130504020a0516112b1202 64
    0x594458495006d0301a070803840700050540204282e040354045400400880c60710540203840c550441c5c86600c0d20704001071007940e5810040c0130329000180154000a4903403a03960b0300d030700802441806501019040200304107944241c0f02c902c1c8805000747c11070700d40f040d4076051403155500b07401c2050580c0ca581c940c1481c2e000f4220f0b0700c0940e25143e0091510f13000e004050b48040c05860340010541c0400c0b440c2444440d082140e0454220f54002035100c1b000404a03007414070944000b48094412144c40d07586a290100004c1e00b150600000520000006900b00410400c1f01c1c400c00180070503a440c000c07858840391603510702042010b10345030702d21243c40320400440d12a561074203820f1f40e47c1c0b05101d0519000a00080c1ca40303a18908250051104103c0741c80141c1c400c0c01100d00c100c5005a403413090b04010343d104e000d80d01c4840d000d518503401e20070501910000d00c0002107400c48900c80b85d44a02e0790040c50300103010142c082c01d800c200304503000241c5401920301d501075241c01102c508549a50f007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 366917724 1250 366916474 366916477
    0x5060c0a020f1201140708011d010b130806090c090f010308040603020315120c03010608070e0c07241a09091506152709040203030f03070903020607050f0c0102030a020307060b030304080102 83
    0x180702c030070720a030410080e05903030281890340075000c050344c1d9040702d009e45d00a85c0c81c00c030741c10701441e0440d0000003041d81c00848183e000b20000c0081109139000c51034004031581c0c80303105820409002d46650b03000071300c10010305102541640c0c0e00180681c24103081040c100d000b03400c010100c1c0103903120b4204e099041c3e030751030b08044201c2c0c900400078400082170f5000d00d400c0d1402a88000315a500940c424000b69031040400342e80b0541000b0142c0d100d1a00d410444c071300304010003002d0110920112000d030a000f903604400e00300007420080b0f6815000c2c0c401400000d250031140c004e0b00360828138031280380960230014650404001003184055001d4401000f0075a401400541c4181014840041c0e10320b00d48041c410380400200c03801e00c020310f010340100f6140e1290414401e0001d20000010712481c1c003030314094002c2e40d0060030380d54803084189400750791044001d000040302c0c801c6241c01c0145600c0003040700c00e40003155000e03608102140c0c1d641005030252590040c0d1500040c000418000000d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 366918974 1250 366917724 366917741
    0x3020906040b0f190806010903020d02190b0d140103110d060b03070b1305030106030305031303050d0c0518040c1d0f030d0203310308030a02070c140a05060c0a020f1201 74
    0x94080313950740c1c06640d202c040b4481440407a0300b4419580d0810010342c0e0880450003c581e0152000350303150340300784005020702031801d0840a08a40c080f0010540760103401c090b2051600b80031013040b040072000000c0413041310910004122092080d442c501a0604044c0708071220b120384030100d4000c40c10350002e4200112030308108241880445c0b038108195000300082c00615041c0c0003080058250f40b0700826522005200c640140310030701101e41014440c8007144c4100b0303030160307003004880c1005000070220f6119444c444a2139070481c01281d91440c2c42d02c00c12000103030710303101d205011701100d501c80e0300d03031000000155120036056144011910144601600082d10b5800345940700000141d042820070246001d0307131007031111026020192110642c00c07003600d0f08400c00036140e41e940403c002c0a80b04a130801800503101c8140011120103002c1584020311049440b007401544075800d00481b8001c2c0d40c15500103501c100d0001003d41803030401104414400390044447c40034030000c8509452052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 366920224 1250 366918974 366918997
    0xd140f0409020f0c0d080a1104081c0908060f0a0f020309060601180902030c1905040803030406090c15090608061e091320150901020d080c04150908010513050a0303020906040b 77
    0x5104001da03041c0103101d524142e00010f503965042c03505050b2b02da41d90749680c03200c8001d0201c1115110300200c0c060380280005000c180c00715401c03031030a006040c203210000e843c050102420600744800c005100d00a0701d209803080001030890b5035455004540c0c4000780b5158691021201e84042111350850006500c90114201c14940d204440c0e401802c1d68000d800b0714104100c004d0005000c1c880c004811650006d80150012a41455508001201810701d501c8000c011068a400141d0286c011401c0003c880c580c3e11528401c1c0c0e030314405e002406810720b002c010504660b4058a44c140b52070302a880e00314103012845034844203d41d49201d48000a45042507004265032981035983c075040340840303c60b40502c0d01170381c20300e101540040d585014a110007424864001d000402c3ea1008900340c0c2d005101040d8010020b004040380030b05072404030b00030fa111950038040061418001e40c052408840c0c0e10130000c08040b1800e032402c40094009000c401d90007041000700085101b940405480c0c0c80f00315 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 366921474 1250 366920224 366920237
    0x90312030513320708101b0503060316090c0f0f0f050c01020f0c0f010b01090f05060703030b060f1308030c07170a0c170105070806030705041a060406020d140f0409020f0c0d 76
    0x28880c0d828541890104c011101b41c0c1484c8000300103440c0500110b482e1205400c056440f9240c41c00002c0c2000408030183c41500900c1100003038810701da030403e02a54599841c1d6400202c41d1080403601031141c0c600303110102d10300c50306c03801400340300300d0007480c12241e80b000050404180459905007036000c01c50310031003a80002e0f000e207422070080c03159910400007400d024403054600707008201d200b201413013158400c880101c0c01809260107a0800704450100800055031010700d8000d901598000448141040d0b4041c9000300b12041d00100310360b0341058400050509038985001d94a40440410400f949030007a42c0d00600002c407108100c2d4040c142d1070400d20f50038140c011600d4211b070300042a190802042c5010b210342c0d6140070a56034241c030b0095401064400f411704440446104414180744c20110004000440350b901142e42c0740349400540e9503002d060600d4180240d140a0101c0d0b00360343d04020002004072800c640d00034209454202c0c001800c11019501080c1403501c481c0380c04021818 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 366922724 1250 366921474 366921479
    0x1c15060c02030f010b10050a0c0f080c010c0c11040b030712121103071709150711030c090c040519091d0706020714040504110d030903120305133207 65
    0x805101240300045054005c004902e07184001402c01e43c464003842e800c3c008000b4110039114440d01c00c03020380700d80204480d9030b402c0092620801590100b840c8c205c0300c1d480c091030803030860b01c87c1c86990388154200e000e4180d00168101044000c2125030141c541c107206100c03002846600004408018900030f9000c0354102e030802ea0040d107880358900b21003046400030807034000025002c1e600c0c8a407a0b0400019542c0300e082c40c4000c19140895800300da1100400800c0801c1040400a80003c20800a40986d00349804c20800c2c001024020342d013600b84400f09000500150500d0300ba405041c041312014104015510030402c0103c50520314081070610700c2c4c00c2d00905054040004030b000b807002d84014240359103091000c0700040f080c4280e4610494807000860107204089054441003c8000d05c924044000351401603d0100c4500c01129840c0900b6182c460081c002c0c4160351083c6500420542030780c180342d441210030a0190f1410020036840644042c0c4022039407180940104010f00078030f02c150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 366923974 1250 366922724 366922729
    0x60f0b030d12060617070c032007050a0504020f120903040b070602031f05030a081c140405011406090411030a06020a09050108010504090c06050f0f0d0204091a061c15060c02 76
    0x1070f03a542064052008202d024401c43c10564891036002c0034510f004242c80d640d40c03908590309000d480395081480700301c030003184060304080341c0c0c4412103600712068030704c00b941c460510069004801c4800c043c20018400144d0169071000c4547e480040c40068900d0035441e00c2c0110141c3e0881c00701911581d9000c0300b0404032088401600d10214160030949141c41c6c94800029903a13400004005c0559402003010001d060042060030300c1403040707139018013005182d03d1400f0043d02c811142920b0b07075800e103a41c8005003a0b41848a40c087d410240124000e0f5503a600c80525040c0020a043d40500c22004c4c10804144a031000d002e4003082542d9031348043d45001c00042c240101078010345d00c00e500d024010070008100c4514441190f1940c145140c99151103001d003062070090091032505440005100022104c5540c01001528441c580411200700030316010b40c291000c03d03101c150010f20400c1809101c60232000c1a006002580c0d42c0480c11503034060b403448207100c031a400100801d160314607410851 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 366925224 1250 366923974 366923981
    0x50f0a0e010e030901180f0303110d0309053309010510050910060e010c080d050a1b0e1504031401051816060f0c2f03010b01020703060f0b030d12 64
    0x106038100240015400054440d49074801e004040d410f20048500b401c0c441c2100c402d10f04001c14148a06941c1c581c1c3e00d06002d48a26016000100b45010b01518214030030f0281c410740145030b40090080c600c50002102d902420407581c01d0000c2145003980f170358240321000c00b002601c07a0600d0307800802c040c203150010f1060030049411551049040008000610990402c0803044488900e000d80103d00c01e040103803030407a001c60002d4115000062212051130113070b000707540987c524180401031400d154150504400d0341400740800210207160409142ca444420b822158481400042c9440d940c0d0b907840b9003082d503141d880314480c2d440380d041104242649051b900c0d6500004027600d18a40a084000d03900c048078000c00060007006c0c181c400900d031044110140f01548062243c0040c01301c0244041042c46101d940c808400c0842165034032030406000e03100c040359040c0c0090000501711b070f692101408101003074072101513075000358007078075542001040b20500803602e603550100710701c0c000c000a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 366926474 1250 366925224 366925241
    0x906280218061b0d0e06030f07030207020904030810050d020d0b0907050d0308160c050d03050406020d020d0902121b010804051005070810050a03020105030115270501180f0b1c050f0a 80
    0x244003002c4080c0405e9265101201d51001c0390b090061900c3c1e4440c00146c0c02030180c0300c400b070741052402c42000101500441d0481c040c10360824640d494640d01e101704018044c581b02c000f90030004100084001410031403075940c1114070802a50701450f01d9501103507100699900540020790740b2410300400c0708502c94105000d0391303546000850403c15490300365503515a140d03d101050350707440c005001c1c4039056042d01c11101070214150b5441c20074100c11806040d20781e40591161584020000002c14001000550011402181480b41e08003000649182000034010760f00c42c0102c58007070109207207910840b8451240ea440c0c0c1030250801c9030083d40c9240c250380226009920002003400540e07000300549044500d90b030919146100525400c0351442182d00660501d070b0700d984105400c0000c980c1003101515400c0e0394005100e181540c21803c0c9003000c0c807070041d203000202e80c14411055518010421440500780001452020344180022210210780c032070044c40d01c40d014030918001034043c0300c15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 366927724 1250 366926474 366926477
    0xf1011030106020712060b061314010e010806010f2d0f0c0503070f0206130b041706010e130203030c070905150303070b07030f0609050f0906280218061b0d 68
    0x9640c1072102c003a40e920300342d00800c0400032480c04d42c4010400c40d41c00400c89000040d0040e1b07200c03032030030070980e444e1070160003245001c500c0d0b80340d01e00503540b00c0ca01c81588036405079141d65594654000546014880038440e404000c004201d186111010492101c141c1c00d500f1425203011442080040042e05440c007803000b0440180d18840c08520b00200303885185801200000042c82144006081441a1400501d045c00c03a00c0700081d04440c0b600281c8104c40a03000042820b40008000c4d5403100b03802d00401a00c04544404100080401c83c84414440d101400f240e11700450050894640740c826441200c0c0d0584400410094000e50340b880500043d01350020b6041c0a816982e07610000401052002007642d102044070784240301740c21050040440100801c0b55040c090a01044000101c0300d4459610500300880c11026410742a4003403c40b5501d6000d9a04204401c0040603510010b215103122003420401442d42d03940800404d104d6800210180f4003254000d009800c11409200210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 366928974 1250 366927724 366927727
    0x90d020304350a0606030215040506040e0a02071505041112060f06060415020105040c08061e0402060409051302100305090703060b12011d0625051b0f1011 68
    0x3244004806040c0d140303081c1d0110820a0000a00c0b03084082c8180714090315252107810803840c28041a9401081580d0081d00c51a15011514140711741c148642c0c032810741c02c000700300701c00c024940303060480640000f0450405450100c040d10f9800c1a450042041e04050742d45074140400c01920b940840030754801a141c40740121300140306103481d000001c0c0803160340c20083d0009030056a4400888019254801440c0180288904024024602218222220000c002010a0340c00c00041c0300c0340708026015021510240214007088100c1002e00120b070080c1041c08042003603a4503001d940c1c0300f0f092101d03905081e00403900412440c10380850186040c1031030003043c094000401706043c030543e81c01100124841d50313031001287c84400b000d040002e10b54a0612100c5520054485a10751514034000310f42c01511000803482904840c0d01d50035011381c80d848600b61040d0701881c0940f100032030484900603803800400209041462140c0d144109400c101a01090711441d803103140c0340945583d2100307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 366930224 1250 366928974 366928979
    0x11030912100e060c04030204050915010602070e0a020906070f080408060a0c1b21021015060f050a0c20031e0d0e1003021e040f0509090a020d170706090506090d020304 73
    0x207025214071b02019000c0c0b5210000501e00d5007040080350b0607061a94140f1002d50b035500300003500e40307410340641c0002940c440080307082203c16000b078402c5008001c0031246070040964586030601650b910481311540e0030301c40000d4800c8188074440c4100d0240c13901007075002ea80d600040210181040c001e914441034200800881c0034680400c0c154944044403012500304501c05a14112005c406039425909003d454000c0710204d00d150401c43d201915110840d0301403040c155860301818046400181245c110500481c0d030380c2e16000000c215144000c80e9002141e130109042800381d206603140c504c480c6245e12102d03601040f181f44056094030303000030110300160019420703510015400c410950081140c1035a044080760340c64084203102d58943c1d40365070303802070f2120364035651280a10032440740000500c00074000c02c180b0801540103000305100301c01030f55070000251200c400c9981c454810f014650000d074681c0301d18028903008500510040c03a01d03a40c0c01c0c1c9801c83e024542c80454100340b004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 366931474 1250 366930224 366930241
    0xb010f080f0601120b0904210f05030c07020d02060703020a0215131203180e0618060f1003060803040f05041b120f110d1d0d0e0111030912100e06 64
    0x1c00e8210100340f802201d80c0b10280f10344005010400603c0d0751180c100c07414042041441120301d07580668003079001148000108054502c641c8092010380802d40800000b40e001d00c80034000c01c95170740700400e4115900c104e50040345041d00050303002c03405a400340580b81c0a600d0681e000c0840e0400c48400d507441e04210584109140741103104580382e0341c8102080d00304050082c1c502400412044e0820102e05580e401c0c1c0443c015015a0110b0041d9401c285580c0e40301c08a40e0310a200b45800741c148009403451409000d030b41c0ea00300102004041c5c0c4c0d0113020a080605100503c000c01a081480c1005400c041c100403c607000980314020000d40646140d0455422003140c100944042034001651900d1360001409401d00340d04001e4101c038001380d0030000c02820751003500681030f001800c5031365011f0f500b00e440c0d0f40c03112000e155000c99444038030101c0383d6215000e014500403d0000f41c904240010000c03035084040341d030880340141c0100610819280b22031140e002880c500100412450409803031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 366932724 1250 366931474 366931501
    0x1103120a1523041d0d0801060e090103030c020d0224180306040c050114040905130302010c11061807180204030b0726071112180109051e0d060f0b010f08 67
    0x11550003592540d0102e1008491040c514010065807029284030011703090006004590900494020030312000c81700742c540c00c00e8000c0e54140c0f58580c841e0100e900054003086030000001004070303442a192441185940c1e00000504404460804505c0e2680c802d044100740d042403140d1518005c1d4000360800000c1680480c600040303a80a0a0010450064401c861541e10454010409540c01d00301444000d0006203c41294075000342d0080000c3c402604044072481540301b000d2040354008008665280406403240703403a032020700219080c95a03126200c103054005030410751505540482c0c108240456807036482d5001040e440c1c44154417400036900004d040800708040a0b803284d07500040ca400b809824020a441145021a41d03c090401c88540c0940e115120144d88411100c2c190358955004591040940e0f2000307140c001c2007024035007480c0c0c1d580e15000b0029881006030600601040061040b5030a1903045103011546c0460031001400303005515090104000d0b13890100034561031f8881 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 366933974 1250 366932724 366932789
    0x709091103060909030c160302040b03160501030f180524010608040816050628020903031c1e02130f060f08060f0a0b0309060708090604031103120a15 66
    0x240d0f81840d070b848407161149140220b82518800c0e1203803401c545042d0b0202c11401342242e04c2202d0521104401000307054407400428103120341010780030428426507000e07405c54081a00460f400180c030b0b4855140aa841610910044d14107801220703e03601041402e60100c0541d008440181106514280c8010b200b241d0003040940081804070f02e03020440208d081c11403040c0d0b0071000315240350400e0710094200510a01150300c0101c41a400c80c500350b51035001740c5850f500c00501460818000c0e500800c1520f403010a82c21483d582c1701c214401f406188268007090039102c2c8001a1075800001a50450b0700b40c0d134100d0b0903070b4506040204482548810140300302510340c40c0c842c0c000d84031000480d03d179910304140a40e200310032220206800c0300d184080c610a5070080308503071007511008426200301e41c0c143c550041c43d4000300e0000380424098050304076a250040112460015040c607286032000c4280c443c0a0000e4940080381101c1d444e100036038010b40301401c0743d0541a09440c074800140307050030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 366935224 1250 366933974 366933979
    0x90d0305070203030f0f1b06090a230109030206040b010e040206091909060602012f0301120804030614060102210a11070302132f0304020d05031908070909110306 71
    0x1401d00c003107450a109444522040d413044a4032941000a40c0109420816082c1070401e20400000490000001c41c2809400040c016004400172034450060580002c905405501580141140d544109100e03c0300414000c1d80600702500f0301d440c12080010041c1e0003000505402030911026a03070b590101c6240e418101e411140013807016500c20200c9040e0740c40b142080c3d150120000350a50107401c0b8032040650f1294046100c0c0000800345645080b1404041013140c041c8014840c00104041320311415000b940d18030306241c0e981d91140c06540190f00c000c00b14a03000c60600404d07580400010340181c0c1c00e00700c0030000410104150351540103010b0320604104402e0f10b5005c0c601414465000510b401520004165089085c1d040151481d5001c54100c064011305682c0f44404102e00da10b0a00c6040440600e151156001c00c016060103070015601c40c00204812582541d800390080703c83d0a55450302d0050745001c0d80b029203040d00c1c41e8000580311381040c1c842d0f05014216802c403680600b04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 366936474 1250 366935224 366935227
    0x70801050f101511100606051321110a030501062405030708060108060a1802040617040c060302030c0f03040b090d050703080103020432060f1002190204020910030603060b06090d0305 80
    0x11006914030f03203031034000d45e84080c925220300814600d074000001c002c141c1848074070051695841ca00105d86245a40c0a0a0351003001400c00c0d0014000f805585506500100341d405030701c1e280d45800d403c54801e40c0c0f00e446500044860b400d121100e0761340107041901103090050031881c2880300139015100060009041062410028405558a4200001030003403072045c1d01c400761103203c2e1030000798400c0c010040401d0311a1480704644015000e03192007640e1046d4540016490200250083d400180204000040c24425505c08103e140040c40c80307540904022034090400410725030400214109400421000300039400c0425000741d00030781184d505480006854111024445c4114502500350003c02d0700c808551401010b0884418026081122007103e62403404003000528014003030b105d40540c00140e5201e40740500b886569800e20b0018001500d04480400041c0c0a90700100118011036540e1205000b03200707452080719200c07481924824540341d840800906084400c00006080000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 366937724 1250 366936474 366936497
    0x50703030b04020d020f2208150a1e0b0109140f0d020d0204020a120e0715050c0705120109031b08040e090c060315090703060b0a030f020c070801050f1015 68
    0x40b5981283c80c1920700c80b1046413980c5400c81500364030303401038103201d82200c283c414042da681c3c0300c200104101d82590f0001c1c040195000500c0b10400307001003031880c080d81d440005014026550f0014440c900280f440003034820300300800035291014540041c2c03d00c40f0740700c403c2c20483e1240c2d4034034455858100c400412100d4103100044a45030b400c40029000f81c00441e540c0802c80d0440a89650000805014480b00c601000c078a80c4d80c0030184101108802e500032500c02c40c1c0e0044000300a0440c0460030780e55115140c00202d5240c046ca000d510b10030369540e150f01c2c400d243e403080040c00c00b007a504410710700340e4503651296292070096019140030306940074041122508100042c80704144043c04642d1245411202c43d0881140010000e004041032800244598171a120306010b4902c60f0000608084040b03004078000c0c401c010755110780907820420b500c0600c0c01040a80b00a0045130008503861821880000e000030000e060560000c10300c80c8140b041c2d081c07400c403807107502e00c8078540111040f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 366938974 1250 366937724 366937729
    0x1c0210150b0702130c0309020328060209010c021005130f050607110a090501030501090312090c21020301050103150c0f0816030906090f03021b09040b10080304091505090106050703030b 81
    0x2403004e0b00802800d8900308030030320b420343c05800c2402c0c018003c07000c3d61856080c01c0c1d83e600903180081c0300c402c6900381d01420f813400142203502511180e030061400054403880c95000c01c490201c00c4801e0700c042107021404000c400c01005220b0081c05c048518892458581004100716004001009102881c0700440200c0390300d41c0c1c00204010400f0303c606210559403030074214002c040891055000503400d80001000c2601c6006520341c083c1d00001440d2070a03d408500242036000718080750501941d00300301c5d0050796090043c01e010b14055000d04036166035544c0c04104640c110344010080c08180d800c103890950b00041032552002d803000340c0da0112450008110010482d03120003c040728505903088092003052500007004501c0381e000c40e0f01020032034401d04005507183e4202584000108002030008001d4540701e50410343c00c41c0c200c0c0403a522045082d0035500140c0001810703540c3c854a00500280c0320030200000c00e01582c01a80d20350610000034501d20071300718098180750700c460284030143c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 366940224 1250 366938974 366938989
    0x207050a18020c0d0504081605011704061805010e061612021e07110102011d0709090807140d0e01030917090f0604060e01031112071407051c0210150b0702 68
    0x103102d80f020340701040100741003d0503d0708a40a49107592241044034801c10340110f014009441050312542000741c03520b00c4c46140500e000b001100d129860709400e050600604440071300840c460400441c0050b0040403161602d440103040078270041a5401240c1403a801a4a40420010002003da664602001c120400c00c160200c2e61407021000a0106c1c24001c101440002c82c4c0030980c000d1062408850400158028a901c01d0820740c001001c10040412598854011144a0140641010b002e501c0300202d034103103080a05441c2e0010020901241e0b4088088450300009003020800c1010030785030814410040d140a4120f8180040c01ca881551945c40c21100300d00000c25003540c841d06c501c00103259402020016020905045400346a03442300b80a40d03140c81224024507803da41c41042c11a045800c030303009212800d1082100380c0100d4000d200e170794400700007003d245800c0b40d12000028170b0101810026404140341c1a40c1043c003442d105040c50807207000c0c20205440f16200d0000501c030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 366941474 1250 366940224 366940237
    0xb030706081801140a06060305070c0203030414030705040e0601030c060816111005150f01020714061e0a05091201020c120a050c1605010212030403080105091503101505010207050a1802 81
    0x2138450108000b140003071600104203179130707240c1e800740030603104c001c415204171284c800c000398107400910003488506901284440460030040c03c4424090740c50002c9021104600c0304030055400240c018024400c0500d941d40080040345440ca000b890444240e00c051a402201c0b10300700458450b1250314500200911040025400c00030010780c104900341505400d0851452409906c1d1003001e03928942c00451000226800441c542e01e041d05500d08102d01035000c143d001e2607450004809485510f00f081c0a042030880d56102c10780e0b00e04802082000d41c40074180304201aa004108074410114041841180a0034201c031413900ca0615010641d554007554003d401d1034450f00f80401026100802020100e034020780a0300e04d1880c445503000101c2c801141c002d80070038036400041040e418100381d640d90000108510080d016290400a428a104001e54184164581d0003d00c4440c005401060080c0424001003420b2071404010070368180091080043c01c4c08078140740150309800307030100c958 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 366942724 1250 366941474 366941501
    0x5040506011e0905100c020a0b030714040801020702032a010305090f1b1005030408180f06040308070b09010203100306050408040302031c11010204061e0201090b15040b030706081801 80
    0x12103402c4030005220104034440d651083d0041c50340c2c1c3c1c2045005144840d02c0135000b8162441c1d0714148041800603500240c0f00030100320f010810300c20035040303d0002d040542017200015a07915501d00415103001c84d04a0400f00790070f40c192603c0c3c42c408400d5401c0100078400c2c00c010a05648891010303080848139a00d0421501601c0d003c0e040700541c03030242429150040f2196a003510543c0b008030b40c280000c440040030714004018140590711590311004d00d4040081500d4150103900c40070660680142c0d00480e1000c1010843d01c00300040351001680c0314403000000c500f1450715600e0f0b042207105920000e0500d0350350303001040c107010b8102d00f26000342d9006004c45031201e45890750590145056410341000481c0d40d0296030010106008031400c861159039801d4020300404108050198070809240540d9600c03490300d40040c0015031603c1c42451b00020501c00410300ea07007804180c40090340198401c2d00160400e010081d0007455064024401070300b00b52400303964480160040000d10303800300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 366943974 1250 366942724 366942767
    0x190806030a15090302060a0b01050a0819060f05030f0a0203060c0a11030a020c1203040e07082805060102010608010203040f060b13050c0306041413080c0111031305070b070308010504050601 83
    0x554180380e5802500c0380320320035803c403807450392103944100c00c84120724008d0780010010800242d0303452240b02c0c1d8940002030f9078086040b94042c1c80c4940d04440f25a448064550305403c0100460720302030010039001c0c1c0180018100c0140f04d580081d8449400906804941c040401c07a042c1e0140f04040f40c028280140c82169920481030310702035690100c501210344510800b00e400c0c0b001c5240030040d2022114a0307805841c0684509200340d88258008007140b10280c48404c0258012030081d0102d101040200d07800146400c140000900b5101c40740c0045800c0e81c010002d01002a00c0801c04401c581e401c4a03001422100500009104414284805000a0810f010301091240c1c0c00c1c0210301a1901f240c04011040c015005540d543d102250058101e014247d100e06c049044140107040a4154400000e038031210012546440e4109840515480c54081c21900030484200f1441d0058050340b40c174103041948a603002082014140101409a40c48074080390407a402884e54552011803525081c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 366945224 1250 366943974 366944003
    0x309060a0b090906010b0d06170c0406243501030308160e06092404090513020f0111190506040512030f041401020f0d0f06050609011704050a05030304050a03020c0402190806030a 78
    0x30b5650b2b5103a00e8070684240e290001c0018000c0305002000b400f0034440050800509200b903090791a0041d20604501c0046001c1c01a500f031001a44640080940400b6510342541107003801400e211b0024200050004d07903203270458480e6040999070540ca40205c070b00507035994801c4040350410394841d00055900c036042c10b4580100381400098800c1c1e0f040b181d0100255a2a507001074208483e004029421225100c4c00244e60b500c220300305203400300d8540480e0006216000c0003089100401001e8a007034101000380800c1100902c0141c444d20300d2a0b44150550806c00c01c200040d80002c9d20050102044a544401880c02034064801000c015281c840d10f54001030749034005000c080042040d02454408086403515005003031f903280f080d068bd00c01c14940c207000c0c1280d450080240040d10300b0b115100700038000440400085100314070880103021400424a4042d141c22040000d4510490051096902c581c01c000c49416070704540d45001195501c0c0c00000c64244a4040e03030280c1401c0722541e14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 366946474 1250 366945224 366945269
    0x5070909141014150d0c0803310506030907030804060c15270203010f0c110601060e100c060e0d02011a0303090f0402031b0309060a0b090906010b0d06 66
    0x1074800481560162030403801c04184110071542c0580d140e4500070450b070003040128405401014080c03e024108510340200b50315400240c0c0403036440b0070380f140c0c00020001954000e0724101c00d03c5001ba100d04d076620303200c1c0c0b0100e056401414000c841c000c400100c00510410420001c0f000250f800003c0f40e039480b41c50b08001400384c00c4001c410f403000540c0b24160b01301359070140700d8152060070018140500c0c1e8000310310f046001c0ba0280040c0ea2640d01c03030544c04007801c05841111401e00b100d8030ba10000b0801404002c2c01e000c2c050f40000184560400b50401c2a100c2010100e1911a07515000d800704002c1d00c1c0001c001c00609203164004e204101110a00b00c0d015401040840d8105a144034a10260010184c0e81e10030410126041242e81203400141d0810380c01079a0403c0360400e40c50340c1d00c03000c0c0318245199081204c15074019403024050108555240c499500810002e0350b0100440ca88000b4080d5543c030b0622610000d01000540780070f1400d215440342c0d0291404200b848542659402c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 366947724 1250 366946474 366946493
    0x2010f050f2d070c0c080d08190b0414100b070c0510031803080601030522080a021c0302120f0708070c05010b03030f07110d03090308180a08060a0c020f100905070909 73
    0x50031604400d1702c00b804940e1201c0050000004566981c0e5084540c0e03c5040d83e916a076005d038081c0d00c109440ba01062030650780e07801901aa0f98142e429120b40d45001c20b03808003004200d61102980807802c202c003001141700040900295101554010000004020210000c00a4410b13422011b02c0101e284010154010fa00b2409203070240c0c3d0a201d2a2281c10406d0b551400301281c40c480d0104030441800003a000c400608140e2400b401920545c500700c00354015801c8100b100d100c0002c1e800203a0246081040421a030805e180a10f00c00c110314240d0005080d042016002e07100340315a040742d24080141c01d4021070500c09010302500d4a0340a0b03400c280400e82c004207800c540e00c2000300d60041150134001c03040c1180503090f59a405003640386450b80000c542c8450140d40506190040300c3d07105488054206006001d0480200710514042908400715809070080b4400c5420a500b41148001e0005140c0f210020285001074200c4403868003601c1c201c2250300c0b01a10a0400c0400c109012907078a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 366948974 1250 366947724 366947747
    0x10206160903140109021305010f0e1305030408060405010f06150e120f0c0f030a05030702010f02010230090601050f10030e0105070c020109080610090b030f12090102010f050f2d07 79
    0x195103005051001f60501c058071000d00600317801040c4220200040c1480c0d0110035006590603a01220241064030b406003540d0142c3c0202166078000c1c414002000800d2291584200013210b04008041c24000b007a03010104842c100010030045a407403080954940710076210401980e400c6540d988441400c003501c41e0f0a0300c8e46103100d00b00b565030541c401e080106000f50100da00c01c0c00b441c5440c0c102d43c019144c8620300c4040d40119942800740300c500300820102c180722030080d08420110b0302c40b64064003074500c100400700480e5030010001007100d91070350004103400d0102180d01510724a40d08100710018022868440403a600b01020f1048542c0c00002d40c20145000386d032804003070750320748000658607401a076018018100490b0104181d00740f13540121a581c100805a5001c1b4000303015591034041c9022090044150000710408190380920490301c01607110305080c0098a0101d40040d11020300500402400d40b171a515140c00442c00e19007200349841082003401241086135000701003ca000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 366950224 1250 366948974 366948979
    0x1a010305061509040b0103031416080927010306020904020c0118020907020a0b1311060a081006180506070804050a0801020a02060a020c0303060d030207050301020c030c06130201020616090314010902 87
    0xc8903440d0850601da41e040d0b110303541101e071784040380e46140c2e0300719271090140010300c150200c144100440030103052091640c42d0b0140c5100c5480e0407402040280d03000a80c803100c61a0300505070504400388144518904680d00710600503210303008500494064410071580d40700395480c00d52100010035040c114915000c0c005d840040300c659a0400a9036940000c88000e0801c0b083d04001580341c6418641828403a4460340110075040445008220070390010041c0d68081141841040210074045100c04001d00b85481c12010504200b18680500c0e4441d008040c050040020090103014001c0c0440b4003c19000e49064178a51795034020a0007034006215041c0180030750f8022a1486116009403051400716001a40c516207034207080210400703a01000304c4c25401030020014159170280b005d04145145140030b10b5a81604110300381c14401d00030030900781d0a07105945040540d80c00079519521400c413113140c022800b040c02003940c01d0500b0707620041c499044c012030105045019008044081e209 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 366951474 1250 366950224 366950251
    0xd020f0c0303040e0c0c150711100b0a060311092d061c020a23120105093706030c062309010e13060e010806070201020f0904091a01030506 61
    0x1190070940c407445240301d030300030728546440814482d020301c01c01090355415100490b40da441100c1140310704a0400c49541c4082400034480040300381c800c6c010150035807515901003000d12100c40c0041c403015a1402120101680d4102d61038040c0c00328801c84610b00c200620390402a11036024202d521044000d074070071072411022022599080c1001034035800e01001814001d5400e071205032030025040300c00410100704003088660404200b00da0840032015005400701d690b010703d0707200d2030300b26031040c0d020600942041c01044000c040390411001516138990201c4404d1041160042c1a51101d0045080003860800c0c008100039032664190220ba20325115420382c520034003554400a0981c110b0403120010421550b00d8540c45201c0c80342400070700411401c8410240b01d42241102c0a94111028035503a800040c018402c04000866221300c25100942c07800d03a844a40301c1c0d15000c0c14240f14010381c0ca943c0d08408108001101066904042c802c1d101e0365a904e052a40c2d0320032080d80c2e0700b00400e00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 366952724 1250 366951474 366951493
    0xa050f0f0304140d15061401050f09040903090b0313060b03031602011407060f020406031d030d150e09010f1805031c0204030b07050304030f0306030218060307080d020f 74
    0x2203154290611100059400e01d49002040450a08140221035102e1024100c2c0300000c0c8807009101c124100c3d00a0000c0c1860070003105410400b02d4204c0141480030510012804070741c0141120110102606c010a080881c1d241c291407400e0240c008103c01c403808001c00040403c0000b01d0007145001d140144911036000c0306042d141e2085464500300b50a04002c0c040141d405554540ca010682d0070800d482e000058664104a850401a05c101035070002001c01c415980360141c016112142c51408400c1d4001c0c04086940b071150f4009018200c0d21002c09103a44042d1207070450091100c41d201c03070039504d07244210500a2154000c2052110318011f043c5c88000000ca40a02d0020340c410011403410030040c0c80b200350b40c00511a070b00c03e610380030080400041d8002c414140108a55111141c41307040c2450b000c0c0210901e40810010507251082c1000980c0e40c1c4c80710300c081d610003c0003100b104c0d04d44c08003103030600102c0d4018a50f20702c5a0102c2c03a0070310f680094a442e02d0340c81c0e042601e00058 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 366953974 1250 366952724 366952753
    0xc090608010803030a0905030d090c08010b0f011d040f0f0b0109080304060504030311070f0f06081308070803090a05031803070e09061603020702090118050901290f030109050a05 78
    0x3a001e001d0380103194028400208005d40581c03003005042d01850031282030402c88800350058a5503414101c031a03030908801040b80c0700090080c421031050844500038500402c800080040554218001d083e00c08011740184640351036005801d800c001580030300c81d410701c0300c00e400090920031f41400e00051b00c00c00000340c240c1c004025101074030802d543d09403500c0d141d51401c449074000300316039581c640074140d80002d4001202121800410242c410298058030701100504040f00080030018004140113074070001610b104121024203620140705522030b1100200e45240001403031008081e4440001c201180503081c84101a01000071011502c5090b02c03000c513013a80c100c2c1910000d10035805213011980c400301c00c189a040415951030010304000301c58000600d041c00a03404095200b0305a4490924003899002d1280d10941100090000841130a841c00c02e0100080320304000c8200703981090156610425a039001d128010000d200034034580c284203407641c08909040b200351203403d0301c1c1c1c085813 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 366955224 1250 366953974 366953987
    0x7060207120e031c090e1f0905010b04031203150e0a1a030307060c14030403030621030f08060105040e0103050606010206070c1e03120c0804021201110403080f19030c0906 75
    0x422000e000390421000c40e610081841203c504c40c0c2003400801c00d000304240b80491801d130721500c1c481c01500010201900340001d0408180c10140da0203003443e0050225152040440301265840441083c02c0310301c1480031001000400ea8801111f012a80c001030340c6c0c000c0310866402118000700801100700b10300840d41d16400310707441c2c035a00340e0814403d90001c111694452511080039082900e040b030901c0000403070540c0115401c42c0444c1d07aa41d028809400030b9420705000c1292003100d9020000b150f200500440d00f075000400400c40d1080010392680d1040c81030782d00800340c1c01003a4800303585a11b025038555604072021801841803074000744219209661004003c2c0e00900c004094040d1240b00c1036138500714007002d0b818000e040c0190030111040c0d20480c42c84052030741c0c40b64001d08042c81004101d0300e00c910224800c0c2e0500070100b02903000103049804480c0c1c40398506a403007044034000c1d40a4000c2d003507101d49041c04140071a035a2038140e04000034070705095445604403911401300342c869 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 366956474 1250 366955224 366955247
    0xf12060b0a2007062c0909010906060f0e040b0a0e01060b031b030f0112052a09070f0e010531061e050315040f1b03050c0405030c0d0606030501020706020712 69
    0x480c942d100d9422007050480c009001e4038001003008085c0031541c0410810141039840e054269501c03980141817000341d1007100c01034548079040502044c034200122542036005400a0604c448420214080b1301725070f0700a40440403500001c2c4401e641c1c1c1c070702c0c41e500c036002180c884050018030807085c10609501d074100d03440750140710401543d6908280d20098044005901110944a840b00b002d01d141c01b50031080d400004070f04c8607200302d48901402d000e0b548601400d0b000600981c6008015034603000400403030150300a28181d40c50b0b51442c088280c00c0703640c1d0540158071000702c568040c6065005501141030310980d4946000d044280c41c100b03241c40101141c4000001c4d000d00100d102200010b5020078562001407000c16454000c80880d41202d140c0c118a8918600444c004c413003c0d50107006855020540d0848541060318050110780c84d08200c08096200e262640000410042550310070b501864110008545805c10b0b03140000007507102450a84070726441c0800c0f8500a441480402107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 366957724 1250 366956474 366956477
    0x60a0606090806102322181e081c050f09030f0304020409020d0605010b040503160302090c220605090a091b0e0a0504110d0b010f0f12060b0a200706 65
    0x50062621207602001030002c402500310303c62240e00c0c0446039030b41703801c083c481c0c0e20042c6201c203d403408a00440120b81d802058410014071082808001c1404014415244005480310202d81e03249441c1127102c3d44250584245002444050203680f003644da80b0040c03040c0d03040c440e070501710344940b2003650740c07401001c0c1c4107500c1c0541040020010b06040d000461124030140c880c540d494010741c1c9420558130260020030740078401060811062a040102c2905c01515140001e0594115000300d0940100207003500241180001d1140e48000002200d00c10314088003120b004c0716480b2007000308950700c6042d419204040d0034001141c0341c1128822180000b0520341035000d4404130002c10750f030303201100180c10f0f80a40c0400000130039443e240a0011200354240c101943d03600c40c80e00d003004803010804018104070030f20448011658000790201d422080754105820307880074100080024010607002041341c00d60208813030f0005034019000000c906401d00100d40b1544c0c02509603035a45645209880 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 366958974 1250 366957724 366957751
    0x12020901141204030809030c0d1206091d06010b160b070507020d0309030203160e18010e0a0501091401020903070603020304020d021c03030e0d050412020f03030301030305040807060e0907031805060a0606090806 92
    0x1c00244c09008509100c003408040422f0703c0340e8814100b02100c0b00c0400d2000304101c0a641400a4841130221a0250814560460910380c020400007107040d01e4440050070984041e022400d0380d4090300560300d070703264020240c02c101401483c0040c1250306502c002c90092140d03954401410940110304400d4a10000441100c0d55448422050380c0000c0290007009550318443c41340d81542c140b110200d818028000840c00c40c4c41840d12511080c41c142c0d030b1501e00e91041c80034260700c0d41c1c0130130044e00f182e50514015843e621140001723403002002d090020340c460800a0a140104136501281c1c0402e40a070700c0401008506200b10303611041d030b07146907500241c8100070911074643d0604400d03621b00d0010304100b04100c1000c0c042851580701ba041900490b00c0420200300060042108201501c2d640c5030401100741080040348070054040d002c00103154442d1040c522010411024000c12900072040b0392103030903c811544000c0080340106400554000d00104002ca4000380c041d00407854560900c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 366960224 1250 366958974 366958993
    0x21150d0b06010c1227060512041103060f0601031a01020c060d020c060f04140304050312070602160308060f0d0203100903090b280c020112020901141204030809030c 72
    0xea040c88010071650620200d0101071000c100340910411004000e5218001d10103050042c0519803409002c3d1420800321160007070040c01c2e480f9003612040c03050701c1c03803040d055111880e0480d02042a0501603405210780d038100404000314400c1940034000a803401c2081180302101d184543d14201211030140c1d01855100301181011002425504601c080041c2000c104c43c7e049424054195400032216460324107020521569640182d00d403281c01c00110300e00b82c070302800300c0c0d00c500c043c040e925008180031a80d08180300c0741d501121a15050590f1901180c81c4600d4041c00c14079080d00c3e0140254405855004182400401840700030b80040c0201519001c0b140c1309800b400c1b83c40c0049040055140000078514101c0014004140129600442401161072134800007090030440504000e0350343c1d10b80c005030b60050030031070036090840400341c8d5400500006a0310480f42e02040300a031440000c114041c142000120750190740300b66100001d680703603840c20700d46e42d0060000402d07280c0c0119107603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 366961474 1250 366960224 366960233
    0xc03060d02130e0f0f060105030303010315020f0913060e01120506041704050a0e010302040f02030f0402120c0d1b081f020d140103061b020d050409050a02040b21150d 73
    0x101c00c0b40140140000c903d82d0000000c250a1203403c488414080d0b10400c28440180424401c3c03501400c81a0700440c215031446c0c4034600071032514048403c0315640001d190340c0166010f02200c00021024081400c000b2131044240e00070b04941c8100340d122030141c0c0001c82e1028803400b83d418010381080040030325464680b1030145690f000b41e864031a540040100060a44880400d0001040e46082040d282d601d540144000d8861308540c02c00d840f0b104000300856124071203001c1c0e800c00d4060b180c4428800112581c14a00242010001d0340440510788110070401071141c8824102803603403010485039601c021460307841d00c1c2c41c8425800f44a00c006841001d04032079003d0541c01c079402c00045140c408109013190469400e802c2504c500d42c9400d0040c030041488000a140394070340d48000c1008441d0600700400d14000c50107590b0b28070707848a010501640300354055070b001c0d040c1c5180640c0e40b0038114615210380320400c55401a101d100c80005a500600310280c541c0c09880601580082400c50303030b6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 366962724 1250 366961474 366961489
    0x51b03030a0e1c02030d050408010510031a070c060510080708010e0c09040606050d081810050316020102043f02090114120610091409030d050711011b080c03060d02 72
    0xf05040c0c074030841064000541d40030440f510307160034940c86403a0346509180105003950703c002d00500020180444c10000181000e60500c5010b40c11008140d098685000456866402110240030541408240000d074180c5d64440c500700c601ea40c04407981242d031411154241c40b1483d05000054100d129070728068140b0340400e070342c00352158800182041d15070000074507404000c0005c3c1da449002044465182a0301c40d014014008200c43d00400394130070420080141c4801071070713001c021a5001044c3c1120b4002d406482c050000381602002d1002503541c82c04081007103404982d003150091103038550035107110111400c0140c0240c800a080da08107103848281c20741d07088241ea0030800c0352503c8030940c1d00a1044034026840d04039402c032000d19240d0014151442115a030010044402c01d1146103540001161403c0404000100d2a5030350948290b0b582c01e0401400c0b0069428819580b08401c14420044c0c0031841544440f002d54aa481580c0c001c2e020803114140c201002104960240c0380079038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 366963974 1250 366962724 366962749
    0xe100c0908030309011e0e07030813093210150c02100e0a05010e1e0a030803040c21050d180b0c060402090f0405100c0504050904051b03030a0e 63
    0x51036039100741d48a2181d0302d07540c0304641d184042d9641d18500c01d145000c11420719400c0031032480a00038845407122254882c042440002d04078000050a100c3d002c00c0044507200510003848108144a061140c249582401c80180c0d42a0784605034520300c0700c003160b0240e90042200d00c00c0c10242138204150780614a40414400c0306102907122246d0040c3e503440241c0038003035696510ba03894020150103110104131181c00a9040c00850304203540d05450300c2200d0700040700c41c0c202601004482c0f070301080b04d01c032054002511000001041209112404510000329411140c402910032002c004070308845100d00c0000303040703410204204200d54454007003804110340c1c441e60484060f0b0749411007000b590002d48101c0341038104178108425803510324451941300c02c400d994030086140c00d076500380d10740c80e160308500080340c0c1c0c03169410754a1384103205031009002d0107030001c025401c003403c16a81d501c48058106002081844402041d03003004400d445c000c3c03841e82c940c240e420f0000001c1044494404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 366965224 1250 366963974 366963977
    0x30712060506040f140613121506080109030e01022e110403080c0616050412030e030102181203040b12070c05010f06140f0915030a0204090b010806131a09011803020c0a05040e100c 79
    0x149c0c0c420308250b81c45400d00a0102c1c500001c0e1000c1e0b1480c1c040c1c40e400701c4041c12415900040d645112070b4400c18507980250300c00100e05050784080c18003200003445011034001e85c1c0c80001c10003000b000100c90050000000f031104540e40d0795030301c01504660342c0180c81c2030400624188401c10040c1a9424200c0840d4800c4c01d00d040f4645003200400d00326017150050052072550060102c00078201180c1c2e000031f47c0701c0000514545030818015015030700c03440d0a0a05a00382c05400114003a21606544554580c000000d210040e2007074000b078080c00881c05501d124441c114240c059601e040066812400400382040540d44e803002540d100398003400450036054024001c090300143d841e40700d2080b0781441800458108d5041c0704041c0d182c0300d402800368841d070100303e501c00702149650346203043c0040e030003d0f900d11558540300c00a025000d9411090015800078900c8403c03d5000308107484041c80c1a14540e0400307586400704000c0c1c2d4004a50050981c10080784400034002c10f811851260519 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 366966474 1250 366965224 366965243
    0x403050702041406240f28050d0507030504031e0917030a020c0307030507090f060509090a030e0105092d06070b0a05010902070206030712060506040f14061312 70
    0x550089400d4580180240c0303d140c45903c1040700e5840c0420101c800c119901901119051400030515082c0c41101d0712411080760101c1c400d04004140f00545611901070944602d000308582409025a0003040b1b007030311810300b45070004100920a01c0b03018440d540559940343c284002c02c5100000308031040644040201c042008a54001100c120385c21214108005580e40c0305c0303403071000382002140c003c00b81c0719400140f802c0012807070028114058072200702c0c0009111906106440042c0800d43c8070a410400030010440c6221001c180440005e010740c407040000d5084800464851046640d5250b1240380720081c082c0402c0b180c03201d0720f03406480c5c03e61103e050800b54005681034000035821641c8917000400c0000c00c0c00a80183c1d4010044160b0540c1800c8003603000410713500005040c030003004481e507041e070101e0840d908414007e000107001c00d950303207482d8804019603120b240245c001c41d031302c4810320012500f044001c903070145584842d0b0041542c00e105c040020204260410b503002500c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 366967724 1250 366966474 366966487
    0x2180a020f04030807051501080a060f060906060203091516060b04020d05100f060203160b13061a330a0509030d0c02011707050405010c030306030609050610080307030e09040305 78
    0xc070000204040d5010b01c41c00340d01c418051034a40d142085071071043d802106200d004100c211000120610401d5100c01c010410b864000311000c014416540a1014036007020000940c0070780201c010071740c01030213681d044804015003003000644e02c901c1903116006584200b1190100351142c2c441001024000c2c00580362201040c06607050b600140d40d20600c00c0802001000052031014400740100300c680040d505060343c0b206e24040320428024041e00131110032001441d80181c0070301400480c1d03448482044003131499404441203205801c03506006845450f100228186100d83c6c01040300c101004100040c0352050041110307030041804078081c031009006515855605000d6a18003604079a142000d204007070000510f01c3d000680540b240386102030900c5001030b4044d00303e9060340c0c0d0a080c140103214040c074044005120715070010340428a440c41c89030405c140492424000e400411200341c101e500d503c80c940d224411114001c0200324821003850076814155074050303004d0f0083c01c20030309122 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 366968974 1250 366967724 366967747
    0x51b090c0a0e06120f09011107020603090c0307180b010503040f08091927050f0402040b03121210060215010515160506010501020f0c011731050705060702180a02 71
    0x7000342844602c44e03a040c0d82008000040318107980d900c04c0855000344003d0344120200d162500c2a188080c2c000e880000005400e480e08000c11032844401400704c580c0c59649280e6513019a14414040882c40d0510404407025845441664011a008101c4c080f00400c01c0d039423085185c0c0010005a04900700e1440c0c05207940700540340c03200614005094946090460780400300401180c2c0303e00f08039a1030702c001d00c0f50240301101c800740d210380d041d1800a4540319000000b840e0404220410004000000701303040c558080c001c44500030704507000002c00710382c1c4031070b42aa151425100c0b4007035038051200040009152078030284d040076040d402e40900d401100b5040800c0c80c24210000c0e10035500c2840100070a5a04100300b0380361300c032081d01a0508022040000f01900305044a00c41c5596420f0049000e5003e03502d03103182d00c50700c4210031203007402c1554150020700246541c103403424001d2500004580c10319004503103031658000d001e008220903030800c4410440000d030030342080641c240028018003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 366970224 1250 366968974 366968977
    0x605090408070318180e031b0c10020d0c110f100f080c18040b0f060a09181103160306150e041d0a03050f09030712051b090c0a0e06 58
    0x50303000300c003802e0391900e05082c00342c80034149401244401d280c1c408100503410b1122244908025100c401017800100586194958010380c1c5591395448020ba6605e250b079200041c205056902c10348000d8951071064000b603031906d500300d2244010441c441d0030040082c14002110220000040071815603005140205084015000b25800882d60844070318548980003940c0690040652180b280380c0351481025071150990b40030f0940c0510303255043c410760781d512002e07007518a0f000586015110034954200810b00fa48501c10b150b1400100388104040d104a406000f048181e91190213107503403111031000740f40c4520109003004043c1e640d000400c480c078114000c10310080040e51203900b41840041080112400b40c400407801c5844101c24800c8910007194a0ba1030a40500b070941e111071070056150054030584540940c10302485002152640a405400003814015411580d046040316a04084001102c21141d80041c401c000290044032a40007084500d005240032070020100e1004100c0340e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 366971474 1250 366970224 366970231
    0x4080c070b0712081305251a0304030807020a0201050304030c03020c03010e011a0f0f040c090803070602040603051806040b1008030301090902031507050d020d060803070b07030b0a050102120d060509 87
    0x946900129461401d50158115070000c1007030901c1d00090a5555a03140d480a00c03100d08000281c2c07a00b44130300e0b9030b03e103248180001c1c88c07800f203200002c9880b0400c4451560048904801050544010450003480056510035960381070f11000c0c91a10345440a588501d0106403c80861244000c0482151028012110080c4580e0300102d0f03941039158141e03051100720315402c0c0c041c0041d100da2002982e15100b6840340c10f1750a40300018001d4400c00105c91400080c0c000c412544400642c2800b004229802003044030343c20381e401c022640741d040740f03c004549040e480c440f80d54000c9021801040c0170102140d08804d682c1d81d4075650a580d1b100f81410f40d04241d000ca40b40380d596501f0302c000d5003024084e83c000d09070011a00c070030526250a025100c1d0150204500c2d010768042802c0c154112030740d0003840a801100100da07150280382c58007032103200c0c00f00c60780400641080c1141c580c5060038108041a114140c02400001c0428001c035101504880440c4c59442d07121000064151640300380c1500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 366972724 1250 366971474 366971483
    0x170403050d03200715020d0e070e07020615030a0327170c060a2001110705010c1815050715090c0602060f1302060a02072c0c0301050904080c070b07 65
    0xb03902800d064014002c41150f031840e15603500811401002031030144803d1401814540010707164451502004000d005100c1c0ba0002032103803142c00301d4042e0300e4a00c0701f03100e600380ea42195503031380ea91107144000e180c0400700316400d0b42c001240305000070300a0051045007052801c1003001d0f10b81c91034200e0b40d601c1030341d03101000c100340340c0c9150061008184000d41607600d090328054501881000001d04040546210b480e1a140708074203690701440a40000e0600c1002c0041c0d6620b50542c1e050a074000c0c4400d48050022600614211001d9003214000f441140c525560a480194040005440580c440c9204480755001900c2000120310b041c422060024000c10488410a0429a0191034541d011300301e40241191401004401d00c00c2811082c25154103844244d1201e6040d00240c0c6006180d03048511401c00f003032101001c0c1400d00c4c144040030b02083ca604002603d4481025040d0310017809416003086140380050301003181396000300040c00f00179017144d020503510030f620b0008c0c0c2c103d103200303d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 366973974 1250 366972724 366972731
    0x7030f050112020307090203060a12050705100e21060a18080301030501060302100516140f070902190309050a1b08011e0509241e04060603060e0316170403050d03 71
    0x203604040201c900608046c00b4218610b0403c4000103d45444a1091103207a01c800400001000001d01a03c401880050b100d000600c2030070101900b054910b00315107001380d200389400001c5d0710b603445294330708401001c064605521013a801002500504014601002d004070070680040c046000460086004800011b0458110310412000aa11030103080400c03100b400301c0910468412000241703564030214490001d0103101c00d581c141000b41c5a2a0398034020180c00044400d180d80040c107000d034001c40c5100f810b90700321100342d085030604903018109030b21011500000400342c82008211024410f00d060000740d0b540101400d4808001e80ea0703289601040d41000030940a000c2e190704000e0520140802c02d80c4481e1102800ea01030031600000f0b1940c0000c036a05003081c074a044040041d0748100c4032185050700784140540458441120384919000400410355404010307110255460f002c4182c4103c455182c0e007e50002500c0c400d42c08000802001000800401c1115565141510b011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 366975224 1250 366973974 366974009
    0xa02031c0807080405030d0b0d0b090a0c05060c030405131509020403261c0e0d0504080d05040b03191509050610030c170414070e0a1109010c02060307030f0501 70
    0x20001c400c0940310b40c05000c2c000041c4000903102000707840c0602c0413040c002400520000c0024646c048c0d524000e0211101c01c02070020894020980d1214a401078000310aa995070700280007032841881e04801954205003c144020720b0075510800079400040703808100240c00c240c1030711010030079500c60040c949c2e00141c00c01c1003100c6142c0c1d40000b218850101c5414001482000c8070070703c11310002410700c0800c400c848901002d0740c0d1002c0ca8240c2d00c0c404444c5c0106281401504036845405031444520130100c040c0c000511603400c50b000d45004501c1603041d511606400b4506600b042225100c00c0d4a07440d4200444c070041c02c3c150b0081031036030342c00304840c200001442018140a484c0f90100340c1407516011450360004512440940030f0701803840c665880c1d082c030013034803c003250700500395002d030140004910b12405079890040b809488200401200711100d00f146116007031a10780820450708100000d0f25001003d15032083c4181000b103a4034003010104801c954003604000319403011440f60 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 366976474 1250 366975224 366975227
    0x903030a081003320102160b0612460f0606030b0703021c0501080309010e15030901020a021e0c06071b0b0a02070e040b040206091203071208090a0c0b0307020a02031c 73
    0x1501161382c0800085240080e042c40d844d5103e101003001500059240300810005c1c0c031902468884118800280e40c0308001c2c94041d810881042102c002c900d40107805004541ea8181c082d052a481074012407007180e00050352030f41000c3d0f0f0301580540e81107540f0040000450f1442080c148140903d6900503900c50b00c03201400c9000d0511000a00744502d0440103000b262000801c07209800401d0909100ba5140e200c0080c80c04103c092a000c2550404810700151a45c150040c107a1070003207409940040c0e03905101200880455450b281e11039005c40b01e499441e052a000620321039000d200071814200307414190516018442c1e0001c2c1240b04e0001e42502d4150b410f10032200a4a6a114010403d007025101c1015108005c0c0001e8400e820000d144101940c800709034000e221304d240c0c1901d4031080701382007100e00704048000040c00314002070006140e205000c00c003825100d6001d122204603a0608006c14560f8000510010a622418a600c80980d030704020406000040713904040a0000310f000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 366977724 1250 366976474 366976553
    0xf1728021f050a020d1a040b030a0312050705040e130201032003150a1d040c15050d090201091a0c0d050a021b15120f06060903030a081003 61
    0x21210215000100420307403140540c0d40440041441039000301d00703901c484880c0f000030721460b0300170800e0500d4440d0768440044e035001142e40b1040d0442c1d0030040034120405050326140c1c0d0003001000242015040b480188107a480142c20a09600d442e030b05041e102d00024801e160243c0741071801c044500358107021503a040c0100200c0140180d00c0081d01240644074001d10701028102d880d0004414049081c00e032160040503000705040350300c144035010301c0b00c1a68180001038600b03981d1003040c0300001c694070078000d100740e80628641d90365604d030031240c4401000500d074100d001c0b0704018041c00001030000c49010050f0030317000618440c1d541c41265040b824074000500d1086d105101084c000f442c0e00c150080f03040b100c559005885015041c60050010340030045182c4000d1000e880450700c841e00309080329615100b1170320360740b4070005500c0b0401041a24003944154503071561082080c02155031062425541044001d55600b038011784907500c03005032540b84040b5040b070081c1c982602085480085 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 366978974 1250 366977724 366977797
    0x50f1c0b0402130501140c0105070f031803090528080d0305100305030712050408011b080907030b0109090204091a10060503011802090d1202010b190b03040f17 70
    0x7a0214980072040241000c80102449928140311440c4040300c290f01c444422101d4040d55400204010311748000080c0950b4100c198a20000e0301d0001c20b01c02009400401421664040c0c40f0407070201c0c074110400c4503007440c40c0700400d8000c840c4d50030303000c2e490a00019480030f41190000341218140c54a0020202c407001003d41c030007a045420b08102050020040b41e0046070008012100c07045612000e0b1b91911481d4030680d600e602e0220703070b0010307458030783c0102500780200c1d5111001600e8000b4040d50360221404054107007985040101b0441c0070f26889241c0b058409030010400e0441501c0300181070b8440e008a003142c0b0344c01400c211a43d1402040b010191019090a9045505001d9903101e08490034030788070141d641c0010f288515945103030341c86103480e0740289440c05107940024024040c18040c3e40c5103000d00c200749110358204400480e441c080d6150310603000e0855980da01c03169170501c54014240e55240103207030504c1ca0640340301d000b07000300c1e454101d01c4044011070400c443c4441d40b204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 366980224 1250 366978974 366978979
    0x21030115020124092306090c0c0a29061302090a08150f2802070c24030506010507050309100504051305090c09090a110f031509010b041806020a050f1c0b 67
    0x4030180001d00c41741c1c603500020152007860040d521905000468440d240c900b44a602ca8116100c0c01c00500e07141942807035580050a4041c0e039035451382e0341c08550043c0c6c3d01c1a8040c0c0c9024080c40f03c05d020f0390280160306001003881190940d00c0316901d0810340a400e0a80c46600c0c04010440402c42403400c0907009110311480e10205000d194042882c3c0c0242d200500e1031a070001040c400344860706442e0f0020305074504e181c40b00c4c5000a10b00d981d61880124500d0301107400d240010306d10b9030081040e40c540d550000051480d20000104000c03030b03100503120711803d100041c000402c071a183d0b4803100d00c00403c03c680005030b0b0b0030f081d00843d140090040c5440d10031030b000f90421882010215211034242e621602c0d880c4502c0113100000d01c1030700c03080306a54040c0710b02080c8041300c0c400190040e01882071840200300750318a80c824031086d02c1100030070114020341150004000b4100741d0080c1040b070011300c0c0041c1400380076a002031481e44501c0c800c0165807100110b003441d01001c0c2c401c00c261036004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 366981474 1250 366980224 366980261
    0x804021023190c0b010b03090a120507111c0f080f031303030605040504030e10091505070c050a1203050a030e010204030b0f1305100b040902090a06082103011502012409 74
    0x29130396204000c00d050045403201800440490340c1e188081046c6071049502003154003040005803030081540d003000805a42070000c46503011140e08012082d0600f401c44100c011201e8003076a1a11560700b1081002181e0307000c020021800d200b024480618000d008010040344108071a040050030782e012504000c6c0f15503e48000d220000b0b4001c0c1c680c806c410720a480e556002007044a0580710800303640d015190310310466a2058846602c4001045000c0c40f1b1b050780100b41c0c0c1c8a0040c045501c640d030240581a601c0140d004012034040d0000d0030078032105141c0419881d11048100b800d90300140d2084070700f400003c2c00d100d11181c10364007240e40888149440c20000b0380c5520343c0c40d5070350410380d01035168540d40d21002c1035540b5160020b00800303401401c405024140882002d000f800548034000c4140a0407001070851113881c801e1420079001f0700502c41c20341c1d017020080c1d26001804032860003035650b079103408090151804105141c6100c00601c6004545c40c14031288117962060840000b548103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 366982724 1250 366981474 366981497
    0x110a0302030a02240103031b02041518110a050304140f0a03030c0c030e1302090a12020a0501261801051e061002070e0406090804030f050c040b01080402102319 70
    0xa00513801411260980381014501500c1c5076050f0700156503001c06074010341440101903840e483d00c410310f001c03620409241024410500304000860706507100480400c42c0c100051001103102d0409541c00c54041e951007003892607040c610320f241200c00c902556182d0491180503080c503425102e01002002c0c1c5007440b40d0842d8003a80c0c020410128840414850b4400c02c0203803690200b2941912943d203009083d800c08207495041c15400804006000c030300c02c1481050100300395106200018041c0000b8103c00554403146810120300e1000410700042d0528050351510015824050303140a490042c484040d886242160384518110043c1a075000300c0301400c00d5200607600044d0b500c102c0f149100350301d21586030f92614001422940c440038008e030a001c80c021040c00700780100204010300c52001ca629036281d02c800d20007598503141003940411182400180503081c86035400361031032a6460041d0b03c049034444003001c42004001111421080403c0d00d00c03e0643e041160603d1030001c0c00c04001d00c61 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 366983974 1250 366982724 366982783
    0x80906040509131214031303091203030905161a160f03050c0d080c0f220608070329060306010309080a0914040504120c1a0103111809060a020901110a0302030a02 71
    0x1b0001d41012000105a42d00800b81842101220007405422504c0765148035a810014003400c145403017035440e8003c48103806400000040d20b002183c12459031400b03d030389071900e880240e8103e0405c403842a10f0545a920004d034800b458084810301ca61202c503190740c20490507618010200c44400c2c00e0006800c180804448030300141d9828441c00302070340da50b40145400048200c047d10940d01d144103401140812005e4020502c04e114202c103a03000c00603000c10400f0300e41d031000c200401c00f030301d5995100100e50380e00b80300c8015580100181004510310482e03130785440072a40910240300006500c3c036024001d000850b1300801e002c0200302c5082c8414102900c038100c10303803040920032003400402005001080100142d4412a080c1d100750061103603500e0402c0310314542a920300c41c0c030881c01c5800c5080d0b00311003a544680075808510003008180d83e48400c500096100d940c5a9040c05094001540d80346010400498454400c1d800345440e00c42608001e4076101d61111510a541c5118229a1424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 366985224 1250 366983974 366983977
    0x16031a09060c1b030307050406021b0f060d140f10060512160c140601140d0312021803071d0f0f06010c0312150614090d080906040509131214 62
    0xb00c1c4040d081c0e80c0e00e6883c03000c003424050444242c160280004010840c00c03d8010707025000300c64643c0c09a03980004000c0d00b03003112041c0c100515600000c295100e110301d041140241c080d610700c0e40c200007074440c011404148102c000300e4001001600c6031003044952008a103100d0001c040a050443c1050003055243c1200071004105030f0960303610303542005802d031240103425040e6421a844010030f0702c1000610380c8501e001d0242c0020390411040c60300081c00e00c65100101160150b41344181e40c1c5080a0581c00b0354082c20b8960102600b00311507501590b010b220304001042c0e2540002070760382182000c001100c030b005000c0b803142ca454100b04000c50b522413660660104092a200c6488140d0303280c152017001107400c4044140d4034110280c4403101400002c6010b846e8a600c500c80130605000482c01c291140c840030b00e80010820704884c002541d07000c00352695050050070301e401d1613102d101045420008843d0b02442105820050003072080140a0b040c2c1013100d840e001c2e800014007042000c2a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 366986474 1250 366985224 366985231
    0x4060e0418020d260901050a030e010f11030901050718090c1b050d0210051b0d1803050424090501110a0b100509090d02060402130e16031a0906 63
    0x303991115101100004401040014030754003c080ca5480000c5040c0000030884000d000c0241d2215118160182101c10080e9441040705a6403d40f0380310b2100c4040340a040510240e480c02c6d900c40c004462144114000c50641c800b40c1c0c3c190548030320340300180f64203442020300340341d05224811400c4080380f01c1c0f861505007642e210101c0841c01a001d44000c0f41d2030004581d00e01d0525907055200c0e0f08001c0b011546c0d81c1040880e07800c540706480400a0b22046030000d81301c620f0450800950030420f54030302c102506040b040d8480000304e148051700d45440c014442c0038200c0000f0000141807101c00d09031082103403410000340c042103441e02048005000102c660150030b05016039041208101e60080112245045d840058070300d45081c01c040c585020070980c0602d42c402c401c400c00007141044001802504841560b000744003035103840d003e026403629940142500551070b040428034a000420140c0b80103c030040d00001070514606010440c1410040b1040c0068907901c1408084c000c0013685580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 366987724 1250 366986474 366986479
    0x506240603071b08040b2106010e030601091116141002040311090402060d0f0e010c0503100e07090b0a0c1e020906040b22050a0b030f030a0c11030303090109051204060e 74
    0x20b10019814813031610b00440e07003c000f003941c002a4017805040d02800c1248421415400a562521118019500030551400007a0590b11600040000301e843da0000c07050169040809494441003c0c03000b0b002e202c1c100416070300e20090804e50f12440b04200064604050107403400c6003414110b50b2289031542c81910721310f104105c2040880d0a43d030311042164061642c02000b04100d040180307100d0081d0003580c0c40102c1c294030301028039900500880c200c0b84034080d5420240e00940c1480985c1d502c00c032014200700100103100002040030401d603401000c802056031188002050b0302d1528850700c09440e0b00c2132243c0d5551021483c010b84461101c281c114030100d80226a0351040b5000c110100d1204600c41f2241d0324405030603002142ea9484640610082801402814191400c2c13555460f400c00e0842085d500c100500c000d018420030f54181c1e0540301c0c0b0003c0da105c80100001a06e150003d595101c0c4a940d1280582c04200c020010480782030030b880c030302a0800f854501c020340038450300090f003030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 366988974 1250 366987724 366987767
    0x6110a090f1a0307050d0f06030b01051203040b18030601142103091e040c0c061401080703080a0507020a03032c0303041205030c060c031b040509070507050a050624060307 75
    0x1310007074010303015500c03031040700c0108000f2440701e180001c028005500c41640c042204100101c0c050a00708100b05812044500841c5030038503000181c45c050b4040307014004611603900c40b5042683d002c0c408075000b42000702100c6050042401004101012000c510039401a42c40c240881f0031004019030341828001c942c0711100b810715a03aa4056440c000d50500d61092428107940c91283c0c010003101480c6000c0d0303808115580c1034407610082d0080032301070000e595000710002c2001071307890303001400c0114091900e2400c02d041c5a0100c0e54008043c0c004602149404658030b020101c8200754004007201c0b070003801108000140400e0b241d11650080b00080100c03c0052400d00c4820412155051081d03012100c8602d03003030420355944e800540d100841182c84904101c030f904006400d803415900d0040c0b24a45a49072414166680d91021000311750b00c0c090f0601d0400414004d01c501449200211303152a002d85200400c03071855101c000900d44a01000d106001d800c607804006062140f5020110a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 366990224 1250 366988974 366988981
    0x90c120c0806070f0e030a17030c2119060f0b0705010204030c060c1a04030909051306050f1503010e060106050c150103060c0305060d0b0c0906040306110a090f1a03 72
    0x880c0140c440d40c014461500c101000c0c0003101e82d0103800f035003034005a40d540940e0074450900701030b141d10b00d110000e0304201e910000c800342d11108000440d0003c40c0d901040b807400034101d09491b440c8c10f00700e1140191803002c20400c181031044003402e0700003018296041011900305880c03951100564040c8483e590310201c0d1542c2084000d504940c00743d50040e04290050f6503942c401460042d940e4421110090420b075505070500a01600c2402142d064685c202005e08000040d030060200410724020580719445c08404a51f2921070a4002c00c880d060750030481c60030a2009030800b0001d402c60740241c0c90604112010180491000e06560f03c500e4802e60310345510030442c1c94001806060629400315900010401c030035584029004201030f142404150b540c08100080b02c0c83c2180c02410303540c5110b0010300c1078a854002040c103040c000700480c1c10705843e03440700ca0880d04950fa010208880c0064207a060581041d0108010004010141101814514034a50350388842e41003441440010012 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 366991474 1250 366990224 366990233
    0x6063f050a0b19050111031305011d130606080603240402030a0209070e041a030d0e011202040f03050705040c0f0503151003140c030c122a030103060f090c12 69
    0x209140072006014144012140944080c0580b4a110710345c007203079120501415015002c000e4401031700100c03101035040c03417801006491003640560141c01e01d00f0568801c80499848001003210504051300024085003800405040c100020341150b2013a80310215080d42d0004529255403100c0340c400150341a900c552010030319200c44824000c0d03101071710108000003140d10803094401030340111028880880191520a521421260b045405030032947c13130400d405005210050300ca030411714000c560308500020000807030704240c00000f1000c012076030130824410f00b001214044c20f4219020008416908006099102e16041c100140103000c4002800d02c0003000800c408600c0150007404840b915a034010700500d211948410401e10304808161446401416607120b5500000454981089094410310016000b130245001c200d211140c5002076a5550b000084600d408083e5500c82d41503103805000c0d51804800c11041501e000070780c0011490040b00d002c212005164403e0b00e18210313050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 366992724 1250 366991474 366991481
    0x90327090907150e06210f160e2710030510111b031306051b0604170d0608011107021e060405060a11300309030a1107030606063f050a 59
    0xa410980035420a40e41b88841600e02c20a100d980e4035400f14400b507860b6000c0144100e002d0400700c000030780304111b604580c100011010500c1b41c0258802e503114010002c2c001c0204002c60740000c070364000940810800004000b00e500340c541d11203007482440c0d4840d030354400078002c5d8403000001b18110842c80b03445c40300610072903007036580316200b001910b074075020080c0207940442d440700503c500900035455440c6001c10184d00440c1d210b8600b0545584858051100e44c21042c11b00c48181e955000002c0c007043d00340309060602c1c0e04418070684030342c454010441c605e60f03800c202612340c100e880b420112039a500b20444082d180f04441d425103914420b0f404176010784098203101154850f09100c001d0000c2e0600c5802210000088208401d60f644000d04926010640d0b51004582c41882031b1300c0380c1401108101d09907903030321013102c0e441581c948a920a40e1020f82c09280468070324500f50445000c0d24820180030114440c3e80300e4000404611700024a04014074600c42c16a28000b00c1d101442580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 366993974 1250 366992724 366992737
    0x1050715090309081006050108010806070903030e0f0d230d022107021009030b01090204030807020d0f0c030303020a0f0309081209101e1808070605090327090907150e06 74
    0x411211715442c0310840200800700307402103501042c211000010b0616001030305c18400c01c1199500c1c20854039540c3c0a03110190b0914807154440411640d4508603254010501080c0c0d001e86404190020b0000102881e66408040020241c1005000e804c0d400c1d00091b104030010080f00c0e01200c02003070280b44220700d0181e40d000039841900403a55100080e80040c010f0300303a0f8003c03e400a00e5980e01d1740144200d01c10b5103c0282078544c02c0c401344000d841c007122502c40150040c4400210140300c1c0d0341c1d54640c50115041280400d9010550b048101e034400c2c0704080003900780c04c041014602c540c5500c00789000b0561000b900502542c0041c6050310248821004104040c07418094031001a0580c031829881c450350103003a5240480140100d01603a44042c19a908005140d10f040301d20b4071070902406001344202801d00c401c20100642e0044a440c8205101c8c484c0441c040707900840040003401c000182c175054440d8403415084c0a00003105800e403e1070251030401d6205a500d44002c03450398007464 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 366995224 1250 366993974 366993989
    0x2070506071112190f2604080c0f030a030b0f0d1506150c11060a050403200603040b0610090f060509120a0c1e0b030a02070f0507031103070501050715090309 69
    0x1051011495405850741003c4054035200c03c0c560a6250900f00c648490400001d01c10b12082451507400811b14140c49410600031000c0e0340c941400c9100702403a00b031200741a0311042d4000203000d010a58903211f1090604411202000410f00280004072800004000540507030040300c50422055102da019900410a40740711400440d0300040140c0ba0708a40001904c40400c1c00e03401d86440d16240044403000c81c804c0d1201402c09040da10fa0000344080814840e08091100c1004031013541d507000070b540705510071010310315646094002d10026903152000d0600784a00d42c0c0040c0054030005413088150b0311186081a2500c15450008070507070104004a607003401460055000e004c0e02400d51010b49403900d0090821076003016412442400354800d42002c40414404a0400203e54008000c1e081c0142c50045801d00c894803a6410604a035104030f03055000031066070400d0409000090080000342400360130900240c40e9107154040007041d0196580d07481d0741c6103007098000c008680c05001403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 366996474 1250 366995224 366995227
    0x1e0e03070209091f060506040303051b01060906030c080604030806011b02061303170310090c0309080c0d020706031401050f120d080901111615020d1119020102070506071112 76
    0x42101c251a0311113008420b949101c0820403242200d645c4c09080d080701c0025058070318007441c5031000c4078550490410200900c0c1c10042144445009004003006041e05083c0002c1e51451464540000c12060b0321400d455000f6008000102e40c00c40f149030b5024100303080803502103e40068003801e686001c28000d60003040400d42c1c075450901200c194060340c1c41b680902480d5a6201c56040081c0411650825040900031060002c1101900400c070004c09234240461b84004560701c295103604440490544c1f0781c030545000820036810001e100051400b42800c010542001404c2406050140116401007052003071402042c2c4501810071000c21282064445490345a4001880e140060300c040009600309412500ca20390710340c040b507583c210f103003881c8120710015079a0307a0402e101002862642036402e02645a650740103000d04003440251012065440e024003049903030070307040d00154104581c0f0610490300040c50000342e6a0b001444d6040070000c012074411103600e0825241902910b40c1c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 366997724 1250 366996474 366996481
    0x5060a120608100b040f09050303072d030b0a0609060c170f0f19170a05060d02100306081005010b030601140904020a0e0906030f07120201020a0f08030117011e0e03070209 75
    0x55540c03110342480001c171401c0c0613403603034548084165003440002604607002000403c141b1401031503042540c1c6803d4860300758610f0355000321901c400b804011400030a4440340e00210a00d00610f02001401480c2002031029080c4000201600f244c0e11005180a4658801400307510341d03001a82c0b440c2580e280d21a03a1030304204015176990301b0410003c2c80c0d58007074103003c1080700c0c090444190920140703601d41c101c940d1070f404010003a00000c1d0041d90800c00080c02a00940c50794240321425489a84020032101d15060f070342468454041e4105200503e00f200602942c40c940b0f0850b6008842443e1404100102450766070b01481610390007680644000345c0c2c440c10a401071000650b46c5411100521541c5d03882c0d01b49910342c107600344401e013147c010900907c00d158250b42c600c0c094500600c100d5010381c00380e9681c081e400c024080c0a5400000c08801084840d00480c07050190000b00c4000380020070500d5440000030000c9003070540d85588914501d90040740030000e0390500340d0000c0c11300d5070900707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 366998974 1250 366997724 366997753
    0x30e030610031407030b0a091a010602030c0c030319210207060903090902070b1f0503071707050d03021b0402070203010c030c030b04090b010b0c070323150105060a120608 75
    0x15070788421a0408024001d20301c00f51004038a107030449070850074400305036855200300300081061a90032030b614002c80300c0544001c0307480d90405000e81400d070015681c846503480020f01e011140b0307a1042c46640300308020f00f140340c941951700c80382007424204030990b41085402040c596402031010000c461000c10a0403d0050035004101440e000741c0341c8030019500c0d010343d0382c1030788900d00015191280420118603078400714003950780c042c14040c100084480d01c0d0b10000741442620340c410210441c0c090040c0c01c00744400d0000000508044030001da0801095030080e403a0a620f0a400d0350b4240b04100403035058407160100c800181d40200204003c840340400540100600382e4000000b0b1300d020421402e508041c800c40c0403c5800c00703880c41c0e03176038a4120282d10644c4500965105801101c200200080c804c50440800f1505100e504407400b00fa004158500030803c40c03400c41d001100350041215442d0300301110903468007071600410081115000002514241d4401662031051440882c41c18 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 367000224 1250 366998974 366999001
    0x305180312090c1309060b06090f0f0a050d0f2310020d061203050310060914090402040212041a0a05070801050904020114040f0e0f0106020c0105031305011109090a0e0613030e0306 79
    0x5114001c101f01300d40041e0180b104900461268980040001c81d40442910349900c0d120800d8600800030100d0070b45032400710304883e22210007101c0b400d080181c40010050751a00c1560866000981c00500c5048650450b070303641400b147d50356200f540040c54621903881c85e000700d0080c1401a00341c41d0768101c2487d000b06503038422038a84c1c1035141000c401041c3d0038410004001100c0c00d10084011000c00401000081038010304101d071312560030002105940c2000c0e454610a0340130f546282c0e0b0b0240c19605036015500020003400b4194a03140800000039009551141075603801e81e40b5140340d40e903510050302d990003229107252901c40080703030000b59072203407901150545170303025144036080c0c643c50b5400a03c1c0100b8010100560850f040e104807070751107040616889441d0704078210b0021801d4480d82d007101d0000002a0402800094101050410044051b00143e1100781081902000c1d1807032074035801c000e0001806100d0000c401c030145446206803d030805030007410740715541000000c1c8a0035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 367001474 1250 367000224 367000241
    0x6120a0203120a030b0111100e151006020f01050c03010e040f061118040b03030901180b0a0201060e0c030411010e040e06010f33030f0204080f010c0305180312090c13 73
    0x9003017801d0715000b5485000c921003000114001072800c2c039040750740103000e400c0c13561948440784200101900c1061408000c14081e047c014441000e050034454000d0030120107441040050303060070144001c0c15518001c030703811a604808040015126494043d88140200f480a0b140d241804c41184000c0d51100041c880c2c0600b030341c0c007415400140d01c18081540c0030290704c1c6905030070038840903003e94011015040f00c3c0421a110804003074442500039882e03000b13012101c0060b03640b00c40500c008828118019003191201407550308500d0540d0711a9030003480d200c0710604014101b1a00c210689581c0c2102c1402d0b4151340039070b0020b6840d8040c4011201462045d0000c01092003102c20018500049003400f030b401184203946d2041c1e1240040d00542070881000c40d0f00da500b0400000e041405010307070014500c501002041c0042c5400340201601c50181880e00300090178034942ca10208c1c0002210345800d0303d20a0b1072450380e0303402445410071000901e800d80205140514400000c01c40d40807445 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 367002724 1250 367001474 367001477
    0x83603012315210105070207241218050606090a0e1b180c07020f04060b16060e121207050a0503061207080d0c0519020906120a0203120a 60
    0x94299105541121125958000d24420300460104070065840c500c00101c1920103080f0010360f1240b00001605030030042c1d80c04040340d5540003401041035050103000d00414035082d00360098510140c8400324406000d42d10400c1c0500f0102d15046c0c1d41040c0c0001d66415030201c02c00e6070030390543c10f105840b03000032501c9a10980c21000001c210f00010300c155000413000f40d00620784422100c5594040d260801811a803000d42119822180701d281c0360130600c110f03400f00803144c0750182c81c41445038865189810900ca5802c001c007d0160362403403019548035044041d944208030000d410944000c041107000b4204501030039244c10702c80341e000c500401601002d03c078401401d0381d80040032521406079204247c000358041010804900c2c7c80070060941902e09420781e2122640c42921500d890070035854040400d905807400c4040c08014003c528500d441d142c128030f201b204690010304003000c0286120300c94004408450245101080342c1c0254950190484540c0031280d00902a15040540c0100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 367003974 1250 367002724 367002731
    0x3120c0f150903030103030804110306070504050405061021020f040602030307110d080103020f21010c02070f03020a0603051f2304090302060403050318030301030602040603200708360301 82
    0x1648000380a5400380702c0c180400180d0f09590840c1d41c101c40e51030016006444001c50140c03025813a80d001d00282c1d02840321f548030310b6640c510f01b20a100a8a000038051445121003507032422a00d5003007000380b80540384814004000100220b802d074000e01843c0348a080002e00420007007015a0000001c500500154445000400b10302c0c070a030380e0751008036002100140d03110b0010001404d042910791031a410081c0001080b0031a0454403400401a0015010980d1903100002c4156018000d8a0141a449915880690840e00801c2c280c2c403861081d8410140d4540025442c51214040d0144070740d411850a10102c3d81c48840942010a0141700260504040c0904840740f5281c0b0882c0c43c2c0b03a92540140c10301da915618240e40c81d42000381050040c82d90714001c1e01c4000b009000441c042e500c1804016200e9042c11001403c031020400d107164903800640078101c18108100c20717210b04617440b400c1540c3d290301498941000984007803200c3c40c4680c2072842070f2450403100000c6000380c10168000c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 367005224 1250 367003974 367003993
    0x8090f15090717060a0623060306040207050d021c0f1b05070f030b04030905040207031b051908190206091b0f04050103150b012102030a2703110c060d0b03120c0f 71
    0x105080e0818003003240c4480980790201c0c6440c200388d8050b562160008000500700503880c0c40348c0b42802c0c2454841c00058001c14098403405510003603a04a032041854a05404010400090305149984030010301d00011000e01d0802c108081100101800c040c0c03420002e0aa62460b1081844006403011404145032900110b064202803080c0d484175509960354419024404030000d04180d15420190f91501030390b404100b082050840c050711083c400c005096a814220085454089601c610b000031900034005110b5404000642d8003c208a90440c0c1703084081e1540c00100c04100c40b40000b60881e0524000000b40410f01100342c02c07100312032030705000e035499a000444001d46040314980c05640e002c0014039035489590301175580001880340015460301c030a03444140071a0141014142000e100341d0b201d040541c88640010f58060702e070b00503c003100f40c0300c000072028010300b841281516910325a042459030b04000484004948c2428640d4541e00c10b0f61721500c5540d49104050503203c0c44808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 367006474 1250 367005224 367005239
    0x2060709090b180a0f050115030e15010b0a210509010f0b090a0917040b0712030501080a0b04050c09090309010306050d080405100c0b1608090f15090717060a06 70
    0x20a000741c0c10050406440100750f042c21030542c01c0150003089030a6440d071040c000b250507403103158007030301e401c90521807901c4209100505480d603102400d901c5821900040081191a0f041c240c1552240c40ca2a071715009103410481d040000c2202c100214060454401520140c540c4498050f0306044002d0102d07102d031a20940955018050281d0424501e034001046807105a200340e2485100b010f4001e20700301058200c0c0040d4000d5003050100100005100c010000401c0d40ba140c2042d070783c1018050780d0b01d400c49042e20b80301c0a040113880e003402c640001c4c081010a01c0354804400300100031000c2030030302c0e02a01d95690051402c080c0030a1804102082074a407171200100440c6e4004042c030319040c1480c09001715204081013110078840101b126a001441009041d0f02c9021050750241d103019111030010070048014100c600c084c1c00c0b40441030b80c6101c022900340c003090300400000c0059111a02214504031556024900100300e81d8042d00c0e1002c00890a42c2c0948003041c001d214440c1c4450342c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 367007724 1250 367006474 367006481
    0x12020711040e0a06020c060106110a0804030b0403091e170721021f0c0b010f06051801140a031a040e0a060911040e0c04140c040302041805030403030206070909 70
    0x140605030030120a4030046515158000c42d0101c0d01c500c050307418250140d070320a02640c11040f0700d042250095401408802c3c0d10507401360000082c840101803109558480f250300c1c2c410381c000074001011100010341410f0045400c2c50003800d60351141c003c000c0701100030b16820350340d9000d100780c240c400c1d031003004217460000364940039100c00810007100020072000b081755880305094101d07001080803110780444d00540c040010003100c0ca072207403c0014810f141040e0070000582008031148104802400401e511800307607010a5540e80581c1d800d2446100161007020110f00301d100c503000000b40f820450340c0c3c10b800030450003062908840f03103d40c0110420095940000746041c1c541c5c800c3c1081d40210740917800c041d4002d40217016a890f20840e2401003003c0e01d000e80d040000592045802c482c11342020311030703085801d042e00d00d048454107041441000b907202d09c0c44042e206680b07803034403c1c4050b6900741e85c01005650003812655103680c3da2030b010f03481d60b6040359a500131070f540d00c1001a12040b10301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 367008974 1250 367007724 367007737
    0x803070b0f0601270312120c0504030f02010c02040b0618030708010e0d1206050618010f0201090c1a0d02030708041a1003030f0324140f03060a02070201021207030309031202 76
    0x13107914010340ca0011130805801c1d0f25400040b240b020000300000454080035840110070318560391078403003620748107004007a180b801c54503404005081208102085c170300e03412603c0d41c960910349024103641500000c2e000d02110f0003c2540601c00140c01628051120070300340600c9400c0c2c0c00c2e11545580da480c054200c1d08080381c00815500204d100a0300035115007c0c0c114143c0075410006002501c601c0421155041520312442e42c041c000254000c640c0c200e442c2c82805e101e01d100030701952140d80d40b081c422020074403420401200140104421070580070650718032100d140811501c9180c000c800401e4504103450588e40d880002d90301040401c014991944604c08100408203c01e10310350b0210340002050300003004050f41c03130391070341200c210b21105003030704070301c4480e0380d55000b070514a1044c5e5068080960074841c41c03100000300c009440216840e40e0110055000584a20755800140d05000302c80060351040c1d1000525002019050741c8050075160096541010b503014000a0804078403480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 367010224 1250 367008974 367008977
    0xa180b0609060a18030f050c0405010b0306010c030e010207030503030c18010c03080c090a0513090303110715050702120f190305070c060c0e03070308030f100b0406120b0a0803070b0f0601 82
    0x40203808000d80c0501184804a100240304540c030030b503039481d01b8045401090046500b60481d0303807505042e240a0240501401040007040c2c0f443c100000081d241c0d0700c00f2103000b03041c088441c030f40c012241e0081c440070004580060540380c3e24680031130000c809070f200300c44040c11074011040c0a034a0354800c5454600741945a201d20390140c0391800d019a06400210740c1d50b81c07010200300040b0b4180c451201c079204031001d003039010a002d030b501d00c0c014042d00c5c401e070345540c1c1d1013001340701d00c501041c1406058503600060880015a50b15141412810a80010b05040b420300d400200c03a260409100010040c01064806100c1070302140141241551403e07100040050342400e05000420440c0d84100c0400300a41803074900c0728034450109041001d154000e03189540b01100700b0004c042c0030b1030f00d1030b40b2149040c11843d6031401d201c0d400c6020b0180740544020010409607402e46042c0ca64400744400720018070441481d40c0e01c090b80c655950203080111380104652011404c40d180c2c0710440f5002c0c0405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 367011474 1250 367010224 367010227
    0x10e030a17090a02040e010209040f1b05030a02040b07080a08010905042d05060a090219050907120f110307022406130f1a010807020703170307020c0a180b060906 71
    0x80c00249001c1001d018041075000700c0142c200160790314440c010910072000009600c625542d4100300231102680d1155040e076041824206a05480490541c06000141007003502e036191050b00000030b004a8102c1e0b809004001002c500340030115003d0329425802e03680d03456042c0e03281c4412109940056500410300700745407141c2d16540118895410301d10401d503030743c10203203589525001d00c0d068081c0c2e0709000081ea01c1c54951301307500b0404070034000ba503403101c01c22001c5498070b000310345038420082429003000704d41c0308006044005600041284441e0304002c0c07080204000000c0c0703640e8000e0f40d11101620401e20944019100c078490b04c3c0c124250280c00d65116942e0b0400d009904101400300c2d508103507501d0000810110620401e0503843e46800c61460450284002421030703800642204155030100804000060481c007401c95442484000e1075181d03201c4000c180e26220800142d00c4c0c3c800d10850000c2260780107216240c0c041841580103000d1401e0280600515200350710384150031440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 367012724 1250 367011474 367011497
    0x20a061715061c15050102030c0a0308061f0801140d1104050a0f1506090501110d0c030c08030a0b010f1704020603070c12120b0a230111070b0c010e030a 67
    0x241d07030403044650710103010340d403070000d040400c03485800740303051461082030340d444501840c4242c800b200d1000d01401e00003146403100c040c440645c0c820000d0001420014100c001610700d498020741400000084060039092450104000c0d0000000b4000d44075041c0340500508028541958840001c0790081010b079031805034a02070201900e8014454850240c41c0d509080a6407080e00c200e102c0c1d0045481d02000c2039007010001441005181e0126040243c03528541e01d0307011010807520701100d81410f104010000e103103820749068034015000b50024801208000038040107030084a0381c52826640e1003125001d864003581d540c640031464040c5490500002001424840c0045030481c42c203003054419a10540e9075410b40d0400301c2c2c4000e00141c00c010b90820509994001c4040090b803c03a8819020f90800113120784250760b202102c280707410f400d09403c81c1a401205075500440c1c1060070755020503100d80d202101641300010128623986801080b800f9100c0110680b1407800c26030740c600d2655031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 367013974 1250 367012724 367012741
    0x5070806091e0a110d02090a12020604120215031f151725120501230603040609150e24011503022b050a0905030f07080d06080307020a0617 61
    0x4a00074551019650745100c0204e41c20241c00203000c60b165100405a41c800b4035205012000788190f000041c00c141040c0001c0c0140d503288199010b8841417090710103200506d00009a855100159881c090b8000009100e020307100c00c84d4030100c50411140c0c1c18203071695901030b100060441c0c55400c0010b1a04840c260342c0720954115a500043e040300d0404000d080b001c101c0800d104900449000705900328a00f403030b0003101e40581e500414540c48131040c04001c4940030400b45220400d214442c0d44000001000c04c04260702c409115604411440c01c1c4105420501d4020a520b680100c001d1280c03240d0030b01702505003d00414040811440da90580c0d1030f1982d00000c1881004110040c541c00340411001214490f20342d01d6044c404408482155044c84010412191f01803c0b80780300d14100714524012400000844090442800c1110355404ca00c1c1070055160250a400515043c100030f00000c3c4000004041c01c484c034021551181110b5580a003a510a402c0500303d0b004a440d03c400204002d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 367015224 1250 367013974 367014031
    0x9060c081806190f060b0f070b01080f070b030603032109070e160e030304080d02070f0b070b0403050f13080606011b0b01030b040609080d060303020c030c060f0c030412060507080609 80
    0x758240b0000c50044c1e00c403002d242a9800107e0080725040d0003040c0303042409806203119005050810140034a41b011a402c162a6511400303041d662800020109146407070420845004895510b030201007518601c8411204035001e4410041911076107401042c2184100032003400b400122164a0b5454550310040d9004c240c2e4014151b8540418800080d85103404d00000058030f05903400b800340b59041120103584900b45800c1040c0e420303814044c102c0001e002184064006802d0700b01541c40d0700610820308a02d01c500528400600e40110340000c941c6400212540104000d89036124001c3d0400451028101e030054040d101003038030030040000c00c10362007800f90003500852012800c0701194440e0402d591029050140c0c595480e2801c009040d4103201503d03021000710702a00109601c074000031801c0c0902030024902c800c002500e007044038010170441c0d00426000442c2c04601d202410310070010403084a8060128401c00001002d42c0351600c890340c070070201140781d4104d188010080c46171a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 367016474 1250 367015224 367015241
    0x3110105061c122a0b10050303030a0b120304090e01060e06090f0402010c02040518071a040608090c120703170a05040b0a0309140c011d031c020109060c08180619 71
    0xf88000540c004c83c50401d0210785480f201c24050301c0d03104100031890124500400206109841c2c0d1040d1070078840ca540c080200c0350044101e000101d0380b80b00000c0041c141c81e00c0640b04425074400094001600310840c0c00035800b80014600070003d45503101d0400c0c41c2c02c1011074400794045039000c00181590b600bc0e1460340c000d030040c034060940c401c01d80c0c00300381110702c155807a4002c0101100740503601d41c030410844010f40400c90541000340c40c2c0450441030340c065405400300b4488a50002105954100070780084840e0003006aa0300450145556444140c1d0740400e0751701200d03039a07600e00e030b00341c04c801101c003840d103180d503a03a141500d40901001b486c5c100e00d41c54401c00da206c10200e00424020002d6441a856540280000c00703107040001d081d00002d40c2e41140340d03001480c5000c085542c0800d480291a098400c2461000c1c01000d08034011300d8040001404286020402c40032158030800c0c41e40304010030341064070001d085203a02d07036507168201c6e13000c41004403001c5580c41c0c1009a0304000b10303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 367017724 1250 367016474 367016477
    0x6070305250f080403051009020901090e030c0a0602041a090f100302070507030506270601060804140706030b010e03010506130b0d0212032206050a0c170703110105061c12 75
    0x18030072200d030340d21003000c0d40c00402621000d2021406000f485814030400e021009206800c200618583c0e0120304820814070650008a80d202c2e050310300e0f00c1007841214040d103040010341b0f003550b140c0d15003240250068002c13409140d0003050741f400c641c0302d418100c0f82d211000400e0348800000903410000042d001240740c10426400780300010004008008120107980b16034080c09062905859005104070b80c15071000c0550350b4040390b20310028012820a055880c2440d100c03c0c3c41d522428071103500e001c140300d01c46041c440d4130340004030f20b541580030f003c201174240e0380d25900c40c600380201826920190b075103542c07156490402c1c446c000d0790780e0301441c4c3c25000034106d811152080d40014143c2030241108a203230b17802c0040c0c1048801500d6466030115003420504020780f5040200040c614011040c0364824440701c941c20105100c000c0241c02000885101c0e82940c4581c103160007080d0700c0050450400c03540c00d020126105281a04c1014040c0302d50001820541c8155211719882e00303802c807884070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 367018974 1250 367017724 367017787
    0x1211032205030a060e06060d020f04090203010b06070606050a0b0c0d031a03030f070b0a11030708090304030c080a03030507020d021011090307120b07030b010806010518101d06070305 80
    0x41c0c6501c0030300103601d0715406000c000a40c0e80002e9602c0d814800014074551064500c03a00e00c50050342c85014500e49080300751800a21407120b071022a0040010005096100c00d010480703030100542030b001101684d10588055036100d40e107844c01e003268020715034034901a0b00075a41c6c001010384681d120701e41039000314035441f00c14500c801c08a801c60340004503c02d14003e0010b07814080c80741c241101604a0300303120003008400d400b010020500d0101402c81e00400c13444001240c0908020420764010b1900005000e00362543c4072441540c4000000c01100800d081c50000b0703000c640085506081145540c01138000700a00174480f200504d0240944914a08213118504294400b00301700d03000760181e03000f841210001820450b4605000402d0241013508010545083e41d0b8040742a5810140030300f003190b154000f00d85840c0c88400a00c07030450f08005526101c001640c2d001c044285188900750801d4036034140001030040510034900c000e00402d204103c040c5045d04c000c91002007848030b0001c2d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 367020224 1250 367018974 367018979
    0x3010b06030610090b0a18050f061c2304021f3507032705070e060d0b191508030306060703110703080409230a05070201020c150412110322 61
    0x1042c0680084d40146c002411034481c4005540e02500d421010f84001c850030580c901d00704000441d68481c5107192624030500c1508180401030b5500b0140803c00c007030401d00102c42203a04003016180d000c54060b4440c64054400c800340d003408071314071000d2030000e039642440740c100404c2d500c1d01c910804800b040b0901b00201c1c030028020f03800e881c0900a5010355030103d0940301020581e1a51408490000740805a0103030301d50008000080980450b0503885c1d10075500e944d241d0008032903910030480a001034000204100c00e405502500c40051900b2842c204000c0225000b03c001c035480c00e01503040f8036841000030540c0c2e840d001010700a0310b4071a15150101c06024442e80b030031f00b070b6260700842c1c1c90f5002190a000c040440d00891100700c82100e01011800940c4041050b0554082c220070440c55880c0c02062442d072007901251002c80140c0102c07a0303241c1c22201c00f021180000c40701591485c4c000c06d10207006604c51801c0074002500c440007942072801e40c106616601e85040c030501da403a800c60500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 367021474 1250 367020224 367020239
    0x708060306070305190e0d090605040e01180603050a0c0f1403030403080f191806081303180902070c050307080d0203030f0601090e040311070602060106050f0f0d2903010b0603061009 80
    0x31b202c2c11206400190010412051028212500030703000503040c800140418401401c440b410b080c11540000f410f506001810807145c0018102c47d00302038524051044960144842007201e83c0c100d40c098040c02902ea6a58405203a42048804016a2640040000b040466059070142551424035041c0d00c0c0703000b80c4940e41c1844401642ca80002290300c1680ca502c0000140007560000e02290038a030400d8608140080904440904020709000141110340b05070090b601401000d050760b003030215560b030120704100160300080d1068601c20300c80c0020106102c4004116030901414640042d03045803604246c151055400921482c10451844c00011f84440d00e030800c180141d001361206030603291030201c000d050050a4200200759803040004020b0340398070000312202c030203030001c03290344a15581942556a00c51360201c0c4141500340014494940814000d00c0c02807144100c194a5507086203083c1426a8100748003254081000c1c0009080303410101c043d5044d076025450800811500d5015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 367022724 1250 367021474 367021481
    0x305071703090615100c021011030f090a0f0b0f030414010203010905040b060d0c0504020705100e030c101a31060602070f0b0304030516121205070806030607030519 72
    0x1ea0050030f9016070b0600408000b00820001840380944800907480c3c00d004000e00f0130712210a009014204001007802e65511511103058a040110150390f5204050b41c0c0040450704112941171159007000c5000980880c8610807000b11100000c1890808051142020003178100510642d07940481d6052200c00100a20040d800780440d0000021107040c142411841c2c040014005130044121181047c0802c119054030310444004403400b6941d0311071441c0c45e50802c0f070b540f00d0140c140c60400010404a400120140600c0308403071085840b1125040c40c4201690240340da20030010218444501540c10001e03d41e8820081003808800c0c0c0b055800605810540c0701d005030201035507121002d02909905116403401404a0b002c40e02b04103040c0000c0204621010b0001014000005000001200c0b4805034114854100c0c0003c4181244c0c15009480030316004801c4240500e450005121036016410690152030050001d00681d80c8182058004004c060502d84100300c42034031f66000d4581030300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 367023974 1250 367022724 367022731
    0x40902061213060b06390a0b070f0929040b0304110a06031a0d0204060b040602100b0607030c0f02012a0c0515070b10090f0b090114010207030305071703 67
    0x20306507041600c3e040c180210b0300450520b92154600300000c00c604424125404082c5a0720074900c0106281c142c1e024245102e108425040d42c001c02610a05101f0300d05d802d40e20414440e1100c50041f54440710480e041d500078010020003c19410060300c1c00c0d140c21509120055000b40b6944c0740075216004180190802c41e0101d4004046100c8400e190800c00401c80c020001c40c1000d108000304118441d41d41121300c40303214055420340ca041d00542d40d80707401c144020603403500565525902d03018002c1d102e03400e81a142034110309100b0104500d0030b20404554802e0341658030022094116500d40031024040e4006904000c080031050507552190b400700400715040020540070030031a8034000d594800f0a03440b0a20640c2ca040c1e10101211a0b44101c0b440b080e8851a842829545e0304054050074000360440c44006103081600c04040c006584083e4541c1c408480000150b030341e810550940883c84d07040301d40107821807141040068014005403601d607101e600c60402002c0d8140071301c6e0650304110f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 367025224 1250 367023974 367023991
    0x2104030b090f0f010e0a03080c04030618030315032a0f080c0108090a0b1b360a1a0c011b0806090a110306010c0201030f0c020d090b0c0c0409020612 65
    0x10702c60344554000030840320800c07182c2e00c1c00a004a4400e545503944540600c00003406022000000510b180c1d024012a4059035101c10f08212040300c107980040e1510460404501080c68458412000600c252840041f00e0340480140005004280800346002c1c0301c80d0f0460040041e40e40224800d4120b449050181a0040041c07801d042c50750300051030100098904001a000550280089200c180205610035030140b0b4a01c464400309454200764031a40a64a000f00350100650318030890310f07003040c64011207060b82080d10034991001c11003100ca8a2052490200c61032950764000e40c1000054144a1201c0000046082c40c0558900c1e07201c075415440320004051908001072843c0450302c0f01e401039445503041080c041c1c1210038549600c000b8154506100c02a66110116880780d04005001035032000107221040001c030740079659401440d040030104040010100c3e030140003009441c0c00d000c91a0081c08100085001c2c0300003001c468406030b82004081140301940c841c0c8802003402001e10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 367026474 1250 367025224 367025233
    0x60303051306050c12070f1e111807030b040b090a0507092108090f13050610020a03120504021801030c0609140904020f01050c0d0201050103060516022104030b09 71
    0x1012010092541c1005060140c1402454100d820004c3c0300d08000345c02c1c004044c0d8800071400c289540e50b800040003007802d5200b00c03800c0b4156082c1c82d07580c0307205c038845c0c030400000c13185000c00c0029880b0302640005a4075680c3d8001651b041c0b00307030000003281d8009040080d14400c9040483d00c03800c000c83d55545001c1c1c484007441903c076813104400c0001c2c0b0f9115171500c030a100f09901e09518089028024211000c04940000340e655400344915080d0002014059181c3c00003000c40302400f001c4031030a120707051078144982c19600200d140f10906600d40c3e14003002c1010300c02600c000b0a40a482641c00c100740a0300354a041c3c8150002c14042c501030140c07910307000c0c03402000074903804003a0400c180000300c50071196825180c2460b460303085903040740c0c00000495030000403929402a08072114441c4035006054043d01d40642c055030580e801040f05209540e184558541c0030b620b0381c208074006910031958028445180703060384004c070816040b05450a9601d4940b04070110003a5110032050b0030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 367027724 1250 367026474 367026487
    0x70c060f090f110d0206030c0307120504050c011101060524070f03050c07140d030815060f09040f061a07140607090810053601020a0e090f0906061e0406030305 70
    0x10020040703c001082100c00303070a061125030105040f408068030039800759102101041449008640d14414604c05e01c0c000c00987c6400d0524660768540b02010701d021514100e0504200b10f018081c4009488000c0c2680c004441c1d118a001e040b4cc941d00d45036885940240030310000101c51405521250f0300a60f28035880c0d101ca88605810a5000d520a030a0107030700c0520440c86484803031411061076050b0800f020b090303482c50710410703800d03240702200e55102c100000d001a2303144d041d00c05008185010b0381c0400c4400e294805007021104d1500465217582e81d0700d41c583d01048020401803100340e100d01d00441c5a02160031006191410070b0340c503400464603070388047c0b0031043c00304880b100c516088807051000741081d03d504034440c04262060310b135502440a501c16200b8288086203000207119008654031603510000401d07000e22140800e204102d100003145400250700d11035405505058007424054440c841000804452202640c002c18a42105004030359501e100d8400118025100c483c0d4440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 367028974 1250 367027724 367027733
    0x50606090f030f1e0d020f0c0d11090703020a120203010807050906130f0b0f0d020109090c110a0506061c0c09180204090f050c01050403030c1b0806010f05030115060206070c060f090f 80
    0x60170a40380046521068100151100019a401000c40151000c2c440c1603101d0405203c0030344850f120702d410035014018001203580c164010680c10215589005890541c4090a03043e4803081c031520b0b9580e401080203001c01d1034544101c6802c20b00080003a00c000032001510400d8520116403800500c0e5500100344560400601f007012040e0211901030217140c0c85da00191080d0520b00035051201da03143c0080311102c3c003039468101111800c42c2155804405464151396a01d001c48020b40a0720b00ba40022001c440e1401e0f405401661160305030203040c0c2401c90785402403224200c007003000403030ba01b42240075890b00d10a0710092405501c090780c076100b00d41030107460401240000c50401004101c1000420b40c04900310000035400b801e500c0d0707185d001c0d61005035140e80c0780d0004030982c020040001844100d030018001122001d030004d0000286412112545000912584015800140014a0703562080c5d41441c540c51061100043c2d02200c3c6c0361610849540d4001100c110307148011103001d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 367030224 1250 367028974 367028983
    0x12011404050102070b07030b132c0c040615120b060f0c01051501210f02130f06020705010203071208190e0a020415060207051003021e09011101050606090f030f1e 71
    0x6c81242028040440f20001082921410786010b5a080c0d40d26183c03504000e644480031000c10a071606442460750120090303507110b400903404184594644140020008100e4541e6101c1134466200c12004a40301d03ca260040d00c041c0d200144c0c4900100110100021050058807421810100019041c80d0040d8942580c000c10301c005418070031880380c414154004102e00c00b010014044001c110f4408005800d4003030301500c840002c02d100040b10100d110b007903e10300e502c2240e20607400c80741d1140d46d500059840303205250010303003035805680c0c1c241207440c0101c010581007041140d40e1914100c00f48210421a030006071030000540113850800154909401018461140c0069642c005440e0840296450b0f44031310800303000d08c3c10f112104041d03500235415030341031100340841013144032402c0e000075035140e100504035808104401035003003a42c00148907040c4a0003000c0c00881c41c2103499401c000b4607054810010350325102e004001d00c00c105d0300f4041016110031685010f0071240f130308443c0d907007032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 367031474 1250 367030224 367030231
    0x109050a14100e0705060c07030c0b0901080a0902011b020105270a05031c3c031107020f0f2b0c0e040b06150d020307120c020a1112011404050102070b 66
    0x2c0790501c064441030040100d803200c00c864007100c0c12a510324400c9049400e00601e64006042000060030001d503a4015030002d002419003681c80000d00d0340c604245204070360907502c1c06070014a1202c4242c0c1200d02603415400c0043c014140b650500302b01c094012604881300b2440c80024540c100320784c80c1402c0c003c00190262408801504d807004280040c210040c07600013a550400800724500514070054140c0700c640b208582407041102020742907621403400783c2070304850002c1c0c03070088001001a018400c0c0c80c3e08030f2b030040803049105030a0017080401034440b1004c41e40001c808a9403410480701021112803036010816954070308031035040234040e208003588017025045000c0304000000340022250b5a009070225055202401955860403543c0111455034034124400070901050715003112103810480b0300102c00780202012110b089803905500580201a00d0150710441283e14101600d400005040c3c000000d09454403250300c15024010360301a500d41c0d500107410000d0018400000c0d60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 367032724 1250 367031474 367031503
    0xc0301060f0e04150902060703030516081510120f060513020f030711070306020c060f0612030708090d05120a02150c070f110907180504060e0f07020109050a14 70
    0x24280340c6440c00002e80700041008241d1600c08000940b0228240e00c58019281c0281901d81c035210b040c030b1b010f4000c04069807a13400340402d0503090200746103d00c1600f44688454030460580f0900381c070a1042031030400c0c502c00144862110041180d85491092901901c0000d10100d1400d03c2c6c070091001c0c8089490f80344103600d004104942e190b15103a070460741c021000e450041111041140b0850030030b80b003600000c1c04580005108035946200050403400b8500c08159000503880d4001000b42100b005444d2680b03540060181c00302150309400034010301c0310094061a0705012941e01d0724100294005416000d160100e1840390b4154100400d6000c01020310540d50329007010b4044d100c1038018a02c008180580e03119402080102c00d904162040b00302501400c1c040c24000e0000d80040f0b40714a0700c0ca850004d040000915141a0180038110740c581c07024005075882d080010341c05510014940c509541d02d41a654000540401802c80ca00c0d000c0c0c20741c0c0708401382203103019050a9143c0c25081c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 367033974 1250 367032724 367032749
    0x110a12020a0c12020307060f0605090601320408070b040627120305120a0605040b0301020f0f0310080604030833011d060313020a0608130f0602090607050c030106 71
    0x325076035004100803a40c81e0704852812040129210201e245116818008285508054141007001c18580109056403001c84200c15240d403040c2c01103070ec000d00d84000c0e01f01696071400700240040b201c00c1003e90a102c190b00285410340380c00b4402d1074140c0591114101100001d030400c00103500280340070510f0900344d44054004000716182d022020640960301003108850509401c1500507000c4aa0603030005c004440c503440c01031100d20080040b44211400765041502c080c410f8507043c8225074030015000941418428000c04851164000030700c40d0007610102540800c5000d01041b4052140c0d1103031b40c1d11100e9140a062140000b2011542a05841c2d901c0d01490307c4074090320407000001a086c80d103400c0c0040400d180641c000505903c2030b421200c0041803100341d000c20100064040c0c000d071503502d8516503403001114200c0e03040340c2c0d070b1601b00417000d4003c0c000340f48412580300c0140160405030801a296001601681c0180800c85256000100104035414280074900c000c01d8007000d20b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 367035224 1250 367033974 367033987
    0xf0f1b0f090901120c030303050a0f230c0708031f080307120e0603010509130602190801080f03090108010b070314040e0604051006120f14090604060609060303050405060903070504110a1202 83
    0x44046175400001d080c9905d450000d003503000c0b698001d1541e6103c100082c441888a44600d595004107103030100c215089060000342403000e034804560840d070f84000d107c0c0c615540c11074210100b60064100200a2400c0980091000e000304040c1c82c4243c001c55118407640d10121000d0003410410b0703140c2d070240c0000c0c001000240d4501c403405a0028028100c81ca40a0040c64141c3c000d100300c2c403521608030044042400002c1e409540c081c161041c52088503510401c2802442e6a070041120707950008001000610850f810007000d001264403d0a0084480c00391000c0e542980d0042e80000b060441207500704015803904d8040e00c6d0300130400d0718001300c249083ca0350041007036a840b006440c00369150580800e4034032641e4080300e03400301650b8843d81241040700358961901d1050f032342a990242049800302d1030300d08a1041030102d075455241d0a00d001cac9400140489a00101c0c100780d810301680d04000f605446900031b5289050f024040300d50344a203111405001c4001041c642c648480c814802c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 367036474 1250 367035224 367035233
    0x1140f01081b060a0309050601060c110303070c0b0a020106090606111606080a0b0604050d05031c05070203070303050a18140d1b06020c0304080d0503041103060f0f1b0f09090112 78
    0x14042502c0381a1681640c80040c403000b41e0180080c10b1000f0554810100001413903a4001c241404a40c850b060340080601c07802d003015a03a0180000144c01c6c100c0c40300040001c0d5190310f000b40303058041030001003441079807503607180c04403034640e80484089200c20141118070081030080c540c40400040d04800c40c2030400d040100311540091007101c00e40e903111003041e283c0e901c17002a60024440202020081c4109150150f280e1300544940044105e0340420860802854007410f881240d80e0382c01182480f03100c0d141100a010050301c0c4441c003a6a88030030b8041e00c10107030398000c07040c1c0c000c000e4030800701040801e0a15100304200104200700343d4000907049000000c00b09601d850b00101c002d600c0701248040141103106a502031b40440c812512161480c0780c000c006107104900803450809444040380606841c0d51044400b402c4480030301c1c00050300003542601c2190031020b080403103100340e1480b81d80000306a006801d0a00e01e8080450788102d41d240c0a0102805449081d1f410408213109589 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 367037724 1250 367036474 367036513
    0xa0f060c14131412030301120c080f0c0405190509060105190506040b070335010906050303070f03140a17070e06070f0f1e0203060901050709140f0301140f0108 70
    0x75518070101039002d80f0b05181d0b645080f011454011100b5a03560b944e4a40c1d80304803111258204994004030780c035000944c0c61010405022003820f8401800035081d4480800c0010b180c020004400480340348250304d0082c0c03041c400d00b48914071a000a0180754101804c03c80c2908030b404495034100d444034030501498640d4416241150900ca40340c0b515926185400d403184102c0865240032019038184080984001d03000900700d0039207080e07052450b662a00360410550f002401860f030180d004111060000b00c0c8002c00031240c1b0300030710705078042c0450780c2c180c0f00b100d030f03c0003541000103101f1442010820500691300364102213903042881082041d0408a071003401103000c0542150080038218050107502c00655403501e900a00b018480400801000700394581c650041e4080c3c800c0d08005540207405120b42c0780a81081d858001c4400d20b00030b0141c4032540e9103071a0700e40105101c0b540c84200c1e2001d00403c110400f03090408005842c1c035850b024401070050380440c2c80c0d68408103405484280850 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 367038974 1250 367037724 367037729
    0xf0609070b0304050a0506070903060f0b06030c070203010b0402030721091a071404090905101401050d020a08030d05220b01170f0f21070206090405090a0f060c1413 72
    0x401c0c16499540301d041c842c1c1041c0201d80d000d49140a901c0400c1071440c1c2c000c80d54411303203120352420448802e14417001411122012011500200304101003581c80c5140230140000d148000c001051520041e0081000c0e40c2040e0707a81d001003051080803c03035109800c01c1c03440c00c4800a5000300300031007685c1c0b0f410748035406d41c24414007410700c5440402c45243c8030760341c2500074060b851001903980360380e03040720801850304d038405a400d8000e007003001c1c29403800750241c1070380c1301c110108001543c0d00308810000800d00902c2c040b68045400f500000e09000c06001800006200756000505858039009440c829203902600d8446071208900b000001a03004030900c2c152584510030102d030041005005203411840040c281242c458608000003030b42000500c240900109420041580880c0c1c021210900400e00029032001043c0845c03817460519070300941c1d00542400071614140341b40d0311804032002d280182694000c1d02c444a001c0c03016000103000a004480ca1100c506d841d8a88650504c58821170 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 367040224 1250 367038974 367038989
    0xb030f0a06090201120c0f090e06090604023105030115120308040c170a03030f020a02070317070f05070302031b01360609050907090509070e061603110f060907 70
    0x42c000c18095900ca0350062001490740c200c00c0108191078080034040c6014a01c8650025804210110795000501140d5000301805051800540c0300e080401010b90000f46041034403c4106100c40c1100b0707040d1100307901c51340b651001c40d900c0d1401d010605007524420380340c0c0070801400c888208482690f5007030306200f40d90540b900c1c01c0c0d076441e03500d4a04545602a4001d0614a14602c990440080007151921103540300751000c0240188040c0308105a010352021100542c100c0c1c0380c1000407030300b2408e0700c08182c44144500703490005030390345e06044d0150304c000540701544017030001c1c01142000c00c480103a8400f080701c0ca050711003082000801109041d007051b82ca050700307480d403000740d02c18500d01281d16a450354440d200c15521003100a2500085208030740c8075008a0000c0350b8058015014103055600140189100c0d030343d000710030781d4190a40c80308030382c00800c20428030301c401010307040014030b5510994402201c0c0714409005480d0021a0030042c80c2c40c2c11090900ac40d02c2c2c000a800c10403968031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 367041474 1250 367040224 367040231
    0x1404020705060f192405040b1c0809030f03040306060801060b0301050d050708010c0201020a030b182a1809371103040309080601060507080406030b2206090b030f0a06 73
    0x980000900a190041000405505114048021440011001c0440100e1076510568540d07910200408c0d1031101c2045074000140341c14240c400300a044401c00080e010b428200c1c6031641d50804249441d1070405420711303c1e00085010302c208240c601801c4018032940000f401003505040407c88a0b10040c071889200d9031b44c6801072010040305001a03c0100034042c000c214209040078040d0227540488510760000c1e00d0b0584a091502c0c1484d40142c0c8160070030581e40f45940e80342000e14010343e807042200981c50b54000d001c2024907841d0018620b1001f000e02c802e02c0000c2c004184042458081c100350b100c01c161490552403200e680582e400c14100468a044155050304442e8000b07181c0c0744180042c03417000208102c2415000074000d011100c004c000c0364866030342c070b03281294540902c1d1002005440100000c101d031a100e41c00c80030360014001c2c000d00e11403a01503140c640301c0b40302000c504400c9403610340030004218103101d40c1140d1003069003c0c204406104bc1a00d44030884190004d022964 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 367042724 1250 367041474 367041481
    0x510050c16060503090f0109150b0a03050304030804151b02130603060e070f0b0a0215041a0703051603140a051003020904050f16080d082e1404020705060f 68
    0x804229009011840342407840c0407079241c6200400310351049845101038400d04000c00214541482001030140e04030000042c00d05a040c1014086c220708001294015056103000c004118180002c00003140708a0880d41e696151440401c807031040d2095a00030300025900107201c004121200107181903040b1183c00200e0300064203440101a0b94002814003464600c0c42d01840700006801001c1d14440e01c14034004a40d03070004800f49101742d00d20080160006081034a41041d0081d04540145c4540070041d0300c4004460804502d0104541c00c4001036141c5090001007001f4400064100312103290078400c034900389117402480700c001740c0341c04100b41d910400034060541900e180005143c1c0185810700c2400d050424540d6140616000802c90140c2c00e00c0100c202683c500c07450480700200054004922a4403041d50124001020f003041c0d110500302d00002c1508100d8180312102020460703c0c019400c00c0d0100b40c4001c00303510210702440c810441c00000c41c000140c0d40342e2000194280096555 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 367043974 1250 367042724 367042747
    0x60d08040b070f0c050402031015022424100e060d0c0f02060606030103111c12030e0c04200f09150a080a05011a16020a06050a090f051005 61
    0x4034540c0250302240c0d010909108020680c41d050340c1c0140540381a51660f0b407518100302c228403064a04040501180404110028107201c52801080c00303401030f01e60165500c0c0808042058010b9100e0004504400b044516aa04000700d0304d82d41c0d80c031000390000c808000103e21140844610030b4240310480107a44c09603907403482240d500718042d000900c402034000c440504a16880e01d840e0002d4015040041c045041c890b003640c2c102c0c1e0b001114401002d800000748169048402a20288400200141070224039a41c2c441c10070340d07909035030007d90b04080f45c01e00d42c1801d240c4a0960710850901c00d02040a502c000c0ba00c015016404040558400c11101e0001c01441490041e54001c3d07924070490010149104c0509010521501c5000c07481c1d1b0740e0b184e10b00884a09000300000d0215511401c00405007800c06030860050f40c22031001c2000054000a0001071158008400220002403481d100d940c0804c8c3c05000700b28030042803141904041c0002d815001c01201c02c0c08010011604c0301c1e105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 367045224 1250 367043974 367043977
    0x150c020607121a181e04020d030e04022b0b0102060c03070e0a17030409060801020c06010e0705090301050408181906050904060b03160f0207080a0609020a08060a0f06050f030303060d08 81
    0x36000503c4e15000e03071840000c090852108a403004080d240d001460691080b000e0800340c40345900a020b8040304680f66402d80e4141c4511a13040d400c1a070034801e460321240541c0301c108100002d4103e800f0103280b403013440410b40701560b5400381150420b40500c001901101c0c1640e8100315507080904200681201290034502c6990000002c50244103448858110110042081c3c420384503051054a848002080c2030b0f100d9071038071480b564089001001010755101c422a003100803843c00754680140c120020b420b4070707021b84065800000000c2e550b8101d000c4580f070f140d144d5409498075100c0d04030306840280d4156003803081c1d20071b210340020207000a5441d03a11850180070240c4109449090018811110001481d03510003c902e01d11204041c0340d00001c0c20000700d402d21401400c501031550340d03180c080d001c040c82c100e80100c9040c0e00071803410000d10107944150300101c8000341ca424400000c0c401d803007035580103900800c10040d0b06140d60720003100f100d50180040d0340c044400e1b801403421841c41e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 367046474 1250 367045224 367045271
    0x1b050909060d1a16050403051c03021b0c1009081009150c0e190f0603020d020909090d120b0603060105031003050f031201080105010b072004050103150c02060712 71
    0xaa031802c050614400e0f88901858000c1e8450354256910504c0e503032040c0c0c0d01d4400c60102410b07903405a24040101c02081d81c20f40000c400918016017404070521600070000416807401300c054128280544007410042c0c60b0400003000d6191088109107808640c1e41c440c1020a0440d03030864841c45000c0500c402029503801255503100108840d0102c04002802040203000c0300344601c034440045040d00c103050b24080d00391160b41480b40341c40740c80c00000740c0c000d42c8540700d43d809041c1c00703200c031412540e203800c002480b440c0d034200030b001e032844800c80c02090303040442c0705480c0c1545003044104003071b10348000b501e03030014003801d1546d17a80d1150b20203140c070810503034002070003031099144d00c00c603030440030010f001200511800f000d81640c80b80c9526090700c009000c3e9011001092007000b01240407094014090041d100140000d00c062101203010f845003600160744030080c000b003244c1d5121551180c0c2643e014544040c103001d062226000b4004028031100f405034949078440c40308144010300b0301e00311 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 367047724 1250 367046474 367046483
    0x1e0705070308070b010302100e0a050f1309110a0b0a0e0609130e0120120c0307110d030504020f030d170c04051c061b0203030a0c120504050109061b050909060d 70
    0x103c0d0242840c00545004007400100d008146251080d00e102d801000401c03482c400003403c1e010030608202c107003d10030305003505669000c080c03854500c50683d024410100c100b8054a02a0007020b407010070701c00d5a15850340a0a43c4203407c01c140000f0680c07110250f00e42420444400c2c2d40d030720f410310001d0b82e14070841c0710030b071001440c7c00c00c0b05074120015409148604400b107240c210410300103404980d903000d50382c4072081041c45640000e0220700070304015544011141405448a00f400c1d201910b040b00000c0018082680c92061105618080316413034241d4108030300400f2005030b01c42c00107000400500442c40b51110b6440860701d010089400c0d00c0207002d004c1d00100c0045910050003c82602501017038031018580101d0245040300c1c1d403d07078110b15040b40c00851131900c0d0148001c00501c1c4003113a1800300006502001e2421140d4002d841c0654090800420440e265042000445065102d10008196150240340443d42c10000344c03085d4000446482271187c0e100c0000c90700081449030000d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 367048974 1250 367047724 367047727
    0x613061a180105010e011412040f0807050703210e0d050102040b120a0b04022802100c08091b030c0f03010b0d08031602070e0604020a0201060305030a0306080c061e0705070308 77
    0x41c003000d20824090403a0710036a24403911050000043da0136482112291451542c20081c2c280d07c0100320082580082c031a03d1506001e50710707502c40701403d42006c10121182d820191041051080c1c5441c0c1c01c40000200d5201c02840400103005480300102020300c41c021006055140f0601c802903041e28010880d0385800b40c0d4a5052002810705000c04968400b101c40c0b03441502d01480c1070520903106049904074010b07010149503009d501d400c9200176030060861003503e0070310420741414000e140d41444152600c4408d41824940141410004a40c403055503142c00d860f4110f503a800074004019090a41d42c401d407400030500401c2c00b4102031540a60440c010f0300d4850108400c8400a41c411044e100c814454406207200c120f032074104602c01d00c0c0d0a642001c0c0441c505250650003800040b0250000103082c42e56503483c142540c00c00448031012aa0f03609007080001c00a00c15080841c20890300c81d49404466141c5424002500c003501c20108000724048041100400c211006944c02c4600306 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 367050224 1250 367048974 367048999
    0xa0e0315100e0c09030c090c0d06030312050601230903010f150305071a0406030b06070209010b09100809101d010f06090f0c08161715040e0613061a 65
    0x80080703240d40304019a1440c4280080c144002c89001d5440d24000240038007800034401c400c1080d0514054603060a0f03000803c07504d10090b0031440340c91f0095109031110011001030300d403010101e80d802840981030100c2e21503080d43d87e921880300c45101c001c8c40700426840700b1515010034010701c0c100e41e041030800c1c0380100007840e07040080024821684681d048030340e000d449015480d540788a044115113264801e000c00c6c0300e5103001c0d0b0032074800c0110291140d4180341182e0002981d0301c02c01e03400a00e800b032340090304a046c0d0810420b08070410b00305d410138600a0038415241b80c0d6910b15241c01c0c000641c5d98184109403041d880004182095407480280581030941d5070b0980280502d21803040500d1a11103000041c006a016140320108641c507118000d0359440d00c8803032506001c881301d0041101001c1152200070711341c407201d8003a0010880c1150681008001d01040360807108000b4441e80c0903800304180b060030180030143c3d00d54000c5000c100c80302c81041000000601c0008070340e05c0b40c00079808 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 367051474 1250 367050224 367050241
    0x302070c1d0618010905060d081c11070b040618020d0b072d14090a12021504031707030e0603041511090109270e06040302060106050f0a0e0315 63
    0xd00c0c02400e080e618920312511000104115846201c4502010b240e50400400005d10aa400b1943c051005010f02100c21200c2d03403422907992004c80c2c02244202195561841c40703800e88100780300c2c1840c1c01142c520302140d40e1600a0030400040c8018100b0b920358556551501400c084000019406480b00c080c440c00c900d0040300200c4204c07040000607091098407200ca04500200021054030311030780704400c00020004690084103210300380e91000080000074907a40328101c2480040c1444090220a1b80030391042004e801e1038100344010010b41400305002041c8401410310000e81500c0035244d441d05c4c54603040e5070120040030303581d501c1030000c070400043c0212441e043c00711900800007009917040c03100d036108040c05051813080c0011080c42d018007034500b2110007104001c0141e500c0d5100b098800d0003400c183e4414a00d00d18058002000f404105501004454003402850500078103003082030084546a004502c0c41604010031000d4850395a1420300c10303031403078403446251a549841c20421 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 367052724 1250 367051474 367051499
    0x1b050a08030d0b0901120f060912020c0a0b2b1514101707030c050c010609020a08070206060607060218121e0601050a0608071b03030c1407020d0308070302070c 70
    0x2078003001d0070300d410008140740813641e060581d0010409054841620b4450500f05c1c2000300c0220740d000e55414510011540c403000488843c1010f0340240001c0fa40d040c18040c0224807588484003840d030520821a2076040c0d0201d40561816880d4107401c007003a4210f41002500500c0190302030008526400b181e41441d5006030301d942d5a003070310b1240301440740302c0e811030342501150308044012001e00c001c120000d2094014803107651062070900e0400c034103980e82c5821901e20f50310030022107038001b40e50b001c0c0c281c014100f103521507118005032115107800f5000ca002442040c034010070555000503c40301d61403404101070082c26000d8840031800c00b0880c0c105607202c84032416000655001a038881ca024000910700c3c1c1603c00140202480c54a4110155082c00000c0d008c1000d00480c0c4e41c1190034000745d01c5004020600036900458240407500010b0300c09486000c45403590201004400007580328041008030050741440d2005040e9202c1204900034050304000900d040030320703c0001440c803100c60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 367053974 1250 367052724 367052737
    0x12170306060d092303030412050f040314060f072c130504030e0a080c010518010c0b0901060303091221050f0c010203010503010605060c070311031c02060f0703181b050a0803 76
    0x400004c003c802d40d0503640d40b80812103004082d00c694010400750248100c000d019400ba102e54440e04158482c0c2e07a444810a62216001c4145c4c0320204220f1030302d002d00660b5401c402c10307081000007180712415100c1aa5401859403402c54024210441d1b1390316003203a007119120641c082084241454a00206510341d140031162080245c803401084014011070703401c0f0540380c142c50382464601c001070240c0100c401c12449034180b0105802110100d80084140c610079560500000350035820340c6800785c440d0010b60486214020701c0029100090412900038000c940428442c00b9005801034080b1068802d4200008103808007068681b182d58054004e18141e5004900030301000b0b0b02c0300c040c42010300411006507000d60000d0710420219883d48040304841c2d201030191410034032100181c81c07c800d0b00c582241c0c016409441080700e0040c2c034a40180c0c001110b45001e006514100b01c00d8102c4105e40d40c00500501c02095031101618980010000145005001c803c2300c03695824446d03071a50001d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 367055224 1250 367053974 367054013
    0x80307210813330608010203090d0806030106050901270506280b040602011d01050606040b0a0e0607030c03110f1b012303010f120f030509010509030109140712170306060d09 76
    0x2c01003400901802a207101d6940c10b400ac0a0100307580d43c0440301010003a00c2c0759015541c5000204060f220a1402070282460401351401d54810030400e07580c0454891901c1c208510b80020302c01a651245c441c201100640e0b00d0021044a401a22815128035580559001c28001900040c81501034001d90049403201c048107a094132002c003081d080e500211b070111360042c002c20082c007602031040b002c3d11180e240ea260001d006000c03c4003040003075000c1002900800e850203104803c040e4031680607850000400007030500b540c0c0c059260b07a42d80003001c0590954070403440c214545648505060700c00c0d4503010060250000611502024035071003030042115440344400d020450f02400c02b1546c45403607124045e80040e02c42601c00300c50079044004164104502084440c495617424040c0e0490240201003100303035100b8455100c0d140a0040c1d00294005456845810210b0002e4481003640404151540d60b60342d246000100544100710480c40c0c2a0f10700204030301031010200e00f00480380c601 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 367056474 1250 367055224 367055231
    0x121503010608030c07031b090f090b07030c02060c0313230106060801030c050613091b030c0e0922080304110f0a180c090f08030721081333 61
    0x242e4009607124030410b0880907407944555010000908409183c82294014180d0004520b0301e07440c0090a41d214620030705c1000351515400d0082c0700c41e50004c0c540000c11400d040201c004c4504000e91901e41c020140100c0c260044005040702c0c404508002072260700440301c690080e080502e11410307221105102c0069882c100c40807540d81e00071600c4505a07504848454205e6180600704640c43c0e01021441114071078904001407130b00413a008120785c003044c51140684445800c0f1000301107591000c2c4040400445000610054131115106908a41c00b421024500c6141a0b0301c051003251111004003000b070004200020301003440b06030004880c00b01d4688807151111420031500e86030b6801a200000207042036641a03039120340c0311402c92901428450300c080c3e990314852040c01c2d00e40d80182d9054100082004c108030200e40d6004e0b051400a50100b98002404001444004002d00c18403082c145000100c003400001c0c40201031000130484015004c0c4c5076043c2e0008802c10146800c0e000909 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 367057724 1250 367056474 367056479
    0x30501050f0109060e181207060209040c02030a2c030609060403110a0b07031a130e10020c0a02060c030d02030a1a1806040906020909010308040e0c1204030c0201051215030106 77
    0x5a0150b2405c0742c03c070030b8410485484819020100031030b1003812900910549400c1503201c41d450010388403540c041e040058850400b4021300c0240c81d500151541150000c21180017190781220124800340101d040d803800c400300f0000a0103000943d1900170b07034940314240401885041c00985184518440c1c1d5840180c0c00d12040c0d1650359142c582002002501e018000981151003035000008080010078844084450700d404591803100520500502c240c8588030910b088404100381000302d0701d8003804502e4000b005540680340e090002009201c0c0c0c00009600c14240e008001f6501d0400300c2440456680c2000c1c0316420041201d103045045400119101c84801c5c602005221540c54007403081040580d580e4040100030840440c040341c107564207004501054444113101d034040d5208080490b40d40e8209884204000401040a60540c200700320010740d8802150255400c5545410070810380181440181c81c0e902884c0c01940346c905000b410062603c0102490b01c000304000c1d4000c000300364 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 367058974 1250 367057724 367057739
    0x9150b0403030c06230703020307031a0a05151b0307021201021201290408160b0a020705040b010c0f0c140d0c120203030423041a0d0b04020402090406030501050f01 72
    0x341c0c4405404641e50410b00808626250408500b00368810448440f5403603900c1c2800045c00240c03000c00010b6404010051001c0e0144034442d0031180b400c0f5580d60107859807000500105050082c1400781c0072544a130b008910b00d1809840400300302000899034620b4210b800350b526004840180d124556000302030031904418800c90380341c84200d5955255507801c00c030214008800c00400c1d00388024a03010000c82d01c51500014201414245c0041c6c0701a5a02003081c5103485902d41081c94110400c015400c0001d8001034014201d942c00e94000c2060079000c0016106100e0001c0d0181911803041801c0c1c04204849103c14182d8003981c1020f03102e485c4e0340003823001995030715000400311981c0100c1445103401502d00b4001140c03004049924050711115100c0c14080c00051622084440d41814500c034903140c0241c40740400d603070050201030207800700041d60380d2950344006008102010040350654855070111800c1100161043c03001d00d5407031030002d0080c00300311500f01e00b6548020000c03803000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 367060224 1250 367058974 367058977
    0x30a14130b161e02060a05010608011d10050a08010b1503060a050d061107030809120a09060302070302012009040f050402061903180b011e06081b0c030409150b 70
    0x1680107100442142d8510b012010744820042d061003e221214034080303201803914001c010211038a90103418241800146c030740503242c060300810180702c0508011300004088008014041d031802081c80304688412241c0d40021245401c440d0f01b15611541c007054488054204c5540c43c0700c15140c513040440703d56403c01c66404141c072003d0b845900041d0800c801c0c41d050395440040c5001d100d00141c903404150815800e40e1012208a010540d04020010508010301000414035910b03246246059a0070600900e000014003807041455808501441814803d60050301b40c116051100f00481030890b005520540040000070310480c28074100d00c03200a51400b916018560280c11a07050200911740e039140990000913180800d6500c146000d8443c50441380380c04058062980d81c079640d4105013600040701c81100e40028108c030f109000b000542d83c8424010340c40460081c0d0110500940c0c0140946441021108e240620010401190480140d8010668802c42420004806a41e9012452603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 367061474 1250 367060224 367060261
    0x150f020d0e0f010e06071208090c06030105011b1401020301050f010302071a0414010c0504030b070e100516080c0607020706020706020601030b0c0c03070311061f03020411040b030a14 80
    0x10441814003a480c1082d0362800741c1e5000504000c9446460000410b10a400405040d01c070f050080300b115001c80d8100c00b006406c91000006006010084000300380c0500c0180714460411041c0f59462024000422420307001c90360008040c181c0c03015000025010b03410070301910303200d034440c2c0c20111807640c00707842140e00842d44035400000e881c59141240c601e03180020400d80300420524140c6881003805e02c6441c0180505803201034941d8210f041c11802190b00500d15003d0040701d800309200c558945410b20194410b5141c4103680d080c1d0031600d80ca200d0301059004001200c0825403520f04000800c920f4450001c0d40d08551405a1b40e0390120399640c0740d4850382e00980c00640060000ca1503201410346d00c103070603180c494509410442803a1031503011041c2600020348070341c0da5042c0b1803c180076a80d0014005d005140260a40e440c25086962441c4070081c45907039038580c00c000401d0f41e681620010304a0b0400c050310307441d2402118010f48000309000041c11180d40c0020340110108056599 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 367062724 1250 367061474 367061477
    0x7051b011d0d09090f0e070602060709090e06040f150c08041a010e0705070309180b040b300f0d021e010519020901180b040302150306030c0d1b150f020d 67
    0x260300f440c1070800402403401091582d9411b8558600c0398000d00200940801814103070700a0440f4905154000d00c1821241c00080003035044c074441d245140e500281c40e40d003042e08050034480305082441c20741c2000400e5800401100c3c204080c00317003042d8019680620460007581c1c02c6289440e00d613504a8001024000d10890044100115610510940103001f109202e424001c01003500d66040c1c080045500c900a04900d4032104501540d04050003002c80b04502920a144581c1c0004182d505a40007641031622030386014a1001c0840802c21010149111010a80f0004d46101034025140c01c0005020a624003041c881801c05060501c01d1038440c8001e071a407109400605229a030195102e0f0341441c5c108440a0180035503075004420101c0100111070015584502c2c500c10f1188a901340702e4017403182203041c0204901e907180420070003800d107070859000b01d052010345031140102c02c8185c0090202e00c084a40898121940c2101409401a035280e0803e000f15405003240e588441c402040e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 367063974 1250 367062724 367062737
    0x3051b06071b081501090b0a0f060c0201090504020703080603060c07020a0512010e010c180b0301050303120c0409060603050711010917030705092701050d0b0f07051b011d0d 76
    0x7800309101080c94a050800074000c0c0745580da80707030b10b82841c1411880320810f0212105004100c454200e2049074410700c0c05950780c1c0c4e070252074943c4a040e550044d10a00080c02203a200080440e84a05116000b41c40d00600442d250000307400c005040c00000c44003e8003070b204a5010a0b10440c400c800c0d980c0142c1e008081e0114a410301c400e0040c07218241e0424065592100f030700c850f04000030f0103070f501c03000107035500c070031140548400303820b0110f40562100440d0141080148199140070044883e994901001020035440e88100f0600c00d128603032001802d1441d004010a42d40d03815048240240398558a010b04282c00b014158200d07040014020b00d03070001200710f04208840b002c003445c1d2043e9a0700b441403c00502902160b0181850701c07658000d90909161100d40c6100460100c0c0540802e40d80d8110000e290366540b00c00000140404450342007940004032818815000c407031201c151801d240e0700507411002154040d01c001400c00d000b1400008804031074400014051241c245030350f8550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 367065224 1250 367063974 367063987
    0x207080a03050c071113270b010b071a0402030f0303011d01050916080603010b0a030b0103060606050408030406140910080612010b15030912070c090f0b0607060f1d01020403051b06 79
    0x81504e40030906d07a0201d10b0b0721004080804015503211a07c000403856460710717580c0e03940c9007154035510140c2011521805c01c0c0300e2200810a80780a032144065444080e408540f11400003078a03003651424806c519100010011403035090b1021420448440441c22240590321402040099001202c3c0c40c00041140c005040400c3e00c40d4131041c0d005400a00009020b1552001140d40031002e03800c25510030850700700400420034913106410050084e0314150342854200300820ba1a07200341d11a20082110030f1036144c0c0380002d0f6000319503102c0d034001e040303001310954554007030300c072030000c076420351146422202c0d1907020403042c0a040c441c50300050102d000b1079420001002c564101800c0c02041d07104804556003851a4040200b4042d0b00680c1e040c00541d180c10742c0c8009440c6090824070001d4100051400e407901c8a034191201c03541d01030004524002c1541b034540c000d0148020300803680c4078002d00c40000c120103600920503a405030081e41c0c4004600300c5404242c0315103640a64100d00200b215 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 367066474 1250 367065224 367065229
    0xb040207030e1309050709020a080a0203040209061002010608010513060c1103090d0804030510021b15010603051e2404111204021c0507240c03080a0209040207080a03050c0711 77
    0xd140101491080018044c0443e498081c0340101942107050720750b40c005141e4100e246c0140314150312544032101540396240543c04101c0350a805403c01d1300404064001d800100e000b90040c0000e444284001c0226140104214140c2e8100000982d0200e01e17101660036000d2140d1210040484407500840c581526070701441818042c580060ba840b10050101100180062060301c10250080c007000d40c85007080881c038401605604080b0302c250b8410403c0140040c0303100e422504440aa0034005981c1d030705d9406582d0207600585036980d918020000f0000d030b80885018000d0540505001c481018541d1414881202d00f0030800442c078220a004003080800fa05003010303485072002d440c021002245603140313404004510b10407501c0350440711041c81000400e94400800c5440d16007010002c2c18040d001a140c4400e880000c0c0c20411013100183c1da5180540443c5d1088002810441d542e90a6040251094100110783d4002a0605c0c0101e0007441600040c5c8442a42080000c82c40d01030749001c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 367067724 1250 367066474 367066489
    0x30e0f041b21020708180d030903061503290c0c0a020f03011814060a0207031e020c0d080d05060139060509010207061103220c05030105070f030b040207030e 69
    0x700a0700307007503540700300201d10102e0300291a40910070b00d00c0d542c460b40382490701115900a070031000c0c005c2c2441c80c02003007c2603000000c9012640c009000064403101c5203031012140c0c00513040503012900300c0309004406a81310a0340034004d000c02c12295165115000003d07250f00c90000007410130307840311500070003502d881c240c4a501110020000203158848800321904140601000d442c60a007a040e8070399080010301c1141d5000d10b217007100314541012590080d140003802c0402042842e0b2080b0b262000c98001c000214066400038002d04001000e0b00d0041c0079030303004001d0400d103e403e010201d110355028a00030902002101c03103040d01c41c1e00c10540300d000c102e425591516000061864100854018400c480c01400180300241e078840d400e080000c00da40a5228850360381c0c0080080004071030f03084c90006000043d40c42c40c0c98500901d41480c2085802e550080795155107403070f081c004603e0300001301076400d20060301c05102181100d820441280108000640410640f808050880c5820072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 367068974 1250 367067724 367067747
    0x10b060315011103070c06080702070911070609051608030c010b0d0f0201050a02100c03020409140c0d110408161706010b1801051e0301060e0609060f090d0b04030e0f041b 75
    0xc04807800c0c58511b48820301422116031003c40810201018040300981c140002c40c0035003800c00b0107101501c610580c8080c90304c030307000c40544980c0d90ba201940811000340140c133038100900300c0004116440301040368480c1d20500031070340a58a400d01000040c2410320140620680000c400b0341805045c0d0015150360384826170708021400f8940180c0443c078a5881040882c2c94950b600686480c2488416001c442c803446440c4400311044082100c80501501210102c2000650204908881014581060103142c20403406409161a800c1890b64450341c420300f10b82c40c02d180c490686000101d059154113003806281c00c480f004000c44680748500c01e00100000078107140907807500c22040354051264080b010264070700b4400200402c00700c1d5000d07040c4a40c07044120b400720302e014210000540b8502c40d00441c1114000c01158844481da51080421065070b080000105c141c503092074018a6080d18044013441a100c410032410349050605c503442804009110081c418400031500303891905410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 367070224 1250 367068974 367069007
    0x7060e012c09100806040803070801090e2104030c0b03041719051305060c0d020c010201020c0c0d020a05061612110303070c08090d030e040f0c14210103050a05010b06031501 76
    0x5072400100e01300c0400000f40720398001c541c15501e03801c3c607000c010300b0b0f0b80e8181d00400030181846014404160046082c140400d48813501d00610071800d0440145406981d1024000450382d1070005103c20445d0b00461140d4071400600185402c400d0040746e860256100e20f001c054425581481e0300b80c010001403c0d04000d81d5030302d2607460741d158002411540240c90020094020f9515000e01c550108040406030030240000d50130454844d10320f40e590004050820310805c07180e02c8031402c2d51600042c0c40c000d4040604207581c2c8003608907040c0c4907a01070890854030b152100d9490062980f080211000114041b00514034648800701c041350100200101555440000c00446105540345588030343c01ca4426140d00c80c603840c1c80020001100c02090f0080c420505105052500070762000400d801185280451074030b0b45001038030340b805000481445024607907104004001c1c03042c000303041040b0602c10b40003448144403140030b10040340019a0114110700f491030080c070700b641c0204504050038000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 367071474 1250 367070224 367070251
    0x315020a020a2901060e0f04110f0d0e0304081b100903111f03090b06100503071107050a0b0c011503050303191118030601080d0813021207060e012c09 66
    0xd407498600d02c03c001e0b803205002c1194046403c129090151142820362000c486c01c00c96150540284002449a0103e40303019140000310340003003042507880400c00c28003810071242c9490b120022079170f4402603000000070341c244d22920619a4501484040d040041c3d550b62480d00740d1031a40c2c1c40c01d0b1130a0300a0103c2e4082000c1c8800c001c1458002c0002d607020f6019a00403440107c030303040020224201404c1c45000c0c851002550b0345a40d0850304883c1c004201d40340101001b5141030545051140c6908416400407400800045018409005d451000c1c81a0000c0018440b8011611003840c00c604c402840f40d001400040c14014110405d9920000758103004107400d081d91200412580c40b4560781d624034415406124814201001140d01420190004200401a20300c02600c0f07a000200001c0e005800c159203401191074000000140d1040a412248143d132241809071003c10450b00701800246110720701004501509000142c0c81c0c1c03a04135030f80c07222296405119004e04028001e2103001d49 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 367072724 1250 367071474 367071533
    0x160509160c0f0227061008040f081e030103200301020304020a09330602010b0d031706010c050f0f0c0307060e0d1103030d060501020d050a0f210e03040315020a020a 72
    0x900c0000c501001c100b0000f020325504d0000b04011414040300c1b00842041154400c1000060820070740410480c0c04c81c450546980d070b0b985100a02d01052030a1810540c408000081089407843d8030803411a91980305d200546000003c0c5400c03404102c4005c0d41c01200d02504000a50490740012190301c10050002e040150405c1601c0d000d80d240c400d02d40400b9a0307400c0c1082400d9081c13150784010a01103034032901000300303928000c05500c5c1d023602c00c41c03060241001013a0140e01524482400e540e000c41940e40c024102804107855500c0750f040d200c2c0c00e0090807a600c08914011400c0001e45e50760b86c6401c5c14001c80ca5040c480181d4141d801110b0080141109929543c0d0400191200d0401e00c840800c076242043c000908000d070644016090003030502280c00703569044030f90701c0c00603440741c81c0c400d910100055500e450030050389000c0306090b00d420ac01a2513050b02100400649009104080002014040120491003101e03070a04c0180c1090240c0c00006c2d84da14000161203006400c10815404e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 367073974 1250 367072724 367072759
    0x4060605030106030f12212304030c0b070207080d0509030111040b04090c141b0a020604080106060806090f0105010c060207050d050409230105120a05160509160c0f02 73
    0x80c0f0f10f40041d1159120383d0081c02c10450341c200e441401070201d01c1e01c980140e00709102c000e04209140c4070101e0b5179440300c0d00103000810010f188243d021003640b90b00c0c800e003014100903003580010300069402a0103500014a0f482c0001005811103040300d00500300c0d076410400480d6581c01200c1005c0c3d05540b1036010081107031107100544060540106480c0c0d0355464000100304aa00c50036074202400110a440c45601c1c170103100b51124041c001410940c14888409005d0628080580007503101c0d80200e4042420300e030541c0143c050314100c0d100c804454503914100702c901c0300d088603000b040004800c014482d55104151b80094580325000141c1003910310380c2c0d0242010355040c0c151000941c0410200301803003003800340d400c2400d8124268040181a180c60200300501406078500907602c178450415038060070403c02518a801c542a58806890415074407001d804920500d07200e802d2050104400b40b1342d907400300e280880c9a0711142e044071b071265130f030040842d699001640d11084602240e60380380f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 367075224 1250 367073974 367073981
    0x3081803070314031c05060a0302010c0f060908040f08010b031c0903150203060a1215020a090504020d0603060b10020c010e12061f080a050c060904150801020703020c121005040606050301 82
    0x50000c1c0f000c0c544621842c66900100c1001d01c528000c01c1d402c120500045840d6803000c0e40c00d41c0c0d028608548682a2420704c143ca00201440043c001450070349040140851130018000b43d8445141c0844015178420a042c01d0314010300b01c00350f268020349441e8441c0d800d0741012403900303540d9003060b80203d81d4036120540c0c045580000c0401c9950008104441450f004020380c001d4002d074602a0900c1a19440390102e86050700f10300e00c2c042c1c4d400135a40ba81d0702c2c010400c42d0000c020040080d95116102c0650f0340240660384001c56425040000300841450f01c581e80100300e83d045c1e80200991603403c0700440e54200c10025842e0403890785540034002400903c0031900c51690801e03442d10581e03428a40d81d6403040c803580210211380060f43e01000151020882c5030319104120744403904c5040480000d0010a000001040c803034070415000507a20a040d00070b0142076000740c00380c035484020002440038900b000024031295801c100d514540c1c0e4810380d80230b40c0c0c01c5401103200003540c50320344003c2400c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 367076474 1250 367075224 367075253
    0xe0f07030507050909030d0b030c10030609110306060304060203060f040c0f08060625050309090f1b090a0509090f010c050c1b01050f0a030e03040e090d09030818030703 74
    0x49400002091050160400401000380000e5a0403d42ca103440440c80d901c0e8004c07182c0c401200c0c1c3e1118500b03100f6690401401903000d0b0000c20000826401c4140600105a10f200b0511907030704140b6050300a000c14025079114903000750055240d950f46a03209002544010843d0342d020070034007100d881640311449007246180d000d17110b03414088007441c4080e080e072100030041445504100000307100660540b80d04043c1c0f6100001180071604d40380340040c1140605601c140e0408c8100c401c00143c00720412013607004513004c0d0001d070500c0c103064250385003d120392000d00d600800600710401c00c908116140c650b2000032002074840182c034108140303080d58107003281400002c50125469440c030740b0074050420041e0a60084147c9158032600190150103920080868038a01060201c00e8501030303000801d250820105590b0340d0758952540f0440c3d4030f41602c0741002c0d4410204940c0d5041d0103a1100800d4981081d20700b803c1c003038280c0014110b0b10100d1426500750103142c100100060403800314511 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 367077724 1250 367076474 367076503
    0xc031e0614070809010b0102031e0405060d060626011a09040c1e0503131407030c121208060307050f0303210406291009150903030806150f09040e 64
    0x510705042c80c0041c03107100050140c0200c1c0c3d02d00000c510040c0e0300002210810350180c07070180400340c1074a40c4a07445004541c842034019800250511901995501160a450b00345d21064002144c0c546083d8440b034401c5507003100301d54040014800300c1c000590380c01c4402c0314036004034a04408000800c0c00e031002040e0000c003140c100240c00c0d95421502e001010108103501e0200e007145007468001d5840c400510018140384100825505000018048035020b142c1209000e1072607036035045d5003000100c14980503542c04408640340000d161160351114010318000380102180ea003000104165070441c0b20322a58180b204200c070200d1307910003c440c2504501e007146209114a8107043c00c2c0f09507680051102d0044031165070303d000d24909207414002c1d014081e102011206d1114509031036103445500210800e1200c028189851507014140c90f01b6a0301c41c0c1d44602d1262280300a00c0802d640c1c0c1d02e00d6000c081d0302448401010000361000d007101c44002480030801e002d621124606107100f052240d003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 367078974 1250 367077724 367077761
    0x324092d0b0f120615011806090303021c02030a030b06091903200307060509061209030333041a0d0b0108011b17040c05130c140301030c031e06 63
    0x601d03490000c2111039a9501941c118026030a041500703610344400424001c811001c1c5008181c499120381140c0c10300010420500004c9a2519400b0b0200e01d8548021001881b5000382d150225001800348180494207400460600640100c1134003e4a49114050740048040c0f002c1c10103503481144684034040c440d0707101500e1509600308144440f05480490001854030305104106031000200c007000c80d005850300c25161140d1100240ea0b500c5444c07007002030048003c040c0310712444080700650040000406116042100c803440c0909a40b44090224552008480322041810315801c00e54083c4401100b900560181c0e81c006007000f91107240560724540e03214010710040d0401d101c0d40c0c180c191403840d51a05034201501c002d04041190b0801801c0940e914089400c00000f88040360142c80300921001c00f0100200b507602c02403c041184000140080554540701c041041c2224103803900109099456800c6480d02c110341540707081d894040034604007110020644510407000e00c54541458030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 367080224 1250 367078974 367078991
    0xc021014030a0b0909010b090613020405030d051207020610060c0606150f090918080702041806050601030c091a0c0723011e0e040b0312070804060324092d 68
    0x440140801440b4102aa2610307d000e00d995894076161a40400300700c4040c40099082c80d0124047c0c080c0b40c4c4895050b1080724050b00301e850300070001c0c203849004107106580c90b6481c502d003203985440548408070a0100c03043c0a02441e03104a14000701507004400118913a9030b00c2243e9003244c281e40400c0c5001034414051408001d50001400b401816404018400440e15501c043c8000c146034000502c0b000c0005441400c64446420516580d203280c02044010240ca0a140001c0d01c0300b01e40c3d00d400241717442c412940d0180038408050030b0300c010340294042c0c420184e0440c603181c0d00070041c8407442d224503040016007002d40350510210000d0881c0e54001105094005003411394aa000200d071010400c8100101651182e0b488001e09401c490108511052401103810140d018280c9164100f002641c0e005024002c2d000380115680e07030b903080001c0c0608150204c01c047d80241c0f4521200601074080041440c0d0f40c00800c601d0030405594070089102c03112101d803c18000d0100c8804070b8848004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 367081474 1250 367080224 367080229
    0x2c010e0d080106020c0d15290d0b0402062208030c010f020f030a0c0e04020a08090f0a03080c03041a0a0c080105060a050702010c1b0b030a0c0507030c021014030a0b 72
    0x10400c081405040800c0294142400030b512182c50041d131360300481540d11441d0a03c0881c00c00400e480e00c808100b00140a08410301d045006130700d908540c175070811141804c10500389500041000c41d007200f130341411504d940d800c012071644104003407144002160307402c4031000342481e000c0c0000c0205500450761410b154003003130b0a40700e016580c601c1c0b00e407052184110360100031040700d0303100c00c1502e000203000300804c43c1501c04041c0c1c0c090940d0414400300d1440003164011100038000d01c6103030220f80b60300d44000c03801a5540c10284000b0005920400407400d0b03448494050364016104d50010440c00c0118000d02d074800c09c048508041c03054070b800d80c0041c03090300098038601400c4245da1442c504202c1c01000307005c5108040009040120040c98282800403040c81d0000d02c40c2e004180c4001580d4814030550560020703030300000150b00e02000000564002c2c402ca80d240341e4552940c11445240303800b044070796004040c041781032124008039039641d42500300c000e601c12603211500140b000150000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 367082724 1250 367081474 367081483
    0x30702060109290d060f0f020901030608030c0307020603040f0b1e07090f052701030f1e021302211f080c061902030409020d0203160315092c010e 64
    0x76481c14015607541140c110043d9020b5032142d1010075070302050710410342e00c0c100000f00303007242080081d54075000c03c40402d20050740082910300000da0b8140000e0792299845516841480415031491340200808001810003e000d59400b0303000704410000c0c22025241c5003450b41d0210750b6010441c10542e108010b07840e0040d11590484c08515054001d035040c401440d802e180c00303000b054401d19056940c0c00e0010701a00761140c2d00c02c86000030b03074010f59507407410078403840080d1000c891007a40894240e040c2c9681c040070400958000f8400200411030001c904020b5000d108148449141c012a08854440505001c0d0003082a6030004030041d500d1350551b0f19a850300e03001503409400040e10b840c031581e1100c055800000c100391032008240080311090b884c502c40e03988114552400400c13030503c83d00d5a40d0107148a0b624180b0100c209030780850003281190050301507003811000c4c8150034401d6803510382c8600756640a1800368801d10b40b403488600403000052880b20132076911107862081e619070500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 367083974 1250 367082724 367082741
    0xa05041a0316030b04180c050103060b0f2205030613061104060503040b0603071d07030605040504031e09090911030d020c0a030f030203120a1508032502060d02030702060109 76
    0x941040c110300340520707204142c0308007001c41000c040d11800c0d0414940c2d507580c07200c0340302c0e5415040203411385024504068040050301c02c0c075010918000e000142c1404c52000c44804007a100c0503246030080342d440c00344000c100e004090100e50200180829070f510100f16480c01110540a0402800840c2c0b0b0200155040d00f0800500f03000c1c180402c00c01213402c0b03c292078110758811081e0946603180c0700401d00d04803107944100314070100d0022034980c0900c08040a4029106550280202901e480511041e0780c03080c1c1c0c005000a2a41280a6180f5021030442c000501c5915200c580c841d90741403010180c41e450b01098036900509000b0f608646010080d0495080b854005440a07039400c5002030b1a8501500c0f024050111f042e0030030041610a0049808804c0003662800d080d060004e508402010b00c1d001000600b405050b021503001000019101e0074492208a0030101745000d00c1c5040c034544107403007240c100f2003d20607059030f130713025001961003443c02c1c2e4010309040d8908021101a03807801c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 367085224 1250 367083974 367084019
    0x27060c0c090e0a060f1428051302011d04020307120605040b18100312050a02150f1f030f1a010902030112021c020307080d0f0504210203070306020a0504 67
    0x1440307100c11804500c2c2c1d50b850b44c11110028403e10f2820750000a0849102c1103000080d40000704206119020700300b07100c1044414950000c401c1c01e030907820866000343c03a50396500702d481c442800150311492000960502c0c09900e00c116803158004141640c0060310040040b4503561815041450b41d4030545005250403901402240074000220b41c040c1c6c0c943d403101a03504a02d42c0060b200c0e8007400d01d000c00955012074151001800c06000030219080320a40768014040c0111042c240c8a06204a602032003400d400b0031030503103808010051900204c120b04000b4084800c002010402d20401d1741c003100d020380908030050002150030580750340c050b08016800e030320610050009006080020403a540e0655070007504000c0884110020302c14002d00943c075104032b20002c80d4042d0f010401641000e074030b49846071aa00c0c0b1a105079442d01480c010070760300394038040051101c1d03180f0524036481240060142c50303200c1c5d10794031144207a900a00184010071000a410052401d58031045400c2c100b41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 367086330 1106 367085224 367085231
    0x11060c070e0a05010e0f1501091703040305060c190f0c02130b04050615031302060906070b1f05030a02040506040f180212010b010f27060c0c09 63
    0x221800e05550f414800001401c5144a5225003d2105042038040c00d40e60016810494214052443d04001030b4910005101c10f505c45401e6010103407002a658030b0303080d828000e1600e40301600940c01c04008100e4801c03101d40103040b03003840b0301ca98900000a41403011003100d035003813034041c0a5072202040100e260086c42e5a400300420050581e4280156034404080100c0d943c0701c20340289080d002003000a10307003c041c3d005040340601c014401410b002035240419040d82003514100d9180402100f800340940301e01460b240000c0f051424421424201008240c07207500d0300c41d001f4003c98a42c00824020ba8454101c0440c15a0780c03003040154805800440042d058440c00a900449644515841004041c02141d03188403060f100c00c11807801021040b2903551100300c1c040c03c402e0a480304040305640d556040340c0244004c3da14002d410a15060081500140390b1015419924 = true := by decide +kernel

theorem cover : BRFrame.Cov 366906474 367086330 := by
  have h0 := BRFrame.cov_init 366906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 366906474 ≤ n) (h2 : n < 367086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
