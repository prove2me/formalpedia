-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:29.954692+00:00
-- url     : https://prove2.me/submissions/b6fa5a3f-1288-4ab9-83cd-821867645847

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 925899280 ≤ n < 926079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 925900530 1250 925899280 925899311
    0xe0a090b011d093415030605011d0319030504030f0b09150f2e0806100909080a110313080a050f010b0f121513050d17040206070510 58
    0x1940c40040c502c62503000200a0a0003103520031019030480100e800c1400480b64a00d4140d40380070742c6a8480701c1c500400611403066400c100c2c100c0c82c003034a021901600e000000340c051074010174040b07a510399001c1401990355012984003851b2008003824143d8140c00e060486d085c0c020707900b0052800104521328000d10003081000b1744a421903c04813101060607010020300c10200766940056071300a20702244c1d40010b08011000d00d0084003006148002a40f0081040100301e9481191a500800148201e41c88000c0000000e001c0c02c210501101a0507991f01e0b04a100b80410036041001102c52401800030600c111041480311038002c444098403040190740350800010b04543d1071203000310f520204001030040c00c1e40c2e0303900240341003140890303030051055407042042e06075140d0045da000c101810001806803406030104580d620558030580c81d00920301400c142400041c8a021603070240ca2000d04403000c0d43c17160703065403995190300040c0391040c50f0480d0000d0310101c5500700a200d8041c0240e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 925901780 1250 925900530 925900559
    0x1002070e07031b03091a180c0a0303080f130f030e0f030a03050409180c06050318010b060306040209030a020a06030e070611030d0c021c080a11130e0a090b01 69
    0x1038100c800d01803a119807106500b02d44003072002001852040300c18103401d0740031703a205040b414000c102044126032811130280010104840c1002589030000303800912980030880d03801e040500343d40742d84540d41552400380030340702c0c01000355413034428400001d07a1034140c550025402c694001d021124041c803500d005012084e001040328000e41c1404603009107441d000480504031601520791038906420000c40b03002414001184c0e00c0d000002e200204000344000d464000249500c0d590162a410700c80000061103a141e03551000c660b040c4040c8100030340c0d03440100c1e50031140c03c0700c006036501a1400407078144100004040c1d0701000302030002070740d43d030140c00c01205030141c00140c3d203695860f02400e964502c01000307210048c1c2e10501c81c0c0c060b00440b40c2d004070b40d29505801140e2003a40b500c103914604004176900b210024001d04140485400140504600d01d40d00d50403090400380155588882000380b44502044903e1900104150300030f55404001c1060700084699810360b118680d00d4042c07207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 925903030 1250 925901780 925901789
    0xc0807050d030f0b130b0105070f0c030201030b010f080f060d150b040b03030a020a0609020d15020a080a0519050403090f0305030c06010f0e040f03050f03132d03120b100207 76
    0x3428091685190103192144c28008030000340b903140c4102d20b0303169240060440002541c18070604010540108005c2030b4039131381c054841e030b001d287d005003944001016120f40095040c18041c0306055074071a2500305462703a90100c0224412296644c0e1000004c1da860883c5d071010380403880d54084411151003d801c8415011400d55007400b8156506042c960740f441410741c030600581110503d0700009129401124202d03000811280b018011506d5003500c40340640700e00c403880c550006e003a108894100c182e250303010032034440811441c17a141c0b240b484110300030344828848641d61400181010b00608400d8007902c0103018488000752280790031540c95020800c02d00b840d01c05c1e10000a208215840c941054803038640340d80402f074890f523983c0d5101e4041940110b00b4007a0500220030011502009980304a10304141e601295459040ca00b0002950000401040440221007180ca250001c50220805d6040ca0005030318150600c0c210010089104402da000c203030300030601d01d40e0342d002403141b0565 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 925904280 1250 925903030 925903037
    0x30108010e0d020d050f03090a020a1e082107022b0c0902031b131e0302100c0816060b0303041d15010f050c102d0b03100c0c0807050d 59
    0x290b8804409990314140315401c0d000140342003144200d1480c42a018503000017521045510400a40d80024000f801c00d07040449031954203028078000b04007048081c0002d2203210b010303080c0240d50000410004100c0b00001c40400c8000800b4821901ca01c4070341c1c4412614681d001524540b40340a1860302025070742c1c01e88404401160204805030075200301c9000e54401114427040c18031003541030a49070030140b4001c82d407280d0903000140e41020016034030003040d0b1035001d04000500f5841044481084800a2000c02c03030b0001000c07000400f200211115141050603610640c0d0451410303002504408003c00d406010124000039050030f225040d00d1140e4660892035a02d9540c0d03040790b1030380d14401d0600c40c00101e81c49601111180901c0042c04842c0603030094803c8032a0401a0b40f09440e1034490394000d50070900345020801400b10308000c400c0003249400c0c40b41c0c02c1c00100080d55040c4104109204558a4085c440c190f4010840100707216030000410b915909641402c07910389c1ca0812194010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 925905530 1250 925904280 925904293
    0x2030105010e03010614120a050d02032503120209030a0203150609060d0c091a04020711040b01020a0803060f0d1505060108010e070c120203041d01091a030706120b0402030108010e 79
    0x1a28040c0195420b90351484d92466148046c07604111076100147d40300b40c0b880c020004041c01141e030902c01f10003681020780085550306038088480c8091907428006010703400c0090400f0001950001e41e288402d40e40007000b58840301044006418103000b544025810310440e006000d0380d8a032160f03080e02c02c56048401b011169907140a000b00c80c64070440043c03000083c0c08040c00500620390121540d061030102d1050b07044000000308007260301943c0140d940c817420640c400410720b0240a4049211000e00c0a000c4100c07030303991482414000900440d100b40d4140c13084050315190b4550070210180c1200d903030361001a14a5180004090a54400d400250010004141c80e1681441c40b4044d0303da903a074580c0e880c44540c850780d546256a09820003140020000041e08039003074450038907258035041c40e81945525081c003040482e5503007004000e0b4000a190440982c0d900030a10b1340441c1d51500340840e50fa4944c1c0a02c40060012902c00c1e64003e00c0030002041d12141544800c0e007525140e07085540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 925906780 1250 925905530 925905557
    0x2307090e071d0708040f0c030f0302150114150c030d02130801050106020106060c06150312020708070801090f031d090a0e0f010e030412030912080a08010f0509070311090406090203010501 82
    0x4080804681c4440413942920205c0c00042540580340c103414000e2141183c40343e03c80d6078001c044400790320294016401480d0413801d2829034030400e4018808000d4001340000f40c0f501017510300342ea03040d007070b25004804503441210080c240121160300002d054215a11082c044040001c04842e018a1001d9031030003001080d41801485000e00752030b0103031650300c0ca12403141d6482c000b50626500c41070746285521000000941c107680c06c0d5804001e180c028241080c1002d242a00c1c00c0b14560010415030304244041001c00c0c00c0c81c1e8a0303442c0300e403d4500101715020610100c0c00c0a4420300d1416000000c8004000400049a12400a5a010405072507003d100116218283e030340010403164a500100001c11003502c43c1031a040369148241400080c0603654001c03200c01419948c0c00762140c1000080104103958015401130241040d1201c26811605180214240000041190046c9039039407224800203200d07103080d5010300e0302c010402c3c44210b4540f5040400f070342003031144501140d00801e0952 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 925908030 1250 925906780 925906829
    0x7050115081617030403020607140106081e01150509091603060f0524040c11120c01060b031e070903060c0216090b060304080a031e090308132307090e07 67
    0x341c0e80c181941c004c41c02c044c00c40c0c082050561080c3c0040f110091026034140700b003103003030003810020b01a24000d8180a2150300c1c080c0b02c407121a1001400c1030745040e120b072aa5403103540d010001c0d181c00f80c1d60254583d5603540d003145014404d0364004003a0084000000401c02c0e590451a0015100b04080c009902c801d501c80d1030a0780d046810042e4524840c81600060406038020703201030041d443c1c1f01d42c50401c004096410081c0c001c3c0508254900007804610000c800d00030340740140250703081d00e4a0f516145200b0303200403c50b0440c815502c0c4205001c200403c3c86001c2c1d0f8006107810080070803544036002c2d0003030b566142d0019003546440d10040005950316044c800d90032808009041585140ea407942e031201b05500030640802450754506160b41ca20f165034034240728079070fa503503000030311900903040280c000d6034014200305200141008030000101d801c2c2c0c103c0c41e81e240003001d082d186e42840c0400d60922003240c1240c081c2c1890000300c034150200004540044aa4540d56031a0b03a00d080e05050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 925909280 1250 925908030 925908059
    0x90c0f3b060d020303090612090f0304120605060406030c0b0706050c04060e0418060e07090b04050601320d0c090f050604060f05070b0a022a0c06070501150816 70
    0x4503982840c4600003021800c00300da02410183c402001d99251450740c4000074806c1d0007001a0800600040003088000b560800c40d0349191484030009500f450325264461030800042c0400600c8140c441021522a454a400c0100519445803801070480c1d00d880107510307a82c006800c241c81c50f070700704400309a845002404032802c0d00c03000e81d1400d41c070345e090030240701c00380010542e0411403e00000042c0d02245e114400c05907031100160140c0065860034007407c007a6018002082d01c52071504050108907a00416651100401050440e511082c42100c240040d490581841c510190006a24003402526407149035000c0160720f5401780c81d611140180d00410f01c074004e03a604400200028012280500c04000f500c01641c40c1a91030094a9580c0800403101920305001d10743d0041016100c1400c0050300310807040740c81c982ca00d01e2001d000501c43d0390b04c41e50901140680070000300c01003406002c0d00b0140924429490f007818035507a403824156610318040210181341c4058202158405414001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 925910530 1250 925909280 925909379
    0x30f0c0917120301060c0c0e07051204030c050616030e0a020303030a1e020403051c08240609030303010e0402031e0304150e091e01080705010210090c0f 67
    0x1030040c814105100307400c0001c0d2000c8001841c1c801c40c482c1ca09a41d07480c2c40254041c0096a44080308904245040301314001c8941245510400000c00c105040da4040150740e4601c0009858000c035480c3d5040640e0303440c1c2c2908000d801c03401403004000080315010802c11092540303550400c05040001d200315242c07070348090002e6040d0400c0000c200f08800d50b402500301c0b02801e01c03161820070500c0b0070b00800ca9200758001c8940703801c80c409501c8010160f400032000d901c030170b0502584515000510b2200000c440342140006c0c2040c10309007078140c0341c040a40f04064406030413030f80d4a5031100910a242201240c040b8400d118940c401c02c50481e003801030440d0b04d110400214246824010440700d0301400c03d4612041100c0c0c140c00d11031316503031040c030203010350140d400c41c60301511070002d49141180140c002540c10742c0660010071890345e00140143c00d4000580000402c20203a21705500e1a1103164400c030a02c0d0800b51020901d041240c00e03c0d03080000308091040072104242c516006950540003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 925911780 1250 925910530 925910537
    0x9050f0103061202060d271208040503161115031008150103110f04020304060219030b03030f031b030408190c170a020708060c0c100515060c030f04090b01030f0c 71
    0x103100700608000d009410300307a000744000b14048014203003811441c01c035401454000c09114020354288051030323400d002120210310701007042c1c0c501034581c181e80348110700000d0b4107080030440b80000e20505c90010000100c0041200d00c1e03d00704d1408031011600b00307443d401c8c4038020001c00040c06100000f60b0110f42140241d110f45181e1843d19040c0e540031504515940001d2480c00d151140da0300d80c40214486d920955006032141142005107102100251107001414039001311a543d540e800019940c070002c0b040001070343d940c2e900958030000301e101c2c03008040c1403102009110030845002c000e0504410452960f00580700281c0c411103c46107285406001c4c482282d0910040a144c0c41c003d1450411500440300780c150f50304451442c08a045400e4600c4d9032010421a0500005104405510a920381c080c021803c0150810000000d03060900b07220722030018450f0705141050064810302908550f207580c980303980c0c0221030090032000170000d00082c07416025500b81113062244018000f01c0c0e40c3c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 925913030 1250 925911780 925911809
    0x605011715060342010207030c150e0a030b0106171e0a0e0d0206150301050c0a030b240304060e151f03020418141c05090a090203040309050f010306 65
    0x24180452a0302c0545240360000064541083c0c01e1607010444c40309800072001e06000762540f004a0310702c41000301102e811074000450420119003000b0381182942d88500d022150131010a13400d03a40b0440030048181c0141038564000b06010a031582c040c100c8555445100c100304840c20910601d82c02143e540c0c8001d071541201f101d40c800700b00001a0302501120300000e00c002c0e0244030a18140d039603200c0ca0300591201e01000f8041741c11304c1c00030070000800e500038031803130501e030500e40140c0c0211040d4908041c2e440242000d56911a5003101e17042032042c00341000d140385803560030443e90046030259004c600b03140d201e202c003a00c0081c1c03c103000380544168100036202c40305c001901c054200400c05045144160205c00742e6254410113401d001e41040c0c0240310101840c2c11440c1d1a194854440f194000325501540c00350110740da42c4c00d9988900d407282e40c50790744034001441e44040341c0100d003c5a201204000401d41c120400d4016500212601e000c50b60941004400741c600a000f0383c00c0240c60702 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 925914280 1250 925913030 925913071
    0x1b12120c030905060d1a030102090d14030918070311090d0303050406230103120504232b110301020a050409020309030403050f10051506270603010906050117 69
    0x458140c91401d01c0307441c06001041d581d000048036900803515540744980d43e40305004844a203600e10101500044e402035080064000c000f0350128a142000b0780144031002c86048680d4050044504009006226008072000104c041031b11220071100b14000c2841d2040c09885064030b4820f5030000f0f1401400c00d88482d903e0780e4103c000d00343c041c004485c800d0b184e900c0d40c400c200b0042440c050000915502007215031650800c412005616040c0c0814494100802e01c41141c8540c075114407602400341c1c0d0000040c1100c00b0580408500c0d2005402611280480d440c1122404480380c0706802a01d41c4000c8821410405080b03114641851001c40c070200b10411a500d1260041c43d403000f180b509803400c2039526140d0a00705415200c0310901c0c2c1c1c02840388144000600e108241d00614960601d41540c0d0491003c0380d594420062041c0502044c0c0b00c00f656a600c2d8104d9401c1c114101400d401d80b00d5030744034064409441c50740034603404101506012039424050144e194481c141000d80b00a804101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 925915530 1250 925914280 925914287
    0x90411040f0c052505070623073e011803020301020304060204061d1008040f050d3501090b060d150f050d1101080907030f1b1212 57
    0x952506a00103489040d041621034080c42040040030894550760b903034014851075030350703243c1c6030040384140b01445520b928045440050514156225070900d00e91643c1d8043c031500411840070301007031160000140d0002080444410f500708540d81c46045c1c1204404814103a00041e2408080d008422020041c07070144d600c40c1282d1400e540521060066031a220340200b400d81e4011202543c0c41500040c0801a4a902c20321449007910084038110b2031491090009440115045001c020012001d0200c0c00b40994084e001100f140c0c0f1008a40851515010142c1342c3c0d5003c10301c0300b4a03003a0200c504403d500040024990080700d80e4400c03085a801c1500d5000148091071b000c41c0c000320184060a0303114494420590300b0000300c1381030180e8610300a00c07a1240b50303180d040140212030b900d040000296029060050000c0c003401d00c01590781d10760920610f8084264006080c0d440c0c514403250a00c015034103403821800c401e9151040340d035141c2c03100401c180c200b807400404018580c80b003004668070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 925916780 1250 925915530 925915553
    0x31b0f0803090310180c0b041a04030521120901050604270b04080f180a1202130e010f090f05010f090b130c0509090c04050609270c04020310061407020904 68
    0x1790f030700441c0000301901e40c0e015964140d0048480e050380014280a06091012035019015030503842e40d1425007103035079098940c0442400e00103c818801c0042c040001d61206461410400e805c078100d85240424005028000584009014502d800d6010b52200324203000304040c034601c501c5407482e940c203590f145802205c00a10a441004092001610000d0008001c0c240d2000b00d03522603c4100700d030b204008103403441c1d17400281c4e08142e0203041030050310b6440304146811101d070340015a40c4140300f03005000d040c6030201c400c2d059142c84669000c01a200111020f1030340100c008000305a45040c2c024121540c1080c040e121204100001d00001956422141000c0c1b00c0c1a120300050f9981d0f0102e10140030a03148038130240c1002c540e0410f141000d11a42e41d0114084406c08082e0901e189c19586c9001030382d00c29444801240c4203042000030800c4803001e100405041150b0b245000d2080e506800071030f02508000411955000001150042c19142047e8008113480003c0d211940c5030440f00c2c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 925918030 1250 925916780 925916801
    0x15091b0c0501180b0108070501020619020d0605120a0b0c0307020601030f0309080715030f06050105030a0e0a02310b0f06160f030302181203070807020a031b0f0803090310 75
    0x103403078160a5035400c6a0700f4851403494401e070060350455041c901150304141881d007055046602400030031540d41d9402c8500f4510b40c1ca103400069035110f650020001502103600000c1e0000034008009a8000b400078041007030718020309201c03815444501040490703110a5a4200060384420014004a004181c040040c0b03403103818881216507640c100c0a00f030800d6907001c0080101c1041640e69060b4240c000c1c1da0305543d080f0010400e0700e00b0200081e24038000600611011035490301030304030f019000c02517000c1803074009002c040241c019201026481a4522130180e00043c0654203208090340b40c058807284090040c034640d540b0280505000564025140e0050f01590140291011031010920010014042d94025a03201c584104001050301c041e0500e80c0a441c00d40d005032003a06c408000e540d1840d500003613050759036070307a800040c090720a55040501081c003000181d000c0b10010281030821141050b2001c0c22113035440c0c488546902400c843c80b500341c0c000000b0b8860880d1180d00c180c0000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 925919280 1250 925918030 925918033
    0xb0403080c0d06080a060b010f021b01030608010516021c05090402070c210501050115050d0203070504180c0909021213050f010f050405010b0f1e061c15091b0c05 71
    0x480040e00c10b815108258042002c541000c0052814042540070322a92001c081c2055020b008001a00a6683c6a1255008042c100c2888000b040760f01c603401040050189100034402810414482c1714481000c000000151041225400301741049050401540030640c80362800d00c5561000d00c0b020707521003841180e40174500500414a031828082d51424081d04000c0c020658285107401400c44806800580d008246100903104080d401001c84000da180c0d5400907880f034130b8104041d2140d010301c5d0400c0003032019040c0c0382660f401156000104824031680c0b10b810032596035001170300300d01c200350070700941900020000d00800714646128a510307204030200d4110b41e6101ea0b1407402c403000885500034a82e210814041445024050488a040d007103501e00254070701c20300007820721480881e11000000300352001310030a43e2090203031000700c00e1600803005915202c90003800101a480b09000701541b4850f0041400f120a20941080f0502c0c0d010207c1060341c0d4103001d5850040031703070084825 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 925920530 1250 925919280 925919287
    0x10b07030e06030a050a11090a06050904020910052212021018060509090610020a032024090616030e0c0a090b100c030503040f0305070b0925030b0403080c 68
    0xa440b05001148034074680000025a0708008501e10152107405510419400f41408074944942c2e841501da01159a00d007030091b03445004c00b0106e0041c0c013806c200e075039010301c0a80ea090900f580100061042e46400404881868002d0340301d0756500b5024041c0340082e290345075000006040641ca502000d0025080a0318006180241c0041e00c10a9070402d600290001c140c8040c07500f01103001035080700f012103031007404400045001796540c40b0036502a0401c0340c1005040e4547e80c284c1c0888030040d144034240c40200b00100ca2401940111241c0c3c80380c0c2180c940d0005d2165980425001e01074140c000c910070400c3d001c070340114094990400b8814150103214480c3c0e54039540c81181400408080780c0100d006504081008001100c1a01d6101400044458803000950120440c1e601c81c0c0e010844a00341c0c4071605044445020b031900050101c417641c42800501503002a100b22140c0c06001c42d071070011030b0303040e07035003141c02d00d91000030103004202c40450b0000740141c1d5030075440380102c6125810f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 925921780 1250 925920530 925920557
    0x6010b070614070908121e0708071406150f010e0111030903060a1d0712080a0302040b0307030515060a02150919060b040507030506091303030e07030515011a03010b0703 74
    0x21803640a40750f49020a9984108002c0349500b4054650201c0d1380a03c903608007000005901c0b40540014034100003c98000b409000304101c5130709490040d600b1000c1d4000c0c0c12690f915496840c1801e03180e0303020030342c80c085181c80c2d01c0c502107809041c08441a91100e80114020380151410780b01a1341e42c00403800f041c8000e0b0344030f4404000303035440b83c0c455100105105410301c0350005000c480e002d02c140c0d81d030040c00090200440d10030070001c1d226400454550f40f05003400c0214000d00440d00400d000000000c1030000c801d034960461400b81f00800c00040300c01010000f0031486110750b40b000000358116490000142e80e0388030800c1d07400401182aa28040d064620045441c00c80c04001c4507440d586200c049114101449401c0d8041c00c00e04080105040080000750641001041f8204801c10b00103580e04040c07003038000301c0d01103a02100b207a200548a2130680d85032880c02214801940c40080009103101d030440340d101e00f80d6144280d0520716405d08400b10f96030740c8154801d80030303c440e03902202d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 925923030 1250 925921780 925921811
    0x7020a0b25150908070b33132307110c09060d0804030507080601091509200d0204030213020708030f1506040e090124050120120712020f06010b0706 65
    0x10fa240b44200000d030340c0c52066243c03004801001510b1031409494040c412031843c0c42e9100b920440c00306018038125015001c00005241403065441c00a007503050039004258801c1410055030001b0340f1501001e802e94034a00112100380c102440045140d00c00040556141030052906070404006008140d240141c4c0d21070181c594020b9000300d03120390003100b00304240350060000b903014044202d4140012100680b00b0340089480e4001c1020f042d80d0b42e035070b024126190305036000841c2000904151030301c180b051000020b4004c0d21051b801180000b844005e000120310880303c9081e40480c05d2815038480036981c0040070740c0104542030041c03c041400c011540d400c0050001028280b080e0044c03464950030803801d40c0c00600d442c044e1056038000310300b4001e9100d882102038840030301e8400d01c400f4648007203402400e110394860301c00d4040d20079880f80403000b0a0090010501400342e20080100c2154100d96404145200c0c20854003c400140454440140104a090300580021030ba444c91318000c039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 925924280 1250 925923030 925923041
    0x60903011a011707050304030f18091505010c08120702070902370906030c020115290408150c070501020d05101203140306120a030507020a0b2515 64
    0x2501e68075140c0703100710120b43e0300c850070500403254000700c03804a0a05840c040c0140c00b000e400142807200000c1800b004074492155048205002c104540e40035a96808600062030700c180c08003440c0c900c02c3c6c0045103039400748100213a450350010800d0319210b20402d01044003500600100b003140226100010544000c1c0041d1840352021000d03803040c600d003087e40300041c0d1002801181170072208011181850b4200c500b002c212155400c6c08500030700842c404a00414880c1124000d000141c000466100010702c2118035402c00095180823502034204d084101d800b56100b040b40ba0351003007204503001c4400030849504886580c0c1c240707040c141c055660070f0170783e0003144e5020b1181f030b40e54040100003019401440010700d00e807600f5000e0207103581c070014000528581d00c800340303850010209400340c981d410a08410035202080d81c0f4003200a1a00230b044c0d90207000d040c1e10501d240340001c2504120082250300304c1c444085200c11199140c2c0034900c22008400c0d080d1203554010300c1c00d407040580e9000b04c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925925530 1250 925924280 925924301
    0x3181203031e0703060501021009030e51070f0b0f040b010e130b04020a0305060c0d0501151b03170703061e140d0602041d0402011704080406050906090301 68
    0x9080310000015540482ca0400400c008105400c20104006c5a42c01082072040010701290105180103e400d055032400141c4135250303004a00d0b8040fa0020500715481038500e150f503c2d43c1040340151000c0c94a8444141c400700d00c03810074040440b009071031a148002c02c0340314031071241c10000135010784400d008810101c50304c40320000c2940400c001c0200104216003d03010703840300001923040036142d02426200700e01d001010a001d0602040940d82c2e046c5114000f15446011a05070b03107000b045804050b08031124822060b42824000f02d075500c404d0400f0b0320042a19503507000549541c1e0386048150501c1c240a0702803201064421180342040c2444078403902c240d45022802600e00041c080e107010703110b01c44203842d56001c0d000780110940d5250344051554200d80102d202c1c521824601c0091007281d125151440144000440114020281d544107038001d032500d9210040c01e0201c0c004d59241120004d1240c04c013003205100f070030b0160022741100c4001070a000c1c103141e20680800d08540d040d090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 925926780 1250 925925530 925925551
    0x20708070b07123902030a05010209010f020715053108120403050d080c16030c140d0806042409090b2d0a0212071e09080318120303 58
    0x12400c080c450700c1103203c003243c0c045203452403070642e140a250341c04a581074485001503092440c00005000820046007003541c0040903600c494001d49410b9000b54480c049c001d000c101e41e2007410307848900101e4071000b11001259542003400c2c11b40c03070449a5900c541c010810078442034800600102c02d460b121140035058401740710b281401d0000741ca20f810300e04517101e1401c1004010500000b1000320341491003c1c268100140030751181030580141c3d00410360300041400031409144141944080d503803414034040e00000005502d42c40c01a03440c0c0f80660300400c0881c2601000c0341381400d01d6800748030709800424002c2511103010786261440001c0c1d500454040f03403101c1a400c01c0c049500134071031300110405d000d446105d0003500003e02001d0f00485001e0705005820000781e8440c070a404403041c0725046400c03190545440d90014011405803008101203642c04c100315101c482c080d1130700405485200c00250309007a000300303010781540d0b5114000c58101c84808001104e0780c100300065802420141c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 925928030 1250 925926780 925926787
    0x307440f0601170a020d03050f0d0609050f07170c040519140118060e0109050d080309163804060507030f0e0d06051e150307050d0201090510020708070b 67
    0x344031528019040c0c015000d046041200c400382024000784041c1a1541a98030340a545140d0805803031500424090744007001000814401082d0356510040c2941e07200a8104041e440e012000da00b0718000b2294900441c80052041d20324410110925a120084c08429403034a52910041074009000c0004400c80605000052115540c1810f4002942d80d00303107060481994180c0480d03443d40141d1158405002e0702022403400b0781d21500d040406000c01400031a0503210600e0300c1081ca6200b15014032140c01001c416051a14000c90b0040c03c6941c2144140301c12102d80e031156402a4a000400c10000e5213001c40142c0751040c040a407004000c60b03100c607600c825032810302800b402880800042041075000c1da8000d10780d41e0720b58180ca215000f500025240da00d40704000c4401e002c40910b900c1e1203210000708050011003004141c3c14100c260152100950794006105011810406c000d002c01c9100005000c60b0809500401441c1141d20403186550b035509048c2d414601560000c111400002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 925929280 1250 925928030 925928053
    0x906030c03120a0206090a020a03140a08070f031205011a0f090a240207080d12090b040c060914030303040605100f0b09090906090a17040e01180b030744 67
    0x11721080780d220342c45802404000c1c02c541c0c009612000a07010040114000000903106403600f045403d00c400d41c030440b1a90384e0141f601b81024540884a812000549100803004c0030404034080d06048441c05058280200412034a0903819000316003040680d1000744100c403880d075648500b0000030104140d1003110140d40c59400c203401c1060b1200303403007954082e0408202c0103000003001c42c0710101c3d61400c68000030300d002d290320240c808040042c0840000d1030034442032102c00c49902d011109a9210340d154960350302c0c031300c01c2004441094203034550401d00009010403060f41041c1d42c0070910949030300040d030f2038001d0000043d440740c1099490700000b051884582c00d020038a2a00300c1580001803540d490900e83e882d61307550b003442c0000e04218650f04460034014030301c02528050182e409041d10396603182d2a0001010400c0600340074070301d00700f541500f410f043c04584982a82c403c5c0d070000d021840d000007e00f251a01c403490814a400076904498071484181d14445688504200540482d1a02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 925930530 1250 925929280 925929283
    0x3080a26011406130e1b0d0e1009030206150a05150d0f0923010f0f050a06091407050310090e0c031b01020c090c0909100807120c050906030c03120a02 66
    0x115560f80108400c1050182c1c5203c1c100400c4100e80c20010b10340d9640e030b6035001880b468600c1da620301056207400700d07444401c0e45154101c04009081c4c0741c115403441c50541c1c060015180e4039030002d009a04200041810001091042001010f0141150100b1580c880200307503243c0e0045c40a00c4004004200c0c0180c1038080d0068240d03000d0420f07800e000c3d041e400d03214560440701c44074100d202c052035040103a82d039850a4100c2c51301c4480e0300004000c2d8410301c0440002400d0122031a0300c82618205c0d01041000c107902c0392800e0280705401d01c00e0f0b10750780c408082e98554405400f84d800781403110030010f2190702d80e009034005003087e080a03060703600c098410306242c160000c000901d8621140c1140070140d1b400601030302c040e90103c805140c0307500c4070707800714900303220302090f032500187c1800800c0f40b10800030314240220341420b422078a80c55900c50211071000709440e0005c140d60440e4804008919040e13000c6500104001d083d01d84010074040024600f81151440c640c00003008110165450340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 925931780 1250 925930530 925930559
    0x303010b0f0d450c0e070228050f0109050c010f1704030f030e0705100302090d0b130507082a0f031b0406170d030203091603080d05061903080a2601 65
    0xf9900340c1000700c60582c1c3c2d452502c01c914055580280c0d07500d0009055103208001c01e8140703142c0c0020704e4501c2d03024022104480905894280c805d0301c16400c000c042d0510510408100b21b40001c090005140f11000441720314030004031050070040601801b10300b140d910300c405409140300340c5940d11509a900d00182c16581419203000803500030340c0c410000e9880d0395075118841d40395440d006070780c0c00701540002c0c61207203031100c051b001000041c05c10805203d420004110707180688116440d071341d1340303566841d51211341402c0400520242c580c03901d04d980010703901d61030600c00102003045a090382e4011070326140e0000d008041c48041e01d5440ca43d40d08051154a0290003c18114007a01d08112100e6039a01020502c04080590000001c0d41d00c0724244000440ea0848c40142c0c0c00190380d07070034001c0c0e00350041641c0d41000d41c94070002c034a081c48e107074503481e40400741e29150708080351940d00d81075081c0c2c000090b00750030b0105200442c2540510f40420300d40f0f02e414840b049540e0750500802c3d80203140c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 925933030 1250 925931780 925931891
    0xa05120606070b0103150204090219080916180e0f01050a06060f050f07210507050c04061d070909020a091d0105010c0f0c03060e030306040e0303010b0f0d 68
    0x1c00c01100b00800c00b80c11030075041d01d070091101841814a0983c0b040284a2640700e4442d40b40b01041c40101310850742400712450700d0603620305503140c0310030b05019183e513900d91000c80d204010750750811606a059000030012811b081c0c00048a200246066003404000d500c2101c803139640e40c00b0410301d031680b8420503014208034038104c4a0b0300b05070003014009200300d20300c5003854103000c1001404c201c01c41c90301900c41320140c0315084440e0781c1c201d4040e18940200404a070640680c6c42c544241d810603205100c211205200c0500090034412461801c0d03e0010303091904000c00fa40c0c020941140c0c5000130100c0c0720407540c0c0c2140385890040c00100c0d0340c4107021450510940040100056a071181c1c039103521f0758100c070025076480f04525091501c02e981c0d074801807405085c29440002c0300d0005c0b028610894040d2401c0c0260352075504c1c61501c030302c000d000e80c4100d494140640c1c2112501b5902070041142d07640b200044441c0c640c1c00c60046150102c0070006c0c000c4565401503c200301009030b01c030404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 925934280 1250 925933030 925933039
    0xc0d0b0402030f2a060c0f060114030307030e04090309090606170a050f271e150919060b06040f030309080f0d120f090602030601020708120d0c0909020a051206 70
    0xd48800109441d10900035280002981c8aa1840303404c035681c08044800b411203000450f0b0b80d460102c160f442d10b56400340300d480d512009002c46142141804001c4039015a45643c64088441a50040000800b81c40005800700601d242c0081100a980d00c62040504180e0f180c400d584201246549000c0500034146c8601038144030500411704105040190411007100301b8010000340c1b46030592019040040d0203041d4400c6424003064406901d28901c141c43c10981039585c04203078641c0c0e210b07005030203440c000340070303400720310f80056001c001c1d40d503030404600c501008121180401d00042c0a500329070885822404003070340400c10141c000950300d009150341c1c406030510248603085c060311070407185590740c2445034020030100e102296034490148504c00c04000c000c0d0303507030f80e00b00b540003500200c418a001d03109000d008180c90100250207868680051300349860110004440c001801300341c1e0846040c04440b16000c00d883d0070b103002604e8004419034075035440d2224154040000b510141c030640c0103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 925935530 1250 925934280 925934293
    0x1090f0f06050d14031309060f060513031401021b0c01030e070e0109051510022a0d0f0f0f150b0f01121a151e04050a14030c0d0b0402030f 61
    0xb15120480b5000000740c01c408100c2d110781c00ca51a860451240380031482d642d2400740c0d404181c0b603105a002000b81c52494141002868658038181d580e44110b04038034050070b004010803c0020081c03031011384400841c0c0009400c0c040c0386c9980011120000403160060380000380f419845580c580321302504852400c005062051400726120340c40300c41800707150041c0c0d8460001441c107a0a010000340e1401010b000f40c40f0038000c189009441d09011100d100d03450300d040150004070a042040c1c03000c2c41e58003e05496030000c40342c2d6090500f2940c00802c131004c8404a4440e07021404014002659a000e14641450846c000100d10129400050341d02d10502e204042c4200c0c5982c8100242060300004000103201c0700c40d9010460b02206914a0075072202811681d038031940d00c144080c201c0c50804100b685144881418140d010780610300400d07400c140d00750030170040d2841d01684030b00ba241c40903041c1ca010b020080c01242d1030159400040d80c00c51502400c0c4000c60a040001c444130a0680340640300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 925936780 1250 925935530 925935539
    0x1c0206030103030c030c0215031b0f040603180503040608090d0804110d060b100f0e030c0d150603020418050d03090503091509060406021e030717030a021201090f0f06 73
    0x12a00042c0006000c000b901c030040c404040c060816102c1d0310341c004000d0b4a41c0a07c1c003103152000e50007107500d058031212410403100c0c0c101225040e1030010203d03041c45820182045006c400500891210850401c10070a404c0042042880280080d00c0c00380c0d2401842d00c0e010f031040b031814603200c0c880020010107030100004540f01100d64403900c070701162644c00c14107040c01c0c41d4000c0d00118039603aa10007131542c192071440c1c1d008418032444030071076104e0300c0c10200e500003050380360803e9030405074000e0b44c9524044001003241008441c029030b600000645140c60344c020a0440349854100d035000c0014480c90000d1000c00c103d00000303c0e5103440c0500614905540e119101d0080c0b084560050400824000e40807144a055400d2034802038100b5403070b16603514000795941d00041c55692640c5c2441c0e00c41f585000c0c04400c480990390010005040c032200720144500c1a4401450443c000341d0034410a0b00c0307010090801c500800c02c0c104089000b074108440d403801c1b40d0340070150800e402c0c6400400c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 925938030 1250 925936780 925936789
    0x215070507090b03011e0510050910060c140f010605090a09021f031d03040e0603031e2b0b010212042702070b0a06030c1d1803040b181c02 61
    0x6007a6810b841c0c010402c10503010100b40580040003100b40c1c81c8800030a10403a40c555940320a108544190200c454581d44005010a94000f035544032a131002200d814803003103004c2c01141e002603100c0d0f048181344605e0760440078241000001c00e460565141c900410a40c034103584410780145081030200102072140c2c1c0010003058052890010f4100e01d0101c0082c800e010f648080035a112040500100103a880e0383c80740c40e688503009508214144501182c0e460800005403100c04a920514901160181c58401e80e59009201d6001d81c102d01d9207040004400b1601a2010b0707800d05c80d1001c40c0c0c07a00301c20000390a03d41d030551300d14101d9000380010010b00c054010b0b141d54000e0100074280d18440110341d100d001c0d1041e0003025081d44000340030310a0314002e0703501c90b1041780e0050450b4400c407a101d1013208200c5a2402008102c1c00e1001c001c00c86410211000d41c81c4021420304480c42c0640d1082680c507907805c4017495418600c0280c4c6040501d0034114107125004d140ca10403201ca1806039070004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 925939280 1250 925938030 925938043
    0x30f0f070f0e040b03032a0c06070f050c120303151005070201032705030316030911041a22050a0b0a0b0d02131502100c020601060e13020d050402150705 67
    0xc60400c800302900c0510358841e0303888130708002d4018040e0380d50740c802007010845407001c40154090800d1400c00000c0d800c4004244d9000c1e501005224a20300f04480e182c801c1e00140030343c1c090364140110800c40c0f0072542c1d86281b08800c5012207025544900c0c00d45042011039020419007402000141c2d54810690340c008220344109034242400152419a42464884466046800c0c3e4000e100c0c400391000340000000a140310310b040e10321003030540e0b9081104900360b40401c40002c1030320b625220011840e01d00380c0c210704100b07000c1d005081484400034001401d80318210101400b030f050000c0d48100d00003c14021182d001051407020300220403540046444003403184642c0d200b00c10301084902500d20180c0480d60001e10782400f0605489d2180c0145c21403040980c1c0e00000b40c4a000301d1500320708054050440303520311940180c1540e80c6407410a8034401c2080002c16402030245814501014461004c1c007035004200d4000030300c1d460940305200702c21071000d8130440c8600080c402c03880000e1001459 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 925940530 1250 925939280 925939307
    0x1090501050f0c1014010602010b090c030406141015080c0304060b0324010f120f030e030109060504050a0b0c0f0d0b0a03210e06070b0a020f1e030f0f07 67
    0x455035510030001d10803503030080700280c2280e402600d4140750001c00903084800105005c529008190341c5c2e0701c4c401d9080300d00e504202604580d90f03d0000c1e114141d072201441d0310030300542c0e000c14410300c0220102800312048540c0c40d02070310818401e001ca03401000110035062542d08024695060442c020f4005000080008100940b5842c209940d07403003d100180c0095500e10100800c480002c85202440209000e9104408480040050f601d0000000303281d00f42e030011190039070300c21039440403900382070072401640d0190348415641c00001d41e14884c00d0311581c0100c0103450b643d240361601d140708001c080e00e4030644543c20700002c6440c400d03810484044074642040083c1c04800c590108480c10220b80c80500400c1c01c1d03040c0162007000d40d20a61035100003a03521104007070b0107002006480d014400c000307096040d0007400200400519401031140089900c403160401014480f0002c15010000c810820500b003c018010f140421090f041d0b008078020b01c640c03031146445c031401008000d84002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 925941780 1250 925940530 925940537
    0x40b060702041505090403080412050703050a0807020c150d0e0307201c03020d1e050a03050a0207140a120206070f0c020d0510020405010e0d0c1701020f0403150b04090201090501 78
    0x15058090021071210742d000300009800030217140307001c0c240989030748000c480950b866003042281c20078142c820341c00c5403045545510f0301410304c4103545044885000c01030445055100b1110219402c0e80c0ba8828414407110410043d81d03203036580c40c8000d080d150700c0e04d800307075683d403060100c807002a4000d00080b618298501011000ca0498000250f01142c2d4600d001c0c8403070b0409402c41d09040d030206052070300f0441c03a03d824549a03032541c10314031141814062400060030030f100d58422107101e80c001540003000f034500541000320b60340307900300c02c1143c4100c42d0145d81e0000080200f00015855800000c0d010780c0050009441d224402401050840e030304c103030420652402070011942c1e1002440c19480e00320045440031080b11882900035802401220301242d104942c0000c10b2808501c118045d40d40302d032885201a1401800b090b1511f00000413407604e5400340030810400c00c46002910086004c0c1c0b800900c98204046071404846466078628060b030b00300746803035006d40d0b00b003001d240c1207a0003071a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 925943030 1250 925941780 925941791
    0x10510090609050c0f134a0c1e12040c1205030d0b030f010608010501060216141c06020f030f01090b0a06050a020a050a0507050a081603110114030a1505040b06070204 73
    0xf41c00c642030790306d6801200150b0b886c04860216900b11802a010105140140c0743c038125030303841c0340000701d010300210a01d01500240058000e00f6114090140c001c1d4540414031504c3d0140c404d040c00d500700c0d40109601c448600304000910204504110007004800f106030081205a1141c94503440b446a1500310151035140400301f58608000d6540c22031101d200070804680c07a01c2925010308070a2285200620a003d610804c08280101e101c0444400c816400c6161a98400380404c0d00068482c0c40c6c0d100f46441c500c440030031b480b4002010384c02e0003013a400d50340740303006a02d80d100b818068201d280b40c5441e00e00500707a0754480d207031244140c400c9424540d0300c41c0800b003c22880c0003005840140f007409221803610401c50001040400d41d44100d9004440030340303440110b540c4103074070039a0a0603296801000c01c08034942d0000101407210614000d8140d1520302c0400d28a9882904c91600159031034024078181942c2d21031440241c5000c58041c0300140158000448034001e648000e44a2a48e42c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 925944280 1250 925943030 925943047
    0xc111e0d050315042c06070914090402151204081201090c05070b1005130609110702011707051b0d020f03030601020a02011b050706020f0616080a050711010510090609050c0f 76
    0x101c09040716194150102c8021740302e41d0300d08076200c040903a040000319100c20008501403d01e12a690000c11018080b0751042e651902007007030700318101c410110250000c21072a981c2203c200e0f806d40c4158050714005954141301050710f40300610590090f44442d10709113507841d40750ba003c0c4c01c461031150400c02c1c4000b10b849030540d03011410000d0b80071a038019401a03043c0388184a98000104942c080441000030b9030081e00458050701c50280e00900050000c3c1047d03500800f0740c4000390300201e0701c4c5032040c00e0100448074483d06011300014441d2035401403140c01583c0d0350400908030b40e100700c04041c42c11410b0010003c4c1d42c0382c0380d1a0009051041c464510b030078204503420203c0102d42c12608548803240c0e107450194a0b4003c14868101c94000c507000505195010100028414141e542d2610582d40f0007030050024440a4981c008108002c81070000e600f07001d00505000d0344108020401841c41d001000040740c03215441001e91a040a0400c41c48040341c00c1036900c03184007600101da40b1803c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 925945530 1250 925944280 925944311
    0x1306020a0e0a270912050d0f06060e1c230102130902040509010806070f0e0d0611042d03120219060b09010509090d030c111e0d05031504 60
    0x6010007030390010090980042e1404040307004030544898111903001d502100380e049019200405006464200304c2d22000e2202e52151004102040c4881000070310b2510010340d43c0c0a480a44d4040e0300010b1041881d03403000c1c5407130f2989249048121030840354441c4a07554076021241c496046102e052201100710b412254290126011400b50250309064151550300c03040c001c1d00070380912030082460000125110400040d580d02403e0541c4604403031450104040f51a44c880440d9150014145c042800005200707014159070100660040fa40321070034141c520100740c003980e100791400c0d100c0420b00c501c05180c1c40400740039660400c0328003482d8038480005900d8128010303110301c80003140754004402d120490340501c480410495403c90166a240c0c10048011803d1b80c1c14101c54000e0307106034271014000c3d809003484025605100c6482080841036504090804c020b8000c900301030062215034100c1804080f8000e206802e101c0e0440c20b10250201000500c00007290155903201b55601c0c00450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 925946780 1250 925945530 925945547
    0x50108060f10090e0c030703060f0e06060706060308071109090a02010816090807090203010303030b0d0525090606030f0f060303080a1515020c01141c150305010e0a0302151306020a 79
    0x30680a1306402d09050030184200c0d40120f9130344d00064035140000c6000c100c0d5020308001c0b223004540b144180d40b1010200b16440d40320030000c0394450b0340c9440002c00540154050070485004149910034024480148801000018503494058001c0ca12010040c1c6c0c0100b11503070041c20890007041444031090042d01c0d0f0f4201600808030a00c43d298001a40c90695002581a288a95002d0114801100034010100d55400c4010055000b14500301b8020564003600c000d105d551280c120314075940d4490100c03c0b600c894120340d002981b64860072200c80c0440c060b00440c00c40b040e03000c100051840e1001040d00e940a003007265425102c2c20085001c692440c1c0c4034001e040300000350701c80b4883d106030180d81c1c0c12810f0603542c00310380d07018245001d40d5500015680308030a4000c802c00c5c10442001450000e103603104000108403044280400800e000f4400d01c604405010002e088102e0349040103843c086910b8030f00110075910100700580d44068200000c00d45500200168980355440b0b802d0b80c1210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 925948030 1250 925946780 925946789
    0x4060b1b0a02042c0102040b0913090804260a020a06050a0504030c3b15030a0c0306051b04050117250801062703020d0314071b050108060f1009 63
    0x1400c05050100c02c00c480c2c05136502142c20b2842c01c0d000b10312000340803803d034000d91003080114801440303560600e0800110b1030414507880d200019280700207640d00c214541041d08242d032080420385580148a45112004401b0007484004241403641603001a0758103403030313004450070000e001c51826803007401036060b10040e542c03080744001141c1c2ca4940000440a155080541c1c05052000342d85210540c41d50522082040010402c01599186180c0b1f80c48002c012409415106e180300300c0e03006c83c0c0220b0304600918482d0001180f039040103228000010351400b00300c0c03040c000801c000c01180c2e13000811705048030b0110104070880d546081507402024901d000080302504c1170000c0784800e9030300c600228141c6019440310b4003141035541413140880182c900d16130445100c80b00a00c09031910452030101c1e01c0c8207140c400c10b00042d07034460144035000b9480c122030300700b880410554200080499600989802c1c40c0410715072404c807000401d140103800085d80154510108000c2181c42070107d5800f41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 925949280 1250 925948030 925948039
    0x60d020702011e020c01030f0221060d08030f06100503090307060b040906050412033b010b0604180507050304031e02011b0e090c0415050d06180b090604060b1b0a02 72
    0x152083c1c802a44510105d00795600003460280308940c80a440e1095640c0c0700c4a100c00ca030a26140001c0009886201422280c0c1c800303106003008000034100d40045104440c100850b5185007001000e107e10f68200341051401e125050040050040d00041a200000c1c1c02550101d040c2c1590000f10300201a01c6201805160602081009001b07043e007940d1003282d00d0b55800c1207441d1a0305841403400c0100e00c00000d10a064103041c103041e05102d191002010100000054000307108000185d5a072700036440b050301700301d061440035200c503024415107602484900b0210314610700fa5034010003a0510f008509101e5010054041c900d0303100b584180625030a01141c08049060307100d0103040e080328803007245c0c031404c1c0c1c80b400912500ca14400fa00c04881c01c681d0050f1b030390307a00608203032502c0d0850500003641a943d0440001c1d420070012141100e2440300b6000038039a4225811f1140380900100f04c140140d041c04400c016103c0e5103c00c40310400103d110800d05200a000c980303060404803100030f50722 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 925950530 1250 925949280 925949327
    0x100c02120d0f0f0b130543080a150b03010b0a020a060221130302060601050703111006090e12090103021e2101090504030906082d06030d090302060d02070201 69
    0x82291941c40b444810303004171401d607034600607224100140c078800c80301c1ca90a4082e03216200307114400d808609028001100103407003424648000340000d111088061070004101c2e20601c1001d140302d204080464410960f04c0e02603e05000880d40170f4801031043d03038014000012680781c5280b003070103032400855125030195501d042000450904481c0380c00c44401c8055604042051003a00906a0081070742c50380140241d0b40e14000156840e0f04030103019018003120031221036168405005042d0030041030500010954140302c407507030441e000122042d0090b07001000103001328190105440f4030100034600541c1c1c964032100e6001e0021107990f2054104400804c062641503c0d1404000502c508889800c40e40e0303a841c4100d60646100b5207014000c120901c505118442c8201d40856001d1a8982422650455800403016034a120340c0340003044401034050207503a28080c0f1842544140d58a000088182140c0015581d0302c00c918658107a25800503d000840e401030070807209080c10706440108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 925951780 1250 925950530 925950551
    0x15050f07051519021e03130c08061603050603060408033601050618010302040b0d0b04030207060f14180d0212010f14160309060e0a050c03100c02120d0f 67
    0x7100030b0141e884481242c070305500650790b0320f03962083d51702100c030740f000c0c3c25800380b00300544410399480602007100c24038000010782e020800449070030001300420001442030b45040c1c1c07850b4004a03010110901010300782014894550743c00103010f500541c000107070719929115010740300c3c1080c0507003400c103e0909000141d10a51419009011000021180248003a43d500030800410700032413808141c0d5540d001c001440542065030141c0820703600541141c00c000c0305a00d503100f42450894084005038081c0e103042c00b0040d4081c50413214000c6c00d0501c0404261308541e824203074090b40c5843c41d2800c0408048000c26540c143c007143e8110f40281a48504611410215000e40f016011400b403032800c007000c0c081da192103032442d03a1007072001a0b51035849003500a0100c1c06820414401e450303254850b5020021003500b480340850140c07080c0d004080c4d10402906050900c240003004084a0386000c4000c14076540109000c4801d05211151f25a5240e0840a040c01001c40d038880541007440c00300000b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 925953030 1250 925951780 925951813
    0xb0d030915210e0c090408070c0b0309150402031c17070203030402010f12061a09120606061605030f0f030609150f010e0d06052e15050f0705 62
    0x100780c94a01e00e240020003100c0d5002c1e00c9440341e040489580240d800d44440a50318141d025284501c403060650b0005410b4000003012038100740d5098921b1540094103100300520301d41000010421803c0541c258038081002a0f00c420418084801d99507580d00018112754040c8560800c4611707010340407204902140b0024102c9003001d4079400c010603100c0101b070040d030000054910a640c16920f030440c1004106086030710f02c8102011012807a00d0707000110700864000344000016221064031521365080380d04011540d151001d40380600d4201906005103070321100c044442190b10501800b1000a05241c0680355102d1450344064208000c0395088001c01801c0007140aa101200c0c000355640f5440d8003144040d0140b82569405130740c1c0410703104154003038407800711000002030494603000000c2c0c54400c152142122011042e40b40ca1810b003201ca00350300c3d24900d104242440d40600c0c01d0074414a082d0b0b12182072060001d1081c041401c40030b405504085901a9070b01605440c2446070074110407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 925954280 1250 925953030 925953047
    0xc02151c050711060114031e19110301061d0126061303090b03190c14040b04030308071b0204050a02070f0b07080a020c06130203160b21190b040b0d03 66
    0x10341e03034003c41340002121041e0800d845034890303004020b4400e015108a106c20610800d485c00e1259020f4466051915000d43d81040e00c158000d548000200c0030410405003180c0049e0000210b007203031100444030b04800d0311050703810340c5c401100c3e0448403040218075080002449180718107a108000401000c1c2e0960456800820f00c43d03241c180c4d0307007526200311501500085035140031050355140f80300e1916500f500000d0709036807a0b00f014200188031b021940055400351f0407600341c81c0c03070000d420020140e005e40c88640c4043c15280888002c13080295005141003074403000703489151200301050a2440700d0381140c09203640405800c203038074080e1804025400c8100d586601068111001600d010325038002c0b210a585201c000c0c01d140d079103000d18043d8100720202e003039030144070728040408550000800100a000090910398856820750f00404640301e03641c911001c0f20048405100c0d403031408840c0020409100f040100c0d5034106c3e078000c1001072a101d483d0941c0140f82c500c0309024550440c068 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 925955530 1250 925954280 925954307
    0x4180f11060301050f040b040e0a050109110307060c030302180d111e2809050705030a110a050414130204230906030c06070606031211010c0c02151c0507 67
    0xc003100544100001c0b80800d214894020300c01d000150013a2905601505049600600010301d40500c03130031807840e088003518100e426a644401c040f0621072105422214840200c008010290030f0100007454451120302c01024140c002c01d00b1a8021160038040103584400f62481c1d01c03030500d45c10001742e09440703002c0150242c1820320b01d079042151035202d6446c070900b01401c80e000082c640340c512640c900c01e442001c400500d0303000300485e01c07041c14011309000710101d03650380342c40e13040c031031080000c42c0c42c000c1c10038980c048204100d00301c80707800106550841d01102240c0040d502c103407010403204511441a14440d41c4001400710ba81d40f850b01540600449424000824024500901c41806400c4e120b041d0b059003d88084d03d8070385803c01c014090588600401301e2515943c1d55114641c40c500707117545010410303070441c50342840c0c0244600c0441105601e0042ea262000e81c020036443c240d0301c841b40400c1c0b0400101d203070340f86c1500820403100c8503910808204514000350020900c1448000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 925956780 1250 925955530 925955543
    0x90801050103030c17040902161203060302061c021e04030c0803192d02010615110316051c080618040b06060f0f031e0105030a320607020703020306010816090b04180f 73
    0x26003040c051190cc580c2090301c1d40501041e2904201e0340912a08084032030001602907020020b00414841c0c4c0624245150a0f44096503140c50075803030310a001c803000c0c1d00400d540394014000c1400c0d110b140301c010810000d0b0b904103540c0c81c407000f01840354414241d2004003460303074040d6a0318103540e90562020045850101e8900e04c1004035a4040300c1c1c01d149000d156070658014051451041d908148402d84103100743c0880308081c0e291208104298a4100ba240204181d2000c0020f82c3c10150040e002890b11aa403d101d54501996043c40c9424080c0c0040e026150108811400714900401c44070156400c0002c140c49141183c0d1403085070500d80d11802055030614000515804c0000c8c2024650b41d01269087c4a281700c00810044961110540049850280b01c03001509200348140350141c20356901500f281801c1d0700603d0b28112044c0d000407500c1e400380d014200c18401c4c1c00149000e81c0c200440114032804c0c10070019000e0052a88a8002d00011810070805c2281c01c55581c3c011a00c40c09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 925958030 1250 925956780 925956803
    0x2c010e12071a040612020c070e0f070201050a05071d0f0d060509100605010203071514040f050d0f0e01110a1a150d02060706050406110d090201090801050103030c1704090216 76
    0xb03401180381c3c02648228004900c000d003030890710f0003154002d0b000c010308003021900141d80e200d030302c0001302d802540d40c0c401405900d014440e81c00d0342070107201e82c82241580c0520960610060061400855416450400c610b10f13042600d01d1741c4d00114900480d030020001054050300b42401c5c4020141035600b805284103290014200807d9402900304071601600910700300b000319140c3c1900b0491014030303002c030b00c1d40c0e9445100d4000c0050007294003030b0f4000e0340e0124070041c10703181181c605203900c070603d402c0c00f00d107081404050b0340c026009180c0e01002c2c40c002d4206020120303280e15000c0100c8009200641c25138007840103c076228401072190018041c001041941c0788140002580e00030806904040b0800c00309011072080c1e000701d50090701c1000c001440d40c680008010a64100c40d5101e6069a1500380140c159070303000300f1850103071042200801c0300d549941da01400c5410410002000030002061195031581d120090354000c0000724030556451480440440c0b000b16046001c0343e540010b50f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 925959280 1250 925958030 925958069
    0xe1003020c06060a03020307150e040603030c060f0b060316110d0e09010b1201140d0c03050607030b0307050f040b060d090305130819060b0604030f0b01050f012c010e1207 75
    0x803a01300302100d8003e40680341940c1000c9d91103511100701801d03481130060701c0000da03806443e18410180150301035618100e00140d1441e00e001601c1181c1c404d1103255082007242c1c2d400c0e070303515011a6008880e0000042c3d1030808014103071502d200d018001c0e41c0900900361018511504404144503454048a00c0e0a176680c85203030040e81d50165410110301000038000510012440c40100005d8100c01030400190840f1981c3e850940b0b104c2e50411075658000360280104140c150250b450b00110171005491000d0070400800d801d421a098900d01c5a500d840d4100f5407a1110822522300320135920003444122414203010700150310031908007103491552100028441400315070b1505102100f07069596034012178607040003a011032001c06511107000c120020001d14800c8900103000c0c41350703000285d0396140100304085650800320942c1405200708000c07071030380752900e25142d02c29100541240d45c0c1c081d090040350307100007003600f04d0b8120055402100024000044030022508100028905071069 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 925960530 1250 925959280 925959289
    0x301050405060111070306150b03181009051b0a0810090b1014012d020109051c0f08090c0d060509010b120703080c030d020412110627010e1003020c0606 67
    0x10f10013415090f00700d041700384000f400d00d4000c001d0340314442c80803c0e078040e02c4e0060440c559000b0350300054a54000100d01220354418008805510a404010803000a07961500c0382c071044001c07103504c5d01c144807402c1d184890b40e621864401404010003129200425140060300410140100361400b03114132002990006440071980c0035945081050300030f200b0a10015201c005001c4407406504112605103a40303000c00e064a205203807456070010402150b581003050a01c40c544c0c41c03c9680c1d000b40c0081c484010740020b80f07000d610704517282080513a0b0b0380546c2c0c030b4104407141c1c0110303a112061032044070602c80a0f40110340105010b000810622050718104100c1c00100e4803005525040060204040b60201c000703003100040038820789282c901107080d401d003203a00c82e8104c5041c000310300c002001400034400305200803200503103409140c8101c5031103540301401d0641100ca2036a078000140041644a00b070503030008032000d42445101c03003001d20050060342207148030070308a100b82030008116240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 925961780 1250 925960530 925960547
    0x50f25120914150306010e040f140a021312060204090501180509070e1519032102010612060f021e18040203150409143a170a0b0d0803010504050601 65
    0x500d03282041c590f140c1da000c11a0401000c09060100d842121610b5860381d0041543c0035030f195070300060f540c4803244524403004019140d05080c0740f05000c101d03072894061a000d4103845041c084012600e0146c50b260b406803196800005005051400000310020740e40c4000d41c0d000079421082c0400e5848040c01c84d40c8203050710075100010f4029004c211013081840c11072084240141080004416006504070b1200c8a075008803049080402e40c940c1141079070900700035043c1c5c40d00c0240314444c40c0600359a203600208002404107540e0391001050300310b65904031003000700f02c807583d40b07c070300000c03200c010140d00b11212070070030b81005071248011490a48220382c8503a142900340140c0e100c0c044d0a22004000542d13084400141d04a90034450340d004110300d1241120500e01e58000603114007806c400c04920281803e00314108103910380c80150005030000d03480c41001880c56169643d000703180302070000c0000b40c540010141074140c0502814100440c1610000c2d10b0500450702d40c10b004440a42 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 925963030 1250 925961780 925961819
    0x705120307031a0d0602030a0b0306040c061b0b19240305070b071703090a38130209070519091401020303040c0905040c05040c0201090c0510050f251209 67
    0x308881c699100248651b4040d64011300000800204c288003000820f1403d032050b607043d6582e4a1000040041d01d40c801e80150604c00c40e0700c0341c55100d81855880080e1040c015000d10000000070060120040640e440a00809014911403120030403148900300090410301041c3c074203024000000c02c0c016482002c40d003070103510500a01c41284c44202010f0640c10140018809000760102607020401b1030364008900600350008142c01025000300e68050b40006101405072000c40c1c0400c02c0032411110482d20503601540d140c203195484020881e1070b445044200c41103104001844810140c2c0700164106440c44991024195200314006a940340011900185040001c1e035007400030720200d41006030807603c914410302e80d880c2c4410020701554080c1628000507952410600d060202d000002d500510051320b81c1d4543c01090071004186215003c2c0091182e4000031329440c1d208040c9000d8240108511002542c0d0356852500701c602e0240b1109140014400c0c11b8040f400c43c450084884002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 925964280 1250 925963030 925963039
    0xc102a0c1703011401030e0312010e1504050402060702010318020913140303010b0a1206050310020711040501080d180b0705071511030a08061c140d05210405030705120307031a 77
    0x84c0480c001180503142c1c102c1882a140000d01410709485006010507020384a00e806850b2940b4240020390005d200d102a072038403890030b09090001588646044462503074082ca4081000e20320150640900d1388840b10094206c0401e600b0080f01c24860302201182d98032407070034900c0300000c4500ca1580d0740800c2c01990b803540001c0282c03d0106003d00520480e01c2c4034100d0219241781d542c4002403c0040508802c0259500000e0000c1004a0034842100a103c1150100040c1d41051710080c0e94100e04c0300501c00303000c094040010f8040750440480010800c0e051015621700252800c00d403500c00f01c5c841c00403845110700510b520385000c1c69254003042c6800000f075060115400048840000144c000d9805c401c07828400f1215251002c41854800d000d0458041030155103500c051070443d003070850b8001c0141c14422a198080a6040304c2000419004035500f85c0d01d403401c01d9811841860801030a070310442485089913141070740074500c80c003e0b9842c2009480d40e241d103580c0d007800309040800e034230 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 925965530 1250 925964280 925964309
    0x1e0901031d0715020703050709060501270605030c0409090f0c0509041a10080d020106062703020d230f01060e091f0b060f030109060b0c102a0c170301 66
    0x66000343e00348100e400900c1110031142d0b407a02c409042025a81101e03d24544a540900c4656000fa0006400041d00b00003914100d030460394010340510b16000f071804001c000004980920f032440e0655025184e010320802211070245010442d481c0303940d500310748100001400061910703003030082c0e03440395030424828024041000c1980301c0040c2c008007100d0039a02254800b14017200d042040c06111807550b00000765a9007041c1c0007514069518420032524030800340104000c0b0100c16080d03049076410b0305c0028070840d540c500071503060b580340051003ca41030450341d503495217000602c00009116040c020403440f038485104c9812030404803041045a4840381c1c00014020b0f40040d06030400480080c0020301000c40c80004075594070883c168031421030080f00501c83c140140c883d840c0204640c2c80c4261a0803000400580c452171480a080105c036078540781003216204003103801d4482e1030a941c61003d0000c200001030a027622403c4140c80d024101c012807203c0c500940101c80c1a150707102100d00a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 925966780 1250 925965530 925965539
    0x30c01050a1d1f23060a08031c09060e0102070b010f0b0909180a0b010b0c01050603160e2d0129031b090406030b06030d020c01090302090402061e0901031d07 69
    0x140d0069642500380000e503140c00000101000c81c1c800d1681ea0010080b805150030301204100510140e50080030140e00200b00c58a20275900e0950002000d80010b001714800c612400c2ca00300612205070704090130f500014288040103900c1008070f0603600040c407208403054070350000c0005070240c801c2050b040350300000803884070030121074083c0160340c11000f1101401541c0e901c201c485503080c2c0c02404514408146007010003428060315500202c00c0d00101040d003030003a80700d04541c180748580d184110004001c200a2061140d450001040110358803401240f01c40700300340816000d22811305c415600614400e2a1400c043c15076035101070001a25065444d004c01900340004e05500441110b138040210314160b0f08c0383d015110056000341010303412440e00c00140f6081147d044108002c542114000c40d6040c3c4c0c0045009007900e4068a0b0b0b0320143d901c170b2001c640e46203e9020081c901500d090780304162902140300400c0408401c2c0d8062102d03c1800003107014156000103048080e801c40d0b4410711 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 925968030 1250 925966780 925966813
    0x40201091217070618051606080c0313080c07081c2c01090305010f050f06030f070311010509060d24050312160b042603071d12030c01050a1d 62
    0x35540c0c0210b40003d40511008581c14204e032601704100c5068000178824000050070070584030003000c160905d002645080251204544001817000a10413008902c5c00c0901c402c41040d229101c042c481215503031a120300740c00b90344440395080001d541d0f101a00045000b0700c1020030041d002c401245060300030710411060a00e030340ca054105ea0402c21102c00c0040400d20034082d07400c0d50243d40781c0002e29410540010301700c420000300faa030300a03401840004400580019030342c1c1281e41244002102c00704040040341c4510402c008590b0100c40840c0080d07489556502c144c14000028042403c082d01500040584001500c183d030762541056002c80703003100381c00c1d0003800408000d10390080a60515075914075000750907142600c1e20044035000404a0205400841722020904030a0b03003545841300300142200e240d1414542003201401c40800a61030b01d4807001095908982583e071038034940e40c2c081d402024100d80f007410080c14450006120500341448426003010700c8007030500a0704280018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 925969280 1250 925968030 925968037
    0x1302090c09210c0a12021e0d080c120708030f090106060207030f0c05060c0f0c010c0c14120f160b04030f020907112b0314012112030203040201091217 66
    0x31482d60056606038000780d82c43c10894409041e001690196840341401440303034400052442040650303500c891804035540f250b4860811a80c0240314560712040210214101030f001d909811018001045640400207034002031741c40351040c1c1052101c0d5075100c2c2c01c035a090b01c11900ca8840035802c508814004034040311a0342200e030707004911144801c1c0e5102d000c1a0258854241004240c224224100d8003400501505007194401d20302860407148544580c000ca8132140315000c6009500080e01019440e600b0078404081e82103002d84010301d000d0b88070303a0b4464422080110090181000c04104030f0b07509810b980a590b00320aa0300030100240d406e1145600d0007500d00414402008540d451420040100310300c2e50b80082002800c01d00d00c00350000340e800d6440040741c1854101b0010010b55500e100041c1e0440320117180b0f40e14006441e02041118401c0700758041c1800104480074140507070990021401507200381e072020b004543e103051658401071855001441540c00701c01200c0c0036084180075 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 925970530 1250 925969280 925969339
    0x15020c090f2406040f06090602031e160f030509040c08090703110303130308040f050618011d0607060c2c15040b0703080f0c04030c031e05061302090c09 67
    0x840300d2804100002421a0800c4d0710040005172207100910080360f00150940c020140c46c0019410002c1da240c0503511441c042d0f0900c9020706020900030b0340401c0015101003425040307000d694012815060003042e962011a03581e020340e0034041950340b414403031645244207415001c080d0038001e04681d0f44a4181d03404404d805e50620007800302c07448032802c0407241c100941c8292982d550f40d924120300c1c0002140c071984094440d03141030160b222900701c1911080040c04003442c2005010041c030540d10b8543c108182501c1e00200007050f128104106a802480303402001e4031000300900005881014004680c060001c00b144610350384459400c0c100c1c42c0d0200e000325003e445043c140c0f10400700410b03812040c01900020021014040b240b42c14051540e040307510520691710307090664032402c040000754400208860b0700c0180407400c041441c4803000d1511740c494203449150411a07681620342d84110000d0348100c103204003080030018494211025540060600391100007100125880111301620 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 925971780 1250 925970530 925970581
    0x30e131a03070e0f0a09170c12090105191206081005060906100309050304091410080706050a0507020406030b0106081b03010e04020f030106091803090f2702120115020c090f 76
    0x103480d0b0001306c8410825100c41150800c1d2912001d14a200c0781c5402c40c240a03042720f00c001009100d081e6680401260b50000d0892180a444030082900701c0f10781980007000c00c0c00341d207060300120701c003100032902484c580c00299081c003071a2108020000200b00988907143e10030181001d400d101c42c026041030810385d00640580c1d052540c0d6000100c01d903000f0f4030340d01c805004490100104103515819502c00307803001c0d500a0030490b003040400703091813041c0c500d54801e016000c0760000440da9036030440c502446e84410070402550b0f4500000e07044c6041561074100c02d05000c02d18000c190311100c2a20704881c003c0015400540301c5400380281c1403200a15203806540340e482c0481c4085442c0503105c20f1070002005108503441504008229608a800243c90301c50b0078103003045921500c0030520300c00c040c1c9507109590044050315120013881424a0b146105401340d00000b503d4505110f0007942916980035205429854010031544034011a44544980c03544400308581c521030b9120036125140241 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 925973030 1250 925971780 925971791
    0x20703020405040308071107050a14130c0203040825030210020a0605101e03050d080907032f06070c17010e1b19140d030e131a03070e0f0a 61
    0x401090981d50102c1d0f0a81c0891040000d2005099100340f850b10b41c3d41c040405040c10509040c002141c13001240724140c0781c24000d6a42c0003560b0f89200d4140e1b6011110a0100b001c54010240a03450743c01c00d01c1890b005014081306240903254040c0707803420b140c03181074610710480e0441d801c20082e0380c501c074540c00451103050b109400003491031044134003860151030a42000b40c5002d1000c100c6007400c8900c403a82812110381080003c9000491491208140c14180c000340c0ea80f22005107802000e40c40504102c403040410588103607600c0700d40c442080c0d1400c0080741d115880043c80310503c91010700900004800c0820040340508504c16034920100400201e000d030026a00d4525240c290b00c0341e245200e40240c8800458607003610300524100d503131520540035514103005c0032541e018407868107020310381c418049402c05105800781c06000d00018070462050224080e0400100081c41c5090201c26002d134080c003451a0000d014003c5640c040b0380d280d001d5a036010100702800c005488219041d0300c64 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 925974280 1250 925973030 925973033
    0x211128110a030c1703151f0203030a09020f2106130803060d030509030703110f010c02010c12032007020301060b0412061a03030f030f15090a15090f0213151707020703 73
    0x1400218098806d00c0b410703008900744407082200e54001c00500314803d0032020360001140d074000c8280c0c4d921030200d40000604a441d40041152450b0385c481465211606808200f804030701810041500b15100045aa903035961188040c501540c412000e000100300348000703070151516010841180d84a45000340c10300d44640d02203440d01d00240c004842c00001950000003606184030a110410024a0001d200d080c894002a00c9a40442c2001d800c0b5035a07494200100c50081c0c01070402c041c0025041000340781401120020340e00620f104034803a50a220b00040c0700a0054141c400b03541d82e04120806401c2642d46410050144451810b00c2045114050700565024000391010489081c081540c0703142040b484000c0c504002e12010a49821120345509512848030342548040700c10400640c0c5207041c1c501e211a0225035010b201114200750142e0008404c1ea0064509120840900c840d240c0e00d60000040c50740444040b03100013900c001c900c2101002c250741c00c0350081104d0055802107a200e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 925975530 1250 925974280 925974323
    0x307051b01110a020c09100302060403120c05060f070216060e10140c071d01060c021c0615051e060d021b0d0513080a03211128110a030c 60
    0x98541c00340582c001c074a80f5181790501500701d40c0c1c414542000c1080160440c2e00003490b50041380005800c41c0303010102d581000e80503951003400d064002c800c5030310a1424a2903c0c46140c0b003107401d00c2c010300600d075010b0784111600c3c10480598800762942c3c4045828813050107412060380410200f0007407400744409080d000f400c0204041810100030381130450400344502000e103440011910801c1d14500100419540b0444440850b94101e030130f00302e4080c0707042c0b420300d44004100c0090001d500e4000009514171200305140c7c2240e806407075110341d01110200701014180c8410185402a00030000c00b440445150300814101402c1000c5100c000001c5859520300780000c0d080a02042001840301116603101402d40c0c000e1070755400410310f0f01e1965400400ca406017549180c131444090030b49c1e8145c5031143d040407003081590010709845440b46203141400c541c9000c49407540740c200c0090700d19100d02c58448414890100c2c3c00903c00602d49903011281c450324940150744c070306880700181410010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 925976780 1250 925975530 925975537
    0x201090501030b0d0227060316050f01110118030f03020a081828020301060504110a181d040b070201060302030d050d020906030403170c031b0702030703060e0717030307051b0111 78
    0x1010400c00c18a561802c5540801c8042c0c0418840d51081e035111550810b00c0d4401c000303a0b081a5924015030b02f03e1001030b100054402038205195080c40102d10001c0410404890514020356070342648203c2490f05800701c0c811104180c00040d2003c0c0012140308500301c82c0c1401444071030803101c6440c84514992101004119410301910060510b1000d61500b40106000b41404582c200201c6548506500e0030f4441c025440043c00034142c801200c84e5421807440303000b0300f00702294544d0215000c2900d09004c504642c03c403040c51520000ca0003141c03051182c68103aa6001d0020309102c0400003066a098011560049806400f0840a0b40b580c60b50300c05075020718441c3d200c00740d800042814101340c1c990028000c5290382420300030006254005200c820b111050380c01401c0d610781080c00885d00301030040e000501202d050054000c10a8000104a011240c0780c2c480b0708803640c0c1c0b00380c03074545034401981c0003c00164203000300100c038003440010301071082c92000005840d00b10200880b01641 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 925978030 1250 925976780 925976809
    0xd0b100303080604060b04090c120c030204090e030a022104030c030b010503010c02060613020a050906130e130305460e0901031203020c0a0b310201090501030b0d02 72
    0x2012140030010542c114010340d400010807201408030300d00300488414103008600ca400500d82e1111944c298442c0142e80300c104203001000309010404180354058041c2d4002d1080e443c55602e4000090101c00c0040240d07042d003801540030b81100ca0441d2a82c403030443c002c5c02c00c90030500742004000001035881c90f400008500c991240156903140804040c00c69924001000035500500300b001090703551000204201051460010384a030610344040b07565024940915410440005144580c0310b081c04019040b1450300c8041c0d07419603100f0845588800405000030042001405016054032058000100ac2092420341b105501c42d081000c07090010070095540c2c000c203c0e07131070600001c1c1d03100e011600c000c0c6050b50030704181d500d142e1311030840c09400b508040826078041000c1d0f00e5004280010241203810068440c80360405032030358500b00c00290002050b845040300700c1144000840001c40929070142c40e4a10000d18150040d000f5000e031020f120b1740b08140031559801a03490100c00501003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 925979280 1250 925978030 925978051
    0x6070210140603060412020a230c0303130b3006132c011b0e010210090201050d050606040503030f030604050106170a021309020a030e0c04050606040909020d0b 70
    0x200340003180803036000c140214000032211003005000e440000e012a003185d417143d801c140d219000c2000302e0a040032010002c010b10782440300d402c2c0e5864050000369000010b03405070303004441c43c1c4042507a00d110b0144070300341465118004120303003544c1f40c01401c84000e01801040323494498104a881c54450a941c03050501115000d100550400c0d04d05a42c40c1d052045003000305510100c604010800400780301c0c0500c0d1001410f03140b005000703401c81c00c1654a1100c17115070b0000c1c111f82c080e02a14112001900500c03c03402c40c0344040c0c03090300644101072340603150b407498074444800f40d202805d8001c01281c0c00a8041000103074545003040200020100310000e9600c0b8203140301044183e42042c0d0201c0200429158041c3c880c1400000c0c480d0082d031402e5005035211804140e407803036001305501040d0f22a102041c03641049405801228540103060180d038091400441040101d5100740c6010b500604284000d1142c510158450f0050900081481c003200280c0d0342d442c501c2800480307580084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 925980530 1250 925979280 925979293
    0xc0204060905190204060516140d0908010e030316051b060c09040b0a21060917030405060604092013061706130807120c020301060806160e09010521060702 68
    0x1040c80c0404801d01e0f80d90303c41415803410349829070061190041c50010f000d0003c0e0311605e603082124143e1607182411165098601000c1c05a40190080030341c1d21624030a5402c003035502402c4907002c0b088902c650703600078501a10000c2440c0482d1181c00858400c0c58003480c0e501c0b055010b000c208a407902c108030b0704c04607039504c00034002404291075030390542c42d0055072290300602041d846100e900050402e030804205804880d0304018015003209507001d00020f4490300c1d070002684080c0000c44c4194010800c42d038203901c4000c288011241d102001400030076030301500103101407507041d880130310540052402c88010011300104044030900c0d440500d131043e180c804540218000e20074941c1c04500e901500212050a84031001c1511683c04002d004080d02442007070321030f00030f021280b940780e00034000b044004e0b00c035146c41d41d4400b819181880542d0b03161054445151041a01c080004406420780b02e42da460041480341820b44600003814050899640301c2400030204036540c8114900d40c001c0c4003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 925981780 1250 925980530 925980541
    0x50702060d14010810020c060402270406090236070e06130602241603021c09030306080d1d0402071b0f0f032003010b120c030c0a03030206160c0204060905 68
    0x503000745c1d584007403070b0705005000400c011385012600d90ba0040d0183c4a52b009124004d01c00380352924000c008040c03814204081c00240720700c0d540300b500400d00c283e030030003200401c142d02e40380c004114950380220110009a24000f051380c1c1059030390014194145180d140c401ca1000540e06d0b007124240300d40c03001d41d04504200b115810400384200d0650300c1c0e40b40711069011031500340703580c8008200c1040601c071001221401803182c0d0466a81008004990b030041e4207550000b005004032400a8002174200309001c240c200d03010401180a1055031501d4140c1101c06c0500c03c00482c0107180550300c00c0e400c0c0050004214810490395030031460400d00f41006040c8403d141a60211360417103420b040000320b0030710009200b02c110039103070520440c54890ba180742c440024050170051070300540180c1d40600291469000080c100f07440310003201a41d907900e1001d0b050120f001c0300352202400680c4454081482d6000c45c940c450552a5285031a0300004031700c2c0c0109080e41c031303550700940f00540d071501040f4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 925983030 1250 925981780 925981783
    0x19060909140111030f01061b020d08030f0117190c1508190b0a09240b09031903021e0c03060705030106030b010903080a0f1b0501051801020901020d050702060d140108 73
    0x40f0325000c486020f0941c10120aa940108014054041800703481140b50207128400d40c0209607541d030050000610000900c0c0100854000b40c071200c20381410000080f4000d20304070203200d40300b400403004099845d01c0c89204c0c401c11701c910806499015107502c012981e4a120182c0c0c444620b00d94982c0c40f011f040071034940c5000d80407011030640743d03880e2441c8290190f035800401e50880b03803505008144041401e500c0e2070b030120011034040c0301c0302c450500010607040d480003402c0400400c8094070004070704101e8071481e0344080d44004005812288081c001c10721030800c907200c0300d10f0003000c0700e0712202e2007008a03282000c1501e40c080402c48c0400104070959042c01000e400b00f4081c40c180031030b280b6568942030140100310401c0144000f400c01c102085114140c440c05032691060308060304074042c1010760003044240c41c140700143d0520701041c5000c1e414006c03a030121b10107038018684280c0d1908101e030280c000c0301d01264010410030140c24034012501880c03481300141201542254580034020317 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 925984280 1250 925983030 925983041
    0x111e0f03091606110d0c030e09071d04140a090f140304050a05190e070c061107050c0d11040f0f09120809010c081902040b0d051f0b03190609091401 65
    0xc410445259000c200890010072402c00d545170505100804074074a2800340d540074445000075030000300500800ca09650b00101c2e40642010480d440e031380e0f0b00943c1c0c041c03000755540c0210506001c0180400b003200032015502418078240900c03501d036104081691803a580d84076040b1611000c1c3e0005c18240001e03d03143e0070000c001c00382100c000326500318560f91043c031003680744244814090b001000602d401c1c011144c001c0c400380d2105040186260629080c0a03d03042081d042d80d840c440d00c546a0218100720a2002c80103030889180b05580350604100300180c40d5204010050689517220481d00040314007c1002080c403c0100302040c0b5840300d4007c11484000b44840d803140e04020070110003540100c812a0003120121003141198a1240f60341c002e44902e40c00000c503c800021003081a4400c1da201c03034010748912481020410340e400b0710102c00700b214019407018400400c003041c4216488021005504581ca901196103a030740d003d004102e13505800141c0762a0030405442e1881d08080c400c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 925985530 1250 925984280 925984289
    0x41e0f03030206070f02240a110c07090c0512090f0c030c1c1a09070e061801060302030a0603080c0a0308091603030c14060a0f0f111e0f030916 63
    0x810140d2454030020341e1044090584000d1092000800407441d109010442019141c110084d0708040750009281c1004000c8500b4407070546040c032030110105001c070407a8401202c040041c4000c60074002c0d11001030150395051010302404202101d9455424492544500020030240c24100105c085c0207040681000764a8802d402001c2e1a50ba06c1e9140c000e82150032501d400c21807186211403420001c588107009584400d4004641000308401001803070305c0a44800f0a604041030b1198018812440c3c8071250884e10040060014000907110303034081c50303000c40c1c2c010300802c4049c2c0d207465810255100d00100c100d2034120f1b400200c1419002800702c0d030401090001014007203550081020100d0315808003d0810400c11015014007812001c4454012804000d590031030616100400c01441c03034a400381110340c184005480014414400c41c0c00840b10f00051510701010201c00d40d1290a82300100d9440d15001c0c0701651030f003048040a180310341686c10050511096101e9500da00c00340c03d40c070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 925986780 1250 925985530 925985549
    0x5010e371d0403140a03140f0417131701150e0105031e0a0f02150a030b10180905070504030b04080301171606051803060702070303120b03060c0a090308041e 69
    0x18003000135400584801454800400c00e91030344d16404d070403005001c02c0700000024002d10300603c01d0160004142500961041520034242006a02c580400f030203401c0c010707042a4a056805c01851111100ca040804030310b00000a2608400c0310b404999242c60b08515030403c0242e00500c240d003010004058140c03183c103154624182404440d0380e841c104001c0003041c589141d040c0e8821500c4030782070950350004400b1150344425050200034024140707000010b200d03030340e8209003901c40d9004c0d440341d10700c0c10481c00203848081d050100e5880500b5003c2d1031101003200c1000000003007901c006841d401072b80300722101a03072035242900d107120340c0c0a020003012150300300880c60388081c22143c002e0002c6401d982000c54650790104990720500e03052090301d9800d80221810007540325404610101501d01c1303a26000085a001040b150403540c074180b26035055889030001c07610706018a009081c2146071894041e40c55900c0c1d0b646c090454100f9030080c072455038000010040e0f5207000842c0e10240c0076000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 925988030 1250 925986780 925986839
    0x406050a0b03241308090607020402121f05010c0b07110c0303040801020c070801060b0d0c051c05040201030e010e1203040507090e1b030a030504030605040c0b0417010f0605010e37 79
    0x803215005e0344107040c00700d80300f0390000511208544854058942c616045030601d8100e00d00b01482400071040700c2c407202c0d20b65420210220320766000710f104501c2c1a070041041c1c0155542c40c0426160000200003138800d074454451b60007a99a02040140007800c540700016071620b18080c030301841c0102c0c1e50400c808590401c64240450701085056407a42c0e2035002010400d4480f50005548500c00c100900e1ba0940c40042c400d0007800e8183c12441c0500c0c0b0030b0380e00300582030002c00764608035101134481d902d907504095401600d98080b81c02941d0070a028a0640b125242c3e0f449900c0c080f100c040502c0c105a07046450001d90010980c04017a94429044c2c0181c507031046242c5d0003d20a01c518000280b813140e644012506115800c41c030076001d05550011243c0c0d407030311407100c44501c41c10714200001a60803c1c5915803032f07041c58041c0340111181a180c0d90100e034030320010000151032510000c0002030680c03000220082e0500c410b1549112072555040d0510f0405841c01a00d200070100e2407580318292 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 925989280 1250 925988030 925988033
    0xf07050a05060703081b07020d0b22170f0d0c0915080903031b09040510090623101707050405090106030b0d0303110c03120a060e040b0406050a0b032413 67
    0x158032030307000e484500006d07070612a0785420340d114040c0b210040d420804222862040005551240d0300402e11026000340960b184024080040100c0d030740109071007403d620900789072690601400010b8a105169030074001c0c1100307150112038032203406100082648404000c1568088001c11f142d42c16813600790507030f00d09900c2c200c2da00c4c0700140c128001c9034071a048140700e618664096a0b0b031070384010024007450401e0104904521281d00689541503c1d080c000101d0030031103203c680e40f005a0a04c0340e20000601401c00035007440d0140d0240c00c2c040e444862440811100300036900c51903441e1500d645071810a000e000b028401600030304181407070301c940001c03075648400b424418250301d4500492030305040a42030085000b86480340d44980710208186080215940c1c40074818210200200b0070700c0e80c3e031718001c803070f00c1000d0f00c016243d00340f1030004c280801c0c81c03a044998482101c0c41c010a0a108580200740341034041240c2c10075850340c0b4007000a0002c8100b0700c4c2c1741c04c0000b00707049660003042e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 925990530 1250 925989280 925989287
    0x5030a09080f28050414010507230c0a08070b071e03080f13201f020105061504050a060c1e050109020907110c130b10090f060306030b011205010e0f07050a05060703 72
    0x55000706d03407402e0903113205510716a21501c1201c187c80d50106145040c0e01c0401c51a20004602010150150248213903121440c200703c103440003181c8110006114042c5403040c2014607a001c0581540d01c01c03280715404501c0020041a007031544d101e507072940158644502405c0c80c0a03405000745810401c1594000b0114a44e10680c1000b40c40b00102c4417041e0340080e002072006903404007810320f0050740010b000c0c001074065215034030075034013a1000c1928507000d80c4c035504240304500910741d01400b48641482514810004115103900c50740300c40b415020300c0e40084054014a01c4200e4007070b0b454404e442c0840c10312a05480d0400300b103003060b000d2090100c0b05d090300c424840568600861110944072a141321035088140070301c002030f101d60f80341c80c02468001c220304600e00445207140040000020130520a02c904000c890300901110a0703a401e0504500501c480303110260703010741d201c410501d50044113014007500c11407514010030000b4544030a01070144080ea01c854802c910501502020a40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 925991780 1250 925990530 925990537
    0x20f0a0807020a020a06030b030709020406140307030e030d0b330a1205092a0f10050d06090b0301060914041b15020601231005030a09080f2805 63
    0x505042408460355001002c901d0103545074406544054200d000084c210b40540c40780000140c140c003a01d15490700c90082d81c046e03204a11425000a0381402082c51041da084041c0d904600b0614001c241c80070103034140d504e943c0010310011403140c1c2d501d10303600007032510b4803217840000407081802c241300c0c0c18503030b03c081d402d50719030300c101001000000d11214241c416031112648802c00c01e4108a1420070307aa545a4902820102c14420150141a15249002148203c0c02cbc01c1c1c0013410003120318580400c2c044d15030103021a410900034181700c00c2240300140e000703541c0034110540303000900450900805007900c0d5a60f2040400503c0c0c0030a00c64600113040550364801d8002aa80c0f104c902c85c014034052182060303026050314803c43d10500d0000c4e6002c03400c14100c0720042c1603040d040c24003010340c061078185600d40d0340d80140000907a030220f600910266610410705580080d045100d03072511101c40e071152000d440c907500c00040030741e985605240c110f81c2020354100b0400c0c9155000401030112702c13 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 925993030 1250 925991780 925991797
    0x1030f0c0f0315050d08040e0603071a0904091e0227011419080d03050726090c030a05070e09011103010e10240807081603270507090609020f 62
    0x5486507009414030f0a5121400c00411000d40140c2d40c05199003880b803000d07000b5004200205540c100030801901c0c000030308405036050240c0785c000440c005d401c0f00c14682c0c0700d0442c0c56080794480300384c40085121149100180032110845c0b03451101144108806500c51982c0440c0c1d030710380c154106c0001c6501c1014103064170b001c0500c51001914140c001081c1840d00d201041c01190f0205020070400c1e40071a91049482c42500c1c01d000c981c5801c1c00545201c0341c130b030b80354468040d124148262041c03400c0d08035540000c01401619070758943c040100781001a49030007500c90754009502004141c808804007030b8010185070080100e00c4c0401c01c130717200520040c45509140c809600104000c0010811000300402440c2048440001d1030b0544058000c4d04002c80c40c0404e0035000024012401428014890956850030180303c44911005a00070440c5018041c014816103042d0f5400140104c160040c1c00e000304005d06082d440c0c0b001070025501150414040d10340180000708035030406200351107208 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 925994280 1250 925993030 925993037
    0x6090501050313170a0305100e04060507110111071407050f1201020d0c030e152535090102090f0603091f020a0905010e060909070c0507090b01030f0c0f 67
    0x2c0c0c5a40e455290f0002c801100600801c075032810861624a6050050480d000c0310344040c4540e40e1a10002074480e000c0e07101d14030003020084005000144207500c480d51010300d03400c124645100c1808040e08648944101c40f100250000f9080281b0040c2800a824886c50b4030040c0041410000861141e0003491500c0c0d000350b412101440340554203405880901c4503a100c00c0099900c84200100900070b1060082141e005882d10101c03c140820b0003d03210b1280c241c10034092601040b0100c000c590351545d07100400071014400754040c00c02e810901d58803080241c2944403030714010703103144140502900c507444984c81000a4a100d444251200e0303103020b812100c0a44030342d51800d605040810000d8810403086403050700e80b0810016502421003000903680b5070186540340c1c0d00558098102c1e06403076074801c4040c00502c04500d80500c041d03500806038580f081c40300c81c5a03034a039494015145c12039034806131140e9400c00e0342d5034580715960307520070240814008425400006000c1180086258041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 925995530 1250 925994280 925994287
    0x17010f1b0509030304030519120201020306090402090c0403050114150a1809030504150221120112030e0d03080703050c0301030b0a1d0703050a02091305120313061d0d02010203010609050105 83
    0x9030b4003802520f000b1074001048da0085058030081c0f190201d03680350304880510410f410114000c1c41482540d1081030301410010342619182c0802240d28001841c40c40c10380f4003080040001182805040891051122002407600341030701d5580444008410040c00b40740b0030001000484020060019681c40620000400350900d060440c6c5a108a4006d403115440c1d040c500300c11a64001441c010a40b0101100d10704001800d110400e180318200e4012122094040148038503450300e0117101c0650b102e42000540d00074228013207150340c07401a200340c0204403450100b00815405010741d950000110301d0540c5190704660700c5280b0001c0161200f20242d9444182e10107003120b10031610410307a0010f084800913637507407500c00c0d62a1000700d812406000302c0070104000d106101907034201a0307844030281400b41c8083e5036074115500011f0400c51441c0188581714007043c82446101d100d04030010048001d14100e8402a142c0401174642d1400c5a1040004103d07155001c601901610000d02c1c02554 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 925996780 1250 925995530 925995547
    0xe10090c0e0112200109061b0f0807140109030c06021813091b0f05101815020f0d0e0f03120d050615040308040302062217010f1b05 58
    0x14012036005800c03030340c51510000c2583c14100600b000910310980004400501803200300c0611a031000256005c40c3d80b070308042c81064020704800c1c035420b15000aa86d1500c041752180d65101c50a00426640c2800018a80b01441881c00b05507004545240082c032102c10140e50040034000680e201603c2c25502045020402c12106903985002d4002418058404940c0e10070000030b090b01030b03044464201a1034101e110400c282640030450f510580e002000300d00e01014440368903002020002003080c040340000540c107001140f40c01508901c00031801c800c0310030b200a8903242d500c000480b500d61140a52462075940071800484030041680c2181401c003000d80032a2801c0c0e070313450001c2d00d4100003182040304507110364000c034840c0c2c4080f0b0781400c50030f00d14034500303010744118000034028034000c02c400d20142c1801d00051464500c64421001e054402d03416096182c0c17801c1c0c00c0380c4132018400d44a43c05c603100900800d030083c448981304200001c0c100100101c41985a041d00f0305000d0040f46084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 925998030 1250 925996780 925996793
    0x50403140315120c03010e010908030112080d020d060501080a090f1e0609120915050406030c121805120f09130213080c010f0504261903210e1009 64
    0xca540c01502501d400c55444840304d840d40c3c00700040c0c600961805403a5002c01005000d0301035283c4e0003480d800c0c5181d003481d0512010107010141074404100c10007003036050706940e100030001d1507040b24000504504140c001000c10070007030155000d40d800c0c0301c0b07001c022a20300040c600d0030b80e50240711b01040d100d60081802a0340d43c0e2120241c00949003034921010300c1034004801d0040d0600e590f4070020b094440c3d201c003801035105143c00000450600c01481a103000b6480842e00c018a030501c24030704181015590241c429100c0000740b002170ba01210002c12000300291050340901540b17241c280300d01002145610301440c0441d0b48200d10050414a1a0049074100d40c100741c070590201e601103498041490362000070301821400512500031144e400c40c803c200b564151000c0440c0540040300e600807851030b4150f211801c440a0049041d040c1460392030344811003a1510940b19503030801501000b601340c5031101c0e07140c0d240d1541000d024448003500440d50b40d06540240c2c40003d1001c0a904110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 925999280 1250 925998030 925998061
    0x18040f0605100504080606010504060f0309020d020a080f010b010203091008100b071a07180608100b04060f030e070f180f06170f07030c06140d0614130504031403 71
    0x2d03001075004415111041d4810004d0080da00d070f030b904590f1684c848500450701481948601c07400582303103200074564244a60044a96180010550069488150001040640d1550140e0760030307072049900c02040d000a0150080c4120240040c5081c41900d03c007003a40c80c01717105102410400c20070001106804040c0352400900180282261521140c1c81d001c1e50220000303445213800c46040000500d5181b14405620300c0380031080c8614030062924600395044040904004204681d18038080790f844c102c00c0160000388080c1c0d0b0744500d614803661000c6c044132800d0324011069002850240050101c22244030210f8400302e40b43c0c105c140540241500601e00b01008464503810081c00180e2240080c0030b024084010b541568004840700d8481a0b640034a4400101407070882c640c20030419008112564460701000412460030a5001c1604100c40c40d42d004000b00704400c401081c1981031800c1c847c45a021300f02c40812242c20503440c050030302da500d00c1050704904000400540c42d0580d14008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 926000530 1250 925999280 925999289
    0x3021204060f090e13060c0e18060f010c02181317030604140f07030b010c02040501080d1b03080105060a051b0717010204030804030b180604121418040f06 68
    0x18240c985440e10001000480c1090302880000c20320f06001c60b94882841c901c50064420341842012810749540340005072003002a04800d004000d48035100e2611024507100c9448504444000c2038941361042101c01002a000c2604000d03940d40d400c00140c80b1540780d01080280c0300c204001d00d0b40c3e10241781c1d001003807000004040c1818030b00421544101c21010718091901101e0030300c201c0c910b00000380700d00041214200029206580499035860207a131000007191018581044032420540104041e5a402ea01540d41c5c3da00c080d004641c165400448034292803c146000310079080d41e81c0b00181151018010070384100e00011f0610403403030061044071140402d1003020040340341c12980d80c1e52269040d01c01c00c40070a070030a510748021441032003110141d036400941c807414181591a0501e03820070003021020030400c004140c545034003080000e01d100f680b00342e108400324400030400400c40240401408042c040030300c144803034200104103c1c07034041c50070b540020b024100c844c1c0c440c2c0a00501e520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 926001780 1250 926000530 926000563
    0x7110f060c030301091b0c02191e05040c0201020901020303040b06061b0d0f180608061801030825020a060c020d06050c09030c060a020c1e0a061214060a120302 70
    0x180c5803041c030404405036049071034400301085030b0042c8061610248403100c14a80020740c080c1410001032610703040300402000b8a013408040f20351102d0300619601840d500c14807107603911071010000362406000d16450905c051000f0b5040c1102040080e60300d02015000074000f60b00351000a241c3d03161042500e8848102400401209401840207621282d242c50300d14001035081c80d03030301000d9001e000200000c20041c8444148986011012140248041c181d11b81c4010740c122410242a03800d2000c9010710f01450940d0346d220344500941c40e05c0344450380d502e4014840005108007503512820741c40100c4d6000c0c00d20000f031340d030b41c0d10000304c0107160034070003e000ba1300e442c081c4002204800e01070165000d040e000c41b14041013034000c00c8000c0c00b1740b4066000590105a050100c0c0c01c0040c2d0626400c140c8001d814558000d540000702c07841000e40011000403102d43c0d8451500340c95014885a050b41644007042a05140c800b165418a0382c0c0210091100240c0341e80007018801c00940040b01c0c0c4614 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 926003030 1250 926001780 926001787
    0x80a0f240c110c03120a0f020a06091a01060908070e04021f020c011101090c090e030d0606170112030c0809011209080901090e0f0114060913090b0c070807110f06 71
    0x50040c141c182c9002d00750905114982403a825410002400440441302e94006410a0b14000c0100e82d000c04d40501d6008502420301c03c100014030a0044000c0503115102820314a1035000314009001e005034442d40030000ba46204016600c4c0100710401030384d14001d048100e035511800466180c41d41c03140940007074000b465030141101e60204100707006030000d81c0c41100114101501500740c80b60604090501d400d01d000800035075806907c03a01c202006042070702c1c00c0004624404044508079030000000c03e007440c0009050317420b11290a8007400c12403610701864052500c005000d80003030680145091400511140e041c3c0c000c0c3d01c144140c0000346c806016107003070f500d40000340c9d42140c041c06004c03031741c22400890400b50b000070a900c00c1840350000c3e009680f8203950403e41d0340700721202940002c002c12031505944c45110164980100c02c03580415034032842d1030403a9005000a050b03d86080c002d00621002517405000c4650264101011104000c50000001d00c0181c1c96030540d98081c0001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 926004280 1250 926003030 926003051
    0x80304060212250c2121020306030115030807110a1503020d14011d0c0f0a0503040203100608030702010e04180b0703051e160210180507080a0f24 64
    0x3c0000412414030000d0b4050803000401d058580c0800e20200410441104403000d00c901440307040e12218140034545909190015400e58802d10300c1c401c0350742ea2942d00007081007540d041c2401540300c107541000c03110b4406442e41d11440224007a140004224255908401000d9030f540401c0b034010b4210300c04000c0055400c0750001d0001c0d40048805c072803c509255646056180382a40300e8101c41d0441005203452810220208e00c1070802010003016000070702c60669004041380240c0310600c4940c850039902c1c10140100352428602000440281d13040c00f9082c802100007109482c100d560a0802c00e03164000040003d016006903548250b0551121503244107111800e62036074020b40b00341e10100000e07110511500cc1044500381c948002c0900c51010a0785414120300248440d54144152003800903d024400141c40046010741202e0f29019500300500c8401d10080000b0450b5600520a0084560715558410308010000e4540e53f4458080401540c102c0c0c103a02d00c542c0704880400100c0e0b00e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 926005530 1250 926004280 926004301
    0x30c1e0207031b030b0c0304031103120103050609010e030f090a09050a020901110d050a08040221060613200f0c010f021306030b0f0405131e1a0c07080304060212 71
    0x60740b0040d5a0380207491220903007081442046010303603400844941c11a03407110001c51082d88007a00442c10440030400029071031000b800905034000407201c80c110340c2c0d4514104a49092809800003409134507000348000700c1d42000040702c04034918044600d450b8045580060081c0d980344d0310a030249810441042140ba00703690081c10040c0307007601d49202a80a0303140d503a40e140004031038800461410844209001d0042c450355900620080004a40032010000c0c0c0f104450300c0305071050b0550019080c091613180818143c1466035504400300008010800070b250390302c0355000a003e914a001442c268500c10f030100711444d030000f5038000c1c01200c0700e26011100950110f06030607040402607102041d524400e003e0003000190003401c41ca103011a010401c00207140c0680701c000b0720141c3c1c0c00b0b100000350281828a4140301501c02e8092a403141e42043c19480303c02c144401c60354003040c01003160400c4a5410386582e41e40010700139840e44e5961038004001e20809840c0c00c0e40305800c40400480850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 926006780 1250 926005530 926005543
    0x2d031306091707060c08040305031209010b0117010b03060103061a04090c09050112050a151706090a050a030809120417121303020402070204020d09050f0106080309010807030c1e02 79
    0x4907a440101c096591012194040c408802c0d00c0c0260308258401c00400c1e12581c4480c86450094000030f141503940e64601d841d680c804100c0043c0c50389801d0412041107828411008110310070708081c582aa001307038030700d24509814040d1002071080400031030b949910035404440544050712603c081c0e10311403440d00406d03802905c0341c3c0c560342d8105083c0061181c81803280d00115481030310b544403030760b01c041041e07005050000d240015103030351a00756496000e45954020004c0408000d0031108101103c03000b81041c0004020201c5580a50308000000720b00090365000315815141c100410b4a840135120304046c1141150b9500f44000b14000c91426060b00103941079100d020111403289441010003001401100200800194406001c0025040a40082c41c4003072004000500d008030580200c002c13640429000d98155010050b607090340c1c0700c01d200d008090720b25080110309200311140020540480200040101600ca82c0d1485c02c4500035000007098094225074500108030022000b5901c28 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 926008030 1250 926006780 926006789
    0x4051501080601030516060f030911100f0305010e010803040e041b14090a060503121b0106062001110d020d0e06040302030d110705030f07030c08030a06050a050405092d0313 76
    0x40300105c4060f080d205184208484068948d00c501c04c6110760250001d215540c1c05643c01812201c400c030aa85d00c01d15610900d1089131140c40c503c01034660020120740058002d2184001410018020b188001040d581215010f004980e25036886181c804650602d000c0040c0f08006c0001011498a11520030140e00110940d00850966551034810098403814490507400d80c0042440c81c5181e24020001c241c03808003240c0071052803128249881c01c440040d4088000101650060541341c2c00b404059014400d17000d009010000d04501058024840c2e160b11002d80341c1c4c001002c4001e080381d6000405803400e540f050740c0c2c06180130308020351640e0200c026444400c0c500040249a252900d05403403a039500900114200102683e440240c2d50101d0350a0b41801003400d0351400042100e4020340c031900f0200008514186081e09100d40528a600810302c900c0c00d190820001c0800008e035282240b04080c110614844200220902c400210180e040c69020014400c105000310306115001c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 926009280 1250 926008030 926008033
    0x60903081e060108071106090c0f0603040b07030203040c150305040b070306060503040f08091009060206070c1a042a050907020c0d0b07090b0706051e0606070b040515010806010305 79
    0x141d8848081c600101014540c4038401c0200c400411000d500c10b2641036440045802e01035498980f40e5402e9152000071103a40c5e4860344804402121030a1408500c038070741809880190071803c01d50340742c28031003070300405813010940e0110028090200f0001c035940200b0603c111104503110f001001005003108840c1556141180d402040c1400d20034440d03c02220990b6131703889d0842c0c450380e4640d450816601015903840101b4009504240c1d035a0192801c095503d0710b031210401c3c68444040d0800d580202840144410306200c42d01041c160304060660f00d000d95140d440b15910740c685405120b83c1c030340030a50000078205032803282d484182100c105844007100c03518000c3d035642c842203a4582060526940010348982c145000a2482016075003150701410301e030303518070303115860b4505540100c5802d03540075403640c007482022518141c420440c0d0103070b42e02c8403a9601d400c1001c6202032081c4a0010142c0c0403d0000074203000302070200b4900c444100740040f8003941c2d1446242d41d6800e0a005c1500c0c207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 926010530 1250 926009280 926009297
    0x240c0a0602220f080a0206070f140d030e06160e37090b0d12090e1e090c03031821010c09090b0d120c0209101a040b18011407060903 58
    0xf0024046a60700302d03044040144140f4885500303010280d04540011612028881200c00010ba40c0074854402030079000000d041d464640340c402403d503641d2104201c090f80004051018070980d8503203540c1241c4250400c00503c10031280841c80c001d0329501c0e000e0800841000860302e28107880d20304180c40c61090301e030380700340d544030070020044a981d03016032540301c0451819100040c10304104090703008084d0030b0072039850b680d4081c1c1074500d480c11039407503143c400740c0354010a404481c070104580018005006003110a5554046542c1c0d200c1e4012501a00703030801079003421959014100040c0c400c4c00c0202d194505c400c3e41919004e8014002d640c40801e01d480c50205021116200c0c1100f10080149031107025500343c0c49042081c0c18081141e0100220560707010302503260307804d9050090200b0b66640c0844c61805501c003002c4001401080d01c00384081004000d246561410b9031460014000d0503910312100000584284041002c450014900420744205003d1151b0080001500035141c0101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 926011780 1250 926010530 926010539
    0x61308070f0815060114040b0a0c1a040309030b0a020c010905070501021c1d040e01021b07140a030b2707140402120a0c030f02120411240c0a060222 65
    0x211440d009062500103c84000050029881045020b141c512030005480c0350684845011146a20165038500450324090280f0100800408403400e07050400c0d1038507030a42031541d001496400c0ca840042c04031230b044400b0070101407003030381100e83c1081450b0080000351010314105403207000d0340c82001d015025030300e8841c05805221240d1241140559100200c0841001c240121144078004c126040399a81c0f05641c08100d0074402405040b0716041050500e1000d070032450b2a2607181c3c0c0000390307a24510310a10410341c5991500b4020f42c0da0103243c3c0301059a907541003054409100002003100ca040041da00058800882c5450940d0390b01880c02d210451103006100503842044044035964103030300e001400d20740c1c2030390201c49410702d0f0389408282c0a40c040c28000a9800440c019420f101c01e01d0103000411105030601c1424401c19140514051016043c900d5203080c0b282c402c6002d10000504d0045078074042c00710820440d4403c1d4119140c070380003844009514541200d9140351090501d0109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 926013030 1250 926011780 926011783
    0x3080f07020c0a03080f0f030717070e01020c040f0908041e21021311190e030d0c02190e010306050108060a0e1906020405090108010209090709060e0f061308070f08 72
    0x50982e4000e020900c030305107156030701c40c01c96102d0707404416054024410000031901c250000e41c0100055070380c81c901000140c0800c100004043c0c85003003408140082d05015980101d4000c000100403600001c1d14820280c0da0b0019002e440c2009000d01c2c0c00180102d0288449a1842c07031121006102001460f162107551010552074028400511070564400c0014034200301c8105554001a2005c240402d00942e180c91940004046500161039040000d400c19840850207000d80340480080400d03100e01c4501a0183c050458061b0082c01c4c0d80c074102c031502c08400c41000c020200e140c09074025603501d05015000700000c1c000d80d8928003a000124000306168001d6002084c50000542a11110000441080c9401810486441d070b02070000150315512003087d0344c020b00c0d8600000d6980c0f0041010003404000040c41c11062016040301809400e511900448004034150741c520020151007001544500504283c0342c02030041e4000407070624030100b03001c01140c1501d8072003c0c0040d125100030703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 926014280 1250 926013030 926013043
    0x305190f0912020d09211211011506030c090b07140a050d08042001021b010221070201140f040b030a0912020a0b0a020c1203040c0807120308060f0f0d0c05030a03080f0702 75
    0x400301c2411b0308904004034101d01181c022a007564213000e0304004410354003600b9902c5034017000c0109200303018100900c54260240c0c54402e803841c5091309009003488407101d55801070542c0509181107070030302c1c50a2014200305030f41205412808541080f507030000f00501031f48040350125100c4102401148804503e0074000c801032405030040e218402c1760702400600daaa80700000380c114030071820405001d8124a1030002103440000c0115035408041c0005050b190610030300318a080010800c0f0a0381500c500305a90503a003102c002c2e83d540e5122501e480c40900741340a8060b11108042d0748148100c0c1d00081c0c00401d140c0319030060300750350b0f03194032403141240203640e100c901980080000d55000e420042c029a44640305007030102c071064451299a01c1c01c00c850700070211001500280c2c409140d00b00d090694032150440b01d2030303525500880498400040c6422040c007814018241400704485090080c0213030201904403108410350307041c020300001094a035800c45041a81c0401d50040c0f021038074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 926015530 1250 926014280 926014319
    0x70b010503010c110d0809011509060e070e03070308030a06050603180106050f030d08131211010621081605010507020d03050c030601020703080a05040e0c0405030d0305190f0912020d09 81
    0x6000c402880c0102606c010b100140b11180c0b55503a003c04100103d03071100c2c1c10340034100850700040c61904100f0190101d06010340090144141000c10f0100d0742d40c00515081600d5101a01070f40320b48661032040058011908126804140441000720819602c1d00c51240c0e002620001e11480d65504203001c82c140000c0303091509900003a40c00c120031401a0140ba0300b14510540704941101b294580440600d41d01040c0c6000807a04585032907a1802405600301400c1c0180d000442c140c2030b50641c1c00300c3d814440005080d403e0205940715440030102000340042d42000c02404103141c84540251100c900380801e8010926000c08502c0804802099034496a01078005092071410343c4c550000c65000000e000b4108002044085140c15aa8200e01e0003031403200c148946607420300c0101400d041070f50803100700301132801041040c002c43c80c0c0300102e030541306840000340070341200c1800c8018010110001c0c0c00c0072107040318070b4480c030b074002929901e445169840303000d0aa200d007012411a60440f08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 926016780 1250 926015530 926015533
    0xe0709150b0703051c092f0402071106071208070f0f0f030e070f05011803050601050411190c020135090a0204060e1e041502180d03020705152b060b070b010503010c11 73
    0xc51f240c90781015801001454014969070b00c0c4800a0f00021300240d0080070200ca001c4003482c1c0d940c1c0c02c25080201c0a400c840fa5080c0800781d0b440340c0900400d40c120b4000d10000308080814030809a03801f035030020705400c0c4100c0a65508030b440701c2401c1c48030146480344c903001035190211b0480d601102500c003c10740354800050110790340381100300806010400040c02c41e4040030400442c00800c0f003040d02c0e04986c081d8844101d00c6e41c1900000d4003001900407038921f800221051900ba01421041c401c001442c071408400043c0c41e848601494108290381c003d41042c6400070101e110b02c0881246032040c0d080b4504141c1e52948a504070140b01000e56005200d82d00440c1f4040e20700e940d54000d0301070004000c058414001e490400100702010089040d0090b801907241800b142c140540c0b1a031240d88010115450445569440110303065860104c03a8907a1001010310081140ca41020004090750ba034407d07103880c0a8100904104070a10545d8403d628140112060768015070100048580d540b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 926018030 1250 926016780 926016863
    0xf0615050621100f080a17070203060402190b0d15140904031d0a270203010f030311011d03030129030114030a02130e0709150b0703051c09 61
    0x402c200c2007806030180a0082e03c00201189044445582100816544008040120b46824048074101c000c030010000614100048070140c1c400003a4503800c20341c1075a03801807040481c0890502e11030746411800d59003000180707460703e0303418580140080d29918064401c40740d03a1040c000005243c411981c07a00121141c0004003c00c1c000c1d51401c0102d40c03041c0050380d05240200000b40040505c0d006607510007940060881c02103080f00701d10f1101d00c880b500840ca5941004421021101c0c1c030310004041101c101000c1080c204207410400c40303164507101780345044c24240c005980380d4200340941035007826840c0c00711044020105220f822856100d800c3d40c074603400c040c0b0290840368004407481d0107110740d00b1800c0c0162103544801d5030001401200003101d003203e80f01d00d400c0044580c403050243c0d0908210302d514003601507004044950000f1026510a9240381c00c0d9070038011000300204003003000311000d00414003030b0032810509120f41d030000040c3c180c0c012018022a80c03449034038500c40001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 926019280 1250 926018030 926018077
    0x906040b181002040b03040618020f0f0d050303010e01030203161d041e05010f061202031e07270f2903010e0102071b080a210c0f06150506 61
    0x110520348040c0e0003030180c0d1082d404825071081682d210303502c407020403e030000400007800003d220390b0200e8251015074081511054002030320201d020000f0318440c504d60a443c100b0360361003038803c072101540035040c1d94032583d5071a0401130f01407091100340e0180c0502d21500c031010500100000c20b071603807082070035801c84107180802040d04000f80101e464501041405180207a00c0d40c04407850791107140003064100741585840700383d0300950b000723603004002041c61034016900812440056241c2c000c40000f812100c1c2d440038545035044d4000340c49081c0e00c103d0a401410020201c0b000d00b50380c1c0006205074a4040040c8003120b5910740701e14014102c2e8480608010302003901c407140030350014004200d6420380d43e0482e0890b0f02615045981aa060a84c00c0e0440d10904545000b031401e000640061043d9032a05071f20409403214000c0742449691400907054010004201640e800c50300e00310001d032083c42c098004100c201c151110a10256000041a29000c011107840080071a0005100983e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 926020530 1250 926019280 926019301
    0x8030307090e130f050106050406061b060225030801081b031c110304090204030c0609061202090409080c060a05011e03080d0605151b030301032d1506060201050906040b 74
    0x2900c10720300764001c3e42d1076101045502d2400890740d4001c0000161551508040200700d90f0780d0b5210b90b052103013480d002484500034800c0ac601203a0803c40c090707074544150800500c00315100007a42c4d40243c80d130800d00c0906521910726411785107144121211042200629000d0425413484180d041d03020360382c51078a04030380401e45080d41240742408800f02e02140c80c41c80c02c54105802880070158049420010b002c24106240010030306030402200040c01e040c4001d103d40d007862040000396400066800054403241d001001450b00320f1200390700d4a90303201d00103803a10000d80740e1494031814100040385c01d95090b5003c8400c20780c0120b60001251841e510165560454084014000e6960100144c291210005034006c0309a0b40303009580c401600b0a015902407880d035040c00b9590044c0011300008510540c000c200785110400520f03518a0307110118483c4811201c01004441e40203940440d24010307400200c241c8056800031300081d907540c403c81d61b507114200e6025000c4d038086408039800c1c0e01d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 926021780 1250 926020530 926020559
    0x905040b0c180a091a040908030115052503110609030a0f05070203190b090106060f050702130c031b02010b0d02010c17030717060303030907140a18150803030709 71
    0xe68901c100c1101242c2c2c1c0000740e401d00160720500800351a0a0003c2c60440e01032041c0301d00300e504440030040c04000da02d9540e41d9000500880c01030240f095a1402042d0056050f81c201d002c800c840b10341d002402210b00c0b45030080d60701040f0041460010080325840010030710301e200b101da40000b54209421101c080302c000720100152801d01000700041d40c09620300307201e50204800f091072110b85800107454040503100d00104900010307403405c0c0e418400319900c030803191440d9540c0d20f0041d4079410035000054090603d0301114400c60f1400c1520a0301a8040c7c2000c0c00b0140035500d0f0f44074034465440c080e42a6812014a40c0d400424244000c0040d809606520b80791402030307803100b0040100e003414048641c82903500c203004c94078480007210205404040c3c40e6100506801460850030880c0c00641d440c1c01c94000d490711507503001c1c94800c4584441480ca4000c000ca1761051482000c80d00d810300003003c0b00224048a4280c03400d0126601c10300004503406508a5544c1c007403664903246c800007074102d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 926023030 1250 926021780 926021797
    0x6050303190302030709090e0105011409010e041104110310080705061608031e07021f06061e030e0a2f0d1b1814091c050c0c04020a180905040b0c 64
    0x2507801c201042c000000d1080c0c8c4503c400c05000058154140382812191514003140c90f2b120380b402400600c48102e40c24581d6801039030241103416001c15041c0010081c0c0442001564520004001c100305400400008802ca40c104070540da03140d504d86083c418180f142e240503800c80543d0300d05100002e8401001140e0001c032428101c0c0c04010064440707221180c041e1089001648200000c8941c14482401b001114000820803c0054130700740001c0d0250079004180c050141800240b640324601a81200410000180699002106c40c0c0b924240300004604c2d10041e40e49e5890207044080c01c0c01d503c080723030614000e0900c400e0006030380c0d403d500c80d400b041030b0040341380c0701c40f01c0040c5842d104160b030001c028030f402c00030031004091500b60890000c0107000078804d6000c040300303420025031301c502c40f011503005145c000d40c0c0321007410819240040e0040c2c040d40103440003901d40803059200242c500803840703c040b5802c51607911040882580c1d0242c0740a080440700c03c0c046110069468000c0c02e420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 926024280 1250 926023030 926023037
    0x14010c0c030215130803120112050c09090708210313050309090103060501092a0e0a05100206270c010e1903060b0f090c0304060e03070f060609060503031903020307 72
    0x554882c0d0208242c0e0314201045072200e82c012a40c050a0748407081031601a0084000079402c001d00ca650004101006201ea0b8908840a846150903c082407050720300b030150140000c4081d042c80e000301666458948501641e60082c40d06d100b4070908001d0155041450090001d415511080c443e00c0303103001030f80b004079524441003040d48916126001b003c3d000394020342001440e5854017034034034103607034107440200002840c00d111400f50341510046400c1500d401d191901000c4c01817408500784e5034013504800e41c081c101200e0107201940c0001c5e00c91207002e0801c07403994000d008100c0d01780c0102d2402d150300b440760004128840694483c03c17411140c900002c05000d508124200c034607000e50019002a0ba081da1205160342190620440700e00c441401990401c1e09890903840038841c030700024000504076070b104c081c441121f200030030650720340c1034021071072030f07a900090715040c001001a8807924a160341454070000b2540b40c0481510310050302d10603c0d10902807007200c02c600a40c00100f080090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 926025530 1250 926024280 926024303
    0x3121206090709270e0102070f061a0904080901030b030d090e0a0f05090a03081501080a0c0302070b0a090c1a0a030f0e1e0c0a0506070f0812131b14010c 67
    0x80ba034142a41401800c48590b02d904914540c030913001c1551601645803019070300401c802c40004400380808105550458000602d0b11924840800a05110295650b0000c42d80c4144414080c010000300241c1000740c9041020200c07031403d040d2101c0f1500c0882d40422000b00003000302c0312107410300300e5005200540c0003c6030a900900781c02182e0040e52441d0284c0c0c4072503188020180c103d800d581d040080400e00e60507000086000900c440e07002401240740644940f00d00301418005e8050341d0a00d0742c014a4040c15207001490000244507400050b1695059020001010f81c0f61648440d2500500c0100f0751403c800a2407c0c0c0140c41d1102c000f00760240c3d42c82150300c1c01201841070000700144081000c1d42d200800321820b00d040001c4840134441c80019404210983d00c280440e10201da003c50b030480e03c0c91403401c205456002c2d8180030503401c503071a0104252440e58403c03500505120b6112105c80c03d0030841c43c0034440303841340103800d44510381c0841d4088641c0904424a4014400d80e6287ea1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 926026780 1250 926025530 926025539
    0xe06060a031e090f020103061e0311030f0a0b0f0a0b1804051c02010614030304060e0118030f0b012d140d1208060a1208040302011d040608030903121206090709 70
    0x229401c01c034003550f513040008118811507a142c0030f240c4c02421403907408010820000c04550750103680d880010013000e080480c94000351070900460301a1241401590280111424001c641d11310844800300d1000c0c5410010380e0032201171044819a00003e80001c0c001c4808040c056602c1d18007803c140c555220301c80500d060030741801c0c2c0d4840580d91560000c60240c5c94010001d0490002c40000d51080d0000c0c0700600c155648020020070904007481c0c8040c807e07540500200c520241e503040504816000200390050044451119040360240b10a0340021050b07115142c0201581c07000500c0101413520040084d4014480e2800d04003400a100314040d025a81c2e9003000c0310402c14568020405007010000a49840ca00480c010302c00d9018202c04070040350340c0d070600351165000007410301c5403040802600345040c8000d02008000503104221164450401958035000201442e02ca80315011010540201c44001c2d00c40418607014924100e0300d42804205030380c00c005024400300f0008280008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 926028030 1250 926026780 926026841
    0xa0f0f0e010c0215040b06150d05041109010803030714130e18010606141e07020d030e210703020f01022b0206070c1511090301020a0504050a0e06060a03 67
    0x301008640001604541c001d101a09141d00701000482810b03900c400c020210302d060b1003066008070205d616a46550304001d01235020300030441116246485c0c001000100101058000c548400490700070416a0b039800c15141c0c2d030300c002c882035000100d8882034266610520700103840c0c0c60306626150005162100e246042c05034003124000d210702c0d0403a803014030026003841890b0240006250200440300f400c16021000d10500403400c2a0204e990440d840010307120040c0c81e22507500078500c0140c8030040c1401042c8400380304a9030312401a0b441d440098180d2450305044480ca03070005000080d10315003c1000860030781601c6810b42c0a68003034400251103803884280010050020425445220100207107041c0c0c0c000c00c50310622042c94000030105481d2025400126100b00000c11015030700101e513869070145000a640660000c1101881190000080d20a8440035150341c03c0c81692681884012038043ea000c6030411010019850a54846d80110f1100c215a8440090708003810344500b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 926029280 1250 926028030 926028041
    0x507060f020433020102070b0f0a091203051906060e0409020f12070f0605030f011e080105090c090a02180d080702130504031709072c0903030118020c060a0f0f 70
    0x1281030680001e1001c0f01d03422904030411081e84510085003003456540e00da040e8070502404c2d01040702c070402c0000d04c51400c150130521006a10042040c9107212052024003c1c00b01a1044060350040c0c1e00c11642034803091003110300311800723607898000c0807104906010007030900c1d031001da8000c02558a4030300d107038980440e80b940c0d10032190014003555207030810f10542421180c1103801081010414802058540c0055605441801031920390b030841c0d020a08015103402d522411041d400c1c0400c210190342c02058810301c41c80b05a4007900681c2e28400e515040f4440c41460101d000a000c010344994102a0f06c103d100318460800c2603d0101c0a400054202d1044881484055210400c00c4100f40d030144040310050420545445c881c105980c28507122405802007444181d02e000510032800c170011450b030021031890010800300d0500c4038080340c490340b017401103011070a41d0030345400e103c507003a100f00c400e01200503000d40b44c4e64407083c076424043c0003860600c01e0610f0720f517014415580c41c2481070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 926030530 1250 926029280 926029319
    0x21c0819020c03181201020f0706110c0a060b030c010827030403171c090b181006090501050307150806010509220c26041118090304050a14010507060f0204 68
    0x101d200c1281080a05c1ca5078815900d900e0740103211192340c1107494030560b0b1039280d201e000410203111800300f080142c040c44030361500d240b20b020359402c01e0040b02d42c02030415105c1038083c0d41d071901403c001523b03040c1041c2c4039140140180c059800100b860300b00d000c076802d00850282e92519a032038554980c51840401180c081d10300000f00b0f540d840361203912a41c0c5109030040d090100c403600c2c1d1181e08807148010560400c1c035004011948000009109000130306111103400c00c0103035190080039008040034050b01d80203204041000c25480c40700700101b5942c030455541c1446a0341c0c0c0d440119807582000c4166030700a801d241d542c28014202484c03001858040781400203561082c0a00201078144503a01d40d020a8600c9070030050036050000c02e5a40260840d003034018a103680c0d0b01085140c80322200d0301d803003d44014180200c142d0040010821614110f401c0c111035900e52802c0090727960345406050226008005c1080003480b160402c01505850190040c201603542c032101c0c0c1c0c001c410500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 926031780 1250 926030530 926030557
    0x1090b060613263c010f0908040509010e04050d11070b0417010506041811060c06070903120f0e011115070315090e3d0507021c0819020c03 61
    0x6079110803d00c1040064a841500c0c02401c01c840d510400060380d0004882a5248124000c0d41c2100038a400b50032036450b0940c50502080b0303564003410224582d40023130007490311442e800400020f8841c42c8680c1070b80500d8214003c0c3c03c6a0700a800c4c10750300d285600c86e4000080c01040400078550f00020064002408228800300e400c1c403100401908540f8018442481203141410801c2014102e5401c28426039000c5044030705408490001200c900441801e02400d1240030100401507038030101410840340b150345101044014000d040d90a608240c218000044480318100125072140c1d8608204103509010f0780e03038100350040d9105282030111034800205e512044954003601501c401f44000b00005c80042004011108200b500e603021451a819000c400040c035840c41ca04540013590b65030502c1c50499803110070340d11000043d19003114094058010305006040c208030904169440714916941c0a1481d668550101e00b03a03001e259030103800740e0b420303c80d21181c60402c00040061818605 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 926033030 1250 926031780 926031839
    0x3060f04060b0108040c09020f0d02280e0612040f2013050c12061503070f1209110427051c020f1002161b031401090b060613 55
    0x10800140e60b050410300741048085010880424401c49414094941c4081c001da6614248281441980948242ea0059610000d6026521250440804580b5881140329011122162800d80c7e42002c0181166040001000b126540d002040e2100c4d038094440e0307500700700305d400305d894203040c40d6060f046204c28411241c042d4000352400b030703944070194a03034a002404589040b03416240e21340582446c1249a15015020807072640e1121031044288091841440c1c4a18082c030000b02040044043d0101150064525000c0d111132805102240341d00a1042081c810510f010720005040d000e000014a1075415240e6187c80c405804800c144c44c019801403a9000d00080c0c4103c042c100c1145040c02d65211505c003056003803003c102c04005410031140103031502c000141001d078600307039030b00000c10403c2010f150301035003030f4641e000d501541d00450003c010214800380460813117851410252000021400013002ca1030130314014941c0080358006c40001513510342c4200014032070080d041c401101c580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 926034280 1250 926033030 926033033
    0x403052209020c1e03160f050a0b150a140105070320030a200f0601060c0c0f060503070201140c300405060405060702070302060702190806090a0308150901050d1103060f04 75
    0x303030b4150304e100b82201440c50b2502e000e840301e803440780141d801440c000100d000705c0d0601009100c0038456507080105400f5600d01540e50305400f550162502e84260942940421a030092010102ca103c106840700e074500f80454030180c404012403040d030070300343d402d100090070344000038405085071308040c0d01c4449000e00c6001006031401c01d00c249040d400da2104420488074800002e0550446000d41440c44d00c01c0501d09041400e0f1400e0f07040045c08022101000840d01e501600662180900740d00802c05ca0103180c0200b141050191580c240e0301c1c0d0706102c011380d01e00103001e00e160b01c010103076002d4038000c0d142c0c0380c9007040e01320848080e60b068100b03104000a0007820302003a6800480c52015041450840d800107440b402540c0f0080c2c010007055400710f40591802140c0c10151a24404030340d45031901149983e41ca02545404400051a04000c1128520304030621070401800404080f207a80c2414240074020954003c00d640817060b58001101e15181804458042d0240001130007441ca401d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 926035530 1250 926034280 926034313
    0x1060902040f210203071503020706022704060305070501030c030b040e160e01080604230715030f02032203021c0314012301053103060e03030403052209020c 69
    0x100780f5141071100070180000016a000301301d040a480c0d014000285a40b46a18214004e0150b880c0003451188006020f002c0a034800b9201254440c50007402059370950400340710a031000d610008003a68400303803080c4015802500500a10000c5140004c0c14849550015040d2a02070040301c6c01a00080395084140c0b0483c0031020141000c1d00d1189219450312a50a44e650402480500007500d0110208844a01440c001e00041c90302021140f0b4640c039100c4400b40001d09100300c00c082464080b6000f1003540c3c900036640300b4240044094101e0f0071041c2a0b407081006428100d045000b003001e010b000101e040c06003190a04030307039000900100c81c0c6010781e00726041030b0051480c4400d0410b03130301d0740c10549608813200700070286062600c40740450030709490700f00507911048680060500104200f03407004404000c4a020b000c0521040743701411080e02c030b00c0b0544011300051010004c0c0762854030110381803044c60714a18405c10600e5942d51a000403a0000c030106031180d00009401d190b030002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 926036780 1250 926035530 926035559
    0x3080a09050a0303050906070807020607152712020a05030a030b0a062f0f0a060506100306050303040902181f0e09310609121106040305030c0c01060902040f 69
    0x1600d20845690540e1400ba2043c092151160307c9100002054002c000d0030b942038175500c0768007401c3d56031103000c00c0c0781610801203142c1980e000549000514140c407561405220101c42c03903443c00091603001511f0395414407441c44840c0080d44544060140016010001800d42d10303500d580000b1514996410403140c5e41c480d50002c000c1001c00d10f641c9009007241309004420f94820842c00110005009445040201032041d840c10b9000b103207100001d003c0c05820040c4600b1003181c001a55050070002074045031418000c0320f4150340280020702034081654000c00141a034400c040c4641090840000e001d207803403455403001102128814540603400001e0741750103d80031a0b64011504d888407003400d09208290348001070149086944c5000e460f141209800d140d0042414002000c46082c00300c08440c0408901d4005900c50407801803100c004504e9a0244da450340d00c4901e10b803039131003994049070051250082c4035540c42e00c0004840020380b006000800c0c58103c3c02070110300d422070034012021b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 926038030 1250 926036780 926036789
    0xe06130c15050d090c08030c010c08060d0507050d05150103080d200f090f030709021209032106030f06180c0a030203070b0705030409051e13021e010507080403080a09 73
    0x320141c1e260720000c0c0c0060582d1103800600b040098088018205440c01c00c0683d440380d0f0b540d010000320a1071000303040d00040e400c2e85058a800400d92186070500403050314085020f44039400003081440f50f45803030320b90000458010403c40f0a107104158112001c4030f02030f40210740c8107500042007a84000c2500580c0b0036014651003c4841204407140082c0c41d21038080356280d10900050801140c0d07403902030002001c10302908407484c4a0700c0e06000b200035845803100701d210540000000e010b001c0c00204170345180d2034120070309242d44200d420042e44181d010304441da00d4003a8045000c9118130402c80584507109203680c1c0054021169080d030b0901e40102c50301405040c0202092000d0385000030720800301c901481c48142c0e110700c0760609600307602880d0420007146007007101740140724240c0c10b850101c0e060219844070294a401c0c54804030164070071710094110750041c0f844000311107900c40f0741c904a003045c101079240c04004e81d10402550b10a8108960984000ca0414411540455980c0160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 926039280 1250 926038030 926038049
    0x90612020f040b1807020f0118060b030708030906090d020301020d150501181e080604050f120315040e03040b1b0c010504180e0a0804090b03010506011d01030506040e06130c 76
    0x20140c00f00d0030b038030308642ca0420145001360210f51030500c00c204409034000030b00b000300001c132004c0089092905030010103460079400c041ca0928103144c0400c061b4211010741c0c00561601030b14905203c1c40b50014079489a21a003804400005a1020b000402d1900d01000c0d00096046410783c284c00c070303219513800041c10800c012a86844c402c48079400e000981d200c0c581850480e0440c11030115407191140c210b9502030080800307000c1005000189a00030340004415201d5090000f4440c9900c0e0000300c03010280d030140c041d0f10b00a00c0c1010b600030110554464140c0303150540350380019155901c51703015101801011031038a1007400b0103001c400c0c4044401d103040303850b1500c0c003500d10702e48030204214401002c1d80da0070082c424103020442c0c40d4090740d0100342c0307545541c0e403603004800400321101081d00035401c100003c0c2d12507201c0c07000c000c00180d01c00c0050142e401d5807070044004140c006e043e55081a5034601c9485180c1c1e04004040c817513540c6802465907203040c1e24000319003500c2c0d0740c4038402c0b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 926040530 1250 926039280 926039291
    0xc0212030901050d05060d0c0b12090d0e0d0627020f09130b0a150e0a0f06080d050a0c0f05010203071101022d0706060308031006050c07060513090612020f04 69
    0x1d50f03910004555840c1c03c00640890039460340300010b612414850802001354040007000520100803101600810701549000200c9a03201d55001d521401c00c000201c0c00280e400c8d6200d00035207080503c00c100d4601462001501c48004810001c002d40312621040c0110510f07a0380b10b0440c905800c18141c40c40d0700355250b0072242014000d21004441c520300c01040144141c00240c1c21940315808141d110341d014540344040c503074a5102d100982001c0d01c80281042c00d2545140c03203044207000390001c80306120010055905e07040811a21504045400d0302001035000105006c2088030030030250f0b080c000c000050360317070510035006001c080c4601c0060540b039005116100e004684403007940014850809115900600940a0109403181200003004c0602d4818007006100001c2d0186100307039500e5901c609c0702600e40b0010b65103406446003c4249a002c0301c800c1c800240303d10702030700e04440002e000054a81d11408100d041d0384d11908140b4028072499040403d40c9403c1d400030380000c0c000d4804200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 926041780 1250 926040530 926040547
    0x30903060621011118010216060819020708090a150c0209040201120509070333020901020f0d020a050d080c0d05060111010e0a12050a17060a0e0103030c021203 70
    0x403906001860544160122104094407941040100079030805520081000042d070034410b080355041210100244001a10403031515400090f102203200150020b40b03110fa841d00c007040303a03915401021341010035440c5003100f81003501c0380050300c01c1d9481800d5040d240c1030442e05000d02003c8503807088803242007800c48a840103801090300740c10103405403406001552a40010790301801e541d0780d681a501d00e4601004903543c80840e00c5401d4034854121343c291400580b41d5110701c08a5020917000e8850150402110300c2580d9005001442c010b0050300c1980000c2c000c094105021802d408025800c0005039004108090006058852440c00c2004c9181020a410b54040c01003c005c030403410b54442c042080c5030b00851010144446800c000d00c030030180140c200e40c8480e11420111901c0c0c0204a00003051400381c0c1c00d0b07440009040e9120200401040c5190324004809030056802800321180403c5808804240c04c0c0a14040e4441450f0400184148030380c8542c070807444007090b00284070158 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 926043030 1250 926041780 926041783
    0xd0c120c02150a020a0212040e06030d03020901050a080603070302030a0804181e090204090c120506012102190b0d020c0d020109021302070204110301060f0f1e110307051e0708030903 80
    0xf500b20584190050303d8100054042e4a0844000e0b0314503204003001c00d00042e015601c092407481034070301f601500c6421101c140c1c16002d0b402549040c0d400302d80107015613400700740700304010345c3c0c02440281202c0788250350742c010a092030381065003a2580400050701744104860780010304402085004100600002e42d030b0b03950842d501800c0407008254448905a040d50340d03641003900080d4002074120a095a07601c070306c601c0c03100a10421500c9025490001860303164001e81c104884e10803169124015006c0d80c2049120003078444a02040440603d001c55030180140180945100120005a40703104241443d80b5041e01d920030282168180144000140c841200c580e5079485d0321900076031217400e00c2c40024080c0c503190091000307268012000240c00d55004a5401110241c0c0e01e031032542030008102150740b05900c52160041e07e100b0440d42c1281c070703c141c81c1408492060800e40c3c2c207104081e52803a04000030713041d40105034111000c80082240060294400070301c8501c0066292074000004203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 926044280 1250 926043030 926043073
    0x90c0901060c08091f032405041119020a021e031e0c1302090f01051207210e07080d090602120307090f0e0f0c04031e0201050d0c120c02 60
    0x5404201c40b140022003004841400d6a400e02d00041a43e02c0e20b454411040007119014841000043c1c201505040d05805610b012580c1c4c40c0e28410b4203400504007010300010301143ea11680b585081005400108000600c041d0a408900c0d40134194041d40386c01002050040580d0314809109000d0509075076640020b50b02404801c55903040802c41900300e0410b050503c03400c00c02e504040317441001e00c411400d9900800031b4000844140d40403400c202d0044030395004210014041c2c9024401007045140121034900c04140301302a00b0f04c20030704100701181a200503582d02c03549544500800c0c4452181440031031440c800d207203044c490041c80e056000f95140002a0050480100080481c1180d44940349140252400d8419111843d580e1b000100b05414112040e000300381e070030130110b0034000d0700a0848086a400031010101001c01c98000342c260300fa8000308905000007003051004100d0707140034204219a071900c0d030924056000100205a41000517a80110b400c42c0305a60300254006401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 926045530 1250 926044280 926044289
    0x220f0b010813060b030d1806030c0906030213050a15030f110d0e210a0e0102030a0e060a031b020a05060a020a0f0813061107060f090c121110020114090c0901 69
    0x460303940007107600f0a40300900c0c0c4542625050b0184441c1c3c2c2d9115034221100c100483c1034150411800782c0e40310012000c89074192030701c2002030f0440c1000c120844c800c2d00549041700c2182c0070420001d40c0e4800048200c0860707400340d420648050100040c0d85d804d441180900e514800042c406020050081c90b824490b042d079511407640d0701d502408810a0070400d00000840350059000143c81088001d21260081c211500006e200c440c0c2030b402651000c01a2441281642c894081d10012101005504e8200c13203c0e890400d42c0e81c605074180c154540d650f1007800c41c2160050488142d89060179400d000340108103008041c010000c80c040540d1180750704c00c40d0071039841d00c0f4406440d042c40c480c500c031917040c0018003860f0800c41c0e50090304070130100a0035041e101d41010801031910008044c203840317000c40d000c2c14465144d0010000d81143c0c58a0030711261260381010b01e02a1420b00003400300c100103000d039006030354902e00081c50014296803c1e401100400040008400f103900160700d00c0014001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 926046780 1250 926045530 926045551
    0x1030c090915051201200c120a051303111008011202060901021e060601090905040b0a0b03030903060109060306050907080d0e0f1008040501150506041a0405220f0b0108 74
    0x120760091907003074010340000e420000d00400100213810001400380c0750751084401103204400c440c4c0041502c960071111140702c1c2d031015020503003a1109401254016118a8042c0001006941d19001e40c0003860b130080c52043c003000036011041d2050000564150410b042400161001882000000d40030441c0c40342e81115220358820003440102d00348541c0e03601e905210700b50048002416600460f0b414418403003aa1f50080180d99941c000c0150340c001e0381d01510f10009040441c2580c0440e81003102007242c044e040b68500380b0403501007441c01100b40c2c0007040b40740da911000d0003041418012103401440d08002440c00300e040c0081030341c54010b8020400c0034044004426a5140c48203c22100c450200a0100405017600c8002070584c450888080300d003035280180c0c9808440000c80c1e0b80040d40e002030030441c1402e0400142c07003403100d2110910080c150080c4000240d9944a20442c40c0d50014028011000b80100e20380e01c043e0b94030050031040d441d050411aa0041e40d0002402e0f512003018038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 926048030 1250 926046780 926046791
    0x30d020c0c1306091a09150f100201050f07050403031706040f18020f040524030a080a02100c08010b0906032502030c210919080a0f020f01030c0909 65
    0x105401d14181426001e950409803002c0220107014180c1d010340d00701c5815030402d0281e2074061440000e0040c15220a69000a40760081620501c0c0590811406040546845040c0940070b0000340820f142e80c0c05170005039158801c00c20000d03540d0032034a4110b80f10b41402c82c1013508590b4060b0049001c030401041c030f8150341c800150141e031207802088851003422410880b808100304800c615000c80381b0240d001d41402060540380d42054031503a40310310b19440d02092a8490592042c807100000805030b42d03d0301c10700341d5040100d030040bc001c01d150300980d0010440b202d007401c159003c0d140450f40c1c3c4030900ca4103200402c4010002011600c64200c121002e039581c1c4ea841202c3c024441c3d2030412030180b03403400c00c49000030940000c01428200d010804a460500c107554a4800b0b170404041c40241240092019030018144200f00e42c1c1e9013000794a44482ca541c0b04d914030740c54002051016100e42c40017034260740a5003070501061a2264007031a01b07001c001402000500502c4640c03003010381e03480da00c0c1e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 926049280 1250 926048030 926048047
    0xb04030503070e0d060e060601090b250b0702150a110d020a12090804051504120609230c0a0602060f060f032e0e06041a07110a0f0b09030c030d02 64
    0xb2400c89030b41c1c0f8001840d08407481254200307000101284001045a0b00c0f0b443c000c9a1030390702039840707181122840c0382014075080d000700e5001400d0001e0308040400d818115500c400040400f82160b01c2025954002c040d00481e07000100c641c10006440003401034604100c41c00c6c1c8448840490b0f403002c03545500540c0c2c8075000358048410000c05003482160504e06191601000f0340e8a000b0f0084039011110b01100186a141c40c0c01c00784250b02c14141078440708020080000c00940001070790501501c1c1c0c030a81d9000300c03401d00080e003001c0e00054105801228085425150146404d000341030544000c04c450b10f400c1c0c254512410313002d40b103680f007042850911203071550200101d031a64545482e400404a03545076041503600b40d000d00da54411402c0001c40400f101c40003415a210350303045101c0400c2814030f407403c8105000e002d00300c2d804214041d01a00b40681c004c0010700c11461007080108040e800d2401c1c1403180030800380000d42300d40c104005404c2d03004800420f903200d079522442c006a4030200c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 926050530 1250 926049280 926049287
    0x140f09031818040b1801060e0105040c05090a03050d030c0504050319060225110301140a0902030312090307020111010b2412091b0126330102070b04030b0403050307 72
    0x98855a106122520100000c00040d62000750160301120903045245c480b0050030303400d171210b81c0100f818800803100100800c0c88c041d0440e1b00f18601a05149181098500c0810b0008015810030388041d0b00210034130240036414801c030b00409442e4a05542403e08120000342c41d5180007905011180200d4140802e00a941d4111444440c0203080c1d4561000c200100d800d1b44504244150340304c5142103d0719001e42418050300420582841580d030311030341d4030300202000704118036043c1d03018442481154084070307aa18400380124900c00003503846a0f0244001812142900d50b8040c6c40e07410800f507035400340ca0f2421101c03401d9403a83d0704031412035995560b404046c06006540200042403005002c29400c01103141300c14601c40840e000f440c05207110054403030590050300803801e00c0c0422001031500540d1648540c10209000d204280e040c0040841c040d16041c0d4822070344076140b52007100380d4a603010840c0c3c20003400740311301c11802e091440e100d59188910041003c4e060140010000d52410312 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 926051780 1250 926050530 926050549
    0x10061805040302010b04021902120a080c0708040f06080f060d0201020c06090415030f0213020a0c060c18060305100611030906071b03050102030103060b2e02070b030a140f090318 78
    0x1c060802c5495508c01074103c040102609410400f6000c0c51014550050f241000c0360800141d41d1034850b020b8450b1180701042e81e00105c415614584203002c003142040070442484000d1015581e080c882d4141001c50b0303404e1180251002c2d02c1355940501c000010703600480c11b841d41440840320a07446805110114004d0700c06c51000c1700740200d0042c404400c02c01030024074200e6a000b6101daa000c0c001f8503044408030b2044805010100e43c10006034800101240c200150210071071404905c034001c4103120920f5082c1e140c00420120741c131801005071032104000d9403002020039180205002d40b002540da500c030320035164054043c650008078403050105003080310903541482440040c1d242d940741450740c003d42080c0000c80c0c44600309260154030b444c0144e8000481d041e00090382408030303d00d08841901100d6641c100c1c00358018030000040359000c10002d036104012008010820f04c00e5140b0131149280e009100241d030303500078400d2080444000041d29128516091b04100440d04000000d001c0d40c2d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 926053030 1250 926051780 926051801
    0x50f030709051305100c02190c0b0d0204080102030a201c020c0c060d0b01080a05060907080403140d090204060801051003080a0201020f0d090b063c04021b1006180504030201 76
    0x40f038120305d1002080e00398050303030300144aa0709580c0e003044001e042c0307880600c2c0c068029040c03500c400c00038000102e0b540010400100c1d0b2210040c47c0c0f0b076403200844c0c00c0ea08211100d406081d654030f0041d4522001224041c401c40c18400b00381e19140c1000310b20000c512408042980e0958003240c94150b1a00130446040c10102c020022910b4a2000801c00080c00500d0740301c0780041c10070700114015282ca405250300a45004120b404036a03903156044610400040060b020030074284000c95039126510020034040c11761200100c1c5480c40d50041c80140d40d015480040681c1c03400041040442650141700e0aa942c000a0305a54100b51441240640a010501c02c1d20131800182c1d148003c9823540f0007603089204010f031640b2580e905041107a4840c074043c1804442d501843e00070707010100c9410940c02e00e0715011030003000650b400d021408030381080b480c6004401031966034040e00d00c01000540301e840009401480b5485c00d010a01005102d0822440032080c0c82c4d5021904060003904403d2104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 926054280 1250 926053030 926053033
    0x21327080f0705160e01061b0309051c030207170a12140a0c05160e0705071403131805040f020f01051b06010603110304050703020d170409020d06050f030709051305 72
    0x10302c450b040640e00ca40030141d0000220554040001e680e80c841d20026040328004d03140d0945003402c00e29801d0703003d0002d55080342048907000340070500e655060650392444120312041c80d075560440ca0082e01d04003554003d40f031201405883c80c1c6501c00001440d061386684540c40c0e00c1c910310284010b4501002856507191200d07030102d603241c049503101c80707643c1126002c1c4044400c664904914090002c40d1401554606605000098132a0f4014002003052a100e840034040c0c6003000f00804d42146c02011002c030340e085400d24100320a0710411080351954030340050420160412390ba0f8011103680000d0028003800444040c1261a0b02030004d5904103015004560528500d002909841d10780901601010a207030100b4080070302c51540c140c0c0e1080d41c0c81001004041c0c21902081039821544504540d4003842c070b421009030071180c1c40a08014842c0140250304d920304843c03450283c85182c1c001502640c007035400103940d56000100901150703002580000c4584901c654210000c2d0000c4020306503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 926055530 1250 926054280 926054287
    0xf140405071a16170f04060c111906111608011b1707031508010c02070303030c050a0e0607060617030702031c020d0807141b0705180a0e0a0f0f021327080f 68
    0x3e848d04003044412103440b50701e8004492448070204841c03040310006d010554018000140036040c0101003003a441ea43d41812651205041c6070300350901501508188101d944802440c458005000c024210083c0b690a0140810700e44400c1401e40a02c028001c200301a11202e40c210f204580100c101c01030300c00072000740705090443c83d000e0350f152000c1c0300860009140c04040b074087c5104206480c944006e84d500d050503104030108102c21034209900c29140d050f41c1e43c500007100380740100b00012000d0818061511900d0386d004150420003065183c076507418090042c03040e9190302140d05c0d003a65490342030003040341d12107442c00c603501901c6030740036220b8020005440010b04140140455440011030032940e00507191018400e200c01603041c0c854547e500c40e400b082e0490344540041042080c0c880c200c0e101fa00161712400102c0c40148000e8036120450345004095041445020a0100c010304061003181200c1075060150518070000c0f0701920300700382890381003044080c11a000c1854085c0d40c1790301c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 926056780 1250 926055530 926055539
    0x7030e0907111005091b0a080118050105010e06100f030e100f110901320412020f12030405040c050408030315100f0c02040f140405071a16170f04 64
    0x1000e4000100342c8114495881c1246010005004203841107901ca805030030201200e02d07180c00110102a000d0b07a002c02c032000b020400c00000d1003006007900074901902c12581c10741c00d003542101e00c1071b0002c4811036248010000d95031181800c0303800f0f04449140c42d41c64261800c2d4210b00070206a100da8801d4010041d12200950f529000700491008040c0200180c0051118900c86440b9505c501c41c00b1941e0b803101c9112202e000b107520004200e40c22034001c003208050700800b00c9507105800464107000507840c220b0544c107001c205081001c0c0c0035a401c4103810710314100c2c542d5138050782c0302d154030030354598066a200d144140203540003400d0b82400c50f0303143d0034942e4880e00c05600044040740610666050596201c2c0f04070110700030f106454584c00c111801c29024070014140c0d4020341809140c682d10343d44892959820600e1003580680c0240804900f00341c1525040301c50129803c0d9031078400d0040d0800e94581308280105036a00c0440b9210102c000d901c84030b11406403201c98500100045400034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 926058030 1250 926056780 926056787
    0x60503090c04060302030d0309080c0d03140c0a27050402031501080c0f040e060f1807090605090319050a020d2a03050303060405071218060506040b01050f07030e0907 73
    0x140104040300558001680080078002140e40c14400a07505500a20510751621b009038005542c4601604645107043d00003c2c1711444d18003c8003404000903511043d544100b25000c814030781000000720554946031908400030000c1c8050103c7c0040381007e03960020b403180d40620880300608010300195107074640b0601281d851010000040e000c1271080700001d80c45401c0c9002ca0350070350a000f104a0800f8105035600303141d040d004107041e4001491a03246440303580d400c0c03113000c0382141c1d10700000401d1074050801415001d4581c0304209219043c0284401ea40e40440c3d10700c01d9a1079010214201c6d001420950701d44001d0050203500260080c04d01c1090002c42e040040d8a018450104c0c01c0030909d02072030130000d102e0384c400070f420f81d041031012521a141079040700d0f0300301840c4d140900c0d0b104007074071180d0125a1800b8880303100c10346050455003005418003490f039025504940030010301e1111320000c0e0044c480c1c0300d01c49417030503000603a660400d4003c9903c4240341d00301402e1000d1501e040000036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 926059280 1250 926058030 926058037
    0x309010e03100c090e0c0a20160e07030608071a03040219080d1713030f1101110d0f06153e0c030a0c0b13030501150617010e0112020f0a0605 62
    0x136490417038048009106190709200b02d881d212071a0369640200d003000e4103650001400707804a050386000c0e0030100c0c0d80921000c440c0002404840304108950300305800080c1c00c580d401c1c8e00a0a25400c180d00401c6101c1019150103591070310303e8081d03552540e940c400070b01218000003007520340ca00007480100b4600400121494038001503228181c40318802c00b07408421403004c80b100a4000290060400001d02c42ca0001e030a400450074500815080c2015950a40c0e54032107030300390242c4000c2107100c522545806400341c4c1d140005400c20009041a003825818008001260148203c0f050031703558100810305ca2003000340200c145c5490442010740c2002c208070860500700a0b500c03580d0041159480d000c03034159910b030750154085035035614040c961403040c0c21201c800c00b104081160700101044080c010070313403090380c0010750b004000c1c10f101005c0c0030307074081060825a2505803401032116040c64000c560554845090250384003400d0b20024031a900240d598941004013071000140c0981c104016 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 926060530 1250 926059280 926059289
    0xf070902041706040b04060911040516031a030d1b05030c0109020a0918060f0e2b0801150c0204090f0501090b09030f19020c1804170c0309010e03100c09 67
    0x40e4803650942d0801ea83c2e0302d8141d50103007100c03040740007080005465034800c07a03420b40714101c40d400f080c080c540014101d400460764100380392a0074a69a5221340d040c4144442a8070324501c4044080050b008260b42d0102d205142081c031050841d6242407003688848020070a40c8201180d03658403400c054607000e4944618101d01500f0005008548105036004203500350101e4000c14206000644036100a40074510342c403400d0581c3c5801401c0142002e12485c3d4200329540315596182000341100c4140c42d41c45031a1404020740100103206450380e141c01d1403200341851400049050080c00090024004000010248445c172065882001010340240980e24000d98620810345c2d00d8a0035113842e032240c1e140348184400d00f000004818210120507001e00945481201c8c0715103001c0c030101c4d50030744400c1003508020000c082044200183c840b000310320118020449400d00080160099032805485505810b000743c500c1542e159880c01c10006c0c2d8a10303400d18040c00742031a1008041d0a90495004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 926061780 1250 926060530 926060549
    0xf03030f0e09130f03140705030408060f0f13080904090b070906180b130b0c0a1509241e022503050a27031109060108061507050f07090204 61
    0x80701c60480c507003401e03820700c83c0c40141905208101c680d920022280c0e5071400450905c20b105030401c4070b16807004090480b182c0b04030029983d803410551340e41c3c07420000901012242c01510104030300700c40e205200c545c00002e980514803c400003464a00014002c0e5001d0030340080c5081c03854002c0c071070000e107064051061501c41e684442d44900044074039204d92002004046d030b00748000c0100004140041050307000c1315034407840b059121590390003d58000c400d20017855010b008040c0620400148501c081c1c01d07014410403001000741d84458400c1c1044001002c408004240a44040c0e015000004c8114100300140d414804004d4110003d401801c2e0785500344810ba80c036089180400480c03100d820384c042e215982810081070040300c242050407426002000b06c0780c3d1424100307a28050010156100380140100c8602c8601884402180248201c4c108101d080074000030380c89006c100758014484a414075685c00c410b0405a00d081c0400200340349600c0f82820006588015038043c0082d15980d54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 926063030 1250 926061780 926061797
    0x1020f040303200304060e040b0409030e1018050603040f0605180c090c04140604030507030b010317160209090c030708070501021c090501051326010509010c02061602070f03030f 78
    0x480702240180c02a07a8083c42d503204100034007265000700400c60b03030403100900200d1180c0380807004c50159181000308401095001e90101d81178a81100741d0b40c19190b0b40d2500000800c045280100a03604500c03816020f02d01c00000f0400b070142a268038030f52950070010a00c09428100100072604203100703180d440070b010701ca02510b030a15254a0081c0507400365801c46090604015080c10407241c3c092311158003403002c04c40000003a60520a01d0011b5000d1149a0403541c07550400010f01d50100c010070300380c0c0408100f5444003014011a811005030140c80381003039503841200d00d910700003404419692510440200040810002410406690080e825112603c920824010310041c10300b240e20701142411a0501c003035403048000d00b4001d0b01d0200000d551640d1100504134200b40781801c4001c124003d60280c0c5d50345800d005041d04180302800070080704508210003034a072040030340f20b0124074901690340343c2030030701c208814800b400b442503103018060307603d00d0040c26500b2041180404502000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 926064280 1250 926063030 926063057
    0x1302011407020105220513051b07081c0b0a0f083309010f020a11070515070b0c07020a080a0b0603161e0803160303050f0c040b0d0e01020f040303 64
    0x1c0c0c4489507410784685050500304d240250740314000c5002c20840510081c4000f0f4141c1d650140190703c0301c44848001160f060000b10340c600c000403140e400c2106141005001c000400c109c0c229440030391550000c11010034594035031000790116158440e07010510b440023080400500180382c044500c08400c45260310720300031009070514525603c0c4526600c19a8010308092058059558400b51200002414030b1100c43c41c082242c100c181441c00140050b1502009001c1c10406400a09401c98010302d0190a09201c0805407040303100c001c14001c0d800d000724802c3c0f0206026215a95801011050303a031307071100b000301c0c1e8490135003000b65481c0d403040740810858100807d80500120703504405031209800c00b10080e14800d011449480b00c1d044030f0000080400050001d004413850b0004c0e0880c2d4240c1c1e6040040944001505000407000c0107402d014641d18004100d80c02c0300d040c0101e494580d2440905100203210031b0000304c0c81540009000e544050340c074002401560300c00d49030748490340000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 926065530 1250 926064280 926064317
    0x40c050a081305030f0f0705100603022707120608010e01240503030a080408070210050d11030c160f1502120f040f1112100608011103041101080a020d05130201 70
    0x9009010b0802d8100f0406151404600e40081c55040c02c00d44140c3d147c01c031181c0d60945070001a040804d1015030314070042c411890408030b904c0301001039424108001c26400d0620f2a40307040508001c1c18400c036801204c0c074464850b001358000700410002000f0391181586403502814007010740e01e204c45400c000034000d10382c0094881040c0c0300003400860a20801d1a016910010080c1050310025410301c2100d005984aa41c85006001641e440b9900c5020480100b415180161410303005480280204559000010280e60303002e0f00e124001e00b800562401e03e9a07c1031005200601626104502c2c0b0080e0130702c80d001001481d004125408050342c4c2c01044039041841520000c1c0b00b0101d60a081c00800c2c888101100c119000a0091640607200780103145082c20030110740b000582c5a07003040101d90310038802c50050040d07418032603145281c1070780ca81002d0548a07540605225108001c25108103503030341660721004041c9400c010f58181121040030003860304000b01c1c001044003100d030380d00f9050b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 926066780 1250 926065530 926065561
    0x5030705150d0b0a0e2a0702011b080c06010e041b03030806120316202e180909060e160b0f12040b01080114010303050d1505040c050a08 60
    0x14070103441400c001e1854109405000703a015031591140c0449000300f00d100a841d1414080d01141c14000c1010640c5680d1002002240c1d1079982448018403242001d43d8020300b44900c11540e0014951818901e4039101d0094011100448a1403040c0b1001041c0c9414042c4254004ca01030442c48810040c01810108030781c82c01e010040015024901140b00c1d814001c11552a903240705003620b040c1159801180b00d08042800142c4045071052448110701c5011601190b100c901610f03146c001509110300321175560000c900c1232a50700e00c0c04101e0800188940b00702400311f80c800519840c3e5950307540e4041c000d0600381c1c605071801854800480040c040024010321414141404545114034180d8942d0103904101aa0b0724410420480320b40b46604003601c9a04c00c52107018400d03059410004c0031030865546031034041d44010248014008650080140e43d0b20080b0300c98003083d1821500450440703809558403031a08241030200120307000360410041c0c000a105a62210395582c2c1c1d1140d100c00100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 926068030 1250 926066780 926066809
    0x7140c03031804020a090b0f0d060504090b06060d020d090b040201122007080408332403010b03060a0c0e030c06070f02181312020606090703050709080307050705030705 74
    0x1107110b00401c40c14203050f00502807100c090b083c020340041da110300c80030b030325403025142131020000011a1b0f04000890300c603c0002e07103000e550802c0840e03090b44d1a00404840609002c0c401c400104680611540c1e54040303403827000b07200e0000c0c05011a140303080b950b02c1d002078400324007140d035030a082d094107291841112921748003c52910184120700300d695007a6806103900b0b6070580ca04210225a07410200901e1144001000c18105102010b011840500c5811850340340c2c111076040500c9042480285c011011445581001d1f21307206a20002030b0041c1030044006416001e82c00420812032119400900c608240352102910300c0c1410b02019182c01d20000e03c50360002e0207000795004202c821601e02e89091010f8000303801d07204250910003016004803041d60045c548456060104400305030075200c0044580000d145608100d00010501003004180c40109660356000504242c801d0282e81d00070810a01036941d24135040c20070740e88421403402000d02a01c00c54400145e182409441c100c0c0e0803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 926069280 1250 926068030 926068057
    0xa150c021603080c030d021206031606080a0b060c06090607020c0f0d08031503060c07110a050112050411061317030c030a0809010b15071a010b0d02160807140c0303 72
    0x1d4216034600782d141e045403105268a110501c01c1000b001d140788010320500c401c4da480f00c9814641503082603c0c100c252211108221042c0000304240c1d80c002003003c1c1c000d8105030000c00c903241040040303001409003801800780c0740700341014070001e110046001401545544c2c01d95583c3d441040074071003080344109100790807486441540780404c80c0c100c05107800c0321041c0607494801c10b5100c00a46070000a480d4000f0541000800e28208002c83d40f80625000086d111807031110300c2c002c0041c040d1258483d489181d681c4440010307040041c1400410780c030b0a402055162558400c8500c01d0034102d41d4007859000c610000009072a00c0000130035222010000340c01189402040c1200300c4031000050554407240d9207820784202d456840c013020360305425680d815a503c0361098102403442c0002c1074045900745e01c02034014000840035608545c0741003800200965903451102c4011342101e540c04000d001ca00021070000200a101040c504d50081c07034004540e20b414440c401c058607440380340031141c5107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 926070530 1250 926069280 926069323
    0x418110f0604051008060301090b0906010906060311070809010c060c05090301291314040312050f04051b1c14070902090d0f080d2d0e070e040807050a150c02 69
    0x40303200320317032507035024001034004100d581a80c1d46001c82d2210a41c0d014440e41c02409c018048142d207840360f00000d00040c6418408075000180008092141010180c909900059916620f9029642104205511602c108441c1c4201c660041c40c50300030225551295003000c00440c040030f40b00c1900e20050300e4102c03c3d062860440c20401141b1001d4445d550001074544c011002d882c0c20040e6850700c61406a1123070700004aa48d840c40701100e500070002d204803000c817024440401c800182c0c451098201014052400c12080000345a881c2c000c2107081041c11105044070802c1034881034103900000c55412900c0307003034035030721220245c3c0182190250031250412142c00490705560b558807915000f03e003094604a8200040010785610480c0030962042c2d04049a030401c82d82c0504140541d11040c04110003040346488541380c070510b2065442d0000300d44042018071540a04030703252151b02000b118400b800c1803900c412116000e59011a2a0303280640c820142400815100d613100540320303007803c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 926071780 1250 926070530 926070559
    0x10f050108060c1c060b09101701061101020f1c0b100e10050702042a0e0a1a0903160f0b030115030c0203090301240603060819020418110f060405 64
    0x43c3e83c011680060b98810803110381610000c044c426000036050044a082d580d904084c24000d8912401f0707406400c1003080540d888002c1594240d0605498403850402148908800040e0181c014490042402040041e4542441ca2500d2402e0318000d401001846044914001c1058505940d44460301041d0400c1a0182d14a0204099501d4400310700700a4100304003600480e04584d0403101ea044190300d00309000d418482d4080707100d0300c254014503014451580700d40c04611008030906c141c441c2c2100d0409210150a42c0c20161615110058106c544004410910510f02090391040c1c4112100c4100007090540038103040721b0603034000d150070307900306800740b4812001440700000880c118001800900c00c00d84c2c00380210b050380035402d1411107580802100b440080d0710710f94001414580307440010050581c2c0030980f40315001100a0604c5142100d00203e13000e09070000c025840c035000440c0e01000c010510108a0b0340003001e81c1c0707015107002e13240f0611070248298041c042c0e1040b083c040619 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 926073030 1250 926071780 926071801
    0x103061a0721120b0d061d0c03071206090515090703030f0c08181504080a0b150a05100c060213090f06030b0c070c03080a032003040b01030206090d050f0f010f05010806 74
    0x525014050030072a001c454a0311403c6c1203e0030b44c0d0380f114565009114451444ca802c002202c44103004401400c0494074100407050340b00e142d49402844903844814810511409100c0b50303c4181c1c0300d400100c0c0600d8402d4106403500c00f940400c6022400520301108418410362401e007400741d0000d007181c5000012500d034410b842c000f9040d168480305404100c52140608030191005129550092569482c00d1a01040101c2d0040402c0c48181151003411540c1c1e40707454030765044070429a0b01802c15854068111030011000c1c8004d49800d0000900c034940201040f1071030304a0306861001c1140c490641c0350340c0113036001c1d80303c040e00540703031440400c1040300d0100061120302d204d2030041010565a90351100e030740d0040320503000400d6840d2014070340014100012100320039000c030201d2441ca040d81ea840030080d81804041e000d070f003000c104840152114070700081020b4200013110482111000d02660f0394007142ca451859508104002c444440280a464107950313254010b8801640d80e0381d00c2e071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 926074280 1250 926073030 926073041
    0x4050406020d0c0207080705191707120c0f0e040b04112d0a1a040b071103030d15060203070309050f04021309050708010e010b03070e0103061a072112 66
    0x2964140c0d07080001024002d01c2e0300c914441100c050300070b011210b14158140b0700781003c940c450750040700290005000d1482c2caa00c8801502c0c101d07030302c90440c0801650701e07038a4503e8680044425a80000e241001d124540c0d081c3c41c01c0314240040c10501c1500c40052403000c40f0143d030010601c054060200300002c0d403820813104a16005807a519070080a070f0b000d90302c4020000c0c0c16800070400500d045116007401015100a8140e4512444103500340e00f41181c034a20440c811020b00b010f001c01e4020403c80003407040c0ea80c1e000020100c81e04e40c004440c15200402c0398642c801803041001c5030010703000d0f0000c01550f40c80b503055120407011a281c00c0601c085103600280550b80039a00b045081c1e09000180d0b00b50008d00154280011503150002010b00420b206800c10b140c00032140004004c01d9541004884e0f02c0440c0b0315000d00359008200c0160041c00041c2c205014294440441d07101c50540b440203400c0b07680c0103081140c0e84090b00e40025130440b0002d078100c80060140c031200c494020058011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 926075530 1250 926074280 926074283
    0xf0303080121031704031107090213060908100f091505160e060d050c0702030f06070e0a030f060b041104090209130e0d050a02120d2a1b050a08031e0a05040c05040504 73
    0x1f103006410311041da414420240c00c0790031015400300711003d252041c07441100140040c0c0c10209000c0d41440b45e1741d5036540003010302c0307480c254070351560140c0ca5003540c00401005500c0215012520311442e03210380034010440789820807031103001c03855420601c0707091050044030029040030701e0507c4600061001d013100074440b007140181006080300588040007251240c10b01e01d409000c0d07070304003103034028440d102c01001d0f24461141d10a0a0000c6480e040060304059401400090501c070907101040251942903000f6901190104000031080613940003440b1101d0304440361580c001040301c0440032070b160078031096600d070700201340b1000044c024002003007021940d00454420002030014800554009005078418070385840d03041d40b03003c0c01801940120200000725115915141c1c90040c010203800d50b1420401456001c0081400030038426508025002400159686040d080d403c221021504411030030500b0000080c910391071920a0902803a440b11b01110a5071420003000007a1502078070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 926076780 1250 926075530 926075537
    0x30604170c030c03070b01080706050304080f2203030e0102011409030304020d0f140d0801050607050c040507090815010f0e091005060109050909151b1b070f030308012103170403 78
    0x500034220784100060108944240c4450b9569070404106500b272a0099128105005080c002d000004000200703032811200850004c03510342107101982c0d40140e0b041c0c00c0201c40c40481d5032010007071581c0103c100c0152035080c0c00a00130141c1c2d40130341c002141c00440380002260400d1000c50018506a000f40c403006004a003240b24170407060311143d0a22a42a514900071340c4003102100010740c01003c101d004000403100ca5043c11995103800b500c600640c040c03944150303034850014040c03a000704044009030030044100d403500c4d140140341c181050002e0041340112032620400082c160350205009125248680141200d141818060005040054061414040d01940120b541d40b0b41041c000d121340d8aa900401040e1040311020301e1080e00500074200844100740c00054040c00c2c64119000b0303c1000200d20400c40306035092605082c1a9000524030280014000007419404a4810f040e84c2c201010481083e05416030ba401c03003444610000d010800c4201d107440814192400f4541c028020305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 926078030 1250 926076780 926076787
    0xb0a06030b0c0301050901050111030a0311040803180301050907080712110907020c011103030709050105130e010b04170309010c02011808100207050c0a1d0c16060218030604170c03 79
    0x280c6042200208442c004401c80c4040010009440d00c4406c0b070780104020b081107191008044050358983c070842c04064113041e142c4048410540e5400b0440d8010002075007925200d00503070650500705054414403034400d46c00d1901142201d003001c00c1003800c5803404401480018606824601c441241c0d1805070303090000240001c0c4d0b40e856500d0454401c250b95030103040b540c2e1404001601908003521086500c0e80103004200410f0b1300b1442c0394040d1002403d0103522080c4003500b11010000070b40080304401102000094107804000140003502d030000000d03038540c61848015541d82c0a2166250f00052005641402650203010b024100d500540507010000d0740b2000443e1524504104030a601a400240b01050010520119291620403928002418581220300340c1004207900c040c0c1100c5921404166200d04200c210781842c4801d40c0000c05c0c001c03441c03e201e4001e410410646c0f00c170b20030340b1260688030324000c15040e11940e44504200490008500001d206030400050b010140c031082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 926079136 1106 926078030 926078033
    0x130924050f130204081e1501150e03120d140606090402210c030106030606050c1b0d0501020403111206010311061305130f051302010207030b0a0603 65
    0xc403000c049421501000954441001c1003030b1108910024000400c604007040060048090300d221040128007005801c0e2510006844070001400503401405a0f82d0a03907000c1e2000446468410194103010740070034980b00c0d10b220000c0900c5000304401d0061011030080268906180e0300000c0c80b400e0880c003080d032034058959528400c68001c900030f44c032100c059051240b20032402505108604280740c0850541c0e10a000320f034002401c003140402c001d4055012604100000b00003060b030b081c1d0801300300d204104001c4d40e460f0b00888843d0650302180013400500061070040c2c440c450700141c00001c10540c2d65010101910a410000c010004149000d4110a9409098403801e0345c2c0c3c10540d01a0344001071540202e6444601241c000c110495075030700031410a00752490410140d21016840c2c40c2550b045440240180d000c48410b01c0007440702c5c4045d0f0f410020b92030022500c4e07500d0307 = true := by decide +kernel

theorem cover : BRFrame.Cov 925899280 926079136 := by
  have h0 := BRFrame.cov_init 925899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 925899280 ≤ n) (h2 : n < 926079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
