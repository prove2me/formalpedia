-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1588
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:43:53.550949+00:00
-- url     : https://prove2.me/submissions/f9889398-999c-48e2-86ac-4937f7e80b20

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 285431654 ≤ n < 285611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 285432904 1250 285431654 285431723
    0x9060f0c05070e01080d08010302030604080721031506110d14040b070c0f0e0f0402060a030b09090c1009080a110111031206030f01090503070f03091503051509090a 72
    0x10400440c0050f86040068101c5540308100d5003101000e000444220b0310a000007903254000e80040f40204000c070019265040c0100400d444c101c03401040c510500d03081c803075004086038036a440c040e26007170440368036002020a4103001e03003842c41604c1c5003606ca00000b1401d505201d1018840c80301d00051005490192000e140f03070729910704072800d2861660440d8803030b011000e80b2014003c510044260f0010340543c0411440c601192203e900700010394000403030030010036548045100ba02c0e035500e0b500c6401004c3c808081d241c0005264140305200001401c0403080c070030012820400c0e042c000898054071f42e008409010600c6500b801201d039072042da20b40128a03c00419010310b09044201140e004640860448100d90030890716a0b00341c82200101400c0c5070002d10101020484c0840380c1c130202c920a11704100c5030350300d1300302d5032481c41e003520341c54070019594008200e54880000c840e00344810080b1214281481c0005c180b658075903080800504046840c001140e03001418082d42401c001c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 285434154 1250 285432904 285432913
    0x518030409140105060901050315012106090b1002070e0901140109020a0f1404120c0506040b03100f181a0406090e070e01062f01021201050f0a0609060f0c05 69
    0x480303607004082d040c1c0c1814206030000307a000028040c50904101c4d0141d400c107840d014110f5885619125581c22005900c50622051441c00b8500d51018118003000d500085030018486040c02c10340170883c1c08a41602c0e0003501101c8000045e00d40004105044a0203c200480603607030b04031040c0c0c00350038074101d01106c0840c0c420012522408540140922030000d50b80e5100c60703060b40e1011942c101d801501454603030001c010500100d10042c201c440054000c1440540566880001c114a41d10581c0000ea041b070011081c801c0c2d4803901c0e0041d100925041921505142c2840c09921066404010408800e5a1030081c210300c440c10804003056690b000b001006659507492205000c1e002c004440741842c020340402040c44411460040c0c1a07540716520703201c440d03040d9500c5551510410846a070701031088110f01c4030310f440034002010040300d0b84401c01070315403403c0d0903c201c040c000007606205001200f814407007a503014156030111441440e18a180c1c2d82002c4d804ea40d4240c410380050310b41d026 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 285435404 1250 285434154 285434159
    0x301030f050c030a0b060306060d0c0524070b01030215090f01080a2004050111030313020d05031608070c05010302120703150e0a05040c050d03050d0b011205040605011701020c070905180304 83
    0x617903442051007980c054060f6405a542c2c0400c028201c1c4100d00c006182502c1a40e050081d4101110b24a55055031004d600c1c0c0002da64862684031500035900850300306140720010300c1182400d012030380507101001985418508481c001030300709000420360b00c0c10405088001000c03507903e0340008a02c0719408192180f80446007a12850a5000e4010a404103604003030030f80b040d0030000103da1169603142390104940900750308015004d2490542078489100038030000080b00145009504414441c940c51651400d09103401d1200c144207a00803811301d032040c0034114001c80c00c141e245610002c0c61a000074050047e440070f410741c0f202500207200080d090010030005030100c0c0d02c41d6000d41d0003041899041561981003000d01140c943c1d0050000740103005040684805800000c0007020504000e02030860b041f05900c1196400ca0702a149180c645004001d20301c0b08014400540d0500b00003580762001400c0380a560307030326502c503460800c1d940b04001006c5070192260501842804010340b984d0341c0c0e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 285436654 1250 285435404 285435413
    0x14010e0d050d080601050a020a1e141f1e151d04050709090c090c170403021501060305010506091302040306020a081b0406081504060b0a0906080f09030301030f050c030a 74
    0x60400302d80d80041540c01010508540c0620190340179281d0fa9801400c1d0b0103001e83e101c020460b0745902c0e003a5440200032030b040018942c1302841b0b15550a00c001051140c4500e42c00c0e100031000e860166840903d0400850b1801c0c0201d042032103415180324001c20314910712040c0c41c046501c19400a002018400b601607540e8400400085c0a140030301d044514080d02c07861302600321030300007600420b2051105420460314442c3d410081908405050043d0900006070481545050440b0203c0050b0400c4006140e02c1c3d01c4040c09601405052030104140d48c1084042a0644507140c0824461000502b001283e074902c0d804540155600800c1036465200c2c001003e000810180c54840c20b001c040e03210300c14800d901e0425202201c0d01c80d0344240caa0780341c0c2c208500d0f100d44040c00c034980158803a82e02180d5016000c2c01040801c1440d030320001e92503d03003a8000d00c8a0000740103404102291002c0c865019400825681503a030072420001c08001c0628049203404c103105401501400f81091600c12712 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 285437904 1250 285436654 285436663
    0x31a09120a0f08010e10030209090304031b06020105070e0307090e010204052e08190b010c0c241803030e190f0e0c0703021b0613140102010e0706050414010e0d05 71
    0x7a99207440e03002c140e90703c44610715200f102c120380840286d400044104054907101d05074640150040090300e01c1c090316502e806000e01b030354410313208d0403d404035410040194240315083c1d2120360f5181c4800f42d0b410398400291500c50603ca80342056440720100c4942c41029812100200001482c4844ca40580c425483d10203030360101040342d5400c10b80140c031099009a8202c1c0c421403a001c40c2002d05201c80c0d082034010105405424100b103c948020f00c0050054180030f8094004202540c40080086140c0240310040d403c1a1040113407014100040070146107010042d25414100304c1c103000904408903104580d040c03511140e031030068000141240030892883c095582c110b03080e2400780e603800c2881ca00ca10564100400580c000b480e4140b040c0c1090160030104540245924a051403c180c02d030142007440c2c20043c141029815070701020343c0c091240243c0c10080c0005070400514241e0090154000e500c07801c040182082041c50580c0e2054041101045c4024007d1a1031001810815500d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 285439154 1250 285437904 285437927
    0xd051c0e010c0207080d020d050310080316060f060812030a0b060316020705060f09041d0a03020f01060602060705030c0a140706090b0105060915070510050106021f0501031a09120a 79
    0x140c051303081d0205180c1da000c6284003215415400034815051480c804841c1a88014032210b01c8070307141031010074510380a20080014400a10051080740f102d400d08108880350300011707002c1c00740f03044010842440081032100800c583ca0308056200e581d500214005400c902d840d00d40c7c0038000008021541203400071921107400d4590896041c00e403500d050011034440c10005a11080061000c80040e24084e0001d0314021044e2600c0301c82c80c0038185140340781000c144e00444c056004004d40080089003440b80742c00400a91008020742e050545002d030441c400030f010042241800200320000341d00500900040050303170903590740d903502039092060062110000c122058a020742c0001018500300e4251004002c00a107202c113985a00400811140d0210310101d80a0042400480c04d000e12403003824002c2c0004d4002d054403e80c51b03030501c80c2001588c01c0a001d01441c00300144007217030309a0040310513490001d0f504141c82d200c0841c51807a00c0130390350420b1002c5600041e043d201545c0001d22418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 285440404 1250 285439154 285439157
    0x309210803040515040c080f0d050301120f05030d09020301050615030402060a27060e010e01120b0d060e0706020d0201141b1201060509010e0307030b0403030c180e1b0306030d051c0e010c 82
    0x1023204041641c0364000c03081c8020001d43c0a00040c40080150304003140c2c8a0700c01c200342e4082c1c400e59034401d4216003000001c061500ea4845480003507040a00400b58403400454260301000b101c0b019003a2540005040039000e8840407070700c04c0034107004014544c0c010591441169011034003040c40104151280030380740004140720342c14003603075025611128160364140c60b0404818a828000310043c1900c42d0016440b115180442010a400b807054641d0f00c00c6510141c0a09030508101030315102c640d81105046a140c01c09080580181741e0550390841600100c8035540710004408509a004054800e44200810300000441d16000705c000c0a6502c420b890720380c1607079103420815445088521015282108240014002a1090340425600356403810a5414078440e400c106201c40d020780c114481d4800c0034018002080b85911025034044221900c0070301d1407401c03202007a00ea0303880d207868000340306021501841c80e01e450244003102d10b0b1801820010301c01d4601605010f0107204a03070a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 285441654 1250 285440404 285440413
    0x2a0715030c0e0a05090a0b090c0c07121106090a1e08060c040f0b03070315030501050108010501051e010305061f0921080f070201021c03090309210803040515040c08 72
    0x81c80c031401242e00c40744a000c014541060f080c80c03d03003071007042440104030f0703030145907103442d4019a039691350400e50046184c105041d17220070904003d24a400800c1e0000000c3c407900c1c03000f81c0300150704191028480d040c150341c078940300c10003040407582d55042900301c40c58900844840c0500403850031542030403120194120742e00c03611400d0461a99100318080d04000e5402d0f10f9050101c00030910040d50030804c6403800040a69100c0c1d424282e800050300100e038242d440d01c00400400d0f00c02d00034180942002c0354003800c00e9110300210083d10400721486814503807194006040d607030f1403018070311074485440d0b0032080800513020010312101260284e88000d6010300841c2d0305c0700300300c1620300d0b0040d0340c003181240ca4298000865501e540046404904611912400040380401058030b04141e400d80d4a000c42c0301c41c1d4510740a010303541940c0285411407008a0080d00303102001e8515440c040d0044222660f035191030400909040d00c58807900640da403440d050004200070140140d040380e41c5002074a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 285442904 1250 285441654 285441671
    0xb030a060b0c1005060d0503071a010b180d061d03070201030501090b24070606031421030a0216021527011d0303130b0904140c2a071503 60
    0x18001d601980705038041e698000b800c9425000110341c403480c0c10940003410442c0b0708003039684152455000580c11580342142d85d0040e144a1703a051303c0a809413400c10341890a101e1100c412400c001c0700814800e12981002c8109001d020080e484044c09100d6402e800c180917100302d0b0a076035240e0010304101c0c0024941000060044094032a038a100a00180581181c0c01101d00450b031035502d0310104ca5000108000c8040003900e80e22491004600c5550a140d140003908802410540c00032104401c84440e1500006440003480c2102c2d448540c01c000180c480100c40c00d941440680844000d41040b8410864001900741d41c002d0070314113145191081102c0c061440311340301203120800583c0840e00c181070250340c94404004196495030064100c0341485114035000d25080070a500c21050b60400054091717150405006034032540701d440388260128180700000014a125010200700d030340c180400c141d50001049070006028280050031596101d841d2031521032501c1c00b04a44078003281c58560034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 285444154 1250 285442904 285442919
    0xf0c030e030f241b0f0f0307090609080c090103080f070f060b03011d0a02010c032a0512041a091801060503190c0203091516030e09011403030f090f04060b030a06 71
    0x955208902c02d4131424002504006200305540000d076940328540014420400c14095050241d481010340d43d840c1c13000f07949003440203040c1410070b4100c140980c00503450080382e6103501c8803860440b0750107403901d566528801c84601343d038060401e00522211103031800f5410b10038650018046010110000c002d5030501d0041c012007008e03c01c0c0b96081d036400c0b101ca0300000d03600543d80b2006242c000d0a003034100c08003070400e030180d01c0780c40a01043d10440c1c0701e442c45e050082c100901c1201c001c00720360007803800c0d043c10708600e81c5170845041c4010030403000481741810340b02e031609a140b032819403641c9103036561514009020341d002290140c042d00c40341a40a100849940585020a140754000c0c5203045903030b4050100e03103000f03070384105483c52042005d0000c1d0443c42c0c0881d92140c0c041c0d0707201c0d13036042840d6081019801060380460b040215240702034910350b8000c400c030790303d021001c00030954400040d000310302d00703401c9550a55449454458005030700d80003d00110b110340c60301001000b03140c0e1074024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 285445404 1250 285444154 285444223
    0x7081f0e010c0f051608370e1c02030303070909050a110720090a0906050a021306050c070f090f0c0c03140c0a05030706020c16060f0c030e030f 63
    0x114880001d00c1080301060080c0a1401001a42d038a071054201d01170701c0c1d8448501a5002d0070044948051080c1c056841d2400889072142041071050f01e40c0c0d000e04102d000500b400c0c0c20400052091b91b1405404403070424045500d41c0e01e6a0140c256a100d1038180409003401f4028421030540c641030400180e0011460701c140022aa202d00066092174242d13101d40020b004103085001440d031142143e03001580c0d80700d40c02403040d1083c20300821100128603020046d24409041040018010b0004103030b42500300800205a40c40ca250031502d4402c41041c203490110300390701880500c10000408078180d0016045074960910540061052410446045451403034807000580040e21404e800070124245d08000e00b078000401c801c81d01081140d480301030a5611801045440da940007400c100030b1038080c00400100d6207001e030f40c0803540f450000041c008200c100e090340104110a08480c00300b600480c0b05100c1e4150240841c4c021500c00d000c466942c111502015480b40c0300c840814814048801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 285446654 1250 285445404 285445421
    0x301091a06100c03080106080a0b0a0e0a140c040905091609140f070801170a0203060a02070c0e070804060908120907030c2306250b06180c03040308040507081f0e01 72
    0x3905c0400751703071a00350110360140d00901200015500e440002082c0c0d0344030070515002e80752a151144040c204071454804644440e99450b112054903403c22003440c4500003030301d0444491b40c0000c1034540e13542c038a1078144070729079072082da002c40740c5480460440c2d0070794050714242c0090384250f25a510303201c207440c4d0504011140700000542e6400140030b2940001408207600140c00300302d4480070b28035800a410040101d800100250b80401c5200c1800101188070000700b4216900580d0303810202801409810010030140080ba1980d11300c0082203550700c2101c40d4120191a103581314203102002c15240d51a5200c20796000600400105024428124840c1d6501c0e8034074040003404c07880005e004240e000100703480400c6240c8584107108038100c80d060170402c1d1160750040301e1072070040104004007041103c8002c144000c8402c1040e032003251011a0740103601420a0013813580c40b40b07441407400303e072504804114080d101e00310b114803524a00341c550720900748006000c0c50100c0f40306a1300701c45034138 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 285447904 1250 285446654 285446657
    0x80909151324060e0a060c0506010e191b0e0306100e0408040308160c120803070507050c04060603020a030e240a0f060303091820090301091a06100c03 66
    0x4039041003030720400d5120030b201180d1010341c1c14080d00225840b0541c003003968003250215010a20134036282c82c0c4210180054100c605100884400300d807a426036813041409007510310b5103640081249642401c80c0103650044106c030501c41030101500454240e41000030039800b00304200104d0900e0701e00840e9a0348500406845110000d01e481090f586120b4060800c0d140c10303800308808004a0343c0500200040002c142c20b491661250345010105030304281d00c003412031404e01341010700140c80a4110390300a01146003d41d00c0c0d5002c0e060990400242c0b42c00c1c0e40c0d0103031400c80000303002501900508020303002c64504110f0480ca9070031780c0784c40f0980705d108210600c40300d14113045c903407246d820000e030490a1523400007814903002c4455001c86101b03400c190082a4200030401c60140401008150000c00000500180e0a554542016404a66400030390b10704041b884c2c8041381c5096100501564005943c41c400d000c5021361900f2607082940c0e007a00420218154509060085491f83c5503550706 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 285449154 1250 285447904 285447919
    0xa0c0201230315061201030615081204090f0b130f0e010504020337030203034201051204080c011b020d1b080d0e100902010c08090a0e0408090915 64
    0xd0505440228070a203e07042d41c08503050103850412001e6090b042c2c0a54460710b0f001401558140741c1d110920f203d5807100201d0b501510306048032041080540c0c04440c074a030004030344030a0140b82035001d8102610703c40d410400b900c44041c81207030340380c000308040ba0404200b0003c0409068519003030303400c102d50294055000c00140c0884c96243c269282200030340d03c6001d15016100e0341c569298410380e610640c01680040140700ca0405010710700520400d4420744000d070700c440440706c0340300030b01078254100d00c410f60090a200c440c0d0144084070a00f40841d00c2480c268a020328284c525500143c49402040d031910100e034140400908070500818110b80003000b030510a1001298040119814401c41c011504520b000148141025100184541c031000c6a103159041000340341c05111654081124108540140542d0700100c0c00b50307280c0c0d0407070311480d5a44299404600b6410290f40714040155103541004241700c410300141c482c00c9811510070b505134445416030540088200e441d103a02050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 285450404 1250 285449154 285449161
    0xa0b2803120c0c08030a0e010306050f121002040f1a0a02100b180403020606040c090510080a0b0306070507030f0203090f0609011e0908010b121f110a0c02012303 71
    0x200340000d41415080703850000a400d80603a01c108114030703964000d00702c0d0391001c030762210001c1e000402003c21050a2a0400a880c83c0000141d840440f604086004881151122110101c14044c0081c2118480025941c9680d103451032601d0103910302c65201d0220020081500d180750380310071124001c2e1141d0060042c0c006950121740209152038080d43d01001200e1407011702c0708101c00300746c403640c060303001341401c0d2415805000550300508224020002c00342014000341e0756285040d07580720310515100b94150381d860034040080c600030701030540c10310401c420081c01d82e174400020006248659200301d10350310b4030242680e89001d032a00d4a03500010405590585060800143c0000302052501d40140c2018400500a402105400e40d000882c41002440b01d00400d00811003007040030b40d44032404c282e080f0b0711a920345110030b078a008001c1c951168050008110340016215580b0700d4181555403e00502c040d054000544040707004c40c0080100712542d42ca260250081a2015941d581c503694 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 285451654 1250 285450404 285450413
    0x17010504091716020a0303030209040b040c02190305091e030f03030603070902070312050a05150303072d0c150825112404061d030409180b0a0b2803 65
    0x30041d184224103083c2c1e000c000390240c0d5941d045000114000d880050b07441c244d0b5030920007500c1001d40305600035801d11700c1e200300250b40002d5015000303003a03040c84006500546405c80d10f601c41d0680207540603045810502c0600070585500c011002c0490842e540f01c14040711070380c2c40b404201c5041c0e074140c00080003000301e25040e80050100314030274a40141c3c2d07101c070103040324222882681c1c00c4032002d0340c030420400e030300a0040c0da142a0322011402541003145595a10340610702131b240e030340850409001c0035800d11010306610833940d5480b0450744d40704c1d505c0f08412202c204001c11001d00041810020034140d00c1d802844100d03003c0f0130600c00480714a001c50680c2c50740c5100c400c125103031250307070b10008500d0300406840041c41d1040100480d50700b454140f40050700c4d4207501c0c25810000c0b5445040842c6800800c840440315901004689050103212040780344036804406410641e0070700070414259241c0e8812075110404442400c0c0140340c0405c102420b009243c2400c0142402100610215 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 285452904 1250 285451654 285451657
    0xb1801082e150903060b030318060f070203060103050109110d11010c170406020304090606080705190e0405130302010507050408150603070314030d050c0f040b090d080a170105040917 80
    0x119580700c800500ca5960b074000d1031940c1c4003007036101e00060f0000c0040c02007200c00c1c0940001c01004030000c0d030074491001c40d210440e020410b009481904006514844980c400055a00c2c55130000c007940d89030743c0c0d6400d10901a0040d8a000c0741d5491141d10003440901c0c2c0400c20f80c40131504070307100b082031032410801940c003450510340076120141540300e00d8040401700b030020030140010382d0165480c1c230320f0083c8035030a07184140c01aa0138018140c08001e0019401810b9400480641141c01800140c00c0010f44450130b6640115030458113000401034900e10000b00621140d210b175008005640d1500c45c00c440a0195014070001a003010a1703404001090441c2d4030380042006050303030a0300d07689503248403062403036400c2c100980d04003041e82d42040400d48513031030340451521107051030000b00c0380302148640701c4c03806003903c1400c1c0400c421815845501e26281c2480c1e2056260360340700500c03540500745645905c82034018102071000810142014082e0095041d80b05100c107085284020a0500d40e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 285454154 1250 285452904 285452971
    0x30103031803020405100314070b1903140a0204030b06010806030316051204120c210204020304050a151d0c03031902101b0816210603020a0b180108 65
    0xa0000722680800940d03207a21406005002d8011700c2c1e00c803d85180b400100103003182c1081e03242600640710400102103400202e07482e8102d107019103c030060000304154003e148180380180601104020170001c0c98885d0300500641c0d01400608000307035a007400444d8000800c841c50b036010340041c801c42480140c1c14541911591080b8160f03201c0343c6041d001445640c01950108038922101d248080c01e02066001c9100a0040300314407108030302544a03000040000a40c0090103503500100003014851300307200302c100341c5070700c1201201005036041580000d01324001801d4518a00101e205004c060b000a00d600c128401502544c1000e44115100d940d21490203104000e60203079030b11120b43d1010314400d074120700e0b00708503504d1340300420303001d000700340030780080100042203004c10804e0302d1113030040f0500041c0d000b0b1407030404680e012030504802170305072580025000014001d01142d0f07804804060b124280121700c3e0020000c0042e00110f42241080e29019200000410800c02c03139002d5010381000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 285455404 1250 285454154 285454187
    0x403120504181e0515120c010305090a03020303010501142502010f0518131805010e0d05070201020a120513030501050f10030b180a020a030b07020706031b03020c1504030807080604060b03010303 85
    0x80c0745c0d1005022440032a085d14100d40250010400300210b50303054480d194204071000c0080040106694001e50b81c0d01c41806214140203014400710940d5034154116200d101102d040c406000c1008000914002130000c030403400704440c1038940c221a4864404e40310884046000c100c0080341c500b0521160030360401400d07039032980340c1c0c55183d20014060b404005907072051000007246007091202504103010440c2c1002000010400a005070b80d0015440c070401d50050410507a14410741c40c16038051007081c00140d11148010700c000b085c0705040d4130941c45000b10048803813441c0d64010f00840c980c0c3e41d5000c020003007106040840c441d0200e444507440c10318800341c100d0b01a0400d0f50005000912150710407100c01d482c602c10041216418010100100b00c5420140020242d203c4070900c0d80c00782c2111340b4100359006c11020003030341d800c10070548615038003003068810741000c0c1401405018112183d80200d4405004101107040c10300c1072104541c07904541c00c1c00d42c2d081daa8100c8100361a00300b00d80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 285456654 1250 285455404 285455431
    0x80403050106030b04050d0e101805031204090e0613030c030e060d0606120b0a140310050c03010e07020f0601031203091406091515090403050403120504181e05 70
    0x20025009106810107140a00c100700207518043c9040c03880c080780302c0d0040c000c2000c1c1901c2d0000549900c4c854128400090402c4140e204050260841082d40e0b60301c881ea01d072080a030300000c0501190010402c0d41d00c0d5076018424444e01251061356040143c40b41180c0301411610003001c00c2c81040c9003070506c0c0c480d20300082c1ca0f015400c0018469084166008903090703865904124864101c0800708036a43c82180a0005104100002d400703c54544581c4d40b000c01c83c0215506142d45c00d0007a8403142110010030030107418181c83c07102c510740003400780600703140000e00400d803d24000a4104c070007054110050585a003940d0322040c8071608120000249074036035101d640000d0a40007280d82d144a004000c0c0118902840d440d0325240301032040c2440180354600740401c142c02d50341201c501c8503051b034103d1190b03281c610341100c2c6845180d00142000b0002d007005036a50b40c1c0100100203c0c1caa040c49200c0c80c03113403000e80030112035101e00b030014004000802d001c00c00103290089a4010401031400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 285457904 1250 285456654 285456659
    0x9060f0e0109111005161a060d020a0320060309030903010608030708030703110d1d0d0309050307020f061c0e0606040e15040c0b040324021e13031a060315071b0804 72
    0xc0001b4591000403180050030510300044241e440c8034030340d40203604548403c07002d5100d40204140c142113000c0500811740011008c5030f4000e0144001a6072180039001795524500222525165006640b0191095082c802c001800b904000191003120382c200c4c0c2c00078a0342c5c035503240c164010a908168110b000c003042c0a00d0300d100e41c05205004150704441903030b110309502150810b003014420041c1c1002c0c9881d02c2d04a07000310b0400419150310a505072030600701b4541d242e001a01d60f025905075080047c00c07240d80410040400d030841c1c07503d01d402101315411600d0310b00402042d0342d48030001d40d082c0ea02c08034480d54078403008142076801034000e49401e02000d4450508001540c481d03002960445081007512150b001507100f2040801c3c203064003142000801c1c920301ca103000030f0100c4112000408110640d00003810342e03000e4002c1d54010401503001c11010380300341c1060b000f200e13068885d01903c0320f554840c2c0000074620744104d065607907170540d0a544038003107161641d406801b602c0080c0e062102 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 285459154 1250 285457904 285457927
    0x5010510270303020f010608010c0f0c0c03080c0f0f030f03060103090f0501060b120901150501080403050c010f0b120601050a0512010f0609020c0f01110405040203091009060f0e0109111005 83
    0x71140654083d501418400c885858601e00350760780c170740c01503165030303d0001028140355001e43c1014540c2d40c24903000403c1c1c049030401c01400303151078202078000503000402c564142400507400701d08017030ba079050f02d02e0f00d000484215203034010b81c580c85240000c108005166984650701c00f4030784a10882c51400f1055981c3c40d09030850310a604003651014000600c40c00310101c4190140d8400201d0f0b000b4403039480540c046400041c1c5601c00da605000114000c5810940038006036042482e080008012111200e40d10b40081c21a0b17203040c82c003592440448140719100030078068140c400c0030704220700b828501018440c009100401c40c050656850030800c0094200340640401812003031409601c400d01501c0317190400040100d130883c0e80e03240c0624610002c6115040d282103450403100141c0300d41e69400e525041854044a0407506031030950340b0002c201d803582c0420b00301b00790007004216444000403142d080303d6004001400403072000d00c5214507407401180509415800345441410714010030031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 285460404 1250 285459154 285459227
    0x3071d011a030c0d3809240109080a08030604060b03041a090127110a030302060a0c0c02120d090803070b0c090105070c12060c05282a020306060405010510 68
    0x34000d04032a0031170103075216982c0c5050480490300088074800024145508001c40961104503040c18401d040d030000c0301c85a005110a800804806058807004506858261b03882d5000f214014030071850b0000c0440c030a6184401c0e02d218540c8644440c41c8510f0030540c42e444070300000c01c0d850b603e44d00d40400091101050308008552462000003040316600c034500001c0c2c2800411a00e40104402581000032a0b40000c0c1150080d60034032002030070ac040c10b8021581078518400294125103000003c000e17484002800283d24030503580c40d00700164445440680764810b51030090200da040340c0105d9440350541008206d00003050400741d2074108079946600d00300944c2d61102d1840d100d01000030040c40741c1030040d00c124403810302e0301a140440d8590200d100030703407000c44040740d0135040302d0380706102e801031103600d4a0035174049011040c018104001040c4880042d0224020f0180c54042803040c1054011241664030003000c412a5889090044514019400d06605041400c152162041ca000c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 285461654 1250 285460404 285460451
    0x2281a04052a040b030a0f0b0709030209010608060f1005221215050903040e0106050a09030c080c0a080f120c01060306090b04060c0f02070b071103071d011a030c0d 72
    0xb0550030700b203034410800040f5040c0d9079906009400103c155800900f4030702140d0b4003207a00140042603507e07602c1c2c00b01c400001ca9003000b500416000008210030b5040300002e0301ca11403c40b80c041e03400389a03409014200007020b5107440400d4041c46100302b05001306480103442041500d0000e0050359502e035203580c4610340e03982910300c0d404000c680c0c40443c6481c00307403c2c3d000c0c102000540c60302d46409144004036005104140810201092021000d4413401a10f002160080c0880408a071186074040d11b448206030a1442104030f81d800080c5980e020421207031f22403444010b0710002c441000080e038280c0c403030b121554065503603540110014100d4451481001d000d100650360918082c94441c0440c1c40303038075a800901042d126a104210b9000546600340e40ba552001600c49015152055241001001c49039142c01510350100ba04038248a011985400080c0785201d141d80c0d0f000010075074001107400b02e2200b5000c00028207040312030402403020484a15000610b14507031444032003040140d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 285462904 1250 285461654 285461713
    0x10c08010302011412040b06030309042903010e150402011b1a060f091612050f1623091c0c0311010512040b04020102190302281a0405 59
    0x11401801556404104136890f0420f00100600d810202e0b04800d604100c01400145000c3d82200001c0003600c06209a0703c1302e101c007800c01d22200c0b41c4c81c481d044400007180c0304103108072517680030710043e40fa050041640454002d80a0144400c1048006406e03060043c1f003603043c00003d00d50700b810100d10501c1f01580c1406003a6103c0707403240c400d01c0c1021034040944007034410031509031040c500c1c1e42c840705815005aa0b8554000c0e1900c540030050380d100f0b164120300c90400740b400c030030041038030b0118000602c14990005c1810201c0f644400944070070424013201c61035680840c4a81c9401180701d401400c001200070302d0182c141c2d1030040601052465100704680b0580462400c10030401e140104c050b00c1c0009080007820050141a16880300000402c0030700303000d215501080035039009000e41c0c20442c0c0d207520b074541043c01e1424080d540d80d0018103845656246403c0d003041c50748021b1745d00300700c842e03000440104c02e2440018030004414041c04c16640d5000d40b881400821724561801200d004c071301c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 285464154 1250 285462904 285462917
    0x16060b2404060813110d061b080901051f12020409140f010f1a010c0804030206030414190305070303150b030a0902090a1802060c120a050409231603020c010c 69
    0x5000c002800960081c21191240144600e200c0c0012401c007420005d0103c1922942c01081c40d60030500060030b46900503d02e240b01083c810b540e0903620a05092090100754000c0c000c0b500d403a9030604c0d03e080d600c21030035a0a541e1160a010441c44520404d00c520300051022580050075291218500c2c4c2044480005501c44050140000d0080c0160b0403c030513031100c2089007548250585420000301d0b5410b0b810401000054001c0000c1101502d0181d5000b8190741d0f1030780340500c3d00f55803a8031740700582ca000e4460081c800341c9103015030f03040c81e100940c5940c4460038254595400e038003503c40042441301e034290f4050040780d0b00c0c03a1240614880c1001c800c022810034030034010700c0700d1200301030300d0400c0c03c50a08141001c0e50389000f100d2803a150313040d02c04c6555070500201040c02c040780c40b500480b6803840062550301083d80500544141d402001b401c008100c200c0301c00204400c00c0d08810b800b14868031000036510306100b80401250321482c01c1c00b500e07002c1f02182e1542112100120751010481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 285465404 1250 285464154 285464159
    0xc0607032109050f060f0703090302010609060e040b0901050c0901110f0a050c15040503072d0e150102030c10020c0a0b010b031501020604030c060b010309021908100216060b2404 78
    0xf04020082681214001404150602c0e40c82c0980344e0b240100310409041c0c540c0d01e44403c05200754015001007030850030400945442c0d1054072400071040c0c0e002d80d001c0103140f020448180c01031003514000c40b500c43e9150324000c0f5400054a229030b40302100c0f40b45020b05c2c0b0b5603406004d818420221124440c2014028030410f0074100244884a010780c400007250a1100344400e480008540007076404904003020040c00c840000780c000c004400c540c01d180c690a01c4002180158681c015014010a00300400c00c40c1c079507001280d80b801820043d0750558030101c000030781140e040d80100042d0014400751008100c1c59110620f07150402e80c07092030b465500004000d8071064003800003d0800b000d01c041c0c0701300e04085d00c00405c1d5501c054005005513585841b40c41c9581c0c00b030744c0b00401d41c83d07015003842100c0c0d00ea410120742c003c1c02840b41121601504102800989180c802c95004070896040410b0920312921101c1c000c202c142c0340d00741c1010f060700003c5406000c034911002000610844070303a4039030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 285466654 1250 285465404 285465413
    0x2041d07031a18040203010603050d0804170304080d0b0307051507200306181f090b010501081e0402030f011119080c040b0a09180c090e090c0607032109 67
    0x40b08005203114010080070507910a03924854000018012401040025101d5000180c010070590344000d0843c4950040920956000a80b5a11590181203001881511201d980c0441d11084400400d0010f042207442c40e002d0644d0b004009000700074044562090300c8801090005241d400034508102002c585c11007004240c4010410710701100c2d65001d0700da00e40c080469960480908000b10300706200d090b14080500030040103c0c1106000030080d000c003004040e0600030008410286e4003586410008aa15401101260b00640700c0c1200122035803400052140d8000c0e018000301c0c1e050040d0803080c3c0408000340900094400e031030540a90b51101c419500302542d04081a810520002104001d0b250500d90103072402c843c0f00d20a0345c0ea440300d0812302194180c10b1a0440c030f10045560b502800d90340020b5001c4400314181c0c1d1034900031a0748903501510000300458031006103a11a0071682c1072418400080e02c4070314407a0070158040318403c003032000c003a54424070b00840c041c0c2c0e80e8071a81c10300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 285467904 1250 285466654 285466661
    0x4140415081509031e030109050702010506010219020a030507060e0910120807020f03060108031e071203020a12020304050a021507020f01031508060907170f07060f0302041d0703 78
    0x903010150440c40203450104800d846100c2d401402422061078070010b454080280102c4100d0445001d54082284619406125541084c007804007075502d070000094099005100300d0740140b10580003400d000e0182003020607044604503040b40c11108009002001500c104900400b5240039100c07006504940e00c103200c1000002015104a00b05904d0100031003c40413401eaa01c0f25040480790303948034010b0011480a03042000c0c842d030903104d07850001030807100100c00f03002c00035032850b80111a1191072890343c5040c00340e03003030181010b24107449030103035607010b036009100512403420100200c084c0050340c401241c02c100e40945240d00b0210800045107400404030400c8000d2054150628969070040741d401d1406070000b83c1810750307038600b00030049207020300c02000b032000c1c01c00c40700249006e4184036102d001c80c0c4a0540c00204400903050100e1011901c2d03105003440030000d003040b6140260032034030701c1900070064040c10307820032002c01e5022519140e403660000b025081610ad00f0701041c01000c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 285469154 1250 285467904 285467921
    0x702011701030c12081b010902122410080d0210050703060303200c0316090e07050105030a0b06160303052a040506030910140f07030c0e010305040c0b041404 69
    0x489220320041c80000c591100b68015078026000f14034040480b49041e04283c40740c21403a080900101c026031121250542269064910990780400060750032081c0d5540d513107100426400131080c100d00322150003401800749501c03d281444101c0e40a5075a5441402c04001c0003031400180c01c01e07221411341e0300480c059550045124503040050307a14548008000f00707100310980242610304856940c900c0c82c20000ca10f464017004003a04c0c5211422203c2c100000124810480b0150624021317280042010921400321507068455600d180d4544042c00020f017600c0382c13240e0380900140002c0094414232001402d88074429280019142030480741c201428900500c330502034070000606240486110003501c04558090340c0664480c0c0b01c445d820b9003421042c10510288920f04420602c9401c450308031075018000303030120088182c903281f80407010303110001440c50100b01c4208000080354425400030340d029014840350004281c0b070394001c0e64144d00030b5011080718840110503036903d207000d00c02c0000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 285470404 1250 285469154 285469187
    0xb0a140301060e061b010c17060a06210905060c0703020f06040c14180405300a110f0d030b0a08011527050f0106080703090302150702030f0f070201 65
    0x215071502500900c0c3d2900c01e440389005420210b440050b0380d220408203901c0a01120082c894000310010090140b05050b01c00e41c1d0300900e110210f01c04e0308083c1c1c2c1e0702d000da070041c1c0c2d64005851903400c1c1d400c60501062418644560b07540000d07801054080c0f000318010500030400075564445814000d2900c00e40310002455500000144400108207a0b00541201c2996030400c50021012000480d12111044824401c1480f101004200040494003088030045142d0030701900d2030000311014442c02507035251a48140c20418001c58502507000c25400d900c0000c01c07100603d201d0300c2e401d420b002c25514200c000c65100d40d0308800b00d00e8034000980c0a0130100e0020420803c101c40d12194142c6a4820085400c400d807020040c1000d03039110031140c0c8100c0020600050810305c03140121004240300d03440020b62180d0104102d0f910074000c2d00036450b0140c0c028031801c0c2c9455000c8400340c0f4080d01403410340c03008001d0034414450100c06400262403540005440d8115030002408400c40d40381004e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 285471654 1250 285470404 285470407
    0xa1706071706091902162a0b04120221060105120309010507140f0304080c0301052220030f06100f03050d08040c0b0408030304110a060f1b0c0b0a14 65
    0xb10343c840d21403580d4041c04040c031020b8a52044480c420007849081c84266503003501d541c1c08001c1c40003201c0808510102c144104200d00c491604c0e402900450b03004014000313104000400182000803108071140c1d000400105a11107008aa07120003a21500d04820a42145004100078603048040b64110941c1c90041d600d445040b00000b4558854084000d1111a96281c41e484204042140034501583b22049036520b5848a00d10b6503030f680480c41300e6120f5820071001503640c100c801051080c442e2099004149642270b41e035124000c108090b4010300101528502072010b54040010700507940d003082c080c1c00c650401848040040341a6000800b0001a044041000a80010340c1d0420440070786024442a100d82ca8a25036031000f1780d000070450880030601003000e030b401100035800303148241045e9650303030050701c18000d06540c03d108000229040d041480382e00fa015110001d0404e03080030072031941c4049070752495454281904608944000482c10603a0f0b40d420000b11b41907400303e0030115 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 285472904 1250 285471654 285471661
    0x6080105030a0b0a0e070e160f09031509021f0201050108030f0a1b050102040b03010503010b031c03021b0109050d020d03060510112a01091202090a0b0a17060717 71
    0x1d070344240d40355004041015820020700011083da210074107402d448030940b00c10f541d0b108107c1804a2087e940070a040d090355024410080c00303003200000700c0c0084c1d16440c2d0107a1071901e45031060a07800e161103603106d480d00603200060360382e243c9000e912850a003807180d03e50540c4000900310740c4146c00c03a4115a20070840f607401e00540030180d45003070002d8505841002030f040d0700c2e5005420360b41c500030700e80c1d0f0000c940861111212700c040e5041c1c030002c0e0300812070745218800b0541d0f542c1c000c03485505d0320712507910f182c03503c14420f40003811885404500f030440407a80d03004a03804c4030f0070f100381991581c00c054000132100340d061081c01d100100916040c003045091100288050141c000000c050140007940c030144880144845881a003010325030800006085003522420000c5c0a902400581f00341c8002c80d1408001c03000404030360300540400041d50f40c400c810700083c581d550346994000401c4100107075809045114031160654040a0308c0c6c2c03810440c80151061046007140301e05c2c500c2040c00c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 285474154 1250 285472904 285472909
    0x602070f0e0a020306220f0b01050304020d12020f2a151903110a0915050403080d05060a03021c0b181b190f0e18071202030304090f050901050106080105 67
    0x1250b0004940c1c500140da0303440701000a0150b1750070045006124002280c00d0510800f40e51184214901e410310600c5401914001141c080c402120000d502080858150010402181805221020030300450310f03800d034401744080c9044c210810680355801d50340b007000b8460f81c0e2900241c91000098801d8815003c50241c02541400748440c6002c1711070300c2d82c1113124064482d402141d5001c08a100c2c0c180c1d2034210020003007540a09024155109040310800016284110304580440c1c1c0c00803006410241c00e0b0a8510103003074083c00d4190b00420350340d000300140e510b1081000300c0f0510141580360308030041c500101798040050a0701c1030000f5409010048400c04905002460004040c1807041404180001c410301d01c2d41c42e2819603d607940b907020503440128030130102a1000e02a07046995901d80c030410424040980710b11a0b2900080c4e01008070301e64408501043c584010150303403c050303c0781c5d46402100e880c2aa20000303107444005011110000788540e034050210341c9420300d2a503040c04007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 285475404 1250 285474154 285474179
    0x6011b2405040516081e071d040203070e100515090612010f090b09010b092d150403030903020904060608011404060b010c110607020d0b16110a15050405030d11040602070f 75
    0xd41b001d560ba50252601480001403000c40d001c0c010a00c4144803011501210350341d0801c0445d0201d0017842071003008079406041c41986440b40040c0381202007103605200a01010524105505070b00362400d02040b1074681e200d0024141d02c00314004110320704d41c500308030750022003490b0b032200440601e480d00a002c10b1b20764000d9141034400102265a0780c01900b03010446544400014804c0300d640701410044202c145054a0408441207403c5503203460390a003159982d00c1588001804540680800c200500301100340d1544140a400005000350b41c43c1600307800d6031504503d064410240c44200f02c00c2294501c0350f2004107000b07180403007850007150303148051021203e08041c81030501294440031907442c0741178114030547c0f045102042d0304001c0081c02c520f0010308044000308500a164404100f00040d5155540307800045091031101130740301d07443c020140948140e4260104121100c50482d941c0941e4a2101c02400c845075200d01c2d05100a041403510b030014207000810200810000c0c11481 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 285476654 1250 285475404 285475423
    0x806060711060c0d03020d0c082401020f0106030303091406150103021c110d050105180103060b0105070501230a0c091401020a02180108011406011b240504051608 71
    0x40031045095220700014410340103035610310740b0f540b140460100d541c0b41c2c150094100b4008044040c008040030f001d056520320300859005441041c1c1d070048017240380e10085003020501041c0113852400b24480360590a492072900709038082900c40301030300b0070061281c154000c2034200d50041c0c045800c00000300b00d641d104c00355600b4101500802e0f04078548c008a05518071230144040f04101c003401045209a00c1d4011025001c48246000000105801e00802002610310541c8194016a0039039407084011700300b0224032410020280240780000302c0910074500101b0000205240c0c00c00e4040c8014925030300107044404039400c1c81285950b00b0780000c051001e803806085000c103a4910140101c0ca406c1c260316010758400e406a106112001201e15114181d07a103243c02401201125602480e604100b030b1072031400540c85580036524111041d0445a04a10034220310032121007928190040660404079100d9240d07492050000f0400700f04680080c010866801e00102d51030808850340710346011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 285477904 1250 285476654 285476663
    0x5010e0d020a05130207110f3318090106030b01050d051b03040b240a030312020c120d06050a060c0308040203011b030213050913080708041a04080114011a090301060b0d050403020d08060607 83
    0x44600e10f08842d42c580010301c1240c5000d040b04d48582844800c00cac0482c02c07252500b40954620400403038018070038041c0300d001a506031186460411910a800d00500f0003e25407980902101c4092401d42c11060086010320f025030b6141d04617041007845540300c0b400d030010b040211000080155155102c112001c403c8a4041c1800252401c40ca9500006803060300c1c4200c08600031040840151501103000e0907098000400801050b602c60007401340710240b07802001c002c500c00022400000744225401c50303109201a0022403441c0585190441011980c00110013198010030b226041580741c0303c4e2900101021545801d0ba420101c041d41c107050322446000e440707180700280007814000e11904440c01440d510034201200c807403115124149422900031101d142d4244403640300340601030b0803018165084016807082100a114494801d070b03000c00e80064141d5250040000c0540c1068041c010750040c1010104003441c05d442c0c020304102d400c0d8131040c1402602d409101240e00c070a400e41da200e84c1d01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 285479154 1250 285477904 285477949
    0x90d0507020414010f0807123c03052106090112030c0c030c0906230105090d05101d1908030417032502010605010e0d020a05130207110f 60
    0x2a4004100035000840f5a50000b010340340000400c2c1d0b43c8032280c00200ca500c001524002c031f03103440e040180c00346400d1003c1c040107000400707500300080d40000c00900300040307080c01c0e540300b421070048529400060b1040d4041240829161100b51030381e6a070242d50703e01c280e00c5020f6131400100103101d1500600075881043e000301c1070302c0105405800e4000c0101e8120f284511680d90b00c0c607007000703d0042030280c11003003410102e0000d14000142c0d2180001c091403454442110f0f064070044034140c1040700041d5000c42c804034504080344042c03041c00c5031112017800100c1e070300b5081200c2c40c0d0070440407000204554020049161408030039000d20f10706662240010703a507a203440c1460b03207040a00e0804540b00c800004203101c0703c1e0340f1510341c40c415440c1d015400940351140750b01c00e03800c0310a0b41c402c103400700e40d4404c4501210f02e0303c00e00b0b00704031501c02054403602c02d4880d0301003098940e030035106205c440d07400038406c000d016008004903074441d82240e400c082c0619540110380300b0914144104040b428 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 285480404 1250 285479154 285479167
    0x11b0303150909030e010512060f0301200c0c060415080a111605010606020c0d0209090f0d050409050c0a09030204050a0b030d03020403020108060607031707020a050d050304050c09090d05 82
    0x42904800441c070003240990410940b0307024203800a04451508801043d4082c0c0c00c0c0205501510998448046441d0004040d9880074244400f10184d60101c0382c2c99581c621000e0191340741210407030341b1405001c5285444900400e216840d000f4070840062143c2d0050004000d42c803013040388003402501c1e520300380740c40d9103400441d08054520103c3d42d0425036404144443d01101544054030b035940584002d00000c1c0d0b4520041c3d840b10795844106030440c1e032001201d00035003411411250003a0f2142c01302c40071a0010136031142420300804401000500008040050107858050240c000840da24910710746258000040c0003014188002800340b5180c00000e200075030164000148094054143c841210704070000030003d6000e4001240403030f40e540d001c03c9141c20702d2015520516450b45030040d043c0082544011a500000e00010840c400c603581000041c800380308800d03017503901e6290f440c0c807401c2c5440c0a80c1040380304c000c828000e00c041402c02100c9040003401a101c0e00083c04c2003581e034103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 285481654 1250 285480404 285480407
    0xe01170103050601150c1e02011d06030106050f070c14010801091404031b150f0c080108030a05130824010909020a18020d18050c0306090304050f01090312030608060114011b03 77
    0x2c02c6880041c00c9104003078187c90050984a001d2034800b4801d99a00043d1001000c1e100d81d440020601c03260028018801400702e41d00034002000c60b403000382d154904180301a41c0b405201c5041d50801020200802140748680d604803200380c1c0581220a024000c508500d80d60541121005001404204600030000c800b5030302c101c507218151703410008074078502c8403482d1604003900e218078541d900a031078488034841551183d00c1090580d021800a9460010196000c444642043d400d12105101c0791100083d0407404004462010400d1050040ba140440105815810050b41300040e282d041c0310725180185d60b550300c1c500c00e1f50310201d22800c22040001c0d0340340c000e02840010909080c41c001d0215501680c400e554052148110103d8518940c003c0525450341c4007660080c1d00e541c400d110030b1246142c50600c00d01c8401d01898801861552515031034110810100c084010940d02c010a000044091006602501c0d1088119142510600c002001c080d5003080a4100c000700380c68020406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 285482904 1250 285481654 285481667
    0xe1b03060714030c21090d05070305070f1a011d060103060302060d110412030c05070602070501091a30010f0506120a0209030a121d0603190b030d0e0117010305060115 73
    0x124041c00720003403900c43c5400b6081503c006c4d03851060900c2042d10300c00c606441007044505c8158103540355800d0a203607940b180c03540400b80c141202e50300c8100481007100e02000c04418002c1c0b1310003070301c8003100141400281420801034811410141402d0083c40035894003002c4540422928100240c4035117500b11200641c05203400031f409020100d500070081c15404489200c3d0350740200c0075120711550f1201e05aa40310603d2282d01c0c0800d000c0c0100b0800420a68800504601040303c1c483c80d09000039040d06030700b440c69403460544080e004c1213000408000070b120f800760501c0c1c20490529030401c030004c0c6950094100150707410410a000804546880e0140e0380b213110080d00322991a40b8510780214412504042d43c4005000400912007484180745040038002000e0030141ca1070321004100001d10500280d0f0340c00740d035200d4140540a8404000c107441402e02a40c6e44040320500c58001091000c24010581c0310701c280b24018408900c001c281a41110780700075071000c04420301c26041e07944 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 285484154 1250 285482904 285482917
    0x3111e091005040c0207030309352805010513080d090201020c030304092003070e04020d021606020301090c0e3604050303010906081f0b040f0e1b03060714030c 70
    0x3060418002130b1100e40c001a040d0142d03846600e520110940302d00c1e5854102082c240040101242d003940f0030f641240d58000255042009030a540990340d0724180b042201040351045600d81505400d204140302c420311031980c114600c00340749110702c0c4040e00d0f130364460302403240030f115a10303595507043c0e04681c000c2110b48016000903007aa0340300d07983c905035880281400d9003804171a030012200d01181e596000100c80c420b0b461034580d003411103442c0d82844000e4104560590400317034200f052825001d1641d04640708544256005652503041c00703c000b094914900414091041da4050701e0b05030f0756006c00622480128140f111102c100300300c00950b140010b851031030030018030f01c020b20050040c013000840c165071056509116555035084e5027035944088841480349034005040281641210703400444014030010301c003080030540712541e01c0c02c44881c1d0501013200d620900a01d00141c00c8003031540c406d4181203000d000f2a28014a01401040540e00841885035000000400d03140010064808 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 285485404 1250 285484154 285484159
    0x50324030a050106080606030106050907140a0504210201020d020d0806100e0603040305070c0f06120c02070b12150402120a0b041b020f1501270f0905030403111e091005 74
    0x5917a924020161940802d41c1e0b000d01039400e0010204490030f01d8240c445c0100029030741d2001020045c1d80140c69a0002c21000d02000010400011000903100c907800110500c120030300c4403c603041c400039103803000300000c613402d540100d009003000b03980200032283c0c8604166204001e4450b400030031a0079411010700a90710040100034801856801005030100c0c0c0c0c0f03e4465600d1040e11559640c04140e5184a0b5000049241071603140002003a004100d100700c04d07004489180d5107070030601000d40c010003c0d01c1381d1000f10310100301800c07543c9102104c00d0300055404514240403000d01510702000101040d54407601c5a02c041340580b00c9600c0300030130410005103490148078822009450380700321b54012525118602154200560216401d4102d80c403050203c00321130241400507290710100140e52843c02d07070360b51040d22204124041c400046110314061951107045182c060303c42c1c034271500f9850003100d440714440c500341558940c0e10900b400845188060341e032008204034102c3d005810031074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 285486654 1250 285485404 285485411
    0x41e09060b030108070801020f030a0c0c050f150a060b0f031b2701020c0303041a0d05040303022212030804080c070602030306040b04180305070f0803010e0610050324030a0501 77
    0x14800c4030040156050350000003e40310485c6d1794a458500b81c2c01280c003440003008003000859203062150f4082c1d03018482c02d060100b17083c0115120a07003418018010ba4031190008400440d42c110403400540e88205941c0003040080e0601d420103089001d07000743e20000c04000401b0030100d42c40d60741280e800d960906c400030780da00800e003054141c10604040408101d240b42d41661040d6001060b50070031003602900550409291081900f54211008041c1c1c21080c4108611216955603024261040303000391005683d840042c0c40b904640c4560f10484607198201010038050a4030440c4001c44440c0c26103840c11700c503225130805042c10322445484008610407400c0c005521500403029510403c000c6400300405142d0600380001d60300180c0ba50391245018110400000e1300030400340601502883c40544504250703036680d11540c2c004e03000300281400d82c07010030411703291012454281c041c0c2031030564110305019240c04826803064000304e00186402c0e80382d0100391810082c8102641c0c2250003031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 285487904 1250 285486654 285486659
    0xc0503040e091c052106010909020c1b1c080310150305090c0402090d0f05030c030d0506030712081b0309060d09300c020f120609011b05041e0906 64
    0x2507641c8500c80384403042d0100b400b03c841a00c80c001d8003911781010810000c0c0444044010320022074000c000d09081c1448480c03c00841c109029101510b00140b00c40300a02901c511412140c03480c1030000c1c1c5040c0f0070362504484110f00d03001c5a9682c079811781d20010321902e03500e502d94540c04003c650380000402040d0031001e961115410341046004d544004142c1e8070045da10700030701050303100b00641c46400108040c11480010000c946450304e4030b0282c2c3c15a414405190783e1142903520503042c10704c003103480b90306021180c6070a203c1c1070020301041c0d54006c5e24850f039607201c80480c0503406982c046104166010420a0014021902c0c03052004101d29a201031510b000c40040000300d005803075401240800c0a40f900b0180705001400c00e9015440448865403001202d589181c0c1c0400c07a0064416110048580c80c2c0740c0a0380554220240580303124074003c07010a0850b01e5060000f1a40c03500c0c14045004160454211400c0e0380c1e00014000348580b0303420103902e001c042e90f40310007107161801000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 285489154 1250 285487904 285487921
    0x2120a120c0809030711040603020a1e09021303020405070e030d020706020c040207021f0c0203120309060708061027080a021302030f01090902040b04140a0c0903080a0c0503040e 78
    0xe980c8016410981007050034079526040341e04240031107241005070b00c100141d20208808a83d100702c889001040450300c50b40703c3c1d000c00c009203100d07848012005034500a0480d000000c5d05000040c100f480001c60615504c02020002041c40d480041c0c0035035550404210000c0c03040e80c50345620783c0040c003250b04520129100030b603114118803441c00140110070314000d6038a85030080760b01c1143c004001c1d2505800c150308070340311a40b0030022841030001c50710341c0700010b031010b0140c030320340e0f88801d1035098032894201c00c000e09021000b4401d004020310720702005126501d2181c4205011134074904690302e10a60202c2055640d1754014000071000d40050008245c0000075007942914400e4401140c4a0810f050300820f0340410b132042c003a10b810140040c41881d03003e900100d21a4001800460310505400104003200c00c0c0700300f00c00c9452881400c00800325140c0c02008022009407911218032881c58807403c0d003030b01401c0701d0082042420701d0300000b80b02c000c005450107010052401c40d50ac0c185003e9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 285490404 1250 285489154 285489167
    0x5011a030106080304030f0b1f09020403020a060305130b0606070f0f02030d050304030e0d02270703060b040e01170319020c031e0607030902030f0106090603050c0d03050d0b0102120a 80
    0x20510a600786040032030501004015102229400b140d111b00182076507032000103400740103010038a025004040807144680a15181000b00103000c4010f960707034114018402c000e04241c12003024181000c0522071000040c0c80d0381e0702c105801005441c029220780c000a4001c2c0302e5890003030a0b01500c01862000c0c0702d802c22060b2007035031080301150000d07550780f0f0b41030b1040c5c04212000f80100b4084100000213041401d80d040750710740700070103079114043d04d882460752000015a5440700c1c0e5080c81c04006007690940b00d030001a04411700a1030400d440c1c0340115502c030780305000e48104038040751500d0000103030410030741d240c403070b84603102c0014041e49040c001d40d0b40903800700092007845003500d100c0e003200700c45c0010311890040401920b15135a440d04c050340a0180310340100c4c1c2502c500600582852402e105801c00707401c1400c404603c1030f185003440c602e0000400c1407948504020950f410000381c003c0200c402051458078003141d14254800140c0c2003c00c1e14240001c8103000042404043d5440403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 285491654 1250 285490404 285490451
    0x1b0524010e06010305040308070305070e1018050102010b28030204111c05060d0807140d020d12020901020303190207170703111606031a060c070302030d020312130f0501 74
    0x10a01e1995948000440c1660000d41d0003401184200d4041a04140f00781c022071760000050401e4400342802c0400315036121740d003000d81000500308030040070b80400c584e540c100c01408248001d1286071046000602100c0d130310081c0e41007465500d040e44080541c1c2100b80d10045800400400495043c031a001405501080c2c203c910740c2a184500f20342d03018903201d443d0040c0d03c0606400f62041d056994600c099100f44000e895402c103001c4211480304040191551b2800144c0c041e03e0540040003029003010300305440a00a640103000c8032200d030760b0000980c0d500c40c11003031424612207201c8290b80000e10a4401c09065440034800c514040021b07480180182c40c030940c0c40e0328000060000003911130828920613116412024002c200c590b00c84e80051501c1e21410040701e44aa00f1440005c08950002c180c1110035084a00208190701d802e110303c0d6901c15040c00554a8944c00403000c244004009040c20301c82c0b0241e808200c24000c07545000c260a60f4450002c20420f81002900300c0c84a0080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 285492904 1250 285491654 285491669
    0x803070b0c13030305030705122508041a040c09050103060c09050303030603060a05071107080616050c0d03020a1116030606270c140310030605060d031b052401 70
    0x2180c0c0032865002203540c0c42c0e0320807080e414020f06554040350b295002412078010010107009030388542c19507e034480d008141c0c0c1d51100b8110300b00c45200d1011400300c109a1018452000104000704401010544614014001c1d06900759210726000c03a042d46940c01554840745403200110800c51564020802000c0544600060681e2242059034900c012a00c054054010401259406d2050380140780c0041c80b80c11705201040000c401c09250080603407051555510107003e000c0021140d1842020500440c80c0c802c1c40c10f100c04a9072682e4250640d001c2c070805500185a40c0c4040c42000d040346003540705800e4035038005605002c1d10104541c3d000940d41d40d403a00724002111900040342d0318001c802543e0650110f011881c070304004107003440042040c040703146403e00340d1801c240003c5101e505508041000079040d410940204c5074010001c50068031b881c0c0008010a0304240c02000700005503034141401400362070103e0030801d0082001c5003d900f2103500c2e000c01700704420755505a0341c80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 285494154 1250 285492904 285492923
    0x30c03031b0702030c0d080f0a032004150c05030d0204121703071b1112060901050a0504021507060f0e0709050a0c0806100519080f090f0303010b0c01090203010204080307 75
    0xd00240000a00c58998004e5042c0c0c04014103c615050117070b1690201c030f01801a16080a00c0c00b07035050510340c440c0942c1c40020b6a9860b20945041014440c5200e84520110071410035003030140d0780c1460074928141e001408891000a800c201040084840d056140c50041d52215580d01300394419545c0064101d4450425001403046a1000d00640c1e110307540d16034600c40c14034644c815140300100340040c01d4800465455980300a034a4520388814400ca0f8080100040d1406009450841d007020b807000041b1800c00b001d001c00350362071605c00e01341e240c20300182c02d0360b6039128500b1800504402d00c0c040001070070006d0340001c81c2e902082440444807083d030309000070768500808008840f58480c21801044a000100c2c0d0030341005400340702c00385940d003425441e01d01d8000245041020700340106000074001020060410441311200b038001405c0d00003098a14030104059481c3cac003050017245d00f4200c3c04a00b41d040c0b00001d410041c00d050b00030f4021540c90752186c0210ba00d0741c2c00403134182c2d480841c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 285495404 1250 285494154 285494191
    0x2a0e15010f0207121103010509070f081b042f030a1409030703030b061608091002010b0d150b1818030c0c011b0614040501050109020f1b0f030c0303 65
    0x9461402075881d81d58040c20105090807001080d6103403840059841904400c1c0c81c114680b824803d0030302400c001c40040c0400e529040310708183d24400c2d08444595003100317600c03110040e0081000580500b00729000b0174802128400c1c20380d0045c0e0181505443e001401d01070012980500095004107100d0b0302c1401030301d10185041c038640d001500d460459500130000080880d100354080d07400c0042c0142034a203011f6440d10f400e20381466149040c0d4601c400040c03001611703d00b180e080b181c01040d60001b400320041100c005100f04804403005040c00e0b4405085e2050002d10383d00079002c03008010443c4a46045d4181c801400c2c1c20111600303189040c4205d1420510400081517070240c0b40c042e00106030320084100112180070340c1c4d5001900d0501ca9000d010005000c60207103406020440b0381c41d9440740781501b886030039a0f006a03c180056441040000c0540c1c4200040b03900c0c81684500b8003940080c202c0c00d1031300c1c0c04517003a6611414007020801c0c100c04040400118040c8800e4501d5034030402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 285496654 1250 285495404 285495407
    0x80601020a0f08030c041502070807050a03020306130c17010209130b0619090b030a020703020607030203070c0611160507030c0b0a05030117010f020c0304050a0b0304050a2a0e1501 79
    0x46001c1c802a0603114142c0e1218006100320004592040941d40350909007680d800307100015488001030314015802c40030060045034000c102c004020302040b14101d406900c2d54000c01e0720b841c2c01501d8060094130300400013013400303001e0510b10700414000320425001c10b03071101031718000d400440c1b01c588680c08170400c28400f00d100d40a1024a40c00013015103190806031040e10304129001d90090061200c0e00350001221841c00c0c014510541d401803025941c0d074090324000b82442e000134020802c1c5803040c0300f40a481584a50142805075206d80002108091402c0400ca907006451055541c00c102d18000c004004002c2000c034210f900c00c00d03030103c072a9294003031708246000d0880140001501480108040311421a8989a5800c403500000308102020340c04030581e030080d01031015075400050104001e0509003240b500405d1003981c400d081d42002d968440d29100c100c1009000c0440044050380c3d891001c8811040348426464201c00040c0d6500c40c00c0315220301151002044c10808181c1a00c03075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 285497904 1250 285496654 285496663
    0x405250f0b070201020d0809011812080702071a0a03020c0601030c03050f0a0f030c0f140f0c0901140906031018020f1002060103031b0206030c0d05060607081e120708040308060102 79
    0x640c145c01411000407170810884000000514020a80d03485100e03901c0c1b40200000603040d134900414910230615640396001d81200d02c050032090440d40b02660400c11000071048048402d00540c06807959000744480441c043c0c0995000c5940301e0003200000820007d014201c0b4080703a00c6607007581d201002100c03050740c0762551044003034035220049641000191283c600d00043c0f601c070f03c0c491041c0c03200315100c005a41e1000390051a00d680900c0d110078045900f0082040d24030301c00c07203100c0030660415010804081043d0440740c043d4aa100c00b28046e5a028012100d0036054a40c2c200301010044282c803008000b40001a4003500c41d65051403503038200710216290707005a42c0c00801c0c0036403a541c1c007210f0f000841c031035540008004a5a4400598440d002140201a58880c403604c0d0700f60b254140c0211540030b08414070a01c02001000d002480d0041510f08640e504c000214124807071044508151161015021981c0703003074030800c4005a04070341c643c0c1c041c50003951843c0450f034401c8016030340c0c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 285499154 1250 285497904 285497917
    0x80a03051e04090516081605040323030a0f090f03030c020f03010e1b03060601021507030209010306030606061d0406050a0b03060d050304121101030c050306090405250f0b 75
    0x40d000c11034842081410031000001e100e100100519040d540c2400d4011208155101c104040082150410840c0d000c0c400d15042000e001d405a0110507259001d0180d100e1f9103c024080c10000c03106039035040c800300303c00d203403060404203407540d8042c181b80061407004906a6540820700d80040411280c24000095003520380c1611542c0c40c0ca07e09400f005100c0c1c03514140d1070761540d03c0d4410440000700038884402002400c0300080c1c4042854402c150402000814840c1103521030b40407040c80400e001c014540000c2103090059944407060300481c0a400d442d000035044505200d40010560b0380001000242501c00703001c20f0b015146401000103a03001d03880ba856000c06100c1c170500c41c144440c0000c5400030300041c0b0f1040c040354550303602800c41d00254032a44002600758402e5080c000c02e11603424002600b4070741041444440c600280103400044c11541c01140044001400c21404004130f07941b03942c004415241e005000514549504103901801200010220000885800380402d0710b21 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 285500404 1250 285499154 285499157
    0x2010804062d20030c1b0304142b0b0a0605030303040803040510050603100b180103050706020f2d10060308090f01020304030b0105220501243906020f13080a03 70
    0xe10b031500314408485d600440b43c107400c0c1c3d10b102c01c1303009124101080140b00800e102c14a078200c550440c030800c5105c080c007041070f00040300301c00b900104003410b1a010a0800b684414240841e403034560b8400010102900100c0e007601c0000244014491200d01640c429031043c0111041a0115000d20301a00c1c019103620740c16900030710201401000e50341000c5510b140191141403810070180c00310740178580a900946140d00400c0c4140034017a4103209046201c5400f0008141c8003216203a550302c84501a4142200690105419035601d60280041203c90609840a0000703641781d00745101554403100020303118280100f490b100650011080d201185d4106442c080680c2c42e120038080000c1c072011401e00b018410f0380d04010b0a142c03074030403135018210308408044110444c100840302c000b800c81082040c0152034145221801d504401c1014035002c0c41c001c0184070300d0080e0081e00d0041403020003020540080f856181c1001a45c1c00f03000c08107608040a01e030781e95100c10070341d112000a0000f90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 285501654 1250 285500404 285500407
    0x504020f03010c0c0327090b030c0604030809040f0209040c090503010e0d0210020901050f0408010204050103050f15010e01030b060d090210090807060503090309040f0c030b0402030903040302010804062d20 90
    0x18080303401614040e0a0300400b100d400e403442d140d10910300c1da01c10746d5008010101d540701e00d03a1840e818100005081858180c41180c40e05045403144a018003551115a101b2354032151b009010a0b81070301a9002c141000c0c109101784091060080d04480c40d502440340203610301440c510004038002141c0d004c50100d50090007604000007500341c0039500458400b818410100040400c81020a0041004010302d42c001a101c034141800181903550180c0351441410007d006e204156040e068410429102424280e0240c3c05500058000d40190014954801d40100d40112403903640e401c4601c0c290300c2200c40e1000c490121074252031070307016030080c0106903201e0034040c8a90f0340101c008542050f0254101c82c00c2401c241d00003400e8440e9101881c101e0364407950119002600350046000c0c02070215020345c110302c0e05170042c66a030701031440060704200c0040040ba080c0b220301d90002c035802c1c035006503450f034a840f4402d480380040f510302a40300c003692906440050749081520380701e00106c3c000d800705 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 285502904 1250 285501654 285501677
    0xa020d0b042016020907050301030302060a0c0f050904110d0903030506062a0703061d1603020906150d020d091e0b0c2a070501112404081c0504020f03010c 68
    0x10340d0603810102c2480f60f20b580f03c41201d00980c0e02c00802c544600c0d110340e1420b50360745c114034009040120242c442d61070541000c1403801360503044a000f604031201450507949a0884100003000740201d1941a800c543e030006899409030256040210002d0282e00d09010707d44410090000d10b120351aa010340c04648510203c0001e019076131041100802501282c16131a100d440d070004440d034880c221000020f40e81d088a80b0310100380310403404546415a8007034070320318640210b898800000c04491046005210503c0e80d00d0422064a1003101403220854030b4040040c0b030900101821103081d151844001542d5102503000c9808030070301d9601c245087c4440c0c4402000e5519900307c00c907140b0b410000030099152201c1c1d10113440303035840c02040c002c0001914010015021a50342c01021304a0b4110301d141c408026011480300303802003141840f443e070030354850502100c54002c482c40341d8041032464101c2c12110a05401c00350065000f224000084016007080608860940a40313002103554403840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 285504154 1250 285502904 285502961
    0xb01020601140f0a03150203010302091515030a18050a030824101b06050f0601110c0d060212040602030703060e01060f0f090f06020f0610080a0f1106030a020d0b04 72
    0x43c071600c1c0d01e014109100441d00c0780d982c02940d030241000c01c8207030740d400b000410544c5402c400709034200c001145401184001c20010540d0074030b980354a403112200c0000401c0440c1074540c4000b40701d18000d5050103040d0303101e103440f07922100718150a070300041e4860041130300c8003100880600c0f40c1d4644005031184800309401e011002c82c81310038003003e00600312003041e1491450f80207000014403c600c00078062904001030144008041d103070504220704026000c0360424005104240724108551500d40c820b0f503071400c1c202070303c030796084e1101c185070f108144401c10841d40c01a5004003155101408070035220701da00c0940c5030013481141c002030426a0810202d5010b09241003180c542031801a203500c0d151020040d601555600500050740728145141d14450184005ca800801400742800d8582c904032490760303144090030014101c081884104000c0000340501040741e00e001406607500d9203070014030300c0d0003500300070302c00d100e51400c0c84443c00a074a09071042c0c40041a00e0a49020140c40308400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 285505404 1250 285504154 285504169
    0x7030b040503120a0524010e0118090c08070324030b040c08011d1b0d172802010e070e0a0209060405030307051e0607050d1109130f0b0102060114 64
    0x740c44602040000768107041d002000e00d07100780b5070060b003c0380d5400c042c0c0f0000b01e824440c10303600e44a108589000109607a201c81070100318a0240f902c401029541c40150070a90307015400001a540b410384254002070f0410562481100f003620100145d403285540550410107140e95042810503800b030034000a004d00032200d4200b80620010f041c0c0e603407260319982c215089241001120003c440780d4001e81c4804102080074041d00c407210304030342e40446001c1050f180403004000c0062481c1d48100700d01c81d01e0602a1059a81108a580100040c803003016290751250440300d0015400c1c070045074204540000c01008584001c14204507903070399888804002d401c014032040e40407408210003c1c0790b80c9c0800251814034020b0004d00128140d071214400c2007402130385607007201d400c0b003003c01140d160017a0660740d5038460240c01007404100300e00030705403910900306442d03440070071944803ca000d442503128074401045103c082202901c40d02c01683d81e034000344185a080c0d540922150780030300b46001d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 285506654 1250 285505404 285505411
    0x130b0a270f0e0f06010513050a090f0b01050312041d09240709060f0f0e030c0909031308060106050a0e0409060c0c030f090803370e0415080307030807111e010e0303060307030b 77
    0x5c9c00100d0483c83d03518210200a034003415070740341c104100188007a1400340001d8418500c18000c2920300341c03074800074508100e504620508035080b90070001c4d582034800e0044e00c200c40a0140b602030349020100c13403e40426420b40d02c04001444048012902038010381d484290121203444441c5006039404003100d11041840741c10b80c0601031100d19100940300c80e070006018180038400f4544400d00c4d02181e1491300d500e6803003d00c041d4044001000034980003000c43d031800c526443c2001d0421a52070104025003100000240311620382099440720690024410b619248030b543c0369030000aa22200310f82c1440c090150035003540040003844450306544c1d10f5841c03101d510400b40c1244401500141000002c28040030340407400789440000c0c04e00c1c091140743c800d19204198110314500b02125140d4034000d2420007414081000b000c29202800380049840c100c00c070300b0449103075000c5c0d032100f03042c02075504243c0c603160742c20304029500110f4080140ca00c14400a0024807401c3d1454545c4608480080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 285507904 1250 285506654 285506671
    0x14010f020303040204111b0f0f03090604031509020d080306040e0f07060e04110a080108100c050307031d07080c041a100c06110307030209130b0a270f0e0f0601051305 73
    0xc0080c2c07c414101c400c910007000c05800c000e800300c034419040450a0020451072540290020001c8526559070101503909586d0009840c0c0400c1d8800311a0800400d011030010b584801402090030400208100840c4215000d650a000c1d1015283e60150740d480005910b100c0c40c0c002c80014000c80748200d0919240b0003005001003040c0031f11200000141c0d202005520020700c4840050005000421190030301d0784201f0b008100154452000802c1d5000c064a1002010740704c2c03045000190500e038550840b400780c0070560700e802d5501c80482c0e030750fa050248918002c030b00304210915001000f503424501180041c01c80d5013030200d044811580c0305105102100e6070740d911400d082001c012140039610801540c3c0300142c0d501240300400075a00e05440080e0f00e124245852f6190540312200903004550030b204031071005800e4002400344014a40203000003091a2287d40004102d281d007003e1203082c8950142c82d00d440c01b91b01102e880300d800b405590f80090120204e4025041345a00255106001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 285509154 1250 285507904 285507907
    0x13090b041418121908160801060e0f18010f0801050610032403110909160302040b0103140f100602031206212d07120803060f06070501020414010f02030304020411 71
    0x42200080c81a000510200144103c00e10007003191340d0008603041d0050328420401002000409008040404c14040c1c582089100441c11095480da000404006070006007054003460400303801c0e0450050901c1030280d02c070001180080c40d06418440e8034040c1102404028205003400700c240c01801c4980d0351110344035152000d11401e14440d17045580a0762107612440907002c900130030801d0b00840034000d4403140e04201072440500480c3c000740001c507076041d14086228015480103034028119403000b0b81c500c0300090304124540707014240c0d8502c00c0318801129004652200400c90f502d029000c03a0541003202100404d080d49080e88441d00383c40c03090801007401c40b00d0482424200b10340307488041841400c24031000d0f004c031403caa01c12074480c0041c1c02030076200d203000e0300c000e032620400c44064000800040814482d880f9080c10b0300a040001d02541d99409080c60070034000e500c84c0c460030703500f586218008921076100340310000803500039500840c155100e54003004001c01c60000381b040c04410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 285510404 1250 285509154 285509173
    0x14060a0905090f041a01060e0d140708010203040c0f0501080c0c0705060f09041409031204050c0603010b0d0b030a03050306060c01091b0f0b1201171213090b041418 72
    0x1c440519500c5210503c1d90a80e9604013880c20325540307a094035400807010f12460042c00300662088218075440f03012164188100f5040c00c0a048600c0f00d080d40311010b00414102003481b900540046014034800c4114912503507484010007440803042c080d03240000c40e540041814030003040302a10890070804160343c00e00e50741d5070015260b03910450a0030408031011070059130500c0d141c4600082e500802000d10390078a03240441503100d101d01c00c0c0800c40324203040049030611004020020140402401c041d5032941c40e6542d291042e007006800c040c01c41c3c18000d0f900d245003404a400e03120150f1503140e0500b036807110004c21a10390840d01c00c42c3d205660300c201403408038400b180c3e0000241044844414011709100900000da0400c0d000482c03442c0080141e50300460710f000c00207045929804441d820302d02d030000c0c420304254607208a01c580303c8020604a02c8507605030003800481395016001c101c0301c3c800e041440181d401340c0c1304100840340301c040020030001d4081074240da940c08070303015100d5114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 285511654 1250 285510404 285510409
    0x10031109071806120b0a082a09040b06030f010b06040303030209130c030b030724050a1107060518030604050c04050a020d020c0106030204060b0c07050d1403030a1e0614060a0905 78
    0x11030326408000000ca0510313a02000b04142d100e00c41505100380c4400c5105c2d42421407540e0b4070351806642111503010b918543c1d5078841500c42154400e800244042000c0c01c0500700082800b2081d40c03100d02c03901500040c1c1c0c8004e01c0501c541099408064040d90400b451520154001d4120240090f0800d006031421524038036039100341580e07211711391000220802040141850850f040c6c1203414801c10744244124a03a0040b20003070740103460740c9806c40e43c1d401d550b042140d40642e4034089014600c2100000b0030b45907004005040e4007050f018001040f030080300100b40e41c0f4001640c01801b50b804c0510300c03034404d04068200c20b500c40a070b288050f01c0c0c01200d401540490384450700050b40d07a599403509108500d407078040c4100605a98800c03600300f0460002d042d480d040b940c495107208000100004007080a0f8140140c05d94540380152500da1500ea41c60001030400c1159440715200400d5009031454550310a00040e40c0b08a448150307400b02d06018040f060703006a10000610005403400030b40c03039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 285512904 1250 285511654 285511697
    0x9050d03030e0d0816020c0a03080313050d030b040b04050f070804060605060705010e0708030f0415020c060f0a11030a050f131e080106061d0108040f06050106171003110907 76
    0x15403c03555001890324001c00f03510100a00c002c0500110340000c4804402648c520b180710f01034030b070400700c074980d640ca8820788a8200e03000c0b850010468080c40e210b0748400c68042d4048400340000355003d001600300c08042001b1248112010100003a40401091031603114003000b6910610032600010490340750341c0001d0494001d13031800c0303c0d681c4d121081c2085620b03003400350300d0090116200441c100102e01c10f03280d50501480c005c03031802c1c1003000f9503000a02c1c801c0141c40b80091001d4440c6a64440b00341d0040030035440140b0b0705000c41d5180c8500080e4880000465004000741d40e5403e04002c80d401810101d5401081d045007035065220300400d4641e990f02500240e540104c13284142079140489580c00d40f8107070780c011424402001280800b030124541d403584400002d107441000d554892515004514003804080d280c00e14120010860507001100c11010980741040511a44c1d5040b01495074201e45000c002c102c00000403684a46080410403550000c115080814903051030415172940c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 285514154 1250 285512904 285512923
    0x60506030c09091e01020405010818070b040311030d020c0603062404060f0f05040602031c1401030507050f0603090c0d051e0c01080604092d0b010b0c010b0d0309050d03030e 76
    0x64129181085104030885260541c1a8104e402507081c1803805001a00036403005040c0c8084846201c291602c811080c420500034120095580d900c031504d90419420f09002845420300a100b105801c0383e1700307400000c01c182c04e01d8000300030354030319a500000d10000d5038020801c2054030501c6007000001c1d48003100500041c241543c0c1c0e5003100000804c0081c40c224a880640b814070030100810700c01d0aa01204441c010301000400d8104a080d64441c04020001d29511520004559001200304180855400100c034011242c0070403100700c4000304941e604c403d48034410030360311180f92020700b410b1000030352040502070015112043c0c904510f58074503581114000d0401c0d00304e560320b10310382d680100d086900704074240e070100301a40081c0e840141c0b0400c0f09039944031100c4500403000c4440d80c03003080d81030010b0b44107902c0c80b91942c0d40c1d808501b054000740c50a504035400d0600c2d401075420200008400150035075103a900701480c01090183d49000c0000035020143c0310400595004010480d00700c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 285515404 1250 285514154 285514171
    0x80f03130b030f060f030316080a0801050a0f0303202406030d091a09030f0723090a11090406090f0614060403030807120912020f070b04090e0c1215010b0306010c060506030c09 77
    0x5c1d03400d52040000c202c90016004144664050503044c4403a0703041d0f0180d3f006403a4503003046c044482603654018030200c81010f01d00254800d0540780c44002c0c03074030b4030f00d42c0d640c6103045000d070b000d40c50384000c03d61500d071500d0005000403010101040300e001c2c420341d88280140031700c403118540780d40040800e0800c206540071684907404202d00304807103101c00326804007030f544482040c0c240100440000c1d00300745010b4803035030000b03840c0e480e642d850762400c40c2294011013006108010b415034900001005d410460103000442c5e1070b1030070008100844400c03629200c40001c0040b441d141c1159400e9904001c0945408104035035201000c070321003560702c5801090303070045064000800c2040c10080c41d01c41a80709420068002e04800c200a1580005440030f64864880108140446050071454440d01110a6611504592041e4154500864034003610701107050b185101c1d03a00e0f000c0702500382c4000d41e40b10340021083d103900ea0204001d64400fa4000000038240c83d0120303580c030300107580c115042c2e07080003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 285516654 1250 285515404 285515407
    0x60a09031202011812020c100309050601080708031b010b09040f0224040603091110031b03020915090409050601060801080f0c0d020f0a080f03130b030f060f03031608 73
    0xa02010741107809505850384000e001400d00101c1150b100c502101c002030005a002c10482c02c135500a01c0440040038026140446500c0003c4008000e02003442042d030700c038041c650020030b00e44008900d03c020380b60b062004600e4071403280b42131005080d018400407210356030343c081c100d5180c2c0c4042140740154021484801c0720791040c0100b2413100c0211b110180164402ea420080e120000c00c00d0b54201c840504000a8014050502510f85003001c510540d208164004100d4600e030036500c88030302003102040440c0c1081e00c01d842234040f0f103d840f00140d4800d42d031140503040e001c4000e0040000c90400740000c035541d107256650516000080e000000440d100d01c00500040c4010068651070091036801868400301a2021908803682110068010002070000c42815241d1600c80c00081c4002021500050300584400d5260303003204030107012070101a503001800c41a00c8090b17900841084c030303006109031102000c200d00303084801207c641500040c80307840c001080051900c4035583c0180002d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 285517904 1250 285516654 285516659
    0x3040b0c10110d06050405060a0e09190506100611030f0307030912031b050f030406090204020f040f06020d031109011d0a0609050f090106020a0b0a020d180c0b0c0309060d0902060a09 80
    0x280c4d402500718038000c1e0702e4441004869601e11910304100c8801f2802104d00d13032902c258881c2403015500442e00786108541d01d4100b000310003e01240710310107101342040156120001180d2013400c0e40000501343c1d0050001014100000300115040b00841c2000200c081381d0f691401b02110313070364481901180e51002c1c400e500005a401004a046040c80c186152040100300381550303000180010301a15610000141191035030340c11150020080e180803600c0e15690301c42510170001d140039100060050015641c0d80038024010b0040495824444a041c440a80011942d0f800100030444800000d51a0221103842e41c030006030161416a88007402c4034281424450703680301200b4190f01074265a4010010300342d0108032001c45030ba000e00c41681c20303124114000080d010320401152414904403800c4403c7d034081100b42c04041c85221910786d0103030740f004a8200c0e405844003455003900100112241b5103001c4000740080700c044070b400584003a6a8010402d242c102d44a003038003081e0a580103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 285519154 1250 285517904 285517927
    0xd1a100f08010f0f060c05010209090f0901060503030310060318060204090c090f0608240301140601020c0102070f0519150503060a090c0914030109050105090c0a05040b0303040b0c1011 81
    0x1202d001d0480c1004400e000d03480c1407022244120795100307030700411440240030410000b0030340442d403d8050043c1038a0342420b0011002c015504203a070b113850360798030f84400002c0c0e9043c0841902d02c190101014400e0f41840c015040d40503114440101c0351048045080f080041c0041c03018001504411034001b6014a4588001e81a07032007035040861882c03005003042110691081a41d684603625a840e108003110419910340c2030001d003030341140e040d400c2039a40b40c0100d01c0c0075046481038400b60708581140755080d0042e03031520380078002c4610100d0340d01010701c801e0a241200400350003030358410382c43c210340d81e190003140e101086c004800001c2000003440007518140b071201c00030705141e107020044180c803100080c0c0760380c1a80c40382d0b445601519900c101595420f60080b802c0300e40140007480140381100b401c680341c0040851240c0300b0502234602041600700352203050400c5601400851410b81040a00c10300781d0050303488032000340b0400104131240c030658040c0d0500201d940740c0143d20750110032031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 285520404 1250 285519154 285519167
    0x6040c0f080f0703030302090102120406050d0b19060305090a1a010618080718060803160b1501050d05040507080a0b09070e091e2802130b060d1a100f 66
    0x210040d40c420000b003003919070b0104000041383d078107060043e41c5400940050707044c04a8015a40b4101c1c101203000101960000014102803010250030030138003e0f04000c20440924003011101c4018a482c024001c00d402a400305421220700411100849aa55108803103502a0840c5604201c180300041181c56045201980401c6245800070302545c1000c650384c3c1d175200b181c0308405404100551428544040703901010141001c8010b6070f0343d07601c590280b481654144107080301c1480301900080c0b0310145ca1520036120081c141d598500e0128010100d001804e000740c01a00c0c0e0707001d0007800144440d01000000051841150304c0811890203840043c1018032590105403a0340e070010030010701100205c1c40c03d890340000c0215040c0d019034408502e180c8031440c0742d00d0381c100fa06101851001c06880001d000014402c42e142c5054406641f60309041d21b17041400541c01040a2141e2100c440c181d4005444403980880074040c04025500081c0f2020b60414010000c01d07031040421640552126 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 285521654 1250 285520404 285520409
    0x70e0106030e06070c030504030c030b0f1b070314040f08071d04031e021c020109020a080a030507240609051e010311040c050c0d020705180402010c06020702010e0306040c0f 76
    0x1410006500b010942503142c650040038401000740011600c4200340c0610180c90103141c0048000440544074980307401002000d44001c1c6580d028940003941c080303100494091050f41c0b00f40102d0a00d40d599606a400d11a610340c2c1c901c1c10360040c0000b140c6e108004580400800483c1c005112043c50074425120041c00c1079841000d4051110800001c2a081203219241d0f296a01007503074600388000d0b04905044500c410b482c0000a2910703007041c000d80c15008411114000c5855102d0b0a994800039580c500c01c01d0001402314030300340040c4020480d0318442c1c002c240c1202e800911b00c150404543c1003296a0ba800041c40380c2c0c1c2e59428401c2c000e481d51629000b02095003040a00ca5045450b4035165114640c1218401c2d03071600c060980c9944907000742c132400000b200455290048818011b07407221003030f00415000d609916103800f0320101038001c01d409070303406840c0c4940c4407209071200700295010034010380c14496030b401d070016651000c0003454840c9008540c122111402c00d0b1441c880f040c140d6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 285522904 1250 285521654 285521657
    0x1140f0a02190503180d020601170601032d050a08071e0c0e090a0c080a03080c25080403050a110f1e04051e0a0e0c04091101030c030f060305070e0106 66
    0x10b00c1a010910303007042c2c07807141d4102141062912603607101d83c108000c52070b0081001c0b46018951020390015000554503068654004504041601c040090783d990301d02480040c201c0040c08c2400340310b030032aaa02100c40c941c3c07000158140011191902c0389021310b8040e0480c5c1e036202c000f170141c0034064422401e90041003074212038062803240303850724803501460740201c41d00000d00c480071440c83c4c00f040102141c100c1d031080d071859076243d64041e210746948044a0940202b03540d040042d00030340c0048100c070f8212104000c08c0c003000307101c10403140c2103008102c0120380c000d200300000310100b4410051042181d1040107228050380192080c004460200a036041c01131180c40304c01544c0301c00410756116800800e031400141b07540c2c0d0404101e401001044010f5404240300c003405050125034012401c21602c10048078015918401444229201f40e1005401d035001800d42040703641c401c2d0000d41800801e4600811038507100c0c042001262400d50044541e9480b1000070407102d2201c5940750300500301c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 285524154 1250 285522904 285522907
    0x6070f0f0906170621030316030207021c08070b16030609020a120e01020702060c10181110091802071a100b13030f060501060e030c1e0102030c01140f0a02 68
    0x4264000e0811551141c0300d5404081401c005605500c0d03040907110117a101c241d0340740d02100021042500c80c1d005a4202040c0030a408010300c0c218002c0c002c07a1030b0b032070340900000600191180c15198411001804413506941041120b0105010741302081c094003003520100c44043d20f1103c064100e0740207600c0007003d40e00601070341407090380144207500e041c14001c0d00130500017065010540244510742009500401c00f088000c1040d00020300c00507020304100041001d0204801406404190524010842d02e10705010070202d041490200d1460b58107420241c103416202c10002c4000744900007400d4101d0380c040303029810311042401040e034010100201b01d959090140540c40200c605014465142000081c3c04042420034102c1e0702c02550003e802d10004041b901c0c14601524007845040c0c002011028802020b04e80410b0185107070724000c050410500709000b10700e0808051110f100c0c10740c0020700520410b0300b000c0c050181404036a000c0b520f124078001c0317031181d800071024160700241da10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 285525404 1250 285524154 285524159
    0x711011109040c11010f230606030c0906120f061011030306060702130915050c032509050307090c080906040f060203040606172803080f090f06070f0f09 67
    0x69000c125524060162408101c0603a005415154004000d880300b00139803a00d0a0003880603525845580c7c3c00c814032507000c8854031800416641c00c1000e0318a540d112004002060000c039440c401020072100103400c15003041c6c030400d01c0c90b000003c2101c0700b03008602140b08011031864802008184034406040c8070355420a8040000c1d920b02004140d2800f46030f00151100030755485201c158040c4c1c1003c40284040341040c036201003405110071000c0105800e10340800c91381c2d101c00c01503901c41c0c00001c2480c03c18100b0301c0e4000500c0407440c03507240148100000d01040588090207502c01920411342c01192426404500030648a00204030140c26084503051000080c890200c40c0c00841e007001c0050b0300c1c2e450703074184980101021380c440703980400d0700206101c0b0fa520119038504103c8901c0400c058203c1d070350180600c001c01411006001561101c0010300d000604035030150010755210440d0100c2c10780c48955440d116058a144c00480c44005c1001081c540c01512401c4121b81840e105580f00e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 285526654 1250 285525404 285525431
    0x909020d351e0304060e100209041505030d08101703070b060102070501320a031a061c1802040c091502030f04090b0d05010f020711040203040519050a0218071101 71
    0x1d090040c0d01c000b42c00000040340501880d500660405024902900c140c2407104d2a000001e5105c820700354003442c209041242c80c6804481c404003154006401b8040450000d101110005001081001003a4940c8030124602e056081d0001075070242100841c0d0b5041c050525411607030000f8100d904541c040310341407107a81d9101e85d28050f542c0c1a80b1b0b8010107911408840e281c04101000d1a00109802081640325650306401102d07050751000c080158090840080c840241304024038418000590141c0c030702c1044459000d44500000d450f0158401c103c640d00007001e0b81e01e41d914141c001400508140800c40e0207400c0145003004600086103445250b21181c0c01c603001e9803184024850741d540c08212661074070f502061225912000822110b4a030200540082d00400029240c1d074022841924060400f8822a409160008010708503480b8841072000c00d05090075040310350703000340030031080140c0f12800411800d01882c40113910354907103030000a09034151903119183d242e04100801c1c0c8401c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 285527904 1250 285526654 285526687
    0x190f0506060a140705010516110106060242060a060e01020c12340816210602130501030b0f0d11010212030108010e06090d02070909020d35 61
    0xb0500ca092150304041a410154818010840060f00a508040801080c00c19181c3c0c03014030a030150302d94415031800e40807000c3c204d800138001c01000d81e00000c03a140302d4600442103801030800301c664044620300c0c0b0320180180b40c0207422a000a182042d418041e80d4034111242402804a0b0700d07041d008402e503100000c0d0340b99000241c250240110240c1025080030910800c540a04502001c2c582c0e48a007400f0503040000041102452030046080411149000701d03c41c1c80188912004078482c07030030810201c03403403000c5601d40d9030b0241000000c84001100e0b40050020b14280309150b468044c0340a0000d07085d544e118002c1031140141110003111a03940c5170206254540156450b09000300500040c1d24102a9901e01502c06030044000a90610150041c00310b404070b036401c1c0c4015480c1c69620b02da64000c44d0320042c0150308200350030f0104100a501c12098075000070201041007100e81c131503000c880420012041400340c400340030100000d00020310252000b41303103009892b26503089002000c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 285529154 1250 285527904 285527917
    0x1e15061e070201171e0c0d020a11010501061803021003060f0303090509130812060604050d150b0d0b0412020102040b1908011403070b030402030a08040608040510050f0c091503190f050606 82
    0x12005c04030b00d5005407441566890f21180400f199a040ca054002d4920000010740d1021507090000124085208400269404c83c1000745d9001550030341d403c0180300451401c2d1201095610203000440d8801c410f481d600860181d124001d00300e0501d070501807180340c0200150701c039142c008187c000180609080300c0e400400984282001e0b1034200010799944550703480706600808071440101880070f219500c20315141d000b903040100000e214180f01540c02030103000362001410b072000801145602c00c009203184d140e440010714160700c440707003d0b0b007603046201c440110040d2820794030601c42d04000380e00e015001c52006028003281d10340000c0e56807625401110510040840800c04540741040310f4811b107680591810340f500d80300c9400411070801243c060b90070f0720075034802081d404581e10641d8010000310700e80382140c4e5582c0040e104150301c90325a642d041800540d000d10105000005103004165820050126029411b18202900d290f07921003400c640c03a03c0d0601040b13a40c0c800031180e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 285530404 1250 285529154 285529201
    0x30906020102120c09010e033a0507120e0a06080f18070611010209040f14010e040308010302010c020f030d020c0109050604050d021011030f040e1e15061e07020117 72
    0x2510345e14100100c03107100d2040300c5d0319014800c440c289001c440d80c1c0c08400c00008204130311120341400b480c01c0142181407070183d000102d582002401e01041d643c4221045401250604141c3d1203800d1002c070350644401d604c98000102d0040134004602036036409560000e00541031914034052139184540c42d825144622010700c034410743c0c0510605029015645240d400074410000d0365803e20b4080060819601c001c8840320210002284450641c08000e0103280c00d50340c1c411107a825a401503504038098501644e114a00c0000c5003140e035010400c159000d07085e60301400e92031041a0001d001a101c64015521600045c0010702181d2100c000340c011381303901151030064210602030251070254040c10344c900d02e03010010b5440928490000140119200b112164a072551000d0058030100d10a4908010f5089004081059155081056a601c041c01040c051400402c4c0300c103030001c0a01307000018020140410880159a007240d0043c0707003e00034003200d80f60303881d0080020340440c6103910340c2203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 285531654 1250 285530404 285530407
    0xc030f07020d3006080115051e0402070f020409030e210a080306010e1305040b0109020304020607030c030509061b060105100f2a0302150109060b040501211107030906020102120c 78
    0x10740158406000e8281c154800008005403912038910390b0107840d80130200c03107000c0402c5400141508220391310400d50b0340c141350b1004275004484100700180d409113009a0301e02590010140240e0784034410f41f51054400d4546c100303011040c80030301c044220070351600011240000c80c0640b03600740100c0c00d00c040e540d003d04129035a540345001600c08909483d652500108130885030500f006880d84801c0c0124000d032000d56040c0e03a151981c606034030007100c009401220900071503001034011440c11180038423070b061050a10009a010a120f90050000300c010342c084a031280c041c2c240d090000d64007500040d2802c16201581010140c031090320f0004540422000c644c50703101c020420903881d00110030001d00c01c00396107030a08000b9554480034003060340c0c401030b0a0000400c0415031041034101c0700726110003818580b07014019100141c900e00d11440301445403003071002404580c89540c03807116080c40141d072104060b04000300350281c035420440035a8070412240c4090141041010350244110301b400b03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 285532904 1250 285531654 285531707
    0xc15090f0609030726090103020c0705060c0c010305090a0b072703200d0213021b0a05070815091507020109061b021216020909150c030f07020d 63
    0x600d0300d5404200e090881c090078040c00140c1101000404140740184000c074016411402d8000e00040143c6105180510070000d0301400c2d4000e0300a0444100558140e07003880799a0400b080203a030120042e0800c40d08a03212484071580c140c401d241e0004880383c01401c02100301d0341c40c1c608000003d04400c007801020041c030700c110540251502c007a1894003035810384882c0d0702d2405108010b004c003c040d11501d0440c8800116040030702100c0301084c6c0040a0350f2561603c0b1a0b160029440f800d03a484d5007000045005802c18000c1180a141e075104100a0109078903085019080c032042404a02201044100b4080420720014804403400c0780c82001086544031000103a0045c40c0c0304000420160910000d460300c8595200400345010907038003941d480045401e200000d83c416125130040d01c1c0d0040f4010f00141c14039549281d80a040042200d9003614680c03011409150201c44e604030300d20002080046081d40004010781080d582d00081400684030f0310301038200800b00c5108116400c403011503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 285534154 1250 285532904 285532921
    0x4080c2a040519180309060810060e0409050715141206040c11060727030302071701060806162d0305070201020d06080303041a010b07030c05070902040e1b0c15 70
    0x495007030b0031400710b00b04803c00301302c0e02200811100c42010b901180c0030b00c41c0028001d020390b02c6c443c42281c01d1a501d10200c0d08100d41601ea03802146082c5421039903030103900000680070010310b0090704108201000c0d510f000300e03005141812801c10045850000d0140c4006481014165604040c0448010a0100e081ca81c00c4400c4000901300280600c91a820300c01a982c1228088100c1105800a54448642d0003403040300ca82261100500503441482c04100300d8074903941e207c00300f80f0100300200c1c005568006d51850a8001c0e524514842d144400c0180301c580c008850750162100c0008501e1041146514032069034400101c050905031604d0006035154801e604035595010b0240f810054641c07038003003d507a00d4000b06c0c2c2c11214481d810303010000410b1504a5503048803c8054020701e0405030b542d04485055104804035407504ca0000c0105094010b030016001400801012040c90b1600c4103140d16604a04407610030017080410000251280200380b4000160f80240c608825445407183c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 285535404 1250 285534154 285534181
    0x203120a020c0901090e060901020c03160212030403030f0201060519060c320c040e0c06070c0e0c03061306150e19240908030a03050c090904080c2a0405 67
    0x2c0b02c80d4020000c90011510b0192a401104106106001c40d1056603030002558202d114088020300554020301010400c0c2d91048680c50a1b0792018000720021500e4a80052641e00550401c0b00806d19000810510755424820301004100071603910714001d00740c0441c105150114000c00d000c02941155110a0103080e40c0d2000007501d00307194400803030301321005100c5002001e10b1401e10a008040c07840c14986494014503c40701500e10140104403880300030047c2c103900562045506040c454000a40c038960324504034840c071542505290340785000005c008600361513005481241381b03400c00c18881c10040500e0108440f2042c180481141442c0703000441c2280740102c2440c1ca00a90b00c7c0c0411091004030500d22040d407066091604001300794030646407005540155a0076a009002e050041442600400d800000d004031449c9400701c00c2c004036085000c00c40f410340e4034003000203101c005064200006010001e4a80701e048190b1031800041d25584003040d45640b0071615100440c1c18085444c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 285536654 1250 285535404 285535423
    0x40308030703021b100b090c0316021606080115020307051b0406030615050a0f0b0d0f09061a0a15080103060f02040b0417101e051b040605030a060b070203120a02 71
    0x2400d888004a02613030785a524030a030380300900100d0400559600301d042aa522a0080451085045c11503480399600c103880018003880b6004c5100b02078460001c0d0a111014001a240e203685401c169810480d103681e9501030625602c1c2103606c20402c4001198001c00c100146a00030078800ea01e03019004005006001079030809054a85011207144e5000e00c0381c90b001d002c0f140151030242e082a980d0342c807000b17000054481c8102c8113408010540201856500a0021040e06400002d9205860b151201243c1c081c00600c00200301070000c20070b661406042e54070007000340c4c02c580520028118401030030500f043c4001000c0035121010210b8250300b54041e0b5020707020740c481c0591650ba07254080401010903c44070b451034000c03400100104c2030b0710300031840c090f980209180000228502420000c010041c0880c449140401c0005403200304900100010070143d60782170340781d0500c00e1503001112010b501a00305104100500c200585000c900102e01c00b0394088156103440f01ca9005034184500754 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 285537904 1250 285536654 285536677
    0x1515201011090a06020a08030a050a150603020d14060a030b04170a0f090b09060f03150a14131802060307170103140f06012402030904020f0306030f0601060504030803070302 76
    0x7035024070440d844101a14480108940000c0182d50300c0c02c0c140d0700d03541ea0b0240a0081c4400b000052002604c41d0055034002140050025021030507004602090070340e500308200080d0001100700c904074990245010344110300c4816101800d21800140d000c24051000a0904d86008002010301c415114045a41c1c0d114140e005d5035012041c4000701880003414500001c2040b8000210300402190240c030f920071000790000345040f002000050b941c0c1c000501e135550f030008612000c0350549400c14642c0003801d0b19898151800709030810883e81810811815030070034900152003601d400791210760b0b454150142d0b40d4550b00e46403d0411034651400f40d4903980b00420300310002040000e01074070a0460f06118050f2035422080680e0641c451100303114803008a04070f551344150808100ba8100e0b0302c000c40e40103d91400c48008081000e80e08038440f402c2d11400c0100403c07203981030502c901001c0780f244a01520441d130401c0d03800f0f460303030155002c040d21031131010000400da81e010354116000004179 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 285539154 1250 285537904 285537911
    0xd0506151603020a02061803100203010e0105130f06081609150312110a080403020a080606030d030c02010b1809010b0334081911010203091c03031d0115152010 70
    0x1002c07c00e650040141c0101801f0b44110010740030207030451f02c281ca058602a038034400c2c041e460601000001f000c00d82c842869942c0d00c400c90220080a80315400080440c0009811a500261000a86c1d08410340c000c00115003000084800d007001c5022003c00d40ba44040c2010700c0f00f80b6003600702d82e80d16840300200c043e8410003161800384542c44000c1c000301c9208031841540030342c884c0502c5803601c005484458050380030015003000c25009400200d400221440005001c11000b40010b00140c0204070407001184e41409000700701400b80a281c100c100f040d0b005000c000c070000010315020400d003d030116940a00c00e40b00401c00110a07c20b0028802c03801152040e241403d6a07410246258400300c1d1811601000701c005035002005940306c00500400c0e4142d070362204000b0702406031000c40700b1010150740388007803203c210501009001d40c4688600009600c0c9500d10b42c102200c840da0006021034110004010701c003503000151109460707880ad00002a04010000d0500c1d0840000700344410350304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 285540404 1250 285539154 285539167
    0x403050304030611090f0f0112020409151706040303090f1202010e0c09090a0624150201050709050607020f03071a0a021509070b0f0903030f0d0506151603020a0206 72
    0x1010300207a034010030301080203020b606100940c41c45140c85da95048020204401002e203032800481178400b4043c1000c800d6900c64224082c01c03a07100e50461103000b41c2c1c40b800030411003005c11685000e822075941419480c8000008155100b2004100608040e2224056410440c0c02c4248204640d40904076000c44085160084d001c0c1411500c4a6410300c81c440d0408003502e425400c2030f0040042c1001f4180803407031516031001030b046080d10017004075100034001074200c6034980b002000340444038408104000100000b800c2d22000391040041000790303a01840180d54003000c444503507034116040e00b01c001c01100440d0030302a00b030b40311500b1041c2c101415403500c5005401000084031507400c4d11448007902070518880c0c81d0513181200c1c0d039403000c08140180b034000c000805180030b90800290a0034001d0300000c1c13941e4004803062240342c2001c80d03d400e26403014001c09800c00000c817950181d100d080da00c0c1851900030a41802c0f40e01d215030100078103050003440444045500075050030381d03810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 285541654 1250 285540404 285540413
    0x100e03060a02071e020109061b1b031203020c03040b0a03092f12060408160f230307111e090a050108060115052a03120f090c0d0213020f0403 62
    0x100700c524240d51200b2107080c0400c003207544c00d01480701141d0507110042030301d0811000b21116600042030004401607030701c100002c0340c58880f40241e100c9641144045040c02d40c507120381ca400060508106040c01400072002009020040e201641c10340d0000585418a21b00210007500c0c0031a40030345a0030021166890002061002803002c810206e80c02e0b591605c910181700c02000004c030600400c7d08407002040c005050f00c0c0042000303184026440c6428141621420011051888106c0c0c042a480c40701c448007107004c0c0511610b140c50340c00918280b101d03984440e180740c0340d581691442100003014004404104400c200040c04000d001071000e441c0080940b00240f5003030103410424800c100001480c20754003404e002c0d001c40c07207944540c24074045034402c0044480d11429070b0312a06040054035442c130410400b509041c0140b405013451410070410b845403101003c0c041d501182c010b905c140c811500d0720b2013000c941640c140c44180400c503003118004000d0003608a20062044009400010701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 285542904 1250 285541654 285541657
    0x1f0f05070201031d070f061d09040609120e010306060e010e0111010617011406031612060f09030c0215040b1e091002030301030c050103060e0606070215041d0a021206100e03060a02 79
    0x115684046e4035081c64580000303842103c441c04500c800c03020680380080003801d00b0142203402c03611480020134401d8881d51420805c01010000b040064407282d40c0035050369160091f20001d198904212081440080000307007641c801c01c0c078460500410000e007241451095114000806507200f11f00001030b441d41d6258003030b002811140d01c0241300c0314007040070b5184c0416103013400c0c5c0201c00381111301481c00e02038040c00b2070680c0b000d440e45640c0e0600040102d202c4d00400c20303010311a40d280c0c080d01102d8810064005000c0003844501002031000f440a021502d003250042c5281504100004108954110052040112107608905200c98051141d07400101950699201e80d0002c80410380352401101268581e00c41c000988808602044050410324010010b0b03600203407200a15016000304910340341e1080e80041c1074104420712000161191103521a04000034031801c3d86000b2025801d10081c08019241503c100c00515644041038050000700302040c0c006019074809103001c11303000009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 285544154 1250 285542904 285542909
    0x10c0203070f060504031b080a0f050c060a080f1b0a030902030f1507020717030f03071814030d031b1116030803070806010e090406020310080a0b061f0f05070201031d07 74
    0x140351400d0350405100c00e80c441001c08e407501c80d4001c100f1899543c031103504203680701e4802c1d00d0900030864040100e44400005148600c855200c094090414030708410100000a041402e90341707808400d40340c164024012158003013074a10740402c00500c2800080d09040040303074246110321030072101089000400c084c0510590064095910ba02d40d101e001c014070000e0803d203540d1680007080f0310307504591002c0145800c642c40e4605512002000789100a80041da60020210f02e0400011000149410000c90040808030703d828800c040c085102c454030b8118580000c41400154071000100707103003c000080002c0200703649034a44954a081170030042d072050318404006510000040c0d210b5004004186255801603c1030f0313001d5580d0740f9040000e41014000b03185400d800700780055400c40402c00d00300007a005100810150602c94200310039004202d210042d4821540c03500d191b0180c0000c405900d11250f03040c1309a071403203d40300480050035100c00710340155941c9007040410210005000c8103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 285545404 1250 285544154 285544163
    0xc0c0304090c030b0d0503030a09030509120703050c040903120906110f0408060606040e07082a120f01080d0807031b020f0607021b190f0612050c070809010c0203070f06050403 77
    0x131a0858080c0000380c0030429000d003441e4401c1000c03860f03110b0340c0d5001b581c16a00034980103040c40340174400103d02c442240c1e00b100190740094802d00034032105106241c0481c131308440070030107200741b583e015103400722845106040994400000c3e0030700c80e058100709211060721101076580c0440701c100142c140c100c0d000e0190750b4072508000494a05054007120709072445040d00702410340c1c801104441c94040200328090b080d22000c200d405100070082d001807905001038100ba1a54150250100c440130002c1403a010700c601c1200401070204041100d0500180a2920b440d075a035511030258007801d8604458034a002d90400c0c0d483c58242d005c54503040340499035083d82c403103132a2500708030794594080521079000c0e06c02a120310100d140a80031110103821881d03807584690743d1440d11121000c0250b21410105a40c11b48400a5045510941e980301c91031241c514105000354031005154015122401c0c1800f25085800c000c1d036800304100b01c020044800ca01d40b0b002d468003001041500113100445 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 285546654 1250 285545404 285545411
    0xd1e0f0b010f0e010e060603090708100905010b0d121206030f080306102d0c02060309030306090903130902070f06050108032205300f0d0f1b0b0c0c0304090c03 70
    0xa107018011400d6130481c0d8440e9000304a94984104009242c0c0c40034220315064031070804001205a81402007580303003a90104009091801400d0260039185105007061040c0c04400d01040001d100420341001c115203880c08040c0f00c03020b2403860004002c035403c0a0b022100d09001c00701040000300040d8411030095900360300000420703100362500b94019810008850a100c00f007940c0c2d80c0c00400c0d00840091a1402e500c4601181d000305450303a0091300e100c80300781c0001042120360306211500d01d801681c2030008505d0002c2d001c007401281480c500410240580007e1118140000d036040340f815180c0000c0304000950b9114880e030742d00e9020141c205200c908483c0041108070800c0302a5044410207016031008450f05100c0c0a1394484040b15040001c82c0390f040c1000400c010401100300546200041941200c040c0b005440300388050f4100c01001840e4030703e40300030010407888019503640002d820301541c441c0070b05030b415405803510781044c0b4400030900058000c55504000f441018545082 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 285547904 1250 285546654 285546659
    0x100c14190e060a0903080309010216050a110102060403120b060c011a0f0a0e0105040903140406080411060415030c110d091403030301081b040212090a051b0d1e0f0b010f 74
    0x1646000790080c0901044c0c01c0b00c000c0012459480040d41d00080d4507000600c1c249032500c1140b8014130034801a1055405061800100720032900202400ca90074002803010380f4055130010320006041241410381d54540341a0099610b0740400d0f83c002c080d42d0002031050884452262000107821031000d4481c03c1580c0200080d820310002d501c043c1c2d9140200f000c0a40c0c02d103000c0c8805405024001c9041121900003c4039241e8907074007600c0a024155681c5445d800c243c00c1901c16466542050341c81290104010054852151000070301c0707201e030317003000301b0130711040b0600f592428500c1c9200c070300c213004041120485550004e402e006681c3d07180580000303900400181a80c90009008a18055100b416402034056034a40a500c036260001c1025107042d0030100d9400407524240d50034047c560100100804200c02404040e400366030b10122200f8009d2103000180c80c034294088050050070140004100c07003110b01d81c000c3c1c109034002c400c0655980641c6001c14200a0074411054a2000d80703401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 285549154 1250 285547904 285547909
    0xc01050105040506130e03040b07050d080c03070806121507020f0708031306081003050a1202010c03150b090102011d0f07060509030d1103090a060f0e030609100c14190e 74
    0x83c00c1c0a1034029260008003040104900010a40346001d204144403d2000040514010000380794161062001d04000c501c03c2e2406461244094280c000302d200c00e000708040c50b40d1217506135038401400c0710b4403030f10014106985420034000d1400b68041620389010070003d140c00045407407219010104840a00d547c1d40e80d55038a90141c40c4200c00064003140007001502d20a800704c40c6c0000b014242d420065640c1c0ea54070b80707009646101201c0c03c030700715a00d403000c0076020311400c0381d040980d09080c03000320075041000d8001d5a150181680e559000300304242564402d502114404800789003003407100040140c01d640d02c0720580c460010303e10690a0114501e032052081d01c900c454080c0081c07540e035400040503500c0c0320004080f080343d071000b4460303208295100a01c007002054551100040400d00356002016074010705402d900031f0b40f165040c04a01c00b40000c014090850140001808011040c41202d0303406980c0e01c00950585c0110300741e10800c4080644080803a0142c6032403c001c0b102c1020b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 285550404 1250 285549154 285549161
    0x110d060507020c06120705281d0d020a030b13020d0f050c10020613020607080d0c09350114090c01090f08190303180b0405070b120703020a030902090c0c0105010504 72
    0x41e241240510240480c100340e001d45c014240d040c0104019035500301023855a0080e81f20301415103800589607210100441e5148000c0004044055502e5a000907454000c6070f0928600d02c00288002d16110001d00030204030401080c4480d8000c0c10b181c0c4404441c1480b06180e00c40d80410342d01070294443d0a1807034904190980444070080c4c001e000e032565000e100c5441505000c0c000e0360016070030007603075000585640080917401c40b85040040d08050000006040000641100c05040b200030400c40e0044e080400b9001c0220f601e2494060113090818401d01500d0481c5442c411072940000b40f19820b1070200b01d040089000303a07540040c09540f00b65003d0030120f20700c110340c030503080780e440c100502c08400402e10807a030190a000c641032201089103d8a114141300540d00018a4402d1108001c0203000c4500180300f0307c1c91040c100100b1180102c440040588114241940003e0b0700100354005e41052040316002081c0001e14039111203000903d0744104c008c0c1c00c0c1c5510302000800c80745028031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 285551654 1250 285550404 285550417
    0x60906032e06170601050102010209150310050411120f060d0b07021510030c050405010b030105060c0f0106151b03050301050613080f0f0613170304110d060507020c06 73
    0x100100408014102421680d080302040403281c01d010200d420866601c500940b80105074015030aa10400084082d901389501030b008036045900402c00300c01c269407140960008280d080000d641c2c0c988643c903000d888001c803940002e42043c20110400881d00a610140c404c54960890000a0380d842169132a4400011200c16038011609107518000c1280383c0036041d84211680101c808290010000106a030700071145e86850030060032003401006807129090000300710540b000c1c8407550410526030520b00050082c9030042e0780115a1060180341045510085c403200c0008000d6aa15803c054160408410f0020082481e400180864100c1044400d0103280c041c1d84003400e6900f04800c00601d075003e1a454007e1004009011036a030b6014400c100100d40824020042a0f10303199403181061001040910500b01c102d142d200404c0600c02c040032541443e01f880b03581c960729440c04c807007483c0c1c0c51000d150b04882445400410040190300c1507002e24090f8086480442060003003000911844 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 285552904 1250 285551654 285551659
    0xf0905010f1e06050703020a02191503050903090402210a0b09090303040c09020a0221071a09030403030e010c050307140f01060812030a090b07020a0c0f0605070f1b0f0e060906 77
    0x1107000c2010030304c1034005d4403240d4420b1050b218241c045400250202d48d401840d01c195513144007040100c0810241d2031030274600c05050600880ca4000d0710315459001e025a150300994001800c00a00e014800020440d490f600c0c42440c0c1034101010074400074200c2e401c1e00340c044e8045034080b814840e8000140c0c0c2c441c03070b03001141e0303544541001c00d91400b0350007040c0c58005510410700340d42c1e041000c092041c1d00042440341b0058031800e80342080003030044041c0d680d4141c07046400a1050011000c01200c042d66014184000d4501004004807824080c41e0700c0644030b4000403a484c800c000d00c0014a5030032100d05422078500c032500c0c960103070032201c0d02e100c0e20045900044003000081c80c072101031588442501c0001558145a03107580094140442c0c0310743c01038004240b140c040150a800f1100500082501901068209080075040b4070035480c001e4488500d4001c0c04040080d903400c0400e8119058405100d030b81d03950195218259803a01921411221a2000850328146003006c648a050b00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 285554154 1250 285552904 285552959
    0x8210a05060a0e07031e11070516080a030e06070c060e100207050607030806120106120605070309080904150f0b0c01060b0922111206041b02250f0905010f 68
    0x103260085e002031160080710004840744d410f1041d0301070b0a030b00c1808186e404000840b41c1c0c0d8051864501d04080200034030040c280303425201401642000145240300c0d0354503080034036500491400113000e5000d00c45000301031a000200114500303600c007607550612002520743e8011006500400e81e1191040d0050a420a00070f02c83d0701b001c00d124421540d0412000303440c1c1d04e080c803c5a80000c3c01d49606410504200c034002c588441040200e10a07203900c0600c529081083c1005591624854031030040031900c2507846622034160003110403041e800410002c0c4042d05180d45d241d00326506904080b40c80312095280038000103101c0c0382c0c642101d150078401040d10124501d55540b4124125414440001c902e640d005404014418500281940d854850300320905140030010402540c46140d034088004041c583740030522500090840300c083e007024440c01c4003515081440c00305001c07a134804441e080d640c20000070f400c4040e90045040e2001c1804140c00c0c1d40e1a50460040110103c80080d2001351 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 285555404 1250 285554154 285554161
    0x16050111010c1209020105160615080d090303030b12062805150d03020f0102030a0506040b061c0c0c02061308010e1204050f01090506070b06010306090e150408210a05060a0e 76
    0x300d0b07130048a1103841418500d0602014102c0400c45100000080301d140740c1d28130030100a80c1d02c05400000914005005190020044200034800d1015110050a2588880e82a1810f0b0b5411031a80701c2540c40804030784051078840d1004507502d00110700d1405c41c1000e41d109100c84080c40c051b09108082c1424042c0c0c000780e42e4010f001521300300701401e50450103200422101420280000c40c0544e09540b80031601d41082802c003c11601d40c0b02415210310002c101003290b940c41265123603004055000001050070041e00e065509040f4064025809200000d01f040a52480072002041d0760f44103008000c403c02d5919003607030701d2600310100d590b84c202c1070104100302e20f81044a00c1c20a0300603d8940700f050745d04c1000c94515004000121a10080c480070400d5550f0300d441543d0082003001c5042c0803648042c1d11f01d90300c4800c844102104c0c000000c00007001e00c0301c06012a2200c140006403401c000c02c080712401c5c0d000304241c806595450910020032840d00d0012030f0b01d01038800407490508280c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 285556654 1250 285555404 285555437
    0x120b150f010c1b0b0c07090c0903020f040e070503070e15012f100204092412020f0406030218090c0901030b07030b01020f0313180203040b060d0602090316050111010c 73
    0x100040003080340d0541e22400b24072111350700b001c1d059042130400180b0070300d800c000104054405091024080001c0007201708056520700720306005402003a2400581d001e0f00b111110300303198050b00704c81d42500c58400700049001103444094030a0302c40c15204130300410100011184814501e00090f02c1d002c8507400b52500066841c0603080c1a55884d0468482d11007044a800c244e80080e03010050481e9903144500442d00d20456249507480d884103000643d41c04c01004403408920342d140603004041f648580b458a440d1a031020004c2c580003001501c10010041244040b41011150f0a440e40203046000310103052200c1079070b043c0c980c014641811a40c481780110006c0a080c0f50300c0e811440342110301d210400d400c2c001442c480403c2d004240c207a0b1304258401c110311440c80029002d4900c1001004082160a0303541504200700721070b00146041c2a05208001c0d0040412850385401150300c00b0321552080b00784503044403002c1c0c880355884045031885500b21240112003c000c02d140540c0c007954007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 285557904 1250 285556654 285556673
    0x70b010e10050904030c063b0a17031902070f06051e0a020a091403031b1f02030105090f06011709120309030405012307030c020a120b150f010c 63
    0x854030000000640c0c1d0b11000503103950029074065011668086d0307004140b04450240f040303825544840c9086800c0220500100d41c09101d10121101103001c40041c45643c00388010340d02d064009030050080b040c4103000d0880c1d54001d407035081e604c00c40c65a508441801c2402520502c6802c0042c031808200c440e00c6000146c040140906a103500c9009003103103007000d240d009406000c89120050300c6195110020b043c11290345c22903201249000d059180310741d030010481e40c03038600e080000d074049030480c0c4890707140809040300c00a40d074488012441c5441100c1c1e02035812504102c50018285d100c0d400440b4103907506480450004200c0e4600e21540c0c82c00400081d04890404201c90340307001c0080b80b4542c150000c0c4d17103408444c0c0000504000310360303002c0c03031015281600a116400301010503407641c0461050ba20001e0038801c04401d0b0300150350700d0018010060000010f0561010840d2812022000b4211881b400c00f2006034064905400c2103910303409403c806071a032040c032507250349490444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 285559154 1250 285557904 285557911
    0x20a0c06210903030b0102060105120a060f06050303070f0308010911090f0f03030a0c06050c040501021b060f04080109020108180706050904020d0606022103040c05040b010e0a060906090902070b010e 87
    0x58001884020340c4608544542d10866000b035800050840f003401c00241003a00680c4814820002040202c4101c0300119400320140d912640000d074021a0f11001d0b4081d0105078055581800301160302024070000e14024007203680f00c4e0342c5900507a0388030032000040790058192404005414490300040d0f0528007a0035001000040c0580d000301c1400000a1031584013049160004100c0d8486c43c04001361801996040311032050203e0505040c140003e640e001d5170300c07800b04070311040c07800e480003504d400d4119040300080b1030340f0b1541d558035110010301030112450100c1c001030b40c04000940d012a44100c1013408148038000d0024a860300b841104c082d01300481c50740d4040e130308000c0d4001d07100c1c0c180f00c2c0c54001c00c0300c0d401508200b402a00c0c40082510220b00d80105034204208010014403031001a07411740b242140c000410607401c20040b02c0c50f031350314007082d5005990940e01117174954204500c0002c5510700e94481d001103889507600e200764091008004d201c40394400c0103002da43c0d06807480550 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 285560404 1250 285559154 285559187
    0xb070f02120712030e01060603020705010b0303040501020a02060a0e031002190914040e010609090f260904050c070512130603090b0408070f06060f060806060c070e060a031b0510020a0c06 82
    0x3611407250017050308452081d801000429270001e406001c121080c06208072440c4102d02450919141c40c002030341300c60300342d180248207190019415428038041d07a0400c0d202d65003c1c0c11580d1483d40050f5800095101038141d0351810401ca444044262107400c01c4801d480d90003000c8541c001c100001d0201a20310345a1140c2d542d500e500001c00e00170050710034003280134042c6c2509104100d070303270801d000900303140e10800c2d1480107000d1154121079086c4c0116460303018241d80c0000e2666405c00f903030407980640c00000300b4034091400102178072400000582581410014121800741d44d03040e09604a40034180000c102810000008000c10b0b1000041e014a034007682c950780ca0f025040ea14082164000d800100007105140d20500809501c0b060850384000c0c282c50301850500b1105445036510428452501a90b0600c0700240c0251501d8620000540d0700540d040b5800c0c040d0b0906400c1e503107881c000d0500404050807014007580c40040d23030104043d00301880f424002c1c00d000c0100d8030312300c88041e00030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 285561654 1250 285560404 285560411
    0x51605032d100f02090109050901060e1c1a0405010b030c150306031606110c012622030206010302030d0201090b13030203040e0901050f0609010515090a0306090b070f0212071203 78
    0x2c8070141607019090b11845090030040e030318105600017402c4040580c102c40c0c0102c401e0f000610000d6004040d14000716001c44400c410b10b030440e0b00c4c1920002c0c03220b1004003240f002c407a0ba80300307140c0d40301190f1340914030990003401803001e1941495036a10241e0310a90b402403403075214108004400004682015020701603404104456294802040141d4807500004901c4512110641c0042c08049100c2c030092030300b142031681401c0320104501c180801c00c0703142260000032545820301e0b400c0381c030081202512055180c10680c00d011351100e4092000781d0107401400418050140b0600c60900419030004c189001600c5034019486280ea0341403007241540710400c00400e00300394551080384a00c428200100d480d103081442c00040d000042d141d039004020700401031100d0b94844a5240300004043d55461310703002c400002a8100d0000ea1000e44000d1074488000103100b0140b08480c800e00e0541c80d010100c2c1c43c222812170791264103104907140c045044c890a40010350b60080c0d140c1c030012030716010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 285562904 1250 285561654 285561673
    0x20a08030f030403020601080c0f130f0f0f050f1e090c1905030c010c030206060f010c020901122a05010e03010e06090f0c0a03050c09190207051605032d 67
    0x949994009440e0600c07120010041104040d8104803042c0904120000307072040c601190f0214003000000441a8804d009545580d49010510782c0301080415007508140300c4040d40d001c030760008181c4c0c103095001060414000076290302c1040c6100d805641003185003001658840c903a5200407030081c207402c080c0e020f51500c07200540ea81034840010280e8840071001010315020801d4501400da1044a05100c01c806041c00031940200e40e4a502c45003e135011650541400012944079058840c000c0d444030100001081440d1112000e8860a2184003401800600d02c5400c05071481d01c0707081904800c2c0100ea080c0080e510440c9050044000030300085517940e404240316040c080c007100c40807116440b601082d00c09040401290300b00040aa40756100319046481e440e480b6a46050403030302480050020070141c1802c074a400d50300119011003152251407620b403050f103c030081c2076031401e1034071110004200c52401142c00c6031200c203450358524030410400306803100308800011405a5024a0520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 285564154 1250 285562904 285562919
    0x150d0507080a05060601091d010e070306172103040503040b0901051b0f1608030318030405100f03140112200415030c0915060509151c11030c16020a 65
    0x861200303110350040c0c0b413286040c00c00103000018590003404a642c420320710340040044000640d042d140c0c541c03002c014a82d0307230460590141c105a4400c4884000c00081d8450305000400d415041049805136842585c290b03c4900781e07140000d0701c3c050800d0700b04210400a6607246401000101c6040c14554104060444e0407000c02c80315290a04c002d40052039074102070041032142c5042079880410700c100b03a40c10406400da0301c0c00b00611150343d00d4503102c020003c406007007041d1001098000d00800504420800c0148540f11200700790022038141815542601d450920791810707141d600d4030b210021005a21002c1e81d6003807240b03014206104035404103480d92076a003e00103071000c2e99003800301c1c42032841c60022000c3d019903021740860340c07900800528128403500f07042c04030340044c90029220800d817800116910000c041d959102c07000012511810b034000c110703295400c10260070400000031400311412461104607021000e0745410421510325010524044900724005004111104c0e12040c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 285565404 1250 285564154 285564163
    0x9091d12031b0c030a032703030504020307081f0501150c080901090e011d06030f060103030c0624140f060a05160c0905180a020306070f05090a090e0d08150d050708 72
    0xc859070f1580000a4120740a41c2500400680c84000562068030304100b4500f150f05040f000001000c154507100890b066640800c03c02018080300b10684032075503421400e04a011007001c4c501194a0b0030100000703620004071001e17921540d2181c031002c0040c0380a0f91403040303940c00401c880741800125000072a205002c206000e01825081c00d0111404080c41c15486070040c0c002c041622070351203404981010304011901904407a4141400611001e05140c50009418265094904044010b00d0a8189020410000e08441d41c1010030100c101030002800320030047c440c901900074204118001b1200d10034002003456000c50102003400040e5030b0354881905001c2d500c054002c0342c44909100014040f12000140c140080000303000007800759002c00c0c6c071000b00902d29001d202141c0c002d401c425005a040310103150004008142c07094854003444014855008510110710844440b002280d004080d06405015180d820b00781881020082101c42c03d100007045855000300400041d0f41d01c1d0800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 285566654 1250 285565404 285565417
    0xe010212090c2815200303010602010f020301120212030d05041b060c0b01170c030a050a030e18070e1f090620030304060b0f100306030506060105040b0702130e030a09091d12031b 78
    0x10082d55495161800003825334520801c1d1501c01c51040004029044081c9480c1d1180d0741c0c1924040d0348001c04070300690940c01103181140c612030401081004001d00c50343c1c2e13060b0300380e030080200441035200d1004840240f042140200400c607001c0045c00000e13aa4000304244a61980440d04203011700c90101e070816003012000c0351142d205147c00000c242d001070140901010941d0482420140c040c101420101c018089505011b44140c2820294035004c14040d22101640701c1e0542170024610002d090403842c1c03198500058562841c40d5016800200207120101010029402d648545c5c9604008213200d040b540e600c5100440151880c0e1112100121010704c03944000403140d01d542881810424001c011904100781040103103c10340c2014180e5070080c0d015500c1400c1560075680309001041849000711480c0f002244041e1944d0741320784514245c400e10101884060869040034880713080081000310365400845207040318032580c801550303002c0908030031070016884a0991381079a0b070006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 285567904 1250 285566654 285566717
    0x8180a030908010516020d03020904180305090102060702010203060a030b10091d070504021318061a09120706080c0a090909030c050f0607120e010212090c2815 70
    0x80300030004242d080c81101e501000061601e4015220150025100e40742c031494001495030201d400c40c07242e2511780c80b4603800400c441900741141e41904000d0310030740100c1c114900511518001980751413040c0252801410003814001406003541c0c2c900740705500040c403034a0040c112400015071007005000741490038811444640481e50880c403907a08020305a041107004600400c4584103028545e0005c104a51000c0c88101d40d00385e041440310040c1c02c003030b03000c545c0e8010705070300c0000d25001c0c0c40010a40300c0011542c04504c5000c80f100541c5913902d41c8900c03004101c400c00002c028082c400c008103e2a052403a007070304d03503548800c1e80400701e504140c000e90028041010b820b0401c11704110024180d006500103140d285481c4200414010b100000321002c29202e00c03180001e18401d4060f180c400310521080100c074504a1a100c4d03940c1d0403d21014841d41c1c00c80c0e1200750150b420208945401c1882449624150820703002d060300c510040c500d0401c02600459254980f04582c0702da1060140d030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 285569154 1250 285567904 285567917
    0x10e0106020f0d120e01021204121b08030705131e030b0c03130618020414041a0103050c041a0d050a05010c090b04181401080109150507080708180a03 66
    0x400d00d00074030701040351088074000d9010b41a800c00064002c41c1c01c0c1900c44c148a8081115000071043c20301a00819034120103007420901031004010352503214042c00b42c0b950b0b03100e12107542c20034014405d1101668020340038842c1003003c42d58a078800c1004203000c00801040d20001c5550706107550300c031310b445c1025010307030000d0400500070040140d107001d401040c502c0b00e05080d410100d0b26840c0e0681040380003015aa0f4901006440300d43c02901041c100f07400400c10010800107440780641420110b9003112405446140700d00075000c03800c6003030b0617070390010000d0142d03622420500c0300510501c41410220078440c1681c4116a6520b0a0a07009900c218040c01c0d020b05c0902c1d19509640e180c24032502071000f41e400034440a0348600680c2d00300c44038001c8641040780302c3c0c450000203150040e600b29820381003130008500700d00e054203c4c070a298420302020301c2d59640303da669001c44409442c0440010780080211743c00a114614241d0000e05034880303500703040d44000642c2c0c0340030890311044021511 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 285570404 1250 285569154 285569159
    0x210506090705090306070f0909060810060509100306090602040e0a021c0b060a031e060609031412030a0b0f1c0303110f03040b0916140f0114092205010e01 68
    0x1003106000e90000d0250074140d090881280000340ca40d440186003504008202e2501c000c194882d102e01001030412050402c99035455003200d9888080d0700c000200410300307001d000607887c18000109849080c0304090301944909503039031040500650102901c6054003800b0105144d203000c5061405004401001070fa04d40b071058092842500030b02c1c620204503c4e11400701307010f072115012141c031003e451a0025824500d40f5810030405075245070070b0000740c5425404640160451200e0003641c0c000c0826422400040149640e1100c04084080c201a42403020030001c00858202a00250700140320700320300002a8042483c8214000002891f1400185ca11050503018801c0703003400000d036a215840d00e8100301100d9011710014000800115103080003d00b40035040c4a0042c81c54107100c03c0c03a61203950303001c4450042250102c040c0c031450543d061022030b98003c2d580008034014445201d41000404400c00c070484050b135462456494070100024000d40540c803c480c064071214115450071350 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 285571654 1250 285570404 285570409
    0xb0a05030f060f1c080d09080913020c0a02060d0b0312040504060f05031207021503010602150105120c220212041103030c03030609180a0506180a0b0412210506 70
    0x200181c00d0b140a460042e40350031683d25000c69251111140400b00103d400081c07030720344807920508078102a038070700c2c0490b580c0c20808414010300b5a180201d034035240340038608216004900c1008680c040aa01000c4000f0050401c04040c00701550080f40c0003a0700b4a617040800e040c030092541303803030186000007801d000e0b61405101d082c010300700c2c4040c00c100b00b504210200fa510344a038484a104240041403c0c01150ba0328686186512100700809480c0d5035900400307580d99500b03c80c201c014003c40c0c00081220b0614074a040c41c041c900d10014898442050700388850f640035540d21a40c45024240d5100715400980028040c0c941c0c40b1020038541e01d458180420710000d0403628502c41d810400140d00302c50030020569802160455040380192102c004400c1401d80070700c04448a8003039000ca400c24004041407642c49201c1441003d55030b42d10450140780c50700a05100249020041e00205010884010100f4981259401c040c0705104d5010341c10005064012580740781c5c81c1e11417080000b03e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 285572904 1250 285571654 285571681
    0x31006120c091a0906040605030402040605090412120e0102072301020304032309120d0e0307060207170c120303070f0306050609010305132108060a030b010509100b0a0503 75
    0x2246404401c1140981142000707014240500c1145240081120702c200c100c103e44048400c030010042c0b246580b0303951590080c0aa0700100c405911551500f480015181020000340c4e11841c0c1c81a81080140c0301da40341038a4410903401c00300d05440c0e07902030041d80300c00e0074402002c000e401405000300c03400c0010b11600d152182d60030500050b90048c014000060b812a4030700601d18141c4207042d0900d040c002c2000101d0040018450340b228000e451840501000300e00101d90313140720703901e4441400c14041030540d83c80d4580300d120b0040c0c2c8000c03010003881181a44c089440c1080c502a1507840340b15400160311a0083c442c0c26545030000130500c113200e900060120040b20050a003404440e20701400202180981c2e008281416215800074220500c1d078441d180407954419950950b1500c1021000c040d000b1500951012825450110715203281c804035803070842e0307482000d19810383c2c00c050a0042d82803000d000e5400c40c8003801310219841300d100018055000b003660340c490322450043c1240241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 285574154 1250 285572904 285572927
    0x605070c05010f020906091507021512060a0506030c070203070f06090f1406040312051209160801090b07030905070f03050d030507110d050a050c15011502150403080a0f02031006 78
    0x207131042002c40e50076102c3c0801d0728410070040311440e20440840000000900c687c1100039408a00c000f150703518210b0804c00741c4800080321002c15030603a5070505100c440e213901c0c02070702d40c040310a20004892800100040c01c02a00c0601036800c207954030004490310229540102000c03580d2507505008249441a40070300501058402400c021280000704034075100700c2c00040c00c90304c422800400701e180240d00300c940036071010980d0005072400795401c1e80c665905c81c0101310742101e540c4000030a10414090700410310b412080c80c030030700d88a040d001d400800302884121800e004940c0001201c40304482440000e41c0a000500782040721044001d0846100804c4e040521074003031081190540c0000c0c0314440300e000340c101a175035808010f03000d840b9401040b040c3c001c01d10030320180045847c5540c990324126404000b00f407003221050340f016602c5680e09400e0000840700500010042445011640d030403071866000080c200458120410907070b07204a82501030380ca240c3c00104009a8860701203647d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 285575404 1250 285574154 285574181
    0xd020901110a150c0306080a120914061603021905060405070f0e070e0a090c0915080903270607050c0306010f0b0f22030b01031b030c0b0310030605070c0501 69
    0xb0048030503540c811a0f0200c0900b201a440e580da410201003d01951040000e4056801254012007840c501107864042e448501800500010310008002c2950b0b4030700c0c001d0304001400d250601c074001605803c0c14050320350981c1148910402d000000900d4480300440d1809a40030b03000500d401d082c22450203080342d110307841c1064084420410b0410148060341c0140c0c1500d0402001c1100c1c3d000541096019040600f01c540b40904510b2481c0e0070104500494904d61800b110b0074890b01015a152309046074400b00c0764104004900da4034000400030303c0c211449807080400381d0a0200803ea080c0c028070781c100c40580c00b18041040c0e07442d042010a0061172a180150049402d06000340d00c1405000c000c041007090204110b05403080d20b0701c9002c40c808030710102d1440e4668905042e0f05c1c8586c00e20003034605140c0b51031403a6403080c4040110f4281e82d0001404060f00f89000c9942d01c00358801025080384050001001c00043c0e07250080900400740d6980e08540061f141c2400d0342142c505007251362 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 285576654 1250 285575404 285575413
    0x506010e130209040e06071d0901031e030521011d0601091a0906070503031009020a08041101030b0d05010e010b0909060601050c0a0606080601091407021509070b0d02090111 76
    0x400980da01d0484582124032054056103503140440824060300500203404402e0144ca0104028150700c8880d52465a0714411083d503c0045502403000d110420b002c094400117654907440e82c001c66869003002000e100386000c5181500150a407100d200c805c42212082c100f8031801088031011008107002e1040d401590003025090100001e01201d1141c8103a1803900400b120450f03049028400365040000060103481d80d03403900c2c1c50866100c0e40304982030400401075880100e610000e41c4260b40c2031307d040303884550f00d0703071182d485200038450030501403070426072660045038543c0c40c0e000052103040e1060f400845c1814540078081d0a59101c03100c0c007802540400108400d514001496542100082c2091a5200364030141d050030301051810252520b030402c2d0000414400c0000c0c018103d8810110420506500c0740c2105c07461a0140c03818401a032240c003260360110800307a0302d5604101950308603141556909420021342e00308080c0440b101750701090704c0d501d40d41c03c0588004000300103000741 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 285577904 1250 285576654 285576677
    0x4030311010c090905090304030b100806090304150e04020702060c07030620040315090b070c0516080d08100513090606210809030307060911011701060230040612050601 74
    0x20320128070b134428200000e4884000c1030b2404030610485002d19041303001e01c0c0403840d1030300540c000c1c08032520550003140706901c00034601d994084241c0d01030340d020b4041d100704402001070440e0101504c850f11980150700b040b600c070050b55074100409555183c040038110319881e41c2008402c481c0b518460b0100405510034401d14802c071481114240e07039104008074100221072004000070200c903040200380c2c0c070101c3c0502642c0c9410599002140b03101d00300315842d1405600c407100b04441c00e48036040b103130785c4142c1114010a00410302d80707030701c903e21000200c0c0701e9a41700009a20000c0c0b84041e40c1180d55a40d1854061050500462000d40000440030380040c0d2404801c0810382d40c56030f0080d01c885004504492580d400b0f0088450050f0416010700c84540541801c444080e19040c40c1804240d001000345000e00c2c04003601030490720160081c1c000311241040c00d400030040340516021000c11000700d81003407070b040b0300a03201070300750359440d100c8400100c10307003c1c00c680002d00207905002200e00807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 285579154 1250 285577904 285577907
    0x603030409090c050406030c03060506030c06032806090b030c0f0307060507030903020402040314010c03051501050a0c0b0a0b0a06020c0f0f0f0a0305030a03060e010e06100909090804030311010c 85
    0x12682220701c60400022800c20504060340c509a0903008184e100d400c00700000203001c502400d244c252070050104004584039801050ba8548030300074a41d0b08000e0510001e0324256032064542400031145200c83c1c6000306140860088800d40d40148541075664031080340c0c1e0f0f050404c803501014000380d0340003070314550b03046c00640e8618452013040108600050b084080521035151400115400350041d074413241c6a1400d60b00902c861070a54840b98a41800601514070174050540282c0711100502e25134424000111000c4d8064440e42060045080000000078800701c11035205448045002034010815420880d1966080c0e02140855000c503201d24984c2e5100e9400c00c116000813a090f4001d0540800800c41d83c1d64a1038803241e20002114001040c400088020020032669580030407600b0745610262007011000e0242070602d030f10890010354a410042003c0e503c11949041511590f50b4076011401a10981d84048628110106040040507048414041904c550030024441450103100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 285580404 1250 285579154 285579157
    0x9150b040e060105040815011d061e040e03130314060c0409050a1b080a0b061606090204091712010e1320030d0306170312040b040c0e040b0a0b0306060303 68
    0xe00e5a5152070900481c000e0383c003c100b102e0050a00b84191800b1600000c1d40b40240c50003441a124031081c0b80340400f000d0012030182c07600c560801007003004615402001c0007160b0810450240e000342ea1096002018003040000d04000032640701400100c2c2d0540c50304c0061022f00004a00e4036504c43e10920405000d01001d59003070b0344520000082c6030b42d6440b070613409450b505000f5a0380035161f000a0109941c484006031091104500a004401d58034003401910700c90881b42d5080d0302204891100001c0081d0801480980001d2003c1028180360711200a107400003010034166880004102d06010103844109004011801e18000c4600c1c00c07410030441d05102c4c00005003040c003c40c2081407980c2c0300412a00c0703900320203403c503100c2800000300540100054040c9030b007045210066203200c120004111452081e022000c1704039521150f6500c81c2d60310015104030f51f00991610045289661503002600c03031400303004081410309041142d441210351512119010f6000f440410082d07840000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 285581654 1250 285580404 285580409
    0x10302030402031902060904052a041d0408040f0e04050624240316030b0a06050901120207022d0414070c0606090e0c0a06020303060f060a050c0a0c09150b04 69
    0x1141d1003855284d440003034028032442806661140c41c0005025000d41c221541c1c10501001c1201140e20002508448031280603a1140013200e201c500154200b10703101e0166241c21605c60740c4c54908281d1100010400045150480e80c000c4e101b03107041009102c01000b140742c000b00f100031080001c039070161001d60040540007046000b0742c41071017413982ea8140200341b83c03040070a14205944901380840000c0c0810750201c1c40c0000a420245c0414462806011540442e0300c1c58850a10b00700c021001901c4010800e9490700b01780742e0a018000240c0c545900c03821112968810301c41000a0501300010a20080e009132405145070007040c502500e600038603640c12560b80c0c201040884010714044015060680000500c07070704001815074258000140c99030410021114000d50540b1141c0c120b035a80808ca0b5501e50024240c0c101c1c40036810300380004d203540d011514100d460100341c0d158240ca4000c1c00642200ea15030805030400c1083d11920920541c602140b5080456a2500284080c02d000e0360 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 285582904 1250 285581654 285581683
    0x301051002101a0123030106031503080703050703090b0c060a0e03070501150503550308041707020d0209072003030f1003081803010f020403050a020f01030203040203 73
    0x3101020318a000304080030200180310803d00c0030030600c1440f02000c0403c1031100707020a003d0719820102d1960100100404844a02d1a5040d40c0c6400d208402420741c00700c800c07507001d10303c45011001c182550b00801c1494047c0d258a5503801e03451400810b281090381c8150178110003446208103010000c03409540103000d044003c1036144940319071905521440e94000d000c1d610f080c0d80c000000d4045074000045560443c280d400c81c4003000440c01c0c4038007141e015605a00c01010482c0c4900f40c503104200031021031548500743c1444141c102c000700118404007900880c0d0180c0c00c0204018a00040e140703500a40200641070003c1c55020800350b20350050002d00c1501c540d0005104248600d203603082250440e200c282113a01a150115140d50041d075140030108030220025040740380320540d28003101c0e80038140d1498492805851349611281240301d0740e0554032100c10fa0800c0c2c9841c0040c201440c0a10090880c502c042e10402011900401029040c50300600401c005079401042d41046801803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 285584154 1250 285582904 285582919
    0x90503060a050c042105010e01061d0406270507060509010c0206030a0e0d080702010c020705012c100215090d09031401020f03070302210115030209030f07080d02060c040308030105 79
    0x3030000600ea039000c1ca03000954600031045c0301c0d01c0c4c0420314200810403c1e0064000704090705400d419603090b110a1300030341c1c12604800104000e402444581507034042d009030f4000581a01c0581007803110a40d445813207030920140105032050000274081d24005041500380780c3d28184401d00040c20040110f440a0310038140030000959001f000d4001f002070400d444252002032050701c0d4080c020030000c1d071340c1c40c00541c6403c440080b26800000c1c0b2000340c0d02e05071154201040c401e0540194030a807200100010f1500101e911201d8894a03410302000304035401400e0b0a507080400c800d205d402c001c00b0b60b0402d81c880c015410105800c031000e1000d50750000c030546a000c0e1444e600c180a881303101e40030040301c0b01c00030400c0440c9501d50301820310200c200d580d07070701c411150130a02c1440c01c10a0045100c07041c60700c9081154507009034001c0001c004090159005c50031440305540c107202030b95020000c0740d00a0340d41d143c0e481e981480010b903c0b010304200d45040c1030071170300c1e20951800140951402540c0c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 285585404 1250 285584154 285584161
    0x3090b070303110c0307140c130b180115111c05070f08040b0301030c050103050f0601050a030e060a1d030304030f030b010e040509011d0102071e02060405120106080c01090503060a05 80
    0x2180c0c1019040c20300840f4a181d40d0854203a2a5559034400303103041e241412450b00c00c00301008089032076034441000078540d4140142d40000a001401c2d41c20b00c0c203038440341090b031141c07031400c001500500078054801d0710070320280c90400140c035008101c0c1d4100603c1d0800408550b40c01001202c001e6176039040c1ca00a07072901c0b00b074900f81e40d8120141c0e5000c0c0c4003000108000500c086040005c5040e02d101c0c1141041d0540c0e22401903084c0c500c01c5d02c08031007046180380020300c0f552094002d400c031148a440e000c10342101032001c09041c40ea0585e4804503282c1c075080f822070980e540f64184601251214000c40c83d51820b0349004250010400120b4101901c4e42e0041007a6845503280908100000703208102504140b00703802d000b803440103510100c030705046c8190f855095040c4240c0d41010341010300407000e12966511865095500c050072640160180004200d40d01e50940184c51000c83d1000001c141d0300f45299107160614131840c581c1007022549050021741c40101e0324a4110141c054049420384 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 285586654 1250 285585404 285585407
    0x5151312020111030c070305010615020318130f051512070b0304051f090b07020c010c0605250503070801081f1a12010b13061d15130b12060403090b0703 67
    0x1215000c10f5080c03101140c20754180c4404500d81c02101e10503402000384032f80e40d90315071010482100c003110141c0c0040c065141004087e220200080e2001003103503800c40c8005d80340f00103c58044800e503035074994610070440440a4450342c043c1f000300469040e00b5908a90300e0381980d503a00f6000d9003d00080210100c0e0412008200641040032001861050200c005001030002e101c1400280c450014540100d407001d80080b4100e0b503130107810b0352204032001d00e549072100500f4001d0f00d00d2400300c0c1d01201c40140c5102902da440d0310325403a582e0701c0c1e940c1d081502005096140607040031080360407520071a040e50900030240c0d8485840b250340411b4a40306140f10903500300341c920000b41c00205508125a58140c1036001e030441c0e0104881000460402c1c130407160454445001f50303982c0740440480e03100b08a0b21090260b034804c5a00c00b0000f004510200403682c0500b41d441d5256201b5221220002180f40c0b0701e001040310401030340144110b103043d0310001c1c05040309114030813038604000b40010038035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 285587904 1250 285586654 285586667
    0xb0904150e0a0807051014011e030602040b0903070b04270e0709050106021e07030215130b0a120b181f0f060e1905040b1315051513120201 61
    0x28425020b44128121504001c095980000b0045982d40035848822001c1c1c040c61040103101e200702c4040401a80c20034003441c5054125036010404284040c40c00000141030340000d201a100100301151075900b0b00c0207061134140d46820010302c3c0c0c070382800305014011301d00e91403043c0c0241d4103c020721140001c01c0040c000f04078580380000c05004985001c540428241c01480c1220201c1d0300321690035801030110298a000307010804002d42202c072042026160000c1e4203420300702040645460050480803480b441b0340c507580040e000a5012030041042c507004040d07001c80031480102031110740e51200000f40c41d00745100040c036170a200d0f031010514111500702c001d000c0460b812405000c264039003000c00506085440b07144005028104c24030054140103614219004410b0381d03040607a8244810040906140034125810102c00c0105001c6550f260064540139154040556132040c240301c20301c01107540c40390344c0c414903050400c82e03e0541a05035500c1e0302121003802044040404c54801213a04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 285589154 1250 285587904 285587921
    0x702060d140f180f0606060d06050904030c020103060b0a0804151d0304080708030705100c0e0402070b090c09130b060f030601030b150a060509040b0d120201060303120b090415 77
    0x70046020008101000807429000e1030f59002807203081251003107869510b00d084131040d03003550490004030380c031820310704050025500d4845000c01d1035a2100082100301500316000e0b800940c084100c0410340d41c0601c03402015207019809207107030140800001c1c01a81005d0001441c4c0c01581c8090342c0e02003055805180c18022014000c035180f603c4143c1a60f81c0d41050140e03072203134011524000762004002045812855001c1d000c1c07d60301c01d030b401c000c000500d0600300000900c650a021066950b40301c1c8002c186142c400da40e120150300b0311420b603600d8201c1b4101c2c42805118070301700b481429407408400a50711036104800c03204654071013001c0380c651421000c000d0740601c145030003c0104080c64080e14890019401d804101015801c01c004148044d81f0480e00424010031603030310181803581022400000281010078100e80c0b076031740d2205881004405030b00503550b52905004241d400181124110314401e01403100c21409400240807801c081c00080c02001002d10881c101303921500006403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 285590404 1250 285589154 285589181
    0x30f02030a20030123060d050c150705010c08010b04150903060e060f1501050901081e070203180301060302031c120e030a08131205030711071e06140702060d 69
    0x211050115504240300e0071039442c6110354200618181d4880003d000040460000900b04c0c10640342e130014000c1c0702c03c0c460010380d160702a2202141084c0c4445c540e03501402004001e00d42c0d03601960621600b103580c401c4c0a10100040b81c0010410b0340da40702d0a450645030380200000d11550000c0065900c4041640b004122900309044001a01004100030380f2800c0780720703c400b689668040310030b0f0700d41c8a4400c001c2d01240c03042c458804e507944100c101503805100c1d006000c034046141c181c1c60f81290307011600c000c01648001080c8034002c103400c0c440c050040080c6d0082c002141141d00082d00c0340a10591404190a00c0301c07140071700c0d446001052211714144808101d142d0b0700c04881c0352039601004050000c114488042250400700d085900c1e240c0380c10062041100b4007486044400342d02c0605620208103540d80d09201e8007a040c8101d03001030116280d4281041e00d25028211410030980c4200280480615034064041004c0c080728117003030781140c0980d9580036100000c0000d00c0c06801d94034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 285591654 1250 285590404 285590423
    0x30e01020c121b0307080304060903050409090b150604030b0c0306011b060e0106050603010518090313060809121c020a091a1305060a09060311300106020c0a030f02030a 74
    0x50905050001400001e0f0040300710b502e5650b00100459481c07150070001003080c80d0801c0040d001c51610760060514a120340307421407030b2a80c0c2e00300303a005481c00781106480000c918000e00a185034808014800b030101560114145403460725841c0403008010846415020000006280c0b07a00c2901c840048001e00e502d414680010741c02e201000344241d0f81030111781e62a000307010401c0d24010042c0e904035400108100503d1080c89102d40250710003400d040904c0c0b00510001703002c00306244481016140320794074100d9a140141ca0070380360038500100d90f105c0e4013040144d144075045052003445a90f1100402503501e2940c814200d07207400040d41b085d40030101e40050206071f40b0810707005200071490050318004440c3c4410810403180300d003403103010100e10240c10030443c1a009030007040000c10700d4074111b404e1500b980344803045480d0922604841025592019807050400c02c682405044184000d014150100002c10b4441d915400082c003803004035280f03002150703402c1196001040e071003000c14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 285592904 1250 285591654 285591673
    0x6050d03020a05060105010801031e1506080102120a09031707110607030c0206150112090204090503030109020403030f02030301060906080a0e0106080714010201050c0a03181709130b090403030e01020c 88
    0x940b50310802804a41500541000140941c4980141c505030380d0000049040d012201594929500b89410b040ba0200d03645c280b0201c1c00495449100010000300e0000f6955155100d16540074080040c1000f4200e8039243c11100802e6002030a510240000000f601c4107881c3d0b1442901d083d04d03c01d051b150a40701d10002c1001c5154141c100d00c1c403000443d001c861641d100c0c40284100c1c0489204000c0c00500d01e5107400310908900d07005a094140041c00004811600b5120b41741141d000740c0042e0511a00054100b003010350028020b4544d5801e88095425541043d000504d08812440ba40381004001d41c08126851020751100c0d4101da51031000704207841c0d54030401381c2c45600b07034450101c3c2a1202c1010146650060240b070748078640c14110f041c44c00e030403a43d017900280a15501c02c42e100c16a05444000205c0700042000c8044030040a1034a0390425410040380680f49100340c0032080c00d020f84404240c80313101b407460700258107050100b800c440c81c40c04030380280210000701c41c586c494503555 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 285594154 1250 285592904 285592907
    0x40b0309151302150910050f0705010f02070203071a03010e0604020c010c0e010f05181e0a03050109021311070f1b1403060702010b062215180906081f06050d03 70
    0x1400c005910a40311541001032070319012070301d40110700e0200d8104504400b06e200c42c52040d40203040348040d8204003420500303039440345401c4840009034101d841303500144400c103500e02041044010064506003c85100d0808404881b500040c45140310108150000c00c039a6611a01500c0031400000e0013000201030310700000305440c0e180c004060102d0100131400708854031800448080c00f85681004451020840a00040100c0150506196585912075200c140d56004000008500500020030a40b00300e004001c05000b04401e0046082c0c9042c0c00d1180c0020b110040c1c0f400c1c117030012039510384620700e4200039100003240e403128900c1ca0726844c40440d050ba2503601d9980c059006408035580c50b690400141d00f01c13200300744180e0b0b10900900c501c035405150b02e11002003041c113205002d407005a50340c1d125441d8085480c461004210b4103000007041a03214407585005003041c000500645261101d41c51b1144452124220614001d988031020780840d50050001842c0c00790a4028801d05801c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 285595404 1250 285594154 285594181
    0x702010204170c040c031b0e0a0503010203190605031c0c0f0b0c1c09050a260409060303020c01021f090807050d020a0302100506060f07060e071e09060308040b030915 73
    0x4407131181c2c3c0f0780400282414401d03c0388a6284440c40f180305580b4200c1003041c0c900140c5a810503501c5100030002180b06e0710b0070b0015500461142c042d0500040c2e1501c0d0302810382e205500038600035402104011121181080040600c0981d803d1640d410700a41c00c218081811101d00039000c030713108100340301d107814000c4010270381800c4400400780003d03086440d1300306913030110001901c02c3c0c2c4860000b41c0862280f081090711410312114100028030160a1080c0b1a0001e51100c20f07c1c41c0da80e0020014103806101c036034801c034803d102070940a102c030a00c0002d10f503084691f41d420030b80d0301c0c4401030030804281d00300d429050308802141e0990440050095446000080c101e00502511040c03003041006400f0305c50040314002c1c040c07401c00041028010054120321001d5800c9912160005240007041c890f00000e000704540c68800340400f00c10806c980c0f50558814080240b4140c403c00110f044003040d50281c1d00b05d558242c0d80e03512011b4840c3d01c1c2020162003803803400c08141c14480c1400e10502d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 285596654 1250 285595404 285595423
    0x9050d021b01110703030305180109030201090b06090f150a090f05250215130b040b07140405060304020d030c1a0618010501120923241e070201020417 66
    0x8100004070044400443e0f010a510005502c668032a9a09000281c0a80c000d1503124040d81103102c80c4031703150b100c410f095540c40d0700160b000d80d544203845420312010044083c3c3c03220065030000c4050801d03496410302480020015503810200e48451070266641580100051649080c1402540d682d484460700400f0191071a001044a20700000c0e51940d00c42d0400d00814480e8010306006054960301c80702e00180103002d08034070400b0040d5000044e4804200d40e000714020b6035002001e141c100004ac105807003407054000d028106000400c403d5959104803035100e54103503403d0b002c0c0c20b620303d4140c03404164400001d0101d424000c010403c441f26100d51842068101c035482c5000d17002a00c1c0c080c0140080c0101c60000d400013283e00d80740100c030b4204060b002c2c070480e000d030180b001451803a0b640320761140612556070824400090036004404040c2100c070400c0904050f90304000904240f007181001c1c200107109603490005600a0003075050b100200803440c400c0400018041d41d00c1d44902208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 285597904 1250 285596654 285596683
    0xc050402181c0203030403080306150d0e1b0f130f140406060506040e010611070807090b0a05040515190915060f17060409050a0602071208011e03110409050d02 70
    0x3842c10268446220034000c5107a070003402951415003541c0300d91500d517000400e5290000004012200000c20420003070003c83d4440d00009400010341100909000d140301038500b100d140c2d02d9040425640d8100765110020089030b0942c00240c1c10714404024041240042690070310300905407000c148213800c801e00c40e92103040c08010142c0c0b24010000300380618080c06841c00c2400c8010701c00c25006d00505071004c5076101c1100c400b203036503550b80740c6004140d800126000d6180c020303547c2c842c01c107c0000d2001d410107c0c3c06100519110f2040c0e0f20540040d1417452044080b84d94100c14070b41c0074030301d02d0090701e40807105100c4009115084080d003040352041600041c101960300205901c83c800800e0310740e5415242c00c0c0c0c01c2c4c940b0310402018000700d0700706498074000c040064001801e1031006001c1a44902441c1c445007400c0f4002600f2071030141c2c800140c840c00d07005080e00c520040002c00c0b050340d074041c2010b544c110840b40420010691544000c0c0305106554004e1066a00010b0f645544c5410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 285599154 1250 285597904 285597919
    0x110102120906091218190807091d0307060903110d05031603050f01030210050408060a06150c05030706020a0e0637140c01021204060c0206070807080a05040c05040218 73
    0x800c0d103020b07503a01c0c10211010013508280300b0a991881960800d0a00b102c004002107070032149200220703140205c540c082491036114140801103030b101c1c0c3c01050107044c410200050340c3c1102c0c2028a44034403500200070446940c0b102c0c20300c01c043c007400d03412000f030510408a4007034083c41200900240d00550b001005494140d2000c52410310a00421307224204e80010b15806901c1c503802d002059680c104000c1c00d0100501c0003080c2c03100100a0641f20300c00c0d02c1400720700140380c94045000e41c0c06a81c0b500c000c200b036441345074020600000465114a0703002500590314451207908461701401c544001c2e612040c0003075580c1084882491a42c15503440c1c02d00c0116200744040301d40c07500691081c4000201c1c44091140784001c101c14042c01d20300d8140303000036251400741c2e61102440102110100d40065840040c032400740e0741005125030066a901304480d542c20726070800b43c07038401d00909224401e81c41d00c0000b000c000150108a0040402910030342d180c0081c4003800d030301a6004214036009240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 285600404 1250 285599154 285599161
    0x1e090607080a1a010807050c0d260c070b0a02160b10050a0501020a0b04171b070911191202030c0904180206070b100503072d05030d030903110102120906 67
    0x80b103100340f292026980d200b000d500d401c158015503000a0003404c00092200a210744031543d201484820703180301d090340c2c85a203148000c24450404507041a80107010420641c00c016940c0d54480803282c0d22900310714058695a982017a55019214411402c0300121000401d401000034481c1424002c04071880500c0d5820303110420302420802e948070300750041e40110b8400000c15444010550001e0040d440e95102c03d0310003044090709e51003c5880b010260410038403441c615014420341c400f8092200f824040d4a0402d201c070541c1c3d025240a030303070305e0442c0d08641121080c00388040100b640c0c428681591a441e0803112090150401110300c1c1c01542485816109101c4448080c40b0443c1d0050501e4280407668032142030031031004140c030001d00c2513003c02241542c0c00304960402855001c0d011101624480c0c0601d20329040403580001d820005202441555000720701e83c880f0880754a0005442143ca040841c1c5004246440740c45a510009035039448023800385019204280501c01c4070500c1c2c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 285601654 1250 285600404 285600421
    0xf15050405030904090206270111030910110c03060109050115050903120702010c08030f01031e030f030e071a070203010c1b030e060c010c02100b10020c091e09060708 73
    0x2482160000c203070307030002c02c240076280c50154060030391180080c4c100c900b0a44e0040c03424500c0c5109204880d034011000c071200c1c620f03680c000c600e040010300c4600510708007104100031030000c050590240d02800080d03080c2040b004010811507003041002030455400756590b001020044c4400e0081080400a811101c11001c1c0107030b040b0303a0b03041000740043c0565a10b03400001d41030741200c6030480c100000c854400010030401c85c040d41c0142c40060540700d5552461607d1300d40404050b1085ea42150080d0300c14000c40e8106041d5041c00085043c080303082001c181403603050050b2a048011181c42244440790035080420280100c03620942c002c000d412141b000c103036194003c18200948061013a1400c0c1e00003841102c11450901000e4041da0402035107141c03080c203640803c444480160700ca00d00d651407105060141c407620005c141c1d10018000d441002c001e4039130a995820600030064000131412090300035902e100000300f291081e40d80750030300e40c0012382c5509056500c8400951804013003000780c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 285602904 1250 285601654 285601661
    0x30b0301060e190204150203090109050d03210b04020708120c040b030408071104020f070501060f420807020709021903050402040f0e010603030210050912180303070f15 74
    0x1104440c8203407065075903d0154012407035000d0303e9540200d409220000d021100c0403c4c0005000e074640107141c81d0460751000421031812584600d01c0b511003801104042a0026007081e07a0501e4000c0541036611001c5046c0098040c22490f10340203880000d100782071000b41c00184c6640c0d04407203034407255621f030311400902c14042c3d405003c062104c20000301c0c0c0016039500061040303c0c03040070304c0f051003000880040c0480c4c10049290a10900015050b03040102c01e129800280509280c00d600250600400c56403181603912004040c00c44800300115141210498900d1000a159200d2b249100355000a000e03540549401016109041001c01c00c06410b0003a5141c004680640b244078014140003107000d420082c00580c0c0242e036500e500c0c2a40d0a032070181032154560907002042c40d500c0c6240081c039180c0c10298000708a40b0f408184814000c000c203c0c07041040314402e4032a1507140c4926113076040c0380700c20821a072620002900d0702c108071081d51929180e5004011031220300a9801c85501035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 285604154 1250 285602904 285602909
    0x90c1f0305160806060d29041d060a15081002130905040206120402240c0c04050f01090c12090b0f0711060103030f210504020f3a150c030b030106 64
    0x803503c1040000c80d02d040000180820f81210000420b0700314104000c0340402e50545094684c0301c0740003081c070301641402c2c06892182040070100d003001840c4001c1e19512a800035161441d516250040341c4c2d0b03026043c0c03c6200c080c1011006690548084003c7d400013035006070341c0c0040345000407100181c1e00e200c0c0d1041c60300c40e80d0050b10003458407900503268145030340000c00490784217046503000700c854004100e60300100e5204104843d5502003580351a0700d0590110a070620131410041000b074030074288010782c0d044409103000403a606421410681c2c407003045007542c3e403000e49410800014444400c41860046281005400382c64a500030101c0d030000340d203881e0110300da2100340100002881500048100da800d403074191025402d0200c0b12804039a030200760b03400940c483d41808154034041c1104954000c00700c031804a000000444003061480300d00d0300e0000301000c00302d40194403001c8245800300179440461a060110456030060007800c0c040d0760340000034038214060060303080c1403045109 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 285605404 1250 285604154 285604157
    0x18060e010e010b0a090b0c010606080a02130909030207150c0c050111150a020412140105060a031a040305090a1e0503070b121f0305100b0301091208090c1f030516 71
    0x42036801c00c020450913600c164426020841400d00c000340c04800c80b005440d1044203040040b900c5441c004004040d2034005d421150128410444030305103042c0340341d08008440c00c520303001c90740d01c0e081d0030144c0c20030303203140d00c0343d022200b07114800b08000390f11203407101483c0c0c8a45156020750751a030300110b034000070703038080e45132598400a02002d9a52020000c0c0b0b82c1302014200c0135203001d44400d500800c603440710b072049801f100740845800100c0c00a0080e582d00004c00d680500b0350b03038515211140b124440301d2078000d4109070f035000320f82854421401c960740e000300a0000e1008581c1e811140d6030b090000210405c0c034030716003a000f190a14021850b1012110b80441072400c00440e1840383c540003e01528031600c03101c071008025200001c0c1c1e0714810055005901405516208d980110151422103088610a0b40b6100d81c81c07000071a044865000035000389090340315036440a00d991b1400c2c602000440d4860311414104125160300310920450490b996814001500c3d1911002c2c00905040d08010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 285606654 1250 285605404 285605429
    0x1091404020405040c08032b0c0e060d02040e0114120f0d0e060705010e030a090b07031b080c010609050106020c030118141203270303090703031103120118060e01 71
    0x90240c5020f030841900240225184102c2d5584e80d102c03545941c2c01345081000d202d0760b00c2e04205040111040300c04002109000610400c490070320010407503203488003040d10038180032804a085502540c1683d0141086418040303c65031510000d200d81c040b01c000c40ca119100901a141c40c01201190071240100004000c2006c14500d903030564664080942e0990031440c00d00080000c80c03024000c1480d84403c0c07001659a0748d14a81c002841e01191360010440101c0400c00e19001036030064000c42e04940100c2c0c03904107030289140204280c4905000010150f00300303000480c411a032503100c00c1c103d909540894114000d180203140c01da94401114000314540c0e40240700114410604c192424005401514060b40b1a500f500c00150000d5031201941020000c0138403a8001c50205901c0740800c141c0103500310b00d4810b003066070b110300343d00004003000fa8940c101c850041d400c000341c50f440301101051100c1903846a0744c800b44281000c1081c041c02d4201341c00040d508003c002e41c0d0303068511040510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 285607904 1250 285606654 285606661
    0x5090f0423220606030204050f0403020a060b04020712090e0105010903020d021201110a08070207170d11030c0d0e0a0e060a120c0504240807050109120507050301090317010914 77
    0x15040c12004084010b041d0b0030204030314081c603060303401d010b9071842840d0005003070b811030060004a0b03400404040d58001c641041c4008a170b0000790784003e003548540081a1201d0510116000c1e008032140100180400f8801250781754103c0c0c4082c085e00c038a440c4002e5140c2e40c500044482405500c0065000400340d03c2c0e030742c0541048440220b402400d14004501e040500c0c1c1261140e034405140c0700002074650087c0141194103012301c00080640c0592a00c501076202d21140e2101080410f18052004138500d5240340038007071080c0c500010796042912000a48080060080038941050900c00c801c090400300e415a10050403038003802020708107800190400ba00c03c40360302100c040030394011407002800283c2d40c1e114003c40014002840c2a0368000321400180a802c40e581c0c2c0045203540c026540c1404640da00404e00c604895640c2084030519180342001405d11907260801d41d015400c0140380424107400c107604c01c1d080921840500003036a600e50b5520200e600d605101c482e0f660180012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 285609154 1250 285607904 285607961
    0x7140a08041106030c0a02010e150f060a0b04090e1e030301050607031701030309050f030d021b1912210206040b0402120105011503061e0e07051905090f04 68
    0x219078018490416030898070b2140b03002407016001110f410600303010010b6030303c0e405907080c0100016071002200400714000d5141c51804011001407807a49615505c1c00024400c1d0b841440c00d20080111959845d5903546620300407019083c0342d00c40108921916040319180c0c40c210036101200504240910b081da402c25082141c1903000507016010400d0440764425400414103106000f1132190310741130249443e020130b11058058191809110760811401c0c0540700340c0100300011002c2c80310f181c0300540d807100400220b031881868166554000e403002c0120f88101c0912607500340745c1c020315020808005095178101d088001e1480c0c400181c0040c800700340094081642c0503080307880105034100501c840b000003402c42c1c000b40d002170103100218440200322501442180044c1000c20903152081e0075030951212000000d100303407410380c00321100246032107101708142c1e000441610489a0802d02441000b019500480c410501c1a1a0030039007900382c1c81c01c1d114099492090071450441101c08000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 285610404 1250 285609154 285609167
    0x519030209120c09011509090e010504110105070203070b0a050c010f0c0e0a0b0f0d02070b0f07112d01090506100f0f0e13080c010609050a050603012711060c0a060507140a 75
    0x86100907c682c0040101e0040710238010350700507824032000060300b49040d080c110f4152110105043c18800100110320160300d011038000e003070b1151091081d50f216600542103440d44521118a822540b824110a004201a03004040b04210b29501c42c03624404082c10440c844006114860404108000d025125511940178010401203051300508108084e00c40c4090349404650000002d001d40c0d00b045540707a001450410200c140000800070305c0c3c110384030b1104a0340c060807840b588120400b1040d40e00070b0250400ca02c01c9500030141d40444c10446401e600500450243c00c005481a0b41c002c6260010090810100d0304050030083c00354541050749841111046025100c0b10382c100800d8140840c240942e100501e610040040c051a1a0607050201d98024103418400d0341840c82e6007040e03415569a2403020f15241c2e008640a80d60b5103441e03411807084600c1c258100f040801c0b0540b9244001c01d449002601a4a0078019139840140480300d4100c0a4018120703040148a20400d0f00d12400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 285611510 1106 285610404 285610439
    0x80712060803041406190909050702010203061e040908131a0a021e070e0f04020906030105010602030f0a03140903040f090902090105040506010519030209120c0901 72
    0x1c1c545860b4440c604c641d90b00d440141c1c0c0c04403445d0340e6201c00c460311049400303108a0a0f206d025400382000b0340034070031a01900c1c44c10b03000031009401070003168802c0f10018404504075250401000d100b0900103c2c454100d0b5603411103c0005002c0001882c80d1641d03064503000d40381ca402d900540174200c000a41c02c841c003042c4858441182c0000310a56901e0f042038070481c485020300030390f40c0703840300540c4030f880f41111103c1031001410180d034410b030246000f502d9005c00c40d5128410315099410a11440c00164420001c0b8400c41d2540c8020f041d0001c101e03d00032070030829078848281801d100380c89111040d00001800c21403482c82c2142c0d180241130110046c413141015400080e16240705124050056444100050040e03104d58221142c8200301500c0303500d6074928180050080d000041100d0240c0051682454008000681d1006e9102c00825100d1242c3c20003d42410008480 = true := by decide +kernel

theorem cover : BRFrame.Cov 285431654 285611510 := by
  have h0 := BRFrame.cov_init 285431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 285431654 ≤ n) (h2 : n < 285611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
