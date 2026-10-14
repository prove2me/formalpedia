-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:49:23.030554+00:00
-- url     : https://prove2.me/submissions/4b2b8d07-818c-498c-9c64-68f5e115e4e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 181654676 ≤ n < 181834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 181655926 1250 181654676 181654721
    0x50c1002010213090e10050705040902040303030b10050a170603070902040905060415080307022101090f020a050301090503040b0a0509030f0a02130902010503040b15040e100b030706050301060e04 86
    0x58041d00204a150a0440e80c030314250380302c4407020200c90000d0300b101011b41c894907018075240550b0344403503000802403c05608103a40d0321901016a8499041240003c0c1c4581c03080302d45080c00302c1b5442c609035a1f814818100300f00751070000e01921807111049c235904030b0000816440e4070103000c0c0303001400085d202950741c0c40c2c84019200c060311061390f0f1107000c1c51070268070702810030410f0044400c2c0c9424802031840c091041d02003284906014070001e445002d1901400120300e424412401060300c030700404421281180100407442d40c480c0c0c07000340130741d0411070702e000007aa02004440c00e50300d40c56840c540b01c060303c000440b0940204502c40341c041c42038074080c4440710710001e2000d0300c4a01c2101d481200b85030f1301e01580705944400700d000707001c1034050002c500096504c0101960007201071403140c0e1150340c404001000d80e400362003040c0341c680050406004010440c080c1d01c1d12a0300c194010a00b81c2c1ca0000020720500c0305108070020000300d51b01e41d225580d80c503040a03040604000190383c025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 181657176 1250 181655926 181655959
    0x21180d1e11030703030903020a1509060302030c0904020408010b010e030303060f011101060812030a05070207060905010e1329120604030c0c18020301141005190c0602031006080708061309050c 84
    0x86c0a03a0000b80e01c624803011000a9103100300b5031066980400e0b41e100702d00d240c644002a1302030342010b0002050b02d01d042c021200a622244060401040680d0010070141c5d00c9900141114202d074020031301a40040041001c2030301c1360b081400d01401d00380b034004500002d620106004001035080003a0302c1c018400280204203941d4060341c05682084402c0003591a4000243d0341e80c8041d12921011810040003002690302500001d0000a0302038001c80701a04a001c4580442d00c40c00b20042c910520380160181a85500040580d9442e00395000d02c0401c01c3c1400043d614000100024108a0f4503203100b01003000c001c0310b0000500f00000c00703007045080900c040303019400c00d02542d85443d9400022020b9881c20010340b54001e121034560900d026000506000b800d07410112507070600004030a04800125144000d511950400e540c54000500700b139402001c802c030150400080001d40741c1030040660310000801c18085907010300141c0e05c1040d241850500b2010102141e0000c086110990b0300b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 181658426 1250 181657176 181657187
    0x4030c030318030b04141015060f02062406070b090d0822080322050d03050f0c18040902060a0e09011203020a1421180d1e1103070303 59
    0x680c1d00c2a101c00c29019080c101c8010411003e100250400d1000710106010400500907400c50000d550b06568001a42180844c1135401c0c0c1c00c01c403105005038482c20495a503100a4920700d40400b23201400d402c4c10084404490000e0340c0b01e05152491060418113025a00c180842e00340c0d5138010390601b03091030402c0b40aa100d04503603820b503010503030040004500c61241450921308600384801003464a010340c40ba50f01d01d8000401d000141c001c0d00d4416a0200c4070500c42030300080c0b003100203114040d2050070060642d40040e004060716120030303081c4050079113100247c4140740341000b01007194103a40000503000e00400e0038041d420480020b00c80d8010343d8031440c0e40528880c252405036030359a807010703041d0b00c060070442d001e40142c0203000d41000151381a0140750316950524200d648100f0318168548004128480e006074001000400012102c1d400c60104080da00072a8640320700c6c0d80c6600c450490020094284446c6102e15800c803040000003003404810000c05030441d1003058480c500500b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 181659676 1250 181658426 181658429
    0xe07081519060602030307110712110a1e060f050909011d07020303091f060e07050d05070203090a030204020a03110f07060605030109030f1b061109040b0109030825060204030c 77
    0x24105211200d000707014042c0540760488400390b00452940d5100141140c80312038215550820f4040d11070006060041c000180c2c901d24064800803455036901000c0041c800704a910070000301020030640c41d4400803c01c1000116007150800360000380390820100c1301031044600c035940c080c1d002000410302007a41e42a628124500c066a040e00d0b0b19200c9059a49000c100d4118006502014040350700030604007042c01001e030b45100208402e91154424248900c0072a151000500c001c81c2c0641103880d1070184982080883c005035140c461410b0204252070b5075030101a00480e000030b44032060034402c2e805501d00c44071b08844035884096105108240da402402c043c0d421604040700490a454180f086800540c1c0c10b8a03410151800f0b40030070303a04054107012001c07000c7e03c040c0000c00854064066464a40a40c03240301e50b4602e902e40403c800c4030035a4204a04115001d4000c0c800500001c040710506114907041d50701d90003071401b440e202c4203012807006188a001250010400100094090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 181660926 1250 181659676 181659691
    0xa14030f070e0a0f090b060903070602030c0d09080a0f05030d0501090f0b090c2a0f03070303111614030d0603080301090c05030903040909020d0204020712020f070602060a0e070815 79
    0x36102400b4010440015040d0143c884240051034082044140b10b40c050003c0c80000f505103810404141c00190911900341c3c00308000d41c00001c0d607240b05182c1808021180016410b1001c11241010760003956205c00240c0240002120f0722610184030b4100240c80d41034807203007018446980c6404400014116420800c03501c075042460b0f0300d46c203141a030243c0e071141200711035241c00d0010707201000c42151a04120000d030300c490358018040e810400c2c00000301e0008080d0055548080ea45802030071074112484640901100b80107607154101c04540d804032a130780042c0e440070811008070700503085114043e5940d0215251480c00410070a00d81c01441c100c51600c0010000c0203c2c24200342d58070b200c1186c210146401c208418461800940d0000c140030340046c005036038101c0390342d020600303c1e8020038041e074031910340c54603a42c1816410016640041e500703001400c802440c22038040c1d52000080c118206458661020a000341c0040040000030403d81301154541c2034140c81d615134a074000d48450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 181662176 1250 181660926 181660937
    0x905130212010204080307060f09020a09020414040203060306040f03030b130504050f160909030507021e03011a0d20090403050d05010b12070c1b0f05041407140a14030f07 75
    0x207180708603042c402c2d141118400409189010800c2e43e9050041c1442031038451000e68a0a0f4400561100a50f50001c0c0c03200150040e5903e0034211045a00205c90700d0302132140f4010410864035880c0400d003030340c0095002e007c19074031003c5450250098080d41c0d2806400152034801c20300c42c14440c0c1c00403070185000c1c505942c10314141c1d40740c003074890400003802001100890f000f08003411495021280c114047c0ca001401c10889900088090b070200c5040d00c00c0c0790000c03d6003045481c01788200010006002480c800300c0b800500401d55070040c0d240060480c010440c01c134a000d10940040c0604404020140083d503d00740c54040c10a8215440008400740f414001241c100c2c2c00008540d240e0001c102a01101e07a110102110480d40c520b00c2101d848400301d840500c00803c40910078003508604040b60314490a11040c00219041c1d00745981e0718072452824040c43da81c001c50040003a25038031a10543d5000c2d02c510903101c921401d1140d024146002040100b03c0f043c0c00302060140a0a6456 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 181663426 1250 181662176 181662199
    0x320010912030206072304030807050c01030c1409010306030203010c11060f0606030c09030a02041b0212180f01020a14060610080f0a0b01030f090803010303090b1e030a020409051302 80
    0x34820100c041c981c0140580e10400101e48090b0180c0c001d00041000c1c03100304901682ca11859030740326081a8412078010101203191800c1000501540b054000c080ca4208a18031500c0001002007080307150000801a0006054010340d1194114101454015000303101501842c03400400d08083d05001c900d40740995070101e8461014070701d086004150003406141540c03184a00b42c50b00d135020001055051041c12015001a2207500406030041100300d00d0a640b41d070b031010080d0920014044040700c0c081308025248503138001d0b240c4980240f100342d4400140305060030061386400c1101070041c1407102c150301004801213001900314030560041c0d80550f8400d24000040d1038001040d04c010540d104228000340d420070700b692008200880514005c62245001001d000c22035801507010342e49030900000603c24140c118444d04000c010130340007a85400e0600800c8002001a540300100c074420002c085030f10480c031501644c003d0302203070400b0400c0c1d00f410305108040c508041c104a000f11600440c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 181664676 1250 181663426 181663439
    0x1c0b030307030215070e1909060504180f03021f1b05090112091b0f08010b0f060d0507030b2710060c0f0516060917060105010c0308040c03200109 64
    0x503901e01c1689070b001010240c1032805200c801e000e000308040200f02801078480340341d41c1c450400c6038807042641c415202d498101a044400d480705070300094020340c2400038170020706968a24000c00345400410b21100380d4040e00d003c0b4203148981143c56141e5203030301a805d0800c1420751100c411419034009600504010020a9035980201030100d404180184607100c0b0000c01078018102c2148100d14122018100c2c0a0b44c0301d0b501e8030358201000500c408942400143d07001d200d50344001d05c044481403444030007100011404c0c420700d04030052807512200842c01080c0660443c8990000c021301410044030742001c141040b107071180062900028550200f00484041c1d0000019100c0568989400303c03410345a00c0115030342803500701d44030700c552014860303400c0056440700d0141c4000c0e030740c0c01c000918008c0c0d03483c00300441041c4000345802220040007d680c00c42c2c0c0f21401a60b00d401d01026035580e60401c05165686544003400c0a104015500b0607241301c115047e07986d4909894001240782c40700d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 181665926 1250 181664676 181664683
    0x19020f13050d0b0a1805120901030b0306010305030a051621030f050910020703020a060c030905060106020106080303150301140c1b0601030c09020f040807150f0e030d030e0c061c0b03 80
    0x40540140403d401044101c140c42c1c2080c890690900020036280e811660703041e24040455403524511180411140c14640c0d01d8001d11240c21000c8000304840d5040d9240c2075120310a05034101c060010004611103c1c40ca00401d08040d517030028452036914480d8880041000c1841a010700041d180a8504035008043c1c4a610b002d0903c040041c004c500e90510b80c079000b94407001d016410752144402803400a211802220902ea0081e94045038403101d61521515200341a0080c4040d64141003040c03118410010949512062040030408941c0c55500400d0041842c9000031005920040030480c0f62a002e40081c129004800343e043c20020f2441c011945404080c0801015000000340400035440d841e0040e041c000b04150500e481e02d603450050302c0c0307006807a80c00320341d1050360501000407050f00800000313007022407410000203418002c80025103500091420005040e95118840c0c80c44c001000f070b4400c4110003902c2d550355052501e0510361424800c1074100030260801c4c6112180703003000f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 181667176 1250 181665926 181665949
    0x1009120f0312051003020f040f0e01020a03060815070f050f070c050307080a0510020a0302040f09050f0a021821160807080a020a060507051006030303020a03050708060102031219020f1305 82
    0x4d2800b040c52608550803c0101449184010b610540b105040b4421007038a202c0c0089444401e4001a51409140d6024040e64026403060301650400c00030100460f5403444900d038401203030b24194503c0c42041e0401d441d1405180d034030b80994840884c01d007081200100c00d02d41520340807400c8404803503031002c881d0360754555141d00805580083d40221001c1301c4031340203404078918a003005030405850f090890807410f80340c4c0c07050b4480303902c40c024418000030041d0000d03086410084c0c250b2030304203261400035290b5048890503000f0100340c0c100f1035800d400c0e42070300146101d001d02550b0034001e2500f076001040115002d48065805140d100088454000440369000c5a0182c402c041c0c55103401400d8807a40c000c124169014052070300c0c402085203992040b20051442503c1c0184ca41080c0c000060031144010241d1051121044c184001c9a80000660394180700707017000c3d04010740c0c6000b86c0c09110440d410041540600100750585001034080c040c1000c01c0413031065107102e9903140708015070014407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 181668426 1250 181667176 181667191
    0x9050102220b041e0506070312050c03040809100309050601060c02030f03071a100807061d0d0201090b09010309051203040219051c0809031203010504060b030408091009120f031205 79
    0x104410444c0c285800100f002400804040310361460781d80b0041071803540844403c5000079645856442040894443e154100c225050b03c68110715040ea603412280c0f291511051241281c5c08c4400c505910941000b8800395005c01600c905507901c000282800c01719031001c034800c0c02041c0c012000d4900c0002a1032519400c10281b91110315091072403030320004c011b4042c205900c1210000f040003581040004024207240d038400e0b0581c41da0444459138805505502440ba19900c1c071803402503a80b114006040d5080803e4107a5120070101c0140d0082c400d81c2d000611038024400440032000d55900914803da0090380e02003c1c03014224450351080070f1501503550300100348500c5145800d02c002d00c8440f40d501c02c1c41e03018036140310800001c1c90402c0b4480401c052140002c0140040c1c2058080c0100030410300010300d04606003a40c1e07280b0315000e091403060165117104201400d0318460360f099001410740f0600c01100c0040e6051041c0c80000d10a01603022030300040300880364010038410395120300701 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 181669676 1250 181668426 181668449
    0x2070602010e10091403040602060a1a090a2c03070210080405150711010f0504111c020f061b0d080f06090604050405010f0e0f15040c0b09130905010222 67
    0xb0f4001c1080041c0b02d07100c03041e100310b150750174401d1498104100400207810b181c4c004041918001d1004010303150404807007080415500d4020085440300007801c2d4100800c0400880e100008100071449001403d640401c00b0b83d21003140300d08102c0c08001400054029900c0f8100e003136244005645050341910000c103d940301c1d50589003015050300242e6044681450032003c41c0b01064115404d4901c031002c50248695100148020020703245a111985003043d9240b010f01d08024510403142020581d002c0e0040d10489c01580d203940d00c24089400c5408540800140f9403013003000203694401450f904804281d980c40850a5840c2c0500d90714880c0c1401016080c0550381e8406002c080d0401510407142c545d211008101008040d0040f1301083c0500350003000501040424030380740c8080080540d400000c404140008105880b80700d2058602c0c090b1150b40c0d81d41480041141b010ed800704200c0e895180241040c10004d0640041260005100c42c038800e0080c002d003064588800707841103904071032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 181670926 1250 181669676 181669693
    0x705030d0209030c0d1a100605040501030b030a0209091b0411070305091306141e09011a1e0904050f07020303061c0b0f070f02030307020d0c1b08030a02070602010e 72
    0x19101c0d00202007030080034060310307003034014240881c0d515100c002c4222003c10508000401601c4090101644100300349a00300c1442e2400c40301030300758030550194904250b1602c104400c41d450030840c10041c1030740508007542c00d103401440d09440c1c6100c5d1394a050380c0410a140f0990600c1c1c6400b034050080401e41c00f41c0c0c503001c2d10341e4041c1d92680c013520903150041e00c00303014801107117030910510004044103010108040b0b41d49040012060b00b01401c0c9560031600e20400141da21200380c03050545024822000300720004c103c00000c1c6001d8100100108050a0110050510350300b025100c110f10640d07082c085602c40e0303048919481c0c01110488010791051000400d64a043d0720380243c1c1d0701a41445401c0ca02d00c60315840b043e0a403c80300710700600f40c004140810140d01041000305820300b440078504505242c01c001b1f44980d0319004020070046144102c030300b8071840403d1860202c001000207040155905980c0751240c00c40391580025029943e03000030784a006004031001800004041d01030503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 181672176 1250 181670926 181670947
    0x150906040e0618090c010e0a08060112080403050709061a09131503050a06050601020c01020715050a091e08070f030b0402060a05091e24030a0c03180b01050312070503 73
    0x1e507002404030350722600b0b180e003440c0740d0782000310311074000d0403d00050500580700c00000341c25804180c15031800303500c1d001c4081103010408078903103054441c0b840700d01c64648064140001d15004a82000d0b000b801002c00004032820a54085070440b000d0301d2801030090004108183c0c1d60207041141900890003120b10145045641c0c0000100c508003040211040d85035240c0619003491094204d5901307a84d4424091654307010010198a401c0910003405440e007410400302080720130010310024048041b42703124445009803c8400600f1998140d814102c50031039038080080800e100d4864180900400840c502c0c60300c240c1c0100f03403038000c0b000c0c0320b49403256030034416142e0203800c2800030060180400655a80c0e15032061502180542e165003943d62030302c0411040c40d0342d0aa940e0101c0c201101ca180303001060206480c0d004882103400608051a04000d401600040c410034003200f5480381000c0c01c0044891080e410b90b0015421951041d1204003184401d114215000d41558028802007060303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 181673426 1250 181672176 181672199
    0x306011205032217010917030420040f050c030a06060504050a270507120c0c0b06041d030c030a140309070302060f0f1c0b041104060c05070503060901060515090604 72
    0x2020780000b00f09181c0e03544680c410fa20095840b0300082c0c594403080c002c03060003032a0101c071080d840380c41c140702e203541481c0d551403514011065204e0035008502020380c08660b11a270005100444410060240340740c00c10751a80f40f80c0c0100c0b4030a003607038980400803491503c600160350984101030181c0320301130f00300079600e0010202e080c548015030b03008000c811411141c0740260341c050703012030300c42580e011801d00d82c0805542003002c00700c1c1003042c054400408a508040c1e5150004400d6400244410030b13020b14141103000c100e0828014800021440740f07443d80040102401d07242036407800107802c00503119602c1d91109496108181e400584140054039200c4002d0080d8820000d8091800e00c66a4152405801138843c002032283c0c40c60044911210a00414021800495007042904d50541c2404500e000c0d5028000800c0a00d441c5070040003810048503000d024010100d5803203140c1030f0350303c2e40a003005004041c01000c60310082c0c0b0000d5951402d03248954001000705051a041803060303040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 181674676 1250 181673426 181673467
    0x905060d1b050c070e0c04030303051801090b090c01020a11150d050103061a03010b091504090503030c031614040306150506120f07051314030309060d0b030601120503 73
    0x11100d80d206640040369884501c0d03003800030a80e40b01d00352100c110040070307800c016007a4480e061322158041008181c6240380308403030550b541410002000d840e010080c1c3d1b45607a07442e02c0d200071507103460b0070324061002c09041240314071160011902c070203600b4001245c80320800d103002403c00020440070f159500c0d04c8000e0000d40381c000800d0070b051101858103c03080e64001e03401514203a03a02c0210043c40b040018015218100c1a4001c0c0500110407011030800140103050100320151021001d400350b0b40c0e0b070003241240b5000300859440303040c00124620b030342e0700a4511402d41e0030064145143c0a00400c1000400d0f146070001d6414a40b454407174174040c1400c1420128001040030300032400da0b40e0b60001e082a46441d02c440c10a518007640395070100d28018003200309000c001d100b031014200d582c58202e02520407000c50010307d1900d43c80400d05c0c0d40a03100c103c035409003020400c048070260540c400004c54204404850b0541daa44a58080168002e4130207000707030300200024102c5107003210500310b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 181675926 1250 181674676 181674697
    0x7020a03020d02041b080f0a06140d0c0503160f06170a09020d120315140a09020702030c150c0d050307050a031509020a033201060c030e0301050c0309100606090506 72
    0x741016850003454004017500d03462102107180c02091040c0444855106a40700200b024100f207001c0c10010030740a501248007034075104042c0001003904100044401d00001c1c000501211070302500780400282c01d24150103071812201800500050700d91186c02a10300400c0444400b02c2651110540b060141c0050003050341c001306500790305000900d103a14214040145646c3c000740304500c2c0c1d200208400e50756481407001345c0b4640c00220950341c640e080e02c01160204400103a4512a910210303081c0941c1c58880d030342c4800c10301840414001d1400003440310030303a05c0d01512800c0c041c55a0944031400305903569030000d00180321146e40b45000e80d0000c20701045e40a000714002c0da64004400581c6d002c12025000261030b000700e1a145607010003400100c01c0c0000c03094580f80140505181401014407409007085483c40c0c00c24241130194a00d03140d0303070001800900c41031614040f02036583e801a105c008040c4180c0600701c2203621940b08150a032141542e030b0f068000d00e068100000b5070000c1440d10b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 181677176 1250 181675926 181675931
    0x90408040f090f05090a021f02070510020a02100c03050403060c200d030c0905090f180d091d1302040b0102012405091008070612020c160e060607020a03020d0204 71
    0x304031107911012020003003200d00d002080303000041040700141e81d0007038034400d401d5210700540001a030b00c50a48145600d40229545500c00c2c17011003c03481d200aa612441d0092300303006a03a0401079011490214250083e0390607903100f54240001ca50034120f680025001a100b03002c28000031382c907078218080d409054034024071480650000e0848860002001d1100c0703601145640101e190980500382002029040c03d24004e894440803a040d448000d0284020340080c90000f100b00741140075080d0040b00390b8044850000640d5005002d0300d40c0c9010718400102c2000e00081003002c0d480d06288500f4003070071400b404501903801d00015007000c40301c060655480301c01421030451100c031440a0602e06c2d8a440d00c26170f10302403c0c01441000a007120410402007802400344a50020b04842226810b00d40810880701c0715010400034094502d24400b10700905840c02007450b40d0703500709020ba40141ca44c1d03200c15103c0c1301c1007018603c20410004e40041404208101500e05810625500750014001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 181678426 1250 181677176 181677179
    0x903020103020a11240a020405011b1e1410050712091112010f0e0303040b0711070e0403050a0914030a02210d020a030e0a03030e0904020d0b070320070c030209040804 73
    0x1030030301c4a0300080882c11080e13020307507100108004a445d0f030805070344041180f41a0500c2d0000b442c02201d01d0340407808010510f074420410030411409110180c1c03810311100c501001e0714121001032546165450540700340c0590002c1d0044500c0782d24010344c0203460310024000514000c50103840700c400280c03000341030f02d006c540140d140c60300050806580b4a0000171130b01c10184070b40e400c0750243c0380300c2c1906070b006004000c00911b0208c0b0043c0c0050300340c280294543c5c40c03c086a071402003150022002020384400740400c1581001c05003000300f08648692500c02d813284900c102d06510601480d0741503104032840c0015041c0035044602d94400c0c1070844442225030040d4614201c070140c0c7e0040141d001e490b030390060503070242c80b0f4100410b0454104000c42c1c80d5483c000c0c648520485a1445001c0c80c070301140465a070940103090403903000c403c0700000d29050001038000c0041c15504400008030640100d80144000202d4020750f900c4184801850700355001d101000c01d0080c4200c0d1008402c010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 181679676 1250 181678426 181678457
    0xb16081302040c0e041b090803040608040b090a060906091a0906010b0d0b03070803040503062a090d0b040501051e0408031b0715090201030f020703090b031f08030d0509030a0903020103020a 83
    0x542e203802006c00e1002d511681e00301c0b400400e00318a0f54005e00150308240030900c01c5c0c5906c29075890304290007030840d05580e00d6041c40c0c1410848a228020300701464007020300c2c20803800b81c1001100900403185511201100e8003c860104021150345089803c150014490a4a018040c002281030030740001540c03803440300881e00e0300c045070b00251a103078004a07041019180070816160700c031008540c00701c44d40119001c4d03c001d1070504641d400c01080d0101d42d400c1680ca80e008081c0f4055000040e188181c2014200307503008040c15156030700300c202020500c01000d8400f07194035000d5076101c800c00b1b00e140d4a4807050325000c2164804d43c03400316020020500407031340001c1070401e08045450001480d98140c400502110fa42202c5050001d00511006001c00d400000c80d101702e4120502d140ea8a40d99401f44901b00180303e50b00b52030514507103001003a42800040580b20b241c0c2d52403000c101d50786072803103480d50360701401c844040082c030200300910055100360098042ca94042c145200c2000f2000d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 181680926 1250 181679676 181679681
    0x1e110a0203031314010f02030406030f0f02071b080f0601030b060a03050a0506090c0a081903031b03050603010c08272d100204061205100306090b16081302040c0e04 72
    0x104072440e5550f0300201800f414548110200d80d43e80c1c01d080c4201c01e030f0040640691240114441e90003403650350a882d0188202540081c1ca1205c2035202c00c55440800b840d05a003111401c003568054950000c5000c290140c00146d450342100c9078274010040360b03185a8407082c00c2100104240e030402402c5c0c82c000001001085981e05480c0b00b10040c228a1604240092070851060341d048d208400001e001c10003038002040b42c4003000306035848150480d01a0a00360042c02c10b90310841c280d00403100e01070310307840d51503400f083c0a05003c0b802400780b000d403032008441c42070054403034041c0d01844d0040341c070041c040c408030612440900303401c4c2d59078045610b1b010988185848034400c4030800d01007a080c0e500500303011a21600041840c1107003400e040000003030100b0023401c8401d220b15a29004901f08804c00c0d40c0c648019075100d48103119454280c079000005200580c2c1140503030003050003400106005001c40e80c4580103102c1c1915034003019408100150032000c0003001030200c00c0c0c450500030b844a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 181682176 1250 181680926 181680937
    0x62707090c0504030614061f020c060d060e13020604061215030b07080703140601110703050106080106031e020303030c18040c050c10140403050a050d0203040606151e110a020303 78
    0x2500c40715162403450800b80161806d583c05500012102c004100349a529072041000012a0303940c0070f800d0f10340600c0241e29007800d07206241c0d132011000c1902d05104429400c41030940780d00c6421010380f03884076059008440d048617002503102400388424003105202da0180d845c01c5a40b1200414168000c2200c1c1c0e045210320b81090b03030030442d29010070070b00350340094085402c22407070310b8100400c40d4241404880070001605140c1000100418060008000c021240207150003c0c003c2185d50b90715824035000709601c1c4801c0f40d41034042c281c3c42c0464514181c08141c0690050060f40c616901c54951841641c0440c1c02400040c4032508548440d482d5841007000000d02a100c45940d0304400040d5443c001020750402c0196003010305c81d2902c0807200d40d515404c80c1d131508000c4e880b041f8030034056031540100d5009000051001c000c0005002d00b68001d8000c031110158000c0c101038401400b105c84034941d580144001400319210004188280d2140b98030380c0c0c54034188ea62210322580040d0540d03004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 181683426 1250 181682176 181682201
    0x20c030301030212160501140c01050a0c030605010f020c04090816150e0304080c10211a04020405030303130804050307060c14010b010801090207210302070b060306270709 75
    0x4030040c0218103000c0c84a0202c02225070042c01c81481c65080201d0a81d058020b4030304204481203285ca0746038011068860a10055009100901e0240075040050804286a500090500e6000180355006078260240369060380d01800b24110054248009040001422681107108020803582e039034080000b1010035124507051030703103445800b20308030650f070080c1440358443d001000100f005600008a10101c400705480c010800c410758101035880048550042140c034480194074070300c6910a60202503890990322882341c0c9040e0040500049000303d004140e0503620170800302d0543d01c2c1c2c040c60300422610410581d1300d0181c0311000710381000c090760301540118220904800400142c1034181e518400b802e0001c001d20a12407000900ca00c50620903280c2c0b20342d00103801002d0061401010680d0030320300780300c2c09104014a40040c000e5100c18420303180340c120540800d0712880c012946034060598051016651140410504024002c0290030402d9104601d00041d226140b0302406404d66003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 181684676 1250 181683426 181683433
    0x60c030903080f010b1204050a02090f0907091401060e0f060a12050c09030d0804030207150806090901060e0a0b040603061a1206071b0609020306010e0a0609020403050d0507020102030d020c 83
    0xd29280c06090750501410300700080e40c0700b00c0140300140000055508082c0040410350071368641d402c1841c1851144840a908421104c0c01c01c07802d2400c10f1001401001c131102100c040c5541d44046100300c0d106000c03d9011b0061110041110911425684a029070002d0100c0200c0300c0711070005015902041d034200204040e03400e40407035150503108882c0e000e2003280300240f8160841000a445016201d1840c0c148040070000c6010b1500c00c00c140e2001d0840780c0e119a0003039980c2c401c05030007608103c0e0680e206004480002d0314407001805400d04442042c1a0800583c48000507103018184061403182c00c20342e110400800300e9550b024140101d1030410616211944480500490348100c46070303903845a1094040c0300049901801c1c540404230178682c503c2c500c10707582c5887d0019209194001c1d40c10f114580000c80d2480080b030400780101d180c10750422200341d85012100c10b90050344005015074008140c220a0395000784000c20703a80388144190703486d0820501d4201c0803a007204070740803020350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 181685926 1250 181684676 181684691
    0x9060f03070f180e07060810080706020303011518060e03010207080d0606090e04150218060715060503191209050310020c01050a051302040b060f16050c12030403030f0507060c03 78
    0x200182010448003d00400340041e440001d070f1140d5500d8644140c004000b01c1d040060003081a403200741d0094440f400c151010195141700096a0760002c0c0a81c0d842d00100f442c907411064000c0000c8081181000d0034039026614242050b211390311900c00e07054142d50200b190f440000c1d603c2d001015542c1d03294000088031418208000e004180c141c0000021800c60f4080c000401c8030b12060703401c6c081d03040001607960240c141070340c07052040b2041403e8122030049861070400010895030040702001000c1013004d07a94580030160b0b55100b010119019070865403203a40801c94640e100c0100389040c0c105809400d56800103c0d1402c00c0050511041175804242c900c000d01081c0a5113400a40100c0103001508003001d0404104106600c020b200c2c0703940b840a21015198182921503019500b01d0007906e8040b09800d41c1d183d400200002c035000e0185081c021000c1c0750250030700010641c808029414a0b0941e82d0a0718485040c02420381481822701c600c00000d1020300602060900030398010400c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 181687176 1250 181685926 181685939
    0x60712020f04030b040b0924040f081804051f060309020f0319050d020304050a051309120c020310022a01090206070c03051c050d09020609060c160914010509060f03070f 74
    0x30201070000c0d002900440071a944c001038001113040712303071000380180b0a1502c40b890800b080000d4050000c01c0140d010808054104403502a1a9580015030b002d202a944000c0c0200f503100e001d400d12640500c5058042c4070b41403295000107500c2c0c2c0302130202d4040798107500c0003a1400c02c94000481c00c04400703050140030004240716040e03010030705000035030800341014001409484913000e110b00840c1d0313010243c0c40d044866003100390079540080c2d60500540001c00e00918003644076030180c1c041d116840caa103801c0c5441d48211081241c0c0c1e12603440085056000300c440d4a0310109175081290b4991039104050382e103842c01090110311500c0c0c9e03103141c64a90b1620504000f0542000c03040a001c20b01d000c0c0607240c00c0300c02c4404004414400241001d03007031002440d18062910f0312034000d10041188001d82000090741003082001c2010b4800350343e40c0d00124000d45007060320b01d00c182a83c6000410640c140750041c0d681110000745181380d99914031022074a40b110f1039000c0c1450404882007002107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 181688426 1250 181687176 181687193
    0x4021605010207140f0706050306040f0507020d0e0108130204050414070b12061e09070203040b0c031201080d0c24091a07020307030801230312030103020310020c060712020f04030b04 80
    0xa40a1340c1014000c3c4d081750b40c542c3c3c0d8550b00d040c464403082c0440080000d400c0d139902e5000483d0007181c440100036a00341120000c1d942e03010f0801c07440102e801000c41c405158011090b40707204603d0310842e628070000030342c00e2001400d0080d1045405036100b0107019884001807005501900e090b042641d2156500e1016101c82c0f800540660300400070b034200031840440380652080d20500540742d0500949442c4022441c61060394001e0414260214030014104c0f0040020706503010000b49030041a40c03907030172032a140c0d00007c1000002c203030b5031a40da07400280b00f0f002e0301842c0903c0c1020981e00d03020000d5640e05070b541301340b003c484050040c4601c1806015034200d2540210a500c011810b1803026a006411500180a8000c00b00146600302d480600600704541c078200000c0c00399140bc00d43c114461200d81c2013030000724400e000e00002d1658400c014802e07600303540e0704100248407948036408242d5007070400c120b00e1840c4035000c10012440ca50404014070046d03206103d110310340c1c80c15050580c103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 181689676 1250 181688426 181688453
    0x50112080714070504062612070f0302010204090609020903010c0207080c13110a0c05101b0e030109140f1005040809011b120908010b030a17070204021605010207 71
    0x61020010840008505014290303034020354454401c2081940c00c1100c10300d05011540855070041c1802d20110b6810fa032040021043e00900480c0d15002007450202c9440d200710140b0580004024020301d00410403d00000700600d0203030000620340390300c0340d9001058902e107412007060150001103070b84a42c1000d00c210104040b6034409030150900b01030110352500c441000261040400300c40f40403a14400342d00c14040c1a9114035410742e1802c0903000038003001042401a19140034030200c501d03d0010501a250700814201554615500c1c8030406845100401d00072940540d40c0e0050000054990510100d154150340001d16040c0200c900311460481d40700309640c102070174142032000045d00780c0141c0700c07001000d092004602403001400d481d2491034501c05000001c68400d403295858220340b0103000d84c0c1c0c15000a00440700e047c0c06056441c41200c40081240f44800c038103080e543c9042c005070513410310085c0054030307104602101180340c0e14400d00560780d40c1d500049680801460854500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 181690926 1250 181689676 181689689
    0xa0816080f0a0906151403160b03060904061404061e0204031e081207030903110c0306040b060d0203030d0e01050609010f091d01050412090911040b0708090618040501 73
    0x15903403400707908401d0078080103004072000548a0301400f04208868100504c0e44140007800c201856580d81440b14451200c0c4d441c038017030301500041c01104561101d501c1e00f40c0d20503010b01891515001c0600158460080080d0307010744c1c0d1080e00010400e0f0f9a203400380110302524003caa400c4041d021b0003540b15148481d118030034410001000016030005d2851103280380140c8140c0320300b000381801840ca105400307032602d680242c0410003011540545c46084140d000e0780e942826002100c09140da034452060391a54036a009000003000150015010740c0d11070b1b006408a80c80c42c4017540800d01e036802903442c1d51031080d00c5485007024004240b184550102d002c94031548030b545088a41c1c1224509405444a4240c88045242941d008032041500040c4010000c1000340341500704011001c0885200000242e10701b03a000840c00601d0041c04816444109568078240c07402d60080290b03440414221865182030211013801ea8800010740a5405d09050000070003680000f0407080b81c2c13058100b00e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 181692176 1250 181690926 181690937
    0x9031110021608220f0801060f06020307141f06081605010f03050604020708070807050606010f021009110301020301080d030e0703080f0915030106050c01050a0c0e06030a0e030a0816 80
    0x192a20301400da204040d02d074100741941d50780c0c1e00002d0050364100d15100e00b82e00e1610181c07400140e8000c4404104200c4c2c8000c03008120242e03d0714681e1150b802030388140707001070713000340000b03030105080a016680018907002107a001e02440e6a030210500c01d00014406e4845da10141003094000c2400010203800d008200c00100c5030610001030b00603401d9485c103100709a070700d2002640985135603044840e407542105100e0748a5046241044041e0700038081203e150086802240055005841c0c1e45000040358000e480c09000e10345413000206002d40d400d035040c103a207102e151142c1e1400c2c40110f028280b0800038088540c81280d000d42990210341100c0a40c0e44030130700800100d08240180c1d40c40014402800f5500d8044100080319682d02d1500b042d4440e100100010700c554000f0014040700d440d0000901181d540c0c0c040c1d54003254908107120000c034554906000701442c10000031a800a412640041e0082246a2403440c5401c204101000304107200c051000718480742041000007651407908 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 181693426 1250 181692176 181692187
    0x606030c0607030f02190c21170d0212072a0206040b0901050d060e071404050306010e06180f010e06030a111e04020d060501090e10030b060d02040903111002 69
    0x104440b440b0300701001d0104001042d0901d034440c42840800c0361420a03500450a881907800d000340d4030049032040f009400300303171481c50081001520000940340d401000481415840ca0345112040d80b180e000d08841710380c01c0003203208640019458600031000742e95141c000001d540254882440d14151080d54081154050001a44c1303003030072142038404003600710b52108070382d02c0103a605019010901690f070b414505c000c0390b001d00044600b880741c0640d80d40d03d119942d40c1e40300d1000500c030340e005590301508540014801d03a4600d20025401180140202c44424652080100f1880040e01d88000030448103004000340007941c41d400e608014202c000d40081c0046980c1c00c0034a0083c168070310b00444c041c07a8409124840c0001910140d500600b055640d1000e20524000418590088030301050760418041032a10003000c0c41407080306081c1e00e02c0d6071182562110a40208001c00540d0302a0041050000585450080f8030401d846a20707500350380075000030f9080c2015001c031400850320784180304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 181694676 1250 181693426 181693429
    0x9030512090d14060403120606140c03040b0309030304050607030209030307060e0304050a091413050304031e0c0b120603010e0d0c0f050303130c090b100e0a03061a030606030c 77
    0x100c90840d401034880556407054040040303540c80c842080c01914010188025004440000c1a107510aa200c2ea85030000384240b4040b00046542c24001c16001030304041c40500805050310042070004060012030381004d55402490f001c50307100f218840401d80020080c007041100c204031440d000280b6040540c282010b200100c2c4e66070054034009042140c986810340700c1c1c0740040c03048401510003e00588411511149103070007800e141000c0c4070f1880f0202d000165441c084801c1e15030040d5000303001d1440d00d443e58413201082c0070000318400c000700142662074005010b4000d0340c1c0007040485001600c480c0b805131405582c400041038980264142441032000500c0420302074012103032410072032520151410040075000c0030100c01000d500c000810300079062a02e000c0d05079250310a0b2504406207444081c2c035400c1d00d000380400c5401004040381c40110a000d0718108040d0070300a001049031766a0f03612040141d65101d581c1c80d0721109207050202980c182444030640c045400d4006003c444503940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 181695926 1250 181694676 181694683
    0x60b0301120605180f071703090a0e090c100c0303050a09022112030403090e01080106180f0b3309060712270603050906060109140a0905011e06090305 66
    0x70700315695140020000909200d0b407000b8130342d00100329007040100000040d560b5000380500003143e03074150716846285200101710b50460102400804041d460801410381c200c2020f0702c50503540c002c0400015280d240e441ca040000101c5a8031304144000c50305000d01140c038060854030140b814824880b000d030300d442c4954009100c1429400c0070020303a5004c8641002c44d1044d414000303d100000384000c0c194800381e8042030310007038020207901c2d0340d80314a81403c84a680c490405500b00b07042a44481410607030000c0100000c00201181282a000003d030040f000e03c400c0d408860381442c220b02245603c4140c0800082e09043d8052600c1c0c0d50000142e9603002e28a00101144800301d07024091600c15002001c034035600292034100942c0340390110108044a01a090000745050002046003c0002c0c07104e0082c80103841b03021030b003130502c0d2020b400d042401e15400c0d04005101400140f1481c03d1241d00c0c02400a1024003242541c4030482c01c641d500207501050402081c07100c01c2c0301060021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 181697176 1250 181695926 181695959
    0x60b0618090a0207060e07150f0f030506010c05030c0d0e1c0f030512010b040602060f130f0602040b0408010204091b1403130206030408220b0a050304060e01090312060b0301 76
    0x45818081c40c0c1c1d107404001000c1d100c1c8880c003c10082c01c028210f043c07000c0000e4500140c6104100c0d64100f0340c0c0c5a402215400480344050340010f80c3c00d04440300341070180d4046500550306240180140303c10b9105d061840d0720448280319140c0c026100c01b1081d42e44007030718017891841214580c00c8402e005030305143c00c07010340c240602081005054001014000d000711805a030b500b00507141d566030350303000c2c41003290010f00c200c0380903004103000510109408065603214400103030030444107d22585900c2065030341c3c0081121105c1d420440424000720f00300c0508000c01030305001503a10b0f0f06054101060702e002128a404000020000624450300050b500585101c01d2484070344a980382102800050170315000a5041803001090005200703072480103254015031442101001c00c07007070450071a845540d00c070b0a16600018082e60055503c104000d503040390280001190003041050924215400c0d81011004030b41441c178005400c100c40c0c02070800600d02101050300b10341c582560a90040c601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 181698426 1250 181697176 181697179
    0x30708030a09180608071e0506030112150e0f010606020f0601030302070e090102121006030b0a030b06040c05130e1b12070c02030109050d050c01140103020609010e1f030207060b0618 80
    0x100043d094a606074461001802000c0403982ca00f80d8550283e1074885001d000e5011400034604046100c4c140345084074120780000540030101203690320381c40b0036117a0056000384200d88810b02c880e0403240422200e148041800c000003050351403c00003a00d40148030062404540000c0010000700c1e8020500804444188a60b52115500c08c0c9100d80284120a5101200d03e4480b080c0480c85054207409400d40320103440401001c3d401d44104100c0d140d0611000b0714a8520400143c02402c003504a080da50702c890410038100b82c0340c1d0031280c0303507001160003801c0261100d4007000111600c118040115010840c0960b2820104004000810f04000c0c0040280700c082e0410204545003540440c00043c1c00c44c00751940c0916008000307081c1d6101064892482d82420090085800c405c150103040340c1c0d0080000385000001c000545030380c00b17002000c1e5842030601c610320711714003640c8013400034032041650010303510551440e141046600c1030300850b00806091002c9a480080d040c1000c0d840c5a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 181699676 1250 181698426 181698449
    0x406110a0c150c0501020f12011706150112110904110a1b0c150903020f040b0108061903080307110d030c02030a1d03010e010b091303050313020103060e090c030708030a09 75
    0x10720410503100c0d030790303e104014030942c80054448460308402d00581440303034182c00b500d41180d0342c9015000c00083c0342c0f00086415040300020822110f4200d50442c0d540106040814107010000000401c1310100c5502920381d500005400038289131620680c0c0301800c1030708406007400f08a000081c103840300c581d840140202c6101c048422b00c0341c80300940c1f0041c1039030354a21f0181540080c0080c0180348901c001c03805804149280f81b502d10702800340c108000d0041e541c0118950b2440200000c88840105181851262200200128401030021441003540d52504444000c011150901e442010904c0300101481e019000d0403031a40801158001010341c0340144107858240c00c0400e43c080d00c40b1405505620b4804455012141034011000c909411154034000783d07107c041c0348041c2c844510340100020820800101c0503059140411780c214018980001c601d603d81003681524142034440d40c0590b802080d0055107458100014070103000c003a80030710304140c26248094244100307806400c1050701c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 181700926 1250 181699676 181699709
    0x70308090a02041a01020f06010b0d15030503070f14061b0309070e090a02040f0b0120150f0402090a09050c0d0317010e01030b07020d1d030a0c08030406110a0c 70
    0x10810080c1c819003540040007001000d5400c845451054220b48071a4050700420344004000040803030001c0c104c803103c48100b4a0324640c0003440c03004110b0034102c2c0200130020040800440e000304050aa034a12941d14000402400d040c201001340032111400400d80c0f043d001c10000300c0c0c2e41c0c180c0c441358040f5051101d44039203c11040a08004c00e1b80c02c031003d200260300400541000000c1c00790001030007920104107501060003070740160796010185a0203d9546d0b58102050384490340d00750f40c85e0100000340d4054809207100040340c0242500c01c0c1003032a0130841407009615010940304d40052144904001c41e026030b0740c13202c0d12113001c0080c0c03038424801041c14070b01b49402103490f0124007107a0f280c503c8507903071100403008031804280415a80701c41c026000500b85400083c250460314042d403100d0b804425080300032003041100f809529094015410046d001400c4440038201611301040a16115410803400a010310402210910300360f10030314088012a80e148000016640311000304c0d11101e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 181702176 1250 181700926 181700941
    0x509100b010f05070809040c030c030e0a0f030c022b02181005060310030b010306020a111209040c030b03031606050907050f09040204061a030f01050a032003010e030a02010f0507030203040503070308 87
    0x38081ea246c0543c019052241c540c10b6950715510103414000540c401300104170801110301ea0782c031544031004150780340c104000f40100e40104185507140e4802083c1040310109007944040004843d1482c4c032040484480300c004624101c840f480b04070211500281c040c0c500020b403240c0c010542d02c5254012000000441c254941c036040482c06144c200c5030051a0796541d10384203000750f0000404600080303050b210501500404580f5080035100f04c00079905210303013002000010900e000c2080241551201c41e200f032501d050000c4c0543c0e505070700c40400f00c0300503810114240c82c0001d215806c1f41e0400c1a0a102035910030000485100080d1000a02c2c1c1d600c0d803012500410307840e000111100c1d4420100045868101e00461080c00440400591644d89000380100d240042c00300404403914404680450b4040350b2810004034001400404d0445181b2070b403604550040c0c1d40640181d458080d20650070045000710350b008201c6180031495460f103516132541341e0107070402c01020052840c0c08640035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 181703426 1250 181702176 181702193
    0x1706070c1b0806101e03080c0715080402030f03030702030d02070206070c030f05010e07180e0a020a0b04260c060d0f2d05040b07031113090509100b010f0507 69
    0x1e84601e84041e00905480d104007598030341c2c04480c103e0401d041c80102003a00c001c4030400a00381e001c0c42c0d8000d4500c5041d9035454450381c0000e403580d082c40c0b00c1c100c2d00007940e06c0c24031500d024a90444d110003076241050b0040c14289501512034403401d6000300240020309a001044946e24598668010303241c03c0c00744009401840b5170174000d0449844a8004014000031150007005e0520860007081580010058252151003070710600398001c10510b5400c0144030507400c0040e910709500c041d1007211103e607000031060100d40d004490301c450089014416003802000421400c002d074189001074141030101955543c0d806400d40740120343c042059250b54100790000011800d82040a02484500c2c880c0210240a102c554200703403c28110140006020703481864003464202c0015907030f81e504e0100c1500a40314481d182d0700401c5007003003030b0000f5426044c4004090141c040002c621030030f090702a07e24010301c0340c0d1545002d9203000700b00951750380c105203280b180c04c21b02d080c1940c1340c81150412440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 181704676 1250 181703426 181703453
    0x2615040204031506080706020705010f1407060906020c10060b0304061d06041b090209011d030f0a0506010303170c030f13061b0201112703010e070609050a1706070c 72
    0xf1032202114800b00b01481500940300742c420b110100d5070041d555a0040f662441e4038421203010410221031740b00418810100d00c41c550010010061506040d542d808048600a9070103889507035021030410104501401451a0407600c0003051200c1030030140650118440940000d001a17559090303010711101c2e21119071078080000d42a54150714142c00d1801851855070340c09241c40000601c0850210107074402e803003078410183c0da000c0e6031825400350742ca6002c00c510a6998503120f844626031059108110031042c40748030314060203035945036242c00391041c1080c28100060070100010851300703045560079641d211101c00c0310060300d900c94401c85d0a0b040c5ca1124041c0ca2a03040c8144c00001000e031003002003602085034000c00501c229154281101d0041c010800320800303400c004143c060307610043d070300340014000340001118221070001c075150440c5a40a040411311249040201c0d00e00220801c00511001e040b000303a2241c04c2285980301e82d0001c0c05041405081c80103031091140344140c200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 181705926 1250 181704676 181704683
    0xa0308060918070305160605040602060610030b100e100203070503030408070218010e0403020601081911040f29010327030e040606170105040e0a0201081503031306261504020403 78
    0x700003035185d06016071103410200003050503c0c04000000307400b40c40b0f5401c0303604582456000e880d19803658000c01090005280c0c0c0b090825803070b10f01d1030030765694a504081020010751605a405d550038018031088580f1200c2103001d5400a2080801044d008400c503a802584150920b5442020388005154013136010564980425030f14000b14049120b9002103001e1b500075004c6402030781c0c1e614841e554a0301c480341c0d034103050707146032103e04002250000094006031004001080311400441110211520f400f00e10384d2a40900401132201c0c5051080c02030442030a01c1c050211080d80c5d030000701309460140e54040c08181c02040f4400f4035110717603001c05038694000c4c002c1c09040c0d07441034010500b8480500c0301003c2c1039000000201c40c80e03c1d02c0742512018101d0090800d23032401e500151041d0100610000ca800003a04401d6030690f01400146946814401c1c040c034103d007451402880c001008002a80c640134840a0702c01803400250b0650f44106001410500307440c5050104001c0d005036840103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 181707176 1250 181705926 181705933
    0x11010e010204120515040c050103110904050a020a11010b0a0b0706020d0e0f070501091d101a120708130b0a090b0a05090606010207440d08090a0308060918 68
    0x41035024120040341c200c24042c4048882e185c5400041e40701c0f4100a907401040040303040001c1000b5400b81d0400c03480d0f44100c0c0e00a50070505d0600100d01500e50448c1d080310526800a01c0480986d0040d217444440c001c924020880360070702c0c1e00402e00450090155074000d03400450740c5002c00c07031690102d4003821b0208400f406445214141e8030b81d1404401702602050241c6400812154840c1c0b641004550141c601005035010400803c1d64003200642440a005a111000305000482d4210190010b011420541c2d6a4980b80003e0190030b0b400fa05050400910100380300c0d250140d40323511071003290440b44005c0603440e90741140b130041800c130100820840250040000c01a40ea50140c4d01c2400050207442d246d50b20700c0012a1a0902c90060302c0e0403242080c09404080314161002c0700c26010000c4080070584180c2036041284401d045400300e5034000010b0910032a402031540d500a0242d4008082c440c026950103000600000c08003809881c040740010400c0543c2c040c43d20070440b902068 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 181708426 1250 181707176 181707179
    0x8120d02070c03151506030b090c0c010e120403150902010f1206210b0601080603030301030b09120c0c0109050105040f0603050a090b010608010312052110030b1801060506130611010e010204 83
    0x12000501003c4c0c1742440c4021a464001591074000d005908119030024611a120383c1c0d80c080066560b0491090103c040d9a281690a40c084082080c0e880d0310300f0540701952901d03d1450b00000744540400d0652504d801c0c2000c10300140d0304503c90b840a68510704051490b074407210509001400154011050585c00002905a040c07a410041c200700b4020104802e80c1d030755000064070b200c8010780e040b9415034803c01c010004141664180c9030400e05007401e483e0040354010302c080e10394100d02c0c100d00064001c050203c04035070700041401e0040ca404c2c2801c5003428589000d1104024141c130a00d010f2580740c030000b5241301c0d201c1d40901680b40e8006000c0800e941c4440b8010080c2409010403200c40d040074207080c003154011703401e80d100106004180ca81c082c1e80082d50b4200c0300400340080300c025044160120000349030000d0184110010300c8100360100c8040125429180f445d44aa07018440c200b10306a8107044101802c41607451500745680031014492005006010050100f805944041030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 181709676 1250 181708426 181708463
    0x7020f0d03020c070e040804260102030a0501140a180b2701051011030702010c03030f09060b0a1a1909090c0e12060f0601080c0d2408120d02070c03 65
    0x3500b0f10304400021240c28640b200704a0b0900789090310080c000342c0c020b1000f04100c8146808440002c040c2c0000c40e94540100325902c1d0036a0010785171070112540300c400602c00c101c55242a820814001c131441c820440c60000c5e0681c45002d0714001174041601e50390702102c0c98940341e0a001c0c14503210320300351000c5004072040c05420bc2080c000c09115552881401000030b210b92480401084c804002e18038100c0554015144002404e604509040c0c850019109800c10340c03107484500740c06030303001181c050202420071440e00119080000c105d03c80304011a4190046005d031441c22405040b1007118002c5850140d94203074540e8400c05d00c040c00c0402c42030703c99500034882156034a082c0c4101a0141c41d10100d180c039594115094031a43d1501c00000c0d00c80c1d8402ca000580016428034014502003021403140b05554811810760003a001807104a00030f07002d00341030b490082544e24080e00079104000300c06011481440900c901e102d801040391002d00c0342c1c404600c801150302030007004001405c1d89 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 181710926 1250 181709676 181709681
    0x30b06030a020d110a020d0c0618110102241303020309090403050a0905040603080a0e15040e16020303091207020a0e160f0e01020703030305090c151b150403050307020f0d03 76
    0xc07500300a03090811165501303c11005a440e0320744250090024441c110300d080310500c500c4007040e640e15440300001e0640818503880211842c0c040c45003100035001441c00640b0304000300312001401092540c5107010206101c0b040c54012030360100c200c07003445480c18102d2850044500d03507640039480000348410560000000e00d080000343e00d801901c0396550080000b124410b120142103030700200b0403030002e00c0c031810002001c650018100c0a42160b500e042d80c40c15000303900007034081000441070003aa80c500310600c10340c1f110741d03200031482d500d0402d442a8495a180f41c00f071101e1440130500b00c3c00c6550710b030310010260070403400100c600e03d0000101c0e0180804000300d9004206030b40740d03400c0c002e403044840c50007011042e001030201c13a2031541e00701c004050081031360000e802100e00e84600ca6880d03407290803001c2030849d40702c2d80b10100c03060001d1009108480d2200d540d03001d070000703500944521a065500c5501814501d03101e660f120002c1c0c0c207180c440000f02c211405502c0c1105074454169 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 181712176 1250 181710926 181710937
    0x10b03030a090303080708060d0602030a0609020c0d03050c0c03040b0c010e011b17090d0e0112020a09061107050d0b07051b030d1409210f1c05160816030b06030a02 72
    0x80c5c0d11075405032070350700042e148944280c0d80140c22038043e0380c80704040b81c07058005507081100d24200188290740c1d02c0154080341c000daa11808650081000a403505515001d4aa00300c00340b01d081a00e008a9003c50315928070a5114809504601180080c0c00320303000e60140410301e075003800a002e0031840720300861301d0041c40c0c21100b0100700c4296071001a0245880a01d100ba4826801081158850380058401a0b403400240d81080b410700224001c1160324005800c0e010310b00d485a04400b814100040c0020041c40242501540104002c20142e038a130b251200da0301e50400094850b903250394004441d244552a5891540108441c1040d2054070020062000380d01421040007506a00107a14081340c0060b00d00b1941540660041c00c0c01401070740e010107000d030740d030710a0038500710704054503096a401008000c02c1004003121565401c2c000f5005082d444881122206e0240100314409401c2c458050001c0c9580880300b0102012076010307900c40840c80800614003070302ca1901c0c0100c10040d5000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 181713426 1250 181712176 181712183
    0x140c0103060602240c04031709030705011103030c03060f03030a0c020306130c0302211c12020a051605010b04090b0a0b0d03230f070501020c010c02120912010b03030a0903 75
    0x101500000c400f480411080d10b0b10111941c407501038204111500f48000d00900074100c0b174141007000100150b44030120000c881c4611904035252400c03c4101800c21166501c014180302075003885412003a0048110ba5005800d952499107a0711140041034020b10a18009a01807000080220203c0e4200d004046114421000c68410341e481030f0310f04c00e40b10003025005020550940003440140341c9401c0c11500b00101c4007100c0040c9600c1c5103464900183e0044495202e0b03009960040195070102c0503080d02c25003a5415440c008000343d000f40309104064074030010541c117104001c01c04c18290044403a00500034014040d001050400700d180340001e9410410b26858507207044000e05041d4440421290561900081c070081d403450440d14a04035161500c5044040200030050401400070b440d24030700800005890712004034056003110561354411003035500c000b007400e01c110a110704032034481c642905d026992010703200b081c2d4007402d100040f4691501001c1911102c45a06c4410319007224007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 181714676 1250 181713426 181713431
    0xa3309020301061a0a0509121c020c0405010605040501030203040309050301050c090f09041a0a020d0603241406010e041b051c020708030402010503250207060f0201050c07020f0d140c0103 82
    0x680d0080c4c107a48072110382c80301341c0b1480c09000d80d592840c020750280029580241c40b17081c20510750390003070f42091603803003c082881d0003540a1405580c1e0400c08480c0f07404081c2c804104550629030060002d0141d4400c240c1003640000000382014441d03a010001000c018009100d2418680305010305034001d0035206000d20002c0100c1c0a042c90101c203070b2401603422107601280300d698064500c1c1c40c08002031460a0180d0204500c080515482c0b0464005601038050719030281d117003400004c003080145e03182c00310003418840407113808414405003e421040909110703541450803c045005001c69089801300d800c400c0241000d419040002010303a0200148084181100918400e04030701a00728040c2c100042400041e0040d401000215009881a045000180d0507204421a0407444060000043c1c0103000c00300840c0e6080540c600d07400c41603000900c4036142c800381d080c040307006e0b03448040d120f40690300005d0704d1074450310100d40c60260820544d082c6107080c0980c00c0d0f601c0b080c0780401e500003072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 181715926 1250 181714676 181714679
    0xe1312020f190215130803070309051806090601050a020a0b0f150102120304030e061903090b0114031f0b030d020106180915090602160309050a170a330902030106 71
    0x500a0040315001a4001c0c2005040f4131308440403c800e401000d10070f144c0080c2220b0100d40b10000700003074051203101e60340b803451103030802081c8070340c00d0040070040c00c511000005002c4c84e542d0303c03402541d2110003881c18a0b190420030104a00c0d020141d0313000340c8010500014031407100b881514881c85409541003800700f8406d02c200480e92040202c0b101c40303042605002280c0064031484624004103001000c0380d04003d590309a5030409560300488101290740c1310340010801c2480c9803154010094401c1d980c84d490417040100c2d4907031608540c80690000300c48000c1c10300e544550303c9100d2002c0c001d030840d800041140d00180c002c0005009004901c801c1101400481c40e65010f11b64000751f102903902c0802008130081e001409460301c0c00c8944c141c09005280c1143d5280c1400c007501d80c0242e6501d0a003510303000501410380516040790341c0546040400d034030a0f1900180400780254408451440c2504048a4020440390300c0d8410480e090040040e56000f8a140c201c9080c00d4000c40007044405d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 181717176 1250 181715926 181715953
    0xf060f010303090b0904110a120b0609030c09060406030506101d06010f1101060317071707080a050309010e0601030b1e060f1306090f05040515060a0e1312020f 70
    0x1840900c00100003070788000c028800300809101030945124060400b1685001040c104540c2c0e401440702d441c00590b0300e010406a0300c440e40181c0341c0c1034a080c1c540c585000b14040c08680c4918030103421034000c09204000c01c103030b07844503403104c0011600041507401508015503840a030700103610600666074400851500c0c58084402d50a0213404141c6a10345081800d8400f6a6000c04680b81e02d50107550303c150002c08a4070140c3c5441c039001e0305401c031940d03c00c01d500e00202c49000e84c0700d10307800600c0103000b040000f60140084401070f00b22410099100c1c0d90301c00e0098050030b050610b00140e405401c000004120725580200e003d4048415106141c0c1840c0d83e03101d850580844440307900a0201d0012425410712020315000790441610200e1501d45400d081c100351403211520039406030341e9104100901a0501161301440154402034049041c41400030780100704134068000076000c80004130703001d28485415142c03601d6210061000f040d0000754041e480b64220200d4541c00d02070007011883c0d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 181718426 1250 181717176 181717201
    0xa090210030b01081b22051309020d080306030a0807030f080603010b010e040c050909010f060806060a080115170901060806090703020a030b0601030204050a0f0302040f0603050a0f021903050f06 85
    0x14101a9119451655000c3d0912801c88005c1310401c99940b003044040701c28034040003841c00300304440103107041d03041c80d000a2200c40400f82500c03440c150720780203a046c01651209422150140c11850840d12900c45070300080c144ac44918004110000009903030007050380004100c0714429640c0c40c0c1d90010390701c040501d03082e41c5119080b10700141c03007000f030f504032071030903030700c58000d050709442c4c81414400c0c83d20110340700c5d031400e03006421408140ca00c100042640020000c0e44588140da030941081c0036414060200316040c00755016004c014001d049500c0c1c807a082c1e15002c01c5544008640a04000301c1c864000c0419000d041102c0c051800064001c81000500c04116a070190040d011946162034005025501620441c101502088001843c0e690380c0b00c400080c1079550001010ba40c99481088101c805d048001d5108078107100c1c080010900c00300302501015000341113841d0030403243c030000d00004090241c0d03400c3c0c2c801141010080c40800502044021082d4084810721348608411141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 181719676 1250 181718426 181718441
    0x50604050a06080604020d0c050301060e0901110a0206011203140f07060e0105090d0c020315010312030b01031a062a031b030c0703020d0302030408340302100f05070b0a09021003 78
    0x405500010224005040169218090714002c40d000082c1701d0b20350001900799330196001c0750400e03143e1018460440e0302803145492444598840600e00b00644c50702039242c103c14850340020f0320003108110141801410a151800e4040419a03030394454184d4180144e0881002034840c1454500c4624002e0303814401c2e6405030401e80020141c050280740203d4509440c0801203030180a6402c07070103102020990781034041c5218505140500070a075030000c08480c42032030036030304040c00c2c080310221070b540d070b034845506d0034605403105a80c0740d074425004048200074001c116507400b003030542c1d80781d0043e020001d0800007508061845051038000000c540e80d0164119600154000d50420801464910181130803148240152030500341e850407414149502c43e0503c801504e480030313542081c82c4190041400320074400034108039050558000c038166041111505052240c403000580609010360180d03a65a944948244807600c0c1c8152030740c01420301d450080b0b006900c03000d45605428000c0c001c1a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 181720926 1250 181719676 181719689
    0x30d020304091505040501080a0302060f13030503091905030421110f0a090c020105041101080f150d0203011d0c010c08030601050304020411070308070f140906030a060b0a03050604050a06 82
    0x10705107400c0000020080c1000e40a40c0e112190350300000503d51a14080d450091104001502256145d1301b0003a050850051001d107078900c0070420445030510314412110380c03e41500e006900d0f580c032011150320705841e4001422604071006808003c1110000c000d10030b0340d0301c0f100490300240d8224074803000c82e2910a4010070611780384264044500f0111218106a00b000f0300508450f561030b0300c00d034120f444416440380181d440300200b0080c8003484401140e019000c0c43c01c9495803a054036403003080304010381005055002c08810150070750380c20b1b8402140c4c40d0014002c002c2d00c101c0700200030000c2141083c000a0380143d02e26840d841d0b0081d081d01160903004a095403a60350780d10011030ba9688002c0c02284d210341e9880c10042d85c09003817030203849014031980b94400c1d00e051000000d000e140d81c081d080420000c40c0780c54000852309030400c1c0e410310781041e1002c1d40c9a45034281c1140180c0340e40e410400b0000c0b40421405005c42e810f41000c2d0240390255402c000903115a80000b00b81d481e103000d042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 181722176 1250 181720926 181720933
    0x30d03110306040f0603080703030b0307051002060a0905011509090605010806060d170f030f061302130302040b030c090c030f071b150f061401080f1303050c010204090c08090c030d02 80
    0x2d003a030070990001c203605455031900042ca980c503035941c680f4a0304001030660019980b08811903850404007c00c0c009072604440c00b1180d902d0000e030081d82c90f14020181032519403150212803c0100940141311030801d256060b400305501d40c60b1303840c0188004801612400c1c10000001a100320114003240100c00140a00380034078050f4680d006109080300d000c403404901007281c9125079040d40c010303501500c0c2611561007141002c00c1000b465100302201c2059240c4100103240310400024004011280c0c140e80101e0707200c0303070309000070305081440d1f41003a008031403c810010f10394400383c002e43c070440e501079902a05454a900440f8481c0815a03050040b1a1a41c0c400380403c542c1010140c448220f01070100f000d115a035074107030954071030754001800f100d9400301540056800c0700c1e00c151302200c80106007a4502d0314040e0142556420301c40a001e01000043c400502e640a4040b10080c3c222100300344198132511100a12a850449054200d8000c4000d11501840c001c00e160f0345040320b60340103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 181723426 1250 181722176 181722181
    0x11805100e1303021615030b0a05130c110604050106050a060203070302030a050d020702030714040c08061f02031308070302010906300b03010609050403090806041a06010908011505030d031103 84
    0x100300c0310a07000d1010f070254400e41d10002e0100340b40c3d180d002d0190000c04111004c0010341c09000d0213444059103803501c182e491400a007c05c0c2c4400219031005418000b011901408003a0b0645450011641c85d8545000318020041884015040781e4212042a11084040c1707540c3d42d41243c80f8012010000e0043e08108000c84c50144210301800c413038441554014a84481640082e1601c90f840c1d0021068500e5170001615900c1d0922900f9064803450070518520f00d440d00009108044088400702e1144400400d00b2482e8820420780300210814020340030041d4075200b1007903075103400b40320890001c0d000003004900c4034400c0e104c00d0708080d4600c5941094440d0341443c1c9000039000e051003040d4075610300804005503401d000b001c0040119500005641c201410018004400c0b9007290415500643c0ae001c00164950b0305005501d80024040809881c3c600040b500020544e200840543c20f000c001c405500c0044808012a002202110030f010010380c03041c2e05030307100c0b14090030602405000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 181724676 1250 181723426 181723441
    0x604060c0210090512060709050307060215070512010b18060a0206061e060714070b0702130510090203090c03060702010b03070b0c01020c01110309010605040501050a140f040203011805100e 83
    0x100b030390850064202000e0103500c0e00041920400f95050f11039407507202100340206c0980009188001d413500f58044d010075800c002004e584c030041448801c980c1c1a00c507002401041c8242c00343c800d107c4415906100c0340d6074580307001d40b05400802c480526503450303850400c0c1901c0c103541120426950340e0041e10041d900c0c40d00f001031480c10303059201065200c0c04408007542e66040d0051100a104585041c1d0060880d00d05510303143d450f030080c0280010030810381e030161713940e4003440c1440e004c02003003c034650303882c016040c46407074080d880089420300110510400083c04244d04003490426400c5030341e40d81d1640000c03820f03101081e1190350190403840052020b02e0b1003600400050b581a0000352410291024840c210b400c820f50554040c0d4000c0203024019100380261070007400100d0f001c0c04954100030025540752241d01c01c140c1e26903000503c820b566281c80c54841010f85c1300800071034996a41d1600040c1c0b2807120079043d01001e281c0000503040502c01120390042d03c0382804644540c0d9200b40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 181725926 1250 181724676 181724689
    0x1080102070b0402041e0509010606030510080a0b0a0905030a05090f1801090f090c06020604290c03041e080409060806101208120103030207031403090f0f0114040e090c0604060c02 79
    0x18603a40b1b001e403009909150228840c020320b4001e901c0c4000008002d85007450080c1240c07000750401450248a84080240d100002084c1001c190844e6400c465901c485171000020008040300920724000411204d201079080382c0944402c00c02a00e005105428020421103100e09030700e18040d41b095448018032280440d58812410304419450010f00369207591a44a40f0001c1c82d4040d100613031100040104010020f004c0849950a44005040c1c0140200c00a20b0440e0010b14041c0c00500110002d4203002c6008003c2c1800c181400c10100c04107143e007000031140c2d016020380506075080007c0041c0004d4000352061042c0000c044440c2e4003030030507000402d50701c62910305440d1507400b0b01400c10804a2090880c1c02144250010300f205444c6250011960181c12041c1805800c144600c1d8401e45505068181d41d0f4030803210050440c502c1c60058540c21307200102c0d40c1e940c03e0046000728280c80c8a401b41c501405029086a04100c484800c2188600c140d00680000800403e400b03001070a0a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 181727176 1250 181725926 181725941
    0x3090303030e031e03010819120c020a0902180a0b070215070f05030c0705031209030d0f0201061710140403050f07080d0218090f06010f050d02040e0709060801080102070b040204 78
    0xb602520b140510030020b03074111504c0584a0041000004010858000c0800041c2e60a044021000840c0840d43c0c0b91180c41030500c40d017020500c81c20b490020110354800c035044019100d6504115111100c03a09881d858610380603044e4001c05a2042c08540c88490f44140d84030035600804418050810200d200c1030380e080404119a01100800352000144091001d002c40303441c010001c103800c5141108061408180400d00d00140ca801c22207101c0986011401208449041c144020300c0101c241c0c0803801440241d0003003e01d03681440105e11301c0e00020a040c500401b898070180b001d070702050b00da4190683d0564004002c08c01c00c012420740c40c250701d4040c3c040540518503140c00c0c00a042140000da0380311907040c0969007801e14800909141c041040394104c80c103101511203500e8200d0001c0c0c404c1007070024010034401c01040c180c0240085404460140544d0000d0164900700002c0c0500920300900810380410401030021400c0c010500c00e8402c1c0503002030308603582d5142c42e001d10000b000d04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 181728426 1250 181727176 181727201
    0x9030a080d020c0106031b0e16080403022b0e040507020304051002100c09050913080906090d0204240611061504090b07090524032706090a0c0e040309030303 69
    0x1c0c00f00c1c0d07400c2c41081c0301c0c00000350700400ba08401000d0141d00324a4203105034210b171750500040b00601c00c070131120030f03c031031140109410002500d4460341820f0740340200000b0210003a07080e07407111041900c00764816405000c3d842c1c440d8500d040f81581044185c400031119580160b0082c8010040d03881d00300c200300c01e10f003c180190f0301603d00c10100e8009541c0151004c0000c5280048100b0460410281c0c0c00ea1014040b000c41c14446c110b5940d44820b0b00c520002248506404a00098165204c3d041280030b540e004100b00016803992079803042801c80b1103412003504100c0300001603054051411121f01c581c0349070180005550715285050000305a051503604965a0582e400004052841d11400380501d41c40c0c1407116454002007002c01401521084900b107480350004d1824004082504d0300a1000f901500042c1004041002c1900d21011883d03060701c00c03081403140e242c002080148841e401440b807810800d032100041035010605450040002d58010410400b20340b01e2303130080b04003990 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 181729676 1250 181728426 181728431
    0x30b0f090601030c050c0706081611060406050c04240e090108330a150501090b031305030702100c020f010c230c0d0311060a1107060905010204051c05011109030a080d 73
    0x1c1020f014a03047d4503411a40203d580002841345a40c0300ca40105030300542031a007000fa082041090680310766010f00000e103440c1d1101d0100b86010f804806440190658502003490781c2c0c0318002002003200c0039882e0202103061000c8013205404e02c014040c1c103032140c0500503c06a17010000030f84025040e0404084050f0624030f00c11001e020f4440342600402c070700c1c030b80840c40751444210360074a0380ba182c2c4810f06200a02c80c08006009800e030580e5848860001d45e5110950345050040c1507215181009600204000c0b042000c1c035000083d0027102c6000365002040460a0740041d070381d05460741400f03050068804c41480c0f00915412101414101000982c2d01602c2c0601c08180110700a0100700c0218080010003803500c081007001d0b03613000a460314207110b032041c20a9140283c0c4100b40c405000d01c4d8488a03180d051040c250111001054090010345000780064080b00d800c2100d020100c030b00b5402c2c54036002e8411303200411707100c030a54000d003d406600606c0c0d881c02d01d6540051201800c0380d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 181730926 1250 181729676 181729687
    0xb1306020409050402100807090b0705070b030108060106120603031b020a0f0602100e07050109180902030601091e0e1e0a1b080f0316060b0d170a030b0f090601030c05 73
    0x660500240000341039040e0b000c900303130a00d4410410b4080000728203000f040070010030002c06683c8121942d003111740180103c2d0342c40e50181017580c1821815000148144000030000801c1540024070324100c0e406651002350240217403844000352040d0f131001070000b4400c541400c0149100025a110403440100303041165541c0d1040058903005e260311800c05600715400101120705507010f140d500e100c1510142c4981400c190000c4d142e0699409204070180c85082c030004d460102d07500c940309031500281200c56641c0e5550b0141e01a00c42c502d90b54100e00741c0c1c03101c0c0b4103819006000d0141c840708d4140c00350401d960a1865591a4542c520110503584507004258003c00e14140310111521103c601c104121418a1032540c50a050008041099070081002125030729842c030b02c7d500d11540c01100450b41001030400103000301285500038000311840ba03140c00c4054529001404150b6003601e040c03007290990001c110818114081d520f4112700700e100003603c50341c443e600180d0201c5680c1089428203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 181732176 1250 181730926 181730933
    0x230612070e040c031a1c0b091006080703020a0b0703080118060302150d0509071404020307052206020d02010b010909050c07080a050c1c051801051c14061c0b13 70
    0x16103c1c6a010408655100d80c041e013580601d940c0411701030010b4072217411645c0105c0d204071080c0081d03207014100f094014003160500c1c0040c09200d291600c02038080c4159501d0326001c0b51a00030034030040344034001c0304c2c2c00090840c4c201002d680060f40c064450100c1070f8a411640b403071411800000c0c0b0301f40c03a134034100440141e480c2240c8081c2c0810100340c464684050301c1000c0201c0d08081e24145440d0300c40f070000c11204051a140140d1144250340c05a12038540c49800d40b194000c0ca8208103084107c0a09110780030b40c061200411a21941c2c200c806c4a90104000c0c0c4c03c071141c2c2c0304c9aa00080005c00b051080f0710f280e130085600207403001f0040e450300c26562541c0c13045400c03018510000810000343c01010200401a10f0340703000030394040040c0350a0162000d40340d4401c040000120f0a03610a030260f080c2e004005441c1083c100c038550350b51140c54038448000900740c111507910358100c1e60002c582c07942009400400034004d41c5001ca40c0d5052152140e0603500350081041000d0703000c006120001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 181733426 1250 181732176 181732181
    0x10f0809031b21040509010509041214121305010c050c03180f030a080309010e12070b0a14090106090e03030907030b101d160f020303070c020f19230612070e04 70
    0x2041220b8140d461354100000c01041c01c006070311440c4640400414400410340d0400c2001a2406a00700030540300303c4070121260f1070140c200d403070108080c2d0000300442d505c0d240d00d542382402c2c0b1a000800140600c81b41c1956107004102d1401195030003072240d010103050100103241d201c4130003802cdc070480c3e59041001034a440c160036421038207150040103002542909025209071851103c0c060001980455642d0b0018056040054100c00c1218086013407040340d6442510307803240b0b00002d100e0500d408200903021748110b01c55500b00c9450552400c20808000c002c0e2401400b0300c0010b413400307500d56100c07414200e20203846810b507580e5181c0002040f00043e104040c800003604074000303041c6051419840b100c40304881907003c1c00452a004250b882d07001c8100c0e82e10a81d141080d1490f502e640c004111952103180d0165002040c130450b00312210b4180881104403154159850f80c02e241c2161140c0c011600b00301c0b055080013080c00000303403128001454070381c40803c03441c140303840d404054009002e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 181734676 1250 181733426 181733473
    0x2b11030d0606021603150504061407030b0a05090606030103061e380a052209060b030c0a24050f0706091101090b030c07050a081206010f0809031b 64
    0x11241d94140801c10b10b60144840440700100b410201c58a038a035450760301e444907030109403070359180c1d032180000c080141562042d0212110b0100310b07155480c215401900500305444410701c81c20040d1400901490511400e5100d22005811142036902e59035030b40000e8581c000180c0740c9a034481c51030203908009407203240d840b81188280925003400703200c600b54880e0a5100d11881002113254010303c181c075841c500508607070094a00c0614071884007904a02d6200d25240407825604207075880090006582184006410440a40d6414070f100410000b0200e0035114003180343c01c440d4000700b1410020300c0004440700860a105180c101520302ea8011a44407160480c2e042da9079400041c107100c0094400c11104000382080411b441c24aa126034841c0001080c07120078140c001080c4041050600ca802c442e20f50040c0307031070313100d12442000140d10306084a51500103848039145071811440b43d901140103200b0b0b40091031030b26001c080c0903001d0484462803100c840c45100070441107080000c04100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 181735926 1250 181734676 181734697
    0x2060d0c110a03080a14070e1915050c0606090402030604030c030c0c031202010f020301052d0a0e0403030b15030601110708060108010b131a09040c030f06020307112b1103 75
    0x9420b443c105001c0070403186c50280054039130302c1140811481301d030003a40e40f0600c158125110841140680010b0003401419080f5070802c5d8010f00302c8000303454000e0060451003041c401070760b4581c0d0b550740c140501403800f250083e41c180d20880105000c01c0c0956254122240203140001c405690b81d15156084080c6610440d204c008101100c0203070750303086c821454072050b841400d61a5514080000d25800c220030301b59800003c2d00f0251500008100c1100b907503080014181c3c5409a80d20240e402c1c01c420100e8003030740428100711800c2c1031803501d002ca050300443d02010242c01e64540d0b000441d180d0b0040719a0b02d0b6244500b0901281004080088034001c2007918004100d4420744000d000d00760070518a10400b03d410b02c541004480c81c29042c45904100994101243da07580b400e00541800455102819141e0b26128200c01e0221070740046200d0216a161081076a007003081c504da0300e420700d1484d18101110344035031085406600c00ac40181440744c4c0360108038800300b000780b42e055074050701c8440c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 181737176 1250 181735926 181735937
    0x2070b0c03040605060406080619061205030909070903200102011d060109140903030a0e07031205040906120c09021b01020d0603050f060c04060e011106100e0c0702060d0c110a03 78
    0x2c003c010700030583d000b80706a8041c412603140580c0c083ea40c50780a4441014500f01c400c0c00700c005181980301e030b030051190381d00030702c131004039803d00c1e5407203074881102e1381d009030702c04000100b44600a2107500101d07980440c800c0259101c5034030030381954840c5904c56045540700c00c1c100080180c0d0440164104460750060b0482d0351401021300f085a201c801904500000070003045204e10020081d240d0100c894500400c603100800ca80c0c1341803803641d8100600c07215210b03003016000c43d804070140c0241c480c0d40b8410051fa80e298607101e0400004501c009040801e00c0e54140040f00490300a404400004d14611007840741c0480801c0c2644c021118540440b592601e0800500904000e000300150200e8060601414080410300140c8202c0c000d5400b03100c01011007030000e904c01c0012035583d14803901070320480d00f40800300b005581498070030301c4d00200c225000304080030f0b0360307408699a19078000c00783c0e0310303194099411001400316125490f051040840503150800010f00030002c8440c40395492 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 181738426 1250 181737176 181737181
    0x2072106090311070807030803041515090c0e09010b1c0b4501120f08040e06040e0309180a090f03020d08070801050a050d0c030602040b07110906010e0603040602070b0c03 75
    0x1a803418003281d2080710940e03c106d40401c0800c940340d0071039410036006405682ca0018608003d0050100c85c20034034051101c174840020711085c2940316403044001030f0313107000780c0034400001c0020300e410a005426044104212144144509084003200d051020102042000c0c0a5000a41189820410081c019031104901c40741c80d070750840c00c040d41d809940400c41000060003d010102d00e05001d91007011250b4560441806400c0c0400440e07143d00c0340c10b096540b07864104000140c081650f1481c050350501010076200d60340841a22980e01c005428941c649010400510751100c0181030300612a507548207407000701d60a00d50400c0c840e0300136001440c1404171150010002100281800704000ba028010b00c881e82d249071401d82102d0f4101c5959201e0300300e0341425011566264001010b680c8005800214540014090078200e40180451132100140406000d10300c801110303154001401d00300090254a000c201039504580a40001801c1c545150340d2508100415600000d11890101c00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 181739676 1250 181738426 181738457
    0x7080c090709030212010e030a050a0314070f050a2a0c1205100b040b040c0e0312030412140d020403030e0909010227030c090c0406020f0d020721060903 67
    0x2001040001a11024420310340400c0007002040c940c00001c1c41038031459050400b0300e50940001e401d185910061b00c0d03070341d05d45650240045d8010620107000c203060204820040c52104030151117a80e0725258610700300c50390781c0110b4480c1d03c119001020304c40302c6514041400b9246000860481c601100b50b482c400890500d44440c0c0e42950007440003030f800086000002e040400c84042081c00c0d10701c0461042030100005014000204002d50858035013a4180351050f44000c0d040211401601030b595400040f40c0585820710003214058803152031040ca0740d07101803082e0510341d00c940d1942c41c11410a400802071405a9209510903000a030f042c01c808146860400c40c00341d040710040000b10314214a03000340703441614480302e0800d03000c81070020486280c3c17003e00240d1110000200410000c3c80c0c201c00d10641c5030024001c420062207682d840c02e0025100007a50b0003c0c200a400928900703103400d100304500c0c0790b4001140380c9200c101c1041800034807580240c0c0459440380d220244000e000d81d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 181740926 1250 181739676 181739683
    0xa110d1a09120f090103150902070c0e18031e211b090d03030c05040b0a0903050d0201020c0601170703060227060315120106030c031a0703110f03070306050a080708 72
    0x40c01c448850303040003040c09840059084030340c4c8100a0a0210b100800a40148822020307544115107290000800e03030304000d20b445c0c0c100142c0703650524040c001d03186c1200c020400c2c1c40d214809289640100660740c0a0340d188900c0102010004806a1902003812406060481214501c1c0c0410301220280014125200440c040c10311a20704000c3c1410322010000c0c80c4103122001c0902415503030740b800360300540b0600482c1d0180142e000c0c0b95070760b240600c1009001148621090f25140100821034405034418001c45c0e18440c0520000c010136400c2c24100d10b140400001075213034a10811000200007001d03800030f4171103030514000700401350341e50b52012150290203000d041c1c0b00e01c808004100e803a4405024080314580c1c02d8440488068402d091140100400e400c040e000545002c800810443c020402c40c40e40f07090041c00b10341a0701c6440003601900c003904c501d00d9110009200c91104540381c1c41c00345034800c8a515001c00c6455542010400c481829044900f023500110028000b028081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 181742176 1250 181740926 181740943
    0xe13050d0c05061501050d1e0c0203040509060d0b0601200105010e0412090303080a0207030315090603170408030304030e21060106031a15070c031e0b0105040e0a110d1a09 75
    0x526581c40b49403d8030001b031051048240340e0740c100d03545840c0c0600e403e4100840c1c0e04d9000c030403101040490641180690380b81c205115043c0725904040014141d820f150f82d80c400755540c002504480c507200e0300010b64900082480e0800007991100d0005e032002000d01a282c000c12040c14a08103604080c1051849680041e00300000d100c4020020400241e00050159000e0000003005880b071000c0d00d13045002c0d08500c0503c0da105113660b4408250b4141c079a00030402c90b4441e040b40f01c0c1c12654181c0b516642d010b00c2c0b28a46c0b00c1e030400d20000d404a8054107401011584c010100e0b000000c080c0100e2056010000d003e185590040300140886601445108000d0300042c45c0d01d801449841c00007207038a02030249418000101040e0a0100303d2000e001034043c540c441032445126140c2088461500d808170400e507080345440d4000601ca04103486113445505c0782001400c0248150b403182800300050b83c6900b42c000340d9401e000400b2800100707501e410011203031041402030074803019503442e00906 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 181743426 1250 181742176 181742191
    0xb0909010209030a0b0705160b0105210601060c080c0102161202011823030d0b0a061110090813030506060a090b091b1603120e030406090e13050d0c0506 67
    0x1000500300b075a400040e00784003035038804d030403115560307032410700b194a400794445040b4031100da503480070300300400d50564a050f140280c0b000c4031044c801c22211419414030001e4803425801440040c061644100e44c0982c40d640602c883c0c920b840305200940c1d089070300640c02d11303196107211000b103010490090071508c013a158a1009010900603119441202400380e0001003e00c1501d61b060f0a90140080d4801090b2115600366a114030700300d4500000340c010003110700e01c11086003a0220303429005a0804242010010051180f090105c0e6140001c0c54514402c2d0380314101805064032000074002400f000d540708002a11050814600703103d148902504512040350804030350341c0e015211801c019034406400380300b00c1428041c00105c50164400c400001200c540558004020f0581058034100c012100d510100501042058429100c1c0101e0141c1c03400107032088010407600700c0c6070802540017501e42500c00307030004070b964459261641004404002c604034060103018001c091108503400040f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 181744676 1250 181743426 181743431
    0x612060c0f1112090409050105091608070605040506030403030b04112d1c06030501110901120b030c01050703050d02120417040803070b04060b030f01021c020403021003020304020102031204060b090901 88
    0x2990803601c640074844030348001c62004c626190203503074a400041e0000c0e0040700800a504001503030b1034940a10500c0c01410080f00d403000941402e001490344112415560341c1801c01e0b0030503003040740b0381e80041c00075000c0548400342952260f44a100303101000e0300c05001250b6860442030032001061121020521180c1c013070036204184030320f01d411100005844405071f64000303414611307071004011a41014105618068004c2101c0c91204000e000701c5a0980f02c584800d402c0c0c3c0381d4203099440c0001e420b034050304002c4401c9001e50081d1301420446219003425800e04504000100490300170892400c01d900c41d0100b808284052100d01d048100c00150140b4036080c100074020380e580c801d42200910341c0d600c102c002400d10503e076000002c0c0500090695000c60907910145010303410929094821081e0021164217182c02803086504990307000c0e000301246a0310b170f04242c009410082c0281d05501003000240410600446602d104511405001403403100d10701c00d03c1079000300142105080da2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 181745926 1250 181744676 181744697
    0x506040b0703030504030c05010c020105011d130b0c071e120507050c152503020c010e0f060a0315080a0507120f0b06030f0d0e030d02070b1209010612060c0f 69
    0x280e610454081c26007608003c100d81e2210300d0103d601490700d801c060f04d02e500e82841c000402d941034101c94101c0740c82b041070481c22005001c50024100b41511458103158103420700074002078a4080c0e0f80e81c4043c0f081c4645003803455680351958100003143c0f080c8600030035528070340c0401000c00c201c0c488481ca0351400e24140700c515620340c0d0342c5010240010b485541000000c0100c6509030b8201d5007a0203a0070186440245110610100c44241500840140c000c00c1114005548112101c909003180105500980c058031b9090010b030b540803c110f0010140c88881c0403000c4485443c10100800d80c1c00d000745182e8030141407041c1400341a4010900e4103842c0181070000c2602e143c4860403098020808511030703140c0f880001d15000c040b80c912980c5005e44c45107841410b8200100c1c0c9600d50041e002e440c6c2418030101d0403a190f001038011041004c1092107000440c1803141030966000e80020000114982c0312104050104c4640030110f40d0039840b465040c071225400780c050412030b009400c1008464 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 181747176 1250 181745926 181745939
    0xf01060315090c061409040e01090201090e0709030605060f21120315012007090f06050a0501050f071e060e010c091a0702031906021209030f0d090503090406090213050604 75
    0x50089210344c03010480400002035424140504881c501074000384100541000e03d008240030b00410a016400b040c51002d002aa03109181300e500d200d6015695101082403c581e1543c0c020070000e4086500642d51461003000740d140c9a11130f2204000820750354118a4400100703529088941c000c1048582003881071201d0201c0100d24091f2899003401c01014280d00f9400310840c09100c035451404510400c080041c00f0703200c90303220508503401840306101c519255001d0007005022440750a0001710b04001c1c0c0c019124041002d0a03070a841421408400014482d15500c10303c0340300d0095840c00da80d100007075040c0a01344910b20071403107181010f06000b45010040c04000828008403110f0f16400a012811940c0070301c28098911140c003400561443c42d07007050002034000d482000e40109451010a0f1406000001e1390310f940d244107101454a400e0085203006020899011262844103000103000e03541e40703000350130240502c050010385441079200c2100b07421020380c0c40300c0d0003200c00704000e1100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 181748426 1250 181747176 181747193
    0x1201050d031206060305100e0903180a0e07021b091b0c070801020c030d0b01080f0a0911040906050a150e0a112218021c0c110f0106031509 61
    0x448008035440803440c501410300741c40d0880031030b010304503440c5040004a0a80d425030701040c02a80c800214185a40e141c0c8080481100b054406400c2e551080c03049a80c05440310004042d41840a080100702075914410201010340c1501c284015030050300b4250180d265011351021280b4045800c03056900305222400d21500100f036140f04282000601c00300401170412000c030061036204002c55859000d141501c0c1c5a0b0042c2844215050800b00310815543c461400369003c1e44007034080c805142c0319041c0c014000c180b18901214040b01c50034074810650f4980c07203000c0ba9540510710101302071400302c664400b180c058469035064038170b11b42400e00c9198003151200e03078044403980000030321000000b0040018002c40601d00000056259400d50050f82d60658400710b98180441d64030101200100c1e01c26030040c00c3c0c620741854480000c40020b40c4182d000400304010905140c980b08403440c1185081c51104e28643e012a0745a40007001004016448581c2160300f01c1c5080148a2880e9507003004d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 181749676 1250 181748426 181748429
    0x4060905040c031415011706060d0905160e0a05070206011a0703170106050c061b07020103020304020a0519180c050708090a0b1602090105040e0307260307030516170106140c070b030117031201 84
    0x4603a555140b107410400108420400dd013801d5032922007140e40c4007011070491104881c0c44400302d04203004520a1030000482034103868a000302d21015032103044040ca8070f500112000e804000382440034002ca0b403448640719000c1c00c0c1c00e82c0c2d0716a40e0307003203440040c0c40c00f40007070314030305508048410610400b1055020f071110b4950900c1c01681d607480350300004103821415044290f0108031180303041d0300209401002c004481030860001c2054900e004220205d03001300c103400010031003c014002c009001040101046030009188504c44e80d282c10010141d5048100c1148204281c10701d51001c2d450040c0b422801050101c1d010f100900c0c042d100c098485c010444010160202100c10120102030960740c0d009015000e41c078141c503071030401e90042c06480151038890300020000c059071140c1b485452441150242a810309500780d00e400f0080381d8600c81c0c1400203102c083c0510625090712010f000040082c00c8128046440354100b0071070514120003643ca00807298000c1200080c1e40c40d1004c920303030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 181750926 1250 181749676 181749697
    0x70f0c150f02040b0a05030402011107050f04091a04060e3007030203071a040b0601170103120905030304090605030c09010812070206090603040501090b07020304060905040c03141501170606 83
    0x41c078041801c0114003a01030768200c80510b20011850491090b4000b0142d0700c200c0c002d0741d07640340700d41c00a1602d50310359005004042c0c011030080350003569801c080e000004010300c1050103680c1d60030851490784030300900f0395003100d01035120b03801c02243d42c0c81008a800c6e82141d00718842d00d800e0300b03a01481010003000320b54622500c00440d20600b454001d200b0350b5082500580c40c04240c151003800354000140440e0110769030700d00003010800d5540708810300742e031040b2000300c41d0314264215140d4035044c0360340c036600c001048410040418640c409001900041405d40c002003041410300c0f0426007042101c1c400c090055010f0001004038150005021080104211000c0e40c0c0d0400f60000c20564400d0100c29034000f2000030500c81041415070050605034090100140607440c1e03104202d8813880385101e02c3c4001428040180207130700d820350226101e103040c0c0c1800121001c02c2c0d00d00d0a52218210344003000340410028901a40d6000814082483d04181341344041d481d025000801c1e5001e40640d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 181752176 1250 181750926 181750931
    0x312051303150e06070504050406090c0f0e040e1213090e0304030f020105090406181a01020c011103090a0f080f0a020117040c0f260102040302092a030f070f0c15 71
    0x20100800c0551014031202d643d8001d441075071800e0701003d4070950007842240d0240340340040c0002d68003600d00c10903d055a40d5500d58600c589400b10844403c0700f085522a4000e96070a6089503403201049038030010884040416180c88a0050b15400500140e0099080300c0c100b00e0b41c908092008400c0f5001e1b03a03845000d000d141202030004031514040c0000c070582052401001003008414007000c3c50f00600040001d205c030015090358400d0002060000e64056440500140180e42c054408840001d03013150460742001080b0707000400900d1158400f580b14004c54105000d00e1100f40078000350501c0001c020f10702042c2e41ea00080210825540036620768443c2800710781040b441c00c40e080020301d403820b1500e16198032003003900812404006968050f1414407100c800c008018000e40d011290010310041059031656003110022080c0700341c203c0a2100d4205006e4170103c54000f03180a2443c03c0d14036441c80c54020340192000760b00d00b038840c0a000211000c0700000d0100e0007907602004140401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 181753426 1250 181752176 181752203
    0x2090f04060e0123100e0a1107020409030c0309060507080304080307020a1a0604141009021c0204031208060102010e0718021b010207030905120601090b1201050405070312051303 78
    0x3050041034004082c04182d420072518002d0801800022082010200f034011220303240c40c5122445600a8454600c07100300041c001480d20907140d100f0fa00e1040c607440b16510700003055000804446900e0380032070110301001080000d00d40c3c080e00f12030140202c0c1c18003a25141c070320f480c0e2448600006100070225000000010401c500c28031480030840c0e030242400543c22000d021070507011104584482c0200c2c6040c03c00c403a5040c4070f0311680c0c0078128a00001250f0b0f800e001508000e940709000301800c8030f04500c43d080c2c50392840d01c001c2c03006500800040700c5494a0752002000c2c058094072041c11a81040c01c030b801d400034003082004c22581c100c0340055000c03050b81a02d03c00ba00800e1054220003200076241043d550040d002400014030980c1c4d851052500c920402c844120401400c200320f0340070400600103200c0c258040b0210200c02031210400104281c801425260100c0d0225880c0d00081350801c100718000c01d66004640c00360420314101045c00c20f4000c0c5100380d6100240c00818082c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 181754676 1250 181753426 181753433
    0x703150b0f06030a0504060b01090501120c050417010207020102070501030b0f01200106140310021606150b03070e010833130c0c0c05011b0201030e0c09070c020108011202090f04 78
    0x12007000090041c000302d4a070302e042c0d1000700041c001214107980c1179060110114003984100b00740000e0760416198003858008000d00c0c04000c0c40080e5a150500104010100c0e020080b0307001e00301c0c084500000565039029610009042514070f5000320b050500b0072007407003890303a10300080c00c2280a0a00e003456151810120009400134400c411602c4c0f5480c054002c1030100450000c142c00701015001c41300c0100840b1411000c030b11401c1e8175080c100e41810000000109a0380020305400d40d01c0400c0400c4c1600c41342c1d0020503038410f071342e080c000c2100c0e40c05021495801560541d4007559025040000c1c0089041000e403000340801680035001c0d01c142d48079160360b02c0c0001c0c0301104ca5a40d0302082802034041000d8445a40020103484d07049040e02d0000b91383d841842080ce02840714812001481c1e0701c3d03401034000c2c281800c0443c8003401085136001c0d80703444200700248284130a507102c00714006540000b40c605141a0041d8469050300201c410240c0c07110400c85d50480102d1031140c603030f0340d164107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 181755926 1250 181754676 181754689
    0x60506091003240504150503060117070906060302040e0f01050a05061b01020a080f0c0a0219020d141b060c120f1201060906080901050f0a0209011103070602070c06020703150b 77
    0x104071002009200012603d491400303014901a6142030340e04000b1241d000340600c550031007070322038039a02d41d12440060060301d038160b9803480304403424821a59600d88039002c1034103488654012100207680401d04100720000e4242080e007201141030801c242c3d5050801180380d80507140101030241c20000307402601249842049255090580021502e03180b0743d0200030145681030f20422041d081d003001140c0c00d10341c14821038003282810380082c0301c09201000c4090541201031020780c1e004400607c500301048840c1c0310403a003007030518080c100548400c0f484413041d40096a600e0f00540c800d0041c04080040025000038604204e481d054507080c034605440d240340300fa604072412050b0350380e000240490b0014007040540e1200d1320f400f1082d0752001c4105080320400c550141000e4142d00100f4a469645d83c0182641c00c2c1c180740000314019440c44203440c43e8031112040305c0f0b00f0350008040081c0254a01003201030b11a601c050702c100c92454407141600341040082080007540cad218400c0540c1d5851 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 181757176 1250 181755926 181755941
    0x127050603011d0c0a02060f18010f050901180807060b060f040306050103020120150421050309010e03040308030109052502030a020c04060503030a030e010e0307081c060506091003 79
    0x800d040e60301d68507180002c20849611401074003140803100440e401010000c180c41041d8207990040215aa481c0c0d81d4400014000c0d000c011f64038018841001e0481d402e024092485030b4452000c034450078090925401c441d010080c0d00d0340c0342007488039000000d0f20036044550b0340d0b4000601241c00456800050301c41d00c207100d2a840d56200010300002001060b80080d4100c90003600e034154803005000e41944200b41141015109070402c862075081c45c4900e1b40010b40090140012854211240c1d000c1004499080c0000010403000b0042105032032003402039040340c0030032078081c40c00e2a29556039070b1400d020600800c28604e483c2c0c400121650038182000c0c060005503c10100e04c1540310740082d480c0c0c0d100044001c01801503401c001c00d507041500a010440f8000340045140161a04045004116044c4100c6041d52503844541c8000d2041000d0100903002e000c140341e4465420710580c03502001d0306405600310b4201407040256a4400c010740d01c120b001594041318140d0000c04c202c0080c00c03103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 181758426 1250 181757176 181757179
    0x150801060e040b0601180b0a030f0c02070806090d080f15060d0f0e0a0206030610020a1202070e07020724110a03030f0e150c2b09150506012705 63
    0x2450400148855072840460045015030100c1815407111030045807002240d00c04829900b00741e540410200d5002c400a114139415460002024601010070909545800689400590010b03009000c0c0013130034001c594105481c00c00802c000240e01030080c01e50070008200e1810588500000307041c1c15201c140c0414030f40002426503a461900310b0a2000030004880340f880c82500d800700114024000042810285400030202400c655a0b4400c015010340324905c110114082c030041d88001a504152030b1075005e105402412005007002692b00d0440001001c1104652200c3c0c400c100054003a640c2a000209010401b0745080800703809031585481c42c462500103200303070b8000c0e00905a05512800c9100340080043c00f40c2c80365080c0b05e50b81c0700719501040c44071410003000308e0401d50800c0300401b8406032201c3c43c0103c2c1420170241010030a00580d001c8070164440c1095010021a0103100e20f00012009040009081140008200603e00e280055620306403810b048050b40450b180c00c0c004000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 181759676 1250 181758426 181758431
    0x60705070305010c09120215030714070c0305010c0c0b0103032f0d020f030a050412020f1206090106120503071704081006050a062a170c0f0f120d150801 67
    0x152460320a0003401001110f84c002004080c020421094000c940d007201500140314040c00c840590560703110780e002030700c1402405043c003043d00030303000d840019060443c050014050317403074954208603095840b04032003d0104080070b44800c001500c0c462a41c0d05407505490001c05910401000e050750000e0144501c8940481c451303030f0000d07014001050700843e070702d55090f034880e01160721080c2e0b42c03805450303044070118000b440140440c00800344543c52030342c002480100050850130128001407281ca5000f50650048010450b4840090007004010f00421066400e4031501e17440c7d1548031b01030050028030f48804080450b004c8015441680d000c0c3c02c00078291141c040402070248020000303807148501a041b6484006206130140a03a01c075413101c00e100d0480d00c24800801103012441e00b050480b0002451321000ea40c107001a40a4008200b4501c0240301d002c4040004611307000c1d09000d4000340390312510074050350b0f0b010402506d15140151f180401e0041401c50345107500c0d8030540205140e5072 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 181760926 1250 181759676 181759679
    0x50424021303060b1002070609061115190e03071101050a020a0b130302071505030105060703120914010b0406080d030c020f060c04030308130309062105010b04090c0203070b0f0606070507 82
    0x240ca9400500030000454010f0410718085ea0207030707100d00d40380c85080b000c80c0c000c000801c8001d00070398800038860012010b90344042c03011548003801c80400e50b101c1a03412100c2d030520510740070134401c02181e40380000c020b60510102e5900d40c01584451030f42141001400715440c40c40a008015003100b090b80210640c80c1440c0203c880000188d203024250010b10130030304001000744448451880b6200380350b0700c09141d80e0070441441550792200c8c00031402c12031250341989600d0a54400c5c004403520a002d004c01e0549030a80481c00d4890749501240708900c4e02404201400000035900e240d405581030200303a0303180b01c00c0140d04090880500403101e000c4c0d4010812240785401c02082607910980711102d440d110b120090360390601d03105008020840c03010007400424061601c0414038405580b20f04807600075002c03544242e440030380c024588810041814410006140a07000e00c1d258148003c40c1007c915480c0e092250401421100789001a00041030726510707080b0884407805e81103011586940d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 181762176 1250 181760926 181760933
    0x1a030106080c1c0b0f06060706020309030a1103090a26070b1306020a0b010306091e060e07081b21161e0b07150605120609010f050424021303 62
    0x1d5a03a08585441002962950720303583c680c80e100c20030348940090101245540302065110384407005050540e0202042c040e00b030000c1c8003800103601c40d40e518409191108110f10002e0301c0400740d9400c03000a5001880005c07143e840fa0f86140040791072044044410070384072a40000e1114241c1110b800500580d1804a20b801d903080082ca00c1216030002910b4450b520700c0c00320380f1000c2c50303000103018070290801003001c107000d900202c1c80140500c07042001d0009041c1050380ca9407000d81c0890f1368689640541d00c6642091107420000c081c0403001d000a210b00401200920000d440300c1c0d0300c82d416813401d0081a1124405091518800004540400f5050741e9010340d000c16510a1400030000103c0d0220681480c2c883c0b04200d580308001d99041850983e54942c95100e1810035110f040e40d1020000703030301c2c1e503008a00c0b81843c5480b00074000c1802d0684016007076443d00751804c0c0d00c0314104404e00c070008004d502c14200d40031990340300103502141ca4030300c50041d204040f0b041c9018480f03d007012090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 181763426 1250 181762176 181762183
    0x1704060f020412110307050a0303030b0303120108150114030a02130609180c0b0901050702090a09080415110105060f01050c010605210606010e0a1e05030d08071b020f041a03010608 79
    0xd1034015441c440c80c1c500160209686d44103e400b41d80c2c1c200410000401c0080e00981107204074000003401d80f070600402500d8985150300980c41000b4130340c45242003030183c0c00300e030380201e0242c8001203002a03c600c4400104c1c0e5175001c844802800f6100610819150042030780c850006858000300620003401c10b410700781c04c4142c09110540d04009501c2c07000840d0f11619040f9540c440b811303159907040403c03d80810642a40007401694070f43d84a901100004500c60010b00290010840191480086890080841c00944440350341c680c0b4040074856644e80d00310075140094824030300143d0b82e20800c1c2410740035040329071005821041103415038590b41c40d074904c0c4081d120424000c64a0030360b608401111045900503010b42c200500c4502400b0001140240c00704d440940c0142901b619a5031010a180100c0703103804034000317542e0b0001c0c0100c06511050400301181c2e00494040300c64200d800140c1d020a00e070000a100b030356984112507010001d02c03003005200c00010020031016076214542500c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 181764676 1250 181763426 181763459
    0xd091208070f02010504020a0303080901090b0403030213060c0f060e15040501021b0610030204020307020c03031b061e16120c020a0209060117061e0a060f0e060a1704060f0204 77
    0xc15020b506221103244140310301880383d600100002d80030b40c5951410340d885000504002d26554a4421440100e0303515012036000350b10a540042e40c4002c0000300a0340101c0e00d4000c0b02c00c0000b100c04003004034420b501d004810070303040900024208500c1c2100c5180840501d0168104a41c0300c0c00c00c0180841980a400222402d9444411400b045a400e035110b070340427661841a1410700c007050000d13042c2a03002e0b5a000c2c22600484078031204800c0000e286410003c840b0300c03842a0500c2950002c1c01c24480240c002c0c5070403010180d804011f061070803101d8001051840c1c404025920109154440c1400344410b1401090410542880603c002d48411001e0f00a07070259070000d001c100d1652040030310000d1005441c20150541d1a0841007111030f99403080c040b0070100034440140015643c035001c04008042030b0311030036410040550054410302052035454031854040c0000c0140c2c41d04a4207a20060480343c6038100e0340d9035503240c4a80200380c020600c2c0354503440810b020820090480441a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 181765926 1250 181764676 181764691
    0x180f0a0e060c0409060603052512061221050d021809040b07090f050d140304031e050c04050f040201030b0d060e0d02010608010207120f0e04090609020405090c10050d091208 76
    0x4185c50b115902502914416a14030403492411025030003200c8000002d442c10a28074075000c400c0940341e000b0740301600c4045d04400b0240410000117000c1204030411f03c407041c00d000904050780455650f000d85180180040307419142d4001a00000ca01040030783e800c0e000c0c00041a980719802c0600300380798040402c4a114001c00d88074880850112014a1940126000180003e2020b40683d54070000720081000502e010302c018440807000034031010345090740c3c00ba81100005e028586080440c40c00c10b117480100e001c0c2d4a04418085c07882c4002c032001b5031054080c00d02003840d80b030190104200e000c086030050308441c03a00942c207000728004117400380034002c01e40c001d0028948030303880c1a00301d00c030b00a8000d000c254111441c250650040f00c0040b548000b40c00c061541c00e140740086400d8400201c07040320039a507145803220861403d44074060f04204a80001d00d0b0312002207022800001c40d0405030300034400e000c5112134041c0c1054005906040c0e100039040d14014917180050540102541c016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 181767176 1250 181765926 181765931
    0x14040807121103060408090103020c0705090a0b01080109020f03280c0810080616180b0f070c060507050c01050c0f0709140106020307121809091b05180f0a0e060c0409 73
    0x20b0014540010311a0245030802009854484480015070007540040c0107018540512500082c80380d0700e4000c09403003007681d00c40204060003207400050044c00c05800c180851031060100683c1900e000007501c1d0b01080021a502130301c2e46404840c81c458121030122040181000004142a40c0c4424042e01400307002404a0206454800c003544840c012a061070701c441c820100d5117211441428100c0c02048000c41041d4540d4581c459803440d03600030f007480c50080000090000c20030031707044046401845180303007050518806640700c903140c00952000504011011550501c0600184035001c40b0354081811038669070303500d00180c0064841815040e281c4a032440c00000c5003400801101e512035440140c0d00483c00e1890007c1c0c1d8007a140341c1e0741c1d120045400700e000c87d0311480ba1240c000ca00d8060581003040000301000090b9165464001c60301845841200c0f4a171103407100000b541012056039540055074400e40104014100c0c1c1d0109001446400b0503c0001c6d04140c0041082c3c0d16070341b006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 181768426 1250 181767176 181767203
    0x31606050c09090406050601030e0706020d1e02151513050105040f0213062a0b06030106060e1813060213091103070806010507060609020a030e0114010807061404080712 74
    0x20404601403600700c2c5400140400c0003030300080b855445258080014100010042c0595508030316056903a0888409030380040d003e44281134201d422900c4000450508920100380c1c038000a40702c48500f03c0c600c20400481d004034071040c00601c0b14508894014080c650700c1200c002e50380021307007028171a40380120700d000c004104813905402140c103a0301c140b44c270350f0080500d0311340c0868040c03001559050340000c844114260000455a0b0000058000d054240e281e003042010942101c225900c00018011186c7e1620070503210b8014504411040c41c0388036040303a48440c0d40445030030540c0380050015200080c0804600194032250003900c3c103404081003003420700700800c107080c402643e4032000300d00458005455580701e28020106184601e0020031401d81d138203070640582c0c009048950100b510307404180c08809007442025180c100300c080c5121503500d07100007203841d09100e00614040124109030301c080100c1c0030307080710010072352130f0200e45516545541c00600010035000c01c07126100030140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 181769676 1250 181768426 181768441
    0x905060403020117040c031509142b09031a0907090501030b061005070614011703040311060705031918050906280504140402011103160f06020c03160605 67
    0x586058942c103071915240d041d03241000e0b040301d0100602c11039a14092400c04000502c10b1819144c0e107006040307001c0783c42000c500e0042c45068810616015a60002c82e013800054200c03180301c641031782912044041c00c48085421541070780b0310340010345a41d4411a90036031858105056030300c81e541c1842036030030030768540004d08280c0e0b400380700103040b045840c00815001d16010042c2800500a41000ea1410030260b03611001c1d98068190300c41140b02c000010040c1d04a0344031071405c00303008400694509403c43e03403110701c04901121000e01814011a0070340400404000302c0703240301d041210710800d80c2c41ea404020040c0700d10900b400300003070400200203006e040a0a4490280c4c500406200000c6036007010349c50301c08042c00f102c0c4800700000d500010140c9440c0720b41c828803500030380174242c03e00c2d1034000544180e00c50f144c00c28441e4010003e0001c012100300c11911070591115004c41180722508006010340030716610011580000070710a0b81c50485080c1203400c0740d01c2420148810790703400d103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 181770926 1250 181769676 181769689
    0x1d060f01080a0f060506010903021201050402011211071e080301030c091b050909250e0f010f08070f02030d020307110d09050d060203090316140105160504063c0905 72
    0x80109010183c150100010b1603d800c840c2c0e0104042c9401c110640d0399030001480394508e92990a0140d54840502c803d65a101d484076800000e03900c002d02c00581d1056820810b4072600a000d0300c14003e09019200620364008860120781d008000c0546a5071281050813a6500c4c81c0b0400f68154640500c410000022014113144a03150f0788a403030801a8031380c280140418001c04003c481080500c00e980c801c1c002c1c002c1c0080e60095a503801c004a0000700c00e114869941807041d605001d0784010009a25900002d955801080d80c42c00c120091001c400a903d18011030000803100380c00802008002d0f17612032503404514102c80119500341d22450400d440c0b0024601450b07420a040301080400b0a000b5001141c00641e02422a4a804024a00d07808003143c002c40845040041501d0455111004d014040d0014034003c2454550b15541c100940075104a00c103031814040e00f20b040c501065030701800b202d002d14009400082218070510034130716041c0e41e00e88100200c0c01000c8041040e05110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 181772176 1250 181770926 181770943
    0x6030c041409131b1502030406031103090303010314030c191a0415021806041e140a03060b010302160318060e0a0b1e070f060f0b0108191d060f0108 65
    0x5800320f8035000300907101c00c1c00c80780d000c40200b100d044188200103488401c4414003021030211368040c40e2150b00701040102600c0c03400b030703a0080e20030041c024040903007008411a811a58003418854a070000000214254041c103411400d0f1801a0036416481021100402e080769100b00310119107090300042c1c0c801e9251060720b0182222b080d81d502c1c244c00c1e920781e0b4018504030100558029449108100195043c0e02541140001c82d040480084012070080ea0b40c401a00e6400211580700c008000400c82c91b04c00e511024040549031469810b10340d0107075040790a28822402004961905420090441000b0060301d10303e25040c2c0b4400224240300390461501054000c2c42205424a01025454103800c8100b0140d0380f41e0201000310422800e074030042403494400e08030f910b0340351480d0405d401203456035008802034500300001c0380c80a0f80e00c070311140d0780000b440c200d815004514410fa04000c0008155a40441d40c1c412030310f1500850014025206c1d01c442d800c401402e07a00c0e100401d8441d40701f17 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 181773426 1250 181772176 181772191
    0x207050d0e0a030b0108010b01020105070f02190804030807050606150408061902040f08100b0108010303050d150b07060506101812050c04060b0a0e0102070f030b06030102070206030c041409 83
    0x1019a100c003040c4255100001c01c880101506460707038407030700c44003903000080e44003601c941e40d24010100c0030b580a020703540d40044642440040c1c54140d41d00039455814400441c0740120810715024204080c240644001e160800314440e1034903a5443c209039203e00c10340e0024480ea003030009400281001c20122002e030f8a614020342240d442d840100900f50140300c00d451203183d02444081800c3e0019010100107000c0c54000f030440085d1010041c04441c0120200ca040107903c0c0010f1002c680c10200322460020000d50008008400c1050341128004035007003540d0700711002a00205114540d00801d000ba9022150111800f1030b1079416640c460010080607100b025150301006600443c580da448280d00880542d9103800020002900310f54035900250015100424043c3c40c81d680500c6840a5000a000400400307040c802c00a4900601d0700c8000c0c00b040c0c0c9000018400d4a017901910000390340036007029120300b414542c07020349801c14000c0c041491282d6009410614100110900030b104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 181774676 1250 181773426 181773433
    0x1c090c0e0c0a08090f1501060e0102012306030709060b180a14010503220803042f061606020f070212061909050f06040303061d010f06030e160311090a020705 69
    0x400d2030b020303110382e000101644e506000f41240100460400c2c070402d5000844410303070769100c0d81410405070840b0080d042041c110380c0b428000750755000b00320a00e03500d0b01c1003080b010221603441d200082d1803d40990040302c81c10b03003000720000d11981070001808140004200420521007503000b0702c076035100c080c030420301280f218030708400065008000441d04642008a0452030155504400448040344c1d5021141c500001041005003c41c01c00305a019210420300c2096082e00d51000190070094040d62500c11100050b40c0071176410085090b00019501070303002d6480f025000f900c1b51464100c01402e9000700101c00310b5090184c03000c03405600c103201048003515002190840100180010744040f16144942c616040702c80c1010000c040c89a07100b690b002c10b00034102031981080c0107908000d20755030000340c0014883c1000e001e1429095858510b000070b02d5074034584001d4a0300c5850318464804d40c5070750303502000b80708014114646107041a58074591944420503684101c0c401c40c10003500300e40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 181775926 1250 181774676 181774687
    0x31a09060108040201090e0c030103060b1e1003020d110a0207050303190507020d0b16020c030a0506011a0913021e090d02100e040c121b020a030e061c090c0e0c 70
    0x6002e00111600580189850541035464488510f00b103102a240709603221004001081000780d540980e903c68036065580452508114980340c84205481c05203c0c07049000040340c02425100382e0680c3c03141200c00000748940000002446c810303510114100c0014050400b010516080010464080ba10301800c2c2c80c1c121920000304581039001a4400c0380d0141c00d0050310008244c000e1041c40c021203500712007040004aa140291418541e5144a4041d400c20035640c0c02144010481a0451744580703000c5032030078500078070710003584a2600f4207680001c20000000342c5444560103405035070711100000e000e0f80082d0704580355034010490010303030207490070001c0d00050424800c0200a4442400c1c80481111000300240a0340c185034003c20000b4203426020358221040e010f11517402c0380b00001070b6016540c14a0007922807802910107024801c5522110b103850300da100440e071951000d5640c1c1801c01024030b00441c0500007030901903540520307610010440400d00d0b000c1074000d8070103220702894003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 181777176 1250 181775926 181775929
    0x12190e030f07020109050a0305010b040501090c0e0f0a03050118050105090619020a09030b01060e0f0d080306100903080403081210210201020114010e04020a06020c0d0609150c02010606031a0906 85
    0xa42c4840c40480c10040c042000103110f84030410300c80055407264001140c505040800d101c11a9016801031000906203030030750f10351a030052005440510191450301e43c0b2004140030641c0403400c0d40c0018680c0d8600400381c4400300310074183c02e040911400c001c3c4100d80b184071400350398007020b55403100440290384540f40f4001c056802441c3c4682c55047c002e03422940c03500d0704d0300394503400d0b48174901050044034020040e1903c900600302e1802c00310784c092441c09054489103c80d000090020307003c0c0b020545041e10300340c003c0050800950b40302c01c1050f078031900c0e4a007105064001c0400f00155603051400300e59509988a0000c0c1915081448001c4c60708901064100114400d4801d80c15551385015408503540d11503280340c0a010007440d01d204604052062001d031910315070105007190400d15001c0307183d031340e40c034100740d8600d8107e000814950310303e082c500410003110000b282c1d0946040800c4e10b9813501034100408890090701d04000401740888075544854107010940d603c06440400a000b0b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 181778426 1250 181777176 181777207
    0x20304030309050d0204140712060f030b060904020a0305010207050a15142d010b120903070f0b0c090402072f01090e0919030e090a0b06120702010209040212190e03 72
    0x58a000400c08109200d15200010000c002508c810000440800c4e4600048000d801900002d00b41e03000159040c03440d61f16400320b1454054080c1d44950200f801003815581c401074001d0155401030003c640d6070010307280042e45c8070725403001140d0403900a008030f240740000b8840c442d004074101502c083c1d10341da0081050443d01001c030340c42c210400748030840032500000b660500c0c0038000a01c540d80d529412404490083d007002040c041c0594000c010f14000103040d4070031000540d03442555207013603071207810010519020307080c0115081840031881d403082c40700824004080c801c00030024408001030070354413040300000d0300c0343c140440d00c1520100a80d410618515a2242d010403d0b81c521290900b10b2400e048a092015030010740c0e60000341304c1c03d01d04500340d641c0041088800f006003c810b60b020582501840c603505040320711000010784128001e404072029000d00071300442d85c81722003c007203055444065445113806008801d90500c484441e10422051017205c600541c1010301c04a0b41101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 181779676 1250 181778426 181778449
    0xb03041203061505030a050c030121060209130213050301050903070f02030c030601031a010905060d1104110d1a1915050d050703020a080912190e031002031602030403030905 76
    0x10507940340400540b0203006090552083c040e50b542507a2424400c198000761000a8440241280c0c02c1004014244040034a0a40c41441c4004030b80d01040c1070030010002e014080055401c80d1452004507440540e0380c0c002c140343c0d41070130001e10b00700b034694003803500729101107503518a960300404c21000454038003110400400e2000b000ca130b0811030a0004681003207001c1e071041740c11700091036424079a480010001409050156401c0045207030407800543c0409189a0252226051280340030351a10f598004148180420040642e07400200184000400000082d02052440c2240ca0074140c83e003604074a503c110320640c3d428105041400000c00c0302ca8028000f01840001c004184244000c0d0082512070030075614016203070b103a02c08000e4421034004180308142e0700300320b081e40711290130881919802d500c8601000c00c59444148182c07594051200d00650510440000405860080d00194400c034503070a2580310310300500400717070b03604d01aa0000801141c0b10720024069070603c29940c11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 181780926 1250 181779676 181779713
    0xf06010e03100f0905150606040302041a0409050d0f0504030f0b070c050a0614070f0206240a03060605030705090f06241603090b0703080c0901020109082704060b0304 73
    0x10910307001d000901084841020f06010026100d03000a81400b009012030740d4403806100400825141030340003e91140b00390b00009102d1913407042c500c0001c40e8200303c0810345003005041040f400c1d01900305175036284604160341c00024013180700b038400d085c407071010b540c2101d5000d02c485071240025582c0310b6001f100100500c2c10006d803001a4000308200708290b403180b034050305002031a2004070a840c0310f0410010300450906c11000600e2080c6c44d4002031031684281c6a070040c6210160105041c10348031810403205170303c107842820200a100c00c0d51303c80c9044501c21022580d045540d9024459200b4003215010200e6801d5400113031281800034003030406c583d0310101d00c0c3c40344880c106120704a0b00450b003e21a8601c40320803170010990414a00070251038020b403024206520741d42c00034407c843c014648620707428041048150f69000f500720f0310f0038503440b11046484500b0f011030402102c028800c1d12550740d22a0380110713001d080c14440d240c2950148000d407071846c0d0b240c0d00d44c003501070000704950 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 181782176 1250 181780926 181780933
    0xc0f0f1806070317010b0909040f140d0513121a06190905040201200304090e03040302030f0f10090b07030b15030903040303120c17090115150f03050f06010e03 70
    0x10280d5915900201111446900c580501c201c030740b06a0300c83d9000503044a03130450700801003482580c1da00b0038541c0d4060303070200300358021135001d02d840c094803020300e0380c05241ca01c10801110800c41e0001c010b45040c0541d0004281c070642c4d9a80c810340741c02800307040a44015413403c03240158a00f24070a090384820050a114485600300c00b045400d0200e503440440c21585e60820320045603842500301400d9544a449204407001146030701361a440b8902c42c41134207a03500c5101c3c502018090003900d0040d9002000c3d5070400720b6900e461611280a2000480280191904a400813119204103005141c00c22a1170340d40744d071b81c03101c283c0061020222070f5500c07000c2070245a25041220000b548507010b007002460701d4518524014000c440300c0d800704801c4c035007007100d11a0322a501c011415101c0d400b021114026071182c941c03a40c0107040e41503203103080715080407001c01c00e141410003081501d0919591220800720012084041382c00549052001960840125200c0e40c41041d15040020001703059 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 181783426 1250 181782176 181782217
    0x70c0b07050c1009030f090b190207051f020717030301031716140c0103050c0a030b0d080309070608091501090c1b0605100b120c210711060c0f0f 64
    0x1114030f0f0000007032408456580b11410b038001c15501c071410b10490700d801d0401c02180350a02d00c1c245680e000d40d034070b50740c004284102d64185c0380307100300b2964008040203454020100c5924006105003000400c03110003610501500041d01c4104405009060803000301450459003590b50b030381720b080c0c035000c081d42c5036540038000030310308402c00105207404a11482215002c0644007050a0401c01100301050601d8500010070400d5050903045540b0384003140b40000cac602c02840c1c000b40d0300c0c0d00106070140032400084104441c41c0c0c000643c020039120151201c0c6101d50f03815010036940c481d40b4070529404080c50b80104a004a15003090350100010308100c40c3d005030044800640d04800c10080d04c80741d4a41d000e0003a6252040a41009005401401c61800c0403c0c01d0140040340c0c0a4001c00040320001109060b04181d1801c00400031001c040e040c40e542004400181120314110b0030140c2c6010f0b40d800b084150642ca0203d841992032090080d08103100d29844c080c164001003402c803481e5601a20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 181784676 1250 181783426 181783447
    0x1c0306170d020c030a03020c0f0402070b0c0309010501050d1e02060f0703050318010209010c080d090f0807020301290d020402040b030903030703140c12180717060f070c0b0705 77
    0x340c4205001104000d00c41c1020300e0704003c2c07400100e03200301c1d40240c210081c2c1c90007082e030201e0560040d00b402e4410740e100c500b092020a00a2161607405030032049014180004000440d0003075014504490090000d82d0b02c0b90700308140d181142c04c005144140c03084482841140311880390a0450004001c98240700104151010035805404110300041000040090360b045604a5641420004000714180340034140003a00a140d840000b80c074169000c40e690800c2c60454200e0748225510043c0a04903084500e80500142c00100d41240720754203080381051110fa174070003000c01c59070000e1901b00c50960440144020310000c480207980244d000c1101154000b4002c0003540205140c1000b1562072401a80050407100035290564102c8900344c18006042d0400055940844242c8102c5500362103410a039010003108540502c030b240a03005002031010716400804e0440e001d00e000b81c803a280e4030407410700c040110455003103000c140224bc101011900e80d690855203c041e5080692400c4140131 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 181785926 1250 181784676 181784699
    0xa0f0915051218060a0e1608030703081506070b0a050718120809030304030c0f120b06011101150f0906090e0d030b060d110712020f0d050c101503050c121c0306 70
    0x59464900944606c02424840c0b0100000400c0039800060b0030111403c101c0c03c1501ea220700039000d000c1001980100382c11111184541000d0f0070010002c95440300d4624041540d91411034030340801e1450400020405070052810501c0c0c50804e0b0342e0007503580c0c242130804020b1003080318250360a4406202d1104075413400c000400c041e5020300c500c40c1100d850300c88003244c68000c80d00003091408a20b02884001142c40c2d9107190414400d0034800d0441540092003801088a080050100320603c0d20009025404958100035502c0309081030100649030340c410015540c0410002895a1084004000c1d8074840d40c07041c00b0442006000f98508202c2402410981e54001c0b000c010320800010903404020514a020315899040d00103050502d55050b0a640c4130300040c1f1205050000019041000400a010000818103800c40030060b6640d0001da40c080102d590004032403c3c8248000c0c521103107461042e181b491848100106016100c2500f0a960a151150300b141410749800c000b043c0740d10f40c50b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 181787176 1250 181785926 181785931
    0x11b181e05040612030c020f010e090a0605040e1207081605031308010f06050d02090402010921020f04060305031b100617070608060a170f030a0f091505121806 70
    0x2003140140e150304040400c03007241c080d980250074031039064400700c3c0000d400c220078104c40364045455102c164100c07001603507900159000381ea03000140300c00304a0061800d60000c0280c5606880801103103030346070076150351001802d00101030440c05001c0d190018403608018100200c1c0c082804010601540e18140303140c00c000c8a44080074001c0c2c0f01400144024829203040b000100e20521665141c20003181074140049400381c040e0001a00107070959000b1081c6070020031f40400701d40c1e98005c40c2c40710170031a00d104075001c0307105690140b01600c00b45842e01880050f40d0f0040007841c5000400e01960207a5140382850702e03818000d2041c0320805400501c08c4400401140d0807803403040c04c400b0f001e035041041c07030b401c0b1106200000050098540311401120f082d5400c012180d0780b81054078060524100c921009400030b4400024030050541d4000c01048410401c4d4543c980b059485541060800071104054000102c0074040c4c2c1c00503500103a0885e4100404e03880c4010b10402c0055441d091030f404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 181788426 1250 181787176 181787219
    0xd0f02040b0703020d0905060d0c201b04060b0306060a020106080a0843060608010606020f1b01140a2c0f061e03061203120106030608011b18 62
    0x2140c80e40c14190180a9600500d003949000d524103407d0900058141c003449400e800c2c2c1555800b41803019038021817108412080c801c01c0028070722038020b80c442d550070f40d06000301200145410141140d08080c0503c4058601c003203c150305564482c030a00170700d6005442440304643d00d412000440007400e109000c507180c058040a581c1d440381555007108081c004122001901c203400f030030181d0107a0940354000e146130329015000d0040d40f50420700050640c94201510030351030194005080c1b900018081e54641c030240558840409500010a04c0301011440c5400300d0020f4540340000802d401c0104490b9003a801c4c01340803004404158071484c51014020300041104060100e050b140c140c8041b1382c006c10454045280c2542104610b41d000341c030040744841c050000c8007003801c0781d40d0307441a02c00015200c011280c544a80c00b00340c1c0c0000c170003031007120b000c030b850f01d075000c240414180100540b00064007011840014048011107035000700c01b201000309002d0007808a40509012403010541c042d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 181789676 1250 181788426 181788449
    0x80702120a0e090606090f04020f0c060c0702100c0c0e18100605010207170c04020f16061413030c15060f090603020907090315050601020a1a0a110313080d0f0204 71
    0x910b64188900d010707024000500c100020301c1030180c1aa80d11a0f44002030909039000740c1c072002013201d00f0109005580080c1d00501500c41004036640b24000a444c5550003100d4000390400c1c116400e0f030703401401d0b080103080341183c800c050105034040401e030b9411101618070164041c0040c0c0c0c0f05802c0000c01441c00d5002601c81404000569040000101a01030300b6011042660121210369444205001d014010368001c0703081111040d528055410702c2102e0220341001104c14a005002884d03461400300600e00391901041e024489104c8011506a150716007410806082d101d01000c0503071311710a0004a911202c0110b241c109a10318203005180240e00402d0844c1584104502810010314030000c000d2050010400b03e080a070010009522000000442e40c8440004034140940350f4070181075150031002c2d00d83d00e450142541840741c200d0f00401c1040500048500c501444151040e203100d071303090180880401d100c0e000a20090080c1900021016031240140090ba081948414241c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 181790926 1250 181789676 181789697
    0x924101107080d05090d14030f0703030e010204030b0a0203150325090b03030412060209100816020705060a030b030a0f0c08070e0105060f07021908010c031406030d080702120a 77
    0x24410070501c80a0480c400181c50340c481c08500003040c40c080d4400d128070070018920000148460806000907649003c0256507a0341c5030620500c010717512144044000a14088405441c40810310a031006e50740e00410340100e580700c480b022006500301515403500242e15843ca448681d40800454102d1014040320306101d540c01c0314451082c1f80540e101228040c00c00078098484d59002c41100c058809151019000018908010001380624188603811440700380c80302c00e02580044100e80f1900100c581c00c608181020012a1194410f1089682003038090009518843c0260000d010440c0082e044901c00c1744103444025160300c2030003007a6600040104207002040c024881003000e09000d920041e00c0d545040080f0342180b0038113180043d401004140340f021981e0740c216192909004446a90700c10b40c807500003a000f806001d000f000420710b13207034803541000c00102c015441044010003824020003001c00540f00c0304030051000303085001e142c080021b0180c00101812011096540b01e410320b9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 181792176 1250 181790926 181790957
    0xa1a0405071115060901031b0315020910031406040e0109170c0f0615090a0e0109050f01050109060f0519030b07180b0403050d180b04031a0114092410 66
    0x2a02691404210f24540302040403030f498070000181141d0b07000c10140c14840b007091803032144008a030002803070911404604600f00e4a240c0140845c018200d5aa1550100e507080035003c5446116444801d0072006000034074626156100e00040c0d62624008203910b00c01d80e03113000202c50005801e0f00703006004908810302000800c100080b90710fa0000078552030070704000c1e404002c0180004188035010a0001030340c00207141d04003040c5041140003d0108070a54940a5101c051004003600c6540c41c01000080d143c0b514095031044a0102e884019103c0c02e09090100800d07000d4903142e07410340c11074000030002c5d0b0440d0f241e9104113103a903500d5030181400d240354110142994024503080d1024001400411004038a0035002145420000260443c842c01e00c0480b1900d607000c0b0f110303084041400801d000700803103945541c0a480070703844442e03a03d40c80e6813030160469800a541003010240000c40031500d99082d40c00c62041c150a04038a0111000001c841c9803580d4075480000706940b0002e4001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 181793426 1250 181792176 181792183
    0x30c03060810150e010509040602070206120f04021201050c0702010c060b0607080310052403090c28120c03120c0f0f0203010f09030f140405100207061b0b0a1a04050711 74
    0x41c0c0b01c0c4d0380c114100c03540742100041034480c5c094401f81115900142803c00c41d998001280e440c1c2c54036085610700c61030103407002da0002a01319016402000c5c01c00c8102840c140611a032881070508612040c244482c4d50011070f0001012142180c070240c0d1030258042964231000940055445801e81c141d41746400805010300c2d0010381d002c1402280854801c40482c40c6d0101140100d51191301e502d503ea5079800c0c0107610b46000c18030340c20f070041280003903900404e03006040c1059880c254100b0130711440c2c2c0c403006c1e1041c00c4400f000c00752110558410600004a0b030711080c01c0d41d0040307840c01070003003075071501e594000103070000080f1120178403412a40700b141000e004000d030703900300540104a0100c260b180a42807003202c84200b020810444113000a00756000c0a482c06060040c10f0803180d203a48450103580c50781c060040740042203440314003500402440310032220301940045e103031165480d00b5480f14007030000b0104c80a481021402400b903680c5071446010302c5103400e99150314142d00c03c90940c2c0d08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 181794676 1250 181793426 181793429
    0xc100201050f01050d020f120105090d0c02060406030c050c0601061707030506090a05190509010903090e2e0305030c01090c09151503110307020601140108090c01030c0306081015 78
    0x559040004014006140d20740c2d8504545003541c0b036540e01c9040d440042d0350105070903070580c2e101c240000b044000400560000e40720b654800d0499140b184d45601c150740c40001c0c1c4a00030743c8480108014045c540c440d4000009204a900700141810000200181403c1c02600a400002c0ca0503e0b2081c3c0208420318803508201141020403e2f402c0c2030001c9500ba110090071074201a4403030b00440d510314401820007000450380d0350100010309049102034044c1459040c1a4000f410740a00440d09805010807940204007003541d40c031460a0485041c0104031407109804180014080700002058040c401070030000d20f15400060480304a1502040c00406608a014028134000c24080e40c0c0051643c542d09650380000c0440c80f031400c101d002c40141c090200481d00c4140c000c81400342d602d070002041030584030340000b100058801c540044520010850f68498103078019070180000354081c2c0d1048000c000140350218020ba00ca203a0b69190403001c0300c03080b00040c0c0e0f61051080300001505400e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 181795926 1250 181794676 181794709
    0xe0d050625020309040c020712140d0516140703080c1510050a03060f06122904030914030a080a180f05032a03070303050d18021c03031d0c 61
    0x10040702103694000d59034064110305070f0003996958042852280204440c400500c460f01816000d0130076485c0c901d8070343d1a50040207a2a100c6c10030b079610304034002c0058030b1600050b07800e2540d0b00f40e800e4450040c40300303103400b424643d40200503000c0042101c06000b05a00000000200101c01d0801c10251274020014030047c003904201200b4800c13590340b00115422641c200d01c012403a034041030085001480d03e68450303a2806003441c46072042210b002640b4405210103030403030b901041004841c2c00c400108441c0280020303007042c0c0912240140700142c1c28003e1000d03041700c40d0740c4981d80e40ca03070071a031107802d9801c00304036130030b40651568003840b14000151aa60000842c01c42c030b0000420f80da14401d122100941200751075100f00c0d064038584103c8440c3d8003c1c1110802580e0381005411540b0040f4401c0e22581002841d084080201070402c00103a405460000512400c5c0c40100c42c4068a00c0118109500d81c88030135140c44002c134000c0904030030200075082150044081001d084102020903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 181797176 1250 181795926 181795981
    0x31f090203060721050f07030e01020405090103050d02060a050f1b121f0605090307090b032b0f08090c01080a020d021201150f021b0409020303130911040b070609030e0d0506 76
    0x2069044280701c1c0c58202e407d6040200d880070b8040415806801542c110541040100300000f060010000d46441d8a00041c0c003500c0c0152580543c02003610801c40b02d81585200718404103503e900d00a030030709050100c8003c41d50611003901546680c10000b6154651407a108482d52581070b501442c1400080c043e0b81030041c81c1603a8100400d44400b03480c8503041d1456030710009030703089807810f001d4045407000c2c01c0600e01031941042404c3e00c0720040d403103509000410244000b03a20705c1c0616140c1303000b09160401000c100024100445074407074000c103201a5281c090080d0080e1940f18005044403030711111110300342d98106105014184002965203040041095410300301580101e00300e0748428180c05007140404c10b910208002c0c00030301d140250584000a000400c0da804401224241d5554500c240300118030040e4075009030145004001d803840c810041e002c00500c01d0780c4440d111520a003810003440d0ac801e000140250414442607865403c0310080000d4103100c256901e00302c441c0030b00d0f030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 181798426 1250 181797176 181797181
    0x6180b0315060a0f031209060509010e2209050c030f01020f04120507030c06020309030606012a0f0206120106030506010314130302070e0112030905040902031f09020306072105 77
    0x240c0e107020990a201d014905000820036544485a40314003500c1400e2900303448541d84d240c540100403a40d09050001a02c0100108000313102c0c204880c40600c059554100c080c00410402502d0545103400c0c00303210345039282c40b07032860301c1c0b40c0110a011030268026100300d810b440c0c2410300f481030701551039910307074410860351000b0851101070768241e403180c206950100070240f4129281031015040507112040c8071000003842c550000041c25a01c10030b030181d0f46241c80b481c0040d1502031401c9115a41e4565550a0310b0486142a102c0c88146029000818144403c0d80100b000b03030344401c80384400a0441e1006028280e0140925038200f40c0c28030b02000502030440d001d00703080d0405003020f0302860a05039001e00741442000200302402c0204c41c14800c03941c0d00c115010420041c8041140030400d5840006070501d810b10800703101d503401601506210803504030b0355400e01e0800083c1c00013240d42d044100702585082040c213102d00300c0e54540c2803503000b0f4001c40840d202c1602894910403400d2804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 181799676 1250 181798426 181798429
    0x30a08010e1b0c120f1b1f0c180311010f0503060603150303091807021608030307200607030204030311060403020a020f060403060519050c2704020d090606180b 70
    0x2c034030442d2020030009548512520260300c2c00d20300704001000c4c0b10f840210312444d4804007800280425400b042c500307407200305401c01040c0c8805244000c1a8842d0711762009401e500c4141e00400a03d00e03603444d0401011144c07031340c00c2e20038804640003510014015611203006581109603040e81a80a080403401d41c6040800207a0700e100041c4980070300880c11203091083d803410000e0360740140b80200005071000d0244804001e0f00c001b01c1700400140f1402d81041c242e41000e03018075058a410b003024620b1079a504106599002c0e8840340e220740170303034624050300d0740507010300815004400d0303580c02503a0380e461410001c007109c00114040c11030350810f10901000076000034050705c1d069410b5503840580c1b800040010803078041d503072003c3d00b800d04041c10860583c061050f804030024200c2d1040081c0d4a0700420002540242003002540c40000701240e00441440820b040c420200100b000d40381030011076181e41510f003181c0c0101c4a031600c4131010701c2160b50b00e02c060740407000b885e1010001e01a0f420b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 181800926 1250 181799676 181799701
    0xc0d081603051c1b0315090e0309060c150a180f0201050f04300209040f15060b19030203071403220b070315060f20010e030a08010e 58
    0x44180390151800419004050054098821070718004900d400e10b00008109a40038151054401e4001010034415012540c000d2080e0a14001c1c070000034414141890314103402802e00040545080c40700380146117980c0e80c0c00e4010520324009002410300030003030f182c40c0341401d50040c201601d201d00303003110f0140c04810041100b110300e4201260b00300f03c03005400180c40030320464030b40380c084c900c0020380490b010203064600c40060b100110005558043c04502c403128802c4100c3c000e602582c0c18003c41c005c81c421500101c0d00ca03000f4999848401e484082e075408840721360b401001c40d05408140144400c00d008101404840541400c1d803841c60301442c000c110010350841c0300e000040100100d1a0b8200c1184030820780406c143c0da0150840007410881c1d1190070403540030002906101b6241001c0a100c04040100d075010b0300c1318801150024803e80f900410b90b00b1101d09800310502201e5005000d01680d02246c610750003540d0755841d8144010101c00058000040343e2054900b030000400700c0300c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 181802176 1250 181800926 181800937
    0x605061204030305130203010606020c0a0b0903030a0c110d060e0d0c0c090915050f2205030a03020c012c1e2d070902030a0515030d0315030b010909050c0d08 69
    0x1480c000420b81d130b1784440c0c0c8462014082020350158644280840c80c00c0d00020700700c019443c11030382c40c8002d40d51940728038400e12603400801d415400a0003000499801800428038075403003405414905603404020940380000014280d62041d00d07010340c40c0a441e41804500307103003509890304110900a0784c84400c1c00148500c02c00403c00c2c1e48610b800107108c01c041544400c5515140b042c0a035040c41458900c5540b030581d03040013500c000300e0001d41c690030324080301012698000e0281d400c0c0010800242d0081d00300424001350f0b03549801e0f80c0350314029209500c80740a6201c0c5a40544482480f040b03c0c0f83c010303c0a007425900f503420007641c40c0c880e400641e407180d828508001c0090006078046c00b9440e800c0e54845500c21703208020300407900c3c5030141c01640c03048040301c5042006a65a8003d0301c0c0400804486581540080200e150454805d4020700b1142081060b0400040d0f0740359a45820304409038800c8070050340d01c3c1407000810100740304056801d081201c0b2410403500780e41b5003400c28482c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 181803426 1250 181802176 181802183
    0x509010c02120a0f060212062710030602120403020c03030c0705121f0506031005070806010c061514030d14040b1c05090d02060108120409020d0b0d030c05010605061204 74
    0x40540302c0349000400c01045400c0b0b9030101d507070800c500403807922201a400030608900c03210404000103000d0304085130085140c03085c4640e41464520b2004811400c83e2000d42000c40342c6010340c0380070020801e140010240311200900300c156910709400d000782044001c840b203500c2500301300000340081c0030000d40b01007a102c0844840c4008a10071100c40d18200801503032101c42d8030314043d61408100a035024a20406d01a800d44420041d901d15460842d4070441e031402c04984a2004101107500c6588020b00301881010f0004800c11088a540c90590495011507140417000004180900b0103000c0a00c8001d042d04043d240152618800762683c0500e0140c1080c0d10000f15000050110081c042003228020b22020440d50030400b8955440f2540c028403100944148000001e06040001f011880c1d40c00c0d8400c402c3c109400c140305140079501820035a030380661281812403180c0c0e02ca4060586680c441e455110842119141c0340b800d44003a507000710f101d4a0207000580100a49031010f07648181e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 181804676 1250 181803426 181803439
    0x1060923011e1a09040507110c031612020a0b031009060b0702060708070c150e1f09090b030c060313121e08090a050d050319090203030409020322060605100509010c02 73
    0x75006220b209502404e018554030030304100a01201c0c640085119208c400d80c10306845500c0342ca80145030fa50034112400d5203d07400312040400c22820200030301d501c4c8a200a2000744d007981e82311124121034009580300d1102992001b01000038061606c1a84014104000703600e040c10456000074181c2d0140c100d019018400c009015002c00070079100e0400609101d205100341400c1c55040144000303522004140581038200c100540c0400d422802102c40f102592210700c0c0c0c9050452440241920010054142c450f80c081185c26544110196200d0080e26102006103032141c201001e99803083e82d0600e05000311910b642d01e010030300120104084e415418400e080b916008500780c03803c02400d4000d825400381c403000450081d030040045010f40007021100300c403040c0c1c0b5003060003110300000d4002d600d0b038010072080252140380d070055a404160840d0a8804034000c1d00e58010012440307008850140c2d4862040c00070317203414400800c51010307901d4041c0c1040041e000280c5032403d0010b0103445102c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 181805926 1250 181804676 181804709
    0x30a0c02120d120b04021305130e15160c03050403020d1a090607090603110306090a02040e01080d02010c03090b0612030f0a26070203030408090301060923011e 70
    0x1121002108261540e500031640c600706550001003a201c44107181e0810309080008881035841c080c02139451000307448104150040c42c1c08204889d075003c2015200000b80c031140141c12248080c4032204508940c44541d100e18a4911083c0344e5044a1026a909110008a0f490b001c690f024040d40d007507d074107403564032003040320b800e02409840b00402100780844515040003000c0001183c001e0054109880f984d41507620f82906409440414020b0540e200050000505620b0301800340c54200381d00c2c2c00014034154441e00b54031036200c001d0300880c00355401104580000d50b0309104030034140da03d0380b504210350741d199940c40404180c05400e0301d04c201c40459100000c900b061007120840d035954071087c0d643c0c0e10182c4d400b51012168064000282003440c6032121701265000d1882e10410566000d140b5664031540c2d032080c1030708400c01884e0107669034240404c0720491482035020200b91040142c420b908010b410b004c4081050b046142c203182d03010001c0840700f62400e041410355540555590418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 181807176 1250 181805926 181805929
    0x30403021504061d0309010e0d110a080a05100c08060d060b062a06010b03220203060103080403110f060405040209061317060c070807030f0507060603050f07050a08030a0c02 76
    0x1003511201c100076900440d003408100242503205009414250f000d0040e034514800303242d510b80c045c2e60700c1a40812001007019420b442c1100d00c9580840c442d006480c40e009040000c0743c0402c0154000c17070040e41c01310070300741306100e41044104c0001c3c500301e005101c0400b001030010a43c1d600a030445020300c00c45c840c00c1c020021142c0100011800240c0099110076049000089000e800c080405464034a07010102d42c6040104019041c1c1e04144601403460301d619100c0035000c00030038200192860400a401c0045c0d42c10300c0418020350113240c1594a0324250309110750360400390b0554a01c81c040b0303404030001c252100d2096501715541201c0c01629030b03504401244c00e922a01030340c182112486640411203c115819290b81103088804a5030f99543c0c2002d600418803c0b00f030050410030041c400c030000a032166000801d11882d0349400b0303041c5a0540e550105941031500f04440c0c0303401480e00040030031420803269004040443e6020341c44e524140900d51a03215600c41041008850000903095 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 181808426 1250 181807176 181807183
    0x907050d050a051005010503040506220501020a0c03030c030b030601150207090f0903080c0708090f0402040e090c040e150c0d0209030a21050910080402030f070e06090105030703080d0203040302 85
    0xa03184050300500103450141d154000400d4200d58883c859260b0040c0070540d544910103030f074071407907200d002090281c4880320000741c00301504820302c490b169003c1c003103400240d0a00140c1500300d920345400100c01c21924001e0143d41a4a000004051826443d40e8183c0d5001a0382d41c11110281c040701071942e0802c400703e06207038464002d0320102e4103004650816881907407280d000c80f8001e5942c3c65140e00c4001c5108214450080c029007610418000d4008524021600e140d60310b000510042c5455501c451102e004003040340d100045821868014500c1d0400380546070b4108000300c0a00010030419161060f0b01d1005008034145e80804102210480c0566046407087c0000408803030000050386411400545a11203c000c503000010802c00140c0c00752050300c01180004041010281c90054100c61002000b401640d1500c240080d0b0364025005000b004043d00c212084180c00c0d103000010320003428010b90160340a607001010800100d490074082c0e607144400c4400c0980c4e82d0711203040c120310303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 181809676 1250 181808426 181808437
    0x40308060619020c130b0306240a0603020705010c08060312130e0c040602070602060402060910031d0109060506060c0604020904080c0d080a0c0309032102070506070c230c090705 78
    0x110320700320940c04042c64001400788402c1c402100ca07680507020426000051701c98420820350160b1010003c41c0300500589043c0c3c2e0100b140d00d103420424282e440c0060720380151580039001195002401c81e080c41004e020768070010000703084c084c13120309061010a545582004241c2c07d03d140118040c2080b9a142414030020852080c411215052400342261640d000384140d002501c1500c000152850021441512a40c0c00419060a00c40d030172080c042e908a500012000301565501000c00a042103403845c401001c204000042512451402104980000e45240d124110074407110341760320000103009034840d90640d40480192910300d8514514002c0354041348a5009000d1100c40041d4801c20480c03040702440320602245084c008141d04513084c4140c0540003071451224040c0d80c0304103040001d0a1109081c0040ca44400c2d61542418602c0c160340d1000000e188502c414103104810300c44041c03103001c1c06c3e8120414032151502c42e658644070540140900c0442c00003c220754002c3c0150384 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 181810926 1250 181809676 181809697
    0x512071a0c090916020a060c050d0c020d02070806060a090c02030c1b1e130527060405060106050f0304030e06071e021009030510150b130905011d0403080606 69
    0x10300c9401c004090380110703001145140d004044080004032010701c0301206043d441d006801600103000d1035251a4003130041d600e10700040c00b5042041c1c0410048602c240030864060384d02800584002d8540207040c950558000b01d196031081d800c0c44104d645650120084078603060b00042ca1540240c0140d045010f010404c09203070003179191001289000d607200079242c1d00110b94081c400f00360a2585d811406100bd01503400002101ca403807019030250f03000300e80101e20704100419a071029503200d8000d00c0100fa0f081d04903000701061104102c0200401405450300e4140107081454150240e41ea90000810140400a60415070040394480004440c522900b202e42c7e001220040704444c054599128001c038011a400050300b0b1000f13100c2e401c0a000d07a60b00c480548505006240c0320b501500300c03601160710295042400292680c801d00042c10080540c60442a1607458012000704689051380501c80103000d100c0346c2c1070b08043e1395461950160741800c003000350307803242400308815008052584 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 181812176 1250 181810926 181810973
    0x5030a20120406060e01060c0f0302120706020d0c08010303050d0207060f05091606030c020304030212030904140108060601090302090112061104090f110909010303050a021203070c140a051207 84
    0x18000007900141041c03046000380381c24010075503202440003101e6000d2040100142c3d042080700d0020b0742d00003410082a02a10448440355882c403410000c036800407108a480a45c0010280014552809090f988210034241103549614603100a02244105c0003200042a0300103a400104843c070343c440000700d01d0041c0304100340d1802203000c507903940b1039031000e000040308600b000070032a10034010001c11f04003550146090500e99420312406440c1c141108030240814880004a1380f501c0c82030f40c5074510000100c640d1540350002050601e0005001b8074100180300d81c0030310150300c540d12020b046903070072042c494950001c0d04144009048842ca1414400c01c001000215001d86800110300c0340c080c0141000030800307032140d803961846000b0510740c000440314010000b107030040b00a008911b0301401907800a5042c00140e20140c0d100b1074a0340b01203001d41c4004800c1c031006c030080c2100d804045006141015544e101c4a5031031056071841145010000f50b50810860f20070041c414900f408030340d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 181813426 1250 181812176 181812187
    0x30f0406031e15052e0e01091401050703080606091008010513021603050705030708220b030405120306180921070c0b070618030207030302010606050a05030a20 70
    0x10003a200101992803000d4102c88001c160011610400765140c0030a0310048106107884148140702900081c07000311802030041202005800900f2400f5004071591040c100704a07441c000b406039021500540420014800b051080766005412078400031f8050610341e220744c0d512000140f40d4480c2000a0743c1081501034521111a0803040d0181600c40c00c440d40e03a2885c0840484600300e006100c513055080d20408809400b19004900505500f406481074910b400c1a0b9190385105034000c0e00c0074400c0203019441020304100000864014000c1591030902d1802c05880c1c3c140d0302e41c01d495109051000000104001c2da444000c410034a032403070b02c2c0314101450050040754a95005c055021240781c6602c12080407002883c00700e851003588000112981424110390440d203400c0140b0468500f035440c615140d401185059103444141700f030f0700820413241585002400d40d0500da004c0b00500038180a94101107800c03800352584002c2545001401c082d040035411440d40142c0107403001c403140001c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 181814676 1250 181813426 181813439
    0x3020d0302060126070b030a0204030b0f040c0b0901020d03240b0c0f0a020d030e040207080d0209011701050d020603270709060605031e040212070603020702040506030703020609060705030f04 84
    0x641c203040f920400450850b1421901034a4940b0600000703401311500710341c1052000c80c40e4100650b4000010352801070401d030312a5a4041d20340f0058910340406040d20040000300f00e41c00601714003178082028018100410500080d50f1904c03032150082c1810703154510081011080c58030800c00c503502c0380a6000f55961025a00440c1e4020102ca81080c083e01e06550710308100050500015940581440c0c0040300c00d8504030b846850b00c2240980c480c4d02040100003140d5110050148810444c800580e80c210660024007061003107810401c04020081c01046184d0b00d0f21020811550140d4503950b6170f030317a0034030f0350410064440c000b03402143d8240f075828407008000130a40140c449030201000042d4540c90f0a03580350200301c4509260300c03814040e00d0044404550807940103803020700102c1040703034280f503210b007001702c6030b0000c500099000c00d43d1805e510701801250f800401c2070b00940707600e07801c50300070030380034401c0100d020b000300000a08181040800c01c121100601e0038041036844545415 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 181815926 1250 181814676 181814683
    0x4020f040f0207020315010b03220c06050a030b0103060b032406070507051915050a0507020a090221040f11060d0c050301030b01170a0201030b0a0905010b0705010c080f0f1003020d0302 81
    0x48050b03000f0710030300d07401b003030000301d0f000d038480c1a600408409030035592040d02c44c443c940b0045034030b50720006030303504210005070303111000784050f2070240c45254551510032401401c55035407452190400d03083c98001c12007010310350200d0760885120001901080303401c941c10414818111481764109000003001d80c00d0010102c0d2400580d0002c17100c1008441c00c1002445107407540b4041c602030710811560544d6101c1c024401801e044080c1d09100d0700b0403001d5000256000da160b4070500100390000750f408075042c03004000c1d004108040c031408002d4103068503120b4820301940001000c3ca0841c16612010b80e0310744c0140c481c80c1081d428240000c0c0b000341c40040098200b0b01c07048680b2007131040081120281d00c90f10a50784007206008000700601c5400440280c0f540d08c010542101d02000b012580c2c19041c06080e01030040300344019501c0f4423030314126084602040a920401607098140483c20750360301842d41c1c00c010f050301814965142c0d500d00000d5491281d1009503c0440240300400f01034022 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 181817176 1250 181815926 181815937
    0x100c05070f3206060103051b0d090c0e040b0604060801090507051011030a03090510060602150613020a08011503060501051209010f02030a2301060e010518030303340c0b04020f040f02 80
    0x2a40c040c030464642310882600441921494031155105002030b0354440503942c03202010b40c0c02130828141c010340d100701031600c1850030b4406032482203e2004005540c00c0902840c002840c0c10b6008000542064845684803582e90041034802e480a404100c2154461592444804882000d82e130f030740e4840c1240a0000d1412450841301270203064110000c280f51480340c40212402c3e0b0f00a800d507441114900e04500d28002c1000d0b62203190042e001c1091a824809000901d40603160301d04154142503191b0f92585501401c2c1d8101800c06406005590384901540e600c0d00c0151100705054940c10b60060151528609040e076140c401300c01c001741301c10f076900007005040040640c944226152406c82c0c030703020760900490010494a04c1c00071500c4d48a94003d000001c0804164410707064203000090559000b03480c11008003880195040030344404030040855400c0c4540c0396080c04d1403011010300002c10805006d0190f9031014000f41c15511000d0300c100d1a600020b20401c90a01d0b01240c50f402500030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 181818426 1250 181817176 181817179
    0x6030c121b0402120c07060e0601150e0d1a13050109030e090a0c0e060f04080a030903020114091f02010b032508010605090606031b0c100c05070f320606 67
    0x80c0c01041071410715200702c0d4611044007100000035640c6094145681e0f02c5030104440c01640d6030b016415240c41030040c1406014081d407015036a201d5081c0082000c00b100032004d103c1d03140c130781414001a101c00c01b50344c10107164005100c07059a61403102000c8440c1010041c1155003000d01510030181e01c61104202044c0c12200402c00b5125840810100da1450300448082200322000807550f18000000e8a0410101c00f52645000d0711220344504048501100f2000b00e05803403000e10466801a0070400980380c0310140b94117140c2c4510002d400700e0408481506101e001d1a02034085510031f40080011030780c060b040b901a010088041100c402c030b5880c1e0481111404140818041418000c8404484c00103000c1e40094031400700704103255002401010041071016940c40e000044180a000650101c202801c004008210807105513000002102c007000005c00c80100000d2040883e80c040070740050324820148801c021070400032001a80a801900043c8100000c00c0000544544034020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 181819676 1250 181818426 181818463
    0x9340306060201020903060a0b040f02040806070e190522051003020102010e030c03030408091903060b1c120f0306081603120203090112091e082218020306030c12 71
    0x3501d0500b00d080b07005030007000e0f41c036400640200d4140c02a40c0c001d480400c0c8010f1000400b0604603052000b01e03442035021080c1904680704001c11140c0083c0d440c0700e0040b013901d080305203000c003e00c03000b444281402620304c20108005070602081d01000740c65441c0905a00070007003401d01150103046080144404ca00640c20a07030b80703c00401d00030050351540ca0412000b141142c0300c503604c0603031075003100104903000703500c5203000e2118444214402e00154003402001a81c3d00f110806d100240c0181c0c2c0c041d0b51000004403607000001c0385800c084007180790034075240c021391219582c11400360225900c036890314802c501c1441d128403402da0340c0408892103a91801180c0440142c00c2e40ca0f07000c0c0141213404180ca02d40e04407608580d5030000c80006110380305568072584800c406100c500c628076400d41e00c841011810450761404501160398102d03d00049103009850101501c130355034100d035000c1c0346681e004000718080352400c020240310540c000b89144801004410160740d182d503009401e148841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 181820926 1250 181819676 181819679
    0x3170105060a020c010c05030c070f180204050d060b030a2004050a060e040201050c0114070305040b15090a090507050603042a12320309030106060e090609340306 71
    0x161140803a0190b06090f00540300c0c4241c03941c01035405242058082e00e0b5070000f086403d560312024800c942c060121401069100c80c2041041200503420820011449204020078401d0f0ba8071080510341c0154840004100307001c480700401d00f400c0d403528004110240303d171003a01c2e10239036603005440c036003800356410400e5581d81d201d8542654410312401030158200c4000c100954030a000904002540340004609580011030720700359840300f103c07280d0001e9510000d0000b0024000443c580188100c8480c0d030040c580311000408101000c1c2044505c40e960b4030720442081004e022200c001c100050170503844c0d2a260902080348240340c0080d03d030583c0e4130b40f0141c25441172410000141c5814180700c0001007120727601d0341e107204400c0240d00c0c0d0660300503a444401d00d07604403405600c182410301440d00c500d83c04c230a02d8252501d98002c982881041e0f003410120307403035021807641d015400701c0e840d003240d4032036103980c80241c088801c0b4100c04040340341b4492042005500c0f01c107069a03a5903010817485 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 181822176 1250 181820926 181820929
    0x10e090a051807051807050708030a021309050910180807050c04050601110604030c212307080d02030705040816050f1807030b01030e07080f0601051807080a090602040303170105 78
    0x424003070049550081d4030152000401000c5c1541a07406116402d00714035107140354481c400150004c964803464690006409900c540c0c00c03440c0c500007060070760130a1200d03040c16420191580c1c0c002d55003d8203950303100d5280700c1c035101100044030b1098000114541d141101e0030300c0c6463300c0c6990350481c016803c0c80302084484d44103101c1020b0b046c55140140856844958007115010000c140035500210118202c001d00944960300c07951a8410b83c0790300004241210b42c3e0070300200c0320038401950610501c14000031819040c1102d4a01c02c149000584e640e950203000d903003900840d04055254840d40c2005150180d00880c1082a14411541e0b07010f1040f4900c1000405005581302802d100102030200e408103000e030b04040740884050502007414030915000b42d01d0040d05901c4191182d0080c0d00301802240c041c44120b001d040700b60780d00e500481404501d6000c0e102d015045c0d804101000000421a5a040d07100607031480c0d0013482596200e0741c0381001080d680c0184042d13a4061402000094103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 181823426 1250 181822176 181822183
    0xb030603120a020a0209070f020d1407080f070602030112061b0e060703020f030c030d0605030c030309010507031b060c0f08040c1703040f08010608060718050f010e090a0518 76
    0x82800600900302140088011602038021109036415440f031181001d0060b035441c046140701704841d1f1380704000c0040c40d80e0000e1401b00e603140b008080c0540815101c00001c0402c1c00c484002ea0000c8001c3d0fa955522416035143e8070400070060200f45c070100000c00c100411100c00c6000e240030300c0341800300d40c000d01104001584103a04075004140c1040740c0704c07034904002014010150003070051311096041000c070103056a000071040600d5070800101007128034000d00c1100c0180100360300901c040340806d004641c3c0d9115a20002d81881004100d04003050b00c00c0714034078541d900e981000b4024110601d0040c014000c103009a07000310707036441f0803001071600c2271218034030840d0001d240200480c80c03c0041e0034840c2d82e414913480c40f03000c100808038841c0d40044442c40244422000016841c0c9041070640c10038030090052010440d9100c001038003811120045803d9817821100090305000e0a0010380da5020019650380e00060084100302144c94164420380c031aa6034600c05080b1320743c000d2402601d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 181824676 1250 181823426 181823431
    0x1090c0f0f0611160321020105010308070209041e08070b06030307020d14010906050906070f020d0c06020a110a0f0c050a03020616060e0a0f020a0e01030305030f070e060a0203130b03 80
    0x1c6074000c403000c100031449032907010081c0500340c0c1030315402c040c0c8a50710401060305400550390701e181c05684040883c14210b200402c015148000c105650660f0b0740c81101d48540a0007070300c150b00341d0006c101030052140e51080e1081544110302401c011394903010070941c10800c41503801c1c2410900060380f0341000300489074032076801407000013440300235528258540340d0601c40203140c0d9031342c0c00c030540001d04611a050080036800300600651500e0a0010480004510b070345045410a150f10405113400c151404103c80c0d1042015842c0c40f604c4000b103030500705200980c0007500c5481c0f460707410701c04000c000c120400d00508040c0c25254448080c400e080c10507120094000714100004c0880c46800081460082d11862020400c5120000d55900d42034000760280c800505100d8607208615203c4000001085558a81d210540c95510094036900000b090800860285000142e10600c240e18110201d03200410154689410702002076498001c1c04a1299000151001180c80d61062050300d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 181825926 1250 181824676 181824689
    0x80f060112180c08120c030d0f090c091505011404090e0123070e03120d09030903060f0605040b0a12150605040c17070f0207060507020d05060901090c0f 67
    0x11425250500111040018006412078482c2d8591010107003200540d01000214041c100c0f0125060600c042241400c0560103c80310480d41009a0400100e0100a6484202c83c41d500062112041e902c48000b60003000700003403c005101d1808141da680c81e43c8000c03000720b2050481c0d0220350b120401902d6a030844401807140750024032040240b0103c6400c0a000c0820402c008075401d070821905201182d04080118840302039001000f0280e98841c2e1219043d4008800074116000d4514180d443c51066111102036513440d44004421300d0300584840c00203580c4000c04004600198080790010320b1540541c510440c109003403d401842c000e40104159050000600302c0e42c600e5503288900031038002c02016030b040c0c558200292581d1240704e02c20f108041a1220110603a00d6000306420182c000c3c600070500c000007414000044e80000e0000660f83c0c6418210741d10f00c000c1c0009680038901c180028a50b00c50002009900c01c010f40144010078403032044042c0b4103484d01d00d40c0143d002e10303001d00c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 181827176 1250 181825926 181825951
    0x90605091005010503060c071104020a02240103031e030b1302030709080309060d021303061103010f120b0a0519090f050f0a0803060904060921090503010b0d0809010203220e010608 79
    0x400c0d030004280109880d27842205461000091800464241d170000541c03403000d60454540382518034030361001042c56501a1003044074030342c10359401074102404401444a4144032001d102da948d4007aa0080c0460f050042032182121501200d220203035108840c10b000140c0304510020b10048000f00380c0321074050051144d401c1c2004050500c00075003103122800c40c0102e05001c0000490403500c65a4810740812304402c3e60307581000c6c41c0034280c0c2800d5100b072520008200000d000f1900c4001000d0b080050350802088540f0b030880b0355a11140090f555079217140c0ba20500741c080001d05450b070320f074141c418006d0362b014040001445841d070400603c0940741140400019006280c4042c145901a10900b4000b032080480d4480c2520708003c01300d041207104201816001c8190840103410080034114000d000c0c6001003000f040411240d150300500141c804540071100d80c1c0240251400d0340381d00801c50404440c1c0e91124101c5a1140c43b60b000c03580802e00010844a224a070342d14407a440a03241e8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 181828426 1250 181827176 181827181
    0x3060c020d0206040204052502010509060c0421020613090b1011071e0e04030f031104180209240a110c0a0e0603070803130501020708060402030a03050c030403050109060509100501050306 82
    0x207000103098000c044040340c0b021040d044d1794160316521403c01d81e0782e89600000d218079005090a2400101600510000200303000070881c0070703103a2001011038107141811100100e00c030b20100e8420f019a09853d910740240c40808a61484180e12000b05004111640d40e14001c2c50841900c0c1301d10014503041c015080000d042c030841e840c0051a9503403098801d605000310303a4665543d590310724203880c00c500084241780300c010826450300480f80c0104018440340e24062800d4503181503c240c3c03d14001d2540e80200d00341c0401d9a07984d6050249500c1d28610702a2100d0540711426071342d00669685000c15618482c0041e2550006031100c08008060a00303c61b49003883c00030340d0604402030043e540f500c119880030500b1a41803010b01032000c1b2100d882d42e10b4a003001e00190400440e9008200c03e98015400c00015a4000600d84045030300f500304541d855134802403050841c895600050800c3d82000b44101c06c110640c1d01c0f41d03104029801c251003400c00104030360015a2000e118031030381036015601 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 181829676 1250 181828426 181828429
    0xb0603041110171006110f0717031c02041e0807090509011b020f0d2109020303040f081b03010903170c070203070308030f071b15022203060c020d02060402 68
    0x10022150302d541c10850307202d500c00d070403d0500503011200ca412842580c80b0030442690080000c1c1c50303940c0a8030203001e20886c0100000c0d95184c080c81080b2a80303000c0c20050f803103c3c0007802140c84c280010b00c1e011400c0201d00c00074502940c0103101e03007040c01101802c80040e0980004072502610b4850002c0c10de60741c07030104884041c22000d001e440c5107559071030200e40003020504410151107410b4002d409195801a46075080c030104a03080340c113001c0f81401510503503212000846c40c215186000056007101d03400032034610701580e006090030ba10250004106000c0010b9280c401800c8901c001e00c02c0840c40d0b0926080e21070032080100400c0c544c1c910b5090304007501c0d0145910001a4040c541011107640000c3d18085075a4410f0303c416070008140311086600a00260344a0581d0900e0501070341c0b411481c8851140d26100a0b19201c40e450310341d14564240e40458260131f400c0d074240d04001c1c5042e4582c8403411303050710040398011700d460b00d42e610789400413652031207400b460340141642d43c1d40c0f42c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 181830926 1250 181829676 181829689
    0xf0c090c0f0a0509090a0b03010507030903021005040317191a030c0f041121060d0201140306060d0509030a0f02070501050a0c0c03080705060403090806011203031a0a180b06030411 79
    0x50b8141c18801c040c0303e0300b405602e603190a1445401d80c9500070501c041e16074281070840d003000e040c071403c2504004124000c65000034242020903182c1000080f06d40d1a400c0890b480314080c20f088100c41300b01402d001d03180301491040e2100341e08608003040204403002a10b054030050807401d9815400150541e0210704e013503514000700c50001b40011801004038101c40d5525400311030000c10003d22540d1110350300500030078140c1c1c0104140c13401c0410710f01540010342020100381800c0552640040003031940d49450041d1864074407040018441c2e4203085280946079008210308200062448a0552034240700242940440700d044c2c455619140981c01e0440e00485078802c2641c6050f85100000300140c649001400c07000c0c05000070741001c0c24a880e000700500343c2a4003540341d543c045001444510801407624113026494100001c1803980f9501d0310608600c00c081c400d03800280b03030070005081042106126403248815004208440c1c007001088840e00069502502054103440031078524101607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 181832176 1250 181830926 181830937
    0x306070f09080a150209010e060d0c02070b040e0c03040302011107060509210a0c030915170a0507020714030c030f060714160f021801090609050106030207120f110304080f0c090c0f 79
    0x41c03414004085042300400c43d035501c00c641806140e55a00d0b03101400541c1840501c000d000b00fa0180c0e46050700c0d0000c041d21000d0040c05901103004000701041c1014000d500005d04078100f020416140d5050303091441c0109411540398803d4040c81001240c40d03440b030130003402500c48084610703091548209003100c4034841c0604c210240062103001081c10100c1e000010b00440c8140c0d00c0000721130464001140102c400b03413810360400d00306024800724a8000c61104103680c00301c03164400410400d80002e140103040010660140161030055000c4c200c0890030354400c0d415900d07201e940c00354064105684d8410390503078404c000b1002c880180010080c49030307a903032140000d140d80328011500c4d41d005500e4201380c0c0202019640e402d801c0042640b40e000c0c990040c42d49060860400c415510354034100080030145108121030003400b004011f008815080d20b481c2000d04603500c40351204000c0f03640e034030990107402c074512608180a403d49007030345d4044d11a411301c2c403a40f07003407050001c02403550743c000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 181833426 1250 181832176 181832179
    0x8030c0d1409030708030a030e07030c0b0a050d1506081608040b060102120f0c10050f040b0603071701150e0601021e010209060a1d040506012c0306070f09080a150209 73
    0x108240c40b581c0d80c08000d0721018000c2c0c140595500c64403070402800321010303001c601c2d9464000342c00410200340d06c0d00b00c45017241e081d015200d589030f440c00821121407061b030003148001c0313281055030203c1d00c05403c070501c1550143c0e143e514040c0c48280c440300e01c1d07801003500c1d00006003403103002800240b00440c010340c2008041c0111115480c0d410a00d0840c0d4209090080c1c2528002c0f49400242c1000c020904601c01601000c00c0103003003900c0c80001c5c00e00c00401c045c0000c12008081109074900700458030050402c019195645a20340c84620b01910821140030001c03001c040c00407914106045540b402008160000c0c00f074081d058541d10845070304090030890b20756003071110203540c0d00c4000c010181000d190b075800140c8884222285208410190403a014901e8502004903a0360050113550002c0e0b40704a592018000c140704811411110480542d0107003d00c405102c400e68106136031140d404859181c41e14400c2e05d40449c0d81e90703155003480c0034040c0160307200010040701296009100c000380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 181834532 1106 181833426 181833467
    0x32a15022b0302031003060f1a0f0303090907020307020405070503180c09070c140703030c0b010e060112051312110c03010506030d1103120f06040608030c0d 69
    0x100700107050a15900201185204ca00e0403000c0004590108003404682c1071000f0403070281c2558454180711801c001042211f0b4601450361a07110f00c0f003d8015030400c44200100540928080c0c5118198003041042101603259401241d00c0313100103484940d520f003041c1018000340041d1000b00c91154029002c8a00c107540c030803c8075600700c07060f4601018448400d08041e10841f408250381d20107840f90901c000f04041d0083c1e134102000e40a4034040312540e03658445ca45001004544481c0080e081d10503880802545a010b1600805103070103d099560665540c884040c03007254241c408102004910443d20f0010000c015440740158028801401c1c2036000c00d41d01c00481c0841130901a0768100721414240410995111111442c43c20f0054101500307003c10a00c029620386000c6e500b801000b06142c0c900208580c629040700b00141404906130034221050848007656812154 = true := by decide +kernel

theorem cover : BRFrame.Cov 181654676 181834532 := by
  have h0 := BRFrame.cov_init 181654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 181654676 ≤ n) (h2 : n < 181834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
