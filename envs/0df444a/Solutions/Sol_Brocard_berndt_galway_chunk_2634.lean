-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2634
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:17:26.573125+00:00
-- url     : https://prove2.me/submissions/179a42e0-56e5-4757-8e5b-0f7b8476d7c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 473561151 ≤ n < 473741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 473562401 1250 473561151 473561167
    0x6030e280c0f080d05030c0c060115080a1406040b03070801060609032f0d0611040303110c1008060f030a17030124051b0a0f0b062b02211002 62
    0x40039000001e0102c001442a000f4185010250755052a5840c607041001c0040000d103822213180507180f0381402d9800300c400740d5842e040c0240c0200c0013202000002200d1000195800c482e5000d01d980511418003942c0c1151240000c0c400a000c0002280350584036250000864100c01d129a070014082c0b942c94050300750851900d1900891840d004149510101808880ba02c400071465514020f0464030b05001c1c5820785055800b5002c04001ca040141020500009054200c00350705a40c000c00e0b801d407000442c240d01002880c09851020030700254020002a038142815818409844401030464003080c03056078800041b0215964034452103e00400104179095042140ea209428480313028041c180e05008001c0650040d0300c01242d406807443c4c0814540f90b030500c0350580c51900151261295201424400b100d09130983c0c103540120414040c01000c550855054807012240104200c42607401d5001c2200303040b030300c200400d08044000b54160401c5801c1282c0c5150342c030013250260311a008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 473563651 1250 473562401 473562413
    0xc010215041106070f06060b07020a091406040203151e010306121106031e04050c0f04060302010503060f060c031308120903030703030f32130c06030e28 67
    0x4055098101150210240000121450300000d42d21009440f041d44601c0c0354180340020802c8180040c181d00d07d462000704507004c0040c000d0059600035200403280e50307a02d217000030031195060b507064010044030010400c1440d080d0000e5802092b07242142c1c1600c1404000108850480c00c109000030504451b00d210558041c0a00e0b40140901c4454001e401d980c1d031500d81c00401c149812501c204e0000000480150384000e000000c4010b07401d81c00494038141c82c0c0036940702401c07500c241c41291401d448011600c0e00b80601000e0f01d41c1a5191800c43d1100d07810f100101c0d4081c0d504a81c06103003031110301e5001d04104040d00903030400e1204443c003107140c4609941080c005d140001011b0004100c0401e442e2030000850f440294980380010b20709070b101403070740014610000c66801c0001002400300444c0350383c03e41c529002420640d91000e6840d01a0109441c1c140c0e09801030400c2240401009818083c0d031040031061005801d860001c1c040e900382410001c400e04000042e6074107045440107000c0c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 473564901 1250 473563651 473563663
    0x6020a060e06091005090a0f03050c151605070c15120606090303080402100c050f0d1101051e0712020d05190509250305010f0203010e0c180f120f0c0102 67
    0x2001e00181001d41040e6114035190101c0388180c0341c20940703c1001c540301e100104203028000b038000d0407000200003a407034000c0251b800b03018100c100e880703034001c81509003003001d12403801501c910255503224426510203903215004007805443c82d40d19090000b80d0010b014403410304d0b21180ba55001d0368240c0c0d20410f5411110703140c0049040002011040c40003942007180f95400c142c0486c0c0781406905224030840e10b0b00700f0b8001c02011b50040c100040da4038030300080c001890310280e458443c000c0d1111841d4034200c900845407020020010544800e40004041c681904000e4a16100000340c59075101d00701a03900c220503002400356030b04100082c03a40c41005400703200d91411418040d50500d81221613488404015540044000c07084d803117810404a82d5080080d03a00000a0210501050020000350824401d0030585008100042c035003500c81400c64618070b202030080740c04403035100f00344014003400c800c07001c2e00700180d46861541d6100421610250102240c003e1a0000d444000241400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 473566151 1250 473564901 473564921
    0x121b01020301120308060d02030d030b01090603180f030513030f02011103130e09210405041b050d0f0b0301020706091101050c060c0d020f19020642040606020a06 71
    0x103403052005000c0403070324205044809400d494600300c2d03610b6983c00103441c83d0041d20003c0d85849004084659190542c0140711541001d032225650160b54100541c15070310002c100950080c2c1065002c0c0c0041c090303498071580c10f4042d1034a681006100000c0c00c0102180390416608030741e5804002c021507a1004c48600039910101c0034608005840700401c0a0320254054030100440e0346001441c11b02c8100061380c060a1300360311415a010039088021000d90080c015980034504004003000640c4402c1c0030007500b641d9654820740340c40c1c06514541d008040c10700c02200c0040e03d840a0904681c0e00b4000f408801e80100c00015a0b4802807810b1480c40300005800c5050003410b01400c5404103000c125603510851100c02a61303a0307410000010f00031310440b0b019103030740c210120340007201400511042c491660581c08a03801b031740b243d99400034603111000003050084101000c144840c0e40804c11007452000c0c5001e41c48485003060005810342c1ca441e042a070050f8030100740d21041c44414040c0703030b20b61 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 473567401 1250 473566151 473566153
    0x30c1b05150406020a02012109110a0902070834030201020d0608070501051b0c150309060c0f0a1b02040501180b0a03030827010c0f081501020d0c14121b 67
    0x40303450164040d44403103a105019051048d0f54a0100304035150040c90780b80100020010040e004003860135a0303030440c200c0764480c041c0700d1280000c06c110203540300b202d41098004410070b081144caa84084c4100c41031003190200300d6507101c0700c00d0a04d001c1000307681040e4404d40002d62540032880c030000807540b16910103007055210703010404c21a6000030440e1b03421610300442c0500047c42041252030000c4131401d01341c002c066584100c2c0460101d001840c040e82c80c90040c0c80c101e84481900b074001e03028501040340010f804101c01c5c81e02a020740f034130950740079101090482c48001500058100c6c0c01c01d0740f086400078058180303540d00307241301d1042c2d0710303204421103c00303a0b03071415524001c00340040180700010070603110100000380f1080703119084491850b04000e00801000881c01800c8100708035a10002c210184042400d4491b003d94040384d000041c0c2c020501c0d5415034400b1104829481415103101040054802c0b40c00001c1c81444101202c43e080c0c0c0e6590362078000d002800d1803e044441040b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 473568651 1250 473567401 473567407
    0x90e09120d1806050628260a050312010608010b1218161703031b091315060f0e130b06131d010f03050715050903010207050c150901050313030c1b0515 66
    0x186c810380b4030750201a1100890690908600c00010000840a0702c4603c00d081c031610750039500b04070000004104200c0c81500c1185641d903101c1d0f0079a1462000e0003040880c02d4284081d00c3c4040c1c078143c1c1c459104421150307030900380c00c11543c45802c107d94040500c404040c0d84805100b4241c1c0c407816140002106002549140380801180d5002031042c0c4a040e00e01200007026003190b6039541403001900c0c03842e1010410040080d501100207840ca00c0b880340851112380c03003403c80b035000c4d584082203503102802c0b103e040c3d00c1e0204042d00400c020815180d10000c01d101c50701c003501007403800401800c51078010803180380c0d00071203182c03040d0030507800082d007000c07580300c2480010300c0481d03080120fa0707508100420800e4202e03015a11800350200c030030307019840071400409002d000541d079108102d0aa410030201e580b549040403030b601c605507140340403030000c00104603c0c62045034500407450183c41d02030350201a03903480c85540401d082000c3c00940034008203100a20740154102040c8810f000b0180c0707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 473569901 1250 473568651 473568709
    0x80409020a1205012106090f17040303021203150904050102160501020408010e060601020d08060d02060711010e1207210501090b0a05061009060c1a010902040303090e09120d18060506 80
    0x64841c1c520a00412490b02c0f0b04001f020442a00742e07400385140d200c4400c540500c41005000c072103800510050780184140351300c113407040100c001224011450742000d2246004880c09001400c2c101900840e00343d07500704102d0b000c6000e80c4200f013440c00d104000241c1d0340c5280001c20390940c2d44803200f00000e90015018130503540e0300022031001000050410b4031031a80e60034001603000c2e0001c080a500a00009404410429076191a80340e0b00400d880ea03600b141049418442c20000c80780d4078a02c1c581c000c3e1801d1010750303454051550021480003104c51511601e90f1a2801d45050389801c4960812140a0000800d014003a0990040d4151000200f070900b0100040944485200d1042400400800d11090146005280f20003008604103004d60f56580e041d0400294424841a000500e07040404a0160011140c150041d00c80381c008000300640705d01c0e12070351540000c14605a0550700c0e400304c51030000058071402041c0c007500000415151840500c41d842c41450307000200740c885010408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 473571151 1250 473569901 473569949
    0xa0e040612050606060a1b2627060a050d0e030c01050906010e19020f0d0516020f07080705040e0a050105010b03010f0e1303110a0203060c040501030c1812080409020a120501 76
    0x800b001c0112401d8012610703030402c450401d00d50301008c20742c1c2d103603808444030950104008000b081d2012014101e45181e410340200d40a07aa030400a51000c0704011480d0b5141c0b084000d8000e444041000049055a0b55940e510b95440709040281c0d59464404000d0b040c041032024038014292202c1c240c40d06d2800203502240c601d8003e4031008415408280f5900546e0f00b4003e82c1e19207404068100724500b00144201c594050310320302c4000601c900002c4070030118020030000101e41c440d5000304081c03410001000003915559480b403113035101d02050707440824000d000d03c6009004404610340e5035418181d0886c02c5081ca40c219201d02e01411040c0203813090010070b40405283c142c584410542d403442d506904007118844003a525118000c207000b07030259218005c00840d2400d8804210b802d01405043d50010381d403e03280241010700341030070085442e4141c050f40da002c1c405c800c01c42c503007901d4950603802c07600318040100002d4041380c480a40545640304080c007409043c0e08040030303025001c501c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 473572401 1250 473571151 473571167
    0x31d070614210c0f0c07080105010b0a0e0d03022a0310060602030a031a03010905010203011707060f0c051c0f111b04111b0d120b0a0b0a0e040612050606060a 69
    0x4400d080c107680c0081d00401c40501030340c81602e444130010b0382d00c000a844c03a81e40c4002e28060391129500c1c0000016a51441208a0b110034010740c80d015074080441c410000c03d000310080680550040001e2042ca44e1228042d00225040405051004000480c2854a0110782a60803201d84e4a4413070b003030001c540c0010a45011044a00e0301045400001d001081075000d03100f141034056081c100a0700810406401446c1603a0101412a010400c007500040d42ca040038440c18000c2080d848000017894032070280d450a5602803c111640c8001103442c50803041100e01503900003811440b0318410440c0e104420707003d0304448d8001400032100d000034422107880c0f02c0c00180e2040e40e507000384100207036514083c0c800d12210048250100e03440c801c81652602c2d02400c035880042c01d0003210252005440c49103034000c1e280685046151820303c005860580d000301030510074001c1c2c150001000e590345000303c50151042120011074075143d0325150b481d006005c2e007030900c00c039800d005002205602c540c513 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 473573651 1250 473572401 473572447
    0x902070f0311070608011502070b0c0718060308040e0c09030303070305010e06030106030803060d060e0307081e0307080406050718172a040207031713020f01080403020a02040c031d070614 82
    0x10703100b00340c201f01a0503468210268030154840c000440c1c84410120003242c43d40881e0318520300440d00e001c050429204891b0b5030f0000400b01141031105028040f10000007070f17409108844154a05110ad500103451600102c1c0c4160000340c480005100c00d0003100700094000038144c00034441d1a0450380d445441d40002400da0307005110041c480030070303c00113401c030740c0313481481134203a9a684420b0304104d132140d40100c44012811544900744281401d201003107070320451042c3d8849186450301d90f030300d00203007a010b45100200000f046011680654030301200e00140481140f00c404802d1041005040640c01c42000011180c90081c4484840346002d51413203081003142c00507a81c0e01c2d145010b070380740b1055407003040c00c01502c03100304501c6c41142400a04000e000300c44004803801c1c0750004540d9802c04650040050308a00c40540060400390854441074016007008600400602008409444003038990061680b00d40d90401105400c0704000208200410f00c85141001c001c4374120780c442c203220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 473574901 1250 473573651 473573669
    0x110c0d02040e0703060501030b01050307060f080103020103051335040609050f0315010905150402090609091503030c032203230304150c0309050307121502040902070f031107060801 79
    0x2501c0d1003440b500340b041d08050340c3c2c49503040000b940c5074100144000380c00d00034117000313100e009004945079014507c55000d850640e030f1000043e030708650045002c1c2001520090005004002c1000018012007041454a4910518503040036200d001150030741045808484c2c00c0d8410042800120b03803004117207040c0d5400b1b40f00303825a12910000709290014004000d8172038007000001050000c19034118a00442c5110501c0c25a00c0840781040201d105410440c1d600c0b400401c003890041c1400400643d224070807030044920021040086421a44041450a602c1e000022506403d0050b1401c0301c0207196511605c03501d6508650741c001e040340b5070700c0324114000c40c3d0b00109400d84d00b003082214090046006031003140c003083c1c0301c0a03003941c41144044020400c01c1c0001326103410000f6a080c02ca4010414103843c1800f40c1d00c4400f1000f00d01c80103444026020400802c600140d400140030f442c0c4140c122000394002ca0070300500c00c07008010101c4094000340c0040041c01d0b4003407012415a2800c031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 473576151 1250 473574901 473574911
    0xf0f12050f01060f031101080f0a091a2805040809131b0807080906100501030b010e030a0804150507030e040f0b15130923130609060c110c0d0204 64
    0x10400364500881e4084159466007055800702c2c550b03010384140c0e02140d2140707605c0d46500d004c50006540f40041180e070001d90024500024004016075044130b0701444c0511090460806001e090200d4a80101c82c50b40d41d05100290368500240701008a107116024010100311a081a541d0f44103a403041c1c1071342c90b101c0c80b40c60206401d00c140e954010a03100210350f600c82d002c8003044c07a000c0d260391412101000400c10b41d00000315a4100807450702e1083c11840c007628011380c02c03e40190001c100007035919040128483d81a0100d0300c0800003e0f0086001e0356120340c8840c544440f2000040f04101c080040100c28042000040c0e0044450810554100d0b40841c6041528203c9001002421410790740402c00707264010403c41040010140000c10582c122400d80d20b50011a0944283c440d24500c000c031440203000350821800709a0f81c00a8070408000804952500c0e0302e402d40e048418103440407540c91040049407904555512003014040c809040c2491034200007401444882c0c1c0f010b030242d030b169 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 473577401 1250 473576151 473576153
    0x1020414010e060409020d0c0806010c050a020112110c01020316050408032b1803030c1b20090702010b01081b0d0e07120f060608030c060103060e030d0c030c020105010f0f12 76
    0xd8004d07500680591103045481e180c102c1d0442c406046520300d1100400e0703018011445552203912141d6115820000514240c0a10380c0111200103d040f481030b1001d0751181d0900604444000800b8243c00e540c0c0003689a007447d40d120030020076501c00c824103201003000f08104001003c02a0303140280c400c50440d1884800c018858440c20b100d0f010340d06000c1c900395046404181c03544400700502d001c4d036401c000005007000d042c0c80d490004440d11940300550100000003c400c0080d6081880c01c40070b0860705144c441300440c10a80090300c03400003503510740c5040e80b0b140d40e12400f419440b031501e1411100d440003012649200d8407030720304a501c1281d16a440310a000d00c0400155006207901340212412400350700f410008405031480450320503003009000611500f001081c0d038290766071003011304943d900c0c5940d4003009000140221043c2d010512080a1040036445401c1d48084c0a071400328405044040007403c4501c140c2100f40021302070b05003840b07091341264070074041d254090544801d9103a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 473578651 1250 473577401 473577409
    0x2090903120c030c0d0c0216051e040902030f1f0c080f04030c0f05061005040609020f22030210080f09070819060618061703030f070f0e030a030e100201020414010e 72
    0x14a000002e0705c0340c01c00d410300c040e060b030003d003048a10b185001c4000d505e03911401000902c480110340030b0005403000c41d10110070b2406038044010b90b48000c0481d0051107482c50030030b04002056500f003004040d0020815004022401440150070345494401c12600e4450b00d1401c004001520160410104c0306030801040500c00c02d10540d25042400c0707481c2032802000590303060b1080c1c09018000d0717043c454006040c044078001c6d81c43c520601d0390170a040414201051300540b00d060b041c824410ba440c00f001015072500200e003c0c940c039059540405510384a025200307000c3d0040c0411711160711002d0200425a0b0100d4a5482c9410316480410510480e050040c00b900590700214002600c00c10411103014003030b4000011030b44c0010104810751a103150b2542c6074003080700d2608c1d408413184002007085204807009e0044000a044c402c00c3c042242010030304d40600d81c582200420303d5803c1171251441d00d00300304d5401c00d8640c402546040c4c01d0002c3d40508404061100381403141c003148100c01581e07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 473579901 1250 473578651 473578657
    0xc030921060609050702160b090f06041a070303060e04021003020a12061404050c0a080a0504060e011a21030f0c2a040b09130b0a0b04020a0c02090903120c030c 70
    0x1e0010810310400c1c1d1a000c4030801014140c13031002c050721412400000e2051114030a40461388040780260078202c2690610405006102c005544800c00f0007001c1104204040d0324110500d03100f0111303071184501e180181c2111010f80150008880320790800006940324010442c280015103009030320381828400568411041001e62201d050a2010200c0d030b248450004210105c0121018801030b111189507821030b2213418100f00014110b00002400207403d50886d5800c2882042c0010310901806400d5003100c61803001d410030407003608440d584501d40340c00803844051028016103011042104251b94901c0750510608100a01044e001c101c80000e00860a560004801c01c0440740031090083d550401b400710702a01c100c2c07400d11103823460704000d0125486a000548456102503150300c40d0803d14a00900c070342e50b419200c0d80c4140031612a80050421000691180682a600d81c0b04001075007400030452a0715074001d101001a8908148809030044901450301c0d80d240c45845902e68944 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 473581151 1250 473579901 473579903
    0x1030e01021306020303040b0f090a03030207020f04060b270d020d06060b0c03070303140402061602032b03050105090906040b10080a08041509150e181005010206070c030921 76
    0x30b04180000500d440c2c02000462056100d0301410f5038542e84d42903100d11040c3c080c0e4007902c03c0c2c0c1c0b10702c034903000190083d4001e140046c00104600b1180029074001030a541d079a4112204140f004220106174561001020380d558030b01c006a00341900c00200810f038070307450030f4802a1080d4240007003201031042503800b803000733003001442003a5030361000c05a040d503e9000c0001140003a1504820200b0302c5011410940110f900405040c6480303440c24142030003400d0404141e03851300605099048007450340c01403180000c004065100c4074801c03044054101d82e01617001c0360156960382c00b000780903d4041146640154031040311101d68a40d6052041c80041d260082d80c0d8911800701a43c0520000101500848104a081d101c5200200343c00b11510010391242ca80049115224000030601034803040b0107520300900142c1608015078410142c000c01520707901d0109000070380c14041540e0601c41c4075841640342c2403900024400703503001082c0c602d4074400c3c511b9010f00d200011180310340454143e01c5403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 473582401 1250 473581151 473581177
    0x30d0911040216020a080d0c0b0703180c05030c01090506040e072003070605060d03120509010207080417010513082502060a0e09070f0e06030a09050a0302060403030b120c01030e0102 80
    0x30341d001c000f503c2d65810188001c0e40b14842d00c10380055600c1c0c00161801d02d00c00e090b03441c084031846542c0c41c00007044024022000317040c1c69030240c2841485480d0004859030103842901d041e00e1426041c54200640c1143c42c0d410880c03140070a00183d11040c0480b4201d489401d60f15520341d90702803081740d4044400c210204503140510010100703540000c050180c49005e000b0811071a00e07002d0820100315502d100050214204410002c9028400da0080d0762202030000050300c0e04000d0343d0ba4070040c0c1c1c859040042203000350b22035003410010074071440758495200071890398105000e444112190085150320b92404030510324050003240f810b00030b005456805003280e42c0711610f03208040c1410144030505409604540c00080700c04c1d210388070074404e6402e40d8035040450140340341800703d60340c401401107449a03140c1080b81e0000e0b20400031088514007a9020f4142400c00740f40c01403c0d642106030503885004598407820038202c0c0850f4465640340e00b401c0001d07008144c040690b0190069400003600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 473583651 1250 473582401 473582407
    0x51e01140906160c0f050103090b06090414030a030906060b030103031b03020c09090a06050705131211030a05030c010612021003150f0b1c02070308071110050c0d0f0b03030d09110402 80
    0x40006980001050f6200d0045c07440d8095100d4004500b02c46050001424038001000410b0031800e14000c440d402034021124054140644a1000c1c0765074824082000040d03074409040091041c2440354034040e01400300024a1949141c40c028440d40c1d251003d00626003401e40c8450030913000f00250001d414024150402510300b0000381500c48007544400d40d100c078100360000760894880d00459688900785012041c5071030030102040e80c8000d04035401c6458058000f880c0302e072580c04204504c0a2407140c001140c1d100b019200315404d44465602034062032840f6484100180d80d41c03c003082040511789000070701802400119600b0705040d900840382c3c021003c90224140224100600c3c4036052074410101e070f0310320913142008902c034526001d0000f41140c408250781c0da1080e109403e140c1824411100b040b0f941078000c00448a05503a5480003200025650983e0221402a14034a502145082103401a20000b29807a44030320f0107240d10007956045408108080c0146000740400702038800c41d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 473584901 1250 473583651 473583653
    0x10050c0703060207150c1b170c07030201090e0915071209050c0f0d051b36011502061906030803100e1f140d05010510051e0114090616 59
    0x83d070091209690314074000d1208080520729002d006c00018240e9505c82c4201d0440c00e500721207101d04c5208483d02036a035103109042c0f02c9450054400010b61030081c002c42441d601c0050280c4545900c29110801c2e2482000391300d501c04110362212006c20302c41c000c882c3d96001c40403544919418046245c1c9841c2164401c10312a00044c03142c60000107071a00307010113100e20708000d559118000d000307007164480003045001119208905000a5014104213044e56048121080109104042c0d281c036041503600d80702000400e541007401071254102e000c01940c1708100082d241c1d10010600c1c048400440e0008034a019641c0c0320100964210f482c0a449060040c5042c004006920035581d0140001002c00d070758200c581917101040c441c020310060628542412a03c01c4d0b210084850342c00b600d05100300000c1282806071502c0380034413002c0e0300981c03418001004101d680d0000c019145e90031484013038a590340c1141c03000404480d1040b0090700c6840240c0015014821040085414010303811400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 473586151 1250 473584901 473584913
    0x30c0c08060a0c0e030c0a0911070212011b0f080402040c18030b0f090f0d08040819050306100305090a0b1308040f0602010c0e060906031504050106050c0606091510050c0703 76
    0x2040000780e40c0389061620304c402055a42c07207220044030707801410003d04104a001e0f03130380240c566005400406003450015000100e071300b69041d400000c04d944a410743c5207802c4002d040469012400c1c02c04110705202034200802c00c08005000030301986e50b89040601660003402d01504a80d0401040103413542ca84c900003680345800d030380e0a059591a8408100b0803203003c55945904d0b25002c00501c4450307140e81c41202c0c15103000e041a83c1d01d40c1c04000780b00491203a2000c3c40c8040703032036403602e954908200d001e00414031002038442040501c0c1c501440f0008201040c1b15a070f06801680300c91150b12841d4644140004100b401440581e0000300040d4666989031b43c101202d4098008200c003130000c10058444018901da8158031100c100f0034140c1d18034002000c0c5030440b0680300304040c8116901c01217030440710b0030303005280403d0700800c61f034074104801c02c40c0c664017000c1905c4200d0103040c28112941615141c0e800c042c858810f00d100c126210303200c3c0b004e48c1e90103951103080710a099640d04240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 473587401 1250 473586151 473586161
    0x51e031b03180105090f06070503100f030605041e02030706140c100c0f092405131e050a0e0a020f0d0c0512010905060a050f0d022205010f030f030c0c08060a 69
    0x4600c95500313000016100700008107040740d044074268041c00265846203011155a07100405210702c00444003404225070b0500151500614403912000515040034201901c448100501031141c0c0030401c043c3d08010384012418004440b120304000300540c0710b03402412644c0c0100c458180c0e280c4105170340c00b5109006500207040b04074103501d5801d00d40804540c11118a9440c0c003030040702607078103001071042d5001e114403005030100070703d820f500380311003503600d2803402d40c6643c800101800003104c00084451a03240ba400202421612204010f103040e040b5403500200600c0300c8000e0386d000c5505601c07410000221410f42030880d0003000361440da00409850360b0800b400b2024000300c11000411076a00030701c40d482c01030300000e000500051400c400c0091819503100481d807c4072548070300c900143c45d1981c40780300980b14800c0040c08030450f124070200300e59050b4044000020034010030004117461180d8035070003680502c1c28090030102818070020f0300c4016400011140300e0700c2e0407c00220181c0e441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 473588651 1250 473587401 473587441
    0x92922050a1d07030b04021f0f030f060303170a02160302060106180e0402090711150a0e01020304120e060910030906060503010605010f0c17070c060f051e031b03 71
    0xb0440405950410500c0460402401007a64040041400410b000d148510350213840103084800400e400c01e4922824016014540c0109820b150505500b54241c082c84003589100740040048a280d500d0060862041d9814001c4d103c1c0040e01041d0300300041d80449000b03011114080080001030701d40250b448409204035000070b180a200e01d488492104400c50440d05201001402c42c0c41c0d9400301300c220710020b0400790510010b082c84440350322052240050245000418540381d1400c129031400341e039a090310782c94440c1d10401c10007000443c11001a40b41c50072901d4032806000e03500c00401c003140301e09a10f895010310f00701441816113600d0740084c00d507684620b1040c040c180c2c0d03510034542610f15034041c1901085042499400491042009001c1c4d0f42c090420032034044103200704422203034050f03030702034403c1c0c8810310060090035001350050804142c40c2c50010316020884280e9200040c503085a441e1b240e03000408106070518408942c110200d03291580c569a0624034403200700380e020400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 473589901 1250 473588651 473588671
    0x1a04140103050103080a0e2b050c12070b0d0f0204140f0d021f03090b010303020a14070f0603020c030d0c081b040302030318122509292205 61
    0x21805551107401824100c03580006084d0405010443c103450040c2c040796644c1d001381403043e80c034240460001100c0c11440c2c08a5640c0c0080e10b176030030300740d0805000c0030707503076010300c05c01e8080b0038140340001007010403071b41083c4041d074545000030b50420140080100c81482540003190204d2080150000414a030070110350701d190900c143c01c140600210000000f950000781c4c0350101141e00d06480c5100d001c00240d01d80040c1007a82a515a03164031000e800c1540168494000c1d4010445c0b030303001400500041000408035103140c0980b4280303500180c000c490806401007240301d90307a0703010420b84d81c10480c079038814400620400310040072440200e03407610440e0121808031b500404128112003c0c0c0380c014024620b8a000e22800c04181500d112080b038004195240403000e03d00203210000910452440c91000c40c00004902c040f0044035800038100b65144c40500d09000301e00d4101c10a40f80b6082c92144591002100001c140400c0c842900403040040100010b840d0749582c070462040c40d8040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 473591151 1250 473589901 473589929
    0x105010e0117060405060103020403020405090a02030105091515040603210f0f0801030b090c030601120b07090602031b0c031002120c04060909110f0a050915130308090a1a04 76
    0x4540c0d030700d80656400b0014101d64085202d9003803d80090b6400903040c100503140941d607601090440b074040b1221612904035248840441c6400c0c0140c5da008440c00c0020041203181075400184c00c040540340c1c00c0f9096034010f80b16000d45442d00702200860b04000290003900c0c84558685000c2040005400081d040d40d8424605031b001e50303c200c50684c01c507510002180e00750390310420001c0340600345082c2071040d0040d1600d60f580030000036018100d4080504400302061910384103020025140700180302504809000159000041d591078400070700100f01401443d0728820f00f40501085082d800d401240900940186d094004104000e600c480d10b0b46259580b40e40b90403540118010780001030061003040040c140581c20142940300802d03569840c0c1325428290003080d62094049101088000c280050107107050035585612440041203036142c0001ca011b4080301e0502e03408010f000040100350441140c46114043c8080d02c13450f510000c64002001e68421030750018031070601c1c064050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 473592401 1250 473591151 473591177
    0x60602150a0e030f0915071514040b150d17130f05150708090613031509030f1808030d090b0109150b0703030209210d02032505120304050303010501 65
    0x603205201448a9082c0074505103114149a507001c0c0d48540030655208012403403002e0300401c910001c3c6a0180300c0c403044002c00340d4518880081e1003402c2c44844d10800441c0400001ca0380c1030307141c19804000309002c2e458099400c0b0005004140e41e03240503051030030480008013601a0000103103c92283c0c1103814040590b104210b02544400d070003480d4004a0240c0c0c8071002100f9100584002c41c0b04000c00e50500048902041d400c1d04550400c0301e051003001010010301441e0401481c4030424500e082c0f21051141e24054000f484401c0d9580c01c010003035050603500811001c061003e448000140c03503039802f001c132105024240156083e02e80c04007070000042c120031144192540400308070b500241091500c1101c00d201d4002200030380515400704400038099692082c2d9140e040050b840b0810300e015001d103801d1402c140b880700743c0203543c001c20210544005040700381c10200700c450b044211136503042c6401414240109075892060f60701000f40400c0140c0480a141130b21402e0361000300350707110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 473593651 1250 473592401 473592421
    0xa150b1c021303020f0d05030a0201090204060501081608090c0d060e06130b04060f0615020f0c06040e0606090a0308070b2a18040b100306030b070509100509040f06060215 75
    0x11049000b4100321a00d008100604000c2041c0351040070040c4035092008954648904540c07141210a0040c1d41d00c1c607a44045191a00c10b5002034a02860700d6010703458422481e8101248114545040c000c9000000f8142c0004000154540c2c101a100304030901452809001a003030940070145980110400111001c00141024000b9a00040d00000a0304c0e1a00c07054000e08c89035442004454031041d0104403030300c03503001c0801031102c05d0f0f00404c103039290030882908283c501081580b081204010410100d1700c441000d40d000300301260b22076554845040000c200200f147e0005200d6800454000180000755011512031109040e9040307078155421050101034400300010040b446050144086020141e80c101c41514400fa0000032074151160000d80c115095001c400b0019860700030520400800040c00d0f07400400e50704010b0306050500f030000b4448a40d194032481082400f1648090a85d1150401c620b0703034005c90f80800c2266200c0a001351641c1d02c010122040d00c030b4040c003103071120b51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 473594901 1250 473593651 473593657
    0x2101d010c120e0d1706030114090307020a1a180604050d1a060303090603160c0803160e03060610050f040f03061407110705040b060c0d090f12050a0204050a150b1c02 73
    0x84c26918414031504581110004070409001941c0540d070350116000d0f880c3c0c0c401080780c05116164002d40d19072a85204200003c5840e421aa50704000340700504207000003c41510a098840300251035642010008141c0a02441c2e0200b58028ad910310210180405000484201881c006009489071341c4c5200381a074922841d95034a8105504000007004001714001d0761400300b855240c5a058003a07140c039001103603002a504150140c401d0141168182c5e003004032800d0005007a4040e10240c9000700029162140c41072480060020000300102107041e180c0444014000070300c0c50040b040c0d105d003850030040040c194130f849011400710115103034500803c400303c154ae4460000b0100c280c104002e001c00742c8482c0d150150003170024440c1c030603030b2182403005140290b12aa6185000c030f20340b264601445410354400750301030b616940e26030f021a1010962003103080c0c059502044a49420880400400c540d50b41d1001099403a035000c01c40400b030b00010011074000c507100c80303541d41c8070001080c01c0b44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 473596151 1250 473594901 473594923
    0xb0f07060c0320091c02191502100b0306010611070b0705010f0608011416361517190e060103051011071e0803010905060108070504030302101d010c120e 67
    0x9041128551425040c01d05038050051025014481d0247c110602400400d00ca8202a8a04056a0950342c0c110b40c100700202c54014180340500031500400b010a48075103042c01040104625040c4504c407034841000150000c0030b080713401a40d038940c00e050960090619484800351281801c100250948050083c40141c1d003941303c6107501911210440d4209500c05a140005d0003416162040c00b000950a46501a50058a01c080e880c0302402c2d046401030003038000c070000c3c0c3d065a0501440a5100011001c030517100407a07540c042d1160b402c07510307581400c20501801141410140080d00b40c000c643e40e41207034483c008540030110034520541c02c0c0d41010304da15420a005000c84800700751540501e502e4140754040e00d40d2040025203401d515940260044c030522502c88080c4030040d40d1183d03420340e214042d840c145003001d0465a000b0b4a610b0001c0315503443d20f4555000d841c6082c2c00032101205501c40381c000700640170003071030003a05181c28801028402440d149460a8450010401441132 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 473597401 1250 473596151 473596159
    0xf0927010f260c040906050105190b0703030c020a0f1b0b04080a0332030114091302040b03100f0c030b040c020c06030c190915180b0f07060c032009 65
    0x5002c6041c00442d1141000424014900c200b6200d038400361294401c2090090183c540440c4560518080c040c4000070001c0790300025a40c0081008031074500c0040d01c0e00d05505150109800750b0a590072445c002514101a0089006401d028100b1000180080c4032404540d01900d40c03540d1121042c82c2ca024610490009401040d0755000282c4610040403a10144502c9504c0517400b4140c41030142200c001c104075101e0001006009035080c5111103000c00204440000151411302c021896210003420001c0c0100d80340d2a980d00a503406010040840f20041c9041007412000000c00001d8038503d0f91003000b2130318101c071040c0181001c3c00707400641807568004081000d0504e044c440c50f0b910007001529410028840181094403621065070108115510503010604000c074840946600399054000e00000454405411807000f003090300b105c00707800001e904d542d107082211800f4450240c0081443e80307840709001150390941d1040e05400d004aa240880d00180301d010a42841070584450340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 473598651 1250 473597401 473597429
    0x409050601090f020418020a08090106210503120405010b0a0f030b04030818070914070e150a03020702131b08040302060610050f0d0902011e05040b0f0927010f 70
    0x4880d0b841d0304888003c074846040145080d9440c5682c00c0d003c41c4001084403016000510300f01841d40c0004555000740102e802040554030b499011100001c4502004140e030484152500c2841800d205687c80c40714000d40c06001417800e8038002c1d00070a0500c4100d44115844400411130300205080142500d6000702250f00070b40f01e5032130030703600450021308880029445440e022890f1600f4040c0b0300080c0540240410307075580e020b11824911500402080400260b486021446c2d0340707480200010f100290511992074100e00c904602030710030b000020b500b0908041c50440ea100c0194000d160a815811850542404541040728103d00503500540103031b100d20081040341ca030a80c01110f0351003040c10700d2860425400903840340b6810081c40b0f421415500d59007581556040388002400d602030000c020111000640080d2103401030b070088452844001c9405035a440d080740840301c3c4ca02c030080451a080402a40752008a01450601c40e00d030b000c12400050034104408070003040e1990b410421700c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 473599901 1250 473598651 473598659
    0x30607030b031b0a0302030d0206040c05060c0a0f05070b0c0c09090609030301150c020a0b1b0c0d080f13030c0303030e0d0f080a0615020c0414040206030414030706050a14060409050601 81
    0x2010707140c3c46495010680e1840000160b80420512800611a4015040c2c51500d4200401295242c0c1c4c00180141c104014594503000080340340314450341e22000714540f104503410054904480794000500b15a0002499000d0704c030300060803244401c08888418080e507428100f85c1d118035041c0c40c07a1075a544288018031120042d00b001c11151859858404c0e032140792500095041c440c44d52100f280382d800058000280380360035440c40010f04201d001003608804420210366058040c2001a08a542c003007109481040e0080881d00100070407501c0e03200741900c80c10844c030780107075602c0114003207458055450468071002c50906203603201600e84480070040c4030310036112800010880f0060913641d0f940480c40c0002220240f00c0b81040354000c102e50010701040c807089940c1010b0102e0b10260090030400140e0382c0b030080301e034040e500000c00511403c19120311032440c044c00c08010012800c04040200904241e07210080b035440503001511942c49440c28041120301e00240545241c101b000140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 473601151 1250 473599901 473599933
    0x6160c080714011103070305090a0237080708160e07050304151407140c0714030a140619021c052212020d02071202011808150402030607030b03 63
    0x200001e40181c02404000c0d400140349800c40740d114400050a83c804400d102d004d6604d4420b80368088900c00040008214070380000d1110070311200c2c0120204125141c0e00c5140454049207031031250010804c2c02d451391580e141a45854590080c4529481224260030702000a0410b480132039486600b880b030591180b070000ca0380d9502c02041900d1078840500d42c110f40d11810f204803802ca48502c0b6944082e4140004001d040c5020501d00c200500010f12040d203100d5800719210003212040f0000107040350329107011909218000741e001e840615220341c120b045032800f081441c8940600001d00c6905814030010000324064248101c0c0d0485000124080410b41584059080701003950050340c205002d050030f00000e410100206c0b01d410200c1104100300e81c04010003400f080346030000d0000e81b030a00d1040358500d60703038441c064108107544880340191058512010084c1c44034000b43d0707a8880070740141d002030041c190b904078000d120752400070746054800e00c90885208001000341c515009000550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 473602401 1250 473601151 473601157
    0x1515150703020105090a1a2706040b0916090c092607050a15030906020d020f0702030d020c1e01120c021609050106142101031401060e063613020306160c08 68
    0x144000300342d5401005100a00b148c918105201003800500c02840c040c98424a9410301810703d04180e0b10295009802d803d55550320000d4450791000001e65051022080381c085150b5481181072200381407503544480d42c014040b8007001440811075196544e100180302c00c141d030303e105100b084081d400c0d04200080c8643c2140e404180119005820080c21804d420203e9019006040212000007600c40c11805c040c09600d0721480580060480000f4042c045801100d41c401080d5104210403000c1520741c1c0a01c107800b00d40e00c001042000003640c405d1004e941c5140036079440080c090707032020000300f5001c20700078a810b94400d580c5090110424031103e0140e44c01c1b00c0d2079040da01711034840700c10050b02491501e50003103020741c0e20212520b40c40b01042c3d00711a0315400541100643c102088032a8440282c0d80749036002e1078040c201c1c0000e034a10449138051100e1503107051b0000400600c0183d0b000c1e5008032420500880942c1c03810340f05ca04c0c1c9032490412051004001c2000341d0b495201007455040030f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 473603651 1250 473602401 473602411
    0x903140106080d1d0915210604030c021903170901020c030303100f08010e03040e060d02041419050123060d11190c02031515150703020105090a1a 64
    0x85070141e100d06000742401d4007403403480002864000c940500c240807001e03240080b00305030b520100a041c130030301142200d082c409505009514a40410001c5086554501158040a0151019400c061800520362200f01d04264810450842c4120f0400c030b02031755080440e5449480c00071110980c0881c2c000c01d4200b81013071415030050301004802e5403011701c01144180d1a400518003010f0400e02a425461041d801100d0540e240c6800350000000000485041d10070048150995690300c60010345000b112010007508a4201078400440c4011610084d003e44041a04034848405009402044501c01d201d602084003202c0c5141c01151008441035082c18070181c4080d14044405221106864254a4014090800103684500c161030016102c96424152400c804040102c1c0c0000c1da84520000c0510622001040810311280310280345064110014041c4d0003121508903807101c0da9004480180c004d5400c0100041da9401d01113542e0390f4442d0310900b000d9003404260210010351500500d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 473604901 1250 473603651 473603653
    0xe100306050601020a0506160f091406031506180102010506010e0904020d0303290a050d030509041a0a08060610021513080d050a0c02010e01050c0403060902151603021903090314 78
    0x4400d8002c18411f02c1464800e40c00200401d000e80544c100081030031100008105c1004190a414801e04e500322182a0f4554001c41d01c0341d40302d03240ca140310340c040350400c2402035005400040142c0900d10340009001e07900400d80080103590740d20310042d98242e8a010266074003c0034030000030300601c2c000300d0398550140249030010b5a2403903501c0125110780c0120800d02c0461560f10820424546030340c00c0400741205850400c000003559130040c101d8003507503001c1c03881142c0341c81e03288000011029440c11089401003200072402c0d5200b00050316144260b507141c0c0901c0c0b0040d0401003003800010281206038100100c0e00c0d01c4d503900500b422509901c2002102d15003400c0140c00000c800078020341d030007000c10860004001103039160107070844801c0c1480a2182e410705c0c0c2000b40f40b0340360800b07903800c0b20380140010401e0129031002401c0c5403642c1503100d10704600410346049900481200040c228442d808454808880c404100c005501c18074005001031340c0b0000c148006101c041590401c3e0140344 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 473606151 1250 473604901 473604913
    0xd02030903090306101401020a080d0f1e1e060803091201230f090d1e0905090a0203090d03051303200a05010e010f02040f030b1308031306060e10030605060102 70
    0xb0010b420b0500c1602d00701c00ea200d442100b40501c241c41c80b003003004a00240018801080786a0f14036182e03025600b811290b20750768006881d12032141d60081e44491f01c9041c5000c25080800709100010030300c2100084c2041c1007075055180b500701501c544010394200304003d5041c0421178081000000103410207030282e548030f0310b0001c04548503120951441c031000c0c400a81c0e520300a48225004903004088030400e038040600442040e030001002e0b030108013284201d40da5926818020f4894080d954003180d0409146070030020b01010a60145010300c01c03030b5055401405040108800b59013003511030341e21545111102070000307402048079480c440c018200e480d52560910707010754181103502006503a180d440e0440891000380030302c26808106070010f803c5041904100d0b40210715602c42c0030040500d01204003140758a4009070300303030b0001035100702c00c85d41d6464001c0403510301240d1000211107031400c0200c08a0070282803c20350f44610003030407c0b00d9415146844160245c1000b40141e030550041c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 473607401 1250 473606151 473606167
    0x90c0706020c010f23010308030a15080a120c1509020a15030b09010504060e0a050408090a0f1802071e170a0201090215090112110d0204240908030d02030903 69
    0x40c0060b02c2d000358181d0000844191a01094058030300404103202e074014403c08060000b01d12000d2581940c0c0c21661480e101d540b8000a030004104940780c603840404419030004901400041001107144507136180101e150741200c05032403510035184010810300030100001c50340460703640960000f900082140c0c214903500c80c1184010714003440c4013070019850b0300508666090040c101401050241d80070855586440317203003440448040c100c001001d445201250074002d91400b51054411f00a051615041e80c440100c2820925841030b103c010040007171411042009200355500180c00040810010711482c82c1c441051403804002c44080a4103940c2c1d01140018a0140c240c00da405d070000120f4021600401c0904510418405070818041081c81c1d1141d0b4460680400c1140807030300070403000394410740c010250290306008020203201040c0011451030b00c2020801071134540c41c03803041804882100302d41c3c016650042c14400e40c02007210030307840080c96005561200d24201540d00744003035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 473608651 1250 473607401 473607413
    0x50f03010b072f0411030c12061917010e07050109090921030b03070803091f260103060f050105062b090b01030c0b07031b030203120f070e0114040302090c07 69
    0x740f120421076408044420780000c1c20301e481540c0c1c44d2014011a18194074041c81800d445104421011f080403450b1808943d00361140c5a4448001c0707504403041280948a4903406241c44c6002c05500c035070744c01d0071000317070324600003147d540e058600603540c00700417905100070131000d40000d1904584038040541f00390561840b188010a41d0880c55a0200302c6040c1d280c105072510b0b410340c00210240d0010001301400d81d41e0001145800796401d6030800282502c960190394540b0014481c00264a2041040c5610000040d03445c0c10303284551010012440d0701012402203401c240503080e0415020030210b604070b03808810b03000d200e0400c031548240c074060158401c0242c0d484264100caa540c41800180300708804801d0a0303001d0543d00041c1401d100c00c9071002882202c9074140300b868540741010f00e8080c14400e1048841004d880c4081d0190350508200c10541d07280101e610400040010040110542c0719005268a50450080c00c038103103400d5808101c1a02400340c45d041211008004010009034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 473609901 1250 473608651 473608703
    0x103022e0203030a0e0f0d111002040b09040615020c190f0b0d0c0c0f021e030105180105100807031e12050a02060f060303070f021912050706050f03010b07 68
    0x499074003454030390400019400503100900300e01403050304514010000c89074005200350200c100e46c82c040075052004100117041102003443e04040d280006004650201110020210000c05880c02c00145544031003a0b45400d0074240039100582084610f80410318201c60842e10a01400c3e4000d2096580c520131034004c0425580032441002c07000c14212132002c61071184414100d6942020041c1ca8810703501c04030000b9421100a00c1003441100032584000192000014030801070f00800c094100098218400d05010150400641c02c000020764540c00040c40d000490712620018a00c290075641e03900000078400c040c1036103c5920554000114856040c500001041d50f2105a522103040c400241400c1c0000c007010003483c0204180035464500000711041070ba042507200480215910001c0d4045110000ca280890582e6401146240c1d0a0841c004034610890844091a958200c00d85040c05026100704100c002800100b01c40e0040c4801000003a01c200b00c001c00c5840e2004054440311 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 473611151 1250 473609901 473609989
    0x25031e050d0e0705041a15070f0b010b07050d020c060a03020d090506010308070b0105010305011805041704092c030304031b0b1524040510110609060f07080609010302 73
    0x192081d201002181000d100b000100a1110340801b03035480ca1a0100b8400000c4801030620306500040310740c00e02c843c65606030303400b952103a0900c4043d40d690031400c00c150050780303090780c00d030060031580d10002d400004c1d09007454602411440c2172800c2a40141c00a4000700390092903240c0740c0107240d001030014004d4501070762003021181e444948509000440c0d10058000030f06145c07811005020001c01d034143d401c00010204400310307543c0d0300c628040c88040000c00d0041a920b802107000b040440480d00490a804040038010381c5080040b100e10305a004070880340c0c801d9800400101300420701c903898449808074822034519a40f4203d030384800c0000e00855a82d88075040416485005c0d00e0b16010340c02c0b600c8000f000c101d103603100500c0d1500c0148514802d1610070100b03d040601520300464034204002510310a0340e130a45070401d07104d92a000202d130301c2996014884000b40b82c007070103002801d01804011b05002100d0303007540d00b4441c8540848000311030000300048141d642c40441040803680d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 473612401 1250 473611151 473611153
    0x6030b07021e01200c010e0714040e0a0f0b090708191208040312200403080a0206010e0115030924060e06040c05030a0f1107030525031e050d0e 63
    0x5030112002c01060101c40c060109090390415005204a01c0000c0082a01c0302d94100d10594420300041064011724802e4810304080c09180341c0001c1c2e003040441300d0310304014299030500000241880d150349a00d00041300801d41d64642a04001103180f00c01616030104260045441c0c490f02da0340228584404c00140b01c020031807030320040041041c0c0d641c40c11a114841c1c10803176103905007958090807030000240a645041c3d520000802102800182c0140d900a1840300c0d507660b641305e05084045500007a51400588601c030000070389200c809480714100c0f801855281800420030710120045c0c00741c1d03841170f20000460710304000d14440046141320305202d00100050340d6803403c10b0109002000620140c45140b925001e1155107800c80200d80d8806103030f040014034040200301c0362004152902070302e000f842c0c010902c4020190840020692110002c0e00307960b6000d198050300b01c84154040004000074040c00303101031801c100b416400802442c60a00754280064410440102ca080c0031400c409 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 473613651 1250 473612401 473612413
    0xc0f0b0603010c0c050c09070e3601030201050406080703060e160f020d0c06050621100b1c0305070f050105070504061806021f1b090302010f0810170106030b0702 71
    0xd686024840c2c1c0fa000d02072800c0c000c054603000d4485d80d03150161120564000c201c00030001e094035200f2502c8003030040000b0003446500d00b18070858280e251842e81c08803a0000c900d00c903c43c41c00e080c8206079049913030582d03c803072416040030003c4945001c040c000105060325442c0208020f8802d0700b402e407007006000900b4246040e00e40c802410b0811404114056400c035070500301c4556802251005100e0b0408004521500c0d58008112210511b00e4981d41a018003007658a4441001c14624040c000e182c0050200c484401c041200200302c5401c440c0c1c604c1d5100c0300c00c1c40000d024601030040703a40911050280395240d9141d05080d108211070040015000003024418035410104400c1072880b2450a6030105082c21000b0395030b9a4240340204480d0f140c0c80d032141384511160422105a0451002442d032450ba030100030340041100d0004038007041c0c070703c080000c1d01441144014030032a108819103101d280781644400e039070701c03044010000d95504c9010101c013140381c1c01055405100b1076401050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 473614901 1250 473613651 473613661
    0x11070b0703030b09040b13020307090510080607080907060e0402090d0804090f020c070905191b0801090c0917010902060c06040c0e090604080f04081605010305010807061407030c0f0b 80
    0x70440740b81d040700b64400d9000e513080c4004110441000b96124401004154030100c840c00000e01e0035039558401030b0003a0400040003c00b203d0001420101c1e01100d049a0321178851600079608002d0803100c118055218001c2084070901c00c0401400450000d0401450040f400000c10901010b000045c0c6400c100001c041040305c1d01c52046442c0d00303620b840110b0422440080c030680314010361207a018400e4a032008504800f5503020550107003441070703400b000100b00300e4191340c610805420f8400c0201c0d284500000b62000c4600515040c4400c1d03545501e4014107100020301c80f4010408580c603103650750700d020700040e205c4034000c00c2030139000d00051900c1e2401c2e02d02101c58402c913070400980d40c2d40003424802c2e00c080001d0515001580500880c1d250805c0d0700c1204400c0c0143c0d480150503101c6c1c0c1144020f0582c9454050b070540b1030a9800303010680c1c840ca042030340c440c0c2500c0f40c800010310594002000e0b1400e500a020914400d00d4210200070041e101c05118520f10300080d1068039007402480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 473616151 1250 473614901 473614907
    0x907031d01140106110a0f080f070f0506070503060913170706060509060607020105030c090f150705010b061806281107080a1e0f060f0e0c190b070311070b0703 70
    0x3d00500c8545090803060540c40703120f5841d2003040b00c0042186507080041d00c2040860000d0b9650916189422612811700e0b041000c407100c000c42003510a8011400820003851142c41185c0c0b1400b4040e1440c40180c0781c186075600050b02022064410300030b02c050307184c240700c000e0000b800741074002d01002c200f1600b400308012081f00003030f200c3c0740f01d00e40c02c010800060340c21105480d4000041c1c080e139500e0795640c40100d483c201c00300710342d5a444080f640f0610540da01c3c14010300707c0217001c1e00c02003007090302d0036050008a1150309064100c2580081030a0b1051031720038028028010040d0552422504100b00340400742e0301814010007203003070f81018182500341041100018a04900100290b103034a403602c4c14030401003100c0444030601104040180410ba140d508040d56000504100e00b80c200030400000704070030030f034103005c80c09010309148151419980004918044061840d1101d14000c0c040d506940894000c40601440010035a5401000e0014500500b41c10050680ea41042d00e802 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 473617401 1250 473616151 473616191
    0x2031e070807030f1209080304030308160e0a05040c0315030b1b0a050f160c0308030717150f1314010306050a0e0606011103070b18070509040803060907031d01 70
    0x200e40e59031048a00304040b80503080406131072a0044c009010400e0000001c890054441c5c00202c03861200040c00000c155115002910848020000002141c9207500884004044030720070365128011207018401c0346480c0e8803100b0701520508001629012000c8040304001d290341c8140c4211040d0000c215103103401748c222010800c480c1c214640303031040300d64014109007d10540b0740d10481c40840c90103000c0718980100444203422841000481e6038071b1800c804198000c469120000c2d0022145800c060414010342c2c2c010b0402c00395422a02d003004080c4065035052400041e4850442f07120028403c14520903240702001d0340c4103400b202d42c110b0608100366840904034241441c585800c0756168180400c0c5650400e5003413070040c01152460940c10329500400202800786890902803140001c0c1115941c0320500c0958141c130500c51f40c480030060924411a005050300d00c041002034131a11f002e0070400e40c001043d0900042d2000c009502845a20341c0c1040340420343c0d503a80c07003a08044481250 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 473618651 1250 473617401 473617409
    0x908130522050c0405040e1c18030b04021c0803060108060a080d080c04170102071b120b060301020d061d010e06011215210b0a1a1c02031e07 62
    0x410448034001191a0444142000034031a00c9a561400b03d40d0303100007031044400403c0014010b00a0214031022140c5540111081c1a0100c0d01c103401800218010004014401e0380f600c8802c211074990b0712100b1031080d0080c4100e0303000e202c01d00d014010621042c104820140901c144c0d41d16441c1c03131000035003450f0011b0482c600c5260109020041c1c0740d000111018640c016180c280b01d01e40320b04c90b48524a0140e03401003d400160595112809071056000c0c096560246200c842140d10b4005000080d40c02c1e40588512a0106500f44002c12081c055440e001603014000614111011010740100e0388140c1040d0800ca460201c0c080c44240e2544003035001d000c000f5080103442c104000041c1070002030060500300c998940200c0c0d1024603644e5039000090000405451261103000d070700407403501c0303580030880d0076000007004a9001040c1e80700c0c52104d1603d103c803c10a11005600f0800000c000ca0041094015004011001a00d050088074003403103194440218804909005608001241d04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 473619901 1250 473618651 473618659
    0x609090606080f070f1403090109031202070b06100e0901030c030209091c030b010e0a14120d020307031101020702031225200118030308041109100506160609081305 72
    0x24081d030150380507030f219004550b03800c00300d452044000701982c00f0400f21100089100e07021003002003155042d04000c000303d110b40c1d0385581101c550111101203000d01180076000601c3c240006e205ca0030108214050018203060244070145c040d0001005a00c2c02d800807200072012440400460030a22405504080c130b002c068070210200000c0e40001c903180c0841e03081096140c0400840f0350f4000c2c00c4611034240040c185440c204d8a403466240d91004554032a4080d00d00f04181c014a00e4000c00c1002e15209668069483c102d03945d00e00300c560380d0810b0b06080484d542044100010ba40c200001b00302410345044403500ea070003052502440030340d08900345840d9404400c5680014121041c403544ca5580b89070803503d00405000104e44003500d40d8080caa0328100b048010041c0b503040103202d8490343c420444070f06c1e58075082c0c007880300c2240b0548072206602c009a000307020600e4802c0141407051941c0c400842c0e80c40554580c581981c050b41c8040c3c2d806030002507688058224071501ca800344c0700c15070b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 473621151 1250 473619901 473619917
    0x30106031a010509010f030507050f2d031302192105070801020f1204210305100504060302091341010c0c060203060406030213051807050307090b0d020a0609090606 72
    0x4002078a401b00e51062142003540e030301d00254456000b1000c1d150030b0381c101003440303403a000901035180c00f0320f61041c4188001003004540004142050044901c91860f10034095086d400c144e08bc0808411003040304441005100d0011a40300c01200e03a0642a1840d6859004400514140030b82881038603080115103900421a01c103021461501f1074120b1030540b00300024540e02e904003121000c0003c80c00401d07a80038006484806585034020b6030043d10407055000c0d160b99200d041008480c1c282c84006e40142103003000070318241070081c202006502807040144405404100740003180ea80e00c16116100078903d01421002d02030700006114034030000000c01562041c950058590105494010503c0c1d4001001514a80311030300b11070008d40c0d019003032070301151605c14010003a1400f220010b02e5410350100c0340d0080c0782d0005c1c11304103c40703001c1e0240150768144950507028000c60b0302003941040e2140782c4c0100580310144283c0050205030760700e200460400c0084000c1d9980c90340701c141081245 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 473622401 1250 473621151 473621167
    0xd150e070905010c050f07030c090e0309090402040c110d0906030f0e0604080c21071104110306011101060e0f1609080c0f13090b06030705090c0904051308030106031a0105 75
    0x15068506440e02420aa00c18510b1490300c03c6c58824001143c84003406500400810800000c00180984d8a4070b10244020f281c0c4110055480c0521016564000d1100020502509023680300350305200c400d1420303030413503502c1c007002910300000c5c204800300080502c3c00801149505d0320a42c41c4010140405002c0c1150580e0000c1c1d803010301500150030380030001912900d0308800c010f61009100700b8100541119000000c155080c1c004410540e072101c001d180740000c624040c4107160400440d192080c1c11034a0710342c011203030902441c18800c0150340e0392101051030043c03004c010b84610b1034070560418602e09508143c4c92104141348200c244100d00c1000e014070740001c182d000c00e806095a40300e0a12100c030001039000e000c9403408500310303441c0c0440c05052020040a061140c03105604462080755207100f40020100704403024540803c0900000e20980781c1780d0421071b04648910501920700c00d840d12005040c1e0300c07c5c1e000d0383c04070746d4a01d110940c0d1903001d951071094500900b0528140610 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 473623651 1250 473622401 473622407
    0x180603071511150a0e0319081504020c0c0a1208030403050d0b0405040c06092702210a0c1403070f081801060603020301050306010e1315020f0d150e07 66
    0x181e020300344018090400462a0500c51068071807050101411110031040020b004108440162104a11241008041c1c3c403065800400c54a04012851640c108600307008402c40340c8400181c885411a10240d000c00c80315610350002e81040d00c6404081c01c1d80d030103c2c404002c0620171551100301c0f003c000c810000c000c01c1d17545080d29401070701030a01c02d03940c1c0ca000300000010b0201034a8540d01c14640000d2006010f801000441038030705c2611820b0009803070380c08100b8821048207680d14184024040315503400c0913a00038000805a10016400744103541000307420145040703e801070600e665080d0421300943c070002c0d220740021008200c501e1410002c40c000c064a1654000c42c050015100225030b24802c0810b200020341c1504008006c60f54071035100601a5100f0710840388a4420310002081c0d0a401c950201e00541000c4410151881d05948101142c510841c03034540869081c0a842c5111011000521110951000000e2944085030030099040811b03009082180702880c1001800d6030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 473624901 1250 473623651 473623663
    0xf130807110402070b010608060301140c0d02090a05040c0519082403070f151116120318090204170c03062406121008010207030813030513080c180603 66
    0x5000409030038070039008000b140c0688100c0318014944400c0500001c1c2e81a408042c03180101000c80c000d0040200da011180544070301a2039a5504050400242160703482c260300030300c40c00001034400b4041d503641d45d0001b411030300419003003408a840029102110014407049804550060801c0c40c0581002120032050304c07502c103207030590701240155100f80c40e42d08000000003401900f110000058407001002140b1195101079008241020340c00900c02c5004162036030040d418140300118581ba0040d550409503d901c016403e0142d03920100618080c021850bc0c007602569401503138651a15211001c1c1655103181700c0c0e2141c20403482040309580100303446800c01030724405003007080070842006c3ca10354001040e559000c00c00042c00c200c4040c2200465208000c0c050b02040d84a6696a005090b4400c00100800241b501e0002610300707007100c000285014064030740142080d04001035065500d50a40040019510004405240385400d403510306071002410042200ca00340304002c265290 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 473626151 1250 473624901 473624903
    0x120f03010501171329190b0f18042d021309150c02010204090e0607090e010b03161b051b0409050a020424141c0305180303160602030f130807 62
    0x2800c40c18440051180d500c070a8480b400010f802174240c0c0c105145811000000001c0d1036000074288540c80220780fa043c01e1802d020340d00509100340700022401000e41c2000010411a0728a2698803908409282d8002c0a500c4504519441040014600404c6800c4a20241550f03080f0300740800384001403074000443c20640b131490740c0480c0d01c2c824000240d01901a5402c01049a41307031508981c1c5440e400607000740540850380b108010300c3e8840c40e04030a50102405a400641d9080001c154030078813820381d81703118030304038038082200e0011040c01003015100ea4009840550046010700003030502000270708150307034003210708120703800d0160384058a80681c20300c007a100d03541d81c108450a84c850701200340e403000c03809142e0f085400d4445007d0700d1640d40464030f85008500c40301d02040c1d20510050542d000304c0d016299641000e41c040104d5070f907201304d906150380500040c804d016803200d40036160070039103102e40c402580f80d26040c1c1c0e20100d40c4500601d41e290b21040106640d01188181040390511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 473627401 1250 473626151 473626163
    0x105041d031c0b041503061508030711031e03270f13181a0108011e0915020c0c01021c230702030319030507020a03021e120f030105011713 61
    0x3400b51607101c04010165041d42580080c10410079440d0041200308490607244500010442c0718005401d150460700d0718095941e4035801001024082802001406042e6000400300da6010302e0390000385c031100c40c90361100d200c0c40d400429088980c460101343e03042010b81218601c03201d041c140d00012011603424052a0151140c0444445803140c00ccd0401c818040c0114913000440940f45800320403083c2501c400303810540d240001080ca000107000f1229448204a55100800020790b003040003410700301411141a1078403003084400c0364140c005004403c3d143c00150098141600029040c12090000a210000102c58000002c0e4000b2488503018800e5220441ea40b0700943c20030b4500d1240403406075151001040c00c046004e01a1201e1a09101580d0b06000c29141c443d0141d90329401a500240580c01140490340caa640002c1e40d504000c2e1038104444d0840d00a040a00c200d40c030440d0104609100080140041e5802c043c1d03003038405001180e000c1051a0928800740706005404005181e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 473628651 1250 473627401 473627437
    0x120111030a1d030a0e03100902060f160501050903030603070e090604060b0112060806100605030f0103020105090d2906030d02151503010c080601031104080c0402070615030305030105041d03 83
    0x41d82e40100d4241000070182ca04072130781c80541003000340c02460040c1510b8403910035a054076a02c814580100c019a42d03000d0200303403c00000d110381e00b081d5000110b440b40c00c3c143d90718002000c20824042d40f40103069401c05107990742002c1c001c0c1400e101d03054201145821900d024040c81040c0002c00c1030740300350003000005011503132000403100b926007801c06040c0b0509080000c01d040700041031003401003801c101e2200e1015680d101c1590940800c41c1c11000301010503004101550060004000e40c6ca0000d008141c0c1075002e960f425490014820200001d08030303461500c1084451a14403a0400411002407010340e21841000b5659003041249480003000407001c96000e0f140e84c210b000364910000e00030300055603065001010000100da0b034900003030402d00c858a02480c4081283c0658030340101030840c600350141880301a60003500e08a800700c1c1d0f02c1e50040c4403821100c003501c000c0c40c442d5079010ba0301e5240c401000300741d84c042460311a60321030102d8150640c180010440718001c15581d01051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 473629901 1250 473628651 473628671
    0x12020f06030912030703020c07090e031801030f020f07050d0c0c03030f021002030414250306021e04081c031514121603031b11010c05071211120111030a 67
    0xc20501d1442c581100307501d0100c18000340b1501500a00803040c40d08045030000c0d82d43d14000030076032f07461722060601ca4001b00325080301d4490422040304400303818107010a0441015052000f04e0b40980c0310f0742900301000ca408410080d05100d8481d01d48003602c0c0c103000c0c0044a449203612030b0001d10009090000081d0300400d2940240024071080b0712030b05c01103440c0e00d0241081045000300b0900c070407450051741f00401e13090b081d8012482120312014505400b690035a55520020341c090010b0240622208140e400e000d0181401003000d041d00501400d03e810b00f1448592181c091500e41c0002c0c1404c10594203c1c031020000c03003108489506040301c06d545500380224021400b0038040c90228014250703e40114010710409404681c0302c2da66500202240c0410100003070340e8103000820280f001001c0c42842d41c030603903a002d150341c040c800359031038255102c01ca8482e07241040c008481642d40f090f000029880e00f6295441c0c80d4040340b000f03200000b6400200089880010f1045001c20f5840324445 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 473631151 1250 473629901 473629903
    0x70905060a020a14070f05270f04030206100605030a0b061314090705190c0f02040e1b01180504090213051906092f250c0b040b030703090f0206070c09050112020f060309 74
    0xc81449040e0423102d4850811080482d40340000715815400341c07141d030000c51001c0129140860032241e20396a200d0464032007a1429000e04050300300654030000600c103c2c20390b40040d959605c014400b55401340f60041d1008203000400d00c0007850b58080c04414400c1a600740b520300302c01e03183c2d50701c2850560701c0e04030a03140401542030841c01c003035003140ca800400290040002500f0106801501e0700300311442100c4011585200c6c1c000c00c40754520310401041056052070342115a01c184000c003064610999200048121b075030484000107031110900702400901014410039000e06110714043c48800715000c884040f0680d40c50f2200c1050710301702d808400758089403003030313030000740f001422144111280c102c00150003107440e0044e110f0328001c1500080d0005807c003102c01703c3c3c0031000228110703075521600394000c00e020070040d0707a280c4c00442100b0040e581c0000800c20607100e00846480c0904001070141205c03c142c200081903d142045940540d8030a08034031078064007155010780c0d9941d035115031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 473632401 1250 473631151 473631199
    0x9040c050f06160506010302040b0303070c21080d15120302190c052715030703030c050703150203100b03010605040b09040f0e030c01051b040b03070905060a020a14070f05 75
    0x10343c0003142d11641c2c0348204203000c281181224021503040c00303c2d9030072004142e26032180013002000e2007840701003040001260b0500009403442110f0005420308192103450302680801c0803c4c19250f61460b09000d01a10914a0405441d02c01ca4400c0c0340b00d4907540c0a540e601c807890300c44100c0c40f10030562108100400048102402d0054030113410b040d54022922242865070004100d100c2100c80000c000000050f0b0500f10300000400500742c95241d41c81c181c1d400b030b54403003042d1007600039200d000c4003140122285c692060000b42c801696460025413200102c5042d800510f00c610f010001040f2060b8002c0c1034805468003900040d030340b11a8140080c00900ca000390f0010b1507420601080285440840900862880c80001f44240da031100d4050900c0810103101800d0a0782c1440184100c04045015562040d00c505094074002d80f218001002c80c0c100388100d100680c8014200d00811084081e03401819950310007d058250a064610403014501d0144030700a42105d07103035004000c02c1c1049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 473633651 1250 473632401 473632417
    0xf1d060a0302100c06050606030f06100201090803150306070f0207090b0609030a032601030b010e0a090209010803030a270303020f160606030c08150f060307080616020c09040c050f06 80
    0x101012400000006050f01081080544441b0b2030800081d10380e00301074048074416420242c0021496039580100300c800303050b41c03101c8800c640da2040ca8400058014000318001c040c40c1c011009004007042c200752610b07500400500c100070034945040e404075000180d2005031240500040366009000f8007082d15405038400c00c981c144a0442040c0174581c112030391400300301c1c88039041c0c1c00000b208068041110420300c40181254441e00041011071907012505800c00000e41001c55001c840340c0008469a10a800480941d00300005012b2007403164441d450310b1120140a05401400e20310790301030544032005001d41407580004d81c402c42d45030010110b03401c2025807810925000154249800106200d0104403200d2060701c3c0302052401c0001890440903000c1c02c4141c0a680da221100c3c070ba412000313007a46415110360000450021820301c83c003885880348a0f07035036581d454860301c02440e03d0340001043e03025544500a000105030b81074224029600b05aa00b5414507111802203a064412910 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 473634901 1250 473633651 473633659
    0xa03020c0405070e133c0c0519080f0a0c0c39090c03052404020c1926041505160302100f0b06071506030206130306060f1d060a0302 58
    0x42c1502c401c0000343d0280a4040b000c89454440040c0303205242e0ba82044040014081c141401c68a03135484102d400000d0808008c3c94803504007503601e082c4800740921300f44901c3c0404d0382c1e00100102740041510483c0d01c1110705009204040941c0005000107440000142180c13011400c1c140b0051500d0b2001185543c3c241c1ca004c62402ca000424080c00360f090250901c06403e000f029120b081c800c0c024180100903000461100c108400070b079400d022810038099070044d809024942c0d100c0814081c00b03540c4001100316805039501c038644100040f050050000c50f110691659441ca4401c40040d9010780781940600300341c0180c224000d8034103009140c404100c0d20500031404042603800f00c0d2910145500300d205200302c002c40e84145080d0307224140525001402800b440c0f01090000c002e48800f960034010000d41161030360081805a84890001c001103c510482041001018401d00005200c4a500036160718200b0207240b008003150701d2448511403601c40407410315030343ca1210b070b401154001c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 473636151 1250 473634901 473634919
    0x30a02030a120f02010603030e04090204060b1801031d061b040e010308121612021b06040308011a09010509061b0d032009330301030f140a03020c0405070e 68
    0x4a4102100301c076800d42c1c070001442c0581a0000d90380140034603010340742d168541c210440c0c00700702440010900440107036402070f168080000d0803a8440001d1094642200d030f604d10041c04900007400350741c03440050301c10b60706400c0307a0074000c0200421240d80214002c0e01c0c107403040b00101171006060050760000841c80700745000000800c620745000303083ca46080402e1110940e5002c2c0b0200900c06034070102c40c049901d5106000c0f100e00b070396005103180340f242460318166802c03640c2454079020085070218003141b83c020040c00200d048058200d440c40fa5000349520b0709001000003469805603c0d0040d00071000800c40c7c400e0605800c28004155107007108489005a504000401038429a10101c00c1d10304211200c404c42d0741c0c502c0880e40e99004c05881400240903081951501e141d80c0007854002544803800742401170408001140210701030301d80c4480145460030004030724040e4060051b030300e6200780c01250000341c0116a40151020441300024103590b03000041e98020400316080350f0000c0c00d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 473637401 1250 473636151 473636153
    0x30504080106081c1e0f0207031b060318030c060b120114150307081908040e0412021c120507020c0d05010e1506010c0b0702330f1b0306030a02030a 65
    0x10f100c80040c0d034a84502c000483c812209583c004209802c0e6100021101d280106550181c0324006c000d08041c4100c0752880d0383e940380d80e0040c5c02c10114100e82848280020000e442d03050145821442c060101e8024100c510b40d00500641400c1d84001d112075102c801d140480c3e583c4501072415061094020b0014121003e00c4c105000c4c0103c030b065800d40c640540402c1241000101c00d01a00c000700c00412074411040c2442c018440c80340c508440900c001c100110b02c002d002e180240c0602e110344040e0018000d400400b900740b00c601d483c12046d0004101111001690220400358400350502d40001c0d00c0d1101403089050010508007940c0080c45e080c0f544041107815400303116444075420a0b41e5240070001e895815070101030f29054002180c0c3c0a507000800c04014100380c0007a80c3e4011141c411620303c00f1003214003045200d50011040001c0800d00c6040b080c010341e5440800108404044c2c54403c00c00c01c036084404c0380b50554484003100140c0c0a4070200a0b0240c0c0c42d0b002002c8802c41409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 473638651 1250 473637401 473637403
    0x160201091a100b0405010e1309061d071a09010c050a02060a1205090304120b0a06050a030f110a0308040911040512030705070608040816020d0b090303060f0319080703050408010608 79
    0x1d4400c807101e0100c8003000200c0d00d0801040d0313010385805030b49506503800c0c82401c01c46181c40004014000a588540013000a090340c4504424110403990803411010f02e0b40640d801c1c0501544030701d640c0b85090250301210f5403420200c4040300c0b03090a226461031581e081c0b007071500c502c0d50030094001d240014000c0c4c081d50032070031042c07003203107050300610481d964954050f03124001c6214081103480c4c8843c1c060005405540c00c1580b100f9440030000d24036640e040016855451580280c0344d40b024440080203200c1c00208a0080302030540340c1c10790043ca50f81e1040702c18440c500c582041d071651503600490002031f9804440080c02c0048c10740c1003122090140d2600da500100c011503c40c45414400101d1a010b181c200e4816038018a04c00c0c00c0c0312680d109001200a004030407039011040000d043c001030007020300e03a4080c083e200e0056440703140180070302c50381d1f24803081000e100c1e50144010290300320303c02d540c58079080d41c440340054072071030a494140d4141c010758000d603000d0750a005001c076071114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 473639901 1250 473638651 473638703
    0x30501051c0507141201230919020423010b0408010507021506060f0d0f090c082a0303040302031002030402030c010302090306130206090301090308060a09021216020109 74
    0x1021140c41c1410080c0140ca08001891414024010340000c142000210308005044407940c201414030710b6900f44540802d070031615584907803501c0320881112640400c1c9800e07141c543c007038203160040046051a0241b02503030800d03100001d104588800c10b208020f000c0f8000b21161200d080040d4a0950316807031035900e10341041c014a1101e41c0b82a00041b8001d10004c1d08101d01e1038519250b802d6a11801e06225040d403055020322414601000031002c0003030f80740708007817100b00c038800b001404c503001c0d1803342c0010420303521907003496014550348084100e0003100d00c50303c90941a802003040811038007207429800360b60300c0694180100e11064490040380e80066108078400c40594221845c0c60b07005500f2401504506601548500001128a084141600141800100000c0c00c02c264400081d00303460220341c0840000c2c07441401c1c0a164108241c265000c0e01201e00117509009112130500e03d400001041c102800000d1140d0f518014002c1d4000e0310f4190b0021204040d0000818044100c41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 473641151 1250 473639901 473639909
    0x224041e0e0702030936011805060604060f0c06090507060216080615040216060f0e10090809010807091a0301051216050609040b030a06050601110c10080405010912030501 75
    0x3025400002e124584040304807000b90348014140d0f00103900e800b220403151500600c5018a09030500702c0151032180c1600520700800790740d030121242c40b030310751903a00a484028100314003036201800140300080d00500309000d50f016500d0501349074041810000040d042904024000303026104e008200d0740e901189060b0309101010341116050341e545c03000c2d41d0710b02c42100c840f0100768108100240c0b500e4907800900815011680280401c0000d44440d422500085241458035035101100c40724007005008084c032070482e600e403c102c0c0d165203481d030821b035226020550741000300110000e410280294030120145c64444030002c040c0d680b184642c00680d0007030140fa40304040009000c2544c0900050840c002240310102142c22450103050000380d40241005c60741c4692209100a0f55840400c00d8450150185002140354145180050b1030350088904249179030700080821003003a1100500080383c04480d26020503030740d6850030942d0042c0380300c1d10000d045100795501070b8007071343c1c0c15004107040e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 473642401 1250 473641151 473641169
    0x212010c080f0c070308090c0307081020030a0914030d0501061b02031f11180120150601030f021305090a02070b1303020f030d050a0f090224041e 64
    0x540307500100c403080c408116000743ea410710411072840000d02c21007405412020f000201c8889681910000c1e06201c81c0e45c201c0c4009a01c51070250380705405038080c0000d521481c0c40381140423004e1624a07031091000401c0c00c02d246442e620302204000c0c000501200520314001501d403034003009540c00c005454284134880c0000c01080290501440401c400a91103500074009d0800034141014110300862a504c0013411030359038024810130b03000e0440105280c0102d81c0028101845a0303001400c881c0c185079502c60f401030341034054001402c4c0051071080c11440b2074252041580c9050041300540144034601d84c003140040380310b0b2418269001030030243d440031a00d1445c01d03965800070304100d000d03105001d4103081606001c101620354804400c10814000d2043d28280e03404041041d1440d030000c0003919600b656007003000351240b91480381006940d1440024040c81d0000d070005140c05000c1121710581312128107030b00421024000072a4010181c1c00841c1209200d03240320803008090a10a80c006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 473643651 1250 473642401 473642417
    0x20f070f0b04110f0108070e01020705030304030b09070608040f030c020a1208030403080a0203070c06111303050318040213140a0905161206050a060c03090b1b0c04051b090a030212010c 81
    0x24039000d581c100c0c2c00c0c4d0040c0c0d01c2e020250340704401203030400c603002c9265065014040f030210751034a05100500c05180507881032107680c103103884080c0ca804016403005d010040d0300c1080c032000402d5548001c0c0c046405141c0001c03100703094000240e11401540c0a46141503115511804000d0f91401941c410f5009496811040d5250340599040e4801190f680c0e0002c1c141402050025005a11040c0c20040d9035020a003001c41c2c0f80380c81209da50081d082600c4a501c007244509203086c940c0001c2d094000c080d10203508107040c0420f120102c046078040d089810406152802c1c0c1c5413510505000200010311080c000c070308000315403041742c0c1041050341c0001105400641c6d600c13400ea0241408884014045911036854607604075121111030104504000c0d43e1180003074680004005050310902c0200c140320a8414a0405480c1000910034203008508040400641c19981f030a580080160040b020307540c1d980e03510000c0c0031b068003600700a6100003e609009101801540f080340c601820b9115840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 473644901 1250 473643651 473643683
    0xb030a060e091204090c020705181602120a030b0d17040f0501030b1c021c1109070804110907030b04060e010e060a0305100903090503011a030601140d06020f070f0b04 73
    0x610340010a043d501030010400040100c074600342d010840440311441a0307100261102c000804621041c055000a5095131003400002d00491007445140c9010740002c02d0220f40c06401100301d4010050103000345641c2c0d28003132506032200c0540603401580b20340b00385100b85660b0070158842e001405440c0c1d0b140c503000710105580d40603104071200312000401207040150010714584507002c00c06012a00140310002000c1c00c1100801502d030380502c44c0046a9240c0010800d10413000300083c40c54040011034010b110202e540030307180450000051300e004c000ca80c0c3e0001e09074040c02d104200990407d01c2c1034400102c007009091181e0613642c0b515801103c42d05c5490800c04030204031301001c0c056400c51040581ca01240d41d003d001d14a101c2c1c01d01080040e5070303000080c211940c1400b09a411582c0308044034143c83e0034000c2074050a41c00034902882c00c0f6600c0032801100002c47c0040050390300040c40f2200d9034100e400d849200391311980440310524203291003556a002039a040b1884901001d07804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 473646151 1250 473644901 473644903
    0xd032a1a1f14090403020111070804060f0509180411031506030607030606140d1b020303161d211906060504020405060a0e041e1406090103080a0c0303060b030a060e09 73
    0x50115042903010425400b10b0200300401e9940c06481201590340c0c0b00325416512030100c02030040e0303a00444500d03458903c3c040000d00341c0045055070f0402c1107000c010002d2542c2d04d1410070350b5400d46c0955031038039079965450000044440d06504a501d486001c05680501c080120414400c010503400e46503103448450090381a9296801140089100203401100e0711681c0302c090034000640d90000b0443d1803c00c1c0407030faa021508035100780103800000400017020303041410310180702d51a260002c50b1909001603c0001c010018107103104000000b03501c050034075403d50000c46401128183d90481d060404124158040e880c0101d80c0e0b0b40c01c04c00700207403501d0702c0e01c00d403021580007400751445c240100a0031550701c80c0c1c003a41d03140e105030781c0d10000508104041c903904c07000020300b4000070500c0d240448080a8500203102901c01e1108900610000b00782c0400c1d100a0070090511561024071498246d002e040c0b690041d02040e100070040001040041d0403030380c129100d02d10140c3d603d44071155aa = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 473647401 1250 473646151 473646211
    0x11060c04210f03080712110301081b0f01050f2206140406050301171f02031b030606222c181b04060b0301030f020f0d032a1a 55
    0x160401e480c1110315804a4004c560503a03101805280c0a0a4490107414120071280089144400494003000602240d4000c11030a400c09403081c04a000b00d40e181000030740402482140c00381000301c040351951907005e603141554007604806c000c10480c1c5000b0903002501130b1443c0b01344000160000c032000c000800c40001c44c6d0603201d82d039075100e10716800c0243e140744d080c0d848507131081d0510480950f030b1408100702c0b41001504001140141e900e0504805000e2030340040011000345072000c02c140311040e59504c0481e801414400062103844000c0018080c0303400b0694818510071641900c401c04814240702074a144a102080040c0c5584070880c1c00c0b4410500d451110790b4643c046244654000513402c1c500100f200000c102007006511400764000c10780081e4802c0b42d202c0445c8410400b14a840344042003040401e4039911045181a00c00509001d58034428042440005a8103810182c03505000b410b8180c000907680f11000c0129003031820340008a40701d540000c964410fa6064140c8401d070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 473648651 1250 473647401 473647403
    0xf2007020103060515030105040902150c011e06050307050f06070506090a030f08011d0c1309060503011407210b060403031706030c01020d050f120c04140d081911060c0421 75
    0x101c1c030704523030900c014800281800354003681e00c0880340c28184c240c0500040200319060f01140042401800210b46441000820f200121558204101882503890001c0d07050125482150400c41c800c0e404400704c1c515200c2d4a130702034014051074041281d21100001e80c01034040c07095803050055150200c040356040b03c2801008250070300602480200300b1030000b0036402c40881c0005600e08090042c5083d905d6225901407034034584c441604000c0c0e07180070f01c035104410515440e807140a250034840100038050005582c6010f101918140300d2000c2d007984080c2542c0405491a50f42d90385030708011307003950030851801020600c500c001038258180852111030f0341c401070f0003d080c8041c9440c03003500c0340c0d002000890061201480040d0744082e406280c1c074003940f842000d40350f030303103080c02120f4923400c0c03042c4041401501051303111400607446104540090b240342d030b03800d000041901d200b21482000211820030900c80d40041c4480411014020f100700c61310040910510040c2103403400940f80c000c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 473649901 1250 473648651 473648689
    0xc0c091802060703030b03011d160605090607030e0415051306060206010b0a020a0b0112120806060d0b0d06140a29040c1112120705090d02040f20070201030605 70
    0x1401400c1030b40207031400a10070305001c514a29503030042421030b411100044900003c076a007803440c0d0780d0240b01e500581c146840380000928206400a0716521512a80500a0704001228001d15200c2c8003111070303005c402801400300c65800700041604c00b95500a451061880f010380a2601c60688038041c115401c07078000e090706030718120b803084950300440c44501c158000d450403040051621505140602292074481106c43c046003800350640c645845224144202503003801450f0340d82405444010240c1c803404039200c80780c0ba000c695550074540000300211308242c070300105a00c10040301c0d403240903e40000c110540f49142545d00d07400700c4901580244440001c0d140d0242400d130043d02030301c242410800c01d400c0021084501e441c15440301c2c0310349241e0100d09101201480f014150300f1540906e0a0b9061481441c002905c0d419203e1000388603690f00c14100d4200741150b0482c94955003040c1c00391100114080e40d03a10b180e440081c040b030000b403501801081d1480c0c5071142e002809400c2c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 473651151 1250 473649901 473649941
    0x5091501021b0a0f081e03120c0a110607031d07050d020402090f061219090b0f04052e0507020105040f0b13020904050a0606060207050d031b05030a0c0c09 68
    0x221a04450540b214001900100425404070710144d0044100c3d0061182e41e0003030040e405d10419110149051650540043d041007013002c041d01c04008040f1f4020621040f1a50307141e100e1041695101c3c1d42580502c0c2d5409190100031026415a00c125544002c3d102a480860841c02d04280c503106240100703540200e4a90544000d07041540c003400800e000603250310810454000041c20f9500101c000d0100105280c081241801400c19000c00ca00d0907030b90184890400c136526034102450007003007140c0c8041801d0005044c40300c200b000790000c0502510103d44503050b26a0303445030494001c0501c8206083c4408190360600c14405e2901c15904540e152154131150390302d410008034080c01c2d80c040000b0706400c01025948111009026520030740040c0002c1c03030503240800980302e0541c00b10b402e54100c08004c004c541c032020207102e850359161a00749101129003580400d2001c1d041400741261001240d07403204980c000d4228281b00c1d01400000007074941c0c54002400740e480003184400c8202c801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 473652401 1250 473651151 473651173
    0x108030a080c0408030c0d1b0c1206241d0601020703030c03030902060a03060512070b0f07020a0f0620060601020d030c1709011a010e0f100c050a06060509150102 71
    0x1070059260841c00880b0141c1c94150703110051480c54002030300c40c6526400c03200305800355907041202100c800114011220030000c40e9240d00301c0b401000c1c4500b90820181030050700401c04107078400030740d11602060a0049007400d4043d030629560a02070a840035200c5642c0455129809205912880341603004003402d5041d994111184c0450f144110245038940490100503030b507200140c00d0682ca03d640016035940360004000c10f0941c000340785003041d004440280704944800044410800003a05030035aa0280341c400b00d200c07429143c0c80303040551125400456500da02815200d80b0013101c0d204116880141a0714648507801510390700c0c056800400710500003402074100044e80d580301d060001030842085606440b42c2c0b03048400d4640e0307964960226800008400460006001c2860300d80c1c0c0300b401d40700c04200c00000d5548c14502c0f500c0241d80c40500d0601c02c0611082d103640c05015210201c00902e0107002500072030141510030581e4070005400c00d00c810b202440c054105038010286041d071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 473653651 1250 473652401 473652407
    0x50c0a03180f170f030702010c0f080907030b06030304030c03050c040516050d1d0102031005100203040e0114040e0319090b031306050711010e0703060f022107020c040c020d080a050108030a 83
    0xf500004048880300f130041d165403050080245101300e82c1d03500041600038203090014900310b04008a2010712401800340b0483c42e00025400301502c4d4049484030351500c4020019185001e140d00003044107104810200420a0124441c0e0041c0700c20748090001340c0350315000d40082c1c1059005400060814007a100c5041b280b074010545140390303c4051001c0c4548805040d003607a2085417007000c00c0746c43c1041041a41866840c0d02900b0461748003440c185810081d9107100044180301d254500c1e65200611801039880c1d5020000485a0404036070f0746034441d0144241c010500c104801c08105180000280710303070030303104580c0700705120901c02c001c602d11969040000c09006c0d21000820440340502c10b1641d03000d21410507040d03405402400682d1a6203041016983d84944107070740c2500600015600160260340812900940821700000795602c106c00c9103407080c1c0c04085a403060919441301800c3d40c000c039110f4201d1000742c1c0c1e54000c0d681c039040c01c1c03c02c0d18428420750070250310401c44200d1082c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 473654901 1250 473653651 473653673
    0x11a0d0816030509090c090a15230909040309030b070c0209040305071a010b0d0501050a030804150302070f0825031b080c070e0106021603050a020f13050c0a03180f 72
    0x8403e05119041410700c0c008118083c104130703200a01d44000040e254040d00d848202e6800402c9802e820405100e59034000601e80e015442250540900076110708008041c144190b903c40348003d40018200e02d0a03040043c2a203180380300507585d2545507130114003540c3c1710315110348180c0d40191007404d030764850390303011a49680004816124081905003e10b95800344000c4a07008040d000009a11411580c4600c2c1c1191010380c031861040f940840700700000303140f1200307850843c1c0320128032491540c0c100c44254083d100f00c1030010410401170448608000b283d5010b003060381a2606081103200f01d5160202040c24040e9002d80031401418030400c11a010014942107180329020640c101001e0340c0d4118600a00340e0041050b201b0391100501a0075410440f42d1a0210b0078400c440034246591601030712072051070701c0030340210001840903040b504c8602c00740418200207030f0200241d18000c255421a904080c041c0c2001a05092010325440b00d5803001c0080d20750041c0b0031242115080e074581400389 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 473656151 1250 473654901 473654903
    0x40e090a0f03020f0c0904020f04020310120602072904120e0909010509010b0d1203201206010305070507020a0b1b07090b0901061707030b030102040b0705011a0d0816 73
    0x12140400c00000035690101c03440c501d511940042c80c2e40c0007690603072803d003580308640c0f901400502003040050780da0500402c00c03400040e500181d4a032074207007070984001c816800a0541c089101d4100c1d040140503070007400d0090003010103100c0c281c034001d62000030344083d488000d0380841610100e0040b03200d400d6500c90b11040c07400c002c2e00244512000c110341242c1100c8101315650b42d1400c20910f42001e0090b14410303030701122044000503055a0f54000342004a40c290101513860503a0310300c80700b8804589002c291151001629981b0320b0502120108080321903600007810000402c00c00d901132015120a0f40d8000c00445d4880d081481075200b541100409243c410080e05c15503130501010311030307000601b1001001241014000f4180404008180d21a500f0400c40000c0310401c000c40984040e0051694a00441d0145034040024013900880e0041480184000340c48000c208055210654402c2e24640304600380200c0b00412007011000034000c0d01c1e5000400c82e01f1705807010404002c3c101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 473657401 1250 473656151 473656153
    0x6080d0e040f0c05070606090b030a110d080301270c050403030e04020409060b0d05150d0204051003020411090321030601080403030f050703450204020d2a0201060b040e09 75
    0x80b0922540714050710f01c10880b01010a00001c1c400c402e202c1540a05009460b0701d02044c4889004280803d50ba000c1c01c15020f42401c1e6082001002079883d950100d1245400101e12a22075840305980c06071000800c00d81c00101c018504400c0b03140125024a00c0132986940b04c00c0c1c101403940d142951070f504507100740382e4001d40c01c00010900e5011841500064101c0c496100e03180c04036055180101c5501900908038542c0343c644040310340d41d0308114009025410f0760045180d4950a005102d2008240c100075485414040ca1250914400026201e110700480864505100110400c0c0007020701079015100e006040000640c254010134107290014841d2500090401060164804550052300c00b10002901c804c4d08117921b0310018610159510442c81d000e0584584090601000803070440e6465805521400e80055542d55415108941090300c0288402d01c80c0e0b4503c11500e11184a903618140c4c2e030400d00206040c81403040b0003c1d280e92001c610301d41418040f6a80740030700000c21040709 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 473658651 1250 473657401 473657411
    0x60a0f0e0619020706020118080c0c1e0a060507082a010204030503040311010e0f100215010e180327280302010e100c12020a0b09030a0201050a06080d0e04 68
    0x21544440009158920790b8038031540241d01004002810204194821030441e0304007440d4501100414203070200850b80900d080f41c0d81c0e400d104150742410903100c0781c55804070031500004005e207110322054020203811202c0000640e00d4a0042d5042c0c058101c01400d410018802c0084038000c0e0780c0060307030f6418440298144074072000e50403800daa00c2600f0442e0143c0000c60700300100314110384134001e400000d0030580803103110a00804d40b9481406851485082c0328080b84942500900c2120008002e03c03500c00215030716020004007011007950906040307a40090860781c1c00c84080281c80d45c0310702040c640015810a49500d407000c41ea10f800480d40206580d8415001d0b005110f8944034031110340c01c001da0b200385540000b4003414101003509001303005214107401401e50240c2c40d404120313404900c507100d14501c440202d00d03180c0e8010b03001381140c480c2000d0000e0448000090180f881042c1d00911042d982c820b808802e554442c410071600d81d000d509841c2c030140c00b60385012120000a000020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 473659901 1250 473658651 473658677
    0x6040b040603020603040822030317040804051804140f100c090b0309060a0509031c1e021b010c09050906010c0203120f0a0216150503090c030a2f060a0f 67
    0xd110345c0141c0302103c0301000040c61418880300f411000001c2540807904082062035a03c0c06031542c4000f0022429640d584c0c000101007095802c180e4000c1c1c5005031071142c017800005114661a030040e681582e001c0000f8042d8a9007400c0007844840f524042805020310070790314180113003d004001c90140c2446443c2c0c0b004112905141c1c051486903120500a01d41810700c40c0e1084100c0e107000d0030385441c6400400c507188030b6000184140c03000c580c040c000003448034028020b40c1956010a03142001d00d0f0b000207456656101032805080c24440303420700802c0341e90951001940c1980c2e00d40301b019004094207000480c0d544c004c11100c0e00042c006415103005c0400f07032140036580e91000e05594401e00300032501855495040103841c0801010400c1822540d04000106541c00e07001c0544400f000070000c0010007440061103254110303500542140ca100b0740f036107030000c996101801c0711038084107076805001e682c2c814080900e51922000c0c1c031251408501e01002c0712103808103103d443c188040e07094104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 473661151 1250 473659901 473659909
    0x10f051c1e060c0e03031b010204030f030c03080114030a060c0201021635220305030307020303041515050405090f0715031b02031801120f0e070501051206040b04060302 74
    0x11005640460003034112100d6032411030100c402150b000707004c1010410075000c56480000445003092203100c0c5482040b03c0340787c00c6502911854000500c401850f00d0040201030300505010302c41c5220f900c5406150313072140d2504203140c900c102d060780d242e40b10b8042c94000c00c00e0343e070000300c80411610000d4a42031403109400c080410745002190450500c8e4036002146020180001c070109001288010300000c03002c0341c110038012601004012002040803c1440c9140d0b59058015580081666160710f032400019440360402c8900b83c0700e014407e5901e1060804a00c20000d080d040d0890320714880e42000103000003828020a419010700c91506264103402042012100070862020501106900348030010700750350610941d1034209a0006103483e9583d00481a00e550217900c449450207083c00302c00403588c022440c2c590000440c031b00f00600c40b45880c035801c215090b20180d81140d004a940e4001103844d440b40e0007003060680105c001284103403905400560141038002c1c00131480d1900c0e03400007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 473662401 1250 473661151 473661173
    0x52b140904150612020c0303040b1f0e01090606110616110a0f050c030a12050304051203010e090c010807140304080d0618052a0318031812010203010f051c 68
    0x840d012401d007000b0030810394003804c01d000050f210b000541c2031440300f22401da500d0002030300040c50346c103152001984001402403e10090308440300c2c5070320140d580721400500d40d00e0030300400d0903003810401c011990074003511040c4080c84c91a00144416030701d94032204000c0b051a502001040764442070a1030343c2d042004400e40081c0102c4030320500724800e1601c0ca15003140b88124a0181d000038601c0d40201e10400c980900040700f40c14480e81d60f5859207090b0741407000340c0c4100c6d550a8070103c00410640100c181180c03103085004203c0700d01d44248001503500792002c0b1082000240c81070400d00c2c2954000c000755800521800280d414140078400400648003550409030f505007800c404075110300140e000300e681106008a0181a102c0c00144043c50030920f4603a45031420300003c0443c441c1042207001051108100042d0394840c3d00c0c81348044908041801d03458071070029050042030400d070600c00c6a04031100c0740c2805c041e8034600801d2246054455464490541e9132840407000b140f401a12 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 473663651 1250 473662401 473662421
    0x16090312020c040c120b0a0e0103080f1303060b01021911010c081306210507020a0609020303090306100f080331150302030406060801020306090402010305060f030a050703052b140904 80
    0x20601c20a121000e000c1c1104d1b80020036034070424200804000000710b4140e2541565046041c45948007a00503142a80c6d1107000b102c40382001c8031010020502240c0c0d4003108140009a0079078054448942007643c08010740903001d0303d500c1110004d9445580500c52075038226105821180c1000500f4000c0744080030290300040c046400c40d0880740715113030f1a071000305680034600020025400c02e564001d5030307211030040003040c2a580d20a05000d56804100b600c92131000141141e00310302d00303008001c1898255118070602c0d41c400402c003189500e008020344010312900e110040302e0640554460002c407142400002d2404200000810442600c1242c00031619940d14050703520f0a0602e030010403207810354801c0388039034414420721000f0364a2180c110380007502407030003080c184c6840c0c000940b400038950340701da454450b840d40c01080007004182601244d02440035104006041d181414043d04070829000d10004094041c3d41c20a0003581c0e000c040d40240402c407800c010351400400e046512030f081e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 473664901 1250 473663651 473663657
    0xe0613021308011104030b06040b010e030d020f0d11120304171b0c0111030306090a0f39080406020a09050a031a2d0901020d0212090616090312020c040c 67
    0x1c18451040c1c00d004200901130609400303843c052071900d6541030074402a000600c103980341e42620300903038420729280c000d8000080943e64104c0b49098065510000300c981e0f000a4003e040d080e240081c0a04130085551400801a007078521905613503681c240e00c01402140c40c41c2500c002c108400040c000034003101c1080d140d05074400303c1d404085618080c503070903c403410850106032000d81c030f040220580c6d030403a00548001c0459140d00a00c80061704206100507409840d1202d48034102c4807541d4010688080c034402c0740050340310031a0a180d5040700d407070700d0808503c80e04040380c001016a80204400151807604001c03c1d511034000448140300c0d5030042d1015088081c0b01d45640c400014401e030800d0060214410030f601a540000904241c0120280344010301000147c00c1d50302074044a00d02c01c141941190b40c1c5280e034500300030001042d14001554429000004d484121a0041c10481c01c241d4541002c07280c950f40d1031a584209004541c0308600030343d014229161680d005000394002161 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 473666151 1250 473664901 473664937
    0x1140403020d1215050409050c120a1518170c150405010515030c19120303050f0f010b190e0a030804091410051c0f0b01031e03090e061302 61
    0x803000616540c0c01d9191000302c04e01d080480d5103400d40c200e0040e0120342c03040c5c4021a60754101e0a00790b00b0151200107031030300708686035840d80401002044e00d400d050301c2100d0700f007281e940d00d2510000311001c21208001e03600003800000702140500e15203211a10814401c4c9142c011200a00c605020901c0100d582d2000c1280c144420081c00f800f4541d0b0001d03029110090005403080000c3c0e039002c103040d000c1c0c01200c00540c28604e0280c070050440203011710004c1540d55a0842c60000c000f00012207040c5050020440404c0c030301012a580c56048135004400941003e4103200402d003180081001c210070300580070030a42098030703a041144000e6016001064a4620f803400040c1a0b036028002ca4005250304d8040100c040c1d00882d02030207984007034514000080007210741c84170089170010f021707001c100c0b07101804040055400c80281a284620040c5401d064030380e400303000b000d5542c40b0040100320a82d8081c0240d80d4480c0b80d95502490041041280c500031441200407680b04001c8100f03105014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 473667401 1250 473666151 473666173
    0xa020d0c1a1b06070e22050c0309120408070513020d1404060c170112060b0a03080706110403030e04090203100f0204050f0306010b03070e240a090e060604170114040302 74
    0x6221441c078490842e005400d103803078606001001040b422856520555603d6491000c1c085a451580c4154103000c104010505004051000503001145c0d0310415208980140039008595810f9404940d200c8005000290a200401210101002030181516428402c0d25270100c52801010004541d07402d46a12a0a0504115055408003401001480700305e410b41001031140c54501c0f4111103074003083c10010486c0c8d10b48000a002403401ca0b0764819400c000210034442600c2c020800350f40b00b010104406072100d0022103141c041c510000c1c000c1078480d46400d03100e042c00c0d00103043c0b4030f20040542c2c100705441c8038070760100e0314005900031800358003040074031046c04c019500c2411440b04800800083d850692602500d00c80148810200010000d0103261a01c86134680303254200c0b641c000100307410002c4820316250700400034450025442a41c0002e010810304001070146001034025444c183c10071244500d20f03074041341100859981c8207002814041d884100742d010354800ea0141c8514000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 473668651 1250 473667401 473667427
    0xf170f070306141507050c22050109110405041515090509240d110604060f030c0e010e010f090b040b0307080a0e06011a070f141e0a020d0c1a 62
    0xb254000420b003090350300c1d0520312965118000c001101c1101003036903460140380f800500300486a0410358004a0265400524000082002021003400f0104100d41e07a81c6000c1d40c020346076403030003c01002d0401c01040c001420030740c01045601d500c804940703003003d907603d40200d02d04951500701e40c0007508061044c0200d142082d42d503500030210f00703c0040080e0000762554603100c482c00301d061240c60b982c2400420081c41c0c80b0a00714002c1c0003808161640c0d0380ba2000b03490000114050b0700040c0c61314510704412401050190074820f01a501d141c603620032000103460844042440400b0300181600019100840b0002000545458214152241001c0d000500520320107842081d9103406e107605604041c0d03000407100c0c111a06201d05414407400708070750305424480c58001500280c4060304810a12250201500d50304d02c01c0380480d0500a230b03040d80e5815011001c400e21116400c18403041000d807030000140d20000d40200504001d180c3d6480409072000816042005404c40228a044036014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 473669901 1250 473668651 473668661
    0x408070b090604050906030f030a020309010e040e0d120222050a0608010605070f0206120f1b09150a090b0a0905030c0a031a04212706020d0f170f0703 66
    0x1100d02681d06010019001550500443c0550350081560000040641e44c0c20810114103041e44002d480da01d045400009481e60b210102c024046090a09a43c81604281c841e0005103c203500280141030030040f022a500a040f402c030b4512a5000e201003d0605072403400d182ca1070000c41d0301c440c940c0d407900e018000344d2000ca03070010050050f001c1c01000300641200880d003000d40e0000940f54000410301c0003841e00c0c0503d0221200207248007007044054141300c0031080c014045110107502140d2a0b14000115100313943c111904803a891000028014850001c0c1202105504000c503140303840314442a4143c000d05800400505210b0341041541400d0100030240c0310260381a148140c255200d002011250f1001884d56018400c002024082d444a10300f5083c400204848004200e1110040001c00c00102c1d0360f00760420900008072600165048000315041500908504804c1e0702d4180c41d0310750740740608003e02072015000072104600c0c1200741e204c1c80d061440c0307003210b041000700201228 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 473671151 1250 473669901 473669909
    0x40b1203040e010e07050a03020901020a0b0103140105011403150603070e250206010f03020603130212030703140c0618070503031c0b0a0501120906021b03030402100503071b26040807 80
    0x413012405210b00742d58020f040303071120700c0785042c00b5a840d2400f00c0102c1c503002c10601c0140103242c0c0e04001000308003c0c1d01c17815a52402900003400566280c402000c14415210388140c0c0c5a40300c24140c401c001d200000d45540b010008042c0c4800d140d9404000308180e0301140c103000c401076001201e000f2080408407a800b05c000da8401042c42e50706000030381800c2d01c128000a0321840d0f010001824100058a810b0301c45503003d0401140200e411135441d9983d000344004401089075000e00302c2c0240300903001e454ac03903900c250052049031290350304440c112800b0f42e0080b80342d016984012841e610200020309100c94441c080040c100700d515001002c41c2d05503002e1510494444104010a030703840500c0020100300d0034800101c82900c1e1a220f8002c0c4944402d01c0350030000803c02c070304003c0000c00070314441e50007a9403a0920007410002215184003c8600c0c801181e0700b4040c01140740c041c0501d1501140c4500d480004190b04440c10b021040c605a030040400840010240030f0f2082c01c0c000b0304014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 473672401 1250 473671151 473671169
    0x506031617040b0606070501150303020c151602040519140f060108091c0509030709050405210d180b090d0207091e0c031b0207030309050d020303030a0b040b1203040e01 74
    0x509095880703003c07810340036000134410907001c549442400000c1d8040218840820720420059549140c040c0d20341c0f8902405600c241940c800300002d50041c0b0742216400e1448055600b0000b03011350802004210182c616011031609034416150340030310f0300c078007400d65401150350000303460034104083d01020001d0149040280b50001d00442032400502000d1030700603400c490080400c00941101c0c00e01400c008282d152140c21070005480c00c45500160295010741f0556042ca01403481107250000c00d2003084514000030040f0340900e07546a8418071030301d00640b40c150900000d03500c40c0c401101003602da20415070000d916844566404100305001081e070b0010511510200341e0000c1e241108258503170310116118045464424840e90142c50080c4614601c0c060719040240025a1600c050004030003040d030340e07100070506183c89840d8444d2564005c00444c42c41d44d8a06111001e040e00e03805c01508252500101e11281d07a481c142403008800410045071110b290000410a0aa0680c041c0f000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 473673651 1250 473672401 473672447
    0x2060f130b030a0b10050d0f110f030a0c0203040605041502030706050901022d0a0e0f0a060207092a0320030a09031e080c160602030c0a110d09060309020a05060316 72
    0x1000c0d4100050301c00c0b005c000100012950540740e5608050082582c241c01c1d6249c000640d80b4007092880e0185008684210040141c080b0b841410380e945e02c528000c3c04045503080c401044144103a0400414564540c416a4145101070b44c2c1c0c101a5482940c10b020581d40204280e000031280c01540217180154001d40780c84610b545442140034802d89800c0d1303040140c582603602140d240c1440c4440030b00380c00303000040c503150b40d114000d49500b40c60164140703c3d41080c0d4119100c030310786105103084581da00380d005c002503a40607090300105001c064060707c200140f5140207801c504000a10320503403440c00081041c0c407061038010300c000c02d194000851503500704654480254800c0e1020760043c82044095595510100d50186041e910a802000c41e8000810010070120000c09494002d0b001d03115078040b081c040d80c0458403040380001410000c2e1008004001c811f02c40e400000b04540040c181410490301d070004201c0c280e01c112001c0040040082440c8803e582c400d240315141520180c8802c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 473674901 1250 473673651 473673679
    0x3020d030903120f1404050f070b0a051821060603070e040c06050c0a0c15260a05130804030807140307050705060315091504060b0f030402060f130b030a0b 68
    0x1c80e0881905190000d156104e24280c040f50f00780d03225a0f0810302002000150703281900d8034644e20540d000b1465024055040300086103852502580c03000407517901c6003418403031013036a01100000900181a4014030b0318841c207255400d15520b005444d6268005020305182032820300d450400143d0000c49012003c0c030411020608002c000e80c107903100c52504540e10380d41c114a5900e0200f444101810844095a00140c0305118001c94600d40445480315903a1a1003880160902d06c004218980700c8060032000840c81091503000325803020f0040012003940510340c86035851504a500120303140c1a000a81c03900b03200d0381c9220300e40300e104004001c51514096607100c6445001030b1107410b000b03600c08804500d030584100c3c060303d1322007805003802070b943ca0072080200600680c080181d0140b403034002e001c2508400482207458002d05409080c0c9580c580364244a295848000c0075220701c4014270914503c405070360105030041c02280c0c01c25442e0b00f031000801c822a103480c0b040610442c180c01d43c1c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 473676151 1250 473674901 473674907
    0x1804140f0a0c0302060a20060618091b15040308040503010b0609180c041701020a0806030106060e0d0206040f08030406020c0405190b0a03291602120f0d11040303020d030903 76
    0x2200f525810345007030342c480a8041e416101c1a904222040c1c0520340500603014004d0300249141c852102200c0c0a01c4e2000300c200381c204140b10580742c000c056008940400044036030380c00740b0034032403a0141039141c92840c500784545090b04a50421a46820005820030051809001d90446114210351040c940104100010710201c0c0b0902940c1c0280ba8150008482000402c00c2d10020405940072102c190800700545000392300c4003440e040420514004188030382814840c103c00e0303070f0700da4a91000c0c0308001e03402c010b4134098082c01241d1001c0d003000b01003803040b9000d814000424024004503140d40c203020029041034052200b59014601c3e06042201a0b8807010791f921040f02203450000350320111501141c440380243d04064420340201d045501c4141c00401c510040005002650345942c64003102001c110301080340c000c2c016070282c042c500114001c40000d09101900c7c042d003074a840384401c59441a03640d403040b00103800b08042020418543c05004501013003a59103020030486180396405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 473677401 1250 473676151 473676173
    0x3080c031803030f12100306181a2701021c050403020607020307050c0909100c1d060c030d020901020304080f070612021303060e0106080a0c0906230d021804140f0a 72
    0x554841610b503404034035280300145000c0059034008c20248100f0082c00d18120380d640c02c0c9174086a14401540a00c4240c54003a8460b074000c44064240b50310540c0c104000358044140021030030820355081040c4680f00c009103c403000c003c03400d41c83c0401c0034076043c03c0103820544000d100d9010764100b045500009a800329010030100d00072284801d00b0b80341c0760b02c007074a020601d119080c0305600e80300c906694907400c100d035a0007038032016000c000703218030178014852640103440188030a60b000b4010011310703824035005443c0302101881228105640d90040b58036044107070120b0240c03600240c0052002d00c0c0d121000000d683c11500085d4070f070bc0104486d50b03448500520000c0c1025076244d0b01d201c4802400c1d0811030040c14240203c4142200609090304003107072520861007100e160250020382140c0d00019140c03482e0400c071a100e0280c465100b403204405144808070b9100c0c0111000c0042a641d0400042c055400307200365148a1040c0c6451616001180d4611007499110b181c3c1340d80010341d10841d0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 473678651 1250 473677401 473677417
    0x409060b010e01020a150c1209060b030c010c2f030a0c030501050703140f0619060206010f0608010501080c1e030421090f18060801110c1006260703080c031803030f 72
    0x3c001400307101c0c1c00c8202c0c0e602100c0302030540014204270101d01440301c990400c00920358101c040e550300c110008010f580300c4501c041b0007000681407a10b20105003091101182039040e44002d00d444003c0a4030009091010310601140e0b0b44000c8242070080c42024400c0b240e00a5540c101009460340d02c0d1850818200000c007100f4184400c1c5c2e002440036107651000e0000d2141c0548000503c035120500a5180c44003409030056400f06601e000034a1445107803154125401a10313a24041e8554144281d40c590203815940c01480240740428000d20808005601c12400740b0002002041c6420a11000200c2201d60f01c00f0881240d400380300e1042c4440c84a0200c500042c08a2800000c2a41c42b00290031a07601004855282c0f10341c01c10700d4280c460082140d0391000013590600c410b01000b80d030856170640198400030306001c0701181c540041009140088030100c2c12218107036542d0355000c41c0e5911240c1c0c0d002ca2604041025030114003000580140d01404401071800c18094042240c078600807020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 473679901 1250 473678651 473678693
    0x90608060d0f021909091103010903090b0c031c060e06091005130f180506091b0609060705010c1206060813030302071a0115110c0f011404050409060b010e01020a 71
    0x100c2c031011903860720382501944000701c0c2c0020940780c1c0c50002c0401440f402c42c0640300740d241080c0c050f801d441c0c18800c21103d10350503151f250144e410420382c6552500300b03100c21421484104240d8900c1030b4901010b0403241712045000c80e413103003060080c100d6031350080c007490b0261240038107004000540005001c261001650400b405906419850000d44405016000a58908a4080c503248920019440c0c890f01610486079161915602d05640b84502c100c0c80765424882e0070703440c18030310b800401861104402440141800501d490b25070840d10800424804036410001c00f2500c13281074019040100700f00d04000c00c291414402131610500b80c0c030700040030940d00042c03000c01c018400604010002000500e5205982c440d08410809070080e0140d1012030201c80354007400036000124500d0108000d0a45011700c41030038015100c042811849500800007440b01040a440300e00c5004600b82c050480403444401050000d0082030065090904640140c0000da0220310b0558905032008040d103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 473681151 1250 473679901 473679923
    0x6200a020c090c040506030f07020c012604020103140a050103030f0203090607110307030b0c0d0b09190509010b060a1e0c02060301030f020406090c0c0c0b0a140d0b0a15090608060d 79
    0x100d48090140704e59040581d02071400300c140844007109640071403203001a0307000c40c6c220700001c030010342d204c0d84101c0c0541e03980007000121400d41e020030301c40140c015106044c0450016294610b04180c4072080703c040c0c00181d40c0d18010014180d110008842800e001e0014500d0b000404000c01c1203480b0f500c0e0041c05c480c0340d440e00c40389161402c000749170042d6041100c0500c01d00b81203101c020385501100300700840504107280e240091400460140c011441c05501444150004540d84007500300100486055543c410340400951030f1a0020890308a10b69550540200010540d00401c640c2c0000352040000340111800103807503c008881c10340c1e4021058541104403440020040d201e240c000d040958100500d06100540141c3e500500d58444c180074003100307844c0e104002c054045c01950500040d00910342402c41c1d8607244c010b0025091005000c100000003501080700d00d40c4d0341d4040ac038407144941d07a01c08400e61150a04001e0452441c140f001401c0c10b1002400482c6000005803401e0400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 473682401 1250 473681151 473681161
    0x1008040215040602030f0f09040c020703060608030a0906030c2d08010801060602120f07080a050403150e03090609270708010e13021e150901110637020706200a020c09 73
    0x2042e920f00b0040184244620ac001d808025102c1105120807503910782064408501001e02200742d41603060940d4550b6802031400e1001c4010700300030b5500d0014807a6280e100c0340040d040d180040900044a003d03006103688240008041d03843c16401511aa4035210091040a134040790030051b41c080903040035120207005040040d1445085001040a04005280401036802c00050030440b8041d841202e02d0036402400300d41505c244618607141d40d0410000d024161908501130116210003901102c5600c05c8035488501c02d90a82c51080d001c915203e082200d26903000780c8a502610f40a24914510b007015105803401d54480d0700000d2142e1805807682002c045a0142c0c90030601004109d01d10084409a00c03420340d43c05826a24006070402004426500300055214003800d000080d40000f22944800c24182400d06030002c03010654540c14480c3c480711600240107004d0040d103000420b092800454218250542802586504107100800355150041038020ba03414043d1118000381d44c0d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 473683651 1250 473682401 473682427
    0x2313080c070806072f0c12070807170d0f0e0105031e270706080412050c0a060c0801120b1b04080a03030e010507080c0a0516021008040215040602030f 66
    0x300e074101007220b01c03c0e6020013150b250300a0100e081c2a5a00000004030345818150042411548014040b141d0108400d403c01d03041040c3d40301c905184078415103049940b81c240340d0781025142c0c0e2018844049583c1407480c0102e040c82203040c540c1c03460900d00b007166030280000c1c0200c3d0080c007800d07041c002c000c40090811081000065414100013084489925099904c0381c1c42c404440e03078006800b417902c484442100d00004407007040c1c840684600015540319518414141003154041081080501c00d802801404002001665101e01c1000c0b071380c603110a80080644805070300c840d09440c045984003011501115aa40d0404401440d0010b0400885d00f8910107128030751041480b482400d00c418113055041d1f00036083c00d0201d0009002e40c3c0c582c07450889000310300b40e500e050002c408201241c6803c1c02070300146111002882c154002c25800d40004004032481c5020002068150742000300714607040c400480c07642c1580003072504003410701400a6890058601c540003c600c0020f902e040c280e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 473684901 1250 473683651 473683663
    0x40606080118060e010312030e1f0e1203010e0108010f0c12020a0207170102040608060f030c060c0726011b02071e09090507061b210507060504062313080c 68
    0x8a9902440b842e51b1340b440d0a184448101c82c1d0800000d01c0c1281c0003400b41000325204a00380340c0107000044c464560345e0480014115030f8404d400510400c0c1c0c80c12a411068070141d402031805002d40f25587d85001a010b01351a000016245003a260010070701c0c18507082000f070048904403c00040e1510a06002a89032001c140c00030b2200450140107030188900540050042d602d440da11210341d62241340c18040081003141d005a4990030000e0310403403500300034000e0140001120111440c0340c0e5503406c0c80020740c540300841d16040003403102c214070b100000d008840b045403001d0046018401c0b251802501e481c0d16005131007400070000e00c1d843d030550b100300581c0d0107008004010800c801386850401d41d120340078440c141c0410210301c51800c00c0c424071400040803603000300340c90020660002c03403000c510ac802003041060100a1110130302081440c0700b854070652081c0c0c0b0004078542c4640740070880c0b00071039100c2c00241c8058020403a5030046100319410040d884910300751640100ca5410381008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 473686151 1250 473684901 473684909
    0xe011b1a041103060115030c14041a040e0109060509092b0201021c05071106070206041127040611040b0f09010e0d0309290909060316060806090604060608011806 71
    0x11041400100320f001c049104e0040c0f01c60b05441c08c000341d40091400743c4940d0b41009854a003058140403c0141564000c0d005441c000400c00e064070b080c0e154140500b8240b000c0c0c008006860745c0b40c1c410302c16414039903030351030700704a1200040103081445c540e082902c0014421480900300c21030900c110840c003d406445110000d80e625030807010032011041c006040c100d9400c400601c003002040410070010074017a000f00440c2e8050881540c0380e4492510208480ea241368020340b21078002004850245540807030202c0384042c0640c0b905090401c0c4060312900a6680048070003008100030144036402201c0c2040c941088140d100c0c0b000b000180c40045d40c0411268022002d41c1142d41059804040c40061754841c0d10107805c1019051031100c13500b080041402d03510401048840000d00c2e0281c00951f025100404031003c17071b4900800078450035295070101d0013240099003400002e281504040351300c1013050784c04204251820100428441042c41010720304800a45003500b4820b007904480060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 473687401 1250 473686151 473686153
    0xa03060f0b03072003040b09030705100512040c0312020d0f0305060a0918061e0c0309081206030709061805010803121306110f030105120606010905120f0d0e011b1a041103 75
    0x71b980c0d4003244215517019a4407039100340281003011415180c064065403540707900b5a14941405098104100d00e00c0b400b030b0003aa94010000800000180d075407441003000e940700c1c0d0107880081e80c40340380a8899071174029480145400d00c01085036907101d510b041801c640c1c40840204181801130315000800c04240005000282003029203c4107120310a10b0701594104414200a196041903040341141d01c1c4480062070f41c501080740320340003441c807a14190800c40040c180e552565460001104130f5034550301c014414002402500b40301c1e580c8d44602c07801490184c000d540382c244142d207284e0082e071001f0107a00802441000103c14403940e81c0c4030403aa820040300c1c0e85e9907041c024201241c10b4100348102031240420700c194100c0b070a80030454500614041c2c6a07007107800d0501c410001091003101c0c030781c1014810042d604400c0801084074246600c0b641d1a0401c442c04540001060446c40c04900510700d0310f102c503040c002030300b110040300901000d812288840e1b1503615021040d040b102c41030b10340c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 473688651 1250 473687401 473687407
    0x13150f0206070e1f110f0307020a08070b091e0d060506100c050634090f14030c0f01030921080609040b010b070206120f0a061a030a05040c0302030f030a03060f0b03072003 75
    0x1c0f1b0f2000000070425680201c41c494101e035581e40794265110494001c00c03243c13440078849205103007010202100b500460036413440d4503801250104c0da101d240144140c8000d91602c090240a00304000500802c1080d403805540d04813064560740c0c1d86101c05444a202c1e00684a104441052000000c08103035088031040500480c03080c10050200c003450152464030310b40602c001491034030f509070ae01c41ca82405800382a0711080d450403c51280381c4104514189615245060009550541c2e08e010740000d04004130100d1aa80310018402c0713030f0003844c01e8041c41051b01444003103110006482e0450f60444416903891040784042862805200211a81d00140000384108508a9560180b06002c4800c00b0407031560f0b6881c401c0c12850150030a40c4410300c00f0804944603010641101d43c0c0140a00d9210654079030b241d0120f40f070884030110561050300b012441500c1140c0c1070240070000e00080418000803410001c1011040c0310113085c010500010411114217115140c0b042030700d851600c41600c4d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 473689901 1250 473688651 473688673
    0x606050a030f020915180406050a020304050a0201030b010e0415170d170907050402031627051c080c0f0f0601030c0b0318030c0f0c090f0c13150f0206070e1f11 70
    0x40c80703003407c0c2c508841017420100020b01406107403095a2195412174001c02e401d031060303001940100400e5000c1410000301c6403441c8155104e50140011800300f01105201580c5000480786800c00c40ba00d07000b45603006044800c02c1c49038081e12503044204907011445481d11000c03442d074540503035503020a07001070021041181e90858a02c403483c9070220b07a29110046010409e0740b12001950318035a00c4c0d610204d1070180942d0408200b02610f4455601d0504000c1010f500c584105810046803082d0710f500c11014098015014003509444000101c01440d465066070f0329080c014606028820001c10044005140a01c1421800b104003110509403a610803600000640300c60038030700ca0101a115000d00310960781407016580303119685501750f210240c1c5134008200c150f9403000d02c84501041a40e00081048030340ca000d22680f50b4041e850307008480008182c0079081242c01013017081030155400301d1f8002030700d442c81d062070900781c00d41020b28104140c0d0b00a0b6281948102644214480d11100123 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 473691151 1250 473689901 473689939
    0x703021603031b0804020307090e03070f0602040312090b0d0203060402091806030f031201140613091401090504050c01051b010912020610140d080d180606050a030f020915 75
    0x840560f0b5100562401c0c3c0c2400c03803d48202e2400d80d00203400d9072141d00c3c02c00c0406680c1d07104174000940c41d000d80e850070000d40c680708082c0310000402d03202240d0009080040214a00b88404402400d0400d99030f01d5180540c600b00501801109040168001000843c41c0d501d40d8100c0d102004c5c000c04c2c845111400c0c90146444d440e0882e00705000384500e150609170400f002040d00c0b81a05c01c0c82c1121550b82c00d0071030441c1c01805484905400030f909000400c88555650003041c0500100034000845000d400706e65aa503071b0040e8098448a4541001e0101050000c1580305001c2c0003801d0442d9101c51121504640c0c1026860341c00c4a546000950010000301d000400500c00b516030031200c250701c0340031145090b41d116114902860740054040007141c108603031121001401000581c0c20329036016542d106484040c01c9600c196940850440100328040c13082c1c0e0b0161106a07100724019055a441c4174100c04d4080004e0b109095480020709204000720400b6201c120140c062034028030511001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 473692401 1250 473691151 473691161
    0x20c01050601080a0212011203090e0c0a09090603110f01052215052a012309010e030c03070f0c0f0b030711060c040b070c08070f090b090408030f070302160303 70
    0x7035000070f00320030100b0142595030090b200812498242d100e00da9182208450101007080f40803000e001e00c10f840052000c010180103032080c00c1041c0341c1c0d6960420b200c4000c01c83c0300c01e900842c2d102881c0c00018800320361151904001d000341039502110510882c0010b8990780540c514409a4510748050340ba40340180f100c559040700c811080118440d130360001c0554144c090132032000700c4506103000041032820043e49000001d2401000080c101c0c0c010031001d5038841d01030b100c036408003601009000401400340702c1d0081c00003680d0302640c28070051400080e128800d0900181c44102c900c0110014400040601b00040c4806001200400c6d9a41d64815035070b0801c5070302d03c010842441c1421072004c1c01148141c403c0a420441074602401c1900c68209130b0007a50701900c0903650300a000c1040c840c10007000028000c050415002c0c1807802c4448420350f82d01c0307003c8902500501d0107000000300c203042a03e803c52001500510140c0c0c541d0030860003230103102e00c942507151503070701040103040d016481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 473693651 1250 473692401 473692411
    0x290307230406080a2a0e040219020c0301200c030c010507020c150703050a121814160e220602030703060e07110a02060a0e06070602040f050901082a04020c0105 70
    0x3030510f4554406014500303c44010030703080c5ca429a0500c50318002c00400b070702c00e01150214181003030300504080203d8101d801c00030640a01840185904c0d00081d010000c00e0380300d40c0210001c0c4503e00121044080b00c0c24079558000d0100008100c0300c114510610503a070303a2001000c0200214584404001e554450300c1d40b1840c040c405008a40d06400f1200003251307281070f01501e0300c1d458986210030031103118403102c4041d844150340350b40200d0403c02004140d07402d1406201900000075100200c10b080c0317800340210b00910410080104a1041000301c01d580c0032100c0c06942544007a0b42296207042c42240000811542c8000104042c460b0940c1c01401500c51460700e001ea84e90702d51209654a2094994880315a80101600320052414500400c0218198541030070300404440210701150446001102c0c0360b900401e0a00060040030f418000511084504104c0d0354504128661904c0d0010080304400c0c3c54010304544580301d03480039502e00d03a00030b001190365200141c0e90900910040e20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 473694901 1250 473693651 473693657
    0xf0f050f0f040e161b02010903140a120e0a0513060e07091409072016060e040c021204030b0c090a0303030f0507480308010807290307230406 62
    0x302049941c2c04080c4005004c480310344554084018807240da5115140c5082c0807410401041d4010000483d44e42ca000002d2031088010500f801640c9090001804001d5201c3c1c2040a9009020030302d45d21030a000c02201c3c1d00340c0f0740699000b41d11a2240c06400280c01c501d4190b201c1c44103009003da40040d510b011142c0c8000001c20b41c0c1010010400c10007410341d00d1000044001907210b40d1150001a000f4450010a080b0303600003402000581003004140d101d0408103004e41c88800f01400c21780241503c0012910150241101c0100c2101007401180030181140d03414000149010150804031407403400014004042c1e00c0e52807500a0190004402d050347c26410840413401180c09118070b00e000e04211a6070030818a5000c0203042c0c04d024080104a050145480d58280076130140c0042c01c45901940d01d030352866040c01611441c1c8020b5912011075855054481e1551101680420781172021000c080b903642d46170184100e640300c0f003d542a44a1000e0004141c2505840c0c03002071041b07400d070341c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 473696151 1250 473694901 473694929
    0x16050c01110a1e05040f09150f0603020901030e0607080f130605010b0c0d090509012d06091703032211030f030d2d02031b0304050a0b010b0306010f0f050f0f04 70
    0x80804c5850740200d10400c040401708a1061019848030303049214110400b04145445136500c0441f151512000d0b4025408281e0015032902c4c0c170b50f8103000303120076101d80e20000c20003070910f60402424280700030710303e038801d590350004a00b0b034117815200c4400c2d003900300800f8892561140c0b5800c505038032011200c1c500b4820034003080390140c000d80d8440304441d8018038550143e07203002076020b0700c40100030340c4100a0b07920380100c0c0798483d8040800000b0708055507440b500c0b2410947c1e945030101e4920310306007107940184200b20711a420040607012080340d800f042e013600000c03403600b401a0300c0d100c4651079040c00399000c1803940c0000000901420560300f0420b0100083d042c0d0040c80e508240303c460002c072007240f450210440095001183c000c0710b071000004017007028a03a00d80c01500195030889481e0040015070052080003007045000d403541002c0580396041c0341c5d002801e00342072040c91400740410b24a15202d203500440c151041000c00308a1265142425445502075601034050000548090b0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 473697401 1250 473696151 473696207
    0x605120d081902120f06181501030b0a1503050406050a090507091d0a030309030215070503041719020705041a0a06110a0609050c1816050c01110a 64
    0x10003100c4200c041d1207407515a1984aa02e41401418100d5101c000d034003002150403020030b180c071441c031440c0b903d11060018200601001242e14034030030310b58441c0c83d00c5410300004d081c0085440d4040c00c02401e000882000e21030100d0303003402d01c50340614207041c218140c141442e27800d0b4100c54401c510034a001c00c0581c0d28035617030508890003c0400b900b0740d48061428044400c10707074080541c040241c10f2040c1d040803c034040c0c2d4a40f076844101200000c0e1507107218420141c0402a04505000300c012500c100d1074072072001002800010400740103071000a0582140029240885440820200ca400d4000010460180d0381d0002d62044c90f01882c50101001031120301900c00d181540001461041e0703017440c09000301c3e80b11102050404860256000e03280000e00faa214401c08284600003038903c48a4084c1008498030030001c461042500380400c00c2105001e0850f682e50002160410a0b03c03803904480d82801401c80b81d00051070084005110f828181d000111000e0005c0c80c0b0300214044000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 473698651 1250 473697401 473697403
    0x109150914010204140607020303042d090209010503060f0d060c030911090103020d0f1110030c0e0102060c040b0703020304120c0e0a0e030909070203091009140111191a010603060512 80
    0xa02e05c2203010120700c0e4000f814240c030340000102002c60005080f00e00302910380390601d40031000f0742c508801d04210f005030f4801d080740503c100c1c0000e00291400314100004075002030024030000b00494420070f145c120194203641ca03021850400c80e00405c08000c09d01c0662000350040c8501e0310b00750740407100c0510080300c528024048505803680070305050540c0c0300c00e950b03d06221075581012a40d405000442036425190600304100c0c290482d5404200c40340941409821500d5180140f811904036030100a01c1065800441c0c080f240d00300131850791058242412411802542c001c100301d141c1a005070800e0000b5200c1444c01d44411012041460700c403000480100c2c1c1da02d5084c1c07656038005200c00c81c03e82c503280c0255607101c0d9440c0142c901c5c04180e44000b500c52a003004422011840c0440b00780f000402e8070340030500d011b10a013400710310002c0341c48003ea519041010f801d601035088801c400308200d03000e40e05c08403906403240c0d0b60105503122a00940904141d000e13160085201906070808030074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 473699901 1250 473698651 473698657
    0x5120301170106080a0605040c03050a0602030421020a03050f0d060f050a0b03040b190b0405070f030b01020a0206072307030302060105040f05042316030c030c0803040803030a02030901091509140102 87
    0x70113400516502c5a1552900c0140c82e00820994201150910000c0421828002d240002e48907101c01030380c0745005c2c030b80f0101000880c265610340100c01101c5e42d07082da4000503039a6111303402d410010384517101c0d80481036035841440010410641450800120b800c503103c21107050b9402210b43c010070984a10461405000444000e001c0900c844081444140340701001d854525229002240500015000c2000e44106a9248000622030b540c100030243c0c0c140700310703005124244050b00c44414180c0020b00107000e001806407443d81e081003e1202c481d82c2d020000c040d014840280c44039207589090281d142c050034428240942d0502402c00140c40c86889034500c44d80c0d101101c0c080882000703194072070724210034014491034803601d410349020880402c038220045204072190082c250071494000070501043d40611299401408244842240401565809103003070340010b03140e42d60410450b02400c0c0c1d0150240215090050340f0420f441650008481d641c003405414910118202c100c0c3c0c00c0384 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 473701151 1250 473699901 473699909
    0x30306010207060e03030405180f0705030115082a0d0b0307030305070b060a090f020918090c010c030c150c180806010501050f0f1b10020901080c0a020a05120301170106 74
    0x20b00050001d111460164405410030f00e000ba08403400e04c1e0316a80420740807044803541728540324052080110040481620540c0805540b400d84c0c195450940740640440f03c18215009101c2c01000040700c01d001007040b085000a10503090340021901002c001c1c0c3c507130080c8103461003681040c04003005424005207a00c22664135a481500e0454940c541d501e4001c0d000c0c0c40160b10800c401400106116140901100f0801c9030308016a2a415107003001103130002d8001d004200d89030724003040140e1001140100e141ca90a080000754500a403070b086920600c07094004090048903503180803600713010383c0424500f06164032008142ea06070940e00042c030701c1c503100d00e080550000d0010700565201300e000e0305107400c030001c1135820b103944826100700e40d070000e04c05000325014908103001c0d4401c5c100500441f048801008510708044480000d0081000602d410070b2480000b9505d01050720809c05505074580002c01c3e502040c0e080d404000840e8000c0c40b410143c18250f46042068a8043c86100e04503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 473702401 1250 473701151 473701153
    0x12020d0f0e0120060a0c0e1801051507060c0302031b070b19020f0711090606030138190809011413050a020603010e040b0c0a080f091006030b180303060102 68
    0x301c298034011290304000c8581c21040510781a0503906200040111502a034000c51011442c0320145900800f0810015501407151105100c3d281d103c2d0100380d0540d040d50020303038a00306071291504d278880d10303031040000003080e151408444804066150703015502645851008005041c40070791419550b000c4c0705c5003d0070b0b403690748001c215400c01c02c40ba66015140061405810704c995100c00000f02c0c0c101100684825018280464813480d0170b518256001c042182c8c028119410700001d1503148910781c1c01c03d119101c04814ac250020070714040d1881c0c049a2401c4e49648240c2134402a0070030b20010410000b2807603581c041140c5000600032528040f4600b254140d030b83d640d030100b0000707104684c5410f5415000f01600c00e4056290b0600550281030b1003035909045052504e00760440c068010010708050100b4000740d00c185601040746508000b0310705900e2070a8890304600c5040003180c040f105c41052038042c00004014006640d14841d10300c0b0600d600c031014aa00c1c0c055203070300c0112042401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 473703651 1250 473702401 473702417
    0x809100c02300a0503010e06090408070f110a03112e0305040807170a021c081603060902180f030c010206011214011a120c010906210912020d0f 63
    0x101c6a46004203a90049166440100184000b4402d4120354400c840c0180000d20000040c0040da0200380b5503030700204c0030340b1081c282e80352580f11003031907008004008240c0808030100406104110400c2c000c3d0313000041001360081d035649404594074102000b414003074507500c120314000505426010018145500d41d50200c0301c1d80c07240c11001400700a004489c1600c00b0710400c008075003000d111840c92103410030007581c1c41c4003d81c00640742128034071401300360340800b4030400e018950240c0001d4000234140407600510a540c4007d034040c15850b08201c1d0041d01c0810030112440d140c41021090442c266800d0704000040d905160b02e512051200c00c3c096801a0b0040180101d400c5040315014060341d030f1a4441c1c6c89441865081d2441d4102c484a0250248492105450300401c6002041410b4008108c1940224006042d04901d0702c07a0106000c0045c00a1010004200c4884450981da907000c0214104500e0902c4e07840c198003200d900140300341d032446903006004000c110000e1004c0e40b00c00e1070b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 473704901 1250 473703651 473703673
    0x250810151701020403081201060206090a05030703111009120311130e04030c06020c0d0905060315012003120a06050a080705090c041d06010809031e07050102040b0a0809100c02 77
    0x541c0310204410079007559404c01001010480320300107002c004a000141c0d00c0039524020000b450300d8005040c0083d15044043e0b48000201c000048411851385800c080d0303418100007006504204080aa1801d03940c18500c08004000005406841450380e58600b0051301042480b80b80e801c0c0245a550000403082180034007820035845181c42d4024420325180d0001c100558490090380c105e8800a00d0f19800000c541c10042e0b00038800e10003a100c2598950304501e85035002c100042100107080b070600c00c2100b40050302d001c0c0400d10407001414013089941c1c4004010b840c0c40c40040854030300740d04030f1400101007001e1500d4215134040703c46980c0106a91410310040040e6038001800e416007018007003000088c803d80302c0b2407500703031211201c40400c000c2c0f400790005070484200030031000a40c0c200304040202c40c0b0751900f9645041c0c0c48058003588903052844c0142c020302c2079411950310500c020801500c01c55010315410f11a84001c01076a0038181c04900d11801d81e920b1002810240e00325400002d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 473706151 1250 473704901 473704919
    0x30c150504090f0b0d0515010905060609040c200c0901080304081209060918070e03011b181e1806030816020f040c02012a0903120225081015 62
    0x800000d00f0180d00140107406500090342c42c01e21131908481e16005031105509010803c00070b54010004410144418074200001076002d01c41c00c2c2d01300c2d201c0c0355501d4108244512880e20555a601a4620a026000001d0b1080c1e691009819420b201d070304c1d180d002085e07040300803040d50115000a40142444402a02c029800b50040140380b6081081400400c91079950100d8030b6180c1c42034400000c81e9030525242c0200700c00300d409030840c003070380c100302095030110b202100c60246201d40c2d00c1c081408403510b44498500e10543d51082c02d038121b800f0000d0300c4c0000c0c0940000b00300c40001c4c0940083d01c1000c0e00850650310244405404200180980e940e154000440000703c60702c010071050a402186001808980d1100141c2c0e0060391f5541e800c0180c510031403000305040703803510f9001072803081c030400091140c2c02500004016800010091500b94000c11152001c00150000b44140c4821704035104802c008901c00c0b04e01c00d01c40e01008240828140c428000207403000c40b2003440e0035040880348 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 473707401 1250 473706151 473706161
    0x9031b151b1309020d0b010c24150906180507080106050c0f0f010b19050a060f180618090c080115020709020d091101020f0c2b0c030c15050409 63
    0x18190007002040840e5078064a40c8075503010f01039803540142c584070080321440441e074900b0f03411414440b003070030888003140d02c0e00e9a449a40c0c14024200d501c2d0404160000041c0600314403041d21070b41c449001161032030258002d103013a1004082c0c0001880c903441a00360981da01900d940021032505401440a14802c90040c80c002c2150030849001c80800107003d450040c0286020b2241d0355204400704036440e02c0e080c0134820b409525106d104860401c2c002072a1100f02c1d00c51201802032401d40302d4405070007920101c92290f0b00c040807500c1c241d40c82d02c02a085030076445a01c0754400c001c01002c0351021003031203242d49060b80359640441c207038207080607040500100307100c01e0150b12814078009000126400281131290101502084803075241c6840d51614101c82c1e095810f64004a41010b222000050b0b103404000d421920032105405030341c00755140305030481c8001c500c0f000084c0380b80280400b0007040d2007160b00c00c0440300280c0d903454165006070f882200321480040d0042008200c010416000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 473708651 1250 473707401 473707441
    0xc17070305340306090b0105030a0b0a0e040606030302010f0c0e010e03010e010204140a050a0602062e0602010e070801150509150d0c030b0105090103030525060509031b15 75
    0x110035072000c400e5203205100405400c005980900001d100020b4940c0750107403030b0060156030424424400e01c5000a40207020003011410020364490100e1300d990b668542000c0240107070000d0000c1030406081c64006041c43c4d01003a005582042c0708904101500c2c41100001034190340c407032001c0040f030b100441e501d0781aa440607905640340c44034010098000e1008000502d036103010b00140021080900c20a5031166200c240b0400003010104009500460882e83c080d00182c0c0002d5505a054103d5402d01413110301003009115200c0c01003542901513008881c0c80c0b850340100c03100280d85140c011300761078100c01402a40155404200600d0620b014000d030001d042d61941d04c0746207002e1001c613070700102560003038803900901001041031215003400d05000d80815074a80c40e00d50704585020f012407007031100900203034100441e458014044200345070b0951354800011711071400e10000c4c00e0341c0da0304210301c0b030511003010645029481200040b10081601ca604814410703a031040c0d5640400d00728491 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 473709901 1250 473708651 473708671
    0x70309050d0905030f0307240204030b0112110405150411120903070b071701030201050f0702090708010f0501030203160305060307181e0b1e030703021f030c17070305 73
    0x60000019801d010019407010280d8031051907901e40420075140645135062411650400c00c00000460b11814141c0b40401d0b581c2204204080100c0d00301c3c000f446140e0000d42030914110010a103c40402c00d0448203c0c000c4000091080c044820001140d5003920f6842880c001ca8148074800d04107a0880c4010400714084c640c140710401c401150080011600c148a907040004e0110801072640d100325000344051400700950340c07060181c1c034210700040c00040d0600102044d0351a03041042411280040c0d0302524a22041c10714400c05410070301d00f8096145c01c00240344010403603500c41e200b030f24418400e0b2500b5490401e4820700c2a0001c0501030305180c0c06010341000403942892101f4260543da0402701d0006150b401d420360343d00480c00440e0b0700d0800d10f0500001907150741d9a1018203246c0d20145110b070070a2812040024035000c540d501c0290041d60341501e441d050701210314041c52210054a041c80400001c910440d20500170076103528240340071202052005100f503006590168280c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 473711151 1250 473709901 473709911
    0xc070e07171f090905030c060c0301030506060613090e010c0306140108010e100305120c0c0a050108040605070908241501091406271005130e0a0f0e03031005011d090703 74
    0x9900303401139030715020080c0c1c5c10350f0000807070320b43c0c1c060104402a40840c101c0c20040c1554191b98801d5180c001c040c10042c8100400300706402c51100c54012003000707004c000010030655091840c60b0b406421603060180103c0d191410008401510800d903440705c000581d12120240c0c204034070f03442c0d0401c019010409403d00c0701c2000c0000390301001700800850184080c1600d0f001c0f07003004507150903130b0349222902803c200740c410070003a600f00303400c160000d5201c540440ca82e61558011500150550f001460034442c00da00311485c0004d20b90480d210f076034a0104001240d942e001a11408030340081060300164201c00b04000e0f13103014400442080e00300800585ca04040940b0203994590000b010030242600d1155170702452030040461024508a070400c0c0c0e084c405104400010041144101a8a00034000c0091005180c640c4211441250320304108089101160706075629003003110445103c1008032008240c56000d0002c40c8159403098071504a515442000d01800e544040c2c0403500303050b02d90b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 473712401 1250 473711151 473711159
    0xf0a0b09091509190510060504030803181e1b0109150309050a0b090609010605010219020a0806010b0a17060307090e0c121011070c031202030c030c070e07171f 70
    0x710040f9405034090744045200d90301004900c1003111400303481c00306c0b0006248801c0200c3c0340c021064a04403500134203142d851b55900641d200041803600556007450080c0700018800022407031449100003089021610719803528080c407107109241812040c04a45510402c20580b00440803406400c0c65030324021030074001c0d9545262414075200070845542d007500040046801d010400141d00c000050002d02c0b2244c40c00c00040c1d10f43e203201d0f0364181d00310b4000a40e2015034460910035030040001008131991581e5510502001d81c021002c6040005c0c5100420001c0c10310800266004440003005411100c1c0340002050042800c01c040701454003e010002c8480d507941182c5010040700707000a0140c40d480003c0b1001100e072075005030244848240244004a2030044510301902d601800103400d2540710718080c1d03c0d6000b030200d0803010344000070b004006c009000c108181100c0c1004207241c051b0b150f2040c00d0380c82c0541c0200440c070a11314500002c006500800c440614807000903441d2050b00c1e22 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 473713651 1250 473712401 473712409
    0x140709060e0406141b0f040509040b04020103060e070206131e0c090b101413080318041407270803040602010204030b070809060420100c020f0a0b090915 67
    0x35031141c80d410240a00300030611140740545100c1d10003100080110f4680b07002c0d80900305504020440c0060b00c0401c05c0352030741070440b00301c0e409000001c15002e041d20302341c90a841083c0e81101c040780080d0401600160031205c0705549805844a90007810042d900c16411200311403180310184c030160310890198415005280b41610301d90f00441418a0f01410800d41030190703040050420300403c028240c0707042c0c6507480341c884a220394074000c08a60700c8501641c0c403001c0c2c1c030741604055014080090905509004540100d43c59072050b01c040c000540303210035220340d00c5012145200400c007000e6410303016501086e20000400c1345180c08002e02a2503100d4580755801c41d07044107015030b500050500070701c281001d0083c1d011426190400d500d2500300c00303081d22518003401c014540c0b00490b918003102c80b0001d2029400d50000303404000d800801c000c00074112404000e00303034015201070f455400182440c0700d0910560ba10b40150300e203800c5040f014080600b00080150152000b41080c1c24400d40d9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 473714901 1250 473713651 473713661
    0x5070606030c0e07140a0f05180301052404050103110f211509010b03122b0c1b08090f030f0a08121003020a0e0a021303030504081612140709 62
    0x2489080e010710f54644000c000d4001806000061001c44040c0405a01191f00550014486e511031070801d4890b90b820905480000e08005a03507855400d1804221032003100d04085a42c2c0514080841e4106e102c0070240403c86000b8040640701d605c40001049090511080c40201d00c6000303851240303a1604107034140c0708500c420002019940001208121803807202c10425001840c074002080290075410000c0d0740c1d10004140d007100b100b07010880049552090007508003011200311444501d101036162040184000c3c07880d0400720380388469034040c030032948a000c003055a010300e1043c0b03404992400c10100c1d80c611040280d0602c2208800b80c6045420f00c5240c124510880d40640c4801012300312551201d401884402e0765000c0344420400b590755074401d80c04540100200d088140c503030240010181c42010040c00241c0c008540002c105944180180f040320b62143c10380d07000d1b603007800d103440100c4030910803100002642901c01c0b010030708000340c02c80140e0307000d012211020360b02c50030481515 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 473716151 1250 473714901 473714909
    0xc0325050a1101030e060f0117070902041503050a02031308030a0b061206100f050711010e0d121d06041a0912060915091c050d06080109021201020702010f05070606030c 74
    0x4018074400c2d030382c0b9580500821410401510203840c0c18a090100c1200010051040880718405d0001d50106c01505200311005004200020355840303032203110034004204008400c0c80020301d0100010f07242c501c0c91095a000c7d01d24603d8040b03804000c1d445904c40c5800c0a092054590760700c3c1200076807640c64000070241d00c415021000c200303103080400c0050f41c08209018000b0300030020b1018035025402000c43c2d001d10b9014449046211507440102c1d0500080408140c000c411582c00405000c0717075028409190096940e1074520600441121180048030000785411520611080c0408900f8448035014010f1001c0298242000c4078001790981d01e202d0807400650b00903009009503480140011880046541803040050034410b11069485241840e0b1030301d4100c40c0b06035402c05a10417011501804111001400060344800790349000b0952b0650032441107041c6000c00c2103001e010f00a90307034810f80585803d010002d03a804244c0313042d40010812036880f46c0d144030100002e094004100054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 473717401 1250 473716151 473716163
    0x3030a0c051f0b030111070503070f051207030210060609050a090f021201030b01090c2d0c060606050d051506250b0f04060f0b0306060f0a08030318070b0c0325050a 72
    0x1c3d45a081030608444807480c0110a01c03904000440c00300780008111342c2416803046190300486141e06001e070510080d041ca1054110002840d003050607800146107000c100c4040c420488140d036804151a003944034841e0301d40025065508003c082c06031340c481c045807802c0c000003610341580309a0313080031047c090300122605590f0000601100699103c1c4c0030740e0400034108444071500c0f0034005d00c4100d038881181d0001680c00b41030b0110f0548226004800c10703a05c80428403c0c551102030150854014065412145141000051064101010007000068007402d000c0c0703040c000c101c000340a14801c064210004810f0350306c050005445c03400d0180304003d500222100b03030605213815425a0030010802e645241440c650000c103913000310f01142c2049044401c40c90b000b50f00c4011803100c5046600211341800088200802c1081c101c41100c41440781e41c0039a80941d071240083da00318082d2102c40200e581c07003031003018039580321030712018200d1002e0403110502008a64445142045060b02250382c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 473718651 1250 473717401 473717411
    0x23090a0c0e0c0304081c1a120307080304080c0708070b1c09022b06090f020f0a0b030708220c0e060307080a080706023a0b03030a0c051f 60
    0x148034495008202030103072011180003906141401c10040d020142c030240650200140c800014050001c01c1d105083c03010703500b4440c40400d03c3c58408002e5502000e98020400000b00000c0c550b008002c482c1055071042245085484549030301041c0c2d0400680f0500910038070318081410b81c001c10900000b00740351446181d5481440c0e4044101d00340011008030074504003880f882c01070342c42ca41c1d680300c5402c4650b40c8010800200d0b00c1008500c000b40409020300e45451550381c00d11001c036041e0201c20340251241f02502000c2800d100703d00c0018800d0010841090010410b120301c20b552954019000309842d03010000d2903440007025400b0980c04940710140900c00708a844280c00e000e0346e00c200110050214070b40380031400d980f500117803000203122600c000b410200304456a41a64071109081901c028200d01002800440754111030650036106040402401c40e84d18034000c06107000405005981400c0c0b0136001506c56140da00c80c2111903000301400b02c0c201d801807123a81090303c81c0d800c0700801c3e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 473719901 1250 473718651 473718653
    0x1f0b0d0c020c0103050112060b030c21070608090a03110c040c020c03071a0403080706060b0a081b030601091404110f090a0e0402010c031409040203041104051f060323090a 75
    0x4500380042042d6810305003000c004100480d02148841209030300002d02185560404c1c0010342448031002400781e1201c000b581400050f0241c0c0c540c68290411401121380894481c0d038282c4030102d00321074140700d81d0701044503c00064400c1c00e90302d03e0148058100e03920000148001003d44019480001c0181d200c51690381941c0b07420400c0100612000708042c42205943c07144424501c140e01000d07080c42400151007041140b40e074003010017801c40c3c08076251282c2c0743d09001800613000b0745698400000911010141c4410081142c0c041c180c142c450007802450301c003c80094422041380c099005035101c0d00d6078405107140340141104440310340f03030316a0703101810204840c40303100307070030550b807a0704031404000050340c100040780302c000e17094101044a02c01c8001c03031035003620604030303500d8219001109010800c80780c82c07035103550700e80d044406003c40d80e140860038001d04021081c00c1c1260760a0700c1c040080318000d40c03040b4603c10002c60180300c1400c000150000c40502030392042590341c04000154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 473721151 1250 473719901 473719903
    0x7050111090f09090d03182015041d090f060106081b0f090d021c2316060f0912050c03060f1306151d0105040c0f0203031f0b0d0c02 58
    0x1a028100c503c00440c1c2411621142d4407505561544103040d610a262140690500b10442940c1c2e808240400100c039089010002c121080b81d50f180556503842d01c4800e0600c40c079040d241500e150342030700e21900c8008420701c13035441d00142c240320482c082c0f06585460580b003405402d0103080c954803202d185041494041c1c1298803001943d00314401300780704074003c07074a07034400700c0d10012012a682c5041102c580000b65082d08030b03011800765942d42d5404c07a0100325071920502d4140c4981d200040740309035962403190302da981e4030f0441c203201054954144203041c041d540c20503007040d5910f40301c00d03060b4407941c4440b81588000c500740c503c0e90201402034107501c3e041042c00c0c1e110301c2c2c01d1408040760800310041014000b41e080e000344016100c90045400d00c511101c05401041c0340518804551039022203040801b02c00c1c005e150007581041c2410011600030584184800e2955000710b103181c0e541c1c81303508a5184201e2021501c0d0180040016070104220003401c20304441440c0018140102e12002e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 473722401 1250 473721151 473721169
    0x170a0e060114010c020d050312100f24030c030f09060506040b030a120f0c1707050c1e04020d060e280b0609060309070b0a02010606080108070b1605030705011109 71
    0x800c0703200004110075050342d00000c0601c000c1d9060b206d800f140040c510b0500c0c02c0d401307040043d0012031108020080c0f2080c0c0ca00700700b4102e5441c901c010082c0303900d840000356030010f669003041d5601420b00c618a40c00b03109512041451072030f45030000d041d1403030020706001d52300301030801e880d529112020b105261409100b0b00000c990f0441c010034180b10310b80e84011580f003090305610244030b11090080c203110b0040b455a840c11368080300b0b02565864680d000c041c80d400414080e580d51060305403264035402c0186041000604104442048410f01c50822010794403481c00d0307190081d151580001e01c510304400c2c20b4040d1074482000ca4030492401c0c4040d001e12241c030030501d66070f410700c1300403800e070b0b22014110b03101800250b0b1460350f6030740e4401080b031400c0100d03881404284000184600041e606501900c2501d415958000c00e03a42e0701d0780340f5270781c0700c0d0ba602482c500d156081056811020001060448207032007030b000d0741d0400d031007a118182160203803980c0384005c00d0000352460303452810b0401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 473723651 1250 473722401 473722409
    0xc031908070804080a230d15050904080c0f010204060306170a03210b0907030902011205100b030a090203060702070816050310180510051611061816030f0302060601021209010807170a0e0601 83
    0x282c41049e1500c1c00140c0c0901d00603001030001480010348030f400d0b1009000302c4040e141030a009540d0b6a55030000100104045d114803c0100e481c8a40e04008050204d8000e4580b1b0701503940c2c0403c490054180c003000d59140f0040c6540315a01c28110246032075901440c0c0c80707800341d92000142c5031380d10f00014003031480918541494624060402c8a820311008844054843c141420f41d120b5a031030001c10700800d103070840a54144036240800c501141e00182c4002502c440000b82d502041c04901e20070154400d6024042c0e01d0340100c0d181c28070b400c00a40c4070140940d1081c55442c00c15440742c4416051074010f0100e008034607120300400c18030303042440e00020100e41a1403c1e251a5070844221030322005c0c050400c40c100100c52800c0038a01c003041041c92061103c01c0c002c601030b03560300d02d4440290b46134501c0403005406a4000a5107660000c200c1500324500005803030300d44403401c0c3c01182d200200034260310034001c40b01014107000211007a407a04c40d40c1c418000040d1000c00001c854a00441644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 473724901 1250 473723651 473723681
    0x1e0709030807080d060503030d2a02120c01110a0306081203012106200304020316030203031c06171b0301020406140705010b060c031908070804080a230d 67
    0x4820000595010110388100e0b0300302c8903558031102c2540384c100182c02c0c40d61007142c1c14880800c2c41990740115030f1040c00380c03183e98124030300003400c000700e0440b400509401d46805030f0414421040807270f41400c0100304e040d0032140002204400700d0b503641c090740c001641c0400025585c8a042c00100c50401c0881000c40fa41c00a02d0700b1580b40c200c0060703100201075603001d106034508614408102c042d4002c2090681c10500c050040c1c0211040c4071099003040750300744d10a03c1126040401c1c44403000199003965009000b0758503144018010743e00030368450802c0c000039552403000040da5019146050180e12112000d0300101200c1d010680c8100c2506544c01c2c400c1e4070400040040c40c2d041840b118210103580c0480b17403036178a02e08245004000c130f4000d42da004070f40081d03c240140004001460384030000c0360058500c521124080741c060b0011618040403648190124012481c42c00141180781c0d1180380105030312504806e1004288075039520b141c6c1442c808a1550341d004014080d00b1200380da440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 473726151 1250 473724901 473724917
    0xb060301060903052a0f010201140a092d020907020f07030b01030203061f05010f03020d020f030103021c0809041a0d06021b1207140a06060b070b011212031d061e07 72
    0xb07000080301715282c503d40d803046d0400c0e107018a660b4000cad0400c08180800e441c6030f82880c03a01c888044040d18041d84101e80d045c120014014413030b1440c0d00d505410760014202c1041854036503003030194503103004c1c1801d030651007491811204610200016000f0b14450207a2983d6549544180351400c1c03000351080e80c252000340340140c1c0d03000c10107070340c54100d803000d1800700408400318000703600a110b074000030b4003070a0000600000d1010340b83d004604a070300c00e46084180000c3c90050034102450b40130b00909120080224000790b2038030740c2206804400b00041140380030034010020300064a1401c0840e0410340115900002e5280c0300d001254070720b0404098102542c00420008007407003480802000145011804020030900b000030300030403035020508201803610340c004418103411400040701c40031a840004a8841c2c98020440211a40007210082c0f01010404c01d034080c243c12040d01c907000c603a405801020703c0c000c01000d406088000640e01004c581000940c0700560020030382d07003e000d006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 473727401 1250 473726151 473726203
    0x5010806030616050901030e030f07030e0303030408030c07060204080d080901050703090507031235010603140a052a070b010501090e07080c07080703020607170c16060b06030106090305 81
    0x11402c14840300f62685005980c44070201c0058004100c0a8540d100603c8086611010703080c01d0720017800b4080c042d03183c101c0014880e0082583d64801114000c0c440403090011038414170880000e1300740c0d10312614001d420162a420010318002c480302072400054030400510a02c40c50a2040b00d420100921b014007000e600303a2209a5150303102c0c070004007411415411040020311403103051103070040305030030030115480c40c054145009407104005040b0b0940a800000c03450300070302c101d10004803000000c0e50303070303507114514a40104070042c0a50400000d02e20a4000800d5184403500c0480002115545801140c204030307047c110140c00c130505112400c6001c1c800a40805d00300d43c0e200721545800030a80c5c0e106410b140c40360080000042c0142404501402019000310b003151048013176944009a24100c495000f00400701900d42105c1d130a800c00021000b440e1100c4c40816035401f640021400d8807080012a007540d10980c01403000801324141841001820320410300c0d4650050510348008406d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 473728651 1250 473727401 473727421
    0x52a04060c1b031b060914010c02040207150c1107090e0606060a020f0610062c060d06120b07080106030b0906100e1e01030b0301060e012705090304050108060306 71
    0x15500024040044041194064040c03002c2c104020b1584042081a241503044402e100c190450180c4404500340003000b080038580d0040411b0302c2c01c8140d480d840780050a8003444000d500200003600d80e25104011880000464003134150409110784d034480c0341e8007005041500781043c50304460251820300c00036040e0002d000405a07044841254032a54a5a038084142d26103030200710024002c2c003901c000c0203c046004c06e0300340121020758880030411001e80c911181d00400750b00b20201908901c2e020303c0a02c1c1005c10140c1020380c1c04810000301d180d140e4543e00b8007100d01d680c040300c110000e00100040254050309550050800d070605010a030340342d10006282d90070080403070740503201804d0451001ea1041c400c0080107403000c1c010030030200680f041546011580040b00340401d09104009001d4201485580b088810210703580c6126420300d000c0040780301440d80c001c204400c0d8102440c844146a10039540180d40f003c00650390380b45060005080313120300801c0300c3c0c4a41c024004101140720 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 473729901 1250 473728651 473728667
    0x914010315150e01140301030b101203050316020a020a09020a0908250f03110d03030b1c020103200322020310051b0c031206120109050c190f061101060504052a0406 72
    0x3602c4149c100c095a10307050b09940e01c805a41c40300b550078084600c09000c0c1908400154000d20302c85e071080060444800c1c0980e03a9640b8080000e400402d404003c001d00071407580548100e071254548124059980c449aa203080e00d26403040403d180403087c190100002103111100501c80121420f50051540d29500c0041c0c000e0740581d40581c68158034001054030961000c007030081c0041a4503a00071501c0f103101508081d52030101d0109190500920b809181c080500d148842170200b000c0c44c550f00c480d0403440040343c512042e1840015000ca0350016a400e00000707081c0c1e084001c0c0010145003443c42d100242e240504c401c60340207000c005047c40ba035408000c030b50300351400c0c6c0890310554442d075000c6014050454510001546030030058010001c01049030502d1441c102c0d00107240482d00722221182050f24807034900c824030140301c01c024480c001d0085824541d40303000002421680e03100880c064990446400401c64014206000d09015031a03058502c2840c6007242e40c101030602c0006801c0b24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 473731151 1250 473729901 473729903
    0x9030406030c09032a0609080307020d02030c060c1c03020a1d0f09091608010b09010e100306380f13090203100c1706010914010315150e0114030103 65
    0x64841400c010020f0141d4060401103903c03401c240218085840351160354442d000305c0a0710038004200004680d84128405000e9602c2c3c0d0014600c7e0103003035402c100320100c0405080307070540110b902c00c0f141030780c602d005072400c0700540002c3c2168100319003014850788400f01801c011b0500c140052520168400104051403801600d011061174404c0c0004280d814920300389580403100c001000203421010035559050746040f01d04000302d0307890f21b1105080c0c0c0d022003907454100194400410000900e040d40503000081a8601508542c0769183c41c0700f510140e11354a182c00301a08005080c0e40b403c1000ca070f040050352990800c50003080000949200080081248901c02d14104039402c1e48281e07010210707181e40182111002115002001c000c0c20000c0000c0b408903444a010740007490314501018400d00f01652142402801c20380b48600da003d40e030311005c1c101662084408000c622a8000d034014050310782d00c030318500d060790100900300b0921105482c1009200c60384488896010785c21b0380e05603 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 473732401 1250 473731151 473731157
    0x1201090219083309010f11041217070b0c0306011d0904260409050a1107050c060f160308010503060907300f03050d060905010302010c060c1e020705120609030406 71
    0x100300d044003034080c1c4064203a5260443c0d2000c0240143d03000d055014482c191904038090040c0f07949610713421054002c5108c0d1007800c242d81e000840010740013020030205102e440041e2400e011164071004a0058126074410160710004244881580c1204a550004102c80115886c0044010200d0080d00b40600020001620f00c3c55075518020750403c081080191035000e50786a560b2070178002c003d01410396802d0796462400300a40325004c0031108030341899800000034154006c0d4481407082942c019803640d24010018480c4040d030012181c60015281c3c0641d80e80b103010350404007014208140500b41a81961001508100300141e80c0401c045240e07803c0300c9007282c40d041c4002d01280d0b40c1300c03003001045035000ca018070042641103009800c10f84c0c8008000c0082c0c58642401e8021a0020300010b404948242000000181c00b604500040d80301c41c54613a104445203800000001200c2d204200980c01151092046003440d01c490011000403034000e241034208444420b841c0e10941c001c000070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 473733651 1250 473732401 473732443
    0x1060b03192a11011b090e062b03090902041502010b0303030709030f05070510080109060b18090601030f05072c09070f030603050d09060f020d08070518120109021908 73
    0x10304000b9030200018080d5000c44120049400350006d1403812607005003001040202e01144407030400c0002c0120340d5450014200b03000745400420040e00b00a0101102000f1110303001080301039050000c0c0c0b0051003400c442c44007010803080081e013990a500d00042c001e40c000d1080041c0f250384030711140112904424440001d6140f400c0c440d00f042a0340c2c12003904100c948486200f0030b07078840f40060480c2e07c0080100300b01c0791504900a01d074450080d042000907100b008141c2c00d898006512600483e050400098105040684100366842190b03100c2c04a14200c0d034491f8810000d0501c85c4010b02164580212083e80d600010041c910180500e000c0040002c10a401c0c02d020381e002c040030355001300c2120000c00705114010400c040ca0301035640069402c054070401140006810500204180c58081060f5924001103581c0e03000396258103e05603080904d004645c603016040143c5883c0c00c00003281c910341500600188080400110340000f1501c081080285808180011130180a00210b05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 473734901 1250 473733651 473733677
    0x109060e06093c01090b2205030a140702030d0806031b090f040201170103210206090709020904060302090c180907050405040c171003020a0f0e0103080a0201060b03192a 74
    0x84442d000c0c0c83c1240c4103601c1c001c000d505101d46140707210f1041d2100c42803c40c110203070040c000b41c25081510001c03c0d40d841407040d102d00a025a0410041c0c48090004600f030410540020340381c013a0342421000031403a0081840110f0409004030700380c0008038103000320700050761004503402c0103005152001000521011500310381c843d03170420410f00c150014003100ea5031a410481e80c0b10005c0c85c10500040340200032110024004620280f080e503503440034041c0c4601e4071300070707401a600101c03079140c4c841c2d0340b18000320050390b0f1210028080c60562240c0d0b030326492403070f102085420041c1d144900c554404030420001e50b501c101110160f82c07040d1800b0845104242050b145401c04800c0c240c5591103d20030801c46490804043d42200d000b00c03041510903a9407031020040d80e02600910341c4003941c46005001251485000741004825403000140c05996000039400075001602e064109d9640005a00d21040d003034014540050f102c0881040c0d198210792400e10390410f1b0715043e0041c8132084d00c07010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 473736151 1250 473734901 473734993
    0x1b0309030b010b04081902030307060e0705060a030204090c17070e0a1d070216050102070303051e0f030406150b07060f110307020d1227140109060e0609 67
    0x500031036004032850100e50b1900c14091043e003085c051601644107121885240d41c1c0c09140c0f06035429000380155140401d143c0320200504040e41e84400540300300100011341b61520320080c11180780d20b50740143c6807414604800144d5642501c042d0402c001c000c030303403107045401904060308040345d0b017005c5118403075203070110b036100d04143d1002d100003100f107000a1142c0f1003801603c6c0305031583da0944184110801c4d0180700c460130750055a0040c1c0c42404140000b9018000800d40c0d6128160401410b0403400700308220341d40400c01040e941e15001c820300007001344902030000790b860b040c003012103807c6c180955441a03020b000405440030f078441d83d41c012070102c154004040e10a03018407032541c0c1d2500c594082e43e9010000100c80004031280b04102204001e4898203030380d1403880e807290848031309105100360200c008000540d61050000d40c2c9040600003417282c4001c0d64490600030540c01000022182004001808041160064050111880400d821040120b0411064030200d503021120362 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 473737401 1250 473736151 473736167
    0x10806031c080a090c0906050301140123030307050d030e0d051c1d060a1a0306010b0406050304231005070810050103020c16140f180708060f180403021c1b03 69
    0x58414842054045100c0c11b0341c0e044442558000d500078000302061100e50010411709200d1040d2540b0343ea403041d07901c141e0124100c204e0801c024203c0f4100f10080c1c0b54141014101241c1300c01080d0703111a001b00940c07040c0115a11f07458181402420b05030004900645daa082c00740d14065181e80d148d180300c1e00107031a002c00c5241078141e0103c078090702e0b00b5803c0c0c60080c00854150000c042844101c1d030064580090000d068070854440c40c1e0405180500c20b03186908050011101e038112a4032480d10624030764455201901c6890041c010140c0501d1603008a910103400d0707804110351101000103d00c44141c085084400a103030050303440c1c102c0c1900b03a003040f5840052040f0300b049034138005000d10408040303003510307042140d400b202c0344c14003410800703151400c442180c400d618050000c0e101d1400780f0150f03580312002520112400070141c0000e10b440d8401403500346034a0f241e40c28001415030410011641c28607031044071018001080014100b00c500400b002c580b1203120801404042c0300e0700309 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 473738651 1250 473737401 473737403
    0x105090709081b01110a0f060b0d0206070602040519081e0f250902030717060d171903051302061305090c1b01020405060315030a1e02010806031c080a09 67
    0x1034420000030f41c1061141c160b025510180061103126501c02824030102d2010002a80564407800da03000c184e580700054580900c003180e2260b21302e4264005038807000c00404480344518070050f501c0b401c007400c00c902c88084240c0c82641041d0b403c0d050000c244006100320300e041c3d000f084003000700d03003840c8100d00d01a00109810f50074020b80140c2101481c10403c0030310034059a0305c031a003c441e15034501d40204d0000b220000001558021420070400909116076080303140644003006030305ea030340c482c09410300d4506036024401c2e07000900903c0a00d543c22074400c2400003464188141e0a0842d409080c211a01d031010340f007007100081404002c3c11810061000b048040d1400340d85142000f107054490700000740490340c04170a05945410404c06108840c01d036a801000d05040d038032258805c0b40c20b541d91402103500740c130601c20108080ba070800d0045010940701403004202c81c06c144001042e0340300140c1101d0080d803000c59000881095920140b91002c61440c103004103070b403211503002c040c04130814 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 473739901 1250 473738651 473738653
    0x130209150604090b0906040903090b03100905070c1e0206030c090307050d11010207080f0a060c0201150308090a050108160c170a050304060501170a0212011509050109051e010509070908 81
    0x40c00640d80302c036508154203c1c072040341d05d0419a074800c400c0c0800e46040300001400a100c0d640180044000b0710051504038000c440a40703002911801e000d001c0b203000395100300100300f45c0c4404100704039084417130302c040340d140410000360b116182c2d011030250f0002034014000382c800415191400e407010804c080003000001c00d8000848503505000d1403c04c0c40504d41d034014065040045909100018080700c00b813030017030003002d080e0001d496040017000300341c030781a04554817090400d01e543c0442455002460052005a5403680104100710f007600c0e03e58402818052020104610704550741c4d0000d8622103c1d040428001c600d070f00e42041840b40c1481d9891b0014030200700c041c25076601c100030710311541c45001c0400032641c03620400c510302001c007842d12080303034451a4240014200403620004c20380424001051055186900740e4558070160000c8100c5503a41c1d00400070b14150340aa642c201d68a01d9a1b0b010302c0645c0f00900c0b4820405004031400741034520041511139101e20822401030138140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 473741007 1106 473739901 473739907
    0xc03390c060a120218040b0121021305030303160e0f1f03020d0603080c07050a1208091c060b040507050301180e01240602151302091506 60
    0x55000b00c10041402010b11001040c2d0000e1720f0320b00721240a000a00c6180c1c1d00340310031200316040e03e81c10001e440c61103004080119247c00310a40d503035070015035110f40c03001ca655290f0300303164003898144c030000040080d03c0c400c0140c0854501d54540d104000c0704242e2040013400105101032a50241e100c2c0705121500b243c909581c2c03840c41090401600b0280d510072000100ca6050740161501500007802d031410760003c0c05001d01400c0100d5444841c00d0401e8404501d0225000e00113100e80ba00154011541e501c03055000c040d454881c45204d102c8543e4034082e4003034079003440d40900490401300030452460007603080e01c0c10b884d0440403c0c00b00c503680485210240c95004111103841d56a11203080689040d119211400380b91007180700115490204000d16220000000d1109500c03100306020b80074007441e0754100a07980484034107a964503515011448070078000001c2d64050800 = true := by decide +kernel

theorem cover : BRFrame.Cov 473561151 473741007 := by
  have h0 := BRFrame.cov_init 473561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 473561151 ≤ n) (h2 : n < 473741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
