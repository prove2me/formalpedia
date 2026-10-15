-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:39:32.305113+00:00
-- url     : https://prove2.me/submissions/9b0be83a-98c8-4b6d-92a2-151cf7ff6678

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 742805755 ≤ n < 742985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 742807005 1250 742805755 742805783
    0x708101701240b0a18050d1a0123010819050702070612050105011709120c0a2603070f140d050132120a0203010207030c05070b03190b010309 62
    0x103401c03020b01c4004400d000200300d40306548044080c25a0721a081da06101440342c00280e07440ba414100300c01141080760b503102900c51001928654545000301c0b4804014007501d6605100c0520309401043c180b0030404003211141c140c40d05000740704081030704000c0301d0b100041c040418408a8900c044107884100500c0c506040080d50b2040c06005460201c0c2c2c1c0c00c4aa8103504400e40141d506864041c2c0d0350681d1410000e41c8174200d010050246411801a48200c412040e41880071380103860303030344000304500ba00d1030806002449080d800402201c01c08001907059070089030440390007201d2440c1005c200001c0c0d440c00c50f4944101c04010344c41d4880020f0b0409003da081d00103a059825104038903c44d88040e071000f050b498480100d6500c64040041c0916161034a280214014010802502c00404559001a00320392003d08124042900d42d011002401400c02140000d00102d0b40040c1c51070414900c0120400d030703000f50f440019900e2790400740c5107034400c2e0000065a0380c401264000c0c1c41c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 742808255 1250 742807005 742807049
    0x1a0706060f2c060607031115040606140405060f06030907030f030306230a0303030c0e040216060b120c0405180d09142b0807020604090501090c1106070810 68
    0x503002d40300d056000980c80340d0101501290a840d1809201d00411041c03030104599019190641d1440c0c1506c414000e1102c2d90041011340e03211b03544250b115840014605080c50303005444240e802031007038040c0e8549030400c0499207840031102040403041b10b000380c8035520082d15916048894100400c0005417202d00001c054060b0024000d4401c10781c0a00c405020301c42855020003c0743c65160780c48181d211003000403030f00136800400d50400c9460520110f01584010a050343d100006a0b6488115241c0d208240704141c42101800c000031601500c401055401456645004c40c425911445da02c5020402c2001c8450b07000b80070020f510160b6400b2100c410026112540f507220758000b02c1c1c0048400e0303000c0c2c94568840503100800f4645600300100f1000a500758141244040f103000b081002003601507500c1c48080c00040c030a840d008540342d810991800242c0e009410464240501c1e4220824140c801040407903008030b01d850032841e0f035074070303800f0301c1080d000030390720000780043c512103645410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 742809505 1250 742808255 742808279
    0x11030c0a03030203120a09020102060a0c2307020a0e0705030c0319050c091e130b0301020c03040e07030c0e1c030e041526030406140d020d021b071a0706060f 69
    0x3d4000c2c170040c00f0303d5a6400880c4080d1481d4a000900607040f00c4006280300b0340c0c6a221000c00f080924250040c5182881c02050f8025290f00b010719211000c1010011880d0400702c41c000703042ca10b08120300c5402c00d1000541035001c060424420f4560100000b02d40144400e41c2088140001c201848a81441c0b42c402d48954460440c05004019285081e40078a00010f0003070448407020f4103011034016400481c0f40107182c10307110254036540800c0070b4550340d07a0420191025106100c80043e503400d2240010741110002c011403c1401007105214000b0340c0c1d02078426400c1c44212030010840c220394501140c0882002c102d055000386040c400802d43c0c8110352080c0165100d50001900ca42c0e980710800032004810950310f0789076031003008240410380c4900c0d222240070000000701c60502d001c00c6080b105903002031010110090717010641988600d800004603500b00340007406080c42a09024051482100b001e010040401d80080c40504200003588014010701c2864000b082c03c503200c4030314401e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 742810755 1250 742809505 742809517
    0xf09060d0204031a04210c0f140d18030807020607020405040503030907080a02060901111005040605190c090e100302040504080408061f05011803050d08010501020712030c11030c0a03030203 83
    0x13002d094203411101549002d10414061500001100e85000310041c00300000d900042065041041d4010f0b008001982d610200b4040752003003840c0841c0600988001c2e00d042d640300000001c014610b5035481c1d01200c0c03c0c82c1541545d41140e5a141c0e118481d00114029100f694402500303d40383c501040107102c00440518003c6206506403041607540303a600c2e80d6540020300c2c0107580700f0020043d100e99503020347c10394031500c0c100c0c60a075504144030845030b004070764084a064407010345580800800010307600e000510490003680c2001401000301000f0b100382024094040102c0310f80001c034040c01c407205443c5004540c010000d100c5860945800d0041c0d801a126000c401d100e140c011070819001102504c495112a450a550359403a0500440b400300074511500400d824544022003c41c2082c49a000e8807441d58441c4460ba500d80b00009241c0080350340b00c1c6070300480000740d030800603074401014524a83c0011568101600d25400203051141e04074296510018590300002019008006428 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 742812005 1250 742810755 742810763
    0x204080f0a1709181b0304030201020a0206071e2a06060504050606030f070f03110d0506011205150409021807020a14060f070809010b10090f0f0b03040201050f09060d020403 76
    0x5608041c200292800d00501500a0380a52044401e801135075180305240d922441d0849002141500e010640000743c1c020340301640181d4000417416103840e010041c0a4010040317180c44000300696055000d400c100240c0e800041103688401c042c6020607600301140c00c00542a01c1408810307007407030f060005200034443c65000d07074200340000701c0900d00802500e204114a401524590307465100898801c05624040360505039110803400e00140d02002903d0140410440002c050800780005000d030301114108003040c170706100400082c07414a420014181000b6074010451459a20009001418030000c056070310701c00c0c00c1085010380e030025001d80f07000e0140c1401070a18000124030391300c0d0b440440f2801302c001a294040390900c0c2c07082002075031040400000181c0c01d80041e0010b0614150150b0120010b81c2081b028030119085078120b100805204025114192820b03244076601e010050002c1d040c0040810054042c0422000322804070a000300403076039034003140395108029001400161 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 742813255 1250 742812005 742812023
    0x1052113022110060609031b03080315040b090408160c080109060501050a0b25080d060b0c0d0201090f0f0507030618140307030836011a090f010603050a0204080f0a 72
    0x40c0e014000d44c400d40c029640141e980740e40c030383c1c1591915a40400304d100c0d00f0040d000606400000301d4151400395000e02c0420510700584007442080005651222840e28840e41c4c2507018040020302c0300049510040710b480d42400940c2d41801c0048004031260f000c010f25508003030041e0700b0010382c2d51041d8162001210560720072920f60000201c6801200010110030ba030840e04c0588042031035066005842c854441c151034040f801c0c840b03109540d09548960303206000401ca40610003c140a40070100001e4402000b0150143e118a2441003e00c000949081d250950980520000744520340103140c0203103003840324a494001d540c504290a107015100702d42800d22070383c3c0128001c03040f1042030350941c0e1440803540700e80f01c2c491703901d40ea41904a003254503180381c41d078102d00f05050b0104808038001c0c000500d01d60080380203218020741641c014841d011030300810903c40503000308141510450b02d00011540c0d5001903c2e0000c0c0300d5500045240d11840130300c0c040b110000152020064071400c0c4075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 742814505 1250 742813255 742813273
    0x3130501021c0906030b1c050601030b1e0a091406040b09100e06181c0302040e0105040e030d0209270403090e06030a020f131514010521130221 63
    0x11882142c420241a0024600300020072016119401903150604010080f41080d02045881752010055603400c0390729801100041060058080c51241c0c00202e60101c454080e80392500d80d03100c00401000d9540f1282d48580750000c3c0164081d00e03070b540b04100d1040700c40300d081c0341c240b0038240300007250a0b01d03292180074007201000e0490700500c0c2140c0c022800800301519040400100c040580c41d80b25820b01c07844410b504904006810303800c0300c00c03840d180142e440e03051160607800954140c10141c09a814800360030042d02c400021501182d00b141e0703005880f100804001411248042c4030341485e000340d0704c3c02c80d225900e11501d15002e1842900d940b0860750340d4403d040d4200d482164030540c540c108000c1c40b809420007100406801c80010b2010341c9400b4001c8018040f640b04000c4004010302d0204140300100c5e0600041041ca102401c00e581482e20b40c1c4059010544000c000f40b1001c160340780410407030042950b0304407600354010000c400741e1003060381203100d81d4800b086d072803814443c0d0541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 742815755 1250 742814505 742814533
    0xb0d06080c0d060c0212030a14090309061207030920030f01060509130206132408040206071707061103100504110a0c080f0c03120606090117090c030313050102 70
    0x10001d010940030b003560840b600c941e01d81d0780003000b0544407071003540262848800040a0304004622074030390404002072030f82e446041003040030401459440c079a03008010550881c1d403100700782c404c441d204202120140d500e80380218040c0c10507480c014031440241031144412010764041d030040000603070480d0303003400209140f00e0a8a032544202a08020002c0c003140000c40243c00da01101c90010f042c007454890074041800e040c00b0664402c40c29900d4030340425145403030a1100d006000340c40d2070b2544441c2490340001e103035842890700040001065449020720b05600c0c00c15900d050760410b1007000b494201940102c5140e0044401400c0355050700404900752620307200e520b01c0c5200134146681402a01c1d10107550002c03d9240c2599144014014501c1781c0590318004d050888178107000e5600e5102d01e0f82541c1c5501406003856105800602c141403030b50340d0109520015489030035038480b840c0c030384801907070038460403200e035540502001454080d03c200101081c400c407070081c1d00f26043c240d641c402c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 742817005 1250 742815755 742815763
    0x1f050717030415020f090612010812120705030709181e060308030f0a020403020d15060b121915170f0c011b1a01030b0f07140405011202090a0b0d0608 66
    0xc2d00912158078411240c410126580c054a014641400f85d0b03031900080f08001540390304081c051243c2c01c003001d0014420b40500303001c1003610245018009050061038000d444000381c0003070a0340100306001c0006590319100342c1181000300301d8024030700710803200e41105001802d0364000c0380403155090640240e611489100b8070080b40c0d0454480c3c1c1c20341d00d62048001c1103217005012103403070907020301c004005a48e8401c0017203d9503206103d0ad6440e60b51180466054504540c030032000d01c4424010640c1441c039101c1c410f503005459054428904a840c0c0a0000a008040307982400440860010801e801d04a0303207201d40b01140422071703000900706c4d620300b07030365412003803038580010480900c490111407400091404180300d22008030b1500c3ca04080d03044040e009a0040d10100c007083c060000351a03407030b80715030340107400f48c506054010706c0c8809884c2c040c400c900c280790400000075882c0c3d0992100d5070554000e0300c0010100c001265540f805e150580c0c11010059958500c1c107a800505518000707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 742818255 1250 742817005 742817011
    0xe04020403211b030c11060c0a0614060f0105070c03080a0c020301151d041401090312140709271a010212210a0207050d1d120a0803061f05071703 64
    0x1446815030041c560b4121760540c29444103c0d00003404c224407041d00d5850300c0c05440c1c0d2604090007810598500e00342881940c4056483e00075810707141c0c0c14010103844e12031203000002c20a082c101e0b075803003591500702c1709810300341d1010f050490081455002310380c1c0301c4051618580210028800d44180c0120380c0e41400d014030940c1c980b41682c40100b504843c4440c0900d5200d40a072141c40c0c2e0003a400c0e041d150a5401c507172400c4002685008601007005154841c03110090341c041c101c0341c070514028101400849042c0540071040403c41041d404512850a07041c440d0007105000303122045072403e403020a50006100e090142c0907103804071201e01804001c0e100405404000ca030301a80b944566540c800b0005040c01c4c0e00389400f00702e482c0100ea410460070318400816610419008813241c0401e4201d02002010b91054400c60036070541050001454180180c020000c280d890304c5420024000200d0202980c0c19215000d24100e655500440680301240c001d42e41a440c00a00345904000f9210031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 742819505 1250 742818255 742818287
    0x5010f0801081009081b1e0a1109090c031203090d020f10020706090803040f060c020d0503180a0f0615092c070f090b03190309090c0e0402040321 64
    0x10400120540c0d500a402403500501e8664130740211060001c546c80d010106d21805a0701240b1002080182c0c107180da58800c0e020030280c40c13040803030360311040c1d18040c62200c13070b00c40c600c50300c01305810001c184904455444000c04032026003803840940740090f0000c40c0d081d00c150048031102400340c0d00115a4800d00c042c20400740000042c00c00d206402034000b44426204642d83d0b460140005402d00c006600450003074100d0351001505103000b10644500c0031000d41150028190762404c5600034003a42d40103241c090f008800d0041c181001e034609244008042e114001414102d014886503500c0008010b64403c000714040362124a4101500c91210526003903085a4841520181071541600c461342000d000752000c1503903801c85500510510f41040d1142c60342d07481003051500e820800034424205c1109030b01110900c54801410b0a45140309800400d51203a0072505038034420740714290803080041c0700315181c0741ca900b050414040c060b40c3c684418a00b108031002254000d0100c0c030640021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 742820755 1250 742819505 742819513
    0x4080705030c0103180b04030c0614090706141204170301031a1b03071116060e091003020a150e0d030302072303030703020c0304081b03060c0405030a030f05130f05010f080108 77
    0x590306c0018490000b0010f42c1003180c491051000601c00c0c1c09000d00401218000040303904052030b15608000390341d030058040c0b100c2e550f1040e0100c6403d40a403444c070035502ea008130042d0344909000a401d07418140100321003800000100400a500d180c24a1b00b4510084250041d40c0d403006044c1040c3c408204288602000d1002500c0c180c45138021102011504082d0346244881c3c84c40b00940740010b4110101040e050700703a02d401402c10048507a448506548184002450341d00401d91301c95590107400000c0da52200100300030341c0510f1501c4800d031f42c068200c494000540c103008000707401c0004126003a070103c90500d003e400340031046191040c0b2041c0510300d1501c844506500030340c425150f80a0a000038407000580d040e050051100c001c2d50344903108880c2c04413604050034280020903401d00800140020b11141c0ca000a030448481d5060074103c1b59021200d0f0306444600035405608404140d4040100346c00d41d1110711202210360a80340e013a01816450001d540c5403609000714144c90340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 742822005 1250 742820755 742820801
    0x4050a03081b0a0b01091103011a07030c0507231e0603070e0324060a030c06140405041b020d1121070b04050c01020705041e0b130204080705030c0103 66
    0x40c070308000b80344250780000e00c01100003141d060070b400d000d8004002e903140c000b1350300108400080750040b0081d168101203442d18541c10103020032000c0c80000d403600c1c0600c42c0820310740d0415005e101e1528145401c9001c694070b16a82e012504d0307080380904481e40840144901c0000c0904040041c101c003556080250b0f04007840d0507007031151541004101c041044869010780115880502c40d0940040340750000c1e45e144200500401e140001c00360040340121030807c001c201003180e040041095a15030303e0302c9540c5494150700080940101d4100300d03070061400c0c0000c450120381000c440190722040c0c00352268000d00000644164035095402c543d02d80040007141c0c004102c060300c4c42e007401c02d102c3d00f082c05c0640940702c0d44080c1c0f004540850300ba91245c0003500c01d641c0c042004c4401000704032400e001e00c0b612941e40c598184929800500e072161114080b955a030f031610301003600341c0e0344c03c07008640312079a904100f55296517900c5100d020b402008080e500652090140a8003051084e10714582e00d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 742823255 1250 742822005 742822013
    0x90d03050402040f0e0303060901080703150c0905090705071109011d3c060d120806030a05010c270b040605180901030c061106091f0b0a0603021b0304050a03 69
    0x3100080040f6481581ca0751144141d00c5248290640724201c04011600d130318001062000c880c4c010b070001206580613410800010b00f0325280c000d004114800085242d4208101c03e07611044d117134200c0340d40004140104013107141d011019011040c021442190030000e11300a00038a13030f800380210003040c1080d54403074080190000d031054206502c910400d40b410b0241402100e1441c1c2c6d14024003d5051200601050400f03001805802000448181e401c03d11542e9864916401402404050100b088002030a550b0280100c040e51a0418028402d4400402004004090401611010750303021f50b82c2c41c0b1410440c07035201c020b40d03205e107034050318240c1020340580322504481075020b0003112070000305000c0d8a0700d5071030794029840703540c0203030b02181040000307090001a0707419481c03264440e4040050008000907021403160f01c144041e280d4001c600c3c5610054103041c12016085140707410000b52166050b13000708501072004020340c2c1c01200301842d03070b40c0380c1c0705501c2800d500c44c01e10101030000c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 742824505 1250 742823255 742823261
    0x4060e040b070e011e02030f070f022e0e0f0a030305030a060603050c04060804050a060e030a09060516020f0d061e05061002060a050a0f0c020c0f040b03300318010c08090d03 76
    0x4c400076004403418102000f403907823a01e41c02200111790074001c0103942011420540d8a80101d114021440d5200f100d181c0c0103500c4010007245400100600718052943c0f903262011080f105503000b62214900c2c54407402c01501c2d5034801d0768a80305851402c080061002d109101e09800342555041c0d4038513040c50410119000c8101810a503464001c40c0440030018076070b8418844038155031400742d5210201c1080c090024100380d40120b00780716040040c0d4003910010340742c070441c490b4116043c00380f40601e5008200d0458038100d00400300c1349410050000c240441c00c564404d45503110052020f03665000a10009443c01c406c0f08000d0703400100400e015029a4025a50101e1041c82c00140695001c54610545850804010141c1c110140c01c2000f030409582108100c6000c0c2d034180001110040843e903159130310046020001940043c3c0c00010441c1001801411004840d02e41c907401c28402c28486c050709071088201641c44c20503204013041c090b200007403203907115201800751540c80324010707409 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 742825755 1250 742824505 742824557
    0x3270e04031e090305011419110f0d06140d0f03030c020321040611210c07020301020403050f0705100e01030c0909060602030909060303032e030204060e040b070e01 72
    0x10700c54620a00308402c29042802c0c6081961a56500100c900e507080c03140c2114a5143e021854082040070461682108030001c0307500800003000140d280f007031501401240c040d103140c0d07003d40040060311200712080f0382c21203002da401c0c1d666444ad400c0c1c00c000400900700d03040d9000428a034109003100c0d01180c0030b60303c495415a03e50058a1525048142205003003409400c41c103000c0b0011000d0105100061140104c2003190701041c0e441c02200340400c4045812f83c5000d49801c03000100025840403400c0c0c04d03250381c60b60280096445907102d01d040798035007040d00c0f006026441441000034451a003004100600c0c141d54030381d0880541d610b40114050a84145180305201d0550030019a17400c5510a520003014260301550b20740402c0e1302041a011000303060f80e4800c0d4014030a002040d0140c01201c1c5111294180000d1843d1000020301070320b0b14180d05c060740c40b9140c03801c0059084250903200b4810791181103050103503510b000b826690003c0404649001030340e420350010900442040300c0e58 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 742827005 1250 742825755 742825757
    0x510050a020106030c0f14041a060705030708070b010e0f06060702040b01021615030f060305030d1503060f02120c030426040308031003050d050f0304030e04090f0f03270e0403 77
    0x78a0b50b1252100d45d80103806520807120200762402c1040803841c5071403c450207000495003840464401d428403200044000c042e207100f00c3d00043ca4108200042003141e0001c3c2d0b2140013181c03151752504203658045800d21807091380890010009482880c1111410700c44e20004103d0b6040941070b03000e0000401c03003001e601d41540300c0c11500409a08820442c180104140301049441400ca150007c080e079480c2d155800920341001018030000c1ca02009a0b840c1e500c1d549400101100303407242600e1880d8982d84090a0249880a803841c1c6104680050004602c6c51403448425240c0711010401d91004880c081d281411181034444051a1001d448000c1501e09405031300703140e242d4443c10030719401031752651141070f5100020000c0000a122240e034508040c20070030704202004000b5990783c40000e000508120492102c0007044e5256409041c0b480d0300202d020000403d14984482d003581c00d04000d801081c60340c6c903230300c81480307910b030780100f10182d03030461805084d14202d020481d0703080c043c0c0224 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 742828255 1250 742827005 742827011
    0x10e073b0a020702130f0c021603140a1208060a0f030b0403120b03340608010603050714030901050708160c02010c0f2a0b1213021f0c020f04060510050a0201 69
    0x700240c5e840d40c0000c1d41c010155100051840000120101140d8502403408159044402480d0500841580d02000c8a07040030710b03000c2210414100d1418120401001002c48050700d0b00501103c1e40025240e106a00954840024607143d11009003194911f10009194071a0b02c0005000603214840c50b00c01207004a0000c100f1088600020b07040c85d0b80302c6844ad51800c90301a2549410a00340611030966016114400c0e846041440c01049420140641c0b4145501d40c000b2410840c404c0d40c10b0307001032200404081c0c5904203800c406029040a80b002d0001074510b001141c40482800f501c1d5090b403055480d00141e5414980c015a03440c0316910003030311030504480d20080820100404060080703c20101d18000307484000030445501d4607500804a118003e1000105020f43c44d4401a080304441d5151070080401d0710001c3c640d8a51440c807121200c0351a80c012403c2c42c0c204554607038440c800c50764001440a400180b1049a0b0244a516441001d000004040300d0040000305603e100c584004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 742829505 1250 742828255 742828267
    0x605010318110118080f1911010f0e0d0605070206060a061d120a08040302030f060f0118020c150106031107080403021909020703050a0306060c0f020405070908010e073b0a02 76
    0x116a0a110a13444050f1785c0e00400a00480c0ca44207000056003d042812000740c000b4484d125040100042e030552414000035100b0714000500800d042c0b25940c000501400c0282c0d4645000c002034075055a8100240c4211008116240b07421110306041d6421540d902e04128503854024a800c4a034031082038000d0b15400da51040548280110141e49000381e807805c0c1d50707a25510503d8034000c240002e07540141c1054090160f0340010030702880c1102c15580ca000c2c92107088060480080c82000c81d41c400c644960b0301c101d410183c03020681030403a82d050301c0c2001190741c0c1d043c5828492140310f000a181100400041c001490f14404044400c11503000c245c102e552200060402c0340d2000e00141c0200c0c40224408544680c140034020161219182c040c1d05044030b079480d01c98005a0000c001e206640340d0002506446c440d0410b103005005c081c0c024096200c48502c5c0548691080c040d400c11f142000401c015800709043c1d1510024a000500d1250041c9802181d444114050a01d020b034540030040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 742830755 1250 742829505 742829537
    0x70504081203040c06050c1f0f0903020601051908032205030307080720013c09080d02030a0207060e0301060504020f130f141201060b03100906050103181101 69
    0x3146001e20a104600341d03a4280f03801c00840074416075001c1c07070030071108000b040c041420101e5401c040360260f0340d8000d214842e0102500242c2203003500003820500d05500d400c10300d035000403024102c8005959142e8034142c80e11f200030203181d584c001c607003141d44108080c000c02c1400312110440c010030b0003c05d21078039440c1c400090550f03001c90020b82d04000049401c10502c0ba5030080d84580080300c480c0c0755905800f00d80080c01418441c04a29080160019010101440e003c00c00e40540c040a040700b031720703a80c035400103403c0407818019002030707105500305334415030b000204a50400c0307001c0e0001c006103860554201c4074150081c460030b4240d500e0380c1c0c00060381d494600203002c2800310200007a0310b4a0707284000c00c0719a400f580c8405013841c0c0e81b1000300900010a030850700b4407141507c040b081d84110a040c640548520351000c654458001304000805104034004002d440da14042445a10b0b0348000450903122018007406254041c44061000681000c079100d00550041c1441e031542146910 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 742832005 1250 742830755 742830763
    0xe010c051e0615010306060c03210203181e060f0702150106090303170f060103020c0715031e110d0911150a020d0306030803040f0213111e030f0f07050408 68
    0x191629580c2d2050051000c01e4035008811a80c400081c0390401900380707040300042c180c208164010b005c1c0213203903c00b149240140e0303034a88541c0c808400c0666480c244104160300075009110050300c54012855002e101001c02c20a501d02002c0c2100284881e40310b0080c2c085403000003524100c04d51061090b006d4510b10b646a2060080c003d5842da0294146541009001020145100c4a40306000000c0040074584025940d80103082880c3c0140c075940c0c0c02e420285408902e0b00100480700c03290b40f5850a2951503001500d1810404484221680003c00278034152107001e4014070818509101008070300740f081d801481c4050041d2104e03030800007004d012035641c01d00381c4548850a040001e480319100d40400c50308842c20214070301002103030300d15290040c2500000d000240350710003051500c0c056694102e01d0141c0b24000039020041003101700006409079028032590805504c00c2200d2144455100041e68071401504e03c5124445d69a0368000c600d03403100a24020a001c000c4c000402c544100b04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 742833255 1250 742832005 742832053
    0x7170f010f062d09230114121c0302071509030806042007110103021c0b091005092e0f18020702010f030207081c0b0907030c0e010c05 59
    0x8000000c149080000040001c440d101100c08400802c201e420000d2011003c9501101e0303900760000350885480000c420080400351480e4031482040d0004104442c00780031950304010200c4410729140c580c04611620741d07580302030344011122180000b9000b640a42c00401c0d8140c03141072401402803c640c45501185e6121109500081c40301e020071041e03050034440d1f602c000390100344600c154007200303048507954440d407180103100152100d90650380c3e900980580d00046400400c4c01c071034103901c41d21240104103680106108802e0f00d07010940090032443c000080c3c0350090201000341c0d41c0c9100da503c1e515a1803203a842e0311481448006000b04403c4d8011019103e03180c00034020a00d48500702c000c01c60342905c0d02042c14410440000183e80001681403a98494100543c480003581403010003401054030072a1040480100501119526440310030340c04422680240c040e140c0040031001c036801c1d2071055000c41d01c6011035600b0782d8003038070014000790310620856007a41c1c58040140545d55000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 742834505 1250 742833255 742833281
    0x2061f030807151b0e09070206060a050d0f0c0e040318031a15030303070f021014071818020d0f09320111212502100c08070201060605070507170f01 65
    0x11045d00b80c1e00f4900032182503080741c141d1005000b20b080c004009020310100303105041c86801034940002c03c00254068501c0500d400200c0d035101c00d07591b0641c150048804481c01c40024401450005400c4e030308035002d1007075a80001440650400e041c604840301c0c0805008100726074440300b03103118645d404000030351140740f0703035600e54250500c1d400002e46420115a40c00d0f1100b803e04040104041522038074a40c404130900e00450481382c01500d09207104c5054201751403106140301e4144c500f08603600100a003010000e0200f00c85100744501d4002c80350000303401464a004214640c0620b00001c010084d00003d15a4000c51559029031450842d502c030b01206d1f10404c4042112001c50100c2ca985042c440c982d0b9241e92064a40105151300b990701d20002107a04403505a00d004410740300704404040c45848050400c801c058862014204240c112841d02c015800c0c075001080841c8201c00f680c0690368040018100b25080013407030101c110000c0c04001c00780c411800c1947c6410f00c240694041e84001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 742835755 1250 742834505 742834517
    0x4080c2706221a0a050d32070b0720030706120237110619111201031b03020d120e1801151e0c1e0302061f030807151b 52
    0x490814800040703503c1d817000d0302c111503000e9a440424844080c0321041d9070240281a281148100414002c100801c0c03c0b4a00e88120040424611000310042c55a14001c3c80e00601210b0705a5a11404910902c0e00382d425030800b500c10007410b030043c042d40c0e034103c10105000d410000c5c010150a031710101141c0000c078440146045031200807a12000c00e200501500d050f80e4600765021b2410350303904001c0c000a10342141c3c04c100381c80071210b03503205507948004015290303a0741c1101601c03040c07030160a000c01c1d62042e403503d8507031407606091200b80c0c044030b50280800074610030301e40f21000c6c808610300c0744070280198100d0305000c030f54404401b2000010a805020040d5051645020745401c1c0203900d002800034426103030b40d05218440041d01c01c501103180441d80701040b403808106c00008500c80c200d540030081c1c03810f400c1540100d25a4420081c43d044541c2c0740358850700703c8401f61441c1c0720103130003d00d0810690010441302c1d4034441410105078404620000c40103034401017030141c08003030300015035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 742837005 1250 742835755 742835801
    0x31b0203031c0911040b061803010b06190201050f090a1704080a0507030501240b1303061b080907030c0b034c0509070507030c060204080c270622 64
    0x202d904d60b41290001d0f602007041000700c0700401c80341d21500081c15410800b100762000719035000d40204416000c06030585413200c01040d03400703a50f0440c000218001d942403000040481130003194440c8035040c0b01000f030140d21100c0e240c480c1d4142200d010035a50407010440131038450030801000883d20710501c010403210b07245082490841e42041d654169003d040100d801041c01c00040440544505945255445201e0b0001c129400104c0d80014080c50910800c0094040084001281300525807600f0030075503228071109403103944071f00006000c006036050a10802e150100910740c0458824860054426109013800c0b0000408850b40c510400004142511407025078030300010303100c403000d10384096083c1800924000e400800b49810440701149400a0620a68004860a8100c5400c40d515902c1d40341254880f10803c0030180180d04c103002110101d8042c0300c020380c5480b00705140031440c1d154042040310164000d00d00c070340112503c1503600480c034081c3c03145404880d804d0a411940754 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 742838255 1250 742837005 742837013
    0x503060412140306030d050a030f0603030e1504080a0b420d2a031a0f0108030307120b0a05030312010e01050604030302121b070f03060b040207031b0203031c09 70
    0x442c4641c44031401c1109205010300c0d0340700001c0c4106000e2aa00b091502d8075013440088000f814000102600241408d0000080c16003100a075440058103440140c0c8030031200401c4801c5114600c43d1070f840340e2140b000304022403814503210760000307c00450280025840d00002040d50b1150200c84580b400d02c2a905a007100c0000414900800c20b842a48500540340c0741e110b492004141c0c468032400300c2180014050071020b070501d001d940d200704803a00201c00c00600012040b81259560b8415072030320004651420001300382c9103d00c1c034035540c07440441c032403100030409000c20407089600031620410101e8141c2d03050001d441d091909402c0d0b54050340c9000404004c404060380424000c81c1d007004140082030f40800c800c0482c44071810040d964001004298404012000d6850150f01400c0001f003401c0c1c8001e41e10700b0886e80902020711031020007504100480c031070030f40002e010842900300f070348400c0880d04d0b650711880c0c0028140d0f4103001c10309031a03070f000c1035000c08142043c942c0c0340b031980100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 742839505 1250 742838255 742838267
    0xa060509040b13030201020c030406120e01110d020a0504091a0f010e101b0206130806071419020a050303100302181b0c010204150801181b0e0103060503060412 70
    0x20802150000d8150909071196424544003500003400007030ba1900400c14107000f501207502c03801018080326a9165100d100510003203201c0360110a4500f008403c0c046c440d0305025240008488800d001c0c03900510700c0d070341c0c002544035802003002e1103028000002d0540f40d80c4200600c100c149000017030f9595407401084105001c0c084191305104c158110000301d619411110050303500c0303a040c0580711119110012101007500d01d002075002c03400080f009004460b8001100896181f14200c03101e80c0c8801c2c5007684c4c1d4410403000195031101c10302ca60820814041e030401c480354070341d00541e0102c1e401601c0c1c2d01d0030f41d4800c43c0c10031000940200200700b141030620740010104015007900000d404d0800301c45848a00c2414040702330b18002c101c40c0c11038542981214028000740299880004030014054500c120900c00c001c81a8801c0550300002012401038060000780e00104080d150006141920404101d40b01c0604040e52040081810b4800300402c0d80100d001d0303c049500405080801401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 742840755 1250 742839505 742839509
    0x610210518010c1b02010306050d1202060c2704150b0a02070506091003050907080609010b09060f1302030c042c060a1a09120d0c12050c060109090f050a03080a06 71
    0x41c3e1400350f2960314642d1003101a51440302d031a01d1002d04c0031103400120301a00d915005285d000c51034012030010801240d07012409881f803a02a4ac440d0341e0741680035180344c05000381441d1100c3c003400c1c2e604901d00900c3c10007410030100400000d03a001480c68a8030552900750450320142c44005103200b842d0b82c0421651008020865003a4135000a2402003040b61070b02e180c606044c99203860120b00e1901081c40701101030100f40040352400c2c41c0040b001c0b800307401e80d442481d02030034910700802c0042c1080703031641140810140410880b68112101c1000940c001080700032058030901c00450200c24515076a00c8404d00004d0000f0340804410104e2903100313010309401e1090700321803410040b031004090079030409561050b00b99110418040800c041100e55070401c401406100c07007903d820354002009c820360314000e25120138610082c8806540500c034582d003806466200134010030501555802500d1032a20400300c40540c00c01c42d0341d030240380621011084000c50000000c1004540d014410000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 742842005 1250 742840755 742840801
    0x5040909080c0604050a0c270c0c0b1e0709061d01120e0313050a03020a0e07050702040e010c0f11151308040608070e060703080703020309071707061805010806102105 73
    0x3103801600f0854075180e001d021008d603625201c00200070703443d0040214001054014047e619585800d034821062014020382220030304c000300740450440382c4034010107001d941060319842c07103c007000007815511300120140c4a04202c603006078160420044d001e0480841000d0b0001c41c0c03540071000b407142e03880160743c21586c017450395007904101507030f5015840d504461107080540880d0b19450011541c0b031140a4001c4e410904150000c0302c1e249056100e08400c6c9425911140c0d90100b44104884071042128801e0341640840701e12105100304c0b01000d50420f180e0945d040e0480f40c0e682d80c2c1c0003a50410303404100861020b4040103513164101c0070080d0f83c0a000c0f120140340c02d02907039000e010500041c101c6820198040005441d603081041034402402008050415031410940960b035210f926000b20000074821038500c09520000e0400072003034402c1619041100e603203404c180016a440f0343d03481002c1003550f030803041c0ca1001900e40013002c90042c00e0003068520b069400a910f0400380c1d81c90314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 742843255 1250 742842005 742842029
    0x70c0f08011409190b34080901051501030e07050d051e01090c03080714101a0d110f06071209140303130e061201060b070b100605040909080c0604050a0c 67
    0x3c8070b00c100c0e502c1d6400c0c43c543c80b105c140c485440b800500f50b8843c00c3e4252942e89141e002040750101c03034450804204c1d05031950b032820403990300c07454800d00741e490640d44403040c0f0001c4006500c0070340c00b1740c10060685038074100b218442961100021080d1041c40410f031411b0b00f2188038100d000f0480e50002035514044d0380288403e181d00c0e910020050154480602516004511401000340c12009089025916411038001020000b032420003080780744448550392118089001700c0381401d00065060f40c2e0407111042143c40712405120030042c500c103103254480b000300b041c800042d610700040b82c1141407a5440042850070301c45035801c40300c0070b4a5018445d5105001c2c100d5007180c40c01c40e007420303141a02015211500e9420115859070500f9922103207135424410041031592981c0701600d41d490007810040740e01d0311101e0b0607001d8410140942000a90104003c2c403005c030151704030f402070612460309240b07814802c014050a0000030b03601200c950b041441c2178010b005002901102503c1452921 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 742844505 1250 742843255 742843273
    0x60702060118060504020c070609050d020603191e0b0102100501290f070305070b15090103060203040c26100516030e03090a1e09021608070c0f08011409 67
    0x180d5140814400c1c5440e60501509421402180b0742040e0002d040c05001551900d22607602151540481d0003458001200d16000140901d02040c6555900c0e4025004525640340d64101a2b400142032440103840e94039030f502d0160503a0300b06066a00c28640c104000750696000c8002402c1a201808005e482400c01005200117039400d201106c204903810b407000c42100030301280d0401e5001e41c01e0010007400000c24010b080c5a040b070001c1c041d85101c0c0000302038941d506601035100c8080901e1484c3c018000c14014800100d1030381c0190f4219004450708003c01d5030710725130804400a07140d02805600301450300744e030070300d001045201d070301c0b801c10803040c40946170030325241c89007152040c901c0b81007546998044558000c00d10854058580107404510010744441d01c00200191076040350104005496000440000d42c4c0b00341d51140603894005002070351507481d48480c91b040311505031005040c151000031030500e0380c1d10303800040c918000003241e4030008011000004c5001072200e040d940005000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 742845755 1250 742844505 742844507
    0x10c020d09050d030e0a0b03090a0b06010c2a0e0c04050f150f0f0c0106030606090c03050708062412071d03030412022d030115031110090b130f050103200912010212010303110607 78
    0x1420848a0a07401c84ca8100e00200fe1040019403d41d8850b110418280381488040d0440c80c2c0104140c4034180e40d041c0500c500380741032041400e40305a28851298044c030410100c180740000a09042010006141c10400c200920a00b110794680c02200c0203651034070304114018231030080c20000742c15410100001c0c43c1100000e00304520080a0604c00c1d106004101c41c420a00480c005424600c0992640c94540ba02100c544048003910304002040141f6480f080070307a055042c00040da94051f01442c00d003407401002c00070031454640200e1340210307a851801d0490328503907042403145038410560140031515406040c21607408202c1000c10b000c2545051000c500701c9003806040c03600a4803010034040d42a1000c44810312650440344c80a074002903018485407070500d01409940c0f4405102c50304540c2c550054048481e5814039030391203180e00e503c8020424400020304900b00016090788419408041c4860899010410901108040300010f000789540300070700754107031480fa100800890a0604d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 742847005 1250 742845755 742845773
    0x130b0307080114130c0212031303093809100216090204060905190314101415040c090503010603060204030b0c03040203150a1409010c020d09050d030e0a0b03090a0b06010c 75
    0x3c0e00b0406141c88401105010741b01700324554030b20b80c5000d401074590a140110900d000301c0c804090303001900c400c070046200c440240c036424502c1060405800e1123520814844140a5038007050062150b060184581a0700d0b4807945a2042d41950301416a541030b44800f500b07985070641185001901c188414400c0d903030030020131400d0311012100c2c448000d115281c4041e800c04d88c4c1c1c2005004c0390346800440c810800004140c502540075000900c1078000c00c0c002000c54000072544602c005144028001e40307414076034801e101c4c15090b49028104c40d034a4801081c00c0d91040d5004695280d4001401c0050202c1d650070305400031110044280303141802c0c2c00281d5904160500c42201c2000400450036200c55035100c1c042400314000c6c243e2081c07070a082d000d4020846454420050702410034945081445050040180e40b0014401300c40702c2e4003070318210f035414134229440d07402c1130b03640da00803602e4211500514800c95007a8004e0060030864a840c510011011707250314180228403031081d0001d14121 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 742848255 1250 742847005 742847029
    0x2030a0215130212060a0507051216110706110c0301060503031c27020f0f1c081209071d010e010b030703090b0a0606020708060609011a130b0307080114 67
    0x203100c01c4894072042c901c07604010520200030352280229502903a08540410b4842c840d00280c5003c0015035100740741580c06205a4410342a9080c101c0f000606145021401c0740b00c1058518202030780740007006034a85880047d401c00004901c0c030402074a05800b00b0002a030a902c0160004e01c8028a0200400d43d01c1c0200c2c11160f25400280340b100920015a502c440381802d8400000101340407580b5205500800380b00c13041e8000c17000e5010b00c8189007001d5890550b01c0c1c0000d0411012224441319003000966801f1741100c284a00304002c0d0f80b83c5180c0480d07540500308070f801600e0302c0341c40e1103042d000b250508480000002d80342c5004114001a4a9402d81118515440203542c6e9443c0c56003100205401c0078014590b4100c00280801c3e6459584082c060740c120340c0031928907035200d0548580d04c0ca4110342055002498000610001844500700b890381c1c003c00080900702030700908a0f000e1004607030804800100e020003040401580300c900b40d40104059440803d02d4a40c0c0008a181c141045c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 742849505 1250 742848255 742848283
    0x180b01060e2d0907050c0a08040f0e0618090313030b1e01060f1803020409150f0b0d0f030e03030f07030806090402010c06091b0f1a0f040e070c170a08010602030a02 72
    0x43d83c0014803080c080c2c42242c801d081484103071341888400d40707041c0045400074010515100c0d101140070031001a5410468001e110007800c06142c142c0a881050325030500400c008840c0c0800e00c0b12214490003402c0e0710010318030a40c4c03061001d1030884803900140f1075664001c0609801c000041010381c2d009405154444031502c4c100030110740c0101816403d189943c0001d41091400c4c00000921085c08900b40320104e9409042c440740b0740014414061700c2d4011100c80d44a0080003501c000248011119460503200f8141402200344041c0002e0a5801c04c400c000d1040f64001a00d104241c1c2c8071003030b981e0090701290001110b040c90b80000341440c81c1e10400070030341d940c0c5103da4802d20625804501c0b20b5045000394136041a10303080000d14118151141c3d40c400805960707003080a2140c4400c0d1210302c0c1c402410750381000d1910344584000c00d070141c02d00007171044918000021441d00c0d907104030000c8030a26016034030344c16004000d1903007005030b0214045400a02c004240e42c0d80c0481e01031916114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 742850755 1250 742849505 742849519
    0x90204021b010605131413050a0c0b130503011e1d150f13030804020111010b060a050a031103041716080f04052125120303141e0406180b01060e2d 64
    0x7d80c580603103494140c40d40901140101840021f2582900c0c3c010182074449811a5251690342c00030f050907640c110b120b00c400345200c800c0b0f1985104261f4081141131348a4000740b01442c030508241c0e4240100e1307900002600d0450410440f2480c5c241c044550084281c0c190303134440c4071203920010920039011708000d0421103462801c4240201c2504039102d925001005e035136030755102c440c014026612004669000c01c0c2481c0e1500040c10112003a00c2c81141c21804580c2448940082522a50312604200390500720700d110078008103201c5006010804104281242e50300e00300b90410410034425074222640e50020804111079400128a40b8003003040d501480104d004005000d60b031112068024140208034940b94109250b4507070041040b0142000740005d154407141201d1811400e040790b03d100c0594150041400030f8890780c8254590350b90100c00d001520110307911003000f04000c0c2c0c041c0380041c15a02d60f41c1103d142c1044903c0361203000701f83d1a403003502c80c0e42d4440b01e90340700040094400c8034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 742852005 1250 742850755 742850791
    0x5060412030e0a26030306090417120c040f090b030c0f012001091103190b0c090607050f010b060c070504050402032b020709060e0a090204021b0106051314 68
    0x8091121500441002058002d9203501d4440321090040c06484c43c42480d1407141044802000100c1200d00800c0050030050a03580d903034a034148202812004500680b1041042030320a00500b0082802140341c40030b0b49580314a00414100b000f601c43d048050420b240c4010f4601950f00059440c10302030041d14400c442c0d881030710050f501220310000d08103206541c41202c8404100c103500540181c0c2c4501500004210741d041419520008075500c2460700c42c00c00036120105501e5030080b0f60007048090914505010000480c1407034221180c200c0b80d03544104144100c10400b80a80700841400365a40e50070280075003441032340d4106d1440744500a6507500301007070641d18240200c1000c030800318400255800714a00c2001520102d0b50580f00600580c5408211a94180980710880d080e540308104e594079800c40801c02002160400c0781d1242c2d0030441d1442d1700400300f00404220000c50700004c1c1e02031804050005a103a90440c04070403510700b08103d90003049a105036500310160003e049116a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 742853255 1250 742852005 742852007
    0x60703050a0605060406050c06070c1205340c09050c1602060910090305010c0c020a03030e0d12050d0f0501080d2304090509190819050702040f150f0506041203 70
    0x4840c0c0060f44c2021000401241540d003100041101d100700300200c03051075a035003104031010002682e0050102d00c250303040702000392068014080583d0103020002c3d0042503c2428600b024a82c0f0300b0000031117412140805000070300d80c003403001307248003c41440070f80b07481554000284103411481440c544c074500c440007551a42400d850340c10700060b102c4880b00e02081e2029002ca01c0a01c02110340b1360a1205415520744295101c1c1755155029080040490450750280e906140a464082d00728411400306c50204944910b50700700c103034182c0c40c1c0c95654821940200705a4682c40c004803c201d003017500403c14103c001510044101052412107041001c248000000720180c0d0b6140802c20340101c0c01092500c0c16074001801148008202c540445885034681407515403480050b124500500080e041d07a0031200145d1075440741c03850803501e0030100342d00280880d5640d580584266a49080e40c0c1e40c002c43d9050b41c08040d00101c03288c2c82149140c140010700c140301d540650f00a0b0903540940742e01b05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 742854505 1250 742853255 742853261
    0x1006180503030703110f030a0804110415180e030301080705010503060105120c04050406061b03110a0b04060c0e1503130807050d020a0303050a0204030302060103080306060c0d0e01120e060703050a 86
    0x80c110040980e5a80c01460800411382c0c000c0c195000310b00d0140d0400703443e1242c1c1c00401c65200d4001d540b0780003603035650343e101c440e00700c9803000459070025120001100a96000314202c0080d10742594529840c0c0e9404082d04101c40d00c1418141e01c0380d200708010720114400013034400464a092070b0071903582e695040100c489000d410038841c6842d1105062011540418010f481030320400d035020418a540c030300b4125050b121004911211110420b03810703010034820f035120401252050100c1c3c1041000c0d940c1c030509400c00320340544040d80c0d5000c81ea401a03601c44004550080704039420118814200400c40c040c0c840a00070040c1078030803103c0305007000391110555524a070003005a92005101140c069100c2c000312030b08600282c40d140000e0800c0c2002d109403000e6079015401010705a0030740d0740e400c040751b0001c4c000d43e6101009120008191500300300c4950401495510403800c0c50b0001c00140c0312202a5500112090030030078000060800040c001382d0040e4646000328007511800d06c14001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 742855755 1250 742854505 742854509
    0x90d0309030c080d0204181b0807050910031b080a050c030106410a0f180501050c010f020408150f07050a0e04141302090a0905070e0c04051c0218100618 67
    0x502c440161103034105a2a504c0401800c8d02404000184a80302d4000c80e040c841c00c9405c100803800a0140c03840900740b80301010341405103810300240b060341201d80940c440980c140340c00c0008021004010f800d070618040d06402a0800404900b035504119002e05a082000c50203c903c82d03003140301990302096034031044200d0182200c04841c441c41d0b00c0402002d58044184400410001380d1202070071441803805910341c0300788144045002e030424004484541c0805e00c0c0303400c035640301d22140790b155a0610080004009180003021021001405c80d6a8207078004d101840e54650001007004091304201110501e050900d40304244a0001c800a402400020700c2b0781c80e030840b11001c002e0f1b50201001c01202581c000c4615428503641c1400707031801d540030300034010320300d070030038001040514095850039400480400c0300b603080c6a250320208103e0301a0501011030701079080011015400c25503581e04080503007122202492a0001c1c947d60403003d140b00704401c0207103072114030b00d104242ca080440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 742857005 1250 742855755 742855769
    0xb25110f030a12021e0d090c08010903050a0c03170f0f060d0201020d12020f03010801060602120c0318060c0f011e09081602010c0b0a0515060c060f0a150b190c030f050d06050306090105090d0309030c080d0204 91
    0x11c1428181ca598440280031555500d62125100101e00c0b28034009107180300041d4141c1c000c0902d142020720807600f00da84010144c1c1d20340d400340540468001c080000d18080c090304400001c00610300f8000915206503290500808501006000d42020012007102c0c0e42580c0701144401c02e08c041c0006c0340051141968400860141420340c3c007407100103400008000214603c1600e140b1b22081c00e4504603645024000e00000d4100000f007000110b49000c00640360050601001d00250760300c2e540c0c540d500c00ca03000d01410343d8520421041100c03409025208200c15a46d0314144000301402d95580e6102510120341c001424001410f01c50460300b000b201600d81c03c01c1c4101d03003070f5920051540c0c0d810028826041507200558160b005200310005124103030940e503075065030b81011200780e42e10b52041074800c103aa0384480002c65180c804006050051502600000d00e503e00402c10340c2c2000c940e40242410982400c80c2d0f080440e80c00511101043d411144407070b0740300d01040d018402880b40f54081c0f1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 742858255 1250 742857005 742857047
    0x3040c0504020906190c0605061824060a020f1b06070f24050603151e04021f0f0306051207030b25110f030a12021e0d090c08010903050a0c03 62
    0x104602d50711a01b110400b44c8218800c1c030407500e0f004108481444000c125540f81440b100020b81c00410350f0401506c0b1280c40c96540071480d40400c007146450b449140000b016a00188110651120410812142055010440c0401d00c03140c3c001a00901c42c1840250988041804150500540318032021031003500c00302c0e16200c100400601d01c0901811143c0c23a210b4052445620203802ca4520498843c03002c012403580c0860110a10b046211000b500c144d802200003000c0041005030801400100c07050360f20b0b0b1906441041d100242618402d4003c0350042400300700341000c10340005555001d0340d80c0310410440030381c0c441c6900e2108030311040d10301d1580c2840e0720403100d0441c3c000c552001804550801d480010f0b6500b00c0c4180c0d04c0c880c007000d89001410401c111807103580158040c0c02c160851000450290310070030103440c180c1d001940018000d1381d8403c4000200300308210048001c0c90f1510081c4444800b44d180902203015400b000310910000300d00d00300c1014071800558420742044840381e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 742859505 1250 742858255 742858297
    0x10e1005010f0e1c0309120c120c030c18150e070507080910090305100b0904080a03090b01140f010305100b070c090c02010f050601020105060a031401020405040203190b010503040c0504020906 84
    0xd40e00e130010707881040e40412451007020490046444a80e070901d84c00642a00f026480c094511411000700c00e001c0e1040c424409011000491040101c4014940c504c01a110364521280c41000c4609024010301d44400c8003c08010401101d41c5099204070103040803030700e0b40c2d030314100326910b8800c541000f64032090000608044540028240c0705890184045a00708072140d4000005c6904416000d0343c00142e0400045c000344210300148400d4500c1d24003c2a010745079500d400f1020420b03040040c8064a20180503180d0800c0c03a2500e6144600346001c0c0040e0070300100003c420403480c040d001414800003007800c02c0c0500010510020030081c5810402061000c2000b8003d00f020004248035a04010100305190f00c1406594010302c4020445d88400c2c1c0346d9035482c1c01c0100b40c100d03107000c55502404000354075076072071029500c01c000030944581d1004410600208440103042d400f030511805106010104000e110b20704107030740381510016030f11140000061050302a0144480c4e07134062003410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 742860755 1250 742859505 742859539
    0x4020c030c070e0c1809180609010b01020f070b09040504050109080c0c21032a0f06060307080106120f03050d05040812060103020406020a0204050402190605040e010e1005010f0e 78
    0x50384003141d005520544080d1104001c5007101d02c5089500d1400e05d0300070310341d00d80070320303204202d07036049038010f0442801c0528070b101883c1040c90468604074240d40d41c086030320440d601400715030001c800c044080e1038141e04161081132540514280c4034003850783c6500103010440b003540040c80f142e03000380540f501c0b0b4650700049551043c8440109000d42098044040ca114012031175840865a0402541c240400303150717107510501c85000e00800e800100700c9400b00180040c41020044c80440740034040d03502e0201c2c00e0510308102580f210300b590b85003807020808003241d00420805158801440003800007141011110341c01049940c5c1e2403e4036000c00d001c1000f01580051640d0032000800003101c0c0e6030f040064041380210b10800c03015030813403d03038a00140f410341d010662051000380b204500022590304565400940d0f08401c000c41c100160500441c4640f0300254018220009035006030314000c10401005646c5104041c184051131002588050007021012401003000d000003801c400c090a03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 742862005 1250 742860755 742860763
    0x1e06021218010213050405060f1e03010b0603160c051c090311010e09150402070515060a080c0d080c0c090c0409060815010314030c030d0507080f040b01030303020904020c030c 77
    0x21207442522490304203440d118810300946500c6441c031a41041003038070f0b002c02e0102903c1c0051801d85c0c031014000d5401070a40c0c6101600d04221300012000b180c0c01c1e00d200070325084550f0548032501ca400300340304200d02c001071a03400003801c418503c2c161704110081d1500603c0c1c080b42100d02e480d039048002c02e1032451a40084c140044078040c03078003148606090001901c50040c1c040c1010f0300700c03201c0030002e014030001244108400d075000d00010701d003c0300c0d520f8403801c2001843e031012b10780408030207010040c038105000d90007405214001d130602c140700704001a21103454000040c107012002c01c0c050305808050100f11003c81c40940705156924042c1c07800d82076030f40680a1039440c10701d4000d020421050029440d01c00c0407100d10400840e0b400d6846002c078400c44082c2c01001888204080749a8030001c0c005050840480c0f8004a91810f084a02400010b8014000d5821210758000c110100d000c0086441c1142c0e01400d00590350181800814060f105865031540203100004880250040c009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 742863255 1250 742862005 742862011
    0xc1715040302011509290f1f170c07020d02040b0d11011112040506160c0308090301050109090f110f060c1b0a080d03020c0109170c0705010f020a1e060212 68
    0x30b485181350740e13210b080040888040040540081004000b40c402c110340e06250b10712486002000c100d003404100e80010741c9502c0d0b91000c1c4d8940380380800c3c44110b0780d070404180c40e40c000b441e840c51202480c082002d9402c40c058680003a12948888001c201035449552202461603000307018140d1185003814440300103060026541c5c0050038240b02e0a0b0829800303c1c150030715070a0440d41c1d51801d40b8000c01c125450f0010001c00505036a150002000200050440340045200d10200c2d51120010001c1600712401688003800c0d0701e06051503c0c0004010251007840039902403132410b0800d61440208a500840d01342007a0449400a00348001030800213068154255080e80c004600d03040070244a0b2101c524070030b0340750b69800050a030f900d007030207500a0048881803000001d200100740c2c035842102801c82011000101c00022090071920040c800c16004c0c00080c2083c0c4a0842c82107002542c4560083c005054602d0342c540d40c401c00f9204290000e00340c3d030400000e43d110b20118140c4503154400f9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 742864505 1250 742863255 742863281
    0x1104090902150313030c06060b0c0a0327091503050f0c04050603160509090c04020720010207060509040f140c1207021903140c01090303051504020301030c171504030201 74
    0x3050b18030080c104203404803440340030000c012020781e4030969000d554590301c1100072030315076440310000b040340300f0b6290140480e1801ea8004080c08400c60078080d244c8510a00e00303c1d403c2c014040504545030300800404221100100005900040c04031402c42d4915181c00081260044103004885200002140041c3c4081201d0400140d00c03170300201a691894078241d0030303901c00100ba00308043d241040e201a4400e942605031420280e1050018040b03071300c041c50449481c0c1012030070b14000008040b145200314028002001d6243c14450064458081e5598052050344c0f140c00c00e6030f0740c0c1c1c00b5410030340c103071195602d218249003408580743c4956000300f0713440807200c61540c0001b03151900c00110454100031003843c02138140850b807012a0214808485090010420000703940c00c9102449411102c3d03009a0b400103903401d181120035601030100894520584c0140014404107010b40040c000700d511640d00c292911312201541800e10390b0000886001d00d40c02d400b000103154040d0842c550b00450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 742865755 1250 742864505 742864519
    0x720062d0603060412120504080a1119150902030318030105071b030e0a030b10030606060c05070e060d080d05010f05040903050a0f1202040314010c0e10050304061104090902 76
    0x200c1000e01031512030407601c4a525603c80c0c0e0100c0c0110f9106004503100c000c007440c0600c252180c8045450954030140d900b10b480002c00103c503e103455011160700454000e100c0a469081281441c202120446000207070040c0700149a5a4410005da07015420082d030241c20303691207844005011a0b09035004a400e8025400d00c070002d45600c0c4902c44031450f103506030b1401100c80440351000c89000c4c803501d140c10340048804401201144107010300320311980340441e04107109800c514004040c0c0d45c542c0d1004051100800a60780002d80102c0d01e0002c0d42c6c202451143e25503211000900084800c15011b01158400180c01e00c03401c125402141c1695940c0390044282d69461051004440c454000a4001007041c000843c42c14440ea0000c40c012031641f030519420005241e044c4100e03406640100e403900501d0742882c1c91880d0030b01602a07070105030300382641c44030b40c0d081c04145083c207078006a1081190010000f030802c0740c1540010070042c00480055102c98036515601c0082110041c180d00c5001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 742867005 1250 742865755 742865821
    0x200105060319020d030804060b0d060c030f050108030901050c010621050705030601061d0d0605090106090b03030a0215100308040f03061d10021803031909060302030f072006 76
    0xa464482e81051a03003d803c1031241007080d05d040381c0c1c444000e0b00803941d00b47c684612590b980d942840d01d20715103025603800500c0c4c4014103400b4040312400c800e22042039040800400506c000031092340d403078141c2030034503c1d40d0303600c2c00240a00421958215042d03071513800540c8aa9100040d10004005115104550b01d13aa00c500400d540c0340804d00ca01d500280b401c0c1d400d8148016140403601c0c98180c043c000d40c80301c0c0079075a42c90064807401c681d8580705179500c0004010045d00c130701078805615003d03405545032003400003000391922419410141894017420104840c00c1c41c0c000c121008682090243d03464a031240d8064400c0b0320399100944940d030074012180440b40110300c107032a07103000a8004000170003601e0361100c0a0341014455500c00c41003d00c3c480c4464800340010244000c41120740c4200c45500e00020300720310340e25001007017054030510800c00484800180250002e1407070420440070b1100c504d400b1140d0035204000b0b152405050184110ba400c003074039140d0b4038214040e0520313001c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 742868255 1250 742867005 742867033
    0x240405070f2105010902090406020c070504060b07020f03340b0c370515090d09030f021c0302070f050105090a05130603080c030705280b072001050603 66
    0x81d216029900800c00b01205104500070111402c02c0038911079030011030303011882c0d000500c5000d02150709071251600045c00e1109007506000c1800940400c440030030031941841c100c1000d600504200900400c00d00001014030b6508101c0e405045500701828240b00665045900301200014240c6c2c1d4a55950140842e8821200c000d507409954200001d040701005000c41018664001c0c400710038001e000c0d66907103030003085820a0001140504020940300d6080741001c2c81d00c4400134041c1030103070051080095220b90080582c0120b03508004928540c801c54000220b001d41c25040e410001c07500c0700504002c058004c2008011103040801d007402d41d80e40c80c80103681ea0322441e4696548440032000038021450500f8108190403024040010019103039030301c60896611481a0001035032021880c801001420080031200191080d4039141106211200648040384e00100425038a00480001d142a2040e4000612a115400c0c1b000d403c2000259440c000c0009481160181c0210b146c3c3e18645 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 742869505 1250 742868255 742868279
    0x1703090108070c210e1002010e07060903150e07050925020c060a1116060c0605011d130611040f05030c121914060103150f05101724040507 61
    0x5500040d40d03401c00016010414005141a6896018069400d44901282d103c40380d4006d9035211079000010010710b02c00b81c880ca400b0003580320a0410441e0300c010310009000214400c034485000c0c10119016101200c55824008107400ca80c0d00700e03882108000601280340c0e004900004c4001b41c42d038688122040480e100c10300030030b4480d0440e82c03c004541803a8400c444c0c1442540e00d26058401020030001528102880d41d440709d0300241c0314008800602a191041c0c50040448a04601040c10050305091886800804203c1088a036a20035028031080760000d08032104006070301650b40c0e88440e04948030070b8050092078041c4c81040000d040e40c2c1007104500c583c0d112944000c050903001c00e0f042c0b04020218070400c45007021811400c48004008001d06806984105100d82c403020305040ca07601155000c1810030840c600301418060200411411101614420040c81401500502602e80f40400028009401c0c100781400715aa450702105102d0255100e48155848560740e00104810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 742870755 1250 742869505 742869527
    0x1203050316020609030901110708160e0c040305070b09040b0d061b110325080703021011070b0a0c0c020d060903180e0c3001050a17120304060204170309010807 70
    0x11030317000b007241b0718140d17014000c2d081c000190582141c51441d190001103003001c6914110101d034102a03041448070030b4044036081d91007941d421000e03041c103140d51200ea60b01e034842c0c45100707844400012080542d440b0f64101914151014006031003aa4035071510b64010181c80900341e036491903060211042c5403041e000f030741d91140030304002c41c10030400b1380c000c40326061081382c050001a8800e507207600191000001e082e80900a070094565040003172440c000b95000086e101c01c60420401052000500000d481c0c0e40191021a00060b07045401c1000d4130602c0d1080d0010307510041c902000000c00a154001c02e202e1031096941e00300403115140c0c0000301e155507000e80090f0381c00e0080015500400070002c1c22113182004c0086c041001090717030514071036100401c174844c41c0003a00e005100324201908104020401522502c00040c01006026202e845000110100f954000b0105062002c1901503038050030100300242c900c24071403081c481da03c0d440044000d0200306c0f20b03c0000e008900801400e50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 742872005 1250 742870755 742870771
    0x3060106020703150c020f06090a021008010608151324050604050603071b060f1b1e031805060c0d0b04060b042c010f0602011524050412030503160206 66
    0x1044c0305000558001800d400e0032954218411342c0c80c1401100c0040141500441101001d00800c0d022801481030b03480c858142801403055910040001a0f403210090b584005000e42029038104603000090720820050040c04545013002c41101d40d00c002d00b540d15801d002c000b0500c004555880b82400342d140180c1c480d10764060b009000185c09140036070702078103541c04045140300710054140da8200486a0781c545000796156034003600400804d4408002041042034201b120705074100008041480140d520a80304240d1a6040d401142942d80e07612013030664004140d84003464006200f024035002003180a00c21b606001c00020541044d00c60502940d8244c81507500e418207161a100040c1c245c00740718881d06044c030042d503644044508082c0c1c0a01a440c0d803240700c00d0300d4414000c0c251803004522040e54850310900304210880c400700f6501c0d024001c1c1e0b43c103000d00e4003c075095030540580e41c0000038403140c20b04600d082680c000021882904081c1c0c6202c1c90711740d0201c040345e0327980d0300b150000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 742873255 1250 742872005 742872023
    0x90806060f090c040e100e1f060e0102030d020d02030f13080301050d02120a1211031213082b06090510030809191203030b030a0308010603050c091e03060106020703 72
    0x1500700e08041840d03d900000002c41a468039a444035607040240084403180141602e00c481400000c54054041c5d0300f15416680d06030140300c040204005410301441800240200c0d8031010a0507402070041c1c81a001d800801152035000c00d090000203588110f8684002e014650001280d05a040035094100c0380c1024030103003980c0c00d02041c000f41c86070076103060307130b0140c203030088014216800c201401a42c1e104244c01000c1e45601840a04070310180200391642d42c0060060814280000903903640c440e8070a12034220b40e4083c0d003414101da206004506605118050321350b03405503401d101414945514903010001c10b55110309400440301e0a568854122200e031030100081403c400140c01610700041c940070b0403903241c1c124514001c6159104241c00b112034106a0b0a1517090704c10105019400d401818040c0a02d583c0142015030500649090594440100c0c25002081d825a03001c1c00014041c00710005d01c00a9180d180103840418501c28801d040010614a101003160300480b58440519 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 742874505 1250 742873255 742873279
    0x120a050c0a0f0302090109121202060a090f0f060e06010905161403070e0f04090303051920030702011d0a02040f02341b150207060e0405130512040609080606 69
    0x4501075841101d24a0410a003804003080c40304e095900b0000323081c442c2a103640880c500300d1019007080002440c0d900341c1407401100d130012031088261080d0403035210032104148020340c940796006014110030310415110f400004160000070354440c034000c5e8500d400d0900c504a03e6501114554102105141e50b28001c2c0003003402030340502c40c2c0d80c1e01030070024400062400e1040204048900e460000e0b000283c4070b1062055480450000c03c10754004c6402c140b00c41e00143d09841c3c00401c88152150317000ca000400585901d100f9800b02d0f2000030f004501009001c002c010181d950b0740e182030245e208a02e0000d01d1940381c11607100f1038104120144807050032a82400f00084c4050b048605041c10f8044854003000182d02c078039180d428804070300740600c0600c2c140560985090138a00c04682954071a000901c030103900000c2c2507504d508200d40115a6598030300da050056111164010001d102c0e0407150410392195a001e04182e40c6107994182500d0f41d10a201c50b0707141d0041d203119410003118180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 742875755 1250 742874505 742874507
    0x1418100b100c050a05010f0624020703020904080c12120906010f06050a140c2a13020306040e011407021005010311012f07060e0d0c29120a050c0a0f 65
    0x21102645000f60b0954119500d075496060941e01c0c080066100305039502400e1140020301420124102e81400d000100109040c0e80a036440000e404043d11035400500090304200408044907000000181600c00d408103003646042981c0000a842c0100130103040010540c0c24005045030403120070080b0000e2591400342c05440c00d507c200404810040908031000345331065100405030700b004030005040d21401366140140202084203032b11030300c001c4085452202d5441d07103000e0014107400c110041e9651a8100020020031411032001c0d959400c002c03140c0204208101d5443c0f148081d6002d480308454240c01c090100c0d0b80900000300b81c3c8501007114020395104043c5000200c4103080c00c51248a905c8000341712000036840300c40ea055201600a124050b8030280c91300c40ca01c400e032510b1401540580e514111130030380c1d014110003241802003140721400f10356422400b4410084540e607684042c2d60964400101c00c807100f000550403c4007250200c000401110124152907a94055007205010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 742877005 1250 742875755 742875767
    0x8040606090209090f130b01030f140f03031914090703030e1c0f06201306090608040212030904020f090405090a0803240907030911061303151418100b10 67
    0x3185490b00c0c406c60502400290b0204501c50295000c0d8510400c1340c00307a803070004014482d02d01e03100105d030014503440e04101800016a07801690702c0a21103004c11210398450000c140d4081451102d405e0b50092144803900401c0b403005480c082d070340b2654442003074000d112401496200b69041d040300d29840e00c0208503002461401284503e1003ca12584107a1000300c00d0000550303d0403011500040100a8160300140000202582e00302190100d00e801300c090858000104064014551503441044020041c000c681c00d101c0010011511040030b600c0070710083c3c0150680e103003d9880d203004030780e840400042542d40240d200010314959501c03c604241c1d089188210b11381e161820b8280880b41c2d44c1d40044007881f410b050f03980007070304115600706070086c06041e003141c81c010300080102911034001c0d54600030035a034118030010391400803035005a00504d0b01d45138540d11500c0304da041c05588901a1480a1f41e4505e4000f00c80c4402400c2003640112422038120b680d0040320703484130404450240c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 742878255 1250 742877005 742877011
    0xa0e130b07110615010c030e03070314010b0a0515030402011d040207031710030308012702070c06090b0306061c0f0c080601020d05122a070308040606090209090f 71
    0x5168a12168080c0e500d1050300402070390458085903101d212084440b104000b140d61100500c05444044460840040d00c4030b504600301904010b65000c0403401600c0c1000f061005603404415801c0460002c2e076054000c00d40d800500344900c1035503500045500d05a801180a0000301144918540303031a80150303840300c0d214805d40142001000800d81c1c540e101e10203050324a020703880303103405a40700c2d801402822500074510056140102c00a0020a500c98089415200d2041c0284003d5050400c0d200c12204000349100041d400010382c40c0400821101e0303101121859158403003000d0301c5503a1104a4001160103a070000014413055034030120100f1510034851400c14001000001400c011080d01e40e4404800302180710001480701ea568101300e0015405001c5c50201d042c2284116110381d000c0c2c02616002c00c00f416000902d05040c070200608042d001e010116030f5032055180b5014001250880d0180c400c58507001e00001c0c0d5004900803109440c0c0004c240345c0b5140c0d03440c0150030b0460005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 742879505 1250 742878255 742878271
    0x706030510260601080610080a1203020a03200d0617030d020d02090402160b0105030a0506060f370f2108130308070203060a0e0a1403070204050a0507020c010e0a0e 72
    0x85030544101c01420f020880c0a0500c0c04d000d080b4500d84207150b0110140d036a0712550b081d5101546890100b0301242200e0f041c50440d01e405603a4a80e00038044001d40309440c40e90f90203100d2804509a00003000f00180700d40404080305221040d130310254800108680111081a07400030061502c0c907c060b940186040e180e02400142031500d5900071504907000031001c12404c15062120f03800b844882542940149000c4000740140507082d51926150300014088a00800d0405002e828540e50314154080700320100301e20441c01c0400e5051040c00c55121402c48200c138200c41008141c40c40d00c41491010f90710300c4900d5400140782c40061401800c500c14081d18080300c2804103000d1000e0800c20500218040e404440e241c4520b80101820888050031010841d440c010b002e5011080106203025165000755a01f46410000e500c3e550640c03280d1321000307602c81d14013810042d42154551149000358801e900702e68007480c3c4040152803250391011203580c1b00300d06941c1000030b071380300840c010341c05800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 742880755 1250 742879505 742879559
    0x9020d0504140c0a2d080c181902031005030607080703060e041e14030c07061107350d260103210918020a0f05180d060e0607110706030510 61
    0x1c00c1500700c0482011b40094136645c00880000c006481c00850300720900b40da01135582402e007001c41c0072000c25502400c3d0048410b03008000584804c040c94007031802044050140ea04c14503013020300030702120040383e01a000c85c1c9082c401007003000d41007140601c40d660125840302e07540d9602d0240340c4a104140011500c5100c2c2d40841e00c0c1001c0140040e04150075002d005000e281e0520780098620308815500d0401940b003ca4200400c5034036109030400c0708805039000e240310500e4404c61006142100c00800c2d10310544001d030740c40d10390208403000c503101110807001406540100041c2000d03c01e103c0134000c561184081d9180c42812250409125441e0526901842e52100c0084101c071490018042d880d5010071180e48160700460103440d1024545002894002c031120180f0b880108444141d000f80e40600700607080180e03a80c03096101c400d40e0b0045640342d1070b1180c0010140071034900c0c108640c0c040d905000174150300a009013801000064519111203050071040c941a00c0507080013124581 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 742882005 1250 742880755 742880819
    0xa1707050a0c1502150c2d0f031501030e0d05160c121407061b02040209060d1a06090d170f03010611010c050702010206070f0909020d0504140c0a 64
    0x382d0350015008210b02c16042007a50744420b0007a0800030704694000c00c481c00d110400500d04501c0049800300712481d0101c90030b80c4954203a8408213109500702c0700404400048000750702e940000654410204204c032040b500c40910011815604510741d54440c0d0780c071203030a000c2c21078003070310103080e5042910021600b0005c0c01e44a4540041079a40070000441903080801c2c00d10031029100001c1160040c02065414070b0100010940070000d04600180e000050707070760085581e42d8040300d41c202070042c01c035500c0d01d54080f03100f002000f60490151102195608140050401100307854183c0c50003031075818420704940b1030007201c060348070202200f02e00400c00d500b40800580e0142d4083c1c0325680e80e81214000540400d42101c1004403904203012090046c0307c0143ea0000d0b20a5200c240d070b02d040c0a4803001018182d035811340c1904911034403030000c0754003202140e041e400a841039001c1d8800880100c0c0300d076905034442c040e42c035040e0b030802c0c40e03003005000c5000102d6000d00a4000c01480d500b00c41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 742883255 1250 742882005 742882013
    0x110a050f0d06181109010905011a0a0212190207051e0d06020d0203040f03020609073204020a020c040b0d050a030f0c020a0f05010809011104140d0807061d0a1707050a 73
    0xf85094000f1240d00406550a203030605041e00071034054044000c04001a5040c0000303200240105140b91640040016001003010302c24890210700e410408400c64590500300c546d0381c0344640b80d5404070018481d8650005051400c03861940050268007855001c40009200784040d008940034182c581c01d400b000112040380c0d240c8000d42c80f86004103500382e95034480d442c000342010713800790801006e43e10503001806512040502d51b0306410804170848a204a50324516600351050322000358031030300c0843d41080158010540c03079080c403011078082002141040810544038a40d0300301420316801a102240001d016480e0206494441e081c82c02403003640d40d0000c1d40d00c55403500305100e00c2040d50700800165800c0b089290b0800c1602000b400408242030512415010710f01c02c0c41c030902c10a0b46180429160400240f00281c3c000410541ea1540c6040c801c000e449da05070540b20781c501485020340c0100c40402e9680003658032007511038025132401820700403a0048502614039001b0303103040e50001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 742884505 1250 742883255 742883291
    0x21030c09040608060f160f0e0d0f0b0103050313170d081f12060e011a21030d0507081612110408030a021005061e12030f0c0604110a050f0d06 62
    0x128206020345c00140b60000c00b583e805540002402d00344070340180c03103c0324650006400401c6d005d00b520700075044052414980340a1680070030103805982c003d0004802d1220202c0109645407102070190005507950a039601141c4401107449099000142602c02c4584140c0e041904200c2d0b460b40e0340d40a22650101da00c85109560180c80803000d812100c004000c01030090756a08400903000308404080644040341d0369080443c01071050744844420380583c04031f5200e4580f054480360031292502003102403940100000d44e0380785c01141c020f80000354070f82001034110648044030307174961500881030a281009041000340d03010700c9410a000104080c0b908001a20f000744e501c0d8020603803050036401034411140c000e08610300403100f410b000c03551400000c4414040b11002e0780d070079110140d010790150540c05030200781e40d4110030001d0303185c40315413002800c070380549d01079941c403409144003c04102c01c2e0304c4603106107074014060904007980c41c604001c0c0300702042d0189101154200340a01d0340074035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 742885755 1250 742884505 742884511
    0xd1a0f060d0e120c030913050c0d09021201110309190c0b0924030601032901050c01022a0d02010c081501020705060406031a10140c0f01150821030c0904060806 70
    0x585d002180c48500c85c80d04c0009950080c603e40400c108a00380010a01c2280c0b10300e000c4030240584480031002152243c030403200311210181e00801102111440c40d20a552060315000032910a9500403001c1010038200b40e0105076200680303900e424500001c40013290400d09000fa441100f41c03845442d030b155020061206800030142041e5a440c141c00050210340f402038980410a0b991000540100c0c0641c1e421903020509003005925031602040042c00380c07160600c0584040384007100004006182400062100e02c03030001d81e200b00c01c0c004000c0342292040354102c1c0005507804081342d00180f11290240440c001071041d180c2498071a00440c8055115912040010360349200e001c1000380f54901000840008075035040040c0c1c0c034440024110010700410300340c40800041e0307682110b08208040b134039264110b0000e0001982c540014080380c4410701c1107a819010360140d4168003191503402d00b56511100c00807500319180d91145800ca600040d10040d0042da882c800414199400c10050344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 742887005 1250 742885755 742885777
    0x22080106080c01080a061d0a05090105040210030209280806180a0b1e100f06051e160c0909061406010c03080a02041703070303140f0424020d1a0f060d0e12 68
    0x2407e8104072a140d81144c10050070f04c03190340d24260034400144d54202d041c512010701460056100c1a881c3d00045010110440b480c40240800c0c14040402680c1091941100c0f005800c0e03c615544050b20202100c0f0140c44109403504030320149000200c000e078685400c540c6141e00c007001981000d14020105000b55600501500086000c01c03420860044c107201a10440c07504504000400460700548050380c140720b400c40341d02081e04a40c0000820b000800e458024260030107445e9102a91401801d2100d000c3d5000da041543c004500612040028024038069695900d287c1081d00c040b100d418025050303c403c6030702000300080100490161030012040f00e0044c6580314002e01d40603049540a0110103403844003070b0308015080c110003402e01d0b0310540284403000300c842501c2c12002c01181010000034043e2002c10700403042e0b011544041d4146001c590700b02c05201402d420841c040e80e100180641c0310b0420003a6418103172280c1c00500c5045821000c032660115100b00e004000c0e044103910361 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 742888255 1250 742887005 742887059
    0x100308120105030607020d0815190e0702060105010503010b070204110903070602061503010603080409050406140c0909090105090a031b020a0b12070518120f0322080106080c01080a06 80
    0x100140c0f400348501034000d1044e00041c240c0161091010300611300091469144041e80752182105484503600c0e031040d2000c50314145079164940c0100610342c141a036044005108400011130a54014011641a0b07a03031441c2c001c1c2440364507403c010140c482003c144644c0c40b02800244150344081003540c000d00015005817103640f603c1107003210300d1168061620b1190303040a1041002c41c0e101400c403400d9649210021840d540c0d1810b00c0030140c03030000207460490f01400d08110546c0c9004014010000040392000041d80300c101c1240d0903070b0415104008180c0004c003d070000207009148404000c41c00001111004100741c000514083c2c2c0c607072102006400000d184038074401c003000c2e00c5038000010704001d03090a0b8060042024212140441c5000e040160b02c0348607043ca0401280c14140400f00807a41e4460a400200510402c1207500300c071142c081407004150300030180500b0003658280c02c01006091000401107405020140050344015510a07000c141d1b20456003180f442407400743d10320 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 742889505 1250 742888255 742888259
    0xd140a0512030708041209080703061b171f03020a240804051203130b16120204032604170a020f0d05060703021b06040f05120a171003081201 62
    0x2850034440c1d5407649100812040041280d403681050031180c22542100c0304a100303524140c4c0c00d80781401a900000302c20320500000208004560308038410100d58008900823041d241030090305d450f004550521911035049000400010645607a90b450515603000417102603030325004684004991782080c026051618244c819106400407625030800440c40e040c1c10304d213040d4035215140d9449021000400c00c0000101c1c101844194503180e44942210b01400795003000214003d40b07030102c1c09c41c0390101d02c2e0600000000c80d110320940301203941024200c0490340740c1c1101c0302020050105014444402400f003c0b41c10400c103c402c40c80c03480100001c140344982401088114000d000341d84e48101e01c260780010010740c004c56507540042d000d04001d41c071244032810010480100e190340101c640706250401050264000c11351a10600030010740305c42d00c1d5503044581c2140705488900d00450400c0c1401006410a000c0340e682c004e0121340711030304850b120754910300590300110301c03e00c540001d1401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 742890755 1250 742889505 742889513
    0xb040803130e040804031707020301140103050c010908100e01111309050c0306130c0203160c0f08060f040f02010c0228050306190504050705030a03080709050603010f03060b0d140a 79
    0x700080c11400d840300c422442c0980d100308091095000040420341c070003003140070400410003590318450b4000c00900c0f030110200c00d8030011440034030045c1c0d0b20b84a10090000705500919000c1c0a650250010b011482c1c0c018130300c04054004119204010741d0ba96410816a0300b40c80080e01400c3c18401040d142c1c5458124072005541c0d0207040d000650004000303010132952800d44800c505919010085200188104140e0a60003074050700d03091103803101022410401e0320950309017500c0041300168080c64032126029075441c01262007240c24201100890b011a42103140142c40500c14544203800c905560f01082031580a42c0e2008007540e11640000c25031040c00c2080c001905094006200718900002c00c18004c07110b00502900d4039644c1c82c00300f802c2c80307420f1050002074400541210148a81e902d001481b0010442e0b2040001d00c04000220303291510404407412604d582070816002c90454036450002c00405e45103e034000c000c1004034001a13040400103048020345400b4242003035250074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 742892005 1250 742890755 742890787
    0x30f160519030204050604060b030106092340090618020f1e0405070c29190b0a0b090307060203091c03020a060213050a121211070b040803 61
    0x10910812080708151010500c80c03030302408594048801041c551515004107000785141d40110707015440010000c14540d8201442130b0407142d2303072210019540c6c11410084042c400031403907a5030007188041002a0894140c0229009004903014074000025170b036030b9403192103107140004a0203a160408a01400854800c008036840b9801060034a03070050350024504422146006d8402d01c00340c8204030011114107942085100050310420860405410142010400b510111000180800c2c24816103040c0d0144c0c0c030142101f20000c1328540c0781d44002611103450200c020180d140c0e141010340d207603a40c0420740d00c01011040f02c6a51703114a41030034581045000d400000c1554404c01020585845200c440c0010008100340d84a40384601d1074200e04108010784050b2800e8008141500501c442c8400401212000c40e5048001682c407111209540503540000d0001b00740c0f40c0300980c3c10b41c01425280d0150844c08c0c151801251075580e00c0000e40c000760801001a8004160845000b000388 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 742893255 1250 742892005 742892009
    0x183c120c0f16062606040c0309051b09010b07210c021e1f08010b281d010f0206062b0309030b011a0706020d020706050a0b100f0f031a030f16 62
    0x1c00113013041c0a403e00507540a10041c10360740c00780d81d65408039640035220390b11101d0840d900c002a03075185400d0b0b08280c29a901ca000e2042d114982c158000580003107104219211280c1c8842c0d12824890800300d400d2600f5580d00c0450240031442c0c18400060b519418400720400030100522140f040000510203a416050041d00d072070840c1c2240031035980d401c0400d41c1e044a5080d04103a0b40d07009a0b0600c10303d1300c01c011030f03e01c080e051400c1c1e02c100b01581100000e10350302c035017082000740c0740e07048001160900b248031200d07409608100044ad549081144400c00320f500c0210281001b03019007104045401d0288501717500040c03155405104001e1581160750042c411510900c00100c265010010b00d4421250010501740d400a4445240405901624200c0d504408200407620780342d1600300250440c0d6a44c0d03407060a03150003039200c0754003c0910101c0c1e07603503542e21010b0021510740154001c2ca420002070140e9405440520301d980c1d02003080340c07590452140903100d0a4260500b01849030119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 742894505 1250 742893255 742893287
    0x10302040f03140f01050112120c030c062a030207062f0309100207060e011506120216050a0609031d090a0203183c120c0f1606 56
    0x40004101c4094078007a40c03001d0701d030007020b50402800c180504914000c000d61008280307500f0000005200754402d40c600e58205d0142c038070003010b10400c81d03007155124031081c0001c0200e60200e88020100d0000d522001d0040110405c0503100304000d14010130390702c0f01c0500d4500194001800104001072802458007414a01090303581020303800341041da44183c804104100320780c01000040c00031600300302480a9072070725003003155140401d04054003d000e043c014403130745e9802c00c0300010808401c0c0c2e4110046581c1641c40c802d02c0015004180007a60040c0015401c02c0640301d40500403680a02041c80614410000001d0000306272402500d03091510b0020306032032042d4005502207858035500241e01c0200f4000050744c1c0ea940c0005525100100c2e041098244105445000c00c4003101d480500382c0e10304901d0018249959450710040702e004440851201d8100c90196810b0507040400f6202030f0031000195051945c00894961824007c0c805171040711418000401900743c02030fa4402c10700d028 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 742895755 1250 742894505 742894507
    0x13080304140316030602070510090807021810031707020303040f170703030c030f1709010c0207080a020604150309080c03030412030902060a0c15021b0f01140708060604030c03050615010302 83
    0x1100030310942c10300350f034800502620780025008040003001d201c90347e092004120100039908980c240244c15421286089001c0c002c10300341034001c40300c040122841511510780ea86010b07411544e840d110341c0204a410a2502c2017400418010f80d424005000a49814071035000a680b50040c0e4041002d00e4054a43c1140c00108040c00400d91100980384456018180440010042401252110b80d181c1503c41c054810b072007400591001900140da9016269080702c0440340c40d001c415481740f0228800a6001404100800c5074540c09607001e60290f400b4240007410410b00c3c0c440c0240e40d40048050001900b0000410007040402d40c1e0104443c0b010703150402c8490311a50101c0d500b8400c401d43c0390117011854030b00c03500300850806117000e030b203c241c00c040d92650003030001c402004880080e050752130b000f1501a100321580501c104003c840c0000c03040313140ea4440303000a070b81c098405000203801203070030800440451480391240c801580710f070340240ac1e00d1804165484c405417140b40c5050400d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 742897005 1250 742895755 742895773
    0x90c012106060c17040803160206040905040807140706090515090604080d091e0b090d021215090a03200c041b02010f0b03060705091809010c110304060909050903130803041403 77
    0xd400000d0390202c6020281e2802380908900001301e980c01650302c5079840a042004100400a0480290031140c0c411250910000c1113071001d1030322480c15010340c0c8001802031900700309a01c3c28000c410007400c00603041d1481c0941c0c4002281c0603034002d810041060740080c0340b0003000c690054424000340341e00b01c5203240c444090021112004810311400000c0341d0701042d441c51030341c0c8154054003080d80c01400d5181d02c0c18019600e07502e80c51070140c040503404943e00029017110010940e01001a0315603204941d10009242c10901c0c8000e0f80e011054510800a00c90135035290340c400c8203003c02042c44006860300380c0c40c10090035940b0240c05910118200003071105079480006500d50052a20b007880b0f0746403001c950118400c221005a06c1e07a034480740200340b080740101903001550b460010b0b501c100d070b4020701c07030b00d9580c0c0d0344103074442c540000c2d480010030420890740f5840f07190811550026645004491241c0340f80c140c0c07494020151a400000c0c0c200100141d92103079803e030b800158083d1580700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 742898255 1250 742897005 742897019
    0x31406060102060a0c02010b0901090515121e0a080a0c110f1e01021f02070b13050a030c020111030304050706020c03150f040309050316051008090c012106060c1704 72
    0xc0340180c1400c0c1c0080d00d64180e1704440703000f9000f01042090103868900c081da0344062000140400751030a2485005c450441981b50900d1260150a00041401002d254141e02d40450008009200c14100c80c01050204000030b0318040c010941e940880c0d0358849540114249802c5110340c1000c6c03207128030700209082c06291180e03800480c0810f03070450000b030700c034101c0c40050707007044070441424010713020f114161640d4480300c3d40030741070301405484620000d80c3c0703101000b4101030103004003508039403204072070341c3c0020300c01c1101042591040c90810400c1360070b44055841c0d50416182240c864105c0d440178050385a0402c08480207540440003081c0329405080c9801410a000d0030b01020400300c50005818940146c4000300100800340c02c42d108001820100d903603100c03680c007038207110341c00711450440d10501c2001c0850040c00c2090141460002d45001511403041c500c1c04000d034064045170381d00c050360a034440c0d1801040c2603218207840f4000c1d031820100c0f1001201e0f00040b900c005201c144000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 742899505 1250 742898255 742898263
    0x15070c1104050a181b050a030c09050403020c060d022113140703051507090906050f10020a0602031f0509090712030306030c0609211113060e04030801031406060102 72
    0x5030415680020b8540f54038203008058882185591908104501080208140615942d03e0580740e40d4070390300c130251100c040110a004900c4040c0c80c2d03140c6040240f1503c45654003483d0494840d0048841e01c1e40c0c910041810368100d00307040ba440d16404105e492410070350031892400d2018a142c40281c52515220701c2c100d51036803d4029241e4552400040140751040007002c01440e00700d0219400c4144004503840e41e6001111031400040c012000011440103034081e04c015110b008042c9030091f400c160500c500341c080c4060100441c0303c0c40c4030910100e0124402140600a05204840c40000741d40403040494400d5000720302a94181040050240011800005540311084200051031050034201c005d802c07030742c0019000d41042d000004009801401d2041192481c0314240000c07071340c03400c40030010a1400d00207070001d260400c1c40c1103d803404040d001e03400c0240030303000100d031501c85101c180380c0c11040f101140403901280c014010300980909007901400d166000b8440e510704840001c2d11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 742900755 1250 742899505 742899533
    0x6030a02060f1e031003140f030403080306061606200c06060906060d020f03190c0e090a0e010906050402090903041223010c0801140a081207022115070c 67
    0x440c5404543c83c00300d800050b00d400b100d02c4000d58007540328104450030705128015848101da0143d14843c0905440700040385684015030a60051401d00c3d145807201003040d0f03c02003130954060810088a080700e104a840d59818174021000007400c441c0248250f030711140c1032000741c09190340134401c074000035000181d842e900150648080010f9142d5201207101402694915030320f0030300100341e2080d00d09441c1d0241d813295005c07100300c411a0b02084980c0c42118a159214800a02200d05200d01c0f420281c1c0140e4105c081c010000415100203501642150f640040417220280c07907905101c00c4d444c10302481f581020084021710714051a25410404402c2600c400502c1e42036050308048a900010450801092240001744010621200b00405c441d03024013500c00603c01841c00c007030180c1403681c58407080da50201c00a00d4061000070100c4400d400000382243c1c8001000d65010002c540301c41020380001c5140000c1c0034920402580000d8010020f280404210010690300d011490707090310246 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 742902005 1250 742900755 742900777
    0xd0e0f061603020c03060f090705060c0303180708120d0c05031303230a0804050715051b0a0f03170f04020a051c02030d0507061a100f0c1a06030606030a0206 69
    0x48003036242c0c039040e82083c00c0e20f1a010b40c14003c51041101c28200707100300500c50400c00b0166003003180c881c420010781f40103c00e1000c4203540140000764007038003215114039150a9420803242004d54a249180c5490074044507100541000705642c50103030391074003d0740c40341d143c2410f04504601d03140181804408403180301a0410903480d45140300310307103111000c960546075440d11647c0d0310138000018160b1f42d020b95044030580f152100000f60504040c60713007080240c0c150340e07513441c00183c070b2280710b251400008015154082c10340c0c40030010781044481d85030984079480d0950380d80d5500e01d01c005450001042e841d45910101c0030000184d5403000f9120070ba40341110b055201003e9101404800c0850030402901440b40800039621150014040d001c030310705c5100244803071940b1100c0800044000328141e40c0000d0f500340e001a50b18010340700c040c5841d410b481c1c8917580340d213140c45050404007203410a03191030301d2900074094503040500403d54440b40540040c2403409443d40820f50382d1040d01d034025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 742903255 1250 742902005 742902037
    0x31c0e06040b1c0603020a090c200318180106030e07090c050d050415050f09010c051e400e0403021203060414010305100b01170a1e020304050d0e0f06 66
    0x5503c002090340190301954001e040c200c0c1d8181c03900741800080c4003c0c49400081040c980c10111850561a4419200d0f61850065418040c0e00c50000e2192004914200d03031100d042000320030484040701d241402005103640204a080c50106a54107080040d00580b443c40c5c18003095094035078103c03003220b01c200c4d001c03100020300381d5850404080b41c2e4001420080224240000d0001e00072a610310039000360108002001101c0001c24251070318030032501c1040000300b07158041c010000c80b030409400b003106200c0d80f030042d4040c108070140c0004017050f182034103c0c1190b10044241300340641084050600611040f10a05250310080c0d0391b20341c00c5070001460314000000810b2500c4a400081d400114400c8c051a207503101d10f130050301c410102d07807440e6400b45803100031140f83d071084001c0421104e10104035111511802c01910141c1a4030001801078058951410b026500c68030042d4411801a0050040e400040c00028201103522000c641f00700c1c1c003145014810343d5510212610709200700446 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 742904505 1250 742903255 742903297
    0x608071416080c010c12091509050102070b101806180b010e030f060609090c010f030207051603050604020a0f0b0d020904110406091d04150e0c031c0e06040b 69
    0x200060120807100902802020406084820b015003140410b0040398841b11305040e0852200740480d128004094051410301d1910b040d5554242e1220f920280144009031500700c85450703088034884113880c003a1701d0103c0b07004204081d941000c0c40b003d454400703800500c00c031b40ca40401c001003418032511050b9174540d600c229281c82da00400d1441e0519101406650522042c04519038560204440c018000c0070400d0010b903181a02058805100780141c444007050350302c2040031002900310890450380d502c90300d00808012025421018000c501c5034000703103404d19151052000402d02ca1380a0088000540024440414080140ca02c8045d4290006071284804400030b40070b807802051070251070b9000039003c11071325817203c4104296070010341c05e4409452034103806c0c07000104c202d4000d0440c0d00400c4c3c1a910546490b085001140310060846169071350510002c0d04001d000c15842a51002c85000c03204411340104c03130340c104154120303041c908240c5401001000380c480d071403050090710318101d20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 742905755 1250 742904505 742904527
    0x708061009051003020d150815220807030f0e091503070f080c01090b120c070501020c100e011503020a0603110f030c04060921150612081306080714 65
    0x4450042c803004007400c1981521040c0a0000c0d80b100d0082c2000506108921103100740402080341140d6011005003640c00010200148180000c0c00f07100740494800c8240142c011042e544981071030213580390030381e03400052601a114806e0b841055050081d9686511403070b43d00d1642090b07120f100b1001c6039070301104000000e420b0803d180c0003c1e983c410814000325080400041400800d01c0a8850032400d075210400c0042c207005016441c180d5a41200029810840c924043d2680702d1003000050b081181d042901c07030400083d982c0c4260003e642d10095106403900340038090500d030050500792030050454002c103200510380c3c0180c005054564584d0400843c1c000c04841c0800640151f040d188d01380880011031750782c440d21075000010140e00c00810428a0130343c03100900032058407821510b0180c0e5444c040c24110b003100000c1040c2d510311002903041c00d55030301c41c031a0030711848070180d542a041c000020b00340c04c1c941008080010344d008008619030007200000d4840003c684283c2c036507883c0303c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 742907005 1250 742905755 742905767
    0x5010618030809061209010506030f0f120d060504050f0604150e0f090304151106010f12060c03061d0105030d0302160f0c050a032102030a0e0618040e030307110607080610 75
    0x5c590002000c0d50381c200601c0500c194410b5001c0d4200b201515051010012003a03070300c0c0d004103c0b10b2019044076003c04010100c80001b061807807583c40c000b05006a4543c0080c0455408071100182c41075040100035451800f413046403124840741903c103902c141081c0019180240c000c00021684640b20701199500c1c07400c000340c50060081003034410b099038503840004c04aa08142ea140c40368401d0500100781000303000b000409071100740030428000a225140c050140c100700c80900281540c6203400300724032440100c100002d42091a000c00154900000d040c0740400c41d00002c0c0c20544141b02d4500007070b0314404200700054110701d0b03444500003d403c1403842d10169901143e80056082d50000400c50540070349034070843c426082c0d81128020a10030381c2c60740b05540c950703400122a00042303000d9140c048003405540104e650b00c056100c810201240889a240d0b4010032940e01c08005c004985030b00490039400e154400780134025500744500040d0104030080c01c7c44e0b02ca01c2c1d030415a600b401e44660 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 742908255 1250 742907005 742907017
    0x9040804030b100e0a0c1403071701140a1d0c1308030304140c0a0609060507060e0304061107060c031706010219080406090e010f0b030702120d050a0501061803080906 73
    0x809842a90070040c06407100c42e900c9101d10b540700ca0540000070300c40c0c1c5c1c061007152075118517030b1200d00e904a405a0401c80030382c0300804000c1441060940007801c0d02c5540c004074064640e00d940d104d04000b0240c20400717403442c03036440106800100d002c0101e2100c40403080340c1d0848018081079441c0c41c0c0c0f071030410104840903000700e00da903c000300801042c4103211502c003003032410000580e00401102401e2000607500f0340504030100303603110400c2100500c110300807c0107a00031303c3c0008000c00301402480c2103601030303840a000101c5034007800700d02c043c050280c400180070a06081600d560340b83c1d8044c00d000c00283c6000d84d1100041c00041c426402400000c14941d40101705d0f40c1241251f1802c9146a000344c01008000380c8d44030000300c7c0462105120700e0586a880c140d522070249080081e081e245c2c002003489086000c0d509a0303204a129020207010314041400c0040340919001070003504540050b88100c08000b4000074a028680903220502d094a800800740e640c0c500e8806c022032210b2240c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 742909505 1250 742908255 742908263
    0x5070308071101081303090528030c26071208090303030403171305030f070203150a051e01180e0c0a0b070b07050702011b1a070201020d06170a020904080403 69
    0x18094080001000b03003041004002d895130101500c94121202040c4400480203000c180c0c908414007491401c00c15402429245000f210b0709004141003036051400585d10032103070312281c10740c14400a101c9000664607038542941364000304144001441e603c00c0c4e030f403080c440c1110340c2803000c01c14013000208884410341c2c0501201d5582c14540303002070841a800c8001220040380e1400300f6101e8211400c296861a000b00055050002c0d1020014866000710303812a418815460501c04c0c0d4560007500d10711a682e41e190000d9240f038100d420f182c40b411000c02c0030481c862008014172138021520703a110728103050307808001101c1400109a0385460f4192000c41d50148001000180c61103a000042c0387c400d218040504040e1910101030300c49009052000b03000c50320081e02c0c0654003490600800001c1e003d9081604100c07218940c4d0940d116007501e6041c0140d400003101c030a007010a00582004001c04050505120041c01030a52a104201002889070400c040407400340540c000940d4050340e04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 742910755 1250 742909505 742909507
    0x11d010b0f0915150a0221040803040605090609091e090111070602031009021603030f0908070b07020102120c07050f0606150c10060803040f0609050d06050711010c1809050c1605070308 81
    0x5400c0196442c646031f41544000000ca07000303c000d081042094401b1907121ba0700550511782084030513102904200f4021790844014407544040d56900218103004110350440450003413054a40704400c110000d29100990303042060341d28003c03801004580906070880001a140e450720103400c402000d81d40e1140b0f040b60b0012a80020712103049004050140c802c0e28104005000f01c460481602d10900b80680800e10901417980401d030328042d8547c4c00440d5100040c907124903055030110504041d80e40092102c000b2a400c001c11204100002041401a004000e50316003807002889440d60b05440e00200344022501200090040140c40c1c840c5007915000d0000e42c0e02c0b08409582d80d0440d11543d18160302c2207100140c414010480407041d07a002038400c0040d00c81641300d00020b4103000d060030003040383c080664548000284103400155201c0d0365003c030030703800c14481c0f108580060380040c10101d10b05814000400e0000013160312012161103440c244142d0350070014108141c540c40500f520b80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 742912005 1250 742910755 742910767
    0x1a070528020d02010b0a0501050a0216030c140102030c101d060a0f0b060f120c2107030c020309010e12030c0a05070f0609080d031d011d010b0f091515 66
    0x12514003000d44080c080e07400c50341d8006481c00124281c50712803014a4100310300d60020301080d4481e000902000840d80100c9500100d481a507801081c46980305035040e2409003c144202d0403c40400034000c4001d10040d07003003014400d81141c840303880b14400c41c00d01c1e07680c0300880910708400040c03441c002645420744084c5d00d00000d0510290880040c2d07c2080c52620038007080314642001501c1e00405134880300c0303081080c11800d0740e03044d400103420341140072410300c200b141c2c10b07140e207004070300d240140c00304403005080080d00a82aa0151066141075400600c03890005981c08070510862850807101401ea400c1c1d0340810b141103101d482500c04043c090b04115902384040021580201c403001600300a5066503042c0031100030000e4091420a074004c00d95051401d4441d41092401054100641545000d0460100d0031240024a07103240c0180500902041c07102c04e202c2d0031640d10f000d0303c182c00550502c400058801c07d0003040e1082c5052402802000ca49030016140034642d071070008031b65604 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 742913255 1250 742912005 742912057
    0x904050a1803080621150907050418020f0418110a0b0a0c050f060105060301095408030606071a0103210216050607020102010905060a050708090a1a0705 67
    0xea400c44209000301400b80c4030b208100e03402201c4d03400c1002c5c0c1c0c1010f031102e0b0035030b00d4a00c00084405400c124070380c45034107408030b5650b1f61840bc1c5a03100403080d5074102601100e106015440ca007504415111724906441d0380e00c071060ba00c001c40c0505034071821900d07d050f0130000040303401d80c90340c002c10396060340412840141600500488251805041110342009003486201c0c0d0340d46090040b02d4010405100400c0510019004550090081d0110385440d00710806501d040b0451742a40e01c400e943d0101b948281c144001c048040c029030907000441c6031000c152540710703003807001801190150400107917038400d12009240300c0040c1d090600c01c1e00a03550756820000e08403c82d080080041600c41200e40400f2800042c4d00d0040504c0124a55410761614042000d0360b0007441007a815075488402c04400940280880c600c100c040c1d07840000c00d400c1c070030002018840004c0c040085079014003030544c007060a40c4401c840000b0f08440454180d550b100c02100c03103004010340d4110f40685010080709003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 742914505 1250 742913255 742913267
    0x1801150b030f01080303010302102a0309140d05030708091306080304060e0306240f090c0c0705030f031c1b0801050f0a030b010b090301150e0103260904050a1803 71
    0x642d600c05005982642c0b03448407a900c80c0300a01c00254003803c1a204041154021041d0354084910740c001c0001002c80c40c50b8050100f08040e4007100000d00326003080c0314400c2680311304660344030184d0781c440d0781400c20b54450703135a0301c00d0b010098100d4801043d8801103645100b042104849904000c0c0043c40c1c0d51415507680c1e42040c09810081544826603140d90704001070740c2481544629040385914800041d01c40b40380c5104090700b90850040c0071100c8161b1910349a507400740c842040b00f1070b5681c11100c8000d0a242d41600198401d03085080420703440d680c0002602c00d5100300265041100032102c008078028001d02038080640b04030900001191a00124440e040f40e05c140e030094a2903000e101000510038903800002d20042101006110355140100600802c0c1c1000e800000d44c1035030404480c8280c40c495008910b0407120350010b00c1009488203e83d403402ca044241c0511544e092907130290369006000726540501e90700e5002610460b000d811824558101d01d28010314019242001021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 742915755 1250 742914505 742914511
    0x130903080a0e33060105071509210507050f0604050303160e040f0b040b12070611010b030708071409100e070c022701080a17030c0904150302120607081801150b03 71
    0x18100440f0010720b041d402401200c80d411340c402c4100308a41205401000180f0360b403138003a18400061000340003c2c8402c1e401e040d04035840c545920f902e481652810392302c0c00c1d83d40180501d01d40c00072014080040d00c00400d81e90001c62a0050310422804070900300e504045100d11150f00a040403c40c4405100070b9120815541c016902404869200400c1c0f1102040250344c62505a00c0203c0401600e845885242d08008001c0004a500104000020b02c0c01106400511050b0405c0c0800c0084440701580b03410484d5080c2d41c2401c8610740b12003000c1c801a003030b105c1c00e0b4200c06503600140700c2d1486000100e070501c0d0f00400c00964800d01809561042440c80c500e0740310424000008104881d002032501c403c40c3d40150462460710200b81c90303c10a800c05442602440420310580d11156114001d00560f0000b150135200442e20f10700400c035104809554424030f64000905100900d40c0c001c1c1d42943c0b200313000903010745142c41035120900405115408100002c5090000701e007266000b001140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 742917005 1250 742915755 742915843
    0x60705032a0d05060f01050f0901020a23060108011803200114180109210507080a030221060306010e0c0d02120405070b120609060f0d0f02130903080a0e 67
    0x102e40e60b0b2010b0005c5840c60824081c086001404008400061072005001590040c4142d40e0a02000c2d55007101d001500f90300482c40050400c4d090f175180340300b00591401000d03030800074419100c081228094481c5009009010004880740720303025139091101303501c04186000020000394215001d50740c0340d24070580b03071050517052030201c029425005020360a0460303001044c510411184401402c0856000d0070000240b007030a20903400450755950261070501d00a407000340c0d5925810a0040c1d144801c5a038a0640c038660381d007072005a071400550181524401d00d1200226101c140c44e9a68600030030820b49040381c0005143c440d00342c0c04049807406680304004036005903480307c085040c0c030f0040850f9129800301490000c1e000f0300e04944010b82044000d06002a400c2403c00442c118890303054050341c01403000042e120460800000f80515120102c1c010440315100b80e400a0a160000d40000d0031540c80c1d080c104030503c0241b200038801042c4500001481030391540340491000f001c03000b61 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 742918255 1250 742917005 742917011
    0x41e03050105150117060103110a02030c01050f0c0910030b030a061a0a0b030a02071505070309022d04020d06090c020607030f0209060d0f2012060d0203060705032a0d 73
    0x140001072152200c0f030100340b0507181e030f10103203a20076141c6500c1800140103034101074075060070203a419003900050862007000c2d07000e1651111a540440e003503600140c21034200c60704100030130981c00300180035030f4402c107022106109460010300d421400f502e815140258180110518001041030503070000f100c0702c0123a2041003181c010351042145414942c85504041c1c24104001901c0c0c23510740c1e0081500c03912400c200812501c1a030040c90841e0320444071a00440d6a8414000651401c2800500c01ea02d8401a9001a03142c840d40711882d035168840e2070f0b00594000c64858987c0b800307600000080c01c0c1c41070003005041520384000703588010a5030040301291174007855a615231024000c8500c0c1c00b070040e0040f40b8005600e403809006080383e016020585a56131045031981d410740c00c0b000740101c0b92070161a1103031030282039400c14150141c2810302c60099469a2001a1000706141c1e51040c0302e03040071500c1c4c1d43e07103485a1f1003400a00030108140000221020b2042c066407000e4070702407052203020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 742919505 1250 742918255 742918261
    0x7020f0438030109050a0212030f0a031d07150f050c0307060507080c04050d030f0201140a0608010c030b091b070803010608041208070e370306050c0a1e05041e03050105 74
    0x3040c04c803540c480700a00160090352200d000f50811580303140c00031344403c085a01d4021403200141050304050740c07410000351180d00401e80c0612042140c441c40000c500504426454a0403080803001d042807100c05100f182c13202c0d140164055000c0e1450040c0c0d2805072540c507002860040000d14080f5003810200384048049826080b04a0030340f002d42d0400792a140b0003409903101a643d2484541c80722003150b40f2210384030341c0401c9601c01e040c005d42c0100000f00e440c9041c172102c0303403d40701800c3c000000c252403c8002d000707aa8411003815001a400d42c8484800b000c0648200e209118119000c1c182680000002610301e51040780c25200740c5c01926544c0180325804802c42d4000f005807003100000c0c00c29852000d051408688024a54000341841401c88003458262089038644040c0d0701ea000304034602c10000c0c8405405620381c081003114505142080705036000c1c01c0003030b041c6402c150088010710b440f12868058806c0f10081c040d040a001c50030080407500d509103039000c4c08215a15400c0c0004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 742920755 1250 742919505 742919509
    0x15050f10080d170c07140708160e01030f060b030d0809120c030301210c031a0a060302061b0c12060a061703040b180405130615060e0402030411060307020a030f090b07020f0438 77
    0xe080d0030b54560014407007480c0d20b503844070310b442076378080143c0fa02390b0703142c0f01410203035010030099104000c00d446128061030000b00d154100b6000c060207496401003002400400c820201c02c580c1590011040d19000440c07242c007405035606e50b898000d12003510103034080240040c42c92504c000f840c80b0112031120783d0b10041240140c07919444003c6d0040800d00135450200d040703480e10b0840c02c42c02011201002c1e002c2000a0104c88440104c0316103802100c1488809403407801030700054100300e4070440c05441950741c2d066a9100f41d115001d81014089203100908880e540c40b4403482c02c006209206506002c141e071102d4410740c100c02c441d00e0307240288443c10030a05056001c00c50b04243c58403051b008a56047c88060340c4000e0003160045004481c441c81c6a41d95405140a03104550040064050518001d010a9644016101400301d40f0f5010002560b400e01242e0400d681501c0042c3d10120040109006e03000c412401c544441c4402c00608201e8201d0729044420249101c1380101c91481c0d5003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 742922005 1250 742920755 742920793
    0xc0408070b0906090105030a140a0606021515010c0f05011506170105010813020a0902040803030601020d0c0f2d03021023010e0415050f10080d170c07140708 69
    0x2c10150000f40c103010440345507001d0710145038440144007000c500300c9a4090702129410044500341e007038035030f910001d00042d541002007030012aa40b140040090400c0f88034080880d034240115410044558801c40411020120b60b82c4d0040d07101000703011480c1181d20901340c02d140c03401440c000441c1c070705a640c089070100e40c0703040c122001a102ca50b42a2120800d5484c500150780b801d90300036004420000d2040407520080c002448d02101450310382c20700d00002400e140c021a541c1041000c1d0800c0d0304c0104101000040100d6030002d0342034000c00404034100110600140c40f4481c284c0c100c0800414581c000c40c0c00c100c0000c0c45482001610344280ac6070500e940280110407003017501c0e40050010025150100340c00900810881151860340024842582c1d400c1b01c221500024007010311031b50000500303158000e4a50b0001401e6a2182400b000300003c58600550100f0310104000c40d064115203001c5540b2070b40c00c600200255489060013942c0d403da68815007120707100b0300000d003a0f0405080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 742923255 1250 742922005 742922017
    0x4111206070f050d0207050a0c03020f06031501030b040e0105071709010c02060604110f0a05040503070902040308031311120a05060c04080a1b23010e0906010903030c050708060c0408070b 82
    0x2803900e8000c00c0966a04482c503812504e41008050f50030002c490100b442009900722680c8201c4401052500390320510094510304100180502418424050070481412182d000204203103800101804110001009070445d40178840300d80d4a401c0c14401000d50240b540c006902104100017010344440007a00e00301e84c004114100180c20540125600d898070b500050907501001d6150b030b0401042c0c0c0d801c8400d0342c0c061740045c03000c2000000c00304050306007401100002c04141c1c00850801c0d01e941c8540c0c4051000912003152450400841c41c100502400c07840e03a2101c0c042c1c0416840240600d64503924049440299a01c1c403c410004448546160484083d544283d000d411070360800d50303070714041000d40b03002c00c40c440c0303040d800108903071142c4210070b5806500c2d02152403561a00c10009800c1011a041e010b005421400400c00140d0700041082e00700c0742d00d4585a1011040342c28824185482904010118090001840b4041c110318000c0e2060301d8070f207000d40d4400c541e0362071500e03500d1040d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 742924505 1250 742923255 742923257
    0x10b0a1419080a14032d040902030115020d0804081b0f100207200f060309010b092509051c0c05030d05070203070e070801090209040209040e031c140604090f06050411120607 76
    0x2c0d003624070280304040041892280401b4150305040d00c408865040c0c1e00240c110441d40e82d00c1c02c0760781000c50f5040201c024210341604107680d06091a0715002d000e4031482c100d5440a0f40c2101c505107000c43e08001c1d840301c400c082400d94031264080400c8101a42c80007505840b0300e5a00717442200c0b0303400756410303090140c900200b02c2c840080b0032905200c00c9401c010074503113055589402848650300c1d110321062207440c50210302651100124220381001d80d4890340c03101000a41d00091066031103840c4950140e10700c1022800d00d04586180041c540c15641e00b003241c050040c05206441c15420001600d2054801c4041e43c5003562107803124444000102d801c1d1000401400040020401075401040003080180025143c2403010f008a810358411603035030400c0383d100140307890058440e42da019001800140040c03020f500702c035103a110031f05006480503116030341c0c801c5e504040054103030100410940c411020300043c6440c0c241102d01007032020302180281c07024507100800c040041002840394042d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 742925755 1250 742924505 742924537
    0xb040e06090d351006031e0f151404110c0c060307111f050109060311150412080a1e0206040b04111806040e010b0a1419080a1403 57
    0x242c1e590448001c0c8120700c1c3c2e10300282a42c100354005049041403075005810806500600341018400d0360103410507903008204142c40c109070381c1508030468030708010010103c04081890b45a88400500800031050703030905003d240710000072141c00d00320036002d4054003203508001030004000080034920881c0b040007003641100c8107510591904401854010b20f4a190003200f840301c01810070f240061060381c8443c9440e05401c042007140c054000c1c5409400700301d006100c0f16286030b0725404c0390120f00b020342c1c1c4600002c113903490016071108141d600824400f1b0040c00000894146003c05502c8882e07048006841d2002200c000b801f42d05104003c444103074004c200f0f0381d5407519041e074141c1c0007400440f030345a0010003214450383e600a1024203103079041200ba4540c20804100700898404030b00801d61a4104000e8103c1c607551008280300321000001002036680c3d803000002e00e001c800c90701b031801162010707001040342c19000541039900c611a214000c000400c41c1c5032030ba0b490003004c4400c098800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 742927005 1250 742925755 742925773
    0xd0c1502101104032301021e07050c0406050607030c08160c09050604020f1c09080a05040906142d03012d050603030f07020409080a0f090e0907060311090a0303030b040e0609 76
    0x4065045c22841d6000c610006041100300320104040c03491640f03c0d203c0365140071501c041031040503c10070000ca401101c0c200319061400e808500d01e03016424000e170034012a485c82105002c0c40804035049481000c070389516081b00d80c9403454484805000d00310307155281c01d0003d003950a042c0708648443c40403900d1141880100f5070340402420790300000444085c0c0380c4480000081041c3c020b01903440c9a46c0320740c0e403034500307080c001c0c0210b540a0b80030405540d80c500020525840356210a404860b0702c04484881a00154440056080c4d040c2d403250190310300507405030041035440b0242504036a031003c48503003404d11040300e8150384054a08640c10f07001084000e00000460000741045c82c4050f1012a100c41c15890307881303d03034005190007004180003050709600c0a500100c4000030389403000262405040003549581d0304c6480d40070383d0062590303c6000341901280d01c8240c88400d0402051170340d41c01d440f46801000380100721105805107082c21207242a0703040c04104581310700654801855502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 742928255 1250 742927005 742927043
    0x30103031202033c28061a25050a1202011e020904090606030f0215070507050f0d020405070f020f0a050604230a0b060906040c0e0d0c150210110403 65
    0x150103903104601a6180304000e072500b4014840c860310a1110035940b000081000c2c030021507990700204c0800700d90b803500205002c0c1c1c078003840040c2c4411030107444903508c480080c214045240f03038041d1220054483c10035104100000050882031007407040c07940b1010101003540607420303035101411803503880640031480e581c9070000d60b0141455a00061010030b8a1070302d621120101e42d01d9030400c0d52440708050300c036002d40c20305550840714040703020560b40ca00b0559446803510380800d800f81030b12074410203221130183e03580e4000d000070864000700108400d0410b41006041c840403090244050700a407007180302c800102080352620544c100000d4402e5944559038960301340e1148601080d18250094040410320003040481001031140c5580700c0c0307600b0020304200441c0002840c4030720481c00c103018078044680c01641212486810707a0001d042c1c541c14038016000704156005201c00c40303085c040c03100c5115400a414108015070480030085410402e0401f4001d100341d0201402150824000362409 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 742929505 1250 742928255 742928311
    0x5090601200313030c0305060705120f0406060b18011d03070303050c190b0405060f190518100c080a050705030c0c0708010f0603111906032c0303010303120203 70
    0x2805418282c034507028948a2192181d00d03280c0083d02d5200340b808051040090812210f9045082c3d4105281041c003024030503103100a00919004070200703100301050800c001600301d01e024021a40200781c5951001201400c820300703003104d10740068410030403180b00c210001c4080c08021400b4001e031241504580f001d482ca60b02003010a45244960f030600b80f602c01d40420303148030481c0b0440e6603580c9400d080c1040c070702d002d0001d0401e07615034120703034140004000011403d01c070501400c40b01140f02d540d840c0c0000c0c24245140c01d910000e01a42c85448014840c5900c025101c640940b20040691076151119040710404c89400d03007c20303c100082030b02e4089500140c400c1c1a0190202c034015901e9412031400d4492200141c02d0140d1501d500303008000301e150002e1654141a030340030110410440c0b0742c51a50185120307802c245980c4145041511854680180c0c2d04d5001078820720201d44245640c40c0d82e40d109201c00d800048101c1d140d034000882038001c580c0548181007000340226500c0f8092549 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 742930755 1250 742929505 742929557
    0x1050310022107051c050702030405011b1a18010b1e060c1b2701090b040605060c1c0215062e022a090a18020d140705090601 55
    0x4142c8a075100c1030101d9021003681c510410a641e0b5081d02d41c0030142c2c100d0400c240041c4102c1c1046c0c2403c0c1045145640041034a04507035007480c14103c2100701d407410b10b414048107070000d002403012981040200b01c0928900d030280c00e561003e45650b204c3c1e40b81580c22141418a1705520a110704101401c00c402e004801c0300b0414010002840c00c28000402c41c5001001c0c08031500c100b5074996000d05626280001c07221805040c014001c510a5101f4403803040e01050152581990781d8a01160541c0c0b02c40d840303400940800b0385819030f00d4160420a07580d403401d00c100380142d80250170200c07004520103d0410450a9810617512040d01e4000811040003101180403610091114080c002c10806c1d994201c0156800e401a12500506003001d40000c403280788038841c09003500f003d200454840404a82c2d05c000e00d1a000501e140b03414601c00c3d40c1c004e0b01a00650702440d5a440042446512951078040048403812a03088075620002d00522040450b075441c0401c020003451102c50300309400c1409 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 742932005 1250 742930755 742930777
    0xb030105040c0e090a0c0807050306091918030203070b010902070c1a07060c031b1d040906020f0c061012020a0608090106080f070e0c040e07050c070305061311090105031002 76
    0x105003c4040085a0142004c0b14007a0b00c070342e00c8080285441d82c1100407141c00c0b03001494000d24515100c00480e81404010307014400e82c50320300e08000e001d01ca030340d481420031400c082e9580f00c0e37003080c40c18025035a03000000241c568044800c0009009185842220340150f804455a81a546080320007200c21005c0c2c4030300031844004110000005901c0d100b600304c403241e02c2e140040e028030300c0448018502d2642804070140030b86208a83d841410a21031420050b50451f408a4850750702d140c1140a0700442410b11a0b90002161410b580c03240401c0f920311420894500981d00c580d00e440c8180b5851a10318040d410805400c42480781c01e01c204c0000d948914600d00103c2d40d1990f13103200070702d404950a40d0f99010303003016030113002071501c550702d4079045810348048504003400c000e4203040084001d0f00c0c08090000c0016041c2c21030340c082c40500c0040d50001700b40d50051034440c6110741c8200001008a0b09181c005801184604d030a00c01103050302c80c00340c01094040e0300d80e41800002d40c00926400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 742933255 1250 742932005 742932017
    0x6081203130602040f14010f021e030702030709060e0702010225020f0d0602090f090115052b0c0e030a03020a0b0612010204080c09091203040605040309080f1b01090b030105040c 78
    0x3501145443c002880200f042c07905a022461804c940f03441040407100d001c9041010440e0255090340d03001590031458950007444544000c1d84031101131442c0324000000750103010f1400c0000d0b100c54181c3c46401110950b100040060b521a00124203d110305074140d01d184800140384400707082030710600511203102400040d21407000c8000592603441c09041107845a400040740c1c0e009051200000100390016142c1d2081035060080400350038254200000401c90082030341d0105801580a16003044604040c00821440b04034a0780c0250071804481c40100321001140056401c0000700e540025030581e0181000c0c141c04c0d6110b4074410b0b405030440d40d00c0810002038059509003072008000401d103240081c01b0106d203c7c01881442240101035035a95040301e1010946401100201c0340e01c19071040c0002401d0b6039515065920f260070b034129080390300c0342c079002c0c0b400c058001801a42c82104481908495205140110b0b400e06150158104010040c00100a10308043c4c03c20402c50303034107050034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 742934505 1250 742933255 742933291
    0xf0b1314010e03100b0a1a12060103090b0117150f181c050d0e0304050607060b010302070c030506100807060e060702120321010e06010c0b100b031008010f06081203 72
    0x6840c000c03a94111804a59507401426003d00d846c12505004103010847c0384240f001d651032010040c000c0c054950390309000c0d6030008005078800e91003495082c2e8061501d6005507160841d13034042401e081c52041d090704c501c0b4080c0d9420340648003c14072812007601c03035499036500c61a403a20540300d6429aa1450702c9000841440c00050000444112000b41c0c0c2e020b48940c00c0403502015507580c0216280f1b903800411041c881e035111001210f800755080364001c2a00c000d4400104d00a11844101404541d646100801002004aa428090418002ca0a100f55240c0b4035040d03c0b20101e103e10004507005030061802401c207075010f04030f006c0c0001d14201030808511155425503100d119045071000e03602003245a02ea21020005002d868034a00c0c9509500e466000a0410991940060819596180003a48124031100c0620207482c01c14203013922410501021804954540520f12140d400c1c8086142909590300c038940071240b00c40020b1515002c0c0b000b5a03003503584050b00161107011b080503c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 742935755 1250 742934505 742934509
    0x913020a030c0605280801030f0c05090a020405090f27010906050702061f1412011b0201020a020c040504050601030305130816090b0904030c080d140a05010f0b1314010e 74
    0x141c00010803c5484082d540ca0406510f5002c060601744e5030503401005000c8051115032280400b8152a07101072080c0e200e800c10b0030000018201d9034411035004401c0c9041001c110b0064024108481054400021030340b1203540801c01d070001142d480e0b40d50360300342c1502c981800c54812807d054618aa0000400da00b0a0b00c94800307403201100c00c280540d002d1418002071048600000f0207800411941c44405400c10007086107071092441610b05c5240300c0d00030360340d904800303602c11188402d500c12010700d00803058001174003030b4116000d4080036001d0b03501c0321a030904050203258416603106000d00032682c00c6070390998090f00810018414085400c2c00424649801c0200c000052502c00306410325034a80750515080d40c43e410325090080d61900c0500c400640c211403900074055005c085581c031541400b4104004151035106c10144868460130b011601c0025440103040e1119900d9021945484510300b03d01485150050410031b9501241000000c07602c58540020000524000b24508001d43c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 742937005 1250 742935755 742935773
    0x91101031112040b070206060603091915020c0c1327081204050a060f18110f0402070c0801050a0e1905010605060403080a09080f0d080c0d0603120e06090913020a03 72
    0x3e0444001e10700c9414028000d03010419980e00550880e0400e00d146001c517400f98440c000794640e000003000610150781002100c001118107445003180840d1a6440480342d541e40e0f85280d000180a80300c1140440f0072100c0d24000d2515035035070310344007140f40005440030340c0b10030f6010310042e01c070f2807400d0103114003420b81420250f00072805040280111011400c110f802c41e4003216441031034900d441000b628020465425007101071b04060040c210301e41c400c0211741492048040c15900c01c0c0b000590100b0080d04118150a550207240204815501d00748540115840d010010b14280c1c0721020440c1e00c11401d1401d080701500c15030001c5881655000422200c3d00700360001c0b91502c0001c5490001c40d580f100d00f4800400c0b04034010050204581d2085449040307104245041221010000300020604001c5442c2c04107a1903040000b81d5a07410000f0080d90846012000a03a185074480c040f40f500b001038400f103010043c0f8051054940c018000000051420100c0c1c0240700818004081501c0d48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 742938255 1250 742937005 742937011
    0x5010e060c2b0c02010801050105033402010e1b13021c020c010b03010605211c0c05073201120504081306020a050601090b010c0c0f0e060103091101031112 68
    0x3101c14201c2ca48a034140c0c00d100511004007020443c00f9074041000d40e0b4480e010074115403080c03d00c13561700d481d03100c413840911b220000d000f401820840c00d81a0b0b0142d41e0300c05107141c0201c0e54001c02c081c2030000364440d00c920616003420481000d1034100c001d6890010451884a162030000501d02081c13000d801440c8400849003108555006c0382c0051080c4081c0104258964210000c000c41e6003400f0000340903103d0302c0b5900400545525900e400c420003003100c00071003440c0601074140002c241a00410003c141c68003112640036404000a40c1d640300c0d010300410400c0c42c070381038105c00c00c1070a43d1b00b46000440101c0f0b04005400349034000346006c9200b281d0249004041a55445415106001c0c0000d081e80c04182198000000b940220f8030100d141c07815905102800705220481c0c0c001228000c0000001909820381400c001504070700586016085540091002d170309540c80d80015001c4030b581d04005410030500032080c01c80b66100350302403408c6010000c005410000f01241d4078004100072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 742939505 1250 742938255 742938283
    0x6030e0313090209130c09030b0702030702030f06010501090e070c020d030e1c05010c0c081b25090b0109080d0819060b0310080d021e19050c13020405060405010e060c 73
    0x140044641452540c4004081044c1c0d81481b8000b912500100020b480344009031140e58882d010900d40c1e482401100e034000e0b00201113400406007940e81c1a02c0340000e104260100d5204800054a00c0b203a80303120348100101d03201c4101011540e0240f0a44209100d8101e0402a1009410005542d88040d0600482d009620100080468a40075085032400e8121001307001d504641d4000050303004040340d4501140064440b8a0405e001c0402c1c40c005008110318510074000e6044031195864800349411103008001c01e001d607078030180044d5803004d16401582e0603604401440450b8074018010706420a60307040900d00d000340103519070421519a90003500da410b400200340804486410607001c043c1c860034014009464030304101944d2031500f11240101d0040f02407050108110a03c10511041c084000c5031303200c00c03000d00c0c24544070f51441060324840c604212550b842a041d40c42503409982020380b81b10b251500703020054540019520a0a030b002408200406030040140070b1107480307001d0703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 742940755 1250 742939505 742939507
    0x40905010b1c02032202120a0b1005010e0d060c090e0a0f05090111030115030e0613051b1e190306092604030f03020c0d030806010f110706030e03130902 67
    0x28000640e42d0304030310700d001050124014000e0000300060b00705140c3c54403c1808011400c20050320200f0700c0c840d0075070803041041c001e03190002c00b40180c0c0c19201e881118501204034500c0c1c1c9482c010745203198000080c9401c25060030b040300020740b143c0d00c8120307240e229091652180e03076645105028408111204007049440d040b241c060203a080c0201504440030b40028410102a8401c0c0c4004e400144104180d07804c0540300100c40f94004c2e40301901c861b100b00c0550f0403034502014201c034500c084100488180c41010740034840c4800002c41000e05000007403a0790343c440e03020f02018600200c09114658085142c0c032020341c0c4040f003540e0f144000d61041e040414003507442d00742551503d20501c07580108400c1015480301040302c1108440075aa0b0042141614050f18142240741c542c41041c80d50b048041e17009800180742d00315803114441c460903138030900300e2041b02008035a000c00d03000380805160701c841d20a0140e14020f42040030301e0206081100d0421145081c4060000304503808081c1e901e038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 742942005 1250 742940755 742940767
    0x4080d0606021614130c090902030c0423030a0201051e0c06070305060904050c100302160506151210050916030b010f060302040522020f1812150403050a05040905010b 73
    0x80141e0310f10000c0c210309400b0048184c030360010601e8440400c0d501e4003007590390001001004e000d0003000c00a008441070841d02d03407800700c000e1852540640075019040803c01001c0ca40000460803825403070b440a800344c4481250303540191402c0d00a440b09000c1c44600741f11400ba64007100c4050018104070500428460a24034006401c44101400160107407003400708100110300c0000d4201c5240c0c400740d4498480007450382e4220000d0040c6c01145010300c3c40b0040d400240100011803601403140b4503040d2924050510070406600704100c000b039056045038440c081000c840f60301281c1d02004100c00c0e0380120001c0b507012050516141c02c1110401d821390300511045882d0440c0c2009004c85003811460141040b00140300f908840480c000d0120082070740c281220030540554400780100d0341515140e010ae00d680c4051070a80840c202d00414250400041301407000485d815405100c224045848d02d483e14102d942c0e03441100c0840600404000000c1c0800d024800d142c020102d2070300984d140c00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 742943255 1250 742942005 742942033
    0xc050d0509160b0c1204030609020117061813050f03030103030201153c08100f02041401110a0804090b310b1f0f1e0801060804080d060602 61
    0xd94081e2044400354808690300103502032a8101c0c50540d509600b59a88480701c13044032502e8150984142803801c0ba02040002c1040099001400000c3c400d803074105084003104020000700200b200c105603c4200c007522a4051118100380c40c0d00b01c0006440d000d6512450345540d460b14507116083c10407644000700401c145542841400034a403d2000c1d4030100798640841c01000942c2c1c0f40000d03100e451206c40b00380360600f00c5541402101e040c4100b820161b503075a5521604c4444201c0c90511306401c103070940d09120858801c5070191195400b1550011105000466103400c1c0c00034148030512815644001044040d0040c0005000100022442001035000d00c414105070b046041d06494550704c0c3d00c050720340b9182c911001d40c0c101c0c6100040f60010600000c0c0d4400301540040c0310044c1c01d41c001d00c0029400f026075141e8406c03523100d8070300b600031100a880c40c1c2c000403042100007454082c0107201540c401e00c2c0c142c1e0098064410a8109aa034040c1c0070216015940003001503801220017030700030307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 742944505 1250 742943255 742943261
    0x1d030d05130b120f011a0f092e0908010b1305280914162102090c121f03030305101502060f06060a020a0b04020406180c0306151706040f0c050d 63
    0x14000c803803001c10307001d40c00c0c05018146010b950420007e820300880d1184042d00c40d040c1c01c2180503502e0000c00103045030b408031f1701014101031007030340000394800c0008901020140115621000c0103040a90795000380c0e0205001404040e20a645540404503002c50019003106030361418414141b0001d20304189292a1010003031000210100b07412044000300301c7e542e00c3c01e54000b1918000d0780403070300048507d80003150701c42c3c1010095010419009100c1c151340c4100203010144102c03202c2a8075030300c40d0403405040400400c0300c101c000542c0714050002030301c203411481c0c00000150f10811880e49812860550203000041080140d01443c20003040c000c0301303080305e0340084042d03c0c0f2910f00201044001c0d101c008001d000742010383c85001140c01c40d1034950001d0024136094001150203420300709041c1c0070b0240e10840c82d0000f410440041201d03039001202031219039040e20341c1c04d443c030090300b03800400882c02443c0d01da00c16500c80c0038034245441070041d2106038406982d8070341da440c1c0c0e43d0104011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 742945755 1250 742944505 742944509
    0x9030224220f060c06090201020106050d051506061321061406030607030213050f210f070501210c030b03070b0403020112060302031207110a0303080402011d030d05130b120f01 77
    0x10440c1100000c000780e030342107400940e003190060702c0882c1121b554001031717002d020300b0b038015a0000390741d012110500102140c101155036084005140a885140c1000a180a8010380e4220401044401c0180884585102900c9903031204220ba1502c403644842c0100c40103d0a12760603541c00008010709131600344403e40c0d1000560400f181040604023030280c10414a02600d8010428403c0c0c4c40c0c40303540e031401c042c04002d4400c21f0005008000203240303a2600000e01c20301c0c080e403040b010045504d41c00b490418000540000344840500851800300d805061201d0b0f0460a0650311182081191028001039028140504000d035450389948001800801d12800c60040e480c50102c0c180016035000c581c2e9071894054841340e030744030503650a0118800e142c0f0f900480e8410130345480007082580100718544180c3c006d803941c0020b80300219082c0c04813a03400040355815000b080039401500e0041c03003c0c1640303052003000d00200c26200d2007481096403140c0341000d403c80038a000c103c2605007000071140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 742947005 1250 742945755 742945769
    0x3020603040c09200a05071505010b0415020d12110706050106081902160f0213060801050103120f170903221707080c042a080907080a02010903022422 66
    0x13a4400c500c0d60640c031034003449a010080000c00541035041c8020480c90034070207950758800300000d50303580c2e030280c0c1c00340c2c007611400520a03042108151054000300340b01920b13a82b5500c50f600003000c4006084000c0621541500152005208050110b4440d01c22035000c0d1005480399529400c0030564010104404a006046e5900400001069811140315804083d40c420b1449030223441c644005950000c1c50800c1d40a0385244c0180007443c04015002281200e003e003030141004079aa10084413403415182074100416896103000520064484040f980030410409607420001055000f4001000045145000704040e00c000c1c0054a039804040d90708100703660013410303402e18042d4042d80741c081000f6128070a60f0f071074044e03041400e541c00f0356000c80b421200181c2d01c0d901c01598080c2c07050300d060b15142814864008041241c0a00049401c802501612001115491a400c1201a40b9a0a03c00d071006001c402d02c144c1190b85000600036000181c00040403110300d2240b6040c8070710b02a40680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 742948255 1250 742947005 742947041
    0x61b03070f021906021e0a08120f060607021e010509100c112b0f02060304081206091e060301021303050d02010c03020405130b0d020a09090605090102070b0c03090703020603040c09 79
    0x41c1c0e5800080c00102641021686d90089000790601402d056145c400a00b0000000410346840030480c070285105103a0b1202ca00d2541c0c40c5c8000b407000500903044c00a400c07003600c40c0e2500341030701910380d220300e08401490502e00e0721528002245203082010b0421000c561400701c04020016146188021550305842001d00790904035900814031007503000e04828000c00c603c0c04010700505896918501d80c000e0421580c03400c0030302d480180c6602c1030003480300c00c00300240810311500c0c112050782c0c01401c51540c44020101201800360144e04c0c060302481d450741d0f0070040310504803004054480110b0107007020f03002c805003032940682550b0420031610304140c410403041c0810360f101030407060000c0d0901000a210380d0010041589074201034030182d804504200009100c681d80e80100030494403510080c4a981c503881161402c2c1d00071641c0c002c2c540c04603440041c81000e0404050f41c5e0109240c01194a020754a170042056039009960035181d40700d00c0f41041c0000c1480f4060b02c480703031035520051 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 742949505 1250 742948255 742948259
    0x90b0703080708190203040804080d0906080105040c0c020312030621190602071502220503030a081003060f0c030b0906031c050417030702010e03060c0405061b03070f0219 75
    0xd0111500402c0705061141c01d41c00300c2c0308089a04001c8080d49524007085550b42060704100c1c0b6a9006482400c165100710010b4980f07641c40f5401141c02c0b100e0a40312030406e6405c01e010031003d85a26603c120402c001c42201c0005603030104440801e0040c2c8902c03a60792030404a040c170402030b00c0e00b400310300d000003401070ba242185000502581d60f0b50002e01102d400050900d01070001e44140c60014090101030b100b901400c00e950b9000348680000040050030340c40c2c0b41020142c15071241e21800d50b0541092048202150080600a50100c54110300f40c2c0f0b5940c9a690304000c8401403a0340c840c18a0796987c00c0d401c9650144201c144c2580100c0d000c00031440c040340040d41e910705550140300d1406600219000c02c5e400f807002c2d280640324000c8010581e0f880c03a82580da41c0d42003e0001d03400141c45d04204442401d002c0380d07840c06141c4c44100c5074909400d00081c880780b58400d1107410403c0c00d17006c8601c5007642c2d00b48040c00d10244950300001a08000f0300402c000280008070300d810b043c9000000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 742950755 1250 742949505 742949507
    0xc08180406120b0a020a0c151401060311090906010e1012060b04050d060e191103010f0605010f0e0a181b05040b310b0301180204060c060506150f0a090b0703 69
    0x283c0383c0c89010b00d000940d60f42c5003900215a505c0c6920001032000c0c1000c4000481116150400300c2c0000d685080d05020b6a41e03039000300d0130784006509420805604001401c4182000c551455100c0410305003001d09101c6940400d0001150170381a20000381c0c1c0d824201002c800e540140801440011624ac1c01c1038103020000306e21002000c030051800e0395603c000742d0f54500501521800d000520290100b2065500f000222410b00c0fa403c9442035203031030000c0400b0041841190207a0394103075507000b018581c001050b074510744101d1505038080f12144000038040340c8034000820185100340b0200340010039440c2003604540442180c003d100f02070101380100151030040c1c0341c022408045515420f407261000c0d01c18031083c5643c414050b0300599010403000c3d840002035040741c0865241c0000506900300c400103d000f00d005d0034000480c1080e90340042030139500403e070054801008040105013007095110640d105299405c84894040340c0d0409498008040710300a0070f05450491800742d483da4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 742952005 1250 742950755 742950773
    0x30c050405131d0f010b060301260f16141806040207080708030109022d070308090124090c050403020a1703041802040e2a09010c0818040612 62
    0x907060207260030b55072001c0607150301c0d085080b8003107005040705203100344802920748031000100c10f80c10560030503520200b1800d00d80c2c12a4125081c0301501c2815800da1304e001d0f0710a0503070380d42224075845006c491400500081c09006001110440a003a12528020111b041e0022000c030032441028451401401c8803c080c030a0390b070262081303400594481c110b10300307601d06000f40e00d006800c0040c08000403074075120340d41c000c0071800501a9240101c9a01c8440a11014492000d41900303140500c05000003d01840681c2d42010b140c0b000401e03484031003041c4140310b00c078866444c2c0c900c01007200c040244031001e02c1940000665403030321624160440d008a40c800303105114103e1001c0354400c1d8500020005d01c02d0340c01038003840102240c15500c0025660203900a030052069a611040100d18211140b000300e110340f59000b00700c401500b45003204004a5003203164110b05112030704c8840030014014000503c103004507115080c0d4104910424041100c200e5080110040d80010002c4089101c0203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 742953255 1250 742952005 742952009
    0xa0536030a0b0606220803040f08070311091e0f01060906030c021c02150a0902031c0c03030c090b0f0301090c020607020a0b06040612060902010305151309080c150108070501030c0504 80
    0x4d40d00e079a9512030700d21410a03000c41d020050b19502c0003144007007805c81c00071008000301ca6525094854081d00e540165440362018403009009a20b040a40141d0342070040b5210fa2082c0b0344000d00841c200190030400306030600310f52090f413011100d0010f1240c1f07500452814041c001074681000181c00d5050080d5840492003400b0140005408107000e01030b10822034a0301440d8044100401030400d4800c05001d00703c3c40710308a200b80180701e0f21a0140042e1400c00c0b20f036007159512955580c0050310242c1c02084500c50385401c100d68400c0201d04000d46000500b0180d00c030f802c200381e581d0f141607540c02c11a2a120424030840d0480b400f400569640000c13031103200c540000d080720f8145c6880000400509069022403c215003004a4000784241d9a22500b03015000782c030107018542e50555900c440031303040060554044502c04280c894801941c0c02410180d1081c440c0303078503288107988060b26051030700321030b82c000b6810100103001c808014442e010003000d081c00c0a00680158000103001c0303010b14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 742954505 1250 742953255 742953259
    0x30403050c0d1817070803040f03060b010206040807030503090a0b13020916020d0f050c01050406020c1c09091a0904080403141f0b0d021e0a050a08060604020a0536030a0b06 76
    0x100c000103041c84c209102081c01040d55008481e507450f42c0c0c001101c81011240b005880d014508802c808441d4000305166106603400503135035107002015641175506400140502e005486a65640310004002e100c1e100e00030400030009241c914100d104001c0905001040d007540408a0b442082c96107400054405080d18070742407100140600500445942c05416100d04056007040140410700c00c03d9401008a180544242c80380641240207646c44501c00d00074042c0000e4101310204511040c0c0d501030441c4c50030321002e58800c45403010000b00c0b1030350252400d844031100094200100000e104084c11150003040c0038040288003180c142400380d02078900d451603c2c0e210000d840441d91605d82914240358024240103414030346038000b40b0760700381c14011540120f510b00c0000c00e907481c24604501c102d03460440100b0302561140180806504400151001e120090000d1014491216000750010f41c401100c4003c90a02180112000e10b9100480c0c0c041d8000e000058086940849001e80c45001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 742955755 1250 742954505 742954529
    0x10605181512070c33021207030e0102070209010f1d011226030a20040f21080313051b060304110f04020a0e03010531030e0402030403050c0d18 63
    0x41240a079940700c1c0c00c0800609003418000300f0381d81d442c510b079a45e0032883d0745d804002100e6424205002c0407480742100c0801460109000149079a20a030040f00200e54070000140c20318455501151401381c01780c1107034042c40829607043c8000034903005003548841000b15081202d51500044018462444801400b84502c0080c0b0780700d0070380c3c4040681c1c101908084815642c1c500340a12100900b0528804c5c003910440740d41241c074400c464415101500e121040c0d20640b41e117090407030480640d001680c43d011040350241803011403401409544101020002e03034a0420071480c0c010b01b4030a260a140d00c8404001c03601d01c0990b1190002d03030350302039488191841c000840c0d100080185038500d00460340140001140c4840c01d43c4100c0403015240700340e009102c95105c401803001150050a2860344240e1400c0300d01c05001c4003070070014401e40c041d0600c2252200c0303da000ca8103aa000f21000e4010400004842205d02800c002e0b81d00a040c031071810b060300441c00c0c041220300c2d1481d0700c50f00c15003100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 742957005 1250 742955755 742955761
    0xd0617010b04151a28030b0a06090608091504081804020a2007081002070c080a083f041208010f060509040b040e061b070b0705070f0b010605181512 65
    0x98242c0480e082c14945c207042c00c808860580d480c045c00c07203d0170580c40020b803d24500c0c0d003090801442d20400e0302e40396210881150705041c4211070306200204002c18a10440c003915100707040500344540120301908000356555000400780c4102d0448890b03a82c0541c0c81000301484090f40082d04a041f641c11000b034220705110501f149107032200175040180c21b8000d0341e099030341203801d560003003158620810f08451090f43e160b54080e12910000030240140c00c0800403080a80054408800c0c594100c1414041060b0000a0080b370710701113074610bc501c1c800040030700041c0104106440c620500c185030426a0758140040701d00100c0441c8a60001c0c000e001c1100c0115644035001189048000b52080022422072051103940d81029509041850b107034510541500302c00c102141c5003a600000d94500644861000302c90692014005641002c1e0078017040001070081c03130116000b014550342d003a0b00c1c5d04103141e001c418250101411071140c40350f41041010b209011003070712140701c2c6010300c21070556 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 742958255 1250 742957005 742957049
    0x5060405121f0b120c10050307020a0507080a0614160302030c0405060d06092711300c01050a090515070512040603290f060d0617010b0415 61
    0x240c01058203540d8015140c1c2d07a60307030b80309503a40551204081144c0e0790841000225529803180c2d0b8000d62103800038624890080709134040c0c0010740c1c10030178910465203000341d20344405062070b8182d0800c60040c0c01c03d00001c03060003243c2c0502c103000981e02501c2c1e1b005062101c01c503119482520504001d054010001030805e01c0544250f60007070030087c0105690358464a5121300404803030041101d42803038401070941c00800003a040ca1541d1180003800030000d840d0b00e8500e401c1d0007240206a10844442c020280c46c840e0501c0c1200343c05041c100c110300c0903007450a250070108503200080c100041842002c60300359005900310100d481c151690541c03030810303105009480c49403440c040d10780d100d10b0182e020f1000c0d100c0010030485160369000c1101668400c0098080c0d04039010700505030152010101203031030f241c81c2c8031031070a00080c8100e1400c180c0e00580010b45035654007500811145400c0c1c485006000c1c015880d0114040b5400c103c8000d04603d140c8520036140100c80020413180c0c42c0815403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 742959505 1250 742958255 742958263
    0x27111209010b030703080d050108060c121b07060902100e18100515040821030f06370e0c1b010b04060f031e0302071512180b09070506040512 62
    0x4120082d042c1c404c02a00c900f0044180c0e0321640d10150350a04e0b1000009103c0c401249240c06280314440d0307a407600c100c40200c40440c040251162001401c082405084210704200030000070782300d00d401050404160040041011803040d50f04180b1942040d0309445035503500241c08c04164a01c0300c181507840754003100c00c200101e900240e03004403041c4840300101055501038011241403a0490b0104200308622900c142080c0d0325144e603030002030000c19071245a40d08280d510410250400c481e0b52034400910351946c3c1c10354240000100700d281c1d5109045c2c130500c1c00700301403c0320810001040c103110400f104140720700b45458035403210148000860131800c0d0483d03008504005d10900c0003c0e11241e841c00d1000e050303c0704031103221394001078143e502d0041030424001c0d03030543c000c0c1042d145010f50b64031031603c46044170030030000c0d0306d000c402c44584184a041c0d000801c03001c0031240d04c0420319055054032409414840c403580090340800281e500d1400701c1341910029181c00c04104094002c1900c0c5c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 742960755 1250 742959505 742959521
    0x11713150e1e0f01380a080102040e0a09050c060c0316060204060f030b0907082e05010305090f0c01051b0a050c0f1806060a0504030510051005060703080402040b0f06042711120901 79
    0x1000a0f46c10000036440d0381500604280c0380c0505200aa5494034074030442115000e800040403900300001074500d6150134400350103010b0621098038600f4044107040140000c1a000c00c40d00c1c40d901080034007040303074448620002c03d0340d24101044049c44000014024880040400c1c040003994000190302c0c00c2012201c411000c000c400c150301c40c04420094100b903034014054540024038190010f0440c0c5070000f42c070305d05845020040c00d20f000540c0011252a44208102c008040c03c440522040600800c820b2032864062005041a050200100300e00d20b41d0030103043c0d1081640050315071201080c028651340040d412508140c0e00c007440041501e81d40100c1e40058598000c54881e0b024a486030b8014520a031003046415441030785500803c070090041b038802500043d01400020018101680140290303040180b403404801d40f100b0011f061075229802c120b605c82100c500d18080052100400140c4841004040c0902403041c03451034124096228580c0d9890b500030082907181c9401c0d404400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 742962005 1250 742960755 742960759
    0x90c0705030c01020316050324030106081b030709020415080403021c03090b0106050f0d05100b03041a09060c0712030623011713150e1e0f0138 63
    0x789901841c0b01450013034004480000f2810310380c03a110030309030740704004a07403040311200c050171681d16400500708146070351824126050366231000c011a00c3c07c0d0401410380450350440585a402007007074181030409603560300200e1203a0040c0800c0c0400d80001b08001101c8070146000c400326a100c0c01d00b24a052013055040ea28802c2004200e020305d90b05401c40300302107003d01c030a1159039076213440490301c83c4101417100101540500031001d50ad4210b401098008200da030300501d47c9a110386080240764000c0e201210304040c848010b1031321826140056074484080c0d40030701014034040c0c0c104403035071203119002000391950840808a25000350300c42e0000c6e000b2107140340c00c0016080344c481503841d500380b0102e0114410388840c01d040d03800e000b0302502c034401c802405020030301c02c1ea507a040040040082201210f45030500c1003d100410840c416000ad44590340400c030b01d21420b1b009040502c403110b000d100b83d04102600c100b81c140c115048035110181d000203511140b070154031241001a621a8a13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 742963255 1250 742962005 742962007
    0x1205010b09010b0316020f032d030106050a0206010803040f090b04020705060901391803060e0a0213020a0c020906031e0c12071202240307030603151a090c070503 71
    0x4191001e0880c051807160440d049582c0344003170071a05c26660782003036511038182940108454003e01500358098140c4480000355003035000b40b1420500c800e40c000340c10000c0050000f10f0540341c02c41c3d0400906004062072805545420305150b211801550140200395056441d02600001600c441e81101c04054102090f21010b081c584021406444c0c0d51107140b02d0b6020510000e40480d80c51000081e05000481d8940d80d80c40318148191000c00c0c0a00140451021369000000810501d00a443c0f5141220010302000041c0b807040000e90400416101d0101d84181f009400e1241c011516961131070b0100e90311030b095a100c00001b8036040413071580190300700c8503040b40784454000241d4210101000c58403800d4642a1450707070f95855101d40703c1c0d4151015800915005400c0054015035108030a4214907030022906003200c0e00c070790050700c00c1c40000303903114400c1040c0000503072801e5080c18040c000307008164541240d1103076041c0502d141482484e1040205850207144c404440710154000d003a0307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 742964505 1250 742963255 742963259
    0x3010905070306050c16020906010507080408070807090204060f030b0f0a080102040504200d111303030203030a050705040609051908070e01151b0303020304020d080f0403050c06090a1205010b0901 86
    0x55214107041c8001c4a80c103050a0215085035403c00075101a42050440004180525000c002c01004003a0204d4107014040052401050302c1500034005801c200c4018005c40c0d1816110514100340c03035018110f81031042c4414011142c0c0500314105440311854003045104407500014403000402d00c44030303445040c103000002c81c0304064002e04110790703080340c0c100510480f15601c4045184400e180020014040100d0f540002e00c683c00210040c2d9008200d80c10460f040040c1d10060100c2c0d082640541e1001c0104244c01c030981c094160301032250f191041c1420b24003840030b810341c0b090340155841500e04251a4030b180548890500042030028100d600381070303442000f440001d0302806094075000040c3c1801180a01a520544500700241004900781031180c03011002500701500490b4440180c0c0070b11004542c1c000094607a01c5003052105688500c0d500d030180c608415114618001d0300144004300b04c0e582c68440783e10459584804003038071103c007480c146004018200e00258003401e60400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 742965755 1250 742964505 742964513
    0xf0c020117090d0e0a05030c09070905040c052a120a020a05070f03031d0108040609050307141e010e0a060e100204060c03080f063a050f06130b010b0f09030109 70
    0x3d40f00800c90b15129101c0d0750044100f071009145250141d01d4269103c0400c40c4030504245030125401005403500c0b815054031000003405641c0700d200d0400001c0d002189001c03800b0000745284030380789030030169020703002481e409180c0c44049604040d1944c20300800c210440500900000c04480d9002e07080e21001612400c08440e20802400154000b841c0150206240c100c0f9828803904114141c50340042503039603584060140c50000012600c50105003e00c20001d0031086100d9003451500b0050400920031001004905003507580c2c903d081e0381410a082540140131400c040c0d9560023910101e46c07001013100300741c5080c0209101d510710a100040001d5a66030000484c5a050712070740e110105511604103000c80301c981501c906511001c40030701d08403c900c03000982407018540024584204819180200218442071400d1b51039402075800c9003401c1c0001e10080e40c1c041c1c850700c1d50100901542c2c40310000510b05000d08581d8a40000c1c0e114044402c3d907040d0303010f45030000d009002c045101d1030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 742967005 1250 742965755 742965763
    0x62f031c1406010503150415030b09010b120a0209150d0c06020d3f20030405010b010c080a18051f0314060102101104030b10031a0402010f0c02011709 66
    0x3031500c01d40c12100200d59550311520880e805403e82c48101c1d950340e402102080000c00d0f42c0c000c6900002c82d026400000038440c1172200b4891801c1d2800025800b0980e01888041e110701d070769000c6d03284c000e5a0450011b9540c4401c4941111003401c40096403401440840d403001d40c41840540041c0712100001000c50340004c6884206001c1e0b51049030400c0d0382807003600d90b84804086d4032610300340300207007951a800349034401c00041081d5501082400240400940b0514807682d040c590180000412041c0701003400b9155440c1428641401d0416240d00c600840740a078811410822260b8104422000c280d00001005800024410120b46222580380e100100d0683c01880100c0e082100c441268150120064030811040e0094003102003540c0620004000d16407007604418001d02010000c01e00750444603105159803010720400c0c4d81542012101070314101c15040c0391000340c104020050341c0c0461600031100f61810500d0801a0901c01a241c00e0540f00c00c10401c06074140c2000240f0000003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 742968255 1250 742967005 742967021
    0x70830090f0705150c1e07081209010504050105220b0901080a090c09230403031d0105070903080708090d060f0b03070e01290403080a09062f031c 64
    0x12904114103080610b92201400d00c105940003a00742c00300d404e188440402419140e20003c04e60f40165141c00d550f41c081c50141007176140303503400300343c0901c03800c0170801990030f0314001024400c1c1040d1080000a00920450113094100708d07002c2100640952240754a14042019101000320907444543e260303103a41045603024000790030300c408600c50100d03601c129103100360400030900c0c00c2030415000e500078064502e4480c042d8141616480100c20105c45a10300841c0704c0d983c00314001020b001c042840076206002900300c0e034544010f122126400040050450764800e0b41941c0302c0c1c08a081001072401141c3d00d00e50007072654050070301041081d0348554a039807802d8804100104010f030038559140c803140100c079246405400103208a5009001108210312078031012210309040d02c0c60031946800070351080b151f0020114240380c0b503503003020884000c0c25052414500812220f2881428240c00241462017051050341d1601126001e008444640d1404000800a1030f214215500104860 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 742969505 1250 742968255 742968271
    0x100609053f0307060c0314060102070603020f04080f0303010e0907060207120201140a090519030b040f0f0206040b0c07050909030703030e1905100612031e021507110c1005070830 78
    0x404504100da00c05107d1401800e042c0d00030510795050010640c0203501c03128041e00c000303609210010703d0b00000c11510100105080145072a03524000c440580f10802904c50445604064030a00589900003898021180740041d00c8209510310b00041e14440203020030b15401060000b2181a6150440240c20498400b6180c0f0b103541c0043c0f0025038030030740c494080100880030030404600407404d01090105a80e0040c079200603807041550004050394802c1d40a080816030101e212260302406001c254000c00d02070361075000c0303864603103603603512485092401000d160b6034054a6008041c00c000490204105c0e4680013080c00907424201e40d16070480f503090385c000307040120205607040c03606800d04016925803a41008030000c1d41034036054038075044030f00e4210b121700000307045485401e901c007a004240a440d00d801c54140760b0310752410800400209400741c00382031903200c04280d00404941d1159080b4450680f180000c500500340c18000300c00d108400050034503204000d040d22001a401a902 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 742970755 1250 742969505 742969511
    0x3010902100e0406170c0a080601051003050603070e0711060109090b010501080a0b0307060e04061a040b0a020f0102070609031d09010b0d0b0402070623101517100609053f0307060c03 80
    0x2841c0701c4230741c0d60802401115008590042c4400c011402a00515003000004040d283c910391216110081c0e14411a0180005010900f0030207101c10144003c0b0301404d0301c4981031050403444c1c1c8652144050602c2030a040201c0400015a5619140d0000c0300010f00101903d415641d01c050040049085e501154407680c030789100003d00d02e042170030040c0c1030382100d03071101d08251030400c010081e90422030b01d90080d8010700200c08000d000c00c0c030080131002e04c1410001580c01d154180140a20300d031140b805015104d01c00095500d41d113210100341101c030b020740c10703a50340c0e282c5405200c050920200c8940d002030001c00e07070404101c425005000c0829847c00e650100c0c41d04c5075590002200d05482c10241d1342803e00c82407050340b540c80a0010310700010704110758a41e4040d0b031b5141102c4421141d032070348400d5124080c850035a0000d010001890200e540c5100b5444060710000c0000d104180e20004000c4400c042950700d282c000c104441d194003105403600c40c0310300e04004003d00847c0c0d54180000749 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 742972005 1250 742970755 742970759
    0x10212010e07090801020903190201112a090402090a0c0c02060301030609031e090b030615130501080c0705030d0b01020c0d120f11060402241b0c03010902100e0406170c0a 75
    0x13070705200b035804030351b4014014602d0130030010b820140101344140c1a410080f41e41007260301018100441821030564801034401c1207880d1800380000d0020161503403017100754030288005a513890516a4200300030b414005410b40000605440541207200c00075049840030000200348030340e84d0300c92550240a902d40c410a080c1503448010214940e454660100e60050420b00c864030b600340c003031341d4440d0000d0544a001d0000e8100810a43c124081c080c1081201c00400c0c04156845007445800174045540307903041074803e5961580300e000325951850071a80d07a1001c400168802c0040c0780041c3e80c00340150000c0100e03410300c03ea0b0f01e80f400101c54007242800c034009012920440c690340c1c1804034040504450340325942000b80a9800281141c0c801a008980d034001c051000020030303142d1002c446985104000381040f40c141000760450521076407408000b4001f5844070019020b1420140ca06110b2800011001800511035508071440c9000c102c0c41c00c50140a0010340300b80258021560015959 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 742973255 1250 742972005 742972019
    0x3080d060501021908030a2a030b0913060b0604150c051603030504030b060a05030d0203070b010509060616080f03010303030e0606041116020411030720010212060f0102010212010e0709 81
    0x4d030207044015011146140c541d01040600e4013640d000505400301040c4400101d0405124903001001e80b44c000ca03400000b01c00c0d05400d03114800400806980580c0a8a04080e4110800e849808054545a11402e03101d00315500c0e84203c502401807441c40d41480c01510100511891105030111102c1c8a903914140c6190384940074030046075410740e0780c3c6280070304503903660059040140400e50000308a0b4400300722075405020740440411144d00442d110300c0300e0300340845e42140690110307000c3c241410034004552151004c1b10f50100881c840014200307004d1404030080d01c541042c192203104040004010542d040e040042c0402d8110121001c0d92208000c100c110b42044003543d2400d40c00300300340e84000440640b00701560b40010000a00340c5810101c020311075004803503290008031440d04003903a0082d5103074031702002d2150400850520000311204421208007070712451183c9032400c00854542e100350101e5000385030021800380c080d45d50300f0034002030483c199824400b04000c07210101d509 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 742974505 1250 742973255 742973263
    0x41107030c1511031501170106050c1005100302060a1b24050f01030b0601020705060403080307081f060c020a08100b130b090f07170c0c0d08010b120a020c0703080d06050102 76
    0x205483c1016130b10f940c41d01c00251241e040f58000c0e5134148807000c0100402290700c80000ca00070801c07601d17100e1b96540054a120b003850440700d030611043e0b00d81424007019282001d43e0b030302569415240d0b540c0e0b41032841c6055032440711280c080d80040d0b81243c0d003032003040a10060400c20045248018040da103c910f00c190a60394203d0b40e10742900034023001040440c0c03585000d1604200180150b80700c550712040032941d1980540c0054078407840000901c01826448a12540d000292014003903043c400c400040517604000c0c45224104040305078043e043d545d4a1142000420000080301c116002c500001009031880011070781c03164001c80d50300f101500240c0a40d0000d100002c1a0740a00e545d083e54040d02c05202500030b00821a0304500e1072800d940c0d8100507402074505030511a100c4c100f02100900d81344451003040e042000d408010018480024150350005a8120780c1011036907c0b4108400240031307030600340e20103200700c0e01d000040c0903280c001402400384514086c49440e499000590351 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 742975755 1250 742974505 742974521
    0x15280c031b05031302060f0706060f24030213050a08150f1006140c010501030f110a18020a0e100504090506090f06090415151d0105010e040b041107030c15 68
    0x1040c1d0800000d00c91503138165005990901c01400c640c20a000e110341d10f0055007010004640075507444034240f26040e440340d81752004240c01000342104049045d661158407503890703061001c0c5600441e0350b1050701c403604e440c08060840644424041c90b0f844ca0a40c1e078611503908885044041c080114038032503204400b541c800c861484070350010a180c00c0086460300c0a03071290300104041030002c0002e814081c05014020b501814a0302c40c201410700703041c1c556000c1e00314400d208402c018420009410b9419150400015448005865408044082e13a8020300c1186480e031202c008541c007185103400001a0056070b00e409000c201c0e03507039140c040c4801d600069582d0601c040403180040e040e0b2400c3c80841d0360241c800c9210300c0e115680c80780030505442050318241a00c540d15042400758403440680000b0b030b01e90b012103914140d454100080c00350b03a010301c8003034011134550b6102c0030a40c07250303003000707045a5002460039604c07980e50400800c04880b1440494100c545144451800e0009028000b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 742977005 1250 742975755 742975757
    0x60a050414040b0a12030203070206071a13030807031a13060906120c1e09020a082d06010f0903140f1203100605070f150b03060601030e15280c031b 65
    0x5005080001c00c0c0703110005c02c1c0084045101c200300344801a01c0f4100a41955482008420508a601e0001203200e6034010b000ea038640c0d043c0700c0310307502080c1d021805580151480c2400900c1140c0005140b180725094a13500307800683d61b151420348400140d001c00201c6010740700420000b03896004e4040540380b00d0202404044000c4d10920501504003043c45409485082c0c92070b0490b0b41300d440400341e800141c80c02c800b00e40301c40200a80d01e41c00c094803444400c4190300450180c40c6603034144580040c05404641000308110760340c40c605000310b905001554224844003801d41c034042d156503680100d0040040c81c9d010390030152080c240f45100b582d014404600001080c142030010031902a00010f20684030a03055450010220340648118100c064030448042201041c01090601e4940042c0c1828100342c84c00c0805420f04901150385524840d03480c24104445e264500b1100b003001f8101c1c401140440152140010000b003503014041c410180c0c1c43c103008503201c141d40c050500e454110a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 742978255 1250 742977005 742977019
    0x1e03020409030e100c02060f13051c03030b1c12021006030c081908180301090b010b0d060506030108030a1b05120301150806151b0304060c1707030e0d11060a050414040b 74
    0x1012003000c04040e20708000a00142c41002b03540e000010b02c500030300f004044d800b190740780001040c550b1500540da8201800e481c507070680702040802410440c0c190380080d10390303170040340c0e042c5206100f444602c616221440d4140001602c905040d019004d1034818403400e8841c508411521401c0d1040c18100a81c202074010708100c1c0240c00038861401d5075182c540e041d5656400b0400040d001945d15028004001b030150b20788503800c0b04d0303c04a401680000d84925401d100400005200008607010b1020600d062803812110622034600700f90f01042c028140d0203049421540740d60744001441c12200f110b1030b202c400852010003620303500c00c01c0c2d520640001d0080203aa00003000038000f040300e80034003c6511603030850019214115005904614001580300119505000148410b14881400007818520f03280c00d40d41c0251042c0290007415000da0414804002803104040030710741c00c0721001c6c00b4999605a407075030040541e409409000400003070060903802c0c5081a22541c00d650034081c10702 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 742979505 1250 742978255 742978267
    0xf06061211071e0f320304060e040209030304120209151c050f070801021314030a03030b22090308090c0d0204050907090e0d26011e03020409030e100c0206 68
    0x5001e41c10b06001000701d03403011443c44100014122050740c030b0100d020f21600708500711114400480c40440141201015042c0105400310800100c21a01101c055043c01180440c0007008100030340a000d44450740750001103000075840001180c4c20001601c01c0b15804004e035184150a102c1081450415400c00d4540b142d4454084595640380a60381c00b0340c003100c803003420068106240c140290041119a500030503103000d089030300103180e0080c2003403080610035503a4401c0483d56403040c1c00c001804043d03e5040812443c0c80f04940200410102c07240d0b02c541c0e110549003203028042c02e400c2240028134000015414130b502040c21800c0c9903004003420072180c8141c08000241401406e4050315009030032001031111200e20816607265150f1010700104000706001802c032107900982080c0102c09a079243c034400080c2c0201605440340c0000e0400a6403c2d9007008006da105600000c0d001440d01e5813100926402a0031190200b40032034100100504040382200c0c003028038000250000300c14445 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 742980755 1250 742979505 742979513
    0xc06090e13020117090c011b0506161e0203040311040509060720070e0a060f21030c08040b0315040c1b020d050d12060602010b0d020f010905040f0606121107 69
    0x1501401e035005144c010001040141180401003080c0d036081a5136012070006401e95800680e844515101003000c0361500b00f45450b01d940306c080080c206895058080043e011581c0100d10402640c0e1011200c2d80d000c07807181c0740180d0359600c60f010685440c651007901000e41c0c5860300900d48130740c0c6083e026110750345075020165074030b5135400f41d818030001d2200c5038100500d000704010b9005140500d220b41e06410203804001c12140e69421040301c7c90314a007414002c1c1c10401514000c0140304280040400f0f0450408450003034510b20010042c03080010009426181840510700890501420000c2401c0310f100300701c1101c0e41182000041403081c0b07802c1c040c0404c0b8603076086880c0d00141c042403164520365203182c1040890941c25001c101d409011040012035071250f10094115030008100c80c0b00244002075104c1841e600082c41805d0030032340d10103d64816075081009010180084c480b0031440c41100b070140c0424040c22001a100d954110300006d280e01480360740d01d40d038041151400761a611 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 742982005 1250 742980755 742980781
    0x20a12110f0d05070903050d0c061401050a0509130b010f061d010e060927040302060115090e040615060e031002030118050c1b030a080f04021e031f090c06090e 70
    0x8400d1061000e21070700000070503000d11240368448c2c0150b80351000903003289400380c1140c07140904110101d8280005000d55284c4c50420400d482081303c420b0071507914224950049996200010210004100005030b202141020402070307070320700d896445000c48124401c9804035891071400c0d0009900c061180c000d400c1c82e00051828401c0945940c07544290122000c0d89560505c80c580d41c0000d181040105041d41448498054500702d00c6072035980009800003445010640100321035901c008000c1000c0240a6115a603003c41c113400e00d10078240e4a180c003030319240500c1c1c00b9900170f010740d14004d550b065991007207a042e941000d503100890603004440000500008000c80c180c1901004140003001d2800300011300d003040c42d8025a50317a80c05860045c968031010306580900320000d0f051000503a01c0301500d60040c08541280815583c3e0400001d1400030214111175040340c179a1181c0e0340302030161b040005401d01540300300154a0703849408a0340c4003002d118a5060750042030200f0103920800e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 742983255 1250 742982005 742982011
    0x2070507090b011106100e0603190308150315010602061b0403060902190e0108070e07020a02010e040b061c060f0815070e0604120c0819060e0a06020a12110f0d05 71
    0x314007000900000302c0c80c070f440d0550954510907007840014003044028299030415a0148c000d070041c01c0e004c1030300300c07544004820019004041c0604807000031600b0040c20050303002e01100030304071500740b0141142d6030001e410070701640b4010700407000040e85906001141c00d0310070030720b41c2000c2e1625107103868a1000b000d200034101d910050704071407044845c0d24171808802401c586403034401e9551400032401d00d8400168820401984d0040c1006095a0007080b0280d4941e02801c051000090800020f4010511140215030002e4007041c00d04000042415139034041d120b8040070800c1c6511030240031240301c04da110703841c8903038805078510044081d4400303c45d40004460500884200c000300014406410035080110301c210780500e09020f22010900c80b000900c3d01402418082006080c454981d10180c2c00c050120780d107545444190003000c001c0b1218494000004640310b0504040c020681d41c80c102d41c01ca2aa420610702c091221944802c036882102d00c1005146400100408180502002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 742984505 1250 742983255 742983257
    0x8120411040e06100b07062a1e0503010506130509010915081b010507110a03120e10080a0b0a180504030f020303012405070c06020303070f03090203100e0a0f03021f02070507090b01 79
    0x506c08904c40300091026000c9882440c1441022301070300c100005225450401490201c181125103042c803050b00034085a0542d1030581c0c0342552505400030021940a240c3d02450f00400320b0000001c00c45d000d54030040b903101030b80341070040c0d141d55400c18650b581d04000c040d80c2c0000c000080711490398013076030040442c0c9101e021900c07111081c0e180000c5090209032320a80c2d4810748150b00c0000241d11003030030549d080d400c881e5003400041c0380800030803441c0020004540c540d0b40d400c1e05009680d070812848014041d0b00240240c0d201800b4065014090a80301103002c0341c4120800c4100c98008801d49040c1c52006070409902040d01c00482d8844604182c072805115040050390046444007081c880502a240c000f96a030b414078050040035058101c0e00d0354205450044144010307613000c01c010f4002240204040f8481103c2c000007400e205000c0c800030201040b010104081607004100414500c031508041034684075035003c800103a204150004100e13400c042403d1001c1d4403a9403002201c0181 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 742985611 1106 742984505 742984511
    0x1104091b0206012105060406020408060c180402070f080a020604030e010c051e030f04140a060f0c0204050c2b060f0e01060302030408120411040e06100b0706 69
    0x180601e0900308800d012084d000b1100300300a481d02604802902c1c51401e02e0b20b088070096105100300010307406400d00086007241040d00359a0710f500c031600758000450510040100a40c0a000101e514030408031159021850b00d60103080304c80c0c81d82c1c00524103030900342409080940c401c055a070400031000c0c0c0840000e000420003034074440403030340024040c03190a200035045005010b82100c500c0d00104000035823220072a015030354441c09640006100ba11440125001840942d03404007142c200d508072801070526600030b0782d000c1308550740c0c2c9003071440d80f0b010301250aa0200034090320304500d08124907988021302c14207000781505071030380045502d080008005100140301d010185075000c0006400d018100c01200c845082a1348802c0c0a45806d1a09014407150200c40a024a03d41841c030504014002141402500c02c44c107842000c9146c0040381419900505d402c60358141c0f = true := by decide +kernel

theorem cover : BRFrame.Cov 742805755 742985611 := by
  have h0 := BRFrame.cov_init 742805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 742805755 ≤ n) (h2 : n < 742985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
