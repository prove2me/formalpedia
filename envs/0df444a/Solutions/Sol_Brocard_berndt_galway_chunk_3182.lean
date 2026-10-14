-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3182
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:54:08.092313+00:00
-- url     : https://prove2.me/submissions/9dbfc6d5-0eea-4621-8ea1-e7faca6fc156

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 572122302 ≤ n < 572302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 572123552 1250 572122302 572122307
    0x913200a0609080c0d0201021002040e18010e06070311041d090706110a021507080f120a050f0705070303111c11070c0b0a0e060706050103110102060603100e0304240807 74
    0x9000f180e0001c4058588103500c40c1c100203c1c074000d0041a0305500801e4070855007d44c8910007030000d800600c0e1a2511424504a034480948a0703200103095603151048014440b000050b01c0e0b54010002d18001c41d0b03040d400014041135004681c00560380405035803104003410800444284a0001d040440d68000c1c0d640304101c2f035000d07200700f0000c00c80d00031481c00c00150800b142d070740c507461403441c40084c80c2c9a0140d41d16001e030391080d890100811004180c45c4200514001c1094101581c02802d1000d4203155003c014205000b42190061002c009190400c240c040d80142660148200c1407548590b80d00b1310123101c1c0824249081c002d245813a00494019800e103050b00c10403a00038904048460520104c450150300030707899101405038618080c400c0d555000d00614906118041c041001e500d5803030440b042c400300c00a2030781590421801c01c00580c40010300510744440003d400b09880c1c2001d640d81e400c6102c2c5410888504001d06980e004800c94610040080c0b5110390383c02c0d8060740e508908 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 572124802 1250 572123552 572123567
    0x501020d060305190b0105010e0a0e0f06031c0503012c0108100609050c0f0a1107032105361804030915050a1d030a1b06030e0307020913200a06 63
    0x2032210601c5c500500c480d500c1119010413914015045151035502d038032149503070b460201c40c45030b07905a40104110050038244410031505200d003200800710700e08021301400c280414003a081017462040c500208081d8500181c4081109004918081c0d5840f407410301d0b2200d94600d601c031419030901d6000a02612940318032841a244100030034103280059140720302e030b81e2000a80e403007003103901112010040014015040194842ea501d02101c2259640020000c00e104250f04203208040c007006240003114000c5c441412003c030201e110100070354011400405a8003205504451031041401505106c0c50955001e68042c1d1181e610a603074480400c000305500d03612550000f4801e01c01c2195450003051214802400d00604509804109000c00d2a021b1600c506075946c0e100d401c24400704180d814940c1001d802940f405002c620303220340b40d45d83d07244140300000707004100080014040f4a41c2ca2040f44505600102d1401c4507040b40d07407540005d04407038855078414540b14030001000c0d40034078030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 572126052 1250 572124802 572124853
    0x7020931020315070201140c03071e0e040b0111010c0c020f0402030402011704030219150c0216030803040f0c0e0a180308070e03100c030e010e030c1510030501020d060305 75
    0x18034505403c40214074809801800c410107564071503940d040011280000746201d0b55089502039100d1030410030090540c00f410345580340c01a61200c824002aa002c5090b8210712000d88000c80e07407804600048804294901000e545075203010581d2400c5c0c0d0340031311950940b40c000c5420f0418402d07640100b004a11007654000c0c041000da43c070304c2807201d13503901407941d00501134010340c0d0380703d503030083d80d41080300e03428204036505140b00111401400c0d1610514460710006e20080c801103006291400450f5030f240006400360354080001400c11501b40541480d003a84054061041b0b681c07120540243c840c141c0701c00300803604080700b49403802ca140c9986000181c0690707516400742c0b6601c8040d9000300120191a4160141c81c1c14031103008098001e400043c0d0869400180e1040b8114010782140d8510b0100c00007a001000340403500c21001680492110b548402c2d20210345502c00000b40f4031a682e40010601d500211b06211180d0305980030700210ba01420945055500a05000540c40003050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 572127302 1250 572126052 572126059
    0x6030e0607021f20220e1b0405030d030c1d0105120408070f080405041503080f0f04170a11010e15030c0c030309010e0c06030709090f020702093102 65
    0x20300c880008860141c1e60310342c1003c0c843e0000340580740081a00d50060443c50585000c240003d07445c0f2500600004550420000860b62404030f00b020705030074a402001d0301d580c44802902103000d001102c244110345c0284401001c58120740030941c4c003d0050180c11140c0d00201c5c0e040c40404400c3e00c0f1440d1762111b003000c16500e0701d181031042543c1c1050700d100500143c813010000d001c041d00117000261403162140c0119625a00c8600e000c04000585844c48030059060841100030400145044141c1d01d60f010045181c2d82c0340c070310058091889000d0b03a07200c1061400d107192040344003074004c03440160407801801c0c100d154140b8030b4010755000d00b0b0114050f8210802c10442201d031801e203409143c00804050f042361404bc1c00080366443d503007040d00c040c1d2050f55940702001d0301440801c48007c485505480c3d503404c0d45880726028107a000148120111192140303441e000e01d0540f541140c1005900501109013400e091120355145004d101181150100e480307620714220301c40408100c2541e5005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 572128552 1250 572127302 572127313
    0xf170a0219030f1110140910030e030d02222103090504060b0306040614090f42030f07050d020f04020f0d0f02071e0311010e0706030e060702 62
    0x5a00788501c10011111200030300c240040044002552180d00881d0180a003800e003181c803114000b00a058422201140144640700d180044d8145200095501d0300c141207612006078180b024080e00540128040c2e0003c6000000c0d0b03203a034000896026200c1e12108102040f8444284211240310b01d0b0f05000300f8a00034850021000240030448511444900c68501003a00640d03d502040c15581d09801c600105a00401004a01e05080c0f150320003c0180d40c0d072480c000d140e0200442c0a0080241c40744002c4007800300024400e0032030030001000e400510444020b9210800c0130554008040d04819002113000b034409a154036001620034a08000100601103a6180008001d000c01d09440300303d030000e02491050712299120f10103011041c200a625645c2c2c1d1005132800c100f09d402034142110714a2040c0038803800b150340c40d5a500a202182202900c120101f41801d5440001c0071000802544c01c04040152246003c02d58100b2264961802d011550110b104191110310440c1c1000050b40f00c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 572129802 1250 572128552 572128573
    0xd030f0b0d1b181a09040206040b030a11070c0603051501120c020a050a121403043306030c050f010903080f030c04031e1e020102070902090a0905040506010f17 70
    0x50940411862003903515400800d07568180c2d03450007000020441091641e1046640003030724450071280c210003c1250340151516040c7e00045040c09140255050444040001691000183e000c9c403000d50020303030501e0f200c82207440c000300f625513940a80702c0000e0805d408541e07180916088001c0c41070f016160141d103c040c02d0f46c903000814030070f5201c800f148501030115002c00c03010b006000e1901e0081c1c421030910510814007510304c40c00d0f02814003c1c10004c000b0400401c00c07000041d06405c244080700c00c054214031050204a4046241c10080c1a150440c004101b24402460000b103402c203403109481200d0000054075a1200e170b12000c2c00c0d9032020890700b00300c9004200110343c4401204541d50405860b81c40741110210201da0b00300303044043c03080240034401404040710b81c5032040c041700c06d492032030366000035142d009910600517070f140c021400e101e0135602d00e0844c50140c0741c04071040150b4030341401c006a4880d020721076905c122500101c0403d00b40c405030500c080106554005107200d966 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 572131052 1250 572129802 572129813
    0x120c0103050a09170408010c0206220201050d021603081e1b040807060203120a180b06060f0c01091506080703110409060203090f1b0d2904050d030f0b0d 67
    0xd280600b0390b50341d03d4000001925081c0960016018640c8154503a410104040d00711440303038001009650002e010480c500c80e088901039040c0c03440903510304001e0260301c010381f164080d618000000c82d0006c200400100c102044120202c0d000b507460b40d0035074403513052651400e02c07d071114000d04c554001c00682000104c14015864110481d6164a4699142611800c00185802110042c0c01c00141c022030010b0018035103410080101003080103400c45944044460f00a406c000d00c0600b814000034107960b10182a80c6074182803600c020b54610a84034824002c010003141150703840500da840b1013034041d041c03252100303440b4200020325280d401e644498031980d0350740b0f0405511507112a244800985240050350080c00e00c10020810103a4588094ac20401c08803400101c00c001003040802581e110540d128545800810b8000705d0000c520250b402c00034200d4145495032a04414003040002c0014070103181401580c08003c80c1c0320b0681484252030703581d0399140d07101c0d4886101001045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 572132302 1250 572131052 572131061
    0xc0409091a09030c0c030c13361a0f010b07080904060e0610030509030a05090607020405010602030a2705010809010f06030305091005090a0915031509020f120c0103 72
    0x1402007107481140c00c54109100741a850403160070b40550008070310740c4003054040190000c0c50800300e01500a60345803402252950040b89028032035035880f1503d9100d0340070020760380001b4111686907500d0007064030b800c0d40090080120708880e06d540500c038800400303051001640c0240070082d141140fa902c0c3c16a85602a0030a2800703480480080000c0384242d030b80c9100303034001484408440030b440c0c82c0041c2042418440d000d0b5031000e15080600f0480c1120003c42203810700e04282c2081c0c0d803a80c0b10880880d90901030a60000d4009142400104101c1c0c1c002024090700c1c0c800ea0307a0840b040020306000c0304006e501c140d1001c910b10081000f0700443d030040a26590122880c0c00000e0000760540401003540e07030355401500407070700008100019090150748130319540d140b4105035103004070650215407000f80a00c41c0c6c0c06c125941d40e14540c491111440000015074118524400c400c1d40008080c0051141d020100d00c42d0300c94440c05007a41c1454034900990344d030050302400d80b0440d044019000303403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 572133552 1250 572132302 572132321
    0xf020c06040b071b0b0315010e09060a0312020307020d1110021f022809140a0623070b0910141302010c0804051005070b0916032405041203140c0409 65
    0x140e190020580d1285c05014522558816480c0d000340b600032000940101030f260040750180c030000b001c02c00f05880b0440d81342c00b207951008480300d0400f20804c040b421806035000c001c1d800310040d00d82c182400041062130040d8841158001c0c0e0b290b02000040c3c0e030b103004180303c0754104120981035002d04900b55020f02400e490700001c60301200c0e90030040e600b548050300c1111010034212003080c4203441c40301e50410b4a076481520f186c40000d0400d03901500384030300407041d040109501354160b040c0d80001c0c004d44e01082c1e4000c140175103909040c006180ca03007a500045810140c5410020030b1380300040d98141e4015800351482c0240c4541ca50011900310503050010b907141d200030040014262076001400000c00059174030f480e180c0240745407902000da0050300005550740480b540c9007000c0c0c1000988400c030b0b54043c1000000d5551049101845818000d64039a032918040402c018481d00410060584d10b242c0c0e010000b0112502d07258030510400c1d0303031400510f0020311041c08403044c1c2d544249080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 572134802 1250 572133552 572133593
    0x131508160e04020c10060608150d140303040308090c0102060c0a0e0a2c0f0c040b0a02010e060118140f070c02010207080d03020418021215010e0d030f020c06040b07 72
    0x106209040890142d91060101311540d6220300d00e2880629006c2c400c05003d81881c0c0340c04021402c0941030100ca4080d00f101c0d0520580d54500c51008120042d020a00f145903144284c03a203c0c40d02e400d020340755050890f071004c1d0b14003404003054100c1d88041880c03031150b0b0080e0701d0503080c060784203800c41c0d0801d0005c1206810090044010078042009481000341c10184c40c58520806005071100300e0f14907000d0284042a1111018001720034040b0050390142e4003c2c030a017944541581030100c1c050070b01300c0300d000031601a403000031500d29440d840c8510b12003520b050610034032181d11112151460100c4207401e80440310b00204500350310a9042e18182401441240e17074407038a40d09103504005c541d50740103005c260700080801001c0c1001d80d00714100364031508210305040d031f10883d940694400074440c015102c5091108509607002d6410401d000101800412600145140180c8606012084040907209000c4030000034a0003c04030f900381c0362030484490401c046e5a0700c90200c61b04c183c84030500d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 572136052 1250 572134802 572134817
    0x2030d09030e0315070e03030f040506030408160305030f09030a140d0603051015051009030221190b13030e3d08011a090906030c03010e0313150816 65
    0x41d981c10050350b004d0a180c0b6555201e2800c2c140d070090040b6508003241c0d4003a800502c1462003a01200e400c0d1000c0721415151290380740d91705d2512a01e244a1a040c2d419000c5641111906042e0710001852060f80b440c1c0b0f02d0841900c410420587d40c0c05400d02000c0003920801d00705440010354030152043c011411004210305840c0d07640d032030a104060715420743c601c0d03039900c0c1c10f50070154a04042c0000c0c1400d40e1800501401080000c0c6003645d1404081e0081440c004100903900c0c500542c1c02d0119541801d59a00724040e03503000c11260350741c001c203441c0a605100410f103010841aa50030030746502d42c0b601545003d00708180305a0180745030000011101c00c403116007a40036406c04080c489032405024240c84102c080002d41041010382000b1010b00c40314110ac2072030701e0024211090030070102c0300354100303640300000a4a80f0300011a1541c05500345181c081e441030300003018003044001000c044031040c0d1125080010000043c1200d0005450480403d410500b003030300804c1c0c410203920700070b01d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 572137302 1250 572136052 572136077
    0x405150d260a0e0a0b0c07090c0c0c030614010b03070c0b090a0f0f03140f090f0a2105060115210e06040c031b030804060f09090e0604030207090c02030d0903 69
    0x98039800c82c903206004210b0700b841445192074203003503210182c81ea4644060524003c5904240c5d01d81c0c180c0241c0c0b107450b81d110340501e82c0600401914400c1070b4022030b500010b6884c1d103010400741c0001d031490380001c014400041a0030405030190391041842d940ea5203071486040d2910014000701804807002c501030141c1102c0031544410510700340c0d0380990140641c402551a00a203406605107525030f1000c014001c8074a2204000700711900e8800481d2020030103540c03013000540c500015884039403480e44440180b50b030454000502a00140140d0a40e261603a0f617076400f42c05584050b03604030004074201c0e06840381203800c4191040030004010001030141034062203a25104050742c2c29114211503078404c00030001508401260100070304005141140303140c2e2a10414007880c0250024400c1c50256031046500c00e60035480200140601441114080303c41c6980310b020942d0268018040d00724040b40188541c001c810340c5c004958000d51410390880c01e800e004001d415002c60401100e0440301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 572138552 1250 572137302 572137373
    0x3051c030e0a030c02090c07050a080d1b08060112050c032205060906240f09090102090310090c06020d0c020f010309081b06180604120201060b0f03060405150d 70
    0x440310b912079201c034071041e50a40100042154014010051803c0c02c01500001500110b0503111070303079010246580b21015001c2690180010350140c60038000a9521250015481005280512420b032140e52840c041b004201d010394408841d200b052020410104000f0400424925400e800361207655600b00da142e42c443d82412401c1e540003409070300403418004240044c400d0103030030491031460045005101030101e4002d52001104a01c5152aa000102c00c0790082d01242e402c0280102951030142c10040b00030000e1000700415643c42641c5480030840754000a8400541010740d240c00d81070101d80c0c2d081188040f5100950350406441e000008001000000a451a51030b43c00c107010784001882c010514044000b4030071025144000720a80b250070000c03840d10b07002600000400d5020014120590152080750b01482900d900007440090980c0031030007641c000c45081f50180100e0705c81d024400c2e02c5203180004c03903500120782c00d0340c000040c040340c031861010700003c444040620f80d40b0320074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 572139802 1250 572138552 572138563
    0x20118030609110405040f030305090f160e090f1b031002040b0d110406050a050313120c03080a06051008061305100e06040e0a020d150c0e031603051c030e 68
    0x1c07924191640c1c0c400042295024200c0c02140c1c082e141000b85d464113132100510309000000240900d0b5407400841e070404018004000f200d501c05040307801950b8841ca0501300c107601ca00c1621420710780ca8021801d017207000308989000501c42d9001b4030f00e001c00c0c44174001e1122111555198144110514030810f4001800a00700070850580e120f62035880c076409440603528142c019102c005800c20041c800180c2000031303268108040d1411503140c0d950410601115052020040c010030301c5a614240716640c00300e40c1c425118030940c0c1c2c0031400e40b03c1c85403e2064274158010a0703804201920100741480c8036001007644a0401041d100507072080f5102c0c00211034060f1a40c0d00c402d55010300a009800180f050f02d40c002c8402e84081080304840c01603542c8a013400c4000034032035075112040030705010030040502c20401760901c040050f02c032790300c3c009440a1051240e080c068040e914549030100300a40c400c4080321380100c05009418604d070440712101e01023170307004001d141d5104a0000703014800c200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 572141052 1250 572139802 572139809
    0x915030203041109011a0903030c070b1b060c16030e130c020c01020a0b0105040b06040e0c0406171003080306040213090c0329040207031b031701091116020118 70
    0x180103030340c0d04060401c0300311607180c822020301462242d801005030808814070401000045d18000745c48400e1100000d080d8401c449118185200d03090021a0348426a0000c049800c1c007002e00401d07180c411070407030b900d60104455400d50800140001004030010410304c2c4a2107100c0d14000449464201c0040c6408500d0304452410599504e00d8034080760701005001c5800d90240010950701c0341c00e644a528a04050040d00e005945822002040c2d0300c03a0001c0d20082c00103020500ca032441c041519210300d80252184500049691a400940036081c00d403550003148043c46001d41d681c20743c0c46001860b80094190340d00a5401c1212513884880d9065000107800c0f0602d000c564107101075002001c0e58003001c1128400602407041110050240d9030480d0013113400c0c1ca000d615200c8504040c0c400030510050f1940401176404ca41c030030507600a0108030080010a1650ba559032034040a1003183c402450328440f020080040445c500b000c48101604c2a205141100c000c00b030b6a400301418214a1780f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 572142302 1250 572141052 572141057
    0xb040b090f03011a10030b0303070f0c0e0406020310120201020303040f1b080a05070b0903100c2003030a0501060f1d0303070503040e150121090c030c0611060609060307150915 77
    0x44c0e140494540449281540c8526140c00c1c41070320300d15070000b07403680704646004049001054188080000b04000c4100901c00700300483e403d840c0ca81000c01c040e500464081448144100020909444884808201517010ba005600b503580d50369609103141c0e522031090708e21008a4040242200c52924010003924641002e40b610800f80e2401d6441d0624580109a20381024440c0b035240d42c50006004016495002020801c1307503c0c3d000550710300c500700d121341c11300084410310494040340c004001c3d406a4008002000a60390703560081b0760004e030b00074502c00050f400280901c25041111098500f101d402410b503403800c00306556044c034507031069000031500d589035000c02c900e45511002c1700c01100b03400c0c00d0101001c16611602c00e50661104a11248240e46110321018011403000a00103184d21506d9000129100c0708d010301503044200080902e071082c540040c0712030500066070382c003a40010340105911070170201e00c01c20440d042d494980400c1950340000416041240d052108004241c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 572143552 1250 572142302 572142341
    0x30f01021b0105010b0a0c060e030a1e020d09090e0304150c0201020613080301090203190c08060406050a0b03040b09030f030703050103020108010608090c280807090b0a0b040b090f0301 81
    0x1c808685407024801d00164899240c540100b000c003207100c0441d80b40714107619060b030b009100ca2500400501001f8400c0c4914400400d00c94111504282c0c4203080c46e403d80300c07000c3c2d032001b1400c04036566110480a500000c0c1c1d804020095000c2c41c4d00031000c0e003000358054a007069255080581d40d0684032486100256145004005550301071045981151080504120481080d121542e1714030041c03003550803540e03000001404017103049200344610b004444041c400d80e462204014403a43d426900d2503c141d142c900c000030249049023404080304c00b003c9046095a58035121080c0f907110042c001c0403d40020000e020100503414000c42c890001c0f510300290a50560000402050052b0440018810340c00c003800515403000550241800e021281c60038050054401c051103403400c0304800c6616021031b140440e181001041000554214400800c101e800c5881008038070384851051403c1c0440812040c010350f02003500502809002038031328618112040d022030300b1a00006020000040d50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 572144802 1250 572143552 572143567
    0xc020d0e22061d0103030804020d0c05090a06031e05070306050601031508070602060c0f0d0b062106130207020a140402040e040b0a0509010b01141c06060801060f0206040f03110c030f0102 82
    0x1443d5103000f800001240303da40b503040d41d9000e00420406000a07100d10084d50b0b114040045000001002d054041d248a0300c50902030400401741a840c00203c070141d50301d0360400c040314000c0140c5004a608440101842883d68466400404003c1c0005040640f6a100340241c00034034500e0000401902c0300812141c0c1c6000b40c0281002d0014003582d0100c0c0f010041c2035900414402541c80b0f00c0c0d628140003a010f40085c00099551040003030300410420307500503074111321a2064071648a2101074621101c3c051440907044128031612000a6000384002820705c01c6036251801c0c118900c001501c0149010707261110001105021201160483c14500c00c00c583c25406000351900070100c03800030300400c0001070001c1c200c03545030030078500c421002181400d62619208040c40c1030402141c002c0040507294040242800c0003401048042590307080701d00400d91002460b14410781e0001c02400e0b1420807980c0c103c03030f400702d03406100e0742d507100e803002d45401640d0600c416002000001c000581d60500b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 572146052 1250 572144802 572144819
    0x9090304050402211f050f0409150b04110c150901060b071101180302030718090605090f07080d0909020703020309040e07140a0e07030b13051f090c020d0e2206 70
    0x41c003c2000805000800e070031700d0140d280725650303003c1d00c030219129075a082070034012030000c0c000d00f9005040144201c602c4c02007c51b0580c09580900d03416901804040b44240c04462180319000c000e43d010350009c0c40c083c500b5401c80b8599900041c0c00400456501da869842e200c0c550081001620320840c4101d141801b9a0440d00001c04850040d822408503803458002036114040f03407180302c1000f180544140214181c40d40094201ca0b40000708000900f48143c00079602c208020000780d051040e4400402c18880020b00d002c4001881c1d59407241c41e508000d07e01c0003070741064004509501c420302c01c4008941c2e450103070804458444005004681c070700a5001802c144884180d80030314120501804100c144000762680001e140c100070452651900125944100881c911520540340c2428042a2118244100c1500c05210b1414016580300c60045c0200da41301c07581d160140e0b2196100602c860300815401e110b48030014603818200da01c002540000c0e5220903034901c0d90a644100520601a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 572147302 1250 572146052 572146117
    0x106030b0d03020c2403010305161a0306150409020a030b0405010504140f071b05010b010806100e0d0215130302030706020d1719020711030d0e030c09090304050402 72
    0x5021600102680d2075620040d407a20701c1400424000c02217407910f4080114003404010343e071101880e94994a60f035a0400030384940c00c50500e02004d02500d14000b0748100161000d8038100389180026242d070310307641d04101d2110084545802d91210500c00042d440c62148081c0c8216003050b103011900c000c2960400040f100c0581040e841103182016011962000011065220034413007205401c50b203e002041d10391a03a04121507594103a8000d44004000043d0049e0035046002e807114641034a1ba40100010300620225080001c0c4200740e1030049840c0820788200954006805010440c44c0e15544e1803d550001c1040701d241d1741a05400c200710b00b01001200c00904152000d800311261110b801401c1d140030003000743d100410003020641c0c7d1951210012035400d0508011591000d9600d090180410000c035007521034014a032581e20030078014400e5900c8100300030050640b04000e80100b068124020740080c5540c0300500000c265078603580700900106494103140d031442240c1c10303829444034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 572148552 1250 572147302 572147321
    0x10207030f210b06041a0706060f0e06010e040e190b010b070c050d1401061202041b120c02011526010e060402040b040222080d09080a12180608010603 66
    0x2c0b84000800c01d0a50280d42c1407400742024007004110115440009000f40c05560403e03071401d100a08802c0110060f00c006040e2184100380a00189a0b00d80c14440341d0680c070b00c6034910710400078000071242e620401030310000650091000136105d49014185141c580718200c0b40350511740d050750680c00e1010503508580102081c81019142031155a178a014881c490f00c6120700860680440c08200480c20001e8401d80f04007030000c0018950b034048a00030340004950036800f46117443d00d010205007003000d0308200e0340c0395a200c0403000e1014042d401d000b4100a08002d0465603503981c0c0d407105205414000e002040c03100340c1840780c0c10f01e0411904010074841c1740b8140c5030785009240c803040e20000c1a003551264040360001908254800810301074801c1c26102c00c081d052001400c68500640e03481c130401d4a41280441d8011000150140c0300c01784c1d103014545103581300b0310503400081e412651542c5e0250681c54203510503a034440c803019550390541c10071800b142030030b0014441541d05215071400c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 572149802 1250 572148552 572148557
    0x917031911040608100b0a02030d0501090c090e06040906231f050f120f060912070b04230d0f021606050d09052d01050105060406080c0c070b0c010207030f 68
    0x1c4840c0c20150400c6403140348500d50a221030440020242480c0c2600315004001411002d0754030041c8080080d00c23917006c4070950702a10314010001c06c48000601c00c90242e02056101c220346da6050050303510312108010203056005031540c42c80c4000074994002e907003201c01404006002040e640d841c0c01c00c003000080000060218050265110001541e0100c044074030689000000181550118800d240750740354080480c4905202c14610600c00200140720303007494029034240c42c4050710f41501c00c0c030030690040c111640140128001c5a01c0e0040c2d510020a40e1102100c2003500c042454240304c030500d080c1c00800d00c00d001400c000707901030154883d000e8445d1050101d4505050001d04180141100e1519007a40e40d8a0300041200401040d5040d40007076507860382e0001910300700d050015862188281365402c00c3c00000c3c403820a0380580c1d003540c4c81500d88081c59620000f50940d507810505400f0550b205e9142c00140092807032005042c0e1600503c0050394071102402c001e01b5545d00c50844004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 572151052 1250 572149802 572149811
    0x403050c04090c0909060b040606020c01020706020d021005150a0b0a1107030c060e0d051b040608030c03040303050f07060c08010504140103020108220206040602060103031e0c021309170319 83
    0x1d514440f0902a1000c400000450000d28207000000303085004095810500d8450040380c0e9903000211189024402da0032a10102c2d02e41000b2600c541014807650056400440413880e0600b040d0446a030210390075085e03810004050001072500486984604c0003e54001480e1208641c402001001c4401e0003004110041c91640c85011154051042c0c400304010707050a19030301d03540c0c11317800404240c2040445503000d03404c003050400c0380074001d01780d4480d1307180c80b5000658400c088191541040d08130061400e25103107440644036036015141100b0107030410007080c8002880b81c810100300703011580d18241650304000601080b41c1d000d81e151440704a000c0c0c01000141e0740000650703400312103041c1c0510103600f15540451443d1100c1c0b0000c2d40008d001c036011030030356030029a0758101c0780650f51b400d0f10b24190f0301185038000c0c0e46c0740940001540008141e000f60900100800c501d50307a42100090800054846d4000203080d280c071904100c2000051241c41007031900c21901240001d0030811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 572152302 1250 572151052 572151071
    0x31207050d03022b020a0e18010b1b0f03030709080a020f0f0f1c0b18030904150909030e09010504021201120203030c0f01050a18050618011e020403050c04 68
    0x941d51107080385400c08040c1c0000da01c03941900d01d0300b5030b6a18400000390210320645080800f8000c0d4001c900d010002a04400722500d052410030324402c074000d240e80070303000c2503402d10034900e51780c2c1d0001c401d0b9003506403c075403600001c1408004804442194401a64482c1801d40c402401c6220562103840c00703a0140d003a82c0003507900c40301581040e08007152460f0080b03030204040381102c40a41400d41e884405010b100441d45a06c8221884942c0f00b0045000d031640c0d01c0007020b004040c0315071810341c05e91052011560909040d400031201c0036640012000c0e4940e42e408400a80745009412000211407c0c4423503501c1c00c06081c61070240604880a41c20040c580480c128101c1052141690444039034002905648040c021180d103e034010040e20103000b1000103c9000e400306031064081c03d4034040c1c12071f8201d1424460604402c2d03014000d400c1c142c540d44401030760304450703804000b0203559803407242544030540c400345046100d1091000da1554554208141030081d403845240c081d070b0400c0c215070f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 572153552 1250 572152302 572152313
    0x906030b07030f0e12071104050405030412051e0f060a0204060f14040305060403050c150c030c03060315071116051c150203010f030210030c08070f0e090c0306031207 73
    0x65404407051500050100e41c3d510560082c2000c64192841800b0b04a00042d6042c0c0000060004900031800c0d2904030b4903440a0000700c45040360050502d420900060040f5a00b04c030702c14100500810031140143d440c0760f0b46c900082131120400703d069200590f940000d00d02444103961007010300504506291800d480a009108400c6180c01040400744542c2d881580c40c0d400d640141d900b080c12144989420f24001d81203501c40340001c1843d2181d900820304001c2c2c007018032480b60344031000082c29500c403c14011074031342014018a505001d00c450071000b103c071a0020a10a01c129aa00c2210707400d6500c04a06021030011a0b980784c151101c02400544c4402171801e000d1520340003507034103036a000c1c01c0246182e0340d556083c0510600010001a80e00b46441c80e03641500c2c001c449a00f900200d03920160101d5442181c0305001c6811840000c8405008000b0401c6102e00e60404d00000280b09001500800084440ca241d415000c000e00ca02410308000c0d6140b481d814014046c0b0b45191501d81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 572154802 1250 572153552 572153573
    0x90a181e1d01141b0403150534080a0e010905011d0a0210050f0c0313030b1317030a0204120807030f020a0317071b050106080d051201120f02120115090603 68
    0x2a070301d032900900c4d45020b414000008803001540c01c000c1581d0402c0480380c4ca80050241502c10001c06800d0440700465801003d00c0d0b0b000140c84c580c3c4c42a0a034118000c02e4901c160014040f040032075558030b44185040003030040c0b00b200c2e0300c45d10000980855011485054283c601300900d602e6000401c0c1c1ea0040c1c6885001d001c0640701030419503110501d2100d070745251710942c050480c440c007000c184501c01c120300b040c82006507845660901c511b0781e02c80491b24200d19026001400c16198001141c000035005002150019401d840140c50140c4403070840d206100740314411a881040000c08400345544034000028090f142d1018040e20305107078a005103032061094680d08543d030303010701081c98030f0b0081e04090324000500080010001403828051300800f40d40c031038680f050041044400c02d8522900c01c071440845400000140b40e42002c03644d1030303a440c090310200d0303081c008034810700d02580d155003076071499141050010501500b0401100501c002d03039403210f0070250074040184005003c81c0c89 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 572156052 1250 572154802 572154811
    0x10f1202010509130204171c0509060702011206050d0b0103020a050d03120b0d0210031406060c07030f1a090304091103060604030311070b030a0b04060b090a181e1d0114 74
    0x540c114131858114400700244200e50002201e010705c0e00c4005022000465500707070041d000c51385d425115024030701c280c0301c0c0e21524802650010301003045000660248150013a404840c013000a10242c4403c0440c4640100b001709a91180318240100700b189060401d50020300010f031035039000703151303569400f4100c0320f00082450855502c409550245444880c024805160000e28080141003804000b0740286000740015201509407000164030b4146542240c495107038000040102d80d117540c5400d1002e02c03008200700c07440030791040d078109905681e5450078050440c030806155240d1904030309400302c0b400c0b00e5415008440c1441040580e80d610816541101d8041c01c02040980c0301c4200542454042d4014448044000c0b0600409003a2035000c2840f200080d10200041515408528201e0151010681d400062070005101442d00b20040c0c113a10b6031130040114005240c00110100b86140c602a004c07600d6607207014915510443c101c40e0328444007007008001c3c2000585401036900710003070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 572157302 1250 572156052 572156059
    0x5070c152f010e0c0901052e051207020f1f14011410020105040b0109020a0c051509190b0403110708010c1814030705060a170a09170a05041a0c0f0105010f1202010509 73
    0x8c298030204801d184104480032032081d02d58110100070800a8181d401100d640045044440d0028001d0b6000050380011140d06000038615590304480d15141e40d4510b4088803011031f141c0c20a000c24a0921050901800d1143e218411411015003400580780816001c4011681030800703110214a042004e2819120002c030096502e00c00040c0640340155648802480c51040d003a004a0070080541ca503405020307078400340c800641e00151607030303413006000c00d004d031022a00c080401c00180c0036103142c1103280c3e944c205855045946007003141c2140c0c020003090010500100e4483c0081490704c0074440a0000c0001c170010346103016001c031b80c3c0d503219409100d00902c0c00003040c50549000710040c01523044604005802841c20090007405804840800c9450403100c1c5030508543c1486001d41c0d403c0c0045984a0741054600507032911001d0a100c56455188010403404a0500060000403d180354081c008512545058102d401411090f44a00e140508102051005030392081c04c840d1920000c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 572158552 1250 572157302 572157319
    0x1303050c0111062e08030d05010f082b0e060d05040b060904050a0b0405030412080c0601050306040f060917070605100b0a05090f0f04020703020a1205070c152f010e0c090105 76
    0x94584c02804219045880940304c01320742c2420010840c0c0080d4141e41d8102c500208843d07a07800c2c8156070f01c0c180c00c0000d2000c40e041c00c0b4696010039042120010490902e4456452080340f00411010f07845418161685912102040184120311010239000f500507540c054440c40e00c1c0c0c5a081d118a119a80144400580008101800020001e0b103005d0291001100c4440c40c00c0d141001e80c2c0e40c070841000c0c2c404c1c014900002a107180c0820114411174108140d20001c8030682d440030000d21020303104581d4031900b54241106046500060a407007882a000043c0d24201f81007010b48065403948000444401005107003034207076014007511480e800a4418401848103400090341d100042000c1c02d0b0030600c042a85000d0542c00900e282080d801105d8480421075920000c44941c464104090004c01540c201046030315654109030703035192103514001080c08804400c0b1180695141c9204600060700c1103c3d0035984402c1c0710b40350300c85c46001e00801c540480c46010900c1134005210b00340c031900e00d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 572159802 1250 572158552 572158621
    0xe0a0605031f15080f0309130501031e0c0801020a091409010b18040207081201030c0f080d120b090a06060f0302040e070e030f0d030203070905040b0d0b09031303050c011106 76
    0x107010a03140904406410341e8905c0420b243d895589420505065100711281c1e4000c032824200b82c45918103a030340090045023484522100d414400f10507110071140c04580c10000a0940001c0c03028202007046d540d035941c4001e1504181c90805003484a50501c01c01014004104a00d19002259007000407a00c07a5248464402c00180080c015808098081c41c800200c2c111414045090203050302d00c07402d88030310303255140c1003414011b102500403c20654030070100b203900720707026103c0ca10101500140c08240584280042803051405850f180400c544850f014840380d13420142c100369072101d528046003083d1500040240b808030240c00b0701e042c0950045450402c0c1c0f810303c03244c0b503081c25030000c588a0b640600310050096104452100004d942c4c10000300c3e0300d18240c042c040308440003c081a40c0741199488a00880f080980304502c0351104205211005e60042440802107000320060140a1706203000907045d401310030f043c80c029802000401806030042c0410880000902c016002410030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 572161052 1250 572159802 572159831
    0x306090507050c33161709120f070204020c0a050f0a051b0a080634050a0e060910170c03070807080a0204090501080102031b0a050f0c01150e0a0605031f 67
    0x80b560f42c0641524041041054802200c100c0b00045c1c5081c1d40d600e0325a01820106e1408a030302903c00e1380143c0c0214500001a206840107003220207001800b10f4a40700c2e03640e0010b001c0740d000310144e035110740200e030307050301440380c10302550300a110104007034100c00b10603598080d00c03014280c01454004114817030b01c00761a1903d015500103800000d0803601c10f81003521600d4001c0740c0b16029000c014088030584500301400750b07030f00549508180c0340c03a410812110803c0e240850150240c0d500f0190500100d000303070781c507800b00110030409a1240b5031700d64618140f10700d01500003041140241e07410000c0c0080c0c158000c45c0254004010718046260352100c48408001c0d205590200c01041d0a113400812200f01c194001d5004500102c00816191126818400c00740140403071507010034000d0100058107101c2e007005000b4070120500004890350340301000a040c2005421840000305541c0412031034003010301c20480689003c50061883c1101c9030030710420000e10a2a008643c0c3d100c1c4144a0001d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 572162302 1250 572161052 572161123
    0x509010209030d02420916060903170c03120a021606050115030509100c02101107020928090f0c03051609060509150a080d0306090507050c 61
    0x18008090340e083d500146002036490b010301d51107000c400078a0400601d03030002c1080209070907059441001003002940e405940044000302810402c0c00b40701c05a1140b407030300402640c082c00340c3d600e40301202815030a008500480c0c07a68101040302c1c00f081000307030b401d070f0010a444181d0700150b00660340340d641080c03d80190041c00100000c0455098000c0c00304003040d001981645c01e514545a2740400c6000c045041e00c0c0c1c2540c8021751508440e80614600c042c540010384042e6841c011280c40c0808114030a00316071101100c038a4808000c0351510851030f0504100c0d0308440611031764446019201c00e1312280d178035006001040c9507516400041040709102680740c03201d8100182c907007407961302d0410584858031103a411130058001040401c4844540c4200019904c010b13003d000c0d60358840300d0090403421052903040c1e101144240000b004101004042189409a0350100d80381d450898000143ca80c0901344006019040c402c0135500040042c903011640c0040f125170600100301a5450040f2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 572163552 1250 572162302 572162317
    0x2d04031118010b07021f12050c07170414010203190c112e0306080c090c2503031a03030d24091401060f0221040902161101050f0d05090102 61
    0x150074000520040300f0000f4083e01802a1001009001c1e910280c041c100d186a50740004582e00c030b40010b0b100d0026902c501e90180400c0c107003500d002c41036140d80c52198500e015407081c840c80081d003031251a032203100010b10b0302c8080c0011420000c0080a506003c20b00444110801803081c640390184005c006240c076883c0701c050a9111428250360f14010650711040c2c50a080010944010104500c40e10486040704c0550015141c0070304140c00f045a6010041c0506104a41c03d106a0451402414010b0743c1000c01000a110000c07840c600a0301361030071018440340311825a00002055100031045038415a191307200000d00b8003011201850301c031120418035910b00d17584903021031410400d03400500c0b41100001958001c1c0e0b0390750401c0300c0403002000924016081041b1101d1001110214492a21914051141403544500c5040101d81240e003d030710340350582200c4541031108120300206072010038a00b01e4903000c3c904001c020184501a081313184507544000103100f100003981940c3c2c48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 572164802 1250 572163552 572163589
    0x4030c171e03030603160f05010309111807171909021503070c0606090c0c0b09070815062d10120501140915010c03260109022d040311 59
    0x5000036400301c203982c0c0e007003100c00703600034403aa94003849144210402d9400b100e01c110b41d101441824000110041e0603907000c22648040103000701507042c0d80d2201100032240340b1240104140c50a000010121604810b410300642a440140051100341e4003943c1d64001c14240c002c507160708140b010544184150b02c440003458000b2050201c80307507010b00e61028950081606019107a16034648904890900a8060101d804044c81c01d00082654061507885090f540c01d5540c00c6640c0c03e5031a040c42100240082541c00d0b503010040d107490035055401000101c0c40991200901c4820003200207500c00b0503161140e0f013411101441e06100341f4403801c103980d058400348090f5a40f000b03051310001c18110184e1041d0042c0000032640b902941101c82c0d440300503540c950b40350500d40ca080d10b03220052514016030340782c0381c40005c3c101200b08003950b0081140080043c3c1d61600b0b0300e020302d0400780030303110300c041404040c42d40c00040d1450400c0d503090b80d4020200c60200c0c03241c180010407014105410182 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 572166052 1250 572164802 572164843
    0x170a0210050c0f160515040b030405010f0c02010b0d030e120f070906050603090c040504060f02070b190902150f090a0602010608120405130507140f0405041104030c17 73
    0x2846910002401e0a882d014003168445010100c0311600c0c1c00c0200340340815442e540300c04104514202c01c00480c4103400020f1145016201e041c008026402118141c4007030b174540304c04125540d205d21441c00b0840080c4000c119a001d5000080c00e295052000030341003095640c030241c001d0380d0f80138130690152844005c644080d5445050b40c0e8aa40061054000681c07400e82c0002d1542810300480e8802d401c40c602400c4100c18080800005100181040e80c00d941e407956940c3d540d018030300c010030b4072034006d01800360b051038200c4000c2030700f00b0280100c0c04003c0c101607070303100161109910010607004804591380c80d0442540e54030b82900801c03031103540c801e50241c80018801c0d01944640261403401068074038103806461408560320448c451150001c030380501500c070140c0aa0300190b08004a40340122030040302420310303606500320360711061b01e6801c0081c0801c10b0780707458411800052400044c0c6401c062654031180380021aa220f4036006000302d404542241c5824420110400e196405461 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 572167302 1250 572166052 572166079
    0xf030210111606090e070314160201060b070602031f050f040207020415060c140d0509041e0501060e0a05030703030507080307020703021503041412040b0f0904050f090d0804020604170a02 82
    0x14040721141c4542102c00b05d04c1004035000320321a02800740c2c11b2080c003211400c0c0b61a00013148908031000b540030f4045541c1c0c6c010200f5014502002082524011580980c0740d04145031103001d4003a44500040441488800800194880e0f41d0705440031a01140c0c0144c6510349400400c020304401c2c4684812080c08410100314581c102442cad01c81c00c3d010304a403c10084003250b14564400e005500c1e2400300e0428482000b640c40c250308501c001251005503910121410640c41060340c40030b8200d100460702c08030004070941080003602c00140402c070000c002540c91a10041e06611074140082d04040e40080040d2856008010385001168050f112815029031100c81b090b0940040e20112102c0700c3c2155164880c0b5030024101010701100056645401c0c5480a40b90166000c40590711400f8814005041780d5a100d00ca010310500140e265040b652402c0e590003418403024114500c103011b451010f00c00981c4640081e41d0640710b45e0701c40407400d07445d5128602d10f8a07042010080d03000d4030030405803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 572168552 1250 572167302 572167307
    0xf0a020d1202090d0803070309150b010f020102030c0a0c0507230924092a0a020c01090e011e121220060a0510080a030c0c0f030210111606 61
    0x40c40c0320341a58510544040086004040c0d02c00d0601c0268810340600106000c540d1403002540c012500d030a000541e04596520a541750004021702c111440d83c403a5039542a5810035403121100d00d00744003c42c5585010340c4808214000c038107205040001406602013000010444140508245242002080f002c281e5404680d40e90665071805598184003103000e481100310300e600402d0765825040f640c031080700240308100f800242400c1c4000018065460300342e482002c00503401c030312101030607520008a800a407400c00004002810031116080801ca0942081e030460305441841c0d003042e031440400002c1802d0750305a0703000100c0420504803410104501445202d103c6580358582c2c003111041041c061a42501c185066030081d0003020010701079503074941c030540d4003c90486401000c41d0b00c2d02c00c0f0760b103022814901100420186c00441040c0314200301800020328004003d040c000342140c1c00b044130507041c0d01e091814400c16250060381e050051182034480008411300c81d261940c2c50300300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 572169802 1250 572168552 572168563
    0x209060f0715020f2704140103021008010807090209040213060e0301060b0405060706022a060106090902160b0406060905100905090f0a200310140603070501090501140f0a02 76
    0x112810320301c150720b180a0b00074034000d546111484a802506254064200600094540001c024a200103a24486a42d5078501c0307468514224000c0380c40503507042d84148111100c908610030103110340b100040010740070015400058800140d00507071503e40080200d4080d000ba20600c40380e90741c0c1c14102080707403a400080b483d44080202c0c020f026450307548001d4501d61281d8041e1a800c448100100c10103d84107400412251070108080c039040005100a68003040f00d040c0013a44541029004100b404d60014007107000c2c0c88901011460403103907070fa444c1c40311341c0003020082805160300001800d2082d16400b15000388000c104c10b01092a080c814480c0441031405040304182c035110200e03102480014240306450409401841c002c1c2294440e0300000c2400030300381400c08401003130248140c0b82888805007440b410b40c03002c118024503181c1034640d000007c040c0742c083d41c45a03004000c1a079006d101c0320100c0702c00b070a0140b80729418080c0c210040c4207043c1c15041801c00060941501c2e0780c0040c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 572171052 1250 572169802 572169817
    0x20111030112020319150b0307090615080106031107020d150501030501020c0d05040b090607021201020c0c040b0603070207061404030219061b08070303050a091a01030b090a0b190209060f 82
    0x1c0e117100410482031040c00441103a005420b2840140000c80c0c219400d51007690181c00060884142581c0e5070f151000b076640c6a044000203004d039094503001d5540140c41c050140806041c02e10091104104148540c01000c101034410120720070448248032507030004800b072480f1403005100030340e141d0078524007035444000d039200315209800501d125180318a05035401d40c0e0b0800d000510b8904400c0811a281c0c010000076a07101080c442e00004114091000300040f88485000d070100075440d601b04400c444541041a000e0b2030200304000d0740945c04100c210580b401d80c101410010075803800070440780240d410003034018107040d00d4800340c0b1103d15070304000c880c5d5981d00c43d05014950f007800d50010701c41e850014800d40c01403145800290081d0007451340503801ced61307000628403480c0d141c840303a940c04640d02106a002000050013486160090f590740200c2c1c0f200100900c071500d80d6851155800180320080c4240c041002c442d1403c0b442d011690601c030010200d0341c0360b80c2c0525440345a41d20100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 572172302 1250 572171052 572171059
    0xb100807090b0406120c02280c0506090f0d03030e070602010917041503020304020d0611090f0103020a090e040c030c0305100c0905090726131509021f02011103011202 73
    0x195181d90b48226810341e003056032594440190403000c00080c140c221001400d5000c3d0601860020100c0d61502500700b0b146c42020020282504007100f4151003908003034010310301001078280c152160010140c800105403002c003070640c01402e08a00400c034900303150841c0d0250400c0010013a80c15000784060300e0183c03480e1a0040000c461111492103144664103c1032001008034188500a501840d4400e0001d400d46280f25000c3d40c40e4401c40e40f4609030b4170390900021407210741070f0900c00310248060000382411803a2050061014000c50200d02c929211015071200180030041e41c0d480703040c0155070081100300b4260b120b01e03100380c0783c041c07001104200900d0011294201882002c3e244225000030700340c232049442d2084211500b44460070000743e1103606a050313010303c00140801d94880c2440d03071001c000c1a600ca2801122000510500085c95420440e030300015a031205a403035511603c0c0316010861081000c4280e002d820340c40f8100418803404000050441450a01c0a440700d00c205c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 572173552 1250 572172302 572172317
    0x180301061a0c0c03030316031a0a030f03051e0d0e010c0504170118050d140430020307140102010b0406150e010c1a0402270105040c050c06010b092b0206030a0b100807 73
    0x24042c280b40240e83c2062541c1c4603015800c0bc002140c440182055038034041d1410a19015400169940c0800501210407828000103540500c900341840351030b5030240d240c0024003035156445402061b602807405110510b160f01c54100314001e030254009509180c001c440007420a83c182001500c400300d8540a40204280504418130110070030100c0b015180c01c035807007160440071155074090021140781c0480e00350310014120f002590b01000003100400c042480d500b0b050a900e00024295900034030154080c41c102282407114554600092261054074600220700d841c00000480704240e0011001d0b12604070001c0d02400101105400c921480c02520001c2481c0d0000510076030340382d05490300c51500e041c5140103101d5407806403c4441c1d841c2d8546002130812210808a40c2000402c0e40040100b01d4006918640740c10019040340341000c0c240f0b10345040c85442c248a139514807114600910174580000050308107001c0b6030104490316400740c80000ba0104c00c0c08064001807082d1030031804103409 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 572174802 1250 572173552 572173571
    0x30d060f14091902030403030621060b120a0b0604110309060615070228051206090d1106010b03040807060905010207140606010e09090f12180301061a0c0c0303031603 73
    0x4540c2c114016240058512290003490351000300a4001030421000c141e110240081d0107609038011901d494071010001c2001115807802c3c030102c03014407403050300800291034440c5600380d010910710545030700a10804080c2d138800c40050020240304030b00c01007500d4040144080c4180000b00b107442412309684001c071a00382c14041110f5402201070081d8045180c10b01c040102c070004003650915a10340701c81282450310b410001e2030005038103c0f40d403040d80c004020040d0065003004030f6988041c2c00d0420940e0043d2000185403190414003604419410001c0403408001034078044400d0180c00c030300f0410900040b403074028080d500900042e0b8052031000e0742c1040c2010085150f900840058481c03500200c0b0754020320415800c010000b007414000c0310060200c2240501810010300004800c0300c0d9544c0385010942c59a01400c000b5a00a0785441e009000300d2001c1b901d00340908106a400d00e448107180824185030454614000b900f41c04040305001c08420401e803110b0b5500003a0b101401105031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 572176052 1250 572174802 572174809
    0x303040308041211100309020f090f0708091002120403121104270f0903090b0304080d0506060702030706020706030e0307020604050d21081b1303030302090102030d060f14 75
    0x61404081c1460508010800c00720314100c0005250034802e14061418120620003d80000130229580020a44131003c400451500540c10f4451140440c0c41095604186000380c800d801c0061640c0140803d61010a802c8601007151200a480001c415980d4000300494002290750983d02100850441044140c0000d10790003070303400340e00c40c0b510814201490840c03000c0034128061034040d13504d00300d8040da40c104400b90250248001d04060081080d01c05451300070700104075940100031004041c07080c00000713020b6408035020071020340c03008035850300c40c040051260311801d0002035152280540018205401285502c2110b0079610100482200c0005554692050490017980280d0410081c080c0b8a40b030b01c59680c40500400201421902d40407904050044600d10f9001180804c420866886217104012a0240e02002c010741040403600c1d0007000807070f0b9408024240354001c030312a069640308000390740e112000074006000040d80d590201c0122001409000a80340070600400d00909 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 572177302 1250 572176052 572176057
    0x8030c0706120b031b0402090a0f050901060c0b01060c030905060a031413021c2303030402030111071e050102130b0d0c020c0114031003020d1101030e0d0e2101050412020c0303 77
    0x40f40a4003600e803400040245a180c15810084180e00580c00c0c400303001305450f8070080402400b40d00d641d40b80001d081401f00070701d820b0140d010004010b00d035205000000c0f4110441c2d0b0450b2510304080340020001e01d000d5a251a0303a400582d0884c0021800e04409540340d000004076280c150518200b540315890104240c1e10103800194004860100043c403a9030780000314500c0310b0003810f131440101e07020150100940500f504207156a0b0000c014041546820301c609040ca404c100c0080d450096141c1e0340d080f0411a0b07a94403112014070504040600000f0740451301c01a03400c0300e00d1200075880f410001c034a074000303803a0131002c58905842c004109000040054000304140c41d0903121001c0b11101400c1a800102040039803800750700004010388171062440e0559220b00c6001c80d081000b42c00040882ea00a0012a0b00c1e910000e001c1e904550840f01d1a10345103401d8a8200c522807450f407241ca9180644443d0500540c07070700080106129503803d010048528907400d5031000600302c01055940d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 572178552 1250 572177302 572177321
    0x140717090d02030406140705030a05070515011401120b04150815040b180c0405040309090510030308271903120b010801051e090705030108011104030b0c03090708030c070612 76
    0x143d10401c02030016502641c0e01000c03540c05c072150580b502e10706036070301d03425030b040943c400780490b40100d580e0080000911404100d84030108000b54650315090005404400d03814100d03060055600c200d0309401c146401181e50240b014005015800c215484451402c2003480752200600401c1424204d100308454500c1c01a508601040d0389030716a005901d0386100f40c00c0018005104601640c3c1e401d881d2401030364491070090710341000d05403400d030f5000140c070340043c0300210b08102d401c2c007803000a4001688980007004003203041545485002004030400780c0e040d00c40c80d1885504524140c45c101e1041c0b06840d984241d440c0c0d88030240741c83c0301d10240c0b1100200c45000c0340d141d80044c0a0b41c00c281107003001c8000c40c01001c01e45284401c001c64001d15055442400082c8000f0061000460900540b20540301d1490000c2c50700340f031511800b8081b00013400c1c1d05d01c041380000102e1a080000c000200181c032000c0c0c1030341c0d0781c1d00c41021041c1c4c0c0d0b0401d030f100d5180441d4101c901088501c3c00c51003680c44d40f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 572179802 1250 572178552 572178557
    0x50c0709053607140d060507021009030509090601021609050c040816170325060f18031119170708040e09010507140a0f020f010e0106031a0415050a140717090d 70
    0x140010790b0740707030406800010480710441c4646072070b02b0442040c60107180c2c8041c0c043d0712216550004003050003a040d1000f07017142e041d540315140120481c25005428000c503007481e40700003890f80ba0551000c1841c404c80e84004400d1040401c034400c070614200c010b00848420360441c2051100785a207007512406108000c1d0711080c0d06101c0c03041d103546882c660350061449000000b5440c0d00404280f000c0b28a5140701c5811014550340d00d03005c054014051308040002d02004054020024038030300e0400e90b0544000b4091041c084510074130f0348207403050f640301c241c3c054100f685440c4c40707c0c80d600018400300c40d440d13015800d210125003680d020f142000c001d0a040c150562800144c224103070b8001256210720421481045000c40c0a09400c0c03040030f2000c14580b00103d0440d1650a1485040548000c1505400340e00014040060458200c14007010034400c40407a00707a90b000c079288000c000c03082c0640c41e40501d0300100f103c4507520203901c10300c0b400c08c0340300c40c0b04035191426074960782c20400541902 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 572181052 1250 572179802 572179819
    0x6050919050d03050c090901060f020c041b0c0203030702042405060a1e0e03011517010b03071509120b010905090705060a20030f070b07050c070905360714 68
    0x3455210307810083c1c5c00800c1003000391802c291440840c0c501f443c01d902c5040055504072242d1078080c0e040c400c000710414100d0f81441b104a102e030000c04220646620b50040c0401800d0050454070b05000b0384d0070940d0002d008112040701c0d00e14029031001e000702500710b0038005603404126440d01106540100c42d0716900c0d50120b85e011041c580d260340302c440300002801088200101c0a6409010b42002e494025411090844c503000e040803048081c084910703560f90500901040a071030000d190401c172100c18108403104009001d00b9910044d2982000c43e04a0028036103109221100149504891280b103040040b6542c0fa004161960341034007a042c1e008078100b0440c808180301e0749282c030302111411032124007021400082c6140d5032001c02703c540b11910104040d0f061200c44101d01d5804181410624540041c0c04080c81e01c52001d4020158890399070340115a0b08400c00300d042d0595044030605c00fa88102550303c1c200c0002c0e0403620343c14507104501003c1046410403404501210313000e0010392 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 572182302 1250 572181052 572181073
    0x6150903080703030203130c080706031a090f0c0c0102030f01210c030602030a020409020c0f01140106020705130e010f0f1b05040e092103090105010e010506030a110c0102070605091905 81
    0x100654406010302d07000d4a201c4000001103800300c41d42000401b0b82c40b005100080c500540542903503170372200b40700f40650554199074240c985409035940a0016500043d00b55950a8070031068041d5000341d41c0d03598030101c00c009005002d8184103041e80c00141035a6241d0044650480c201c126a0340d008100340d811490400010f00da0b0340196400c03c130046805801d084d01e809584003281c101d100085460ba0003145151074141d000c2c07044031010504112800c14543c1011006581ea0f00544113460140c41382c0c1d141400f550090713a101420040e0004001e101c640d00030b0003001c0107801c5010320280b084d4a4102d401d02c1c040174881814841c1c89641c2c441d14100f07441c00c40c180030701450007800000d40c2d00038540c0c00345040d48684d05111004100d403c0342c40c2c070390800d4060a421928141c0002c00300da44820010310095903000203aaa11035600c1802050203d0003602c6000a4001c10707164400a60010540d0420444d241e04460b2040b802c640403141810303c81c12514130300c0d0415000140850300f0825070030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 572183552 1250 572182302 572182307
    0x2031612021b010f0b04020c1e0a0f08270d031112160506130b06060a0309140d18050d0f03021207150e06070f110a02030703030306150903080703 64
    0xa4408603505003005040c0715010b00d00c4980900000000142a55030310021003140e503192064100c60740c0243c030118103240040d2900340e5103104c100da1002c281e0300300301a1140c0d00c21080011a101541c40506440c803188640b90001c25034014401c007c1c642c0c0c0340340140408590300e101c03805012a100402c003800800300341d01c0c107464114645c1c40c814198002c0c0300c13480050084080080011208003421401c524a007410190700b07040015020100c0c5555050701070011900000030580c2140d07085400325600c1c034500400707030010125a02c0042c201c2c030405212400d90007003ca1080c2c0800c7c0c5030b0315150301d0394880c2d0324446d40c44000ca0280725848505008400c011070203040302445624420b0044514500714110840c0450300405801c4918043e00d468800300c1088901591801c00c8064008005a00301420082c014442c0b106c02c4000f000b0700f480c1006402403007088004450340e009820740720350710346038140103000e4140c902074540d0503184030f80340c00786482c452030f40d11003200d4011011600308034660703408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 572184802 1250 572183552 572183567
    0x2009011505120907030c091109120f060c090f03150a1e020706020415020606090a0c0e06030c03090f1f05181b0301050c1305090403020a0c27020316 65
    0x3041000002d1200002032454100303a1030150100354000d00c06503155160101d00c3d0a0103820600d1818140f0740c404007261101001d0340c9041c2e408440806e0500304460b4150f240040d11181c044982c4240c1c1c00344000c80c0801001042e41040035950824101d508000b41940d0700c0c144d079800c4002c400346400084121540d940443c0503500f4405124481c404000602d40c2680c21a000030307151940e0020307003000010400c0d0860b181c0104580041c0c00d1030314000f000a0020903001700303031417100ca890f44d5403445558850740230100c0d150340062030720f610b80c03c0c810070a04c05e82e0000c8848140a02c607141d201c2950407000034204466a000210040306400605040030241c44003515000d003059014100d400b10100c184141e1034606849140c40d641d24125008140c00d440b0080c160740d500134000c101c070b000c03869a40302c285400d4031000d680c802c10a86030703031604900d040e00750302d03010705468501c89000c034503030440608a0368160510450b0018041e0101141800c0b440141c41089400e900e444003450720f18003a585 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 572186052 1250 572184802 572184839
    0x40e030c0712050f1230042d06050105040c0e091807030b160207090c090504020309030432180a0509070b0c031210050109050607170f07200901 63
    0x5030fa01c00720210540c00d103015170900510303603161400314003030381c2040c02c0d805051a00d40920040c4042180d0507141030a4200e070180c4007521340d81101c007174800898070200441100003220300084105420354100307000182002c1c000d162069041404069447d0700c1600b005407800d800a010039007a071030349098451451960740106255000300741d000400301d0481c401c800d115405240c00c0c1151034042c001c009017441d0031900b03c4005135242c8400660f4075940088400155075041e140180c0d80e071034542800345140a6a8040b40052800345610002c1c1501020500e645c0c549084150b000d190a18040101060340032602000611220340003442c00d041a03084107030800307200d400303940003640c844100642940c800c0e04031120130361001821940c1420b03c510000ea02c081d48940702d40c59030b0f08200c00208841440d2144503c203103000300300038040c04280e031607005400d4202d04684c0c0c2d941e548503100000e40d800c44603081e16150002d9480049200c0132120108003000c0080c11b03848640e080542d110385c441c80e01607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 572187302 1250 572186052 572186063
    0x90f030601151d0a0b07060b03070b0f0f0405100905031b0f0d060905100203180604080a050c070f0906030303061e0b0a020c0414010f080304030c05060d0b060a0e040e030c0712 77
    0x40030b072409504d403840e841d000341120007042c907580c040d141011030030389035115109400395005007400c10541455000380c42d81044211104c503500c2c0900e46506c0b44c54052500300765448a500c150049a854001c3c102c1d200b11202038090760050354403904d91426040e51240901d400100c1e140100005140410090f0055889184006180002902d5185c035210000c0c00c90042079a00200f40f111141e21041c1d070090032480780d4020b01c240d16042d951943e0a016080e00e8100b8414046500c1c0345208040c40000301402c1420f00b040d414541e52100300c0044c0000384019804a4a45000422401851001440300d41446c000b600415880c210b6440011b03845400030604500030940d03400c40030340d00c43c06000103005052a000540e54101701c0400d105110644c0221002e5004020800c00035002c000c6260844004940c10364483c1741c6c500c03100c00603180200b4869031202c800210f40786110740000740c0c01f600d030100380c030208035202410b84c1e842e65a00c207101c0210002d51000c5030400244c9080f211106075140b154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 572188552 1250 572187302 572187347
    0x3080a0306080312040215070201020a02040902010c080319112506020d0218040b10020d320a030c03060f18020d050907081009030905210d05090f03060115 68
    0x50041c5400c3d6001a9101603000d0f140b40184030039403420f540800241400801c0c0c292901500c0c3d40007035030324251104000c0c01541c40d1400c0100b90f85c010341e001d00706160400f5425a8030710300f90300381e030356403584d110485e0410728078040c1e60f071014460fa00e090f180340790803900c01d1404424504040c070100a0405100b151115005c000540880341d150010b000c11070030848981021030421700800003034800000c191405014080d18060b4202c0e8009034003003441a440c1003c000c3c034919811181d0030526060800e070340110748000461358108648005100ba0070340c40e54100590407050301c0c114161211403040d134500921311102030100036000034640a01c0d50181c5401032405403959210410b94a0850360030300300360041c1d18204807641007441749800e6040590003c201140b01a6005003101c0a5401803600170150700a0316100801001d108040d2204594200c81e080f212854004125230b00c590351503801044c43c0c11100a140c2000900c4605844240c600c01685480000e402c5840280c220028644586d60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 572189802 1250 572188552 572188559
    0x9060608010f020c010e060c1207020a0f1110080603060a020f0d24060c0209150102031b0c01111605060a120603060b15031608150a0b04060809120403080a0306 70
    0x24030800008100e07442d800350304c0707aa200ca401c40c21200c5080340f4900c26001202006640035500b01101c20000d0002c04880c51622840000c03850000b1010b401441c0301d1050560406000650380d0142c010700e41184da20420702e024100844410324141d0780076805521480c085403030907030190060070406007008900d50404c40c003c81d52009443c00e40d1005050005d148600c1c8413007940075260303070700540900c2c2440741082015501140865000506051948003d44e000300c2a40c0c0c4244210362440105081c0c05230b4100302041026103400b005500207020822290110300c9d0094041221030360010340c20a401007051030141406107507800343d80500c080125a120845040320a4401c11000d5030041e50002121412501844103006103030700d509500c6042441002618110160009014161840c240c4440d0b00c03042c05a140103507400320182e60000000307800bc103c600c400005801150910382c1c400500761204500151510310704400c510448004101c00d20200304000d004041070f0805140003d00340740d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 572191052 1250 572189802 572189819
    0x20d0e1002280507080f0a080906310518130804050d05010c0207051f12150b03090d050307140a1202030108250501120e010b0603130303060e0f010504090606 69
    0x80d0700c04012480000649110b060040801c680b9001c0d06000c3c00034990000101d0b84a0764400c21900700801c05000014038980d030351141001d9a0f2404010342c0a000300c800324032071015900b00e9411000d0000d807003a403000501490440400c105401c2a502c904442e600d51f01d003008218030f60650183c456140401c4005400c2d00c031040084040e41c011000003410601d2080001e0034403203168041032003050306030842600010382c81d1b032802e01180c450904514004170104860094201e580492104958800c000986004000004e603c2503952005443c2c084848034010b0380c560109451490000d0b4441a213181030b54081c0740184005074140c01d000d400350001c1d46003041a40d00c03d0308000041c1d00414065403a2205001008008030388604054400d181440700090824000c9210080c150707495006000544d0b000b9804000b40385806041580d8900d8800e010f54104009000c0032030010707151070b10006080e11149001030040c10300d10030070a2940d2070142000050084a01d040c0e480d01c0e95028000348042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 572192302 1250 572191052 572191093
    0x1b0103051320100504081b090c0c0c2710140d0614180f0d1e090b040311120d05030a090501020c07080d14040506040909051c030219020d0e1002 63
    0x1c3d6075541c01340d0785ca0601c0d0240c0e040456400d191104000c05100342c21030756842c050490362000800e00b50741d8441c2c890584c003a18000d6080e0015400141800c8400c1111200b01daa401142c0307854400a00d10303445000b10121042403621555503050170624900002d4900182c030f40034171b640182c502060718241c1d04810101904140c4440c000744501c450f410340d0504050041c0381c0545146006400301c188240c0c00503180300540e0a26840603210248904401c0f802204210064000708101c0c03a00e40d62685481580140c2d1000c403240b2520540700303580150500003074400c40800c16035032050700b152681d50f0100c0c090942004e040314255000c1c403a4646400c020800d10005000000081441c481c0d02d10028001c00c0380084807801c00d0004010034452615210222000c030390000c000050001c1003800d10500b0418040c0d50460440d01c002c011001035641038014103c14011802d202426030103859050f6a118605a01c0da400f03c4d03070100e0146002d140c0040300126182180c015209648000c0c00003c4050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 572193552 1250 572192302 572192329
    0x20f0d0b0901090c1e0504200c0d020601121518020d0b0708100e01051207031b08011a211617060109050103020a03080a0e0907021b0103051320 63
    0x341e542d802c128050100002145006200203200c170016820f1045401608800c180280d80c0969118901c10104034121540c122a01610840150320b0700c0d4400643d030b40f108140050000144521000440e54401040f440900d072944650590201010206818050400301e40e0404111a01c2d01540000d42c41e50704102c1d400c10f1192560780b4441c50001c00203041002c001d00050403040d00110f0500c81c4070410b000440c191102103c0703100494603492405464100f044d0030040c42c6406502030180814140744080c010b40d1500e1000b0302002c40012411034050510749041c1d07a01048980e120041c5d8141d0080004008014400717442c000c14005031044a640800e5001152000d001c501c07008850106101c41c50142060034400d100030751454001409130503123800f000e031903810001100c0620702c0c080c012000426070060000e800616114030b01039140c5015a070309443c600025071803c806588a0700ca10340c414a0402e0384400e0045580e182d00700c1420041d01c040401c035142c0300e0380000f25582c0801c2803071038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 572194802 1250 572193552 572193571
    0x40e22241803020105250e06091915080f010b160b070504050f09100b1303021908061b04060507020103110f2122020f0a030302070f0501020f0a020f0d0b 67
    0x4114076240c000d084500080180071103458041c00342560725420090318002142d44d10b00b507400070445400051040c46090b016640c00300d4041c84c408140ca0a010020b4201e492a4418079402040b030f56003959214821034440e13036070000490040c0305244141015110210400340f15032482c0c5403035503404504080c2982d002d404543c01203001c001e0f03850100300c039045654041d0780701e50f03080c20604480b9048010318061420040008540d4400121501000c5001140c0040c403d07598001c003841c06d00d03040c05060062100c14003440d40050003003094030307200304040404122054940b07460310401710b51680120000328100b64503031440c102c114800c48094440b001c22034200d42d5452401c2e80b0005010515111400c405009070000c10540c00e458414030315100403410540700d8200e00350310009003c0b034070380e41c0c00700d40c8001410b001005060780028640280c41c00c5900b9000d010b51240010380e80d502d050700e040b02055000c2d200325801030a1054220540400191101c0b1003a4915602c07400c031044c0480d040400d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 572196052 1250 572194802 572194841
    0x209070809150c03160c0206030c0708071205190c380903030915070203070b04022b02040e070503030418020c0d0f12020909041403041208040e2224 65
    0x203914045c0000ea8803009481d041c221214841d550200700b2500000b04001e00081d0301203010700030b01035200205c501c1940d100704042c45008040d8009000e03600104c0e2002d210000903650705501742d000b0782090380f40e5900310441004041d001e0a80360824607818203c0c20785040300d1191894180e44036400c3c180105040c2d80134580341e18000442c14948069074a5110500c040e00c420f010455402004075440c56070400c00c0301005030355a00218140c41c000c00da03c20f5024005101c80501c2c40b001222048501d842100c0600401e01702c04501980d9451078090706a064008200030000c1080e09042e01620452180000d801c051041500c0c60810507041102000b00e14030003042c4140b80d500c001c140602d55840f410444c05c1c518030002048a0000c014801840070090304644441c046040090ba401441c0e07501604081c1c180528002c4107a03002441228110354908000ca640c0100c5251010305070300049005600440c05501c940306202c0600703081c910395061517501802d8103811406840700039003d00d210701a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 572197302 1250 572196052 572196061
    0x503191e0b04110316150201180506060103050f01140910121a010e160507021207061d040209060906070c12060207031209200a0906140108090a0209070809150c03 71
    0x40740c00e43e020020b0721942000405041c034a4a420b606002d8488150100300003546080c016070050031900390810016001100440800c00001100d62040d6000e90f014010394440c4100307030103150760038050706405c00d001c41162a183d04002964551105007140c1e49040e40e9178840c81d94508612801080c0e0f0744211084500303249101e40f280b0f02d4010070f599030381d060080c54036194040400c40e222440700c0801900142e05015540c0d0050441c03480002601980e070003e55a203006040310200e12084044003010781c600004510b0b0610aa85202c5009410145043c50000c10041ea9a10098044a001803902e2010a00611120509150510813000140d40f1115820050540300003641c000314800e0800c1c07061400542c0505940c4401c0d80d2440d0511600314030280040d641140c0c581065608500d00751000850145203604086240000e8a03205203130b885401c51581c403540c40d0a8040c2d009405507003c035841d10303c90f440d81584504110180d9071400c0b40203094070000d40c802d50301208001c0c004410302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 572198552 1250 572197302 572197313
    0x6031e08040f03050309011701151b0b01061805031c11030f1207080a0b030c130e0f030703080f0c0f070305040b1b120a1202130b0a0302040e010902040503191e0b04 72
    0x400c1d1141c2160230071540390315042030025000a000300b480300f0000d6820142000c40b0400318182c88840e44070840074000c2d070b101d103070007042d03900100e6001070f2001040302c0c0003409007004a50107010900280d002002003100000c02d480e03907002c4072100e4045100030400260001c002002030711203000d510424242604150720010203414002c2c00d00340b003042c5488030f003800b1542d0000d80001490000d6840039050500414150014a201d580c400c000f03001d40618074543d03520120040510324826215000c060319490141d040c110402c0320005103040e0204400c1448006c810090f00b03005101e45000f03464aa00c81504034007940018605031040ca01e851000d07006a202800410300807003036201c2441c02c007494820000d22007144004554009a400203500b4007032019605040080c140d564516999418a410020b000750301174420003c1000a100001ca45052280202c03022984010018005140056111054880c02040071640408903d00c00002c120002c841985060700500b490b415914160400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 572199802 1250 572198552 572198567
    0x10090b042c0a02070b0a1b12021603091a090102100207020d150f0509030306100c0f1a10120f02090a091b0503010e0105090304060f111501080c0406031e08040f0305030901 75
    0x34006ca031401d241c010480180700b9000100105190b10704100071744210f84c801c00c000d00c2841120003820b00421020342c14190001044001c5581041c0780d115080c1140210485c94003540c2a07680c0180c1024131010f81075462600507040c0f0270f000400c019126412580e5803039824486c40d008000244c0c640c5025820010a8032400d544001c1c01c0c00954a540f40240c0040d018401180e604014030246502013024414484003064030607900103414039136141c551318102003036682204d05554019500700d01254510320f0310100b1540a5100d1102100c107d059403c00050140050001e0101c6a4030303842c590221380c140d004a90340c02c0d1510469003659040206041c250740380e842856120b07a040c0001e02040260001c120340481e5407d14000b0250814604201c401032071040140310300380700c1c1007003010824025140c1c0300d0480740e40d001250b8820a80d03c2c140400d43e036440c03201a1204082e8500035541504440140c00801d101d007240741d281c5503c030703500c600c60212503070030a5801d81d002155001180d41c10001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 572201052 1250 572199802 572199811
    0x9040c18060918030f0c21050310080d090e0405030d06090e070b040509131e06051509130305030601110f060109180c060e04020f1810090b042c0a02070b 67
    0x682092030401a140500500007030700c0310108101c581b042c01c1091000e8840407040301103074060403854605840c00002c201d0f4006035260200c1148004001407a0100000d0310360142d941901e480014526040070070040d46001841600c44e40410481885282c82c40e12400300903051540d8009800280e2082c0c60b440d0419039003040391505410403007407202e42d40d41158030f940106256070390900f81c21a403603c0403081c1591003500c642c040d0b9180310801040000c1d04414480d03625140f0840d040490b8004022840c4020b0b40d010b080001e0113000c0001103403185000710b42c442d10604001d10b0403514600c01d549001c1d0701d489940c00d690410030041c08001024000c03400515050340c00808420903988030115062280d00c20300042c400c012101c442e6030303112601500c000040d0fa000c0540c483e01050303600d140300d80390b040c400b6200c0c0c2880c140015807140140c0301c600c01c5d1624030103000d09290510700600000004130307074085506000180014441007044564078860b43c900c0d5005a00e444031450b110f042e60300040e2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 572202302 1250 572201052 572201081
    0x5070c0501050c090f10030b06040315050705031302010309061506080f09060c0406030b0109051309120201020324030c220606033308031314090403080609040c180609 73
    0x1514517a140e100305a200341d021209100e400c0c0b1108000e50041c1404041250400d0001c08c00200b0700026029030902c101c4a0181401159590311084603140320440b402c4c400200400f8070200554841e41c0003001d001c1c8070f03400c0010509000801d4100402060340054001412030003000b04440c2601852501b19010078001e200b24146181c500c0380b907004178014a005c2581d22031094015a215001c1c1d84020003024103151f032520740c552450005000500f205030303042d15001d28000001441442103a100b12164071340c1c40780900c4010001c42150031990103150741072240c4901413240d551340c40c5040311000c082c2011105490050595902540c10076070080c002d02d890100c061110302c107160139901030400d1482d001d25450b60034422015012050360005402d510021410080c8040380c403a481090b01e090034030406801407080100090f06001301c60050005410202003609410440e20242d005403052104105440e11804420714140104404200c0b2540300c8104020300c6c100d81c441e100d0601403c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 572203552 1250 572202302 572202307
    0xf0e16080106080c240729100515070b070e090f01080303010312110a0501060504140c090609030a050105070c1101230313060204030c03021c030206070c0807050105070c0501050c 78
    0x707083c0c4502619004c45d0045600103041e80440c10b41c51040003910454010711070b100d00301801c000e41120107c150700804e804c08500200d1070305451650a512680c1c644002c040380394200f009000c1051b4500c0390075040b5403418444040003c05803600c003031141c0c40c0c0e80e4607606620541010442040d5005e810042c500c143c040040c0400d48000c811030341580d07004651080401e0506500710707020402480702065901400c0408001c204040d040b040894808480600a80b11400326090010703205550f15030308203c01304116242414504060320301d0341d40003000d40391040d0080d03d80c00d082d903004175a4800003540c95600d0404102141c0301040c02c5d96820718103030754240d11301090707800704a880c500d00c5090010040002a501e00600e1100400c0c1eaa000000795182da030b42e4900010f008401d03000c00c81c800c1c0d504006c11010750f1040140101c4290b09135008040d19100c10030181c0c2e41c1e07007000c003003543c041c4400c000000108009002d0b040c0500c4965699000c5180706040003421250060806030240d07008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 572204802 1250 572203552 572203559
    0xe0624090306040f1e05060736080610051309030203090a170613020112050c1306022808030c160c031101020105060303340b130302010e030a140903010f0e16080106 72
    0x240141c2c0609581410400f415240d0b0440c100c27003a405181803203030100307040201c0503440b207444c1e480c2c1110f07a0a0100c90490b1243d01414008032040d005290300078076122140001100690402002c1c2402030065030319220007140420341d0f02e40203400c1038182010224181845c0d0000f00480c1e940200325000340c0796281c00307075800200349446000d00c04200039103038004185075400d100212a03411866000f0305129a031313585806510784886840c20321400203a122009140c00c4100d450051603944000c4451030760b89c2e1035240c03407540c0e00500341c04060282401101c0c80000c41c00501c2c2d10246000311400031030140030700c0c002829160004c203c94000c0c0c109206201354800804240a44080071800102800010800c801e925a402020181c0085554014485009481110100000e009900921243c0c401b43c848580d00d00c90702c40c2c1e40000401102003241000f101c440541002100200080340c1c480322035280c10265200c01e02d03041082e401c45881256a000843d0340c1c800100000b600a00420b0328 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 572206052 1250 572204802 572204813
    0x709140604050906061b19031407030c080a0302040f09020304060b011128080d060315051e040201051612030f060b0301050405070908010c0e0a0e0624090306040f1e 72
    0x140502000c3c0a498086034040b41c000c820006d446c00c900d080011608041c5090200107004c40700750754140d0202c9c03102c610b11a01d4000b02821109a15095203488a824180e980c44241540c0180b80740010180d0901c0b003c03907002c505420f0080248401d010250302da003000d0030020704036a400032465040c05010764410501d1139020640c001c05a944224000440000d9006502d0b104250480209554400a20800b28116561041c000d50780201c0e4035244145581055204a0f030050b50191465075520207145150b140c110101c4e40e005106140035401d00164000d0580c1031110102c00b1144204801e0000b50b101c0c5d070610404c0780c958424030041c0200303031504417004200e03c81030044a001d2a1628000340c0c510740604100c03001020010001c00c49000254130040c04401c805c94154420b90454200040340542110218040d041c0100381410250058407918014031000100f1008894140490503041d5411302c10284502d010351400c0000441a01c2c00051a480003d21010348451002c01d5402050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 572207302 1250 572206052 572206069
    0x60306070c0618060203010801020415020f03120c0f0307021c0903020f04090c1508010905060f030613022101022206081f0314030c1e12030a0b0306070914060405 71
    0x5420240005005910009840c030350400f03c0c1e03000e050700c0c0c0000000110120158024411220010581200924055022600c6805016001c1d46a60080c0440320850149150040e04034060480d12881d0103485003250460383c00844000004da0809a2400700495440d0308101204100f07181c155091800c540c001400200d9008103180513aa94000d04810000080c11490140c090251104058106c0301002003440c0001d024003014103060502050007400c1443d401c0b4003100b07005000d02025505c046012490441d0329005907401500e10081d078181c0b103200d072508108100b00f00005a503c0c82c440d98541e070b0308254640e00403421045403004006241d880321f01c1981040c0c042c0e88100b08004420f0030341a0f481c9041d0805041600c1198918820900000c01041d0075203170401503c820316055480300b4506800580420210f4008945403604601c450b0001d55000340032841c0040c41100c04000301c2d05d000b10445104001c07030f04d035503070500c0151801c6000011817a81110800e26081c00d260200310a030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 572208552 1250 572207302 572207327
    0x10206010e0c07061a0a03050d02100b0901060509180106090509010f030302071203031103130b060f030d03020901030905060f04030215070f03090305091302041409010819051903021506030607 84
    0x260b81c3c501400c5c00c43c5480c0c1200c01d0807158003d104044068503420015250000c002071a0054418a000b11303000c02003a015030603044900a203015086c0c0e01c1c04006890300d500805120b50300600c1584103204c03240f02000210301901c00395864031905070a00050001444043e0010b608100c0000401c00c0005d5000401200f0f03500440c08000f542d10007840e083d0702410481c862503410410100030000d035110fa9501c00b41c100c5016072400540d0380c4620040c0420082112481b0350103401c111001149035000e60014119144103140024010b886901c90900700390081e03508120702d11200c014001459810030910b82d841c85540401051800c00d080060706040c0d040c00400181901c4986481c145801101504c40011001d054a0342181d2844a4600254414003030f410708040504c0300d0401c0741c206110914166140c01000f40600304e0045000d0505503001d0030100c6152191844110303c02c0b101d5501b003080399110340c008080444010301021490f520090885010350304c003908002490303038054004402d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 572209802 1250 572208552 572208563
    0x1b073e181f08011e0b0f01020709050709080a0807050c01051920010510031509030c1103070f1d010501110a02010c081912060b310312030902010206010e0c07 69
    0x12401c0c010042015001950300c654019460641542038001401d2000c0e03806485801c1d080114003034070805c0004040000006900680c04000b00b0310601c0341945c00319400000c603080001585075909a558681440100200c8921602240e6041040010041054144001d090007410030f00006c0040c0d60260b5100901030800014051424a84035000d5001100200080003403100d440d2040d00782c8401d41c51407008603207030304072618034440314141e511900000951603610021104551380742d02104440d8658416454040c5032000070785506e60640100050007640415803e11440113a030139801c01e01640030078103202c0140c8880300c0000003c11052062642428210031910072410300461381c2c0114203d076503c1c0184111040c06450b048107611445407051141400a40d849e20302c07811017801417405030740000403942c8040c0d00c0c0d100403a0201c84d030214040d0381d8582072550780d00c94824401a90a0b404080b9030354018032820355906010550140040301c008402d9420710210311802c85c801d4410240a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 572211052 1250 572209802 572209831
    0x1e030e1908070c060e13020c3316090f0e0601050a090e0106020a290601110102090d03050304021e030d030b0a0503031209151b073e18 59
    0x410040d01c1c1a52085500304942045003610359401401c00e00c000034006200b031200316081051a02c2e40d0080b9913000102c81d0241c07001e0311a94070040b40351003494040da1103101001440344c90800740b020096200e8183d94550184a490140d0050481c00d0a504011256054003c1c10300c5039403d01c08090b80c0041c002c0c40c01556420090500303c59201c4207408c418042240080002500383cbd0005003c249580501c0320411141640c0c101c90004610f8010000851584900042d11075800765841540307000d403080c005460704081d400002c2c407010141400f100400c2c00481031005605202c610f05440c0b44080700d1a44101c40c80300c0001e541c490b82141000704054581e41e91003100d403248141c40b40100170180032070780c5139081040340b81512441110b0000080c4103c0403d002410001c9603400d004858070050500700ca0401100d0714407660140200741c7c1c046070f203101c150a507080031852000c601121150010907140d0b480136484500040349a01038410040b8120000100c3c003100d1090780c03ca0b60021550380e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 572212302 1250 572211052 572211103
    0x90907021c0c06090203010e0309040c03050603120306010c05030412150207050709020310030b0c0721050409380a081f0504020418050709140f1603110a1e030e 70
    0xc0140c84c1184000707405500300940b42d01c0c034090000107003a111004590502070307010444c40850444100b160610b9060740030308609121104aa4021a08240c040c5001c500c4036102c0d49a040c6941e10030b5002040002982903400140080c0244030400740b8901e0005501d02016501c82e943d0342c1142c2c0c0035860340c0070b6000003c0346e10a050394461400850b03204030040c41d14030b40380001140035009040140d0380454508104807a1407144a5583c00000e0103032203079810306041c2035200008040051814101c1c54480049203001c03180c002c030b44040c1ca81e1018a0101c0c81003c101841405500c07917116101540c401a00720050b100f160403d16402c0150102c001420303980c0d400020060080041d02c41c941d20f41101c6039105009000c24a0001c1d102c0c004824030110b6101440880143c0c01114018442d207a0700340070840750080d520300c1740a408010728004c038001c00341e050307800030365070052030458003041000791b1a1b5040a104c0400c0040410300d8101001942c00030070f404d130384844032051101d49400328140b200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 572213552 1250 572212302 572212313
    0x120c020d110718140a050105132f0702280b07080910050c160515090103091b21051c020709060905091911010f0912030203090907021c0c 60
    0x1c0b0041a9104a0701491541c10300541c0091141d900c07007980304030f40704002820301c5956001d864126400604040031403044614000c00a181d240c00300040720815894044082100c0c14450790400c0304500100d07030342c141c548100110090610403c621128150500701c001505d8408068219090400816a03c0e05c0c0c500e0301c402988a80842954444161a066600a9408000b400c115a40041100c010440d4586416a200a507101c0d555002c210209103003022403c1c007001e82040b4030b06040100e401e017060759900d80f00d29045200d101700082c660300204404c0300450a00212010b04034070906004400b03172619074031107070020280c0030000c59518a1a601c0d0b44200b0a40300100090807081086588a84040c3d014003c01d0711442c50600c1110076210303004400c540d81403d12a40702150a0740304050384015100e01080840c0107090082811001814401c0c64106400c2140310b035010f15501e0104800700261558042d201008541c0700007107258581c0f244400803000c000e51401c100d41c6030100fa103400f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 572214802 1250 572213552 572213563
    0x15050901050d060e09070905090a0204110706050a020a030c090807030206071e30090311030124030308090a0506070302030a2423031e0f0303090c01120c020d11 70
    0x3610380082c41d2600028007000c4d00c0b00000d005a0840d4142c0300720598a05000301640c41c20323901c41029411250405006141552041303046a5a0208050404d01543c40302c1c82155001c44003001442e800103040202281e0610400306103004600300301d81614104141580d440c0001d000084c080d200c0080c00c0d40c14003001051182d107129241204c10340310780d0140307002d040030583d031145050b54403114502001568049410441e80a40343d035500e0340a1850740d21a088088080c1c100c10303805550fa03e4098030112408400802c96040350000d2040c075a00e1484c00411014008000403090b402840358100003c00124503240c12010764500541c50b501e80100e114020481c20f50b5040c007000c010b0051500100f10300c44081d048860304149108801d0228249840e070b18101407005505800c040310400d0741d4080f00d002c481e265240c00b8100c0b00802c603001600c0746103920a84521209034460020001c2079a880038500c02020070b00c060601982c81c44403006561a440304500c04e05009000c0754504003508100300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 572216052 1250 572214802 572214817
    0x302040e03040509040c0302150c1c1b140c04180303090c170a0b0609070e01050711040207080721050403031d19170703030207030b041410060501030b0a1505090105 72
    0x4900d1980c1806c0ca4001c5000e442e9210803409024480484420400410192020019103201602c01c00060001c02070790108074a450f0001d2200c00519000d4072284544179008103480b42400c500c400345d403818883e01e04500880c035240300d6803c010540c08420003503501202c90036030505020038044914034000d580c20000d07800044174160b248024036402c0c02d00044050000b4011001c80707465841d624244102c01c42c2c2102c1722030100e4400c409440e80b5521800040c01c40c64003440000042040301c2000800766880640c0680704041d011500302d0510011a100e1491402c44820081e402c100306100a04640110711018041c00030500031001d4400086584141840c00204280f503004454442540c1c0003409002e035941e4488000343c0d905081500150f0f00d41543c4c1c15400924009185a03142c0301c500b04010000c40e014200080c004501b8001004664100c02c04d552020401c03909040004040301c0f618003480c2d210381c01482040102003c544800c244207625440c10b0b42e5030322a4040180c849109041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 572217302 1250 572216052 572216059
    0x4050111030d092a05030717010608070303020d0206010e060f060702010e040519062702030c040f0602030a1b0f080c0c03030705061512071203030f050f1b0406090302040e030405 78
    0x1c110301089200d2030a10a050094079018420b0a90405080e600604c94000d031900740d40189414005017000342c0040c81010b64160000c6900c940b1008100e05149030f990089000d40e01c0f81c02044140764061060a0150106441400040c40c1034000a00c2a80040700650300441d00041e40d0000e59201c0d80307000c210204003030418410f5007498024581c0f089021500c0c080e07480d2402ca00032901007a12800310041e0302c51118402c00c007c40c100b40075002540050601000c07010200400107800c0485e100c850020060368000d50b4483c007a41101415061480c0c00004903440a1035401c070000d1714405d21003080303d40080b0300303c0c0c6542e51003200c10318020754038004561506c0049030410422034006a5144225112a01006071034000b4090051508843c0703081c0030744d42c00000e03050144800d6240d913106958020301d00031452045020700070085880640c3e550805c0d03036070b0008002402c001440d40780008680d10300110302d0246010340040840c00d050000034481c41d00c1d02104e040c102c004109841c040c00005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 572218552 1250 572217302 572217311
    0x30a06211106071b0302040b03151503072106061215050705130320010f02060f06190306020a020705060a05070b0a06090c05220e150103060e090f070e04030504050111030d 75
    0x501340c16400c00440c84101c2c49917042c010404c2450034013040f00300480b0700c43d00554100c1e40b03c400c0584d05151005106a8151156550000303035050318500c84101c0940c0401c566004015904100c03042c0c41c02c940202e0403030007001c1503176400131b88103402c00c010399105602c00103101d490f4100700700c92501c85d00307441400e0010000c01c08801d101f880140395604001d00303194a88030002070401034582e400060064409170b04013000141c0e40c581c0c1d004209038080c1004040382074641040c9620041134130a0780091320080d40c04104400f041da0108503c201514040303403506d050411440c0700403c50322503220010285070325000410441e0249801240c05041d5004003480450358111000f02260170203c145103003141c40ac0e6040c15240140040c2c03400ba112900c01c0da41e140c1c1d0b13404075006024103109901354100350f036998002034401400100107000f0400b40b005000b2103044080c81514103200ca81096140f03407050410b000010360040c003103804a40302030278944510940015004c1c11401889585850399060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 572219802 1250 572218552 572218583
    0x20c1201020c1006210c0b03040f032304180207021c1a060303040303030e03090d0c050f01140301090c09180203041515091505030111030a0621110607 66
    0x190050030400c400c03401125101046952040103840c220300c1103164101c062050b445c0380b00d984004040d2401d01400c0d48000e8559100507400d8181d20884040e9203465808440e8010140d03c20354083c44000c40282000a00700e5100764040c00740b2980c400c2d0035061081d1071048183c2d8505406490000b84c0050250396415440703002060a203020310000c80741e54031040e00030503420780b0320740ea494051a030140040d4242070455909074002c221452507000a484203014440141e6503131401001e500740704003000c1031450700e8a0140003e600c03d96440078140009003e00700242c05811084d1303411140d100c4004200c4225895095a285140381c00c41007a95910504c514074600c0c8503001140568070a00000c40001c0700700b4514803c442c018498184242030002c0c00308000407144d00543c034131000c0c0c001802076079aa5040040e0840f0b0840c44000c1c0c070f804010042001c00006842403078003c2240e0003400c1c00c04c8441070baa07080c1d20f40d6026001442d65240c0000100291039180c1500e021039800301e1599403d90a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 572221052 1250 572219802 572219839
    0x120709020409110403030e0d080708030a0b010f050708220305070b090306130b0a11190206160e09011203200f07150507060506120718060807150c03020c 67
    0x42800703007a609034100240f8100d200302003012501145d4060355080b0304030701200308000d202e084040003a100c1c01828403c040101c0d0260b0021809501000380c005820101174001500300b6001085000501505103e480e0200f01d10208842d000c6604503504100e4601007205480e4020740c941018100d4800d1030b00108503c00c00d4401407001d00c80c11000c0301d00681e9907003848a80102a038000400c8051030801085508480d41c021100a1600100181c2000001015000031030403540c503200041e8410720a200743c40298409044011003945070000306900003a0108e001010103105582c1c047c0341503114041414410b9140300c054650004c8000014004507030400d60f105161104581e4a0040c400300040e04080141c00300000d00d45611030300c0c1401c54546500008100c02440107800a40050240308900024030203400074000b800c0801d0800325411424070201c1d212038200109540c0140410701c02c00d8014216048141c0091038281042003441c60202c0c04e18043e84010794215503603001101d0f5401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 572222302 1250 572221052 572221057
    0x4061701060320090a0b0c1e03031015020a150906050a051509180102160b090601060207090b0604050a0602010c14160209041115040602012a050f04030507060e1f12050612070902 78
    0x88203840021423041207540070701c1d06d03484150b070300c40a820050395080280042d80101003004500314015175440b080141c0b03a049029040c80706140b1919918400402004407501c00d0390340040b1043c030100842d240850b10b034545043c44000d003d00c13881850000402882280180200741041d680003551513002a6040f4545010380c032204580d0f421050b4009400c1400004641341242e900b6070081081ca40f0345520080200304180c0c0d20b81c1c0004080002240e1903c0c1c403555000240307240d900016100300426802440548404542c24200f201080b8a40508000311703401120300740c049410008a8070b80745020b02c01c82c40307030380c0c106600680740c0e80312024483c2514024104440198009100f800d502c1985401888035104104002112803000e1a1601c1d01c06c002819251402e40c2040340307801e4998451a2900220350b0200001800302d104a06881c10192861026a1440c2d81300a8030b02c458080041d11010b06403551906442d9036500007502a510024641310320803140f400d9035a502d4544040e0006503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 572223552 1250 572222302 572222323
    0x130b031603020921010b1c02130b060f0c1e0f0703030e0f0909100b24031e0109090c0e0903032e08060a0507110307120e040204061701060320090a0b0c 66
    0x1074070000118188604c0e2400a00e000230342c014030083c00700b1a1003004900600a0f440b060b9084501481035a1916607240002d0800c501844024030004252181000000b00b5202113212207412110b213040d14210005040c1c41541d6140c28004101804107000c2400380301441c500302c2d40405000705228654002050120149902c84014400000040d051240a141c0702c020320071011030461045040a1100c40030315040040c5450f014000380c60b229050405800a070441240a0740d070700c040c1c108011a80310010014040c3c0780303000200303107810199541c580c000203041f0603024090031200c054290006248852034006003054001c420789030300c031a44c1e41e240100d600c2c0c61004c0c50400440c0c4540e0007000802600d206083c003c5103406a03a40d1225000c01410000005100d5652200400c42e03803039002500c00340419954070742c2c1c0c103091543c1324a044001a8404014903140c005501040ca1407100c0d41081c0181c0c0d4030486507100d555602003030340c69640d58081040c10501091080680002051000c040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 572224802 1250 572223552 572223559
    0x50702070608060a03080f090d0b1e070509060a1404060f090b25150504080c150c04050d020d020319021f021c1e0203130b031603020921010b 62
    0xc060700ca8a0640e5509000d591241d0b0210b002c100420000d1081d00c01071122546080045080080080200e5103846240300b04840e4a4000005c1040b510004c040c200b0348003d2100b00d13840d650805c0e00029155128503050786000d542e0000e000c207582400351007890445185002c0c2e20350f8039541c0d200c008000c440300c83c00c4000001c09840d0001625032501090310685501c40c620102c00f0f505002c1c06628403405400110351126216481e42e0010055218051150740120005075960307280c91030040c14040b03500d04118082c4918030502014804910940b4250790007600c154049200d98000a203941c8600a8001d503d8881c61052401040a100003031b981e01d0700c26038121480c0e00e1072101e40c54030b018060010701d00590140c0d20348a249446070703a80136003524041c105480003450603812000d81ca8440298031015900010300c804c00c8000307204201004100407800e0034110704290380c0182880320514800c030700705900400c54001e559524082504000b007000101d01c1080800d403511030290441d00107040c403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 572226052 1250 572224802 572224813
    0x70c03150c0201020702031002070201090f1d06060c06040212101a010e060a08060609040b030f0a030f170a0c0516030c030f05040506120a1b03050a0e0c010909050603100906050702 79
    0x7021801402504c18007503004016010920b2412401c0c1c000307401140003a41044500e002c00a442c001c0b40491901600900460340c1281030740c805184030b14480600803034058202000441c3c406100400c400c0e0700144c2c126680d441106d50104105d2030013142e50600d409082c90030328000c0c07031040315140380c020740d101c20b80300c0503000c9824501f00806c600800040e003001c12450000900589812030081080c448000c10001da180011808a40b0f4030402d00b11744602a0310404200c402c1c19000440031002000900d0b185002c40100000c1086110340980410b644a88440300c078003d01d07000c1c1040c1d40c200d8900c500400001c00300390500601074154000c043d0b000c82c240001180360b60f48104115410390b20060606864081e21424103001c216005101140c3c4036611100b5280101e6003565600d090411076030081420f003400c038080307022030740a16106021988042000300c02a604041040112500c8180020b100e60f1200c0200741482510425880740b145007018090400109610032409600d00d0783c2200c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 572227302 1250 572226052 572226071
    0xc2a03020a05220504051218041b05042309070807030f0506060306011d03060c180306040203060408030a06030803044407020a21120203090f09060105070c0315 70
    0x1a0144010140c40c0c03d14258070710f150044002c0c1e801a58000e1712900803907030741000c990a401425005401c6d000314a158900320844d8030310f000d000d0310702d000c542015881c200c48405980904540b040388101d20300d44088901000b1090000f40c07004807010303801b40c20f11b6840c1c581844014001a41250300750702191503c86154800c031100d200341489908080c2440d890f50300d80030019202e80b1980c01c1c040842070f03030074180d58280340c0301880b030140110740041000d500c0f03203e184c544101e110702c400000c034081d034002000c010159a0000d1079036001500010555942d440310050800604203a40014004640010030300c801c0002e0307168041c800032040900030429511281d0003840300403011049900e820f06e41450320303542800d110b00404000d40f0040102040981c0c2d06c8521400084204032615a00201c0c60550180300303490078044c820000a1000c2c62074680030400150300392410040b00b50050408100058559008204035140c0f40c2d04001e8014035903981707140c451185c403400c0c7c04054400d8145400711 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 572228552 1250 572227302 572227309
    0x40b0a020a02070501200d0801080d020606132703120507030e0705120f070803121006080f22051e030f0f0306040b1003050619080d0c2a03020a05 64
    0x15450301c809640a01000740c540300044030b01c40c40c1a1100b614410100804d038071080c00c204000050301e20705032900d020340e40c90202882d0a00801007146420b64104034100812030340d4003104006091304d40b0000040c0b81c544e0f900d400c25003840401c0c03e6211a104102040c0516400485180301c41038141002e0200d542c2c0d41c5000c409403402e10b204620b00c3e13071080c4400d00c202e1606121049820701c001c01140d40c0c4118078105249044030b50360198400b41c000103503032801c01a41c4a5043e52082840c0c0741250b400e894414014000b40e03009105440703100444003c252429030005000502c2d2940400a1030705c0c0308036040c090384401109031147d031190518003a0705804400801510031010017400075038100514102c404036664001420b183c2d11a6880c00c5489869862075901c1c08004226a000034013407811105024000b0440c2d41d03031505105000c1405c00c544800041c012186207403a103040d41d050710551420301020328074100c1c803c1c0541d80c95402c80e481c9009031a07808088134001c90b443c22480d82c0d20002e2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 572229802 1250 572228552 572228557
    0x3050c0a052b022e060f1a03100315110d053c090f060108060406050109020f1c090804090c08181908040e010f14011404120f0803040308040b0a02 64
    0x140c2c100c007042c40000383e1551352181c0f00210b5070707101c02012035050f02198101d4030b094002080041c0304140c113002c400100c4141011000104400c10703e1343c204013088084460041c4001020750b0081940b82d561a1000d070003942108481012054403900f880376a140500340c11601d8148010911113001346550f041e0705542d80f90700b01c06403e040403404000c2190940840140f040c85148502e00c041d1814610411000740282010005400d543c213191600205440040c0e02c194456030040c007002e42c00c8403001c01105d024201101003400b801c07003051031800280c04a00006000350300003040006202e541e40e04080c94a4002e0760707030300d000c1d507480c4001030601403081461b0360500d501240490600f0100000c1e4001075030b0040e0100c6080c569181c2c507160f0101c200740c0010341c91140080b401c206030503501c2c61540402d1024240000800d0302c000d2042ca86005900c1022081007290b0440c0c010700041c41d0703444070800d401c28002c0b65a46080e0030041c00c4204207035011205911550009000529280309 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 572231052 1250 572229802 572229883
    0x3060b03070513080601030b04021206060619020c0909070f0603061a070201140f0a0806100206071d1e0f010507080a051c0e0a021f051603050c0a05 65
    0x9415921654411140e642040031401c0010141e1040852071080400c1540e00851144611200300e162900c1031044625444603c512542c1c001c20038800d403070307031040c05960002401d5150300c808860404022032922481e03581c41d80c0c10140b0075052020348040410f8003c2905d8000c5404c514050351514128101c466620800001d8544000c548041801d400000d124050051602441c40c1024001c46061580481080203048c03800181984102da08031581592101c0c1c1100d0145c0c0e40b200034440a5120309008000004011031140008600068480800c8241c1c4000c1d002a40200c40c000810600c040003c00c40d910070620350880701ca03a036105104a803c00383c2d201c41702a0070403440d400f0586040c2c010001d404040030358680059402c50541c0b190300e900540041c014203c50540c1d005000b0100c07580d166007459500220240035840341c00c041204c0c60300443d003038020716400365030504492030b0089180141960150705070070010311000245504924242401003003c0030295890310206004625 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 572232302 1250 572231052 572231069
    0x2120909061324050301050705041202011812050f0601050d0302070905091f0207020f010503060120030c010212100602074e060e010207020d020904171305010f0306 72
    0x1030000d511070524801010340c080207041c02041c00360502d078403400b00d00300720241c1900c051040d56040002d8902401295000651070030440d10301810005080540e611900c000b90501c140388410110303410b045c3c4000e00040c000b214003e241c140341c80c0f40036a15910303c040485c0042c860400046428505640209641e40d41a0000e02c8030500c0c105c1303080003410006007030001030301500720141d04e25208614900c2e01c3e603003050700c01640e5007094030400c0300148040354050304000044c0104202d0340d80203e9910442444e00c80303480d0000304800c014519500c5844504692940007113401e460741d00204050500902c503503903512401a03115401260b40341060b118103c1180030081c0580e07000c0d081c82200c1107040c2075003182c4018103046003c0c03181303007001840683d11119440414903402d01480384a00780070031340c4201c000c0d440c00e140e540000d445540160705c064840c68840c0301040030800c2c07891240c481001d42900403034903030000581c0180b4074142482100c1c0803d200c0030714541d805200344111000e403803514 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 572233552 1250 572232302 572232319
    0x5194706180f03060f071101060e0a060e0a051513020f0f0406080112080f0c03090a030804080c010503100b22030f0308130b07030c2303060103180827041b021209 71
    0x40c6d01c100c40443d0885241c2c0c486550f2075901003540314070b66400350b02c04c407199400811100e10740712444d40c0200740100166a202e190105006501403050180c03c40c0f45011140c441d4030401004000009105031940c212000710001b480c4552040c06c000980100c071060b0300e030100160380e2210300d8816410805001004188200009517001d2034401c068003015007020112401d000c80301003c50211b0302160800e44401c0d801060030001f5100801081c13043d81c2c2c0a01c0c005095060108a02820040901419607180408100240c8541040112a040c10912070000c400d0588c1d07800d1a00c82ca1040d40029030010b4046000113003150342c0d12041061040e4802d85030005d40c1d851000c202c2c01480c0404400e810803805903c80c2001840c07a003540780007031101d02402562800c5c103000140880c0da01c14140022450009101404142d40350207459454640003414442d40080380140405115503e0445601c2031030300c1c03588000100a65101e07a00303000030b034088802c0901c3c520802c001174040d003110650701800c030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 572234802 1250 572233552 572233561
    0x603090a1b031a0a15180906090803040b0f06060315100e060403061d070f03110406030b0717060102010e0c0f0a080105194706180f03060f 61
    0x8035400481039000c14444060019125030b0790300d1940c1c806101c901c0c1014424401c0c800b2004c2c9a00c1039204c4034003502c0120100764078003201d21b0320303c4044803588160a503949400a080c001650007541165912a200590f245060300d490a48503000b6150300300c1d120008000521241030180403240034105140c284824a80030300708010342c0c6a00c0e44140f0f420080780c404034400e641c45040141000d144100b00100340690030702c100c21100d0003840d2402c00b032507000013410440101c0c1382d0210310550b44c10500945900070048007250143c4440d40c4000c00341109042000107403644000c54080008201c02e00d1981501c8060049017030300c403460319941803600401c002d14882d180400c80f418111201501c8000e289035642c108908440d000c81e804111f19404a40f084001c80d414440c04802c1c5415158100820002d00d05c09100a03044540350400c2c1000155030080310240385440c3e09000c100100768a43e07031401000894100d000340c818030380c0941882ca1300c0f2201860701003400c41c400c890002803e4207e560307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 572236052 1250 572234802 572234813
    0x303020709290910170a0204230c0f09100f0e011d060d09080d0e1c0e041805100f15030f0b070c0c0806010f0618060f0e090f0405010501050603090a 65
    0x5050030316051113118002a038150300a2030b01c001c0d8a2881c025200008142c01400107540181351251020b102c03114007840140c402e00100ca4126500403010340d102d180401403190944a1054602d902038030b51156021985d0f0b01040380c05c448031056480014820481d4015503011501080c000c106c60a500710550b52400c014014100c18002010003090f0303148103886408465014000100c45e044d01d601101407046410081d20350075803040d80c1d4600c0080481c00004201003036410182d072156489140041d00302e0045400c002c04940c01000351280d600822212000412400300c94980f2182404035040f24542003030080000c03203030061040300001a49603140001c0c00720003041d9400344a210388240022414030003289026240d094020241541401c01704220308869134070500401c010307651500481900001800e00300d40389400e140407078290801064a18400d045201b40d00303c00d1250400590704040c42e0b030303140650b010340d00820140c1d8032401845454401110703070381e5050380001100c000151 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 572237302 1250 572236052 572236069
    0x2160201030b01020a08070c0e06101d0a03120801080c120606042004030f11062107090b0a05030109060803030906240907020a020108090120070c0f030302070929 71
    0x1441640c1e1248610707aa4400182c000587c10750b000080c0340300c1440380c1c3c0e1004040542050086035080480301c400d60707008281c451012000780480420901c6082c1980700d00007106c1c042c552190313400c2d9180820354402031050400344a8289036100e01c1c1c0360420241000c42c400e0690a006d07201801965440ea0144005000420066168141541f41d0488003441810180000d17500c60200d0f0700d00c0480a090503006e0340ca000e690707140310707420421134115a102210f0808980050890f00d20103956112401903d28a0055100c4080000c0000788035200a92240085050b100084810049a62207134011f41c0d5030701080300d0240c1542d1200d00418000030901d903000c01a0302075401141c417079100a43c00f00d4100d600c00e070344400140e80040d00c05421581c00655440d44200d0420080103035502c1100110101031168011000d03001e00002c45100307200d0030f030b4045c4010780406900b48882070743da8500299507480703030310601e240359103050892101e00c9503a40c00c00b407007407075000313814949508444104064030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 572238552 1250 572237302 572237321
    0xe030a03050315100c15060e010302090a11040618090608120318370305030a090203010b04060b0a0f0813061a15030108011a06030406050621070f06030216020103 71
    0x401c02c0003800070441ea0754400c413959500c07642d920b1042400b05445d045220b0900d01141000315030074000188400c600e8401214112a011545ca88641d122448404000c042d0001c054004440000e004540160801a0030030032848001c00c0103031a40c1e03507840310402c6440c94007400003243c00090001404902040145030412880802c40e2031641070454154901008840b104c00009859109140250174040c80820300b00090a401c0307a1b4071007541d80041a42c070000f42610005aa5a224030f0290341b400d45c0520368600d80a4410401da40c0c070780d501e032001c0d600441304910000b01003900122019102e115000d014001041017200c1c00349240e1350714009445000b445020001340c01122443e5a91042c144200060301c960000f03990b5414494030600b9a8042c0c00030201400c4022310300000703a2100002caa13031040c1c004000140c00d440c0ea10004a85407501400c1020313a8996400030003104001060400c119003c0204401d4420381e9000241c0590144905009200e42c448503a00055400781e04282080d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 572239802 1250 572238552 572238571
    0x50a050910150627180f150e150d080405100f020601181e0e0c040905030405120f070306140f07201f060e060d020d170409021209010501060e030a030503 67
    0xd504c0c1066440c0c519140303e90003005c82c2107030310720310b04202c154078801e503c94032848a40c140b08800e448201c030540c04503d4882c0c40594100c580c0020250042e102c16580560001400040c0800c80c0e818903d2a50b001401854402c481d0041507101e841e00695014101d0700064028001513881c210000c048030b02d048822840d8203450b620b000b14212070000c0019070f408018500060580180c0588a20b41507110507154000d80c0740103e89070214200005580803100101c401014038050340c56004c0c24610701e0301c041101071140b007102008119143d00111a0030565a4142c1ea031903584144201301004d0035620a40454010542c0050458046005200d541d00b1502141c400c2c240c5200302201d51200489800e4103a0780d240d1041c40f16116882510b81c003c40112072503406480940c0002e00325400010005220100198010920903104016138006024a540440d25806e00050f000700c142c80031105034801e0751800d40086244d9000c5c220400c002c4802400400f43c0c034519507070a507034903071001c0e002d0700f41c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 572241052 1250 572239802 572239847
    0x90a1205090409120806012c0d060501180e070605040311010c12090e0109020307051b1f0b0306090a0819140403060603030206070503060d0803040602070204050a0509101506 76
    0x4041d160b034001d0481540c407070500c0480c08100c20b02c0091190501400306810050385542d4803201c8062201a010b0102070161904d80100c503400c009400068500e82c001c211a081c100006002c1e4030204205101c104282d00c00e00031040070b0701034a034039544140144000b04009110a0000ca46c07480c20f04940c60106040011a152490321011b4290602150003400102100000e0041c0005908214014181c404e400d60541c01c100c9002703429401000c20380c0b070301c0070742105402d00032220803c514411400c00b59000b841d818208041e581c00b5141214215000703101e80e0740841c0d07040100060000b45290000000da041000110f03d101c680710303101007140c1c1000039100d030840307481e030050000b003000754030130200002ca80d0702d54640a0308004005010b401800740c180208122074850740c01c0001010380c4040301c0d070386c1ca83c0c0b645051402801070540107900940f506041002c00c042d9503120900030102541120341d000d84800702d08050351001d26a10309120070400082148034025070141b84020781140e000c11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 572242302 1250 572241052 572241067
    0x150209040e011b020601080a03081b0307120b060705210409020301150318240e0a0507050f06040506071506030f0507050117070203030711030d11041409090a1205 71
    0x2000d4607103812165001c0d940d9000480d00800c640110001c240000d800684001e600d401c141680307400c15803002800784008034001a040481200d0b149100c401c404000944034101220300070203400002c0c40c410030311303442d0107800300c3d2610b011020750324043d41c84401441c001c10200e0110003406101250100c078840c0512001c90214402e0014502038404100341035181c103600c15000707050352151b640702d070341c0040000512004503000000f05c0070580400d04855800c829503005003401004042800038490144446020400a001c21503500b210702c2207412043c0141c0420030860584a24412241e0061007007141000240000d0702d1141d4041ca1040f0021340d455694641c648003610210b4119130780d4010000c180025a004901f0810403603c0700b054903001c1c030b0002000b82d40d07848050020f01c1400034455144824041c200212103d45010100038401c5405000c101c900320b404c01d000d07502681c030f907400201c0c104e03082c002d100c0fa108240f03c10041c80354032a41d48030442800818805c1d0020000c08009a2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 572243552 1250 572242302 572242309
    0x40905121204021c15091b080a020112060803040302010e0d020301060e01030b0f0606070609050c1302070506010812071b0b040e010e0a0504050607030e0a02190e0106051303150209 79
    0x34440c4400300c5072044602e15192042062524041d51001240c5440c041807101040440e81511809070303190b0400030b4031100e20b041914070002450101400c1400d2400003051105000c104151554404e0b20b40d400d008580074500015104c89014150b41ca0b8020700007080598440c442200c0c080d2000340c0726215003800354010a003034896540200c5c00515030340004200704001c8601060388101400c1c072081490508800091844c40b036010081d003020349510000e000e00c4000c0c440310000d200020294540044802440806374000400a0f0307050300440f400061080790210b640b050b00103502010515145103a912486000001071601040030400c2101194040040c0b00034000703452810800c0c0c1c01b540c54940c080002480081500324950f00b0700c03041c0710010b0800107107950807194074100031408a01508405207000000074020707512404400300380c40010740000d90139042e42c05541042c01103a807140c0c1c09440030701c6484925003401c0803455042005c21891103194808150058000d071034900c404000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 572244802 1250 572243552 572243557
    0x4030606320102060403080603100c0810080606031c120c050405040b0303091806060702090406050105040e0d0903060b010908010f060f051519261e010e0604090512 72
    0x10100460040384400790800701c00c4014410000c12080035980a2040c00000d4503400060401028000a4008151036a4083c401a80601c5402d501005070f80c4444000404118050390f10210900703090202064044012070b4413807003050007070300030407103402a101401907040700c9142c2c5404109514050304130a038002e010702c0d11405900c0d91415229402c103410041194924a009ea10aa00400c006180f645401d4010000540d4104c00c820040d40c1c0c41000c11924800c000c2d00039800800001000108a101d5002c0d5060710016036042100c0700c40c0c0450303590396201031181d20300400c0291404000055803900071503c28001854601010b03135a0321111400d46900004030b43d6040d0310741c031051000481c20300d120310040c102100d035603168901001c0c25181c0d03881740d031040445241c00c281442c040c482c01071680132003d02c481c1014615070180d00031208007070380040e15541208000004034400890325070f81c16a0607200800201c040f00c2c1c0761801004018880c80c0e4044506005502d170303103568042104003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 572246052 1250 572244802 572244809
    0x903110a170c09070305090a020409110315270312101a0a03150b09130603170c0106090207020a0e0702070f06050c060c070f1e050a200406150c030504030606 69
    0x52002e2202941089500040108200300b0540f81070b080020045001522811042d01518001841011b900703003d0100c1e44420a1140c0500c11800747d141c52524a1002e035124400c41d40c2e00490181c01e5694400c4003c5080001d0100c507402071040c0042001d0b6108019040a060400031502c2d9648501030b10403c8245c55240204c0d25010429281c550303094001d05070704121207828003103217a060002c003107110b0040200746c0d40195003030101c00541c00c60355401580a10340000722101203a100c403000003887d6020903207c8905500704140003a00c420107000f40c54080350300501602d101030508050101c80c0100034800000c5106001d0000344450280390610050400ca55800350b4800e5051141d51901c600505050005101005102d002c583c4803070241400c1503020b49007090707a4641c804001c804686c020000380990142410321010081c0000d40b0100820502c522040c4c0c1c0b40d1030300d017040100c1e040380c810048060124038000008a11507800601c1c060321030b04040d8209522902c5200c115040341e007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 572247302 1250 572246052 572246099
    0x2b0219080c04050925090503060a1d01050c0717070b01030b09011d010f0c0203120103110307170106060305070806100311070f0b070e0d03050f13030f0f0b0a0605010903110a 76
    0x2103a1028003107400d901702c54003032042c180440364034035002c040b80e41c3d4030004114088031a81c90481544d81141c807490207401681c03400082c0050b0178040e5602034154040701d0115000201d100b030f480100030344001139410f225045201c61240d0781ca1610740000b9501c1c002d003099170035543e842c3d00425410200300500c0001c51850000108100b44038881001c0b21101c8a400c07055501c18040c00440045051309503055039407012500c00c00400240c003292820b841600403180e001c000c3c2c114803a400b281544135004a844943d02840315890b080000d0b0344006082d00c0041c0c1045810210304400c500a03000454800ca40c401d0705841c01c00180c0340c4034249a903105080360702030011028404500c2e400815052048070440d0806012503203650003070300610990740071800703910010075010f10b180e00815040300210f4000800d94042881c600e4518551483c1070022244040d41c1c0011403e0384600703100365000e176441a11850302c49425901c0d150070404c154000594024581314012070200807081c040c80301c0300c0019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 572248552 1250 572247302 572247331
    0x20f09090a1e020906030c0c0c031f0f020304031b0c12050606120303090307121403150112060602030d05060a030f0b04110103090309030f020310022b0219080c040509 73
    0x100b010120450002600c1074031180144009255607460b20304a07900403401c0e1405c40d6840c048201c08a090443c09035120780d05000e20700c5c02c03200004e0058441503030040c18402c01c11215000702005400c0703003c159409000128050b605500074140c41d10030f4030101d405101e4001403199210102c95211705206421a00c2c0c1c0c00004c00d024032800d01482083c0c1882c025405503085103411704641d9035030f01940d0b0015103140c08a2a0803581613006659011a843e00743c40ca0950b6480d10440a42200c810501d8403800a00c6580081118940d648140016558664003a601d492030301400f00010b420050520341d4003540d030000010000c0c0e80c1e801c90f0350340a40316800c0c01c2e400b40f42134101494110030780106a03040c142004041400240c0c462558400c1c4ea0b40841114082c21580c000310f8038120031203010094003440007031540a40600c03000201000524808214054444a0611400c0e40180c4503840900306a820a00640600500d125580449034903800c605044e552070000b04c2c0f21905550390400c0780f041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 572249802 1250 572248552 572248571
    0x60b0f0c0718243501020a030603050d0e150a020123010602060114030601030308040303380a030c05091305070b04050f061e0309160f0501030e0f060406020f09090a 72
    0x51441000040f50715582407407100d2404401c40000a540c0903a00708a10814003030340108400000035106011584e40215102d502400000d030007070506000590301840303880e8000d11198803440c548400e0300d80241a0341110031080120b21883c2c0c000100c3e180555491b4403441210301c0c0d481d04600c40304041000445580d524115010b0704290307040c0c00c0028a80041607150000e61400203650381101e5051602030060740c1c442c2002c0300148540440045d890121603114000c00189104003a180d4440425600c21640150304020110146110080c2070b4001a9030410151411120007540510480718001f00383c03040d50395003820b000342d98201c207140c07400101c1d05100d24240031100343c1e1081c8058541314035090300c40c5c821a100ea0901c0c1160f000018002000406c108021311146411040306810f031154291144d6008092213010300078180020b19103000c0000c109030005440841c040420041d00a0f41c4454482c00040e500c55070001d51191400c116108280d1540c0d03034481d00c40c11440200140c0c40c101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 572251052 1250 572249802 572249831
    0x2091006090602060103050d0807050421020a270c020f0607030c02062409190e0714040216030f05040e070203030a0b12030a120f0c0206040b0901060b0f0c0718 70
    0x407503000a011540329000510000701d0000f41c5100300c054904084500b03603200c00d001c458612075070300002d45104c4010300802c1c5000d8094003083c0c1492085681d0400191140c400007811242403002440c00280e0702c051041002541c0d00241c190139882c030554841642000b1010f141002c141c031080e000a64440e0300c04182941486600d81140c03005071380ca10808403286011220030384079100e280c8601500c8001c11031000c1042716811f02010b034020140520321516202c513898001c14031540564a902e200080014a0203100711100c198001c0030814001559403800c4819a040040760424008108400710b000807010041c18450002580215524035148400350b09031201070412138002c510006c60717110145800b0040d03c60030505840d003100d00076410031851014109031111140d40c01d00e0601035049460b40403681c503115034040d003800b5406895500d242802c8070700500c5415038500092216030101c00c51400145041483e401c1142c0103540c54804540da20f001600044078843c0c0d64480d8800c0c030b4107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 572252302 1250 572251052 572251067
    0x70c080a05161a03041101230a18052407050303280e0d030c09120317090c060301030201030e030c1c09090b1c08040806240306280902091006 62
    0x14696400c64104103000c2e1108143d40800340004151720541100b604007a4441c9400314900401c2e20304e103140d0302e044d90f051803003164040405040083c3e099a40100240f0404058000b120700c090544110360380480d100c000f6410901c0d50859010000700000b50104800b00040c40c05a008516114510007081c1c001003905a11a00d141419a0070000300441c840070100309503c1114a40c00e01182d0501000c600702e82c4c2818030340040f030700340020380014410704d60700010000c0ca8986104204c01c0c2500d8482c41203540f10213540d25181d10400c00c00061005511940010744101c1c141800c0320f06203040c44524500780b0100c0a414007150802940c04022107501840c548001c02140c00f080010000700c10200d01c401c7c000305900c1507000800b400c541c0030814081c08540041080c030b0b003a640903003000340c600e81d00604500e40305480c100788500103442e6443e01203541406041c08403030094105407108444004001c5c64030707041149a030788031585400b40e2152030000e48a069a952040006420b19178040d0030716 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 572253552 1250 572252302 572252309
    0x121501030c080f070c0b09150709120201030c12020703020609061005010207031e080d0e1b090402091503010603111e0d08070c27060509150402070c080a0516 69
    0x360821880c00003841c2c20019203504400680c010546544d81e000c1c09986801c00d103100286613504880030003140d41c0313002c10422140740c0348660340c003020384941340b04846e008518000d801230000134401c160010741c040d030b00148042c825401d0100d140f054680501c03049030800703601540940c00950070802662000c0c01880e40c00141c0b402c07044400b5040000003943c1f1429404001c107901c0c01030081c644a5007200c1407004250f68040315090341c5006007021b5002030302c5d0904400303e43c1e01c43c44d100703005a004202d21010380000f000d080c0c0813840d03585408105921601400d4a59440b410006c1803615807028020785001d14000c2e01d00c0243c1d00c40140a0262040211641c001a0b052112602d00f19030f444c450814442c40d000007003281c95100074140106040040e5000d100e48440303e10b003900c031640f01000700560030121200200f102a80c0d410900040300c0c000c454442007c8101c042d40c82c540e14107075000e0314049014640d01d00c1065259910070b49484042d180640e401d6015401c80620b100e8211440c8025 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 572254802 1250 572253552 572253557
    0x1104060c0b010b0f04051201020c06011e2405071112070501170708071d0301140406050f06240c070e09060717041e0b0c0a03140c0d02090a0b121501 65
    0x4180380e1800070305185c000ca0140320300c503881303c0c40d00440c0c40c031094050340c150301700386000d650a03940d4520560380607480f1a8280d45058140d4100001e0011080b240c274120310204480c0024058518617045803280d001d0b0101f1280c401a803c6046110f8661400308021111144000c0000c2c5041500140100481c0e6070403010b40c9011204211702c0ba94010400c4c0d820102c5801c005a0076020080b00d0030440c0c4503440c80541545c41c10302d607100d410740d0610107140a0742c05800704005a407107100b0080c07480c010403281141c204105110b0504010a050790f03074081201141d013581e00303044c086100c85007850155070000902d409a00240901d02805100c0140c0003101d6003400340101d41e01d00800c00000c580140041c00403007040842c40644100307904000040c031f82c424109121450010041c4100d900000c080c08002407415004082802440c80c146024904d084901400e0140e50203071038010b0341c801c005103038100b65036400000301c2d8120b003005898004c40404492859181c94007005118034000e200c000d04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 572256052 1250 572254802 572254807
    0x3030518010b0a0614040b030c04050909150f0603010609050a3201050f0402070510090b07030b0303040512010608030a020f01051b03040b0a0e0a1b08030310060f031104060c0b010b 79
    0x5503070fa60500c51000b1030b802400d064442940c00c10080c00503019592200c0035140c0d0020030010007a203080010000e5031021621140c140d1a20440315558800b000c0e10340c5c41542c50b00005c03442500c1b1142d1029400f0328010004582240c40310203d005450007034441545140c0c40780200c03940348251800231f01400c0131044008141c1c4030704c0003131704205100605c64207010b00d14400759561951155011182c249810004980305c0140b4081c105009001c00345040d5240b4404201040d48503200780640b40e0307030100040003142040e06020410405600c3c4061500c290f40d614500025841d0050016002006241e00070305016039441c0441401d45070000c0c4501e1070320340d0504141948600a8050340c0d0401c0d00103503145030700d41d500d5103884001c1181c0c005200c42e51017050001c03c100007003050000314000c50742c0c000e024515034581d0706594030702081d10802c081100b00710007401128400c1140740e030703001203c0c03502191564010341c04841a500640055000a4100b43c005050120f54104180109040d581051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 572257302 1250 572256052 572256071
    0x60105030c06250519050a14010c1202030907032a0f06120e10060f09060e0f04142b081024030633050702010507062301030303051801 59
    0x422600c00a400c20070761218801003d0705008003009001140e005515000e44400d001e4100303ea50380902ca2011078011162501d402c810060600030a110100603803601c0402e0440c8800c4100039400003000c0284600c520710b8000040759a00603412800318020f800d65003400c403c21a01102a0308503042806504403020341040100d0388040341801c0041380d100001020248803005908083d005145014060300b0a030012503007140c542d13501e8003101c60611040020710350300c0409001c07945c0c04031a000c40002080000601203106d030f08103032030092004010360704907035903e48107482014880f0004400e49203806800050550b0455000350308106128804205185004401c80100c54440c091051b82042110503900ca1802500840c01410a203801101020384003902c11a82001b5400c008a41200d54504602d005000d8030490f54050b0301a910607140010079198a0081d08021003622034800c1e0f680c03110705e034612002e0801c2c0c0c082d6202e5603022465041800042e0303821680e02e410b03d03045e03916010149 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 572258552 1250 572257302 572257327
    0x507080c030a050c163c0e15040e0d080402030a060c080618040f030f110712030305060109030309260d03090b01080312040b061906030516111923060105030c06 70
    0x4910f40c0c0c0300c003504c42c070303021b00442142414a0083d2649002c081c00d8503404541d41e4044000f40380b10b0040768043e01000400d100c00c0105580c2c00c804946020740040c0c07280240188181c282c180e1080c0060221441103600d56500d1081300c0d032075000180050309607018000c4500c1c24240300107541c5820031641c4078a0520b074580d08801a203150b001001d2191408582007d240202c0c800154289000280d5441942d120300c84000c981801c20203d000030b2906000076001d60043d6585016250503941e0780d04180d052182c0b80e9813484a628002c0042c0c040d04013191711240040003829400c1e00c0565000c00d05545a107441ca0b021141038001c101d0f00d800038007030081109440381c011a4055000710305038659854140200700004801c43c5816403640740e010700801c0458040d01f0132805101d6a1501200322200035104481d0310406000010403604010006800714810050400005000340d0080140842c510088084035490b01101e40700d640100300108114a07050202c40e080d071105403051403404220b076205 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 572259802 1250 572258552 572258579
    0x2060613061a03040c0b1204021512151306031104142a040b030c090f040509030d0f0603020627010504061e0e06030a0f0b030c012f06100e15030d0507080c030a050c16 73
    0xa107545410331541040c0303607030317200e400e8180b02c41401041008100d443e0b0030b185210102035041c460099060660002100c010f15030390310300c640d07052850886040008c40ca002a0000c0c042c3e10f85008440501c0041800030000b80210702950700200ca41e641ca10f0b5520500036550000b0030041d2040c2d00e490100200c494011084801501884000003144004540c01c0c40041001d41c1001c1d40015010070740340c0f81000203050110b42c4030310200624400700543e1004460070b204600483c4009114070505c2c114841c0d44459103102c0c00f0050800c03a05881c6440d01042d42c42d001110304590f410744800f03081021001e40d00c00c42e552000160042c1c00d11304003c07400070341912015030500e8026012180c191070341034540070311440302a085000765072080c1491800d0008916142c018480b01180310804030700e1050303208104101074080a00507151140918400382c400342c00494040e16402c404000c000c00740c1da42031009086824107503e4994480ba0348100f910f29040e1098148102600e040d1018046280b001aa = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 572261052 1250 572259802 572259811
    0x6031b1216020604110d021207270506010c290718050321030606070f03030911090f01090c05040506070c03050111031003080706090204050702060613061a03040c0b1204021512 77
    0x501b41c22142091010492124048082030604e01403c0c1c1c021500e080800329103040101500c0c03054041400c0a5843c40407180140c9685010074245400340f00015280101140100c0025100d01d8000b441c10400d842190b1040307071180c000401c02241c6900f842c03420b0007090003a140540c0140030072030f509480800181807d030b0716071607440c00110000f009030750740c0d9040714215680444802e03190204c42c0350140140030b080b541143c0c07410440400c03840301d0501d9011039218091503028481103920381102d0760014120340516000300f003410800130074187c41e034200410542c3d02c03411020303d40c0781ca1405d00508481c0701003410260540100244041003800701d0740541034a8101c172501da40c8845515010340100345d440070094009042c03c040110058020943d14071030a42900c10340300c0107000c041e01c2c500725003850242d0a442c90540d04098100c0b0030003005964440d02c12842e406c41a516100f0307000706500700c10a02d43c4e08040c840100000c41c204074a8040c0c0844505212504040b4054600010303448001c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 572262302 1250 572261052 572261059
    0x109180f05070b0a05071505070c150b030a050a120e010c17040909080706141006030e0c0a03050d02010c020c1c060902100504030318030c0506031b121602060411 71
    0x3903205106040c072040c2c00502c502e502c03080d0b5480c24140c015015800c0400c0a90703000c220881c0c801d004d03604600442e440348000360354402815000c1c0d80c46281480803140c1007100340741c0e100c0030400c0c103840411141c2c5420f13020328010503070b00c6494038001d2001c0c1c2e80100c0344010801200c00d0000ca13a44c10401040001e0b40c0910301540403001a00070341d40c00e000e950700410744a400c050415050003030080c0108440c40c00f800c8107018030300300305d07084540d0040c080d40c4914050090700c2c5e040142ea0701c80e610900c40391024006840031015040000385802000d504140c4c3e15400c480305001c18560240309210083c81c10340054040481c080002840340c0312507190403509140c801880104002c05a030280c041030354000e147d200d08184821000b00b0f16080750008801150303a61300c10502056660080e10100c1c0c1d80180303900f0007a8180000d2048980029010b0140c5604220403034407105d03618405880c1c8411042d90602c1c0d1031500000c540c0002640381c1343d0100b550031120600c0b01145101d42d00c030702d1465064 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 572263552 1250 572262302 572262323
    0x21e0703030e060304031103030a02090f0103050f130204110a0e0a06021c1d030f03030709050405091c020a0f0f030906233007090f140409032015010918 67
    0x303003016a065210300d2400081d43c023001040080f103100550241440c0d040580d105d011948000e80150101c400a46a98298030400000555440a140340102e485840a0004908503010003101c20054000c400003402060048155078070034241030074404005c05440c401400300101e000f02011014125070890300401c1a00302c4010328009240020801404000e003c844e0702008000c5666100d0304191601400a0000d0300006803502d8180522805288418040d1030040c2441da1f0301c01c0c0040002e0340355030950040380c48010104948841d0010520b002d080900c800c10594540105004002d81295050040800940d0007960a09036900e00710751010300001c3e0b54000c1e184c0c0b0344110140140140110a500d2005c5c881400c2031700d4441030081c10079449404000740c0300c1e45410b000c005180611040c90034036010440c02c03403a0a80004049500908200184100e08400803070f401d215404080c034103501c9503005200d00b8440f0030000707004208000e410842040403222402120350420400703002c00258 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 572264802 1250 572263552 572263561
    0x1a07170304140312070305130c140a0315050105212104090c120b0609060f030703090b2707080a0b0c130f0315020f09190e0106021e0703030e0603 64
    0x21400a0302d0035050520403240c40d045051a410440c440403546200064103240c08907101c01d41c0008500030341a40044450700070760038100031780c0c03140b101c03407110030703840380c002c1a0000105480c00041c0010312240c2d907010801d90304100602c003c0d8408403500c4504040e101d100007440d45808904c000002c01c48565500b001e10740c004184100d40269000445076610b008026550fa9402c83d64000103d50711103000e10480c0f0040c01001a07078001c105030a0b402c5101000302040f525035000040d0b80c015258200010116202d4445500b120001ca91111040888004071809000715004580b04100d20303000034a1128204440709440342d039082e000030040c00419011403510013860301a07450480c046801c0ca071030b15544540a51281c181480140e600705141c0c010808691010b008a4100480e800400c4d45482c03506400c2c400340103074103191048400741c4100041416004140a20300074400d0352300070301203d805038100e00190364040070718074502e600621080000036040080c0c41841c21080350066100d655 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 572266052 1250 572264802 572264813
    0xa020a170c090703060501112103191d0c1212070f0807120f020102030f16030b0301140105131503061512300206011802070204090c1a07170304 63
    0x1040c008580d106040b00104200950306a1007001210000d0380c91810310707000000403c3e10303846403040740c984840c17009440c1c80b914000040110781107065164400514240e074070080c4129181014440c4880480301e1070170007800d004201c08180700b541110341d12604001081600c0e03440300154902103001c2000719161051004240c3d91020050b04040303480d6503440240340c00c14409810048400200700c24401c01c0740030901c140700b42c0e846401d0404d08200640c4460000d43c440c6003130410701c42d007090780314205840d1039182030040c0d81149414110082d55541000c0400014010041c0b82c500e6a0746415249005a04e150740280300b20b90f004403000039541441c01d1800800816a044607840b0490340101c1c0c0c00708100d0580c403080d140084409001c0004044c6281c400116001800c400140d00035001403003815124504aa008913510100628000495021909880240c4016030b20451541c004101189400e0b024600d00c000074890140741039603a550354800e0100842440c5611603001c4006810000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 572267302 1250 572266052 572266063
    0x306150a39140a081b0f0a0f47090102070203060105100e0901080718061d2a0702040605030c10030f0f060905100f080d11031b0f0d020a020a17 63
    0x682054980340d441c9000301c40e01c10f071000341c00c008117200d1280b1900d02c9489840441d110780311a90145800d10002402e440f0340c2682c90302d5043c248030b29400c0c48000a01c80450607003010000315600c01a003504814180c00e0040004020003058070b90340104101c0740182e0307020580e40d040d100100c0d02c054083d4020203049400512850390141c02c014040c001050a49001841c801100c11042100d00a041d103030100800b620700c0d0344a00407000e1400000781c01c0421205a1181c0c0c0304030b4800f010607480001d2511940020445c0c00e80d103415000024501c025820140a030750003412007907008107a03410810010036140185079000c04201030341c481d0403a01d489010f402c000c2020080040600c58a034488000b0001044180c40405100384141c600041c25200b0207050411510102c025040140e000301c0107646000244001c40300c1800104000c201d208c450700c0c2105090034240000b004014400e003022494051840380310415035004120f01c40050307440608a000350740e64011141240d6140062151601c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 572268552 1250 572267302 572267323
    0x30304060c20150d0b040207200f04060909020a0801051605030c04050d06060612050601020303070e0a050a0f0e0a021c0c020f010c051c05060d06020306150a3914 71
    0x4803031403c62440f03000707084000d40f04603150030800300080c00300101000100e00c5030711801402c045040000c240d0a0610742204019400d01402030b1101c03001c00f600040c2102c205801c05080d80e640d603034924065040440c442d2016041100c000c026a0a00382a00c5414003500792030302e020081c0c00000500b40d407a8450503a001040040d00d40040b512161801001a0645005082c0003440e000303480d03031806025000b20350003200107070065440c645421200b11a01c0000e2548160401d80140f000122500c503076459000410704041c07220943b6081c01190103c55801401d8088154018001c3e64000183c1c0c0340c180d02c00120580002588060f241c0c0168101400c109002c0283c1d443c1211075220180c202005103e00b0700274902e21070165150706480d804641c41504e0640d0068160081803000071501d60080d60844001840319050071403200c8402003640c001107407040041c0d20b903503440d58011455105038210085c07140105003268485c0c0f824844820101e01c018054080d0a00c660400002c01e20252070078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 572269802 1250 572268552 572268559
    0x303090a0215070c32280308070b070e090907060f120e010c090506040812030604090c080c03060106080f0a09030306090f140703200a02030904091202060105030304060c20 75
    0x105580b4a9204081038010009240ca000007118510005c0403107089a481d200b0003c004240300001807814580454400840c1c1003c9964080301001095045020300b9120b0300c6022400b000e46043c1400034046c0c013440311464012001c1c07800b403100e02040400c3c0501654454036000b80108481e41088400f8001d10240188003442c1401e000580c22042d00300d0000005541c03204d4280f03030350b070760240310b82c522461143c07010759044074050031842c201c9180219084040144045409040c940758802e100d100c0e41e00111290340705507000c00b200c0c1002d00c81140148460b09221a491504980041c00000c000f8074451000340d81d590606c0426029070b11a50203040070800030002e003502c02401f400101140d900505158113039200041030688a805007030200710140c40788600c80030007819045840c0c0c001c41400c1007540000e200720311054849201c0c3c0300065000b02c0d00c141c0060441d6402a080180c180c2200e802038008100901c40d55401c076140907c1254003603003c1c01001c00411602d0420b11160300d41691 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 572271052 1250 572269802 572269823
    0x807020a090b0a1509060c0804030c060521040f15090c14120d2304150903021003110a2a082503020a1509020d051e0303090a021507 58
    0x1181c1e0361640c00984441e000791a14078020b602e883d8420707009030700d4558401c00213000020600042c1e00c01c4400c041258411035140b03003480c0d2a03030750b06500f9100c19000200080d01c04203004109078800042003001585600d007007203003400e050304c401d1071410b18948081d01e00c9515410640050b01c03141c4c0002c0c40c40d40c01c010740c056515290328a4450311422071004500c038864003070401d8845400440d450740b0340764540c5c544a080001c00c00c441c144c0e42c09600e4550080305400c0c40002089080406401c141c1001680d421103802d04500c1000b54a4249440000070545448041c12194210200700c980d4900c190401c45c480d82c001c503400c108081004004400d421003840120010880c1ca20050101003044515100740d6008400ca0034071600310400004c1e0050b8400102d480105040d010483c1003140707084004500042990003103a403081d9070314021107181c1d00141c29001a00d80425001807074003140c030061451414100320090759038101000c0039210704000740d030074000020007004032080d80b40e000c8603101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 572272302 1250 572271052 572271059
    0x42a03170726040501030b010203030f040f02010c050d030b012a020111010f0f050f0105031b1009150c05010e150604020c03040510030501081212151201020f0c160302100c0807020a 79
    0x1040c1c0c003d44103540c00300382040c201182560000c000c1d02e218900100d550820b643c1c46868410710804010800d81c14441c24900c06004100140302020807100c4c15180815038503240d000040c20100444804443e1401806040300080c14400c515160550240b8201e1a07026165600b180140b1116202540b071034503004c14441504a035400607440750101844c0c80c1c0a0742e0b600c4040c141c944103100c15103000d200100c820050549494060a80e1100c41441c000b044a81c4400d0f4440c4071065410398540860a103107200e50400100b4007454000554100141140b905255240a550722003c0c010a00c41c503008103250710210410400d407002000018452050300b130609002030b004040030b0044100501849000081198400702190f0700803051001002da02d40d41e1035000020312000d0801242e021034854114102c3c85800d00186c60341d903c00c0d0500c141e41c3c040800006203094903200803104941410801003015a80d10540040907035054200407005010515215065214418000390710808103400071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 572273552 1250 572272302 572272373
    0x308161407030c03210507150f110304051002042711030c2212020603040f050f0d030e061017161401030b010206040c090b010c0506042a031707 63
    0x44088034040ca943c54848120700075003000405c2290b0300800810000c001541c0043c44864112030039440c4003000140b03000d6090003000a48900c0c8489107000c500c04000c2c0310078050180b1030a01c101503006021850305140c000300c4038040108840e1445040b4040b9001b511850070358201401e10502034815a0303507440c0c810070041c95500800d600c0e00c0740381c4c0183d0039038101c102c84a0030a4260381e21f01784420142c0140f5420481d803588001c004a40002090555000203942086541c841d15007103005420240802032005048a007008442840d5500c10428009204c04080002080d04e4a4030704101c0400300601c4c11520700801c01c040c0074a1102007000004008c84a01d404402c03140c409d82c3c00740b2142c64034800481ea203c0041d503029240c0386446000b0405c0034800c2d400344100b240306051440380e00e255511194181401140c5c140c880c01c4080f0312209034500e000c034521000c030801c0c0720407105007070950b00d80d460000c180032100030849400144103002d110a03421040c8040100c216011079108082004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 572274802 1250 572273552 572273573
    0x914030304050f060c0d1a030d020f0d0c0803070f021203070f0f0804111003060e130204050f071d01030f02070507050102012009040f24030b060109030816140703 71
    0xc0d02c05000d100348081c90302d8008030704280161400c0b42082e05114469164400a0082d0500c0c1840180150f8503e6003e4074140654800000d040e0003402c0060048000d0a0824072443c1019080005a00c41d8000058001c000c1e290045000d1800c0d0348029400b010981c54451111030100107800c002c01086926603201c17107007241400042c1c1c0d82c4481c200c26108251655202580c0040c0311050b461100c1c405800c0010b46500712101a1401082881d0380e215441c1c810702003502c1c0310074104180c6401c4c0301982414050300e9000051801d030a07695180c203600090040a152804100440001060300d0050b03203e0380010611404000c4219030b14000c52030140c2e511002442154059402c0551180e0040ca807040813104001072568541d151141410800000740440011400107956818101c1c900a40c1149a54000d460243c6002442d5003036040803945071000410550400c50105024000503101100740c0b40014020340740000c42981e1454104245081480f0221451040000c00414040ad5051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 572276052 1250 572274802 572274811
    0xa090c031b1a0a020a02010c021c080414030f12090d02090109020307030e01020f0715090f12090e0411040b030f1c080a0c0507021509060d0204180e0c1309140303 71
    0x41030550b1004003200803a1030b02501c0e81220168004095440c0503501071182d10401c0c52004000a047c1e1503030420406c6100c94844003603800d05400720b41400049400b040811005c41e040f402480309945141b48617643d03504202a80400e4a00401c1045c0c054441421510002d03500900d500c0866854a17100d01c000d40080710785000080c01d1454080c0848010f100301c48079502280c0c0c0840c0741a100752a1540c0071496605151102c0c0da44041b10004a2000185c80540c507209045180d40b40c2c0741000000c100c4181a00190805101d0300d051100207981c24032401c58442c03040d070f808079040300041c00003403d00c003a4005100440c0078411507824403c0300b44105041500d015180d00c4182d0710303480e500300d0485491b1002c141c0410f204200c000054a41141600d071340b0802502c0c118030b0503034004007041c8580c0007414000c1c0071680104050040d03409900c100400c4c01c034117945c104031503005d8040c2c003507654100072040b5015014840340c16210018a802031a0b035140c015240394041d40c0c02c00031107030780c0c4d0f2f00448 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 572277302 1250 572276052 572276069
    0x1f060302100e1905010f0c14060907150f0c110303091009060f08010f211209030201080a0b090403050307110708070611030a120209010e09190e010b090a090c031b 71
    0x10382c1c00c0c150f41e11000303c80103940044e0341d507070743d504003101c0255501c42c24040d003921200d4003040d6100310072004120061040240b18042c101d41440c0503400da0002910040356030a00112800100407140e10880c0d40241d2a00070344d80c9083d911980300840d041d480303200b0126401043c2201c003140c0854000c1c414a085a010381d491040480c2600c6040340d40820030b0043c6e2105040891302005241ca002e14a2081c15400b00e4418060184c1640d07038804c0303c02c500e0a45030100c2c11f200020400e540c2c005030070b55400301d0454400e000a240110004e100710500400040621070003001280d0410f201d100040e42d60318071201103846183d00d40d001c080d0f69110f244a90300000b80070700744680000380c0100940340346141688950710f0404902c45460069040014500d0401c8001c580031440c5a4031001240d0082c0103460307041c0c0440491140c400240e8401c1e05080060f0303814011204503e031518004107602418011001a01da200d0389024103802850b0361001d4400394040c1500390b800c004102c4e000d400c503080d48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 572278552 1250 572277302 572277319
    0x1a0117010e061503120a0305070905040c020a0b0a020f07050c0a06030c0f0f1e0807020d021612151407030c020a170d1508010c02100209031f060302100e 67
    0x12509895031810580303a00d802803408540784014810b0070310100c180040c155000e00b02d500060300d02680114071001c0c002601d44c03003841003450700084c010014190a0342c0c02d1048500707451010f03640f0b20b400d080040013511400006000c045443d416100e00080380c3d82195a200800e0070101c0d501c1040d000c4940c4110504000010010300a1142c0740b000002c0d0748960b0a107142005d400e42d121915501a80144100e1302c0414540400d2411f100003d00b80c55207406a05003402e8000034a40084140170070155030158140003443c4103290f40803801c03a0080b941042c400109403600c4c880307001803103114540090030584042520b451088042d4405d0b425541c0030071610b1820501241e4455042d0009030441d222084510041050030000f00203c0340c40250203c0d42e038140085001488401d0350000322165596801d820505505026084182e240090305505103400440001d0700c0300741150014071403620001410004125a4004800664009016030b407000e4600e0340c060969800072201c1882002e24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 572279802 1250 572278552 572278589
    0x30815060d090605151818060406051807050618030c0604030302060f0c0304120509030c10020f0c0d120e010c0f03051206040e0a12090f03050304031b0e1b071a01 71
    0x3c0c12a084511070005203654821010306440b84806e400280020360010b05c0c010380007030707004410031202d8008c0c0d200c1c650010356480c0900c08421002d00c00030419080d9040070000f00702030b40d906800d4603020844800b840001230340180001c2c1c42e14054242d6a46c1050700413400005042d00441c87c54420000c0f01c900c0086580c50521742400c501c4100c070000c14041d0301ca80220f035204e01c560041e01100801408464406110500180c0140c411031010001a84400500036040005220001c07444505a070040032141d00e82d9108490319148442ea08100f0441c150814003a0b07100d82c0d940c00a01b50440d819102c04e40c21420b000380b00346e1101000104407000030000c142c041c1068030a2941c07820002016000341c410b140e454240c071000b80465081000030181c404108a0b00c2c141c4040000d500c54030003940c7d5a0314518107001c0007180c00c42184840c000f03042040200410000c84203038000c0414030350849110003540020703481e00801c2c2010301101940b0710b078180704003003407016141a690052060818a1345 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 572281052 1250 572279802 572279821
    0x20c06070309090f09062910080f0408071a01090b060c0319090503070f030b0a02090d12140309010e1b0f09041e12120b090103030815060d090605 64
    0x240e440c0040c0002c40c41c034010401c50b02260300441030400c0d51000400c1500194803090181d600b100620740144101101d5605036001c900b07822001d02e442581e8001046691000280c00b03900000d200c0400d003c64080080c3c200704409085902d880c0e400301d10700c01c0c0c884c030b444c3c0010302d40c510902510030801e1502c10780d0a150320300081900c001c880c08000842c500500e41c0404419141070f00b2598043c0501d400c4040303404e0b80c0070310280c0040c040c4c0411002e002c40ca14100200d4590018246114142c810001c0e801d039500c030044c0031031039945c11401c0c001c10030703640d24000c0342d01c400c1d1742584001c060782c04400e00c00c452030107400c0b07420500200004c40340c0c041c03455403040d40003072800d41c2a01d0303010844642e20702d03050500141195000703006e034104144090441e059a513001c00c2c958411100110f4500001c1c65284e0403030450f90700b03076541e5a010880d011031003000c5407a00307206005c0030342408100f9000038a021030f008044021076401a0800741c50b03c00d014110300181500740d004881450504000682205 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 572282302 1250 572281052 572281057
    0x312070206040b181f150b0403020a0324020304060618060602030406031a06030c210405031b0a05010606050a1d0f0609010c06020708090a06030903080402040209120609030a020c06 79
    0x783c11202811403500e4003484c02e504c3c2600c400c01ca040701c1c041d0040921007104c1001485a070340c02c20705800b085c2028016140d0806420030340000d04040401d002c1070001d40c450540b040c0547e0340c0300840f460403014a441c0000d030a942c072060741f15441e0000040200b0821250480822a00042543c1e1b241540d102000802e88080c4d010340c00c0140d0052004015131482078002c0d48440300404400030584007444045100359204803800d8400c40070028085145540c115001c1c21082c601544000c138500b029981c894692041c04809541c503201048c2d4404121001d1108918040e44040200301c0140d680034050440e41012203c80c0202e1101e001c000b803054000d540c80714190400600f1140400f02d0340040210603081940068100318a8612950015045100900d00340e03004400464840111004005150450b50082d60415007029500d030000794000c0038413500b241e4116400750311107400c50003040c4207980e654010f0485c3d10480003444030410011004150107400350b401c0d50300f041800d405105003031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 572283552 1250 572282302 572282311
    0x3801080118030806010e06180a0501021f15090f0b010f0903050c121f0207061109090604050901110412021e06040303080a02040506041418010b090d0f0605090312070206 74
    0xc1c0c0c91641000c0064414084070764401c00504200c8088005c03240480c0f102c3e0070500384191b400b0005005801e180c40c0c5003000b1002032100744010f12a4014a215403c15581510a40d0080d0350703c8905540d0510000c1c89454040e20b1000000c0026082c00c606a00c0038290f0846854041401c02891360b500c1da110b02104001d0301d420000401400b20014240440020a484100300038001d91340f80f50801441c1100103501e105004602607220801d43c01e02608031202005d41c1060020200441c0c480c0b80c0366840d142d80d0240c402c540c005082e80d600760715a400f4042850107a1030910b40040d010509110484800407018020b44007000c10050ba28070300d298807501d003c11540e1001c1c0c140000c000183c4501d402c81d078068099100507081079030744e0000c40e0098200341c106400d0410740200304800d40c1040c1044225050580840d48020f5140c00c001d48214441e515819004414440000c001c3c04414402004002e07881003080200340344c650041c540301c2d007005004210500c90100810901440080d60354005c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 572284802 1250 572283552 572283581
    0x150406120807080c0706080403020c03060403080a0203070c210806040e060606250b0a1b050f2803060e160e090901140906151e04050438010801 63
    0x5031469032289019a04061411280c1c1801005010310b207103c00d0009400400d20344e201c0c0320450a2902c0d002c0d06107000c100c00b8501030340c480d03c10400841e601081c21900300242e06401640d0340c0701d0705070071190140c040101030032428148280c501403004510714141202851f0780c0303000b0251200301c02c02040d0b80f5890a001c0c0366a101e1404180d081c5800740060034881c10710924842c840c40031801c2c01c2541d43c0d0051042d17454882403401c10502c107810b40114a20700d00c0a01d510158488c029030701509038001d03092501045c6e140450340c04100401205031030005200204041d081030b42002c1c0c001c1c058a4140222031001d1405004294416141080ca200c0d1034101d40701e48002190081c140111000000c140c7c0035150340302c803600d108603140401654001c880c40006081245801d00c0994115039955071903070700030080990154410012032030b840a003908221000300c0c01e902c07079082451915994240003c106050040b16400032509058418107804005400c49800e0303980d414250b080b00d590b00e200c4440b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 572286052 1250 572284802 572284829
    0x109180507050402032205060a050c070201020a030503091e031801090b030708061309061b0f08040204151a070203070501140316020f030a1205010f060207151b0506150406 75
    0x1403071500d130700a15407110701214881000c00c00c1c0b80000041c3d1365200c400b50f4040e0001000e100244c101405a00d500450454407189045c2d0241d0000b5619140a040901045004401304641c8401030007000840340d05800000303080818070071590380700c1d0301c020a0914408c1441c200356105500034014031303003201d002d260702ca825640c0350003082d038000300c008008651001000b105800000c50070310a1110706802040c00103040145500f810342c03003c414045660521490810080000d40d100e036086030300070390645012558002040041c100030403940c00c001c040c1d81507640440040d02c0488082e0000030b0007102203801c0160344200550700100c1034100c03506c0d01c10080000405560351045002410b410a204581c0c10380301a0800c0760440d0848400c8600040481c44070500310201f44c001c01e070240000003044201d207494a5000303551001280300d5503404001840c400b160490242a040c1c2803030804100c0114110007902e410750700e480085402c510301e000900c80b0f640003804c25104401c00d56101e00c0100c503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 572287302 1250 572286052 572286059
    0x121e0618030429040b120f1932070306140904030c0507030804061106180a02090a0b09010909031e0f11030702121e03070f230703030203030109180507 66
    0x44081d1401c99005200c0421070303143c9145560040010002800e40e120b40b65210b80c40743d000c1c001c91903000b130300e500340d095500000d08c4010302443c90b0310210360903c5100060b80205d80f000302841003020040f9607040901c7d003203040b842400c544560506c1450b450341d08102054a1302008521016410040d5070407041405c0041c000034000c0c0004010603000340200c50401d40c3d00d5643d04102d0b441900006c00040d2140400e05040c00d00304225a013007a0710841d413061440161401503555140000007912415a00c0003191480f5444e0b40304115040002d04544507940e103030300000010300440682200018991484031006600005e01c003a040704c41c0d0341e208002c034124204100c40d210902c901c0240140010001c89005a07104090082c080a078540605a2611044030f00084010000640d070500d030000c0001d580002c11000da815032135a0710a6820342e080703580a0040d080116103071000e54452044140100c241500040039504982c51000148101045201c404c14000e0304484000c01c1c80c4c4c007299090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 572288552 1250 572287302 572287319
    0x1005010f061b05011a040608010501050d06021b070b1308010504050c01080c09033007031b0303021c050105090606070203060a0c1112120105040b0f0f121e06180304 72
    0x814001c51441114080c0416580759182141c1442140190f85c11031244030300d0b41801c00d80076041c010f01d81d4034006c0046601d802d01250041c0440f650042680354001a10040d0945000040300d04031035040c103c6600ca070301e03850815240d602c580c0c104800c1c140d8807003000541d010305001e070921513a030003009882d84024407070054510034405000c0b058000801e00000490380c50130054400000a00c2035241d401d240110118038450706003000140da10313a410002c16010980120440b9184000c20580342e181c1001810b0440c001d004890500080100700314180d03009080f00e4020700e059403030031204980903489180800105100d80300c0000e4040c1c001500041e40041c07554408800c030403840c204150088415030080342484249420440500c03400b1880c860306100b0707001810701411041e14200456420350000941007980c80f909203202e80f00c070552180c0d01d900c5080c01052030005038412240320408184032030740f20b2500c00d14100300c1c40c8240000540c010503036400185840c2c01700d5024500c0c150505003c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 572289802 1250 572288552 572288567
    0x6040f0b031e040c030b0c090d0b151005030406050702070605031303180e06030d05190c06061a0310140105041502070f0b09030c0301090b0105190308071110090e0c0919171005010f06 80
    0x41642441c441c20402c0f0b4503468200821003a808a41c1e1042cec2d8900d014a0200122000501900215401030105103d40354001d01101d400c160440f041e4150503800346001c450030845602c0181b40242186030010301c250040050318050300c4100d0a450b1140040c035803c8a117806003c1c0850b000060106e0300c00b6030070b8012051407070b03950f00840021032825101c1000c800c0310101d080c05035503810000010040c21522401c8820058942c0d080d206508640b5400000c01d28011030090091464030a2000c1d0300c0305000b005068010419956401c4a2030f030380ba81c00144941081b21414020702a08400b030300c1d14a418801c07182510f07809007407030503103900341424042c18040c00070032210b000001002c044085500103018050040c07044400c40340d416200c805200101045d134074070b80184a140c10060110b4244180305940c44041011041e445101c84800101e0103550150111481d404048001c81c030703101091300400440c0c0c0040704a4440d440ca17501100212002441504643c10082c241402f05900c51401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 572291052 1250 572289802 572289811
    0x206071101020702040905031306090812030a0e06010902040f080c09130f051c030c020a02011d0616080901032007030804140105090f06010506040f0b031e040c030b0c090d0b 76
    0x5060050719130100c0c0c201c488485083c1c4240c0c0c4080380e505442074980322000060445072609204052034843d0065a5200307100b42107100b20804000181c3d9404141d11000501004c002190625652001c1d0304c0025841b40c0640c5070032500c1090086641c1000080752210420042d00b004203581d00c407150000d0610603a441201d0740c04c00c402e030308008101c00300541c401c190401c0305460120300b5146405000c5070303101d80800c01950810094040580c1c0c201d20095005550307a0710022035044550009003140c8110b508925103000d10143c4181802080c01c090080340d0030a88080104142e102c001d01c030f003144a6090207990380001c101c1400080d100e030038082e401a1250304200c180500c1b00c80c09609403030045840302d40aa01c00031488202201c20021140104815a0240d240500340a600160502c01e1302031007031040c0000001c01e041080d010607604041d4001140c104442c140761400441c50b00d40b5220607940f80b00c1541c00f240704102107404494481800501d1f021302d0010030387d50300d00b15210041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 572292302 1250 572291052 572291087
    0xc0c030d09030212040e0108060f07080601120605030a14010515130c03090804090506010306051f1b02090f100f15080604060b03090c1504120f14030d020a1b03020607 73
    0x1132040004ca40034400360026140c81403104003990b060400c1c07140740c031200030100e03203d00e180e07441408102c907040050240c02540130306e40004036502a0700c2c404050400383c0c0c0721540610440754501c051255400004d2810f090005c02800f0a0705c81e20454035103201c0c0343c01895480406e01da051180032565034048410003507039040110303500000d031700c4d550b01c950490f9024828403901c46040080304c0d039242c07280d41d0182c0422620407232000511406400d00c4400c006091081c000242d82d03c8050700e03030b07100440344110b500801d5100075103000d5800c2d6a1100054803c00d6500d40242c0c00070079110f40c0802c2c0041625001100c2c15204040c01d841160152005050ba80c1c105643c0c5a011404051400065120382807900007422035040c0c12040c00003103c1443c80140c40003600b03000500145550020300c14409401c0071020180340b40d44d0501c0881c50786900e64001d45444001129034004a07d43c0160030040c206895442a62a0a105000000008000080050f0001c000250071640182900d81d40c1c101102c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 572293552 1250 572292302 572292313
    0xb030c030d08070314010f091506120c03090f0c03120804081e0c0f0304060e0105070f0b091609151707150c1a010509090718050403170f010503060c0c030d090302 71
    0xc043c080a1f002810301c045a0070007400b034040c4034000c001c070001580e904201e6440c81d01400030410118210310031219138640507010b0540c0d10940010780315035003110b8030904110700c03841d01141d24141c1d4882298070a00c61512101003a004940345407065401c11403480c681201d1300306042d030020813100075080c202401d2185800c6060204013041000078804d004581c0c0d05e041c0300014120500d41c520141c10000100070410015200d500c102070400e500404080658407581481810120304a000c0544501220000108107801d03410050100c0324011180210549490100010b40c00c12a07000d1500d80c4045003c014070480c1002500200d04149045502900c6a541d1614054110340b552034213100b0607001400145040c00700070703800c180b2110080560700d1a0250364804060100b444121040d510740002c0d041c10301880a0304461350304074642000701d00c0e060084180300304080c01418024451100024034902d1b000e006c5401e20004480218248440348448101a044040b001c50450003032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 572294802 1250 572293552 572293571
    0x51204050f0303040614210906011707230a030218010f0603050402030d0807092c0109021905030a02040308030420101403090703080a0804110f010f050d060f0603020d0b030c030d080703 81
    0x1c1f18202d000f40080700281005503d032502580d1503030824420050300790040c0c0400c100c046045841d08202075410808004128003020000ea0038003515030000c2d400540d011501c81e19a1801c2c01080d05a504416450401c151070742070440844104540080d05a84090315510096004200ca1984503c1d1441d01e1400eaa4540600d03000d4001c501da121040300c40108505c0d40f00310b682408050246c000b45c4c8045041403558000b0440300ca1f81414507034280400000401c400040035011a030186030040800c0b65281000d02d00503001958442882d014128450642100f914200c00c8007ca401340702d6540703085081840250031207552018040c2d51941c402c0c0c0c00c00000103020040900301c201459125903034649058100402c210f080850214403600f03218a140c03515a03081031408611084920300180c58a400c203240030010020754100e440c005102c1c0d0400500154180c004011143e841c07031042c070610007a1020316540c0c500307450880b0762541105105041c05481001e503160b20104e14580800d08103030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 572296052 1250 572294802 572294857
    0x30c0b090d27090f09171e0a03020403050109080903010507141b0a0b0109150801110f030a140408090f0904020312070c0e041a09060f04060b0d051204050f0303040614 73
    0x3550740440c0b44240c0c4401c042c5e8240032032031013070042c08401c1c84102071030f140c840c0c51401d2805503d5180004c0d06403020a850003000d00c2941a1005140d0200003080703840201d040c80302044e00060b00c183d200c0d41c00d140c0080c2c0c5a0b48203d510001c4c400505501d0340c1082d0762054645440da2001070902800d10400a0600c082188030080714000d10000f0780c0092000d0800d0105101c100031600152050703810914006051403540e0221814408030f842201c0d200d032915104c90000d0922400960207110307041c010712040c03000c1c4000500c5085e1b0216035245500d1940400e0000d8410704840181d49600b04940e01000d4110900040070714034400c442046400e61070ba0400d050040050b80d040c2c410300700d41d030411080032b000b030310381c55402100807002400a8940302c1100038901a00a000510f466182c8030044c0b1181c03213005901003801d501a090307a5480b03501c0c819460941c2c1080c850148612502901012942008000c036000c0c1c80b01030350384014800e10010300381003035030004980c07280210140060410214 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 572297302 1250 572296052 572296061
    0x307030b150403050106060c1203050c071a0916030201080604050606090303040e091002070506041101050d0c0509040b0d0b010324020a02010203061e010504061809050103030c0b090d2709 82
    0x64407100903250380c00e50900e1400c64060390010b90520150700201c1002c2855802d072400111003074600841d16940b02059078069024402004051031486c0315440c515120310301400741303c0c103101e008841c2c010f04c141c2641003070401c4a00c03002e8046250400421018205030b0401540450003412076441d000d0b40d0004240b9540c0f047c0d10080c02412400140f04801d88180400951401035504c19801c140d0070b51951907d81c040034000801000030036116000d1640034030152410891902e2040003510345492010b41158409240c03584a103241420366820351920108581c10981c102c01c000d4202d13801c50340c0e00c0600a40300020403141c4119118070300082c810600041440300b4066002603140c8c14903c040c08010a1980c41c41d1101d1107240403160a1fa9074010150723030858140d46020b40c501905005051444d25854020740701803410080003005040e041341171451007074415411454540e5901c55003586030001c1001b03400020b100f00c1a0000c2c840706c1e10101400d600c078059100d44080350748484020886 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 572298552 1250 572297302 572297329
    0x503030f040609060e09060d0510051602070812030105120f0a0c0302090f190b0a0f03050a02030d020d1209020316031401110319090c210606060509150307030b 70
    0x100c0c00020180712a640c41004003004000d24145014003c001c14001190b280c07009007c14000d035404440d84e014817500f0004115080e08222041115040c100701c110303801d030700700129140076100e88000020100000a40d1841802d800300c0202c0c21030b4282001c2003003800302c59040002d944541540710394000d105000500240d84580c5000103a18038620500201810092035840110150300401c10045660038009451031140403001a88100d80c00005e512141c264016000d2188440750210030441c001034440c0101d402181124210b1482030000c990702c540881e5901c002440d00c4640c1c005100c0c1c20780207029a244001c059036007840f21251954440d07401540300f0360320841054030880c0c10340000c0c4151990884000c49903031640c94403440c190483c141245510102aa40d046400309211401d000c18000e000d1083c441c42d041c510b680c50350500d180a19400f41c898518200c00001c81501484c102c42c40c00702d000d440b1010b00c0304200d10710a42604005e11074820715031107554241d016582c12400c52040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 572299802 1250 572298552 572298577
    0xe1f0203010501110a030e09070507170705011407140a05040801020c0717190803060415151805031c1b03020106031101080f130320061b040513020310050303 69
    0x80c0d61400000424014200149040c036070132010a40c80480d034024614011082d06880d181d159889440c4110b900d881043c0b00502100c3d0a04940e070303818100000180703c080d02690080c45951900d10842c40d01c540b00b0b89100000c0750a4214189441101c40d01070990852542042800c140e5182c845c0d81c00c0e0b0303100b8440d821a98000d0b50091200302542680030040c401b00170020800d001d00100d15120f000a58100039191030404400240d00d6038403504901039100c03c0032441e50f0910354071281c0f10030700c0f03c400510b140458000903032601043c401241c0c91086400003402811102424495034003102155038010041040d811640e1011990010024010328841e60001136003034514200820000d00e05c0f820300b410030500e1800d0201c07480e41e84044039000603d2841342015a0594541620320080b150b42d481004154516080450031010845034072503500065021502d0240d2550105a44200c1c09000e51100e02150b11805d12400c40d4051980144403080d0f041c245502e410000c0d103181c02aa20000c4c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 572301052 1250 572299802 572299807
    0x20310020a1707050c0304050f04020c1501090506060306100c0f0605070509040501080d0801061107050d1a060907050f0c071e0323030405061c0501180c050c030901030e1f02 76
    0xc064035001220b55001030245040c5041c0060a05203a8032032140340310703035841294074845c0c2002907901c0d54110360f07000c4280000c4940c80e100e46036903203288005c00d111302c0260510b040300148880c101101103030310400c00108807540b60740b0f140ca402e880c44070b00c0d4402a034a0201080380306000070001d1050501036200307a102c03d0b840d00c41102c100000d58805801c4101c040d00403502d154000c5800c00384590640f042e90924011016505000d2440c201050740b200e0340c0404000d030f81e48280101107507207108000c00b00c428407801e80d50b40018412260819101800000e000704800d00c10340d980100645005031303141e4140ca102e141d40380901d00c0c22203c100c446d1802800601010410072a01604041500812000d403140d00380c4d40c407010544900640c0b05541c02440c000900f01c04004078102e1004c12170310810810460f42d619906802e10488201c4902916249024130408006001c0d60985a9910030302004501e8501c425004402803e00b030780103100b4a2152034000368454240707460884028103110030058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 572302158 1106 572301052 572301077
    0x30507080d02030a0e0c0d17040308030f0f091501151407051005070903020f0f0a1a0a02010606081314190308040b060105030906040f020310020a 64
    0xc0c021603000440001440032540a180101020700e002c2010440040c0000da071100d80d41c140541c401114034401c030005146195004021401480803814141d8a42d152070003600240c1d500c020003c0c0d89002c0181c4580106541c580c000882001450020180490081d42040602614418100b103141c804541800b0b40800081c0c0700088065a03a034952600300b182c2c232103c0d0b05410328145c0f4185008280c4e01c5108900711407e0b6174004201c0d00340344696100700501858008200c41e0095030417200025100c18101352900040ca03040c03c40d82d921880d13808024212101504000144140101804a3340340303501f1000d4900ea911012082ca881c1c00d401d00c8038a400704000807040c0c96012912400708155101000070300540c4217074922642c5881c0e9030015201030004588080b856840a00050082804402c44149103400502a64001000b0700448000e903805003c9072404918a0310100c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 572122302 572302158 := by
  have h0 := BRFrame.cov_init 572122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 572122302 ≤ n) (h2 : n < 572302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
