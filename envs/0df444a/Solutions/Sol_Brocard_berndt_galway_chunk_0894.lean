-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0894
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:32:25.134908+00:00
-- url     : https://prove2.me/submissions/b45431ef-8200-47b6-ba2a-3ed62475d468

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 160611510 ≤ n < 160791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 160612760 1250 160611510 160611523
    0x1602090f06150702060f0406180608010e071206031e05010e0109050604120e1009061107211104020a03050708090a1a0c07050a06060f090902090a02090d061b090504020c 74
    0xb400d2682c2c011500c0811075441005540701400005000d83c0c0790740d620180203001000708032100354030003106000801e00520407291a4140c4066613010303601ea8071803032400c80301c0350703c01d030528411a61b40c1c540200008102d007078003000191001d580e82d1642161801c10038212a40c00401d50f10a038506003608001030004295142d101e50404030040c980283c211041d00c01c5240c9446041d441485044081e262903008001882516201e55aa0f0712001182c252103a035802a80201d101200105c0100c0204501001c1c41c201c58a04c20414a1039900400d0301281c142c0e00f003a1000d00109403100d0402c038265901040e0f80ba4000c01e210000c040180e403944428107045400b07001407000144502c0090800d00f0054101e441156010307044910707054450030401e005184c0c034060703030408568074600002c1251a0340914420250020651b2416858800c12013000b5409401d150703800480c00440940480c0d1a445815542a01d840084154150840c801828000103400c05441240f042c04462036003980001c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 160614010 1250 160612760 160612789
    0x40f030320010c020313061d0f010509061204051203070e090a1d0604030915050906030403030b0d050102090f220b221505040204060c060513081602090f06 68
    0x7011020590940042601074002480ca810360a02c001d03403861550010003454104000c2904c0c101c030b503072109402c50303501072140e4000c034080301400000000340c9011500d64140d080141000f40c6080059000714615410580d080e241501c0160200710a1141c10722404547c0c0015941007172451405031405400c281030f2504a90140b0f0004c0c000450038482907203d80a10030f520303000f00a00180c000307465941c8240443e0101c0014040000000360009a50703444c04460242d03880391030a0940c082d080c840c8030340000780f00740c04054503801c122016403140014802110b0080c000940e40c1c1d6100c409000c502501c0f9040c482c090811003144035004884481c2841840b16030b204081641c1120b00c0000300328850004074102e540143c4a03c0303140003110341c0d000740c038210a665034410a8560b24001c10080340180d00c1034001049038184c00600045860340110740c401c0342002d100a050b1015290008281c0103520019880c0324400f14080031b625006540b0b580c0000b001c1c40c2404607140102c08942961502c185 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 160615260 1250 160614010 160614017
    0x41a0705030408130f0305010c0207060908030703050c0c0405010305030408011404030c0b040f0209090c0109140a0314030708040306050402090a06050a060c02060d1a10080106140a0302130303020304090f02040f0303 94
    0x940200c411100021325000f04110f0041c600d91036243c0c14590f000300323180c21500016115803140000e003d4003c0001400311102080550b040825503107054400d903121424a0001d80244000c1aa00360317114814a4069030003000159103540c14041941d0031220400040581101e21004120019a0000700c90101d40e50042c84030400c1c0c3c031a40b50880c04864080002540b0881103810084c00000004400000340000d0781c8006140e542c6465240c1c19034440140300b0f40103041d50b1310038000b02d070341080500309292460045030700c1c00c43c16071212400c039082a081140d415844d00f06200542c60240d203083d80001740d8071410000d00b0311f09400189100d20b00d203d001c0c2402081d4440109654400007036070b86a02c1403040c18419110f600082c281e0050b51548040c1c030800448002d102d04911804547d8103076140d1341c642c09240c0136030b890701036041e070032042d522010140c08211081c440741000c80f01e20025482070300150385403404d004500060f1400358500c200d990384180300030010501903522141c01c0740d07050f09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 160616510 1250 160615260 160615267
    0x6050d0f0302010902090a1509021608070f0b131104022a0102040b030a0b010206011d060d0c0b18010201050921070204021e0702011e0e09071e0206041a0705030408 72
    0x1070140e002d41460400030358000801070402c84042810b03001410541207101c3c080e40100e031142041000c90041c1074a01075800c41c108250000180c40100074911107000e407940c0303151649160303a0840b0241c022102e80481c03911001c4a00704002c004d810b00704694504980a60a142055850402d001244010f21b840d400c041000411543d20030741c1118050840960304607640d1402a1080b40075101a0480600500c100b50000810020741c404002d03840720000c100c044e03192901000c0141001c03441006075860b1130b079440300144402c59000184400e00f44075845504030b40b00392001908480004100d52510b801054481e05a0070900c00c002110250b14a060f5407550071600115000340a440e03d4100c0040f2241490b00040e1006c5001c0e08425100340d869600081e07080c13000c2c900d4800d0303900760340307012402d1070003075030f00d180342c03e41c8107a40c890010f103403282640704c41c90070070400d6045203000f45001d600980c09110500540180070318000b01900c807042200c0c20031000c02841c92200510190040c0c1d00032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 160617760 1250 160616510 160616513
    0x91a0a0b070b07092610020a080c130905070c0303051f030b100b04060801080706030209210a08031305060a020a08160c05030f03012328050a0b0a0f0306050d0f 70
    0x541100b400780c440600019800e1030105032001c416040d0b03c10740032140c410042644c0781b9010700c1c003c031442034000717030317946d8002303440e081400f25164000382060004186807010101c1c03065101d21607203101d10138944d02c2441e003206504024040705c40107032512250018007a0703049200c5a8106415048a034040e802d941c0940e02c59a01840981c0150000c030159900004c0000c0d0705548a09840d0590b80c942c4241c408965442500f0340491050804042e041540140c01881251509999405074401c01c030a558056140c0d03901e0101344d6004841c100c43e280003c0c078182090041c10019035504c803075010710451801800070f8016050741e100408588881241070b003480c00d0309228002588041c0d5020046a494070941401d0034a190000d0085102c0c00d540c808895800342003445840e8000d910242c0224911b03920b01c4445c1450703544d1798000c03013004d650044c000216512010900d900034410003440725140d40700f008004008120003800c140805060030350501c802c1e0307143e8440c0f0103120307800700c031010340c11006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 160619010 1250 160617760 160617767
    0xe0601112d0a05030408070e060a090504020607170d0b0103021602091e04060b10020102130603020f0f0c0105062106060f21010603050705190b0304050304050604091a0a0b070b07 78
    0x124400801a801580d160b0402c00100001078000d88688030166019251900d0119250420854009600410f40d1104100f51081c03a13011540060016001c1c0e80b85c55515201ca81c0b12039070000d4a03071048000003a01c4540b0841c240324070012084240b90a519021400515503603510700d00070003a101d030783c81d0004207160401c00300c04151040440c4880c2e0743d603480e05081c00c500519681e118a4024148610310303405c1c6500c180308482c280e90050300c4421206003024000c50094000504030b07195107c08001c0800604075210180c17803801070741000803a00b031500074184604031145002e42d1794a06406034107001a900d001c10140c0d441407003615510903909110b40042c00700e0910190b0142d803840c11015a1f90154410f4001d8025217008000310340c5075950780c1e010f0120715400484000305148030790303c0c00d00014007484000c5030000e01407030840e8109500c0b03400045840d4855400f40000030b94485540b20780443c800300a0031038040854414401e907207441c20310140fa11075075000412511020300000c205500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 160620260 1250 160619010 160619083
    0x60c02030c0d050301030618050318131d01060e0408030103080702010309080406031b091508060402131d0108160e0403030e0106120b0c030705090d0305120703060e060111 75
    0x503070449071411400000a0910f81c000c1c007003034400b18100b40086615401a8080302c2c603070741d8440f004510340008505c0c4110843c09201103a40c1c06505112150004240d90084407000c00508041c8481c4035103156040b0708403002a4010400c5004290410020441c10000d407130440f90851507807940c0d0000d62004038018000904020108803001c42c010600c141d241d48072071a81800c0e1100c118400c2c211040950340310019101d0349055141e0b0880c0e640100388a00011a004100544054144041c0c4528440e0203841d50f0800b034800780156028055402d040a066401040004040c2090314156035a5000296460007800a2013842c40045410180f00b90f001c521110f00000c0204121510380e105130018400554096a2180c040804148034015400c1280d000c3c0121ba1505440c0842d544240000d440200130182c0a0200074455040c2c0c0c02141c0308141e00c16002d5540c001009410104003440b26070014041c2ea04100001000000080c000208226140002c404400050882c402c580c3c1141c0c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 160621510 1250 160620260 160620277
    0x30312100e01030b04060515060405011805040501082a090403050a0c050a0602030703150503061302060705060705040f0603020702090109020d1d030c1504030e01080703020903011a0108060109030807060c0203 91
    0x200c031600000c1806160110305002e284100d10507c69038489090f880c43c040101d44a142c0e111008110030040383d07000e0801d20110700e010515040380240e035000010110f4800340e001210581040756000702d0fa00b030030000001c0014901424001c41c584420100b104028000c10040030300c9800162748001034090382d541d08006520108607000c036289803519101a40040d030307801700420308110740c1808450348005108180c078000b5000f45102e80d80e503544160303080c40807002030381c0042d4200003c10104e8401d000355842080b40351605955240707800d08050070b20240782d0160701090b03c14070041c4010303910841024111001d0b1080913880d240d07020b104d0030013421888070040a01381c07100b0344503c102d04007002809002d4252000d6800541202803400b00d140d00c1103034004d0010340b00195045256002d03d90864000c00185001820085c42d000860708540c4580f0030114840c00741607198045692015000c2c0d4015406c3c40c2030071065140d5550041c00703000d2860028201610cd60101c00014820001d603406071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 160622760 1250 160621510 160621529
    0x3070303110f0706090201030b1c06020a0e0a06020607080a1406010818010c0801050906090705031b04091d0d051602011103090a060c0b0901020406210908040f08060a060503031210 79
    0x10085850240010f140401c8121f000c203050000c1da2205141043c00c51700e0b108002c81c8000902d000d42c1c8d542c14025030000d9450b02c280b080c1350610749001d45404d074a01000d0a11500101540c0c1840c940160003084020a007840050030128101a00410981c141c6d410210a003440c80158131030f5007114548070302c1c00700801d000350300e0a42d6514801d54005600c5040350000c1e592100203417110303000e02810100480e1200d0118508001080380b40d412401c00201111421202a081c140c40382e203400252844c030043c0014080d0f9100105007403c00c00d0160002954450410740e10f4203a10851000068810b001c0180c107000480020000000c01401280ca0010009040078807560311040e0161103c10592010788212a841e00050b000440c144211010b0340c0d41511110701a0b0100c803000c181c80901c40140c2c880342d84d210346107040002d60b40c001520113042040101d08040d800e0a41d61460004000c1003035040b94103081d410803550318080221607800345a9208031500d50744444940c483c1c500d942d404070480 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 160624010 1250 160622760 160622767
    0x200607030c051e030a271a090a1502101b0e060408031207110102070b06040218090114120c0d06090305040e070c0201120203072007080a060605090f0903070303110f 72
    0x6140f000700c001c04200019448801a00c01d6041510301e0001a1500200d04440d50200c20f0242e0580207501c0c88020000035011881e000d1050081014800b00d9405002c0100c0e51090b4004215014054000b004215107010480d040460b0b1280c0003841207030030703000700b4002d00a00f403044070703129181244c0c00340a40c402200c0d44c442085450b088025001c54004001592a0041010701d00e01030007240c0c40b1540010382c01c1c1c0c0315111241000025404200d4405480500901c403c20741d80f212905603009100044061789000c40080c1840b01d00d4100c821800c040d90001c1000c41d0f40c0d940c908040040035038006800240482541c0741c160394500c80c0b9000004981d02100800407220b0b4400c2c09050200c0c0f003a40c2d1034200107240c5040c5d50903404151030034000700303103c2d42e030b81800692604c61f031a0442c1034142c00c54040659525500307042c1680742c0d90580c4c005865040c00d001a050401c0d106400a134003140b070100c585080700a03a9103a021b080d40041c00c2646541345003071050b2104c02510006d04001c011241e5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 160625260 1250 160624010 160624063
    0xc0a0b01080f0c010908060a0506040605090702060a0b060f0706090c0807080c0a090605030c0f030705102303011d0703060f1206060608013605090a200607030c05 71
    0x82d00c40c00ca80341c5000610074490700b0055075205200150484400304010440317a240c2c0e81d030b40c40180c00001c210385e410a544d1000002d44e039580c8080c003400740005401808042c140b0701105400d0b24003100040780130744c3e02004552820806603080f60358547c3c104200050855a42c5400d84504209502c030824600c103406010401080210f03405149940840d0051040ba60b40c04400702035070000d00c90550b1681007140c0e41022810109840c0c0d803580350090503100c10170745a000003107070303480c0c3c041d0203d0000314200342d001440c11072072002c040c6c10030100ca9200d041d0361404058402e40207507110388808414030200495503050080d0828005442c0b5548040f0541d07484441d00601c01c4c1c4145003e503545070a11100041d000c0c050181c141c10381d1a1242140354054800c10b80c50510756207244041e02c403e2040d0f840200704038251262900800c2c840014140d81182810210320301819012504800c810442c04042c643c0e40e100b08850885502d4201031000041c4d84c10510309002e09500d03500c2c150182030f121500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 160626510 1250 160625260 160625263
    0x40b060a240320030106120c020a0c120312060602010605043b1203070e0f0a06050f07080d060b0403150204061e11060a0c03110301030f03050c03130f030c1d0106050c0a0b0108 77
    0x180807d00300d03408000380315540074200da03114a030a2000d070842c0f009980074031440f0344402c07201e000c0038000d0401803020f8109103c01e1003229515800300340140d40d220024003641c0b410740685010710102144481050703407081c822014001d00c0484480c1d800041e00b10200300c0b40c5c3c0130f20034181c91410b104d0040b0388901c0e00740006040102c0540c65140f143d42c00800542c41443c0402200701510016030342d1b1406c0040324000301e40c044e4423084068803200c50501115451000600a2601605d0b40f00c8100d40c48902e14a01890500d000307980c0c0e034029500500060020983c450380c0141640c00c84026000e032800300c40703400e40d150a903421a40712a03001d080204611090344dd08190028801941c040042084e0424054441c0c00203000c010600c0742c06900080202e4031a50241c41100203000940f440e003840c4001d0714003d01805e41c0165030f5103c00c51410000e100521003c071004241d02a041003040340010840480f00e00c05000d064281301c804640320032464004c120000e101d65001c080c011407542c5800b0003a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 160627760 1250 160626510 160626527
    0x31704050a03120911060912070308070303150b0d0b060c100e060105040207030c11040b1801030c0f050d0204050405011512022b030c0302030909040b060a240320030106 74
    0x30b4000c150f00806482c1c40c20303014403943e40300607007000c040c400804281080020326030154561507400700000324040111241408014015446030000560395030403403a001d010755450780c6072103000542040d02049420a07100440f019858040750001d0030394490b2002510901803440d40b04a01d1141d1341cac0f1140c0d814802d03486512201c04841c211101c1d0380e604d4040201364030842ca00140005c40617440e038000145170711800240700c20020b002082c03c0a6942c00314000c5010411104891000000100140b00c0c41a83c5c10014000028003030307103e1800e0070f000c42e550128048009001d140c0c1c0350001014004294404182c544503c40701005d05a80c1c0da00a4061483c0740205030305c1411806c0c1a8000e0458104400c420101b8103244950706110b241c5095a4801c0c1c2e0044c103800f5400100724850300d603607400d035003140b14501c19601180c43d030800000340501c00001e43c22480e030380f03070301d85282203142a08424100400015403502050f5103040404141b006148440b02126540c40070001040c5207401c8031a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 160629010 1250 160627760 160627763
    0x31023040c15111606020a0209090f0f0307030909060605030402061b12130e0709050613080a032a03141303080406050c19200415030302060601020d030509060a0207031704050a 77
    0x101c2d0400602d603882034140091174400c0801686c0071a001384018245006010351282540c010f0b600507410344054203003800540a4071400941000800300d0030190000c0940001d0081e8079000c0003103d09101c03010b0000d205c00341c8082d110b15030114030fa40d114940004100400c4010000b642c42c80c240805a002d955002100b0020710031500010205146071581030151140c050fa65480701142e141000340041030380012001c0c100640503c60229110030100b10030144a803096440111340030702120b00305043c4411041400400306000c0014000ca83c0c02901283d82e0208110099900c60a40c030246d11043c00f150320080c0315080104e400194241c1000241004440c0f001c103803482070020784101069600003a500400458801c010800e001c803059a003c4400d0001800000c1c1150040c50701a1001e0183ea00880050f03028104001045d41d050100750450071450401f4015410100581901d5070b01c001c1944503101d9000c03850106061052046400102d004069100e69040c0f604015844040b800030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 160630260 1250 160629010 160629013
    0x6020c0a0602061902070f0b01031b080307031e170112060c02070621092001120207030804060e0304050a150f050f030a330302031023040c1511 63
    0x250040c000303c0c4581c460002c0781c0414103d690483c1e1a00003e4118510603100f06c510601600f0000301080c9a85000e18001d4800ca100c40000d007042039507950141d04035aa1980090010400194102d000c050041d000e4a0b417080b084501e500c01215550b10007107840c060a1840c40c000a800c4402041003950540160000d11404170400c106903a18071203441580005410118881444001580003181090b05144041404e034103903203c0001c0543c4000c01c1c12124000d20042c10181e40e0070a0400012036110201542014890789001c1d20620006001030003540d120580d60f204235a0a01c2142c0141500412286ca0340b44c40f40032222490900b080311b00c0201c0c00c1c140c105042d4a004030181d403180200101550325541c1c4e517100000c0544105d404005e03a00025903000707101d04c03080110b200d00980000401c09140f5103140100f51900341e00c9610503028901d02840f100d0760541c00f41c0d180d48083c0000060b000662100d1500308220b105a40c44002002e000f11122800c20780d008101c129440c00703880 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 160631510 1250 160630260 160630279
    0x12020a050a050a0902070510050c0a0e03011e110c030309060417070f1113110d15030c1a0c1506010f09080c10020109050a052a0603010308090d020a06020c 68
    0x4050211010081c060503a103c415803e0812902000b60010400b0030700c104241e40c0903802c030030154820343d10142c03140b500516002c12051b104a0f0b1040031303011a43e104078002d100500c003030347c031000007204003402c15850a40c44100b10b100400035507048440e0740c8035803800c5903075a00d440940f007500e0b00c00c142c904a41d1085030300c50446610f1003520a4828558005644c1c80f001c42c4a0703a2201c116101408009410014055081480601c544a11041104895241e0b507844c0144d400180c01c0350030b0302100d003500d016001400c0c00414600500d4406854004c07807a0311903008101c0600c18640a5132454214920484100e0a100740103880e8150150000307803a440201e100508040d45c01d28454020401d469000d43d40b1944580340c5004d03804000d20b0b29000001d1314040a450301f50502c0c42c00e92068074168843d408107810912450b07070100500082216060441e010200000c905100610001d002c6100c0883e00c0b0001c2d42d03c5020b01400340f43c0c01812400d1443d42ca07280a511040c5001c00548100d0506 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 160632760 1250 160631510 160631519
    0xf12070b07120e0303340615061110020306030a0f0c06080604180b07090306050c0909010b040303080606071505040606090c030e1203040f051002070611160204050a0b0a12020a 77
    0x1e2003e080d403264028061801c100055001c0b804040303c5942e500140144049540107a500c00d150460210f07005050215100741f940c041c021444045034400d2080216540d0000e103040400b190584a8070060f950242c0d03640c465200007880e00b41008409401c01520800c0101080784c0b5041400c00c0310310b15101c1c030004ea511b400402080311800c2d040341200b04075481061001400c0c0c02c04559000f022400d001030180e03140e480300d000b228070441c1e590071181000920803410f0715200410303a0041082195071032030503055a40050801300c000d40450700815001c0341d40c50400044c400514902c4000200400c920f26003410203e002e40000d10540044e589480980510b840c03103030040c030341d90a81d110b004040c54010700500c80400d03440101b0a8554401c14210706001501c2448200010805080c1c05600e542c240e051100844142d5040880c002c0d508020002c51040c84640000c6444d0b01200c000440340d84901c2c81c400274104034050700d075204070400004900541c0c80304c46045200c0c02520000301c1785848 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 160634010 1250 160632760 160632767
    0x204090302120d0b18010e040f081b060604060519030b0c0d090b0a0b010305060a18180c030308060303030411060912030406030c030b040506060301180906150524090f12070b0712 78
    0x203007e182d21312805a400140802c0c2c800340880185481a01114070b09400003465400e0b513000642100e055412000501c04075203000d001c2c5d00003800d821070342c40c08000300c4a03940300e810f0800c9120080c84010560002084000303640c041d2100644030755818841c050706031a107120001c0f0202d40b940f440c01d14001c2d01005135446403142ca4070908002d0a012403c50800210504034840b07030b070384003d030b158440a0f90540c00204480c0d500b552842200c810040c1c6007185409040000020643c9004e64414010080800d404a0081a01e22802c0d124035545001c5103000c5040401c941c00744a440c4d200019000a07803990542c0b00071400c0c0ca180d6001c00115411408000070356900b0384040364000b90600050103280091101d0b8140c2e5a1300ca100080c1c0d2400d541d9858003620607228a80b1030003003908800b086681408a00c4006100f00815109070322001d81045031500d0040b6803800780034101d1104941d100352140210308046858070f2040360801a0b507110402c103541d02c03607442282c2c02c500c0101071703242d403900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 160635260 1250 160634010 160634059
    0xe060a0501270207140102041701090c061115090d090501091d131e060c0302070506041e0c0b0403051515010c080904021b06150d0204090302120d0b 65
    0xc4440881014240c900844540d10020528454802d40d081003500001032000010301c800064000000d41c9991800b48803100744144212100c42a90400380b0314400a03044030b0b10681961510b081107002c030005000c6641c64101400031240d1820344001c18000050f900288011400c1c1055030790b2183c480c0c0b500011104254a8451030031242e400da00c10b0000e5079149400d855000700f0241e1392488004c844c3e2100c44a40409004030a000e0035100c04c900280009409000044030050505616000da65170324a681d686008001820b0904101c0c600c98804001489498480d600700d00c0c0c0150f40b83e10303078040444c030394464801201c00d4400c0d500514114114040810710440c1041d0340030710310150305001521402d2545504507801c0e4000c1104a4059036688050a04c140d414004440340e00c9041800900d020009030860242c00403d03400900c440e5184400810110303815203010801500524041e860302c1c140d2001c440e044000480c061a5038101c0d6405030f180c0100440300000c0304d03041d00840781e40d02c02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 160636510 1250 160635260 160635269
    0x1305100512040803150d03030603021c2f060a090f080109050d1101020d0905011406030c030309040209040204030204050c071b050616020d17090909070b16030c150e060a0501 76
    0x242400082c0100300c00714061580000d0070100124200411000600ca000e02007200b00c003c02d42d40c0000b4401d41c1084000e000340303c40384c5044800b00b100b8513201c1002d80a0725a24000c0070300040b2600d1628510350040c452a03205000e861107494544000010b400d0765054050a0310107400702800080452050060706071a81d00100038120008000705c088803864500903c92440359020070000b4880101c030f2054101150050000050394100c0101d800384200024003024441c1d0b00c0402c10026603079021046580d8030004540069860702c1c00c07030100e006401141d001a52041c0f030103040104d00d140040003044100d1050b031440c0418500361a0407140400300340201500a03006000c1540c164803080071040c14640001c10b1404010817035500d00c420035454903010040e0b00b5000c9244030032810b05140843d0001d0603c400381030380500f448000140c600600141d00d15000d4449440310078140219180300303581740c0261041007450180c81c00840a030192500d04115485124001800b011062056034141c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 160637760 1250 160636510 160636537
    0x307020604210f03030e10110f0702040605030d030c021c3005010605090406090618021c05071e0806030a0201080702031b0a06240e0703020d0213051005 67
    0x2d0400d421100c2402031114140040c080246260000c122450203d14410788030359808954261039000450524400e88005003c060402d502102103e0481043d101120602840c5c5511007800740000341c00350165510103a058005e40d060b10030215407541044a10803446d4081b29012451550045000e04010601c20005954821007505a0b140e4041d40e00329120030313801120310080d0007141c80701114803c1e401900441c000040000903400c00b4080c15000f0b0001c00b20030000c5600c0c00c0c01102040d000022001e801a1340000c4607600d0071a552041030040c900b082c0200f000e03180158002c1c003a511030720ba0413000099000d02d1070180c24450003000d4800c2501030068591030724039500541d0300010113800c4106500050000c1c2110382c400c0303c0c540c00300b03078201c000504407407040f07090050848108400e03511300c160b10640c0c000c807900c178110300300701c2154500100d42e506a903803690210024042c1e5485ca803031090000030981221700020300168240c0b0011991128146680042603a840c0b05115408100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 160639010 1250 160637760 160637767
    0x102090402310f14040b120a02030d020102070302062a0304050106140d05030a0f02010e1204031a0105030a150908040b0306040c0806010e060c1204061d0402040b1602040605040f140903070206 84
    0x6007000c0604c000510094000325a055255000a00010541c1610302c8154000803500f0298178007003248200410590000314607011803920300a46072080140140c80802000c0803642d20341d6030100c800e0f0b03c04203001c15696200e00b01842c000703018050790722408104c0d041c60703000f0a1f0180f41000c00000607a502c03e005500c1c0900d000c03825a51003825010340d0341955030302c0c5102c01c0591828000500180b0a410520350758606501e45425202c040ca04c501821349050700040c803050714002040c0d00050303007118621f5a501032424240f4080d000300800140101c402041c000f0340c00d011900a1401800101d03018071000300c42c88422510700008651440c0041c0d000040e02606040c0b040051020001e4103003075500841412040603e10380c0540c0c414400143c2e00c0c0000866078400d5485c00d11141001c5400b503143c60b01d0084e2a08080c01890305000242c401e2040c1d400031543c4a034418001404080e2045c0b0060100030111001000c52480c503d084da15410005020300b2130200c11690503da00030328440c11b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 160640260 1250 160639010 160639019
    0x90a0909020d06060f06120204030c1a0c0d08150f0105040603020904021213050601120f03110118061508150f04021305090a1208040f060e0102090402310f 68
    0x1900d252402641c00204210008001c20300e5401040090f204141d09402c000f4580400240312240c50844d6130883c910500007400044c0c05401d00c40110350b1440303a02010b06200e00c001e0b40b42c0340b142422210951040c0340d00100c3c6250003a070308505c1800d80210005000ca0f4030000d11040034141c24040c0d002501c204014000580a0350150030b4650018000500b808021000b04103800f000380ca9049518000c01a603d0403c0000c200c0c241c050f202400ca42c00000d07403c0d41e5081040748141d64001c0070700c54021144100010254010141c0140300c00003040c1e0407a0b10304064005248030340701e0078860080b1640120343e1240004056000080c94144001203030354080e000c1c03038042c40c06401240c1c41103480080c4c440ea1500350055134041e8900c2d00103800604041d00c0c10b0100454041040810712049600304404102461814040580c2140c00455601c4810004074024840e04103c141c1c41440803400c08101440030318070451400c547d02040008842d084801d565420040c4214480400389000600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 160641510 1250 160640260 160640279
    0x51503060403121e0509010603060b03070803030103060b040b09040c0602280809030f0303070e101d0f010908160e01050616060f0b0402040803191d010e0303070b0403050c06090102090a 81
    0x740681081320700c0b010360342558070041d801d0f50020b540c02d02c051307912101c0502c01d01c0712500c01d48041d000101c00401d04145003010742916070005210250403981d0b00d10a01301541c8590f0442c20030040001c0051280e840c0c1442c040700440c0060181000500c11821600c8400c0c1014400000004c1814070f000d4850f01903560b00e07450380d0b200314806605409845045e003d8610108040d40c002c94003070329021100c80e112424000111a114188000c01c0000036099404e1429611962144581500d0f14000b0710950401a11040304a0307022040c24412102c0c8040003103100d00200050b111000b02280890b42c0c1d540400ca12400341c03403005035640780c1140c0340c240051440d91000349c2680071b42e2800300d1100401c0001400700c2e045540b0621040d000090350302c110855100040810303080354142840601050320903e4440b1410281c2d260501400103500c1c03525950801c16a00e146911031810740d00751505243c01007098011411410403840f40d10007140074080c0600903141801005054848207610301250724 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 160642760 1250 160641510 160641521
    0x21819030f020619020d030c05070b062404060e010806030601080c09040606080105070c02011205070e04020a0507080a051201060212030f130c0b3103020609060c0d0305150306040312 80
    0xb240d01c40010002c4000311440ca255002d040500f0750050840852100301c09026103820000d190100903042104100180c150700c0038075001413003034881180f60b400108810400e150154840c454905002c6400155941c0c8416190550482070380c0da02065103401c0240355690710b080c010942680c10040d01c0e1456803c005901d60307131160086901141c40340d076904046003112800d88050b0005840190f0301020755800c441d64a2400044001c20455443c0043c0f00905200084051a00ca42d0300010218072081c07040c020348070041e4006800036074550080f43d01030b01951008100c03445000004000083c0240089401d6071402518110305256030b90300c84034403140780c000030001042d00103c01014000705030b5440710341002d0b003030306221141e4a01c000c106d801958103013980001e560041405210114413465150041100e90640d903160b10782602c040000c43e240142c12980314544581283c0044083e4113411017030142c2c0001ca941d0100c41c034060140f40d2190411200500400d10400d01e0142080b0f055124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 160644010 1250 160642760 160642763
    0x33011070b01120312060e040204050c0316030f1e09050d0804080a0318050f01050415020418050c04030b1603061409040b071407030206010503060106030c12020f120901021819030f 79
    0x42c1001011005d85041111215040901200c000008000440c01c09110b4580c0200c001e903403083c11071030310305064010404145400000c05458014050724450650800024100e42c40404801c1c501100c0c00040144038010007601c0034032a240c040380c0c4c400c1c012143c0da40116000198139140405448096024005a160016250f4488500c12020500c140422800003580c00000b150600303007400c0c084410300a0407450041248100020483c080c14003103c0b14100801a101054965801a00d000703503000301c6d4805000c08070010100400518031b0b02e1080420701064404200513030320b544000120318003001c0c031a5001542c1e08040350101e9202801d90794072804919060403040030988213005940c0010340d04074090b91007000184103519050004034050175076403408210030100c510000307286070740c0d605009a03010341c009046114142c0040448042d90f55100c0360790740d41d0401e008020700039880b40746080d010402121081d40b540c0360501004840f81f01f50300e0b0050b03040e41142c0ba0341e583d91520000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 160645260 1250 160644010 160644017
    0x50403080d0e0a080c1b040b01120e0c060309030703141303140124060806060918100b040314190c091a041404020109080d020d0c033011070b011203 65
    0x200c00c000100d1144c028400040460301400c050440c1c4c01c8070307210811012803c44d20072403e006002c2c1c15030740c0c048201180c1070701c0310f200841da0450411109041c5615807810b01e41200001041210b000c01c0000103000c030604c240d4828000c051103440050b000e01841000c03208108505000f00045001072000d8031000e201ca000016402800204640e07108211076441807400340d02510811a4541144540d588468191804c1c2e00c0c02c5604e00002d100500c47c100907440e43d10009011034076034040b0040c082c001d0090101401d54075500c03420000d8120560301e868180620800146908401d0321b001110121684030309040070050525460340040d01d17100501645d045140691414541d84600a0380c0d4200003411254550382868000184800341c2c9801601b2503a00407144000b40ea0b50024218485420a203001e0042144502d80ac035074070a00d01282483d5210b001554500c01d244c44141704100c001c10800400204e01e003075044500038002c005019110740c100c0d0b80104280101d001080c0780c018481e00c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 160646510 1250 160645260 160645273
    0x70f0f0f020309180a06090b03030a051b06011e060c03020c012601120201020d0503040b04110a0b0c07150201060326090303040e01050306060a030506070c030302040b121501050403080d0e 82
    0x41342c4c4085a800341d50348039442d25014015140034910840004d44150700d4280506007014001c02e580f032144901c40401c0100c0003854811014031444a0342180564500744d84495a6450007800100707020304041c030900d14444c0340025503902a1120346201580340c1c010b080c0c101408401552080c1d03030b070110362056611002c20081450300c0d80c2d034a54041d001070420124013000c1e50000a24000000c94071005002c2c0400600020a10580742c0719400f03503015030101e21003210b0b00003041d10800554041c161504c00841c60000205011a02906582100d03505440201411104030300303807030b01c0d4400580707001c1c60910080c1d4100000040510010694611185440000f00109145174080d03405100410700c800014051850140000d030340002c0222001c1507400d0440d140d42d0340300d12000d001c0c4030512004180100405000c0c1d01614024140c412045480300740d0584401400d5104030f47c0d500c10300c60305c01c1d082940c1703600800644003075039008058203003041442d132600d038000c21001001145c0c910426 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 160647760 1250 160646510 160646527
    0x22505060d0204080105010608010608040b09030f0d02070501051005010f0503090a2102060601031a040e0c090703060302030f060f06091f09060e130201022805060906040b070f0f0f0203 81
    0x480c0101800701c2048001a40c42d03203060360103404c642c0107030440320412815100400c455648003003c540c115170440c3e10f185d00c0b03441302e043d251724511407a448002044c00100350014aa001d41d80076000caa0700900007448295030b0f0a071410002100340c05000d02048980d050500b42e144034401a6512503501c1d03040b01e40e02403003a222403969900003030591801040ca1040a410701e50f06008080d000030081c20f00740200128040c42c0c400303502031421784a0049640341c50b000c16000d000c100c2c1e1411810003406aa40c0e40c181460010044c201502059001c0d21591001c50006900014001c0c850a040d03800d401940e142c020410480042c044d02c14a02303100d8542e00140c80c1e104c044801c00c000e04c6a040d000420030b10f0700310602e205400042210300044025440040940d0700407032811007805c88010080e00ea848820344900c0e40300c092000240803807042000f08205010002005070081c0d0090b00078694a03030320707690300300d510140f545001c0000a004031104024640511200717200480307140152070401408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 160649010 1250 160647760 160647769
    0x130902120307060204150806060a0c02010201140f01060306080309030307120507061b120905070312030915060303081008071208070b0702210901200c0a0e150d03022505 74
    0x140c000b80d9581c4c2e03000600b0081c446621000303d030040200d0400d40074030301d04100011802d0203808501c0302440340741c012403c21607200f94420390a81280a0740001142009034484003061008d004603004070303181c9030020800313420000544114140c0100114940328542d43d40c6e40000003501c00c0a000e000c018400400041d900d400b485011800341040070a500a4030b2100814154080075145070300c5241c0f4a20a000c15800b24903001503e80003c10001007400303014046000300700c4c09202070803251094000d1807002c4110380040702101d0203591500c09030344404400c801017034290322803040d440d0300c05001001038144569402681a00610070b44e42014496201c100103100202d401c0e10058201c0640303a0004030101d00e81c024040c120501141c104034586002804560751180b0000364068a4114402942c10400212006c41c401600d074415803030f80c42c5405412400241c6401c00c40400d8007076800d955080c030700d002c1d81d4410740641c000c114907513400c0c00c1c1030400c6c0507440401e03010030f0f54420080740d2601c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 160650260 1250 160649010 160649017
    0x20307050d021c08070507031d0a0b0d05010e010e01030b0a02120901140a0c0918060801060320040504110613081204031a010608011a0408070303080618061309021203 73
    0x1540c01802c84100c40c6180d10803c000d582038648107004da004103100b80341e98008161442547c2c541003000003840030b003d001e04090f0b249d0b80e5036a0700c885050000b00700b01010030054141d28065800602ca82d0341c07181d00c0300190b60400d0060600f6540f20b103004001007000124042c3d017100340c0660051620503441648004030404a58142d00d5030745809016142641c00d603281c0d940060107100401141c850094000c18074402481000c04102440c844200603d00c180e003c00b008126610080180c3c0790f0f030340f400d02d41c0c60401c044072014220303110015000c507003005d015452203640c1c00209480c0390f251050030080b558001f8144100d540602c00b80100f10610300b00b2481030a1850084c0f420f840ea459480d00403108200b84161030b8050901400401140350458900ea0650b40c0c030559030654903055804600c41401140c2c451882441280300001c00d064000c050cd03402040243d03580c0c034050a61180460b6aa00d0a0b50b0071345d00300e1240e4130700031419400d680c03100c03c034144020208240d9414030199a480c0d0381 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 160651510 1250 160650260 160650283
    0x3090506030f180c061b1906050906130c0605030c090904060b1e0a030b04050f010c0914030105043915030b011103030403030504061103070306060912200102030705 72
    0x48409081c40800c0e56807140c00104490f02d90010000340c6035000220741c0f54014414050084503102131034850301c25081c80038455041101141c6045d200d100d040c40000b0740b40a0366000850b0050307401107800ca8000c844058401034110b80e0101d000c0745840801c86a13640f0040c0f4090540e081400301c2401759840c81c0e01240224014900441c0c00b05000c020458411142c154690281c2c28141e10405183c030b510242d801126080118095182d4403414a5403c018848100d41d0941d40b80400800c01150403c034840309403140e45084811302d426040074107003200d07010f0b94080c2040b00d00105000128464201c00810008409510164440790700760340d12907451140c000c8400000c20500701501542d161050140071a000d10340318950740084101c564480c4000741001d0100b68503640020705000a41d0400c0f90700d4030030650040c0c1d40c1c0c900300100030300030f0078113008000004103423404c0040c2c40704240041500c0c0d80d41252000756a12001f5680c281084011411141580001c0c080740021032003d01c114444407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 160652760 1250 160651510 160651531
    0x40e13050a0c0509010623090d020a0312260a0c02010209030304060302270a06030c0903140a02040f1b03020705101104090c03050f04060b120715021c020312040309050603 75
    0x250420b020400d1a03041600024201f0462100043ca0900e0500000e15032803c005280c0765038103030444c042950f01c000002c000c2c1d04817a003400f0003c20064031603102c88100401e40c2c0c0c2e2081d12402d4203005400d403025a505c0c0c2a04800c0c0901086c0e07101815402200501c07070a0000524210032040030a0550b0065440074002c00d40c0414401143c21040440745002c01c0c00202c007405079258880011b00f460024006d1008069842c01d071010494010015000034642062070b4201040302d02856994803556000100d02544c20488510002841030054a00c08000c02c43c14000c000021001280250400a416039242c840d00980e240a0f00720340c4034101800020740c0d821740d039560500004070b06450002031044209071400040203000d21001c1c1e00d182d042a4403c0011900103142c1c2d0000d600052040c0c48051503000c4c0580003d01400600b1240e00c10070801c1c1c094900032a080ca0100c42103a91b40c2e05107a0158100b004003020b04045c82d588640d20900c01d0400d004095150404100a500110ba825440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 160654010 1250 160652760 160652783
    0x204050108030c011107080a20060a0902030d0309111003060915080d11060c030618013206040e04151e0b03010b01090e0a1e05010603110a0203040e13050a 68
    0x101042030007054445d00034440700b10310304070282c4d50760141441240c41c81300804c00a020301e2084403d4400075040c00182d50811135a060500300b195400505880f50202e2191055001c6051403e00901a8003029500071142d000d240c81c40c9814000c6040c0829410810156102030114480c0340d903201d1020200011005245000d090082c281c0ca0138a40382c485105100d920b032a182040b060000c1c0e6264082e600d0300c030f55030f1291501d0000c20700b401410486120848411000800c003d03182150407a211142a5500c401624040f03500070b03480c0440340207480e0020002c03c800d1004100181c040c13070b000f9100d0300d0100812100d5408030011a4088640329183d0401507403160304610840c00342204151b011002000b0380d00b030714800a000500e03580f240320f40043c001030019905803a00c4d4480d21a10680c0703a140c0804c030702000c0d01c0000404090081c40c011034a00750030644000e110806076a82030780c4640046213010700780302c1240d0070008020900700d502007040c000c2d540065014441c1c4a506407040c410301c2304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 160655260 1250 160654010 160654027
    0x150f0a03050f0f12030c130b0711130207030203040902091206070c05120c061501021906020304170301030b18010617010905010b0405090304090911090f04200d021c020405010803 78
    0x43c80e00298104906501401340d4880d42400c00040343e8100c1041c4403c6030b034501b000058034100484070fa21400d0011804503a810a000d0304c55070b080035200048402c50450000640300404034056440c2c0a0011f80c0140700c18000c541084e401840109001400001a92007420440746420811201d035000175007026450030400c007041000c9a0041e9541c0d041c1400c0c000301e2040300e0ba44a900528180c03020715a0300041200e43d001380451019a2000c0d603240914100c0343c14680c010350300aa030200c80c882c280c065403a2040c40b1410580f030503298031a1281540b80c41d1031001080601810300c1c50455956140e000080c902e0258140b1580c1480690010030440c00d9820010f0844508a6005000318101410882002008011030b82560455100000c03000c3d180d003003012a881d200c81c40390f41c008030000b003481511240c084900703124034031441444032a00d07220020464203020550300160080f203410740030001464030462820136003102440385e10340c08e0019000202911000e0380409840d8000060605 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 160656510 1250 160655260 160655263
    0xe0603130807120e01050a080601080a060b03010b040302190305030a0c1104020d0c0e0301090201050405220f090519080315011e11120c12030601110102070812010914150f0a03050f 79
    0x144e04580074200380781000d039a000041c240d800c00a0201d8104603c4100186110b8840c4c0e0103100500707060781502e034803903869101020030790b40b190100768800c40c0002404444805403500307030707030540f68800083c0d410400c4081c4151101c0c40414800c13948442d00e0481294161170741c1c80038000302c809000317000c60480809007025224400003403111b402641050100005030740c000044400f1a001603518078129103180382040010802c4017010590f850800d03400980000b100d40080c880b541c000c2007a60100c50b1100940340f020381c107001d001070001c0c00a1000070780c204480b0900134003092060420882c0e0340010021200950304012580c00818901042c141c40900d041100340250000007040920345145070500036504c00b2400c0a90a0b89a400030004c3e0740340e480303040d0766a2200c00c01340095403528468030340300c4c41c26003091014072400d1027000300000e901c1d00c107405541400c0380e520814248540f2602d02d0008003039040d550081d000b006088000469458140380940218014400351100460b14400d15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 160657760 1250 160656510 160656527
    0x62604050a0212010504110f06070c170d0203040e010302010e010504080a061401061d0603060127080d0801050f01030902010905180f0c07030815011b110406060207060e060313080712 80
    0xd0442d13078981400c010004143c7d5038100c2280ca0112043c9056100c4d00000800b10b01c100032004091105501f0002100012000c15041250160781524141c0700303029402c80c0c0d030340900d100300400890450010030141d40295110b0129050615095203060f440761400344c40d160003580e007140c0382640e40d011030810b500c44210840c003400581c41c200e02da51903241041013018503280c0c2d02500c122400804260181e0040c0d0340c0311000c98040c0800c05e00a849458015000600380c840c08205001d08800c01550f00e00c01c1c0f03100c0d0b0584600400e605604c1c00d41c030004500400b80148201d0510401403004102640d9140c02000380c091051403100140c030707020303550030f844810140c9224010a4140445800607400c4030849500c044050100038214203454012100e000c40068500014003001c00c41c102448104411307440003030b8041d0f5040c4041a41d400040765205914455400014010324140c00d8629100000319040031502c2d1070460f00203015154443c2a600c031440c1100d03000c80c0100c1c4081940d4002c45607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 160659010 1250 160657760 160657789
    0x11205060a1a090d050d0816090e0702150a0b0f040504170c03191e020606090a0c02010e0d09050a092307051b0d12060f062604050a02 59
    0x501040c109100440c54207001405900c40300c02008100d108070b0740c0b0000941c0d0010f01c000f0900d21003042c4904002d502c6105c0380c8140800290000c0010708082c03104100b454040d0801e0303495103112460080802094140906080d08500034a142d6140d8401d40315101406441059400039649032a1800c00c60400e0301020794030300a6050004000c00f099024031418060010341041d55030f02d04071100e8441c1140309513020400308203088408103a48541c03240140c0c0f000c071491541800a101140d00c144d0381c4400440b4940d41c06889040024941c02007a0000410301c60a4000030a4141c00c14070303076a003080b1080359400005015228204450300d07242c4c0304c1c80000e00030030004108060390340140f13415560700d502c03801842e1000800440c4040b40300c1c9044802e4000c4240f0f486c2c2c01c140c9e040d41515200c5101c1c0c109000001d43c00d24000302e241007188200421100c911508000b0b1070b00d000d8003510300050701c81481b01710310213004116883d800da1404441c460741c40b820240c40110307880d00c100078030310a10314034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 160660260 1250 160659010 160659047
    0xf0f12031d100b01050706090b1e0f1602280b061203091005070822080d1b03020c030709020a030f0207031b060e0a0302010b0405061c26040b0901 64
    0x8403500c071680120b840481c42c000e280021034405001001602ca9200d5404028006850243c1c020180400d0054250003221408010824200c122120514002050740c0000317001c290b10010034004a80010b8030140c464490040e80c80f5080d541c9280d030894002940e00d2504496411a90405c02481c18405c5070302001c1101c02807100201002e04650300c1c094440007a028410744540d00c0700366801001030390903683e803008145540318400ca16000f400c032000c29210079084520340d0041414140071039004806000c50303541c003480c900724202c48110040e031041c0660960058804240b40d54070244403e9000d441c0c1d000e03001d642d80d03401010040071103501c041b1400c02a841484440000b80d40b00341a80401031a0800d0080e0714140f074200342004210401c90034806101d490340810406406403c500800c680c1200d042003d0342d14070f0184074854096802048404155040c0800021444c182150003445141039001540e540f00701c0d00d6200c1d40c806d1308071080e200404103c0f540c0569000381c0e8046110100c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 160661510 1250 160660260 160660301
    0x80f0f040308160207050a08100e0309130b0d021507200a0b0c07090f0b010e090405031608070812041511090d05030706020406081e011a03040f0f1203 66
    0x11001014504040c082c18441d0200896584403c1d10810100000d44801000c0002c0140d80b040c1d103e54542d03040384d603002154146004685203200c081705032070b1b00200c00b0f09200781d4044081b502800801843d04110b5105820052040144c3c441b00414244002c0405416556007854281403c001d5640b404c80c20400c101a50103081607102c00000c0310884440f0881d143e02c840005030300c50700740340140d0041c0c84006d1401010340040300a981040d542d4410a894403004140701c0800c1c0205880115000b0b03240b44c0c020032020145520b013103145404c90340949001810b200b210751f00c0f43c5003540806603400600b070b070481c18401800b4116881541e00a01200104505003810601d10118018142030601c13401c4004e2945060003014011510b029500420455803262103650107000300c0020717200041e5800c912542d001103881c00e0307021a8161001c7ca00d030080d2518409000c3c80d007507400200b00300c0320454007910400020740c2800c80d02c0d0034188610001040f1402c8400c008040b1444111401004000b80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 160662760 1250 160661510 160661513
    0x60c0e090c0c1f090b09030409060509100e1b07061b020f0607081b030c030106030605150d020a031b120b061e0703020f1f0f09023d080f0f04 62
    0xd000c90b00c041a00404403028203481400d0801080d1005000c0c01d85d45803442045203506001c001032007900c090000800c400b603290000d0104020040301e0386d0320703800b040b43c1c400d02c40880754025140d848040302c41c04032181c0c3e860f02400321590301b08920855520380c440741c440d040060454404080c58402c0d10050a034200b0544405948900240011080c070586101040c031222050200388a003540c2d40c903c0c00e1307036030910f8807114525034401d2060f000000d18050b0081114030389801702c181080109900300d030401501c0c1803040000c0d84902c1e1442c0600d0b94031550001d000481c8114650310040703580b2001100703005155000103031294120b0f220b100c0c038000c00c0416400805150380b900c250310480356250b16980c4514040c2d2070607524146554403445800b58008640f0f0360742001d100f9404240344188080e850310038040d016a02030400007980010820700341528450081c80007402401c2400403480341c045149500c210100701e2546800010707076220200b0080741c84080d04640c110981694803451490f00303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 160664010 1250 160662760 160662763
    0xd0306140d020f0112020f03040b010b09221506020a050706090b2d03010e0103051c0e060901020c041e0615050306060a05090a171c020c040902030307060c0e090c0c 72
    0xe40d07100a2044108848a11542c0d02c078042540121551100840d980d1003042501202c64100311001c6a60107251000170407204503c4c1c2c107807684240044d20260200b400754117540003903961501c5084015903200840c00100140003900c0000340300540191002caa91b03030600c0347c105625900101d050000e003000402c405444901161500310001c60000c0400e41711409030180c2951041c00b00103000c0c0044000f2500340c404030b05d4181224440e5044519212100b0380e040e00c100003008a0001140300210320003903d041c000300802d00c0700c50500c1541c8901d142000001c084507141842e200c01c10701c00b4049020480303464401c83c4013910940308854040c0c0000140203040303210041800380207010108440c1740a40c01782e8140d0321840e400401c2c6030b04094032030340700145400e94100c0d8000742d8400d408520124030100e0450043d80c0966034007a104a550280a2001a2040420403a094401003003c1c5010400c580301d05071501c201d07941c0748007401c2c81348400c10416a202030800820270a003080700700c1c001c840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 160665260 1250 160664010 160664029
    0x927020a05010507020105091801051216050103050414100605040f060b0a0e1305010605030708070309030c02210106080c01090e090606040b0406080d0c150b01020601031416080d030614 81
    0xa00f407a0580d40c40303581c0d00c012a290b014844040341c10081c2807d246140004140406040c1c5005503524440e09a012101c0e6544040030091f50720700044006060002e03502ca80c100e19030040c000d5008072000c80900300102d141083c0c40300404082561884240894981030046c2030070a0301e0854140961f500f0030b40d081c4203600c07680c40d0075002c0c46480a0581d0868035210ba140000a03200081007110b980d603101c01400507802124140000ba00c8500011092802442084502174142da28814411182e50901c080900281c00300009119110f00004081109000d5000a040301002900c00340300c1c40d1002500450440d000b614000141e14100015141c00241003507114400711804500d001d08000450014034003a080104240101500f012007d5081801900740e988140c05100000003244004001c90303103c421903034010b0300300000400100d8003503a03d469029000b8800e40b08441c0403246c4200d060103043d0f0000000d50404007042482c660103104800003071141e86416015004c5810004001c42c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 160666510 1250 160665260 160665269
    0xa0302010801092c03070c051e09071e0c15060605031b0702100305070809030f070b061206070908060108070501091e090513061d0a020603130b010927020a 68
    0x56132915070498014220314002043c1441401c140c040191203042262680d101100c03c2d18a0001c0501c00610782c10804c0304460700100303030500c1d003c00a0350b4001304108518090880c00030420f4508114034941021480200800c4803030700c580d0146270340791400308444000d05007030066244ca0700300100310b980c0d0040100c0e42d11003070f0040c070403110713007100e5183c7d4600d40a04080a50030003900c100c14a07089806510950250450b41c03501d01d00d90750380904260781d82c802e121000c849600b0502c902400210110009a00820001d10100c008203196654510781003086810300c00040c100e4104009440b801c0c0710003405030061802400c02607080c080080d000c00114410b16460310b9865141c05500c0c40201140d8010b080c07000f0050001d4180000c070221165412041030300c04903c1c3c500480400c0c40100c1c011030420700c680c00903004101c4507808204d8103410081118480034528000b01000805900c49036004c0d04602c0800115a03441010007181034482c10200c01890040440b070001603a01c8040c042c0464 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 160667760 1250 160666510 160666529
    0x2100509010b2e0c0f2001080a060b0f0d06050402030406240e010b030a1b0302091306050a05061c020307170703090308041506051e0f010503101203110d0f09050a0302010801 76
    0x594130314160710083d4045d00003900d00790a81700111803001c050f2a2000c5828000d80e03500305a61038403040301c0d00715031035445001d80e4000104200b205000500c0301606400030307c8140042d003540e40b20046410307070707101702da04131501980c44802c904494090380c0c040c10203802020000841c4c908140010807001070602884147c000040300180e00c00346c203901b200d0742c000d082c00d100740c4501002400203000380d00180c800314450300380a06020904000c41c0700d0300045903802403820201e1072901091001590101d00c1003000314440d4040060b81a01500003140103501d2035841c1c4042d0b2916400d56148800d019000404141c107110451b0040303a40030595607003250f0014a0034001d0400300c0c42110003000346520081c2c011000e403291078001c03c9010140d0050f00c20035201608074a1641c001103c140c403003103030b041011401410050042102c40c3c003007032202d80d00c03a00780786c080300d410609041d113400303c250282c0380040c200070308440302c480e4410000401000e02340c440555036811580040c0c45184140030b0782050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 160669010 1250 160667760 160667777
    0x2d030f0f12030f0103020d290108060127020a02071203090303180303022109030708030d1b140c01020409050c1c020c0d03021e03040318050a0b040306020a02100509010b2e 75
    0x1400542d1061708e101c4599000104054088030040d01149a824403e0030042d000b0200006190310641107050000340c1178014200340e400e90107503580e0083d04a0031001045104140010410384940c0304062500c41c000d4640c00601851840d00603c420350300c00741d008800321412020000640c00040c1000c4401507011800e92140302444412901d004112402d0343c1071241d200c00058490707001c4010802c0c40034690090160501d0a0340080c0b4494015011320b0009000f42c2d00c90b40e6155102c0c01500d412044807001515080e561001c0106407401980d000390035000002d560000c401070113200044090032084258207103101c41206907201d0681c002075005043d0005840d100d466075034017a1a40350320323008001c41c0e12810503080040c031000a00d81220702400541c1000b18007442d1110075441203030041c1c1c0000f0718150455440700080e41040c4270003000c0d440381d420010300d13200701405601e21840f4190000100390f03400100300201034884030b16000c944007000070445880c001c0340303c000d2411070850400100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 160670260 1250 160669010 160669013
    0x3060e01090207021212070506060301140f0703200405210c061b010c0201140106020705060720090411130510030209040c03080f0403120e2d030f0f12030f0103020d 72
    0x7030302035962461002074004c07440071440c00761754a006086464008e038225900c42e62058245802c07075400d401e5841340c410780c0380c0004018001d02a191580154149004034940c030611120081c5542c60482c0c40489002c00716081c800742c24030b21126104c402d500780170304840740703001100b490b1690040c04106014140004010036070901c3c5804202d40c009045008001042e46100000e00804082040c00b0100e0412000000c506e440000e020081d913400400c180d1814030760307994081c070381694000000050481070280c0409540c500030000d1040e405107000303519805680c02006000e00c2c03001d508030301c1d0902d02800e214650301140005015203505480301c00007520b40d41814892480141d000a0050200142d80008804072501900849108009920702d862120744107459a02d41d0340f2906d41c10403160a990700d085840d0719050b50000400303081c0c1100508014000c2070600c01982e039070440d6503105006011407010208907000025401075409821800d001021140320708045c48081d01c1080301048010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 160671510 1250 160670260 160670269
    0x3090b0306030a05030c0c04230f0406062304050a0c0e0d0c0f0311030601060c0213091b060c0c080115060309050c0402030f070e0328050a0c2403060e0109020702 71
    0x210b4101e02140e0b129126254819540c2c0c0d5450411402241041c00385060031100c0989c0e20b00919500070395208503558603541c0410280007e00a840d007a45480001503403800c001015003c1840b8104214490b141100600c0f0035610060324029841d480c2c201c180018a5000005411550080b941c821030103203d4203016254500c0c94210702501521101c000040020003804000c40c0102601a00d040e0f03a60b0b0303070054510301200400650006610b00d030142c51400d880d031150017218411186440780c2404c0600c0ea00c0e04100c540c0050f000310b40320100c1c01c000d10075209607440007010704c40c00a01410542069490828056100c3c4809164595444000b0408140240340c1c803540c01074000c54aa140c0b01300100c0c1e0700101940d11001084200d40e403c1210300380807901c100c1c45000a0140c424a0000b0600d54103100800704095580b0700a02a012001811440028008204001042d40d0201c40c0580700401e00d8003241e0b580e0b00b494500141040b0540b40c441404d1b0454000140c01030316850b060001c41c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 160672760 1250 160671510 160671523
    0xb03071115090a0b041704080607030c0206070801090f0f060b0c0609070501091a09040f0218010207061e09030204090804170604030c060e0319020d0306140d06050c070c0603230403090b030603 84
    0x10329000e00030a000c00c110500003060b511802b429034007801664180c1000740e840d2030707050341c407035000031940b81c018003104010b03030441d02d49007054400000380b90005010303000403101640c0001310351217030003d80e2082c00102001119048000344e009031a00703616000020f4040031881c070841401c0300c404403251100d01c1e460800e43d007403c0c501074000e0200b4090307070154200940c0090100e041000c0c0480400d0419480080d031241030351502e48800b40e0b0382c3d51280601c2c82d0418501120400c01041c40c0300032006886c5c500404140ca440740340015101d40c00c00d0586c440d102e4024501c00d00710783c8a9010480804c1d44152034816160b04504009904119003d0700760031440b0f0b121813480c81c0f491940500806540c0050240c150b24251398081103810384a59041211040f1b981da01a40a10010181c5011a00e41c0c0d000e541c01885010045240c40380c00d41c0c0f0403100c01e001f907100102103940c6640490001c0300103031244c02c0c0c14088000f603818a180a603400b1b49a020240528817020303c0c08000a81d403a03c040145 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 160674010 1250 160672760 160672793
    0xf0305040f080606090703020310180b06040b030a0b060f07120306051002070915080703060f06050909030c010b060f0315120304090e010e0d050403080307090b03071115090a0b04 78
    0x1880e0701e00d803111101c0e0340d034103c1664194061120540000c801074840d100356405200c491030210007091510070700030045100803030b0542440340c3d2030407101296a90707880200020645009425201e141003060b2400301e8001d002101d00485040060301d00c20780d0341313000f11000103a00200c5507000100c85602103004000313070341240b60001308900622407100d800050480c00c40b12441814000c2035103d21020000d41428030903083c1641c0850024000a882504a000550211440007407900e0740d600c001074181e08241c0d11000d80c1d07000002c00340c0f003d110a0140031311002007600c0c402d00e0f02d04115200c917013070310000749268075910803482d035090540d48504036034200c0100a002c0301e446075140c0360090b00404100a9000881d07207041d03050310081102107021403058a49464090500d45544c450890b1540014441400c00000d0381001c02d6440c80c880143d40641d58595075546400000c0b40150702c1c0c0b400c00319854000c030407940c040102019002451005141d8440044209038039540707020050350000c48103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 160675260 1250 160674010 160674029
    0x409050408071103010c0512041104060b12011508010b0706060306050c0a1803030207030b07020a0c0b070b240d031e030902010f0503010b030c0703020f011b0306140d0f030504 77
    0xd00c418009031201618495016204142c1010740c003030200b50803103800f0048080400c80900c8480221401156215800b5000b00540c00650a800340001c080304c400760004200f4080108202c18010301c1480603d015047c460f100354600c1e06006d40141801c0e60510030304192407000600e400402c8a1500484000c40d4400828000c80c182260031940c0b54119030400d0300002e42d4000fa0312117035910380707065404403501038024040c180e0640e140d141d6415001003a00040d80701e03204020300040e02c5500c003a00180b20142c40141c841e045441c00d00c0c0200c6014103461000d81010041c900b03c9860803c0301d11184000f2200c401641c0800d00d400c5c0c0d00f070a01003220b42e50042c422240900c869030540c000d6180c4a102340d0b2480940010040107880c24002805802904241440080c4010040310018105140680100c54961f500b00080c5420761740d12681d0800091b013540000944c098160040d40d02800303128030341c0d526248190780403a068072445400a000c0c0044010003c06050107941141c014290512 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 160676510 1250 160675260 160675271
    0x51b0d0f1104140604050d12020f10020d0608030a0f0806130204030f0b0105030303040b06040c0e0402210a0c0c0b06011704030201090b070e0f1207090e010501091a060a050309030409 80
    0x700720118581052150700e140d4502c0450444040c6405401c55056a500a100769814544d540b160005640340c0320b101c806511518010107080b10301006011646100003d000d40c1d11401000d03501e05417086a40320a90582c400c0c03040008440d007081846100c1c034054949054a0756401001a100300d00d8007000518880c0b000801000340002003010b0502213004680c10f00c2c4030b90382c032404d0503680d1100711806803541480304046031003071a20740c01c0150f4041140c904210b400d040e00b00003804a031700888040c529203046501d6003a0030550004010707804600490100200c1c584d105d405054200c40d01c5008041510a5000902d40d81c06100d240002c0200444c0c003c903a481e00d40780207802881d00d044261844503088000030032507403050603444041c42c009401c0040c0419040140030f08046992035062440c022400049101d40c1c403441a11842c602100c00810035515014110085031844450981c01d00034103003031400380e52100701c1100c11204040c40e0150b82d90b542e00c2c814500b1340c011030b0004082c050a25 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 160677760 1250 160676510 160676531
    0x100c02030a180b0403051c02060103020123070b090a02100e0307060509120304080709110403020a050405040f02090a0902011808071203020705030303070e040528020d0e160f09051b0d0f 81
    0x1503208031f10f42c080742420840c43c291003400e83e82c90b002440000e00084d01c42100315980581d10280140385c284031032100d07060030043d40e104a50b40600701c9203440191f200c18024029841c02c641426442002c50500e090201d0003e80031075103c1d18207020300d030103003d0b000a181e85c850300c039000b81140c000400c0080d641c5550316001d08070745824451252822103030070001d44540981e020b0341160110b990050000710305d240b5100c140009060000c1060f40d540315148901d5000d078032060640341c030901d005c5070b0001c0c0440c0c00e07200141c01110f208a02c1051340b03580f44014401d2840014403c2c1c142c03150601c1340301a115a0707240032440c0494580100e9054000802440182a0010325006c03000703604443c00d12032a5110744500c04d076020001440c641c0700841d80e0780541d075810141d000b85200300350140c3c08185002354511441c903000c1c80042d920035040034541c04010f94001c29401d8801b82440c1c1c00306010030305003042e00760a00c00c0c0f0055100700b01c2c500003c442c00c0d018020ba0240c40c003c00030346000d00141503403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 160679010 1250 160677760 160677763
    0x6150307270303050a27170124081b030c09130c06020625080402040f02070b0903030106030e031602060a1106160e0a030b0f0a180f020102100c02030a180b040305 71
    0x200805e18003080225044120001c80445003030884010b04240100722403a01000300f240c01110328101030b181d5660340e00d2005c00340c1c0c288060246000b070681c080429900c2c02d110310f03207001e485805446810302d1040305401207640205a000346403100322003040c41500e94144000c0f521130b040c0c40003406481650302c00034145401180b0544a110103180020200c0c0306021000d80350103c0120500014140b0400200113141030344c0301820100b0745810060400c4050350b100c0091010640b480c1c0e055a0000c030040150644c5405048802c88440e805075040c011200003c08803041e00042c02441450701203504400c3c0c512414409604659680485c2d07039070700300201c09040c0b9180354028900010f001d21819007550078030848090440741e02443d46241c991706d640c841000c810020304089901521280d481444600350501802c5081c062a8400b490100a20019180c42c03280641c256450b41010880540d4a4010040e80c10700780c9242410303041c0d140d0542400200342541d410580300703078202290120a0040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 160680260 1250 160679010 160679017
    0x602090301021909090612230313030305040302031204051507020f090114120303090d08040204090204050106170a06050a0303080405010e012c0f0705100c02031905060615030727030305 81
    0x82880c406c000039519081c04541510076404040d100b5400e42031170b01c1181000d01896210a0000c1d0f081d6810045602442008508158801d6002840124082c020b52030103205800040345040070881c074261800021a8826000c680b0242c41c0c5240400c808081d034a0702c0d82c0781c10403070030018100c4605603160a000748512000c425054068160403141c000c680d0800000c0b64011440d14000300000118081c04451845005000701d0308240c5a0380181e0060b116809514042c044a48500050281c0c40c8070b84003075140300408240d903803814004100300c1a25000104d9040d42d40510305981c0c5603959003416800b601354000e0481d1558a0aa1944c64116040c0d080341724011a080c1f44a0180800d02e035855610400f20256903555040345100304000c1c6010030500c5521550790510b06d4484419400280c1011b03400121801d001c80404010000c1000c24448154001c104603000e205804a220a40c3c1c2140402440c0805020b900074081000421070700b5030600841036036030405035840c1c0320700d0f00412070742 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 160681510 1250 160680260 160680269
    0x1030c06030c030506060306040903050c03040e0f1303080f07051b0c0112020306030712020a03050d081005061914040b07082d0d0504080c0f010c090506040609030602090301021909 79
    0xa15181c10041060b101380621070085200400280c110389400341003200502c0d04200403418400c080041c00e070502c100344050002015100b4600d01c0918001c0301e42c240c040c03801041e5000421440d030a020000e44c11840250700a0103c1c00f00623410703a10810f0545452180743c50141080703580c81c0700c48200c5007001803501c034024000c0c2e0320005424a142d42690507800195581d0798550008101440740301040103040550700c0c0010720040307036141d494507800d003404001014440099241000c0000142c1040c1e052401820142c0381c03280307003081e01220f40e08400c00f00c0c0c4424081103000301070b000000200f101500d02401c2080341d15956241c491801010940c0000d0301844103148482e0207101c00250407540341002ca0100c8603051810403044550002800003d1003183c80200500442820103030411115401401c5070000241d071640001d4091f003110441ea00c420b100e00700410007841815845200e1b00112507100502680703c04d41140024068020705802d660104144502904090b0344850b4400449 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 160682760 1250 160681510 160681517
    0x130915081b0a05040f230f060d03170a0e030a05070c0f050307090509070e01080604061b0507030c020d0210080109050106140a0804030e06030108160509130b0a021201030c06 76
    0x280904800101c420502229512800e81c00301085141060b400ca59180c0d0019000002c9803102c03684100c051010200c0c40d01c0706040d903c1c041142c1106e40a0a02e5045a81299900c5c00c0242c03a03039004081c0130040600144456681000c203001e0300301500324845081740d090589403110300100000f003164029107420780d603204104000140313880c010081d2400741d0b1030140c06030002c00c2c2031400d0340f4003814016100340c1c0c00c1c0c402c902e000074000441010310342c080c01e03002e0003618003420642070550a0b601c040b00c005441001007400485611341044c100c40d03850741d00d03044c02c580c10740072800020307000c0703480d0480a500711034451001c1c00025403141005040e42c211203030412040c0d803194011034943e85050851291000100405c0d10070034010030420703a01c54840d1070090144c50006c400308085820070f0340466000c0d480b40803500da11070880740c80c0002412003520481a540740c44403819100e02140c0101510803000480401c0303904c1e0240d0111214003081c5c0d0110443c0e541e581c0341c141c1054440e4480c11000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 160684010 1250 160682760 160682773
    0xc010b010801050604082d071203271a040902040f03050706031802010305041e080a0e0f1809030c19060b0301021c0f0b1504030507080d05070813091508 67
    0xd85413540a50701511811001003114005c07640003001c0c016100400740356402001c8070758400c0d84108200c0400036000c50801104035003054540a00700b0740220518008080751507207030800749607513601104200d8012034a500d070803480ba034850150328072998000e50f150038000200482c0c1c0b03460b1034a4001c2101d03c0340d0304544c01c05994100441c122105040c41d4031003281d10052400241d8429001140c0040c0a01281108903203a4030701404168044d90040341e51a50101d40c8a00041d00028136080000382501c210562001c0e1000045244040d52a01400c0e0701c84000420b40c0c0100400c01d0741d040d000180d04030ba204a1503c0000f04c189244c0c50340850f031083c1032680000b00c2d1b08040c000d42e194082104507428203042408000b00141400070442143e0743d40e100805a030303540e5103d6040810b910b5082020b0b0b45e5a003103090643c18010303141c2094440303522543c000140c0380d600400302ca001c640c1260403107071981c00e415920510880780d680300201290518280c40020220103003428121503103034080700c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 160685260 1250 160684010 160684019
    0xb0409060c0917031903020405120606010909060b030a051e0f0103020411090915040e031c050a020c0a12020703021f1701060e0d260a020d02060c03180a05030c010b010801 75
    0x443e031518012000e5240c20601000c0c142007444c0780003803031070407050801504083d1107a01048040700d038031001d01d100b40d01104c188452540c202c2c038110b01070154858288103460622500e25a00d1002070075600b01e01e0740c1c0e000000c1ca445690140c844002138002e0003210035003084502016003103401e00081c2d101d5071915180100345c944450440381c030028081e10140496450f0f03051700490000d0b40070a145c000e604d0f10015081c200c0180024480220024038103071603000c1400800702240d50007001221094810825201010360010782142c40a9001300314200c41840c070b030022802c000c0f0300d178802500580d4003d034589041a070000404807200352039450074602c03514402c1c8980c1240d0280f081c000400c1c40030402060504003802d1010069006004051341c1502741e0700640f244a8814040b00c1c1b0b00300d030100300705040c1541840f050554004600c010304c0c903801d04d003400142d144805001800030708141003000c0180c200a100200034560054103880c0c5940b4821800c1d806010640c030150700180c041400400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 160686510 1250 160685260 160685279
    0x20f060c03040b0a170f040803070c050601060518060717030408041802030a050601020a171e03040606080f01050103241b050306030c090405071a0412061e0b100e01030b0409060c09 79
    0x62241188a0146c0010b446544a40c3c526510141c07803401000004602c050120f0420040b4a00030075803a44c9080c1e07a1940302e0124400442d803040002d10a0318204540c5020a802198980e031240d4808642962074a9914000300c01703100d180e002c1c584406a00860001d1004c0d80d038080c1d44900802101406030340d0b40da07801281c4a42c40c0100041882005400d104020754441000c1d225100315009484d42200030501014900e403c101c50880d0b03040c0c0c072414203000c0a841445030f450301540c520000c0c803035075065030f944804883d5105905d0810341c203240160103400a154001c220f03003c40c0f09540c00294500d03404020709551048507114000d01c03401c8803440c2142051101644100d4010303010340314044c01c11407052081c1c03a40100310b41c2000700601001c00c074221a4015040122b21684000892000324500a82a0001030701d9440400e80341c2024512300340c0351407415041d01906440d00b81c00c01e0820100590080205006894000c0d00e448001001c10001e43c0c071030342c00d9a0868036070141c141d0fa00c05208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 160687760 1250 160686510 160686557
    0x1030b0105060306150906090d0c0f0e0708040f02151303050d020c060d0c021c03020d0c030204031a04020a12050f07050d1e080d020304081206060f07020f060c03040b0a 74
    0xa030708007450150b900004000c17035001d800700d054000c02e00c92402c203d150000b8600c81c60a50180d0b560b101c061400c200d0a504844100010142011519a43d2400c00e40203010700c04000c00140c6180c0007044800210365860403c0303134100041285030380d143c0760038400300400c0d03605502080380c00d442a524a142203a000180011130a44000c10142c070f44591060f03020060701c0c49000c85c1c02075108106c0c4640040c0d8011000c201031400941c1c0050f160f4480c24840300655142d030040d9424144100002d2011804050b414145d04265520b44603450300c540c0302003001d038a101e42c00b81c4200360b8000010030070854041020f00401c0c0b41c003811a144039448a0070428201c032140b00c010301780e88030802204401c0b4060706075080d800e4000c3c00c80e40d0510489228040a90344111001c03156003100007028090014105840754000c0801d4584074286280b8100710b81c258429407001078400e491f030301000c102c1561044200c640c480c2c42d2070700b641d48544e03079040041d015403c1640010007141d0b02c0e8890940030703803090800f03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 160689010 1250 160687760 160687771
    0x90d0305090c060c0a02060a0f03050105040501050901030602031009021602010201060e01061e0c05010c050301150f080a0e1204090b1503040203060a0c02030d0c0207080f151f080a05030301030b01050603 89
    0x40c10b0700110a408001c040e91000c01c0c0c0c040070b070069007540400341e5134140141024000d15148d840e0345203041c01c030040890390142c014034411817818005128540b110482241526480000140e4984441c881e820040d1103c1d80819151800060702c2d4855058040c003440e0600e20030780003400190b40700c0402829145003405450002100e1800800580c0801d9200d0001a030307540c01d10b082c28a0050b1a0306080d10a015240703400300380300000400183c0d030503004140d10541c2525203486680c0d40c4040007032106c98082c10080d407058581c0b6130122038602c02d01c07000150720303108400c7c0d555a556400384bc0000d85811340580d4818168082c151012011000032248030300ea009002d8a10b0b540d41c0350400000b08450700c0590114030060140d09108080c621407a5040060f503001080418a05002d05140c50b4401b140c6803840c2d00540e031042d0070482c04558480d04a044851035154035005d00780c07041c402044950244c5c0051061074880e50500001000950503a80102c0102d001aa211b905006540c07005441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 160690260 1250 160689010 160689013
    0xa1202070e0f150a150503061f0816090509040501060614210408121e0105030c030a0b1b0403031d0a0501050a14040504140a05070806010f080402040f06090203090d030509 75
    0x1a401010480c15800c407200c000307107083d040e603460b210040c148130700400417840030070360020902c8040e29020081c03600301d2255405c0c0508814032010006c1034000040e02e2010701c000d1310003981e583d0314041c641540103010003600c0421285030904195000e44400c0c030a900100e600450240740210100b0204ca551080c002e01c40c441080107203800006904000b04291542c207001c0c0000c98101041c2d0840d0781c000c0c96100c80a0321040140c0c1000450727444183c1c4000d120b5400040b001c1c0b855280031600384141d607000300f45190360340e40748084c3c4502c04400f45d146280c8000c0000b030120030907420100307020007503200f510f80d110640020014040c9464050043da07000c60018401095002e00c00ca1101c000202c6020081c4c1c10030f940c800100e0250349900d000c04101a07001d400b0020394240070301c28070368420500e01d0580741609089001030401c56140c9007050800c4400b10001c0c0a40d04c1c1c80d004080c00350b030720641c1008080d07658888a4000d4009842902542c0104c1c801000748920902400d40078082800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 160691510 1250 160690260 160690291
    0x606090605030712060f0221101a1303020d0f1406060d06020c01060312020a02010806090f040f06020c06151c110d0611131d040308070f020309030a1202070e 69
    0x6a080315880c4130741404540068444140410361101400540b0190300b4091208412107041a042c0c95800e50040c034a0103049201002048006c5440d1940110130110f1000c459450301d61071144103140c031060701702940210b581c0a1060800005010031504030713000e4001440c40070416545261180750598010354421403c421300c90200d0210340c0185141130743d88000185881e641c3e540d070790000c1c00c0200e484000d600000b61000a558010241590000c8102c0f90f2500310301c0c000500620f4004040d0002e41600707012071580342000f10f65411589440090011200c151404401c0c07000d174400960402800743c0101184400d81441d903503008000f0550240900c221002c4400a00c0450180030340c003a22469145c3c0d00c02440e2b203100d070006200b80c0301038840000b0994103100d40c003240d85910b01500c513001d21f0844200310200307500002c45508080580703090f0b40c4111203c0812451130180324010703941801010b88610412460400c1d1061640d90364082c0d44040340e07180d000041a0400315110b4034480c1140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 160692760 1250 160691510 160691519
    0x91206131a0c030f2707090c020105090a0b070219230303071d0f1f09080307030813151406010311040302031c0201020f0f0a090909050c0f040b03030a0203030406060906050307 77
    0x3003c00c10703400400d0034200380006407454030300441c2d18441140c0051700c1c1c00c07401080c01640002e0140d481e05450034002449903040c1a42e10381e42c3d8485021000e407003048d80d2808101c0c1c2900c01d001d060810114130180181882d1030341403040f6101c1c1d034544a60400180304407a035410800c0803040c1c0b0300c43c248548030030402105a003e039055620101f03038081d61158503181d411025070741d480da40c0944c045032a981c4169081c0140000740294005401000c0c81d60b0051201c03100103588422040c1e8890720001d07910703c00390040e2070001d07e03407091403401d2060b25080036071340100940900112885800c090382c0c00d210001013903c440e1100d00c55800041e402d50044030010121410080220440200b144001891304c3d80c0581d64a01a80088980040890002984047c070a501000e204081c04880e2030810500308c4540d900b9680f41e0203516154001c0901c9044182650740c0c0368410f607c00b56018064030741d69603800c4c200070740340d5004440441300c0300d1400c00d01044064480c801c0200340c5001400510406082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 160694010 1250 160692760 160692781
    0x20601050d0b043008010806010b0708040303050c010603020411030f07050c0d030e030d060312140a050909040203011d01060338090708120405120c0312091206131a0c03 74
    0x800000c000152031155410030a001c0810032104c1c0215503560f4082541016002c0b414180c2c1a07010344d2502105100c2c00c40840c0c1c1550031a8112641810709603540c1d408011200d01400315548040d60091070303e0201807540f9015401140f0601e2141c5104c2c0b496030326070b1800c2d03c50717000d400d14880940d40420340e800b821a000c1c2d88400680c034085004c0f00d0611103404030060a403002504103c0d20b420460903101a203a40112202002100581e05a4100048000024650300840e0741d030718450304100e00410b040d500d083d40aa004065414111a2010b8039140100c0c041c00f403901c822548464030a45d006250000555580180141c2c41d100180b07264402001d03007a040303c041d2254580c0e00408500043d4504100000c0e400080100c02454681e1710308010000d01c42c5441002105540000d14991055135000c5240c413041c07460f4207180d42c0c41d0b01d5498042000d2140c5115900710900c1001e06001c104102e50000402140c42405081418034036640c2d400d04007102503c400d04451380034004101802d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 160695260 1250 160694010 160694033
    0x20316050109150e0f1207060c05070203120a120b030c09041e030e0f011707080c0f040f030606061e080a0905031902300f09060c0c01020601050d0b04 66
    0x2400042200c50b81a10b0f101c0540e42014103480650355a00102c1c00c13501000d0140b00d4052404902610410140c41ca180b0424403c8110003030034140d4800140d580a030099050f074000980103011030b48664031401039a071059009241040c0803070811040d04030441c1c01409500c078007040190240c0440c031010310a21852460140c02150802c1020041a4040e61603400300c1614034001d0b0b8036020300f400321a040c84040c0c109182080d040000c204a003954500c011262aa00b00c002da241c5220300f5a50101d00d032105000761580404c051000141c001071100d50b4000032010b0740e010b1035082099640d50041034540b9220345200c00f5816403486800d101d81d40c040c59180b075101000352800b28545420344c2c0c43c0d40c150b83c810442c0d961261030101440f100990704001040310480c005410841c410071000c0e4909100c03003040340701035410702c000424020309101d850540b070700c0d000b004d01440e840c0c10303244004c0780e210019402901d0040c4141c1000217600e00d0320304a4001307040d030000c107228201c1d21541c680c18050030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 160696510 1250 160695260 160695263
    0x30d050708090f03122106031b010201020c01020d060e09010204080d180306060312030b060c0705190f03030801081b0609060d060b03130204050f060f0108100302061201091803020316 80
    0x600965443c11501d052215a24032181c100c0d01c01d50b920004e5486056501e100001002c40071404d01c101708903030b103000500c0c071029114407041c0700c40c2c1c00903400100c4c0a0b00c031310f0f0300300d040300e500200d80c1c0040c00b6000e80014080e6400340201c0c0020b6942c007040c8900300e010302d2080b45510750081e0601c0c0c020394003c02040c05205030404203004456100d80342c60059441a60044640c8107140001e120420b41c9841110b281243c110344080c0340c0b01e4200200c2da9681e100307020719031244416801c03100001c2c0303400200e0b500402d0759048500a695403800c000e004c1000912500141d4020100304060803117080c200d4114411009000908215120040c0101a013005081c100721a544000119021b094100998850342030544e02a00d0040d02c0e1043c08140c8401a00b0071031011082c5040c0000c0e9601e100b9105620002031810b1081d0342d0b2000048400d8014a42c00a5000500000c4000d040c3c02c0301108103041c4c600700310301030010102c482c80003501101d00d0b94026006803c103110f040880850600308442c2c2a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 160697760 1250 160696510 160696519
    0x4020c1519090b010503010c18060f030f06170f0c1f2304090c05030c0307032423031b09090c060c030705060105011701090f0e0109030f0806030d05070809 68
    0x18201c80c039600080741c502281c1070796420700d842d004000320b03e001d005001054200b4507160f403004000c070070a403407250b0140c0a070005000c00301c0501c40d09284a0780c081d4440705107803202406000c0d6203541071038400150161400e21030282c1d0824241e0803400242a0003183c00241050b081c4008210b01c03050700100700300144081080000d2404c20a010303891252440744e0141d112147d481e40f81000880456a900c480081400f405108128000c00b03464184c9a11040c039060100d094820907030540162811508501c080c0040054049807203c418240c00390007404c206d450f02c060341c81d13110030583e44801211410305200351b8141800c000c0c0c00c100c00c1543d0000408801c4401ca0b54100c400106141c00900010400781c0c0085000030611104100d0140100300a00706071655030115215041b0303100b07050088128481e01d03502c001c0001e0781251f000b04401c5403c1002000352004615005024241e128081c00004580070003250180c03402103084c0743c90b0b1085894143c50001c0d159a00d0100c4e8010b4110f0541c070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 160699010 1250 160697760 160697791
    0xb12041703040501060e060d0302060c280c1104050402030c0f2103091908030d090f1712010602010b1305061801060f09090506010c060203060d08040f050108010504020c15 75
    0x140390810300558010362107a80007251660403d5208490150010115480790f0501c01d48807000c2500031520540000c00300c040b1542e24549150100420344800903030209000104c40031202030f542c0802c8200310700c0d200b50380c085040040b8404100c1500d500703a50181d850340180e9074465492030440c076400030181000c3c10f8540320080d60604000d14000840551001e90800507240315203141104000b42c1d809213202c400d03001c41d410540d84036079034040c40b4000340015071f80d09400024460440000c0c0100c9a001c0e001c110702c4d1841c6103180000d030f0441a00302c0000c407801d00000c21520b00602501a000d8406000302100c4141d44c041c0c6406401e0180110703402241803282441c0c00c0001e00d80c514003a29290f280d0faa00a00d407104c0052000c00d90781c2c850708442d03150400f0f00451360307030044071803025540141d4091780f2600e84100083d900b1208200080c198a000600000c2d00b02c080c1e6202c9080300c0090703c03000000d0380c1e42e0b02407006a21440201400d540c110170f0ba10380c081140c60b22101e070840720748000c41e00c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 160700260 1250 160699010 160699043
    0x402040501080c1608030c09030f0109050a230d030204050319170d0605040603060509060708040308010501050d0e0106080f1506131d030c0319020a020907110a1a060a0b03010b1204 79
    0x1140d8000e46510041a03070002300c200650070104600b03038404140300000c1003200b00ca034460a440d0101c280c0018500c46418522500b05289118520a4940140180d0f034400c2d155440190003507200e44621801390069100105800d411819241d909542000c8409031204080c2c00c0c0c41001c0d800410000d072204d5a0703520100d03468540c1d210300805540720360000110713420001c0009142600040c6010301b045a018100070010358410b42c054119007003820169181c0d954222554041c20402c0503003202517181c54000150405d0001d0031143d0baa0212059034240423007660390740711191048803040d8100700d43c107070030008000840c1c9c84015032011403004050a6100c0349411411944030702c3c01504617030310109000e21004800d0000c03501d4401c07036000400e0399010540c04038503031031801003174a0280000c100c2e06c0510b41c08203205071045642e100d00b1420b000d000504039010500801c2d154180504404c20740070840301c0c1130703030110790503036003240b040030308022044103100ca54140060080310b00c60500d02e0400c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 160701510 1250 160700260 160700273
    0x3170603030c0a060903030e071409060111060405060126190206090d060203060310020307120509010b030a030507150c121e0504050a1203050c0706240f0e060402040501080c16 77
    0xc244141ca02260035045420b009060701c062394820401504110760402492800290f41a100031013500c48450681d607080040c5c8200c44615618000c6000b240c0c200020070001081d8a8141e0703240710b2107074403000d1a880582020140d10004058103034081e100d01000b071242220982c081e244001c04903450110590003142042c100040200c5800341c021050100c145003c1c0400920201c41c030b00c00f10304500c1d1200e0000c1400f02c03411481784c40f095803900400c0e134618081d04072a02c104005030461b0820500c0b4034004280d80d10400d0103a984404041410001075540d00070f12103001e110b83e83e0180c40020710300e00440240100429070185003550b01c0c1d41c440e024524054244100c0c0184003405041c9243c0c03c0c45080d609851111208142c500400c2045004610040e641803d270030030000030708498001480c034000e05240152600c402421000010002c2e1003040a8003590000c0b003030300e00c071038841c0f5083c802a409280950f5000c0755000d00000c08465101d03001d043e43d0b6581110a011000c01c0d40c0703400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 160702760 1250 160701510 160701523
    0x322080c120a1202030c01060506190804140105011d0f01050109170f1006030605060103050609180709050f06100c05210d0f0b040606170103170f120f0606030403170603030c 76
    0x11405a00003045001b50410b0030310403000284030584040349451000400c1054858519048406103c0107102040500080c1c5081e0340c52049014001c110340c0d41c50304100419a03240d0024503129034220000a035860350480462812a501a1070311141c1ca401c007403c1b0010a09082001050351251401600342c01c4003c2100c1c0080e0040590700284440c15130804038203681c001002c15050605110a01c880ca4803081c02d00c551001d90110020501c2c544182d2003030900c500c1e503001d0103200e41060240520440c540f144980200d0007201d085401c0c500c010400c1c0c440d447d48003801f400030740080c02002000710003860114084612101c0719881d10400070f04190448440359805190320350f4415800d80207080500c60f4401a1a9504010425801a0303510305900c10050000a20074007071440608100f14405094400c100c5402145603200c003a401903980d5440802c03998045d90100940100c1d1245c103200080705c1c012500343e500c00a1540703440302103090806015200e150184020032030540c0801e024040c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 160704010 1250 160702760 160702793
    0xb070c290a050c0c071401020f011d070509070e0d03090503060a0509010c050412120216140a060e090708071b03200102090105040e06060412050322080c120a 69
    0xd4500342802046031007115001002044441d1041106182450300000d60504803000303900e00c2036000e07010000407030425000c00e810100f107609020100200424610700100c0c540864800c8030f20301c0c0e541e081041440302c0180d030144081920b0b00046030060401c0305610300d8460090800c03404d107503500c801080c540101200c604a00c9551070080c80b40b42142070140c02c2130401c6518103e030800d0704000700d08054004002006005101c1c0b400c10f00d0300c0d2402803010800500b80001c040456954a0030392000c03c00c0031007100340c071401c0b00f4a00807071202e000741c2c0e00917550361020307001c980c031035687da00240c0e40b603c40034010106200f4003151144d5030b100511a81203001d4400d544810b840e0501a002d550001c441d40d4103c20164018080140700f6603200060303404594460341310f41d600b520b418012581c984501c3c0c015520400303001020b20140540000280f20004000070101080d03140510004290601c90181503041d0b0805410001d80e8070b0130b0131080c0c424451040586401d803801e83d84501c1c2070350709030300bd = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 160705260 1250 160704010 160704083
    0x1302060406110c01080601050909040c09020304031809050714032509030201080c070321020c01020a0c1a010b0d0b03010213032612010b0304080c01060608060411070b070c 75
    0xc8070b815014004007030700c64000e090281031402c00e01c0000e8010b000f014040c5004140d0840003034240200b118000009007036842046560342407a007002005041c004400b024003070b0110a000555490710700c5641c2c407803003495580c80001032118520160692000d0100a48035404841c662051440b9106540700030321070f0344a502c4414554400036243c400010700202c801c10042c170120010a03000080d4250040c80414011154004a80240000d0055a00030589036201042e00c998154000012050030b9010b141d90021460501d480c03250b11700e03005d001e5100600f1090181844400507a08102219031001f0005130a0030308030080b6004029141d44181c41018809121020024010b406a014241c0041003c0d14180b400329003c03c40c41d030180f084100c40c0340008002820b104a0b4802d0b2080c5ca035400300203000c44ea584003002049800c00342c602d14403891400c04030384076408054003260b4503568480440c0f441507850f103006440f50801e0701c60649090703103130006900da0080d00241d0a40d205840c00c0c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 160706510 1250 160705260 160705277
    0x509030d030203150a1404090f0c030302030307090b0723010207020618010813031b020105042411010e070e070509030f030d0b0603041112070f08010608120a090e1302060406 76
    0xd00103222120a030380c51342c09585181001d1260b50100f4185c0307400020103540100c0e03030640c2c40c601610f402810072409001c544c1500b40202c00c0548c0800154016400750b520025104d880702140b82591150a100401c1c110007000c0300500d10616078201c1c0c0c02000d8071800141426125000b10b2515170149200c00701006401000b003500350b8200c10741980000341804401504402640c0103481450600d0728000072040c4405107004580c880c80464024000782007030030f00e040045e440043c5000325117080400108000c4070001920403414410100c242622000802501e85441c07880c03104800c000c1c01520405c00100202c4810340c40070040b4807080c0007001e00450391140100c120200b11050403100302d118403020800e00011605402c4240200c10040b24401d25180984204502d46845544403003010b001b03c3e01c0020b4110300c10750000d000c03140301c030094550004002950078000e104045d481e00224280400a02c0300a01d5507641651000030005104d00c0c1f08601e40014889400a901600009620a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 160707760 1250 160706510 160706521
    0x91002070320090f040807120e01030c140a03020d060b0c0607022b050a020a020406080114060402070b0c0c0703020a030b0654071e18090b010509030d030203 69
    0x40b4051941c01c0c14000e0b048105405a4000403154040038016001500c1c05101080520900d01c1c01c1341c0d038207640314055003252520040c0c05400190b03070b0f400050110785400c1d040103c2d24050300542e504c0500c51252a840c1030180f00096009401c0101009201544d9980118010541700010510704a03c0d400500e040e2400c10310003031905090031846000f08000c01c90140960b003110710144441304d21401e0480e1680390524040340740848914010f94001d0400b90300090003441075001d580140710042000200b6948d403818441a8401e081000b440d4442d26800251034070a9a00070384808281d080586016070307605d0b0001074054802e0342040c0e81090a8109110b40e17454044012041d910b202240c0350011001e8000008401c2001860038a2910300115102d00c009140000c113680089812940441d50515103c010b0400c5039403c0000c402592008040c3d800341e014882418201610910000480c0d040c4583c0a003c0c103001601203040c0903080c400c1d034180d9039003405100300e0115669401a12481c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 160709010 1250 160707760 160707773
    0x901060309050f030a0504060509010318060b0a06030203090a020906060c010222060c0201120b0402040801020c03040503010c1b08070807080307080601140702010903060e0a080a0e041512060c050910020703 90
    0x2040f08034900c0f58001c0100c01c43c0a508202914200d8400b42012a203c03c0d01c00d0044e0081c0000079004541c040c0b844010600f0002190301c218250502070b100d030049152038100660481c40251641e41d0b145c5d000a021030014684031803900c1c0d1048010740b0407805c20001940d25402d90300054115001c060b0081c1c079490b00102640000001070201d0310700707198154000d40019003282010039040200036103c10710440036840300d40440b40180042e030006c540d60b00000d5001078803a0018061184a9402c4c8846005158450090208810350344407841c0b05800703003651642e04a9003c080125030481c4284a15004219004059441400244c9400000f490010001032808030042c40e540e506a405004140140c0da0090800050b65401000001d840650a00c0709242c8126a0f400606146000074081c000c158440c1c00e80c450182c0c280c0d014025204142c81507001d241031303402401d00a0031014814000f140d141e82010004000c2c50504900d0b00304420003052880000c1003040015a100c00d0041040111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 160710260 1250 160709010 160709023
    0x506040b0a030213051018020c0145080315010e01082707090905070905010503070302060a12060f08070305060c030f0115020f01020a1205070c02130911090106030905 73
    0x10111030529040e03045600090b40c81e010032100c601c1050b500c05c000340808030944000340c0a00200350325541184017031603000029512138181e00171903509040c1150000c5407520354071410020401e9008a4a0f20451582c911400c6510114010120032410352404121000010740c095048403440e1400e480c0c101002400c0c820300000d130541013280e50000c100361024441e060f4101e0f154041c5655800d0b07036104c0b0b81185003200035005a20083d240c111520104100050300004a40780081c0900982e070740e40c020507407504a130f444041d420a41c20840e08402d02d02c0346c03948032620381c0500c4001502c01c0d160740e00c0d00c0c1100c0454005000c0f81d40403100501c1071141c2040982d44c000310050f0301901d103292140e0400458401031107201070100c410b1070300301d2000b07000f031003240d03c60520403000b1900c4084400c0010030002c0040500344910b807a0a0210b5241427180001c031141c1c64001c5c0c07240980301d0101038010018980c042050307030803121110380307140555951080c050081000b990086000302090401900344103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 160711510 1250 160710260 160710281
    0x11030901050f0c0405270901020c06090c030706030b062b0e03040f05150f0f070c090905060402210f0a050c120a171603120c020102090d0803100302090901050604 71
    0x30700340080206460f4494119002e84401341c3c2c0000701000800502e018041c080c001d03c402c404030800402c031340c0510550251035100301660071152140c43c1c8007580740d101c5105080298141d040304000340243d83c0607811020309a1805041c56141505003805950030b641c8a030301c0d00400c1d0044401c000c1c402c0f8418060b007510884100040d5103040d2920600061448a52203024060800c603459403190300664405c0d24140040580c0305541d50184503440d00d030f00e030f05c100d004445c49040f4100c00720b4080700030301c901c0e0546a4800b00a04039134850f80c00308180b40c00c20905009200002070401e0b00001800e000d5a034201c00c1e864018003410740e076881e0590401048110140c000c04462132031041040d00007904c0341c2c94640000c0da23400004071074556070000b4414240302000001c901444501015841100410030356500c000c20400c110300c0c0300049081c2e02c18002d0340744e0301c1681c02000001042e100390045401c03201103006000301e03d56030b43c0030540c41c040490ba09030b0700d03075074407403c100c2c3c0c07401e0074050242c144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 160712760 1250 160711510 160711531
    0x3020d0302040e040b0702010207051c0210060803030a0b0622090b09090a0b04020a1d0601021507090306151d0417030103150914030309030d06080109030f1b061103090105 75
    0x5007043c1ea04449010000c1000e800c000b4040301041241d030007941144c1c1c050350010309a50100c40c507100b070085480500c451101c0148508400107901014a11030001500c640002a40c43e54940d0217420026002514001d903118604201c0d00c90114034070506c0c0404403040010700d000c60791810301050201d480c1211041c0c0540003100400440c24800319900d00d070b1907800a800e54090b11203001013100c440441d08021400e076500013502c10202501c440c03152040000b6421a0810220f4100c0c240100d0030981d002800300300001400d00029495801c44541c50401a2030140503c1e6509440c0802140008001e00c1400e410b0b41480140598100129409507100c801c1ca491545169580c0001480180307101940c00e90f80c019010410400740e91305000a0340b690101c0f0745a080030f6003099100c1d48206040501d0520f800b0000a00344c206000c2e45a100d5091f4031080c000c0c0e1181c1a0a88502d00f510f241758441e10f80301c20300c030030001b2030724491f10788166011410b00c0e4480c0b900746072103400c4483c00307007824031031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 160714010 1250 160712760 160712767
    0x20a12060906081f090c090504020909160b0702041103010b04080d020a032c040614040c0e090403030e07080609070f1413020c0c0913120f0c03081009150303020d0302 73
    0x150b140000380c60103101306800100c0507070070114040340014020b01070018808030300740300d0010b0400f480747c1086000d503000f100c005e8010340300c0006440d42c60b141044080184282600c003003146035000e1028100d1940040c0022805507146201c4816035442600b2240385508046404d0102c0c0d17400300500d0500d004280020080c01269490140608903200072003804010300181100b020300c4c144080311014000644140206c81d2500c000962052070120302c40d000d0380c542a01085060b00c43c440c521070701c000243c000c0c4c01c95296902c0c200d0207040c4402c20082d4521032010005004c160070001d443c41180d01754041c00b003450621100c480441c42550000c020b0508040440030182c1c1c420401801121a44400680e903980b194503550400c61907c00300baa0010b452000c10a4014150710354400492050140441d01075040348291518000498000700141303000b0600c20020f4054401250421448502018416510311400b000d0360543d1100a11122a084040042640400044001c6841f0f418107504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 160715260 1250 160714010 160714019
    0x303110307080f0d090210020d0e030a080706020310030212070501080c0a080a0b0a050a060309110604060518180a150501020106120201050f07022d01050f0a0f090801020a12060906 79
    0xb580101100031081010000ba18001000140c0c8484030043e4003502220200e85031050107901c0d50081500b0802054103d0016109442c010580005007644505490300309400c503110080207404c0180a9501c0c925002d070007001584d244080020101f013101c00928240d420600018140840500344003c0120288400420142c102c0c181581c07243c900c0300c00050281c01c0100080c0c00c0c6800b0352005800c034035003403404a9190386c5038000a92a50050890301c01e40400c0c0743c14040c0620840c858030f00000d0040c01b41c03040d00701000d400e2201c007240040041403110549103800c0030707022040d18000410383d6240c5003228031400298540c0c0007007409000030400030389405044104c81c440c4a00090400c01c1c00035811100e01041c00594034481c4c4c000d000e0706880d0080900c40c181720804088008110107403082c3c82107140d0311440840315140700ba8802103090940c888816140c40d500315605200340054001c0201d80a0000d2020f04032001c807c0e03603900f110001030011b40301160026084906c511741804d20600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 160716510 1250 160715260 160715273
    0x30e0a050109120c03150e1219120902060d0e0c040e071a0c0604030c02030f03070c09020711041422021008190903030606080c07151a09040c0303110307 67
    0x4003207640c2000f00300114070807403800f1050303044036400040014104484100711000307160b11440740c02c0010300840d01408000000e83d00c0902421401e184202d46d894050707001c003407140301c900104816429010030222043d03400200035412602c65010403135a40e0850300709410082000564401c41074070104000545050b02d1900c6410a00911001900c0c100a00900d0368020003219404100082134699904252400034031641030380c3c409a1107031040c004001c000240c04422115119802440c0054031382c0707002e40c0308019410024094503882407141c20030802c0e032214000c80054040110001041c2c1c9840729400303400b0f900058910001103007850710400142c8965249051004035414041e12035a03980191780004440070910300c503041c0c10548079104068154101d0416140ca5884070101d9589503c00c84546014844019041c0641d001540616881641c0072000302c0c201c5c03030030141070103403041c0200d2103400303094900300d800341d08440c010018940d01810280c1811020006985405515107881 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 160717760 1250 160716510 160716527
    0x80402010509060c0a1b06080c07021e030604060b0910030201120911060a020610150e220e06370507120504080a031a0d0303091b0e0103030e0a0501 65
    0x3818008001a8580b40307035901016200403440304411524a00c4803807178150740c011003100c5440d00b50f0b08690300c04681203025859240c8240c0861540d2824412180c003000009507070080615420350348108004541d071000e020701441507014040200704410300340c3c01d104001600800140c4400c206040c1400180e038888031741c50000040d00d00124002c0c0c0c1c1ca0400000342043d100126604c0300c00000c1000c4000d8010032001d2144800d808443c00c4241d440500e02c3c001c850b40151500024410070601740b0500e040f0f0040e282e9121001402a1252414808001210480402003c65502800412112600150902418040c28000b258103681e50446004c151080c030300d00d80c0d00454841c0b000402480c42500003403041d0076544018070107400e1074240700415600501502d8000382c00c1c644a6030308140184191811004c000d0410120342886403012401051940e41c03c0304d40381100001c4500d001d603607110b40b2000d007081d10140300c034551440c54080c0030840c2e00c0d0025401040400030801c020383c0c0001c540d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 160719010 1250 160717760 160717763
    0x12090a03090b1813140103300f03021803010f060504050a091109070c050109060f0b030f101a060406080906011e06080604020705010e010e0d020a081803030d0207060b040f09030804 79
    0x1600d02800310820400150881070802c8001354080d900000234000201407000a5115124110800030414550f481600030080e09050100703044512515010b40b1a5008010141001142c080e044011000007800e440440d60344200c2c145d10303074200f42304a14161003900d411040b004130030064015542d070b411681040c404841c0384101d0128000031804e074000e4101c1b4281940c401d000300102d1a4510308003004150814541c0915440c0616041c0386060020b900c45240d0452801000c8150300408410043d0510104441c000308071188414540d0f01e0f05d00251018001a0b2103407806890300c50300b16860010141d018109420442e400072602c9041082c0c0581524580e10300702c40c0b42d07654440410040d11400c41c4c010542d41ca46404181d0250341980a4510060054151800010595030407a595800c080c0003600c00d0b24100004051200c6052000b24901c00207001d5034148900b614554040b6001510305441443d110081c00000f0f2505100d4500c1500d4219420800100b05403401000928002c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 160720260 1250 160719010 160719019
    0x8071d01150309030207030605010617011205100c090806090303070e030601120305090406050d060f0506120615010e0a09060503060a09050a1518140d030221060612090a03090b18 78
    0xf50414140b09200346805907401038018816035940e030400030040710500c0b040105240003240003040364186008404c03a0f480c4c002c00109841020f070803032400100b180402c0c01c414020180000524543d003030061512641e00305000d180c8070f2604400180034038181900252003030300810700500803425a00000c2141d1071301894040d85403030907040403400800301900515032003401e41c0c05400c1084400e8207e01280101d120007132003252224024018441004450071403603802c01c1000805968194041c07903000c90051601040d107028990101c4c505400581101112586484060225040c10861650050f5905104001c1d6600302e4a9442d2241c4416400403d0441c0c2c00c2040310169980e60040d03403541900c0001d01096402c14640220840c1d81040401d580d80a0080d200c040e05010380f0a4805200202e046014050700011010003019002018954880700600000c1034040c0c0300e0030000d2082d43c00c0c60040c80d43c0700043c100500085000e510007810703044200a40440441311001003862283d00740d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 160721510 1250 160720260 160720271
    0x1506050307020102090901090b0f0f060409050a0605060c0d020616051206010c0c08030702040b0f0a1215090b041e2604030f03020d17060102060411011808071d011503 73
    0x10002c80c0680320f560342d1a6813100200002240110700c0340e0040501b4901114540d155106180c10b00c42720801201e05a5030048052004100d503c01c01e03041700c0d903c04a0010300150054450f8000740302a001542c107454694400740170166030b580c04100c17980d008140b414645d010700c285c00301c00812034820182c82e10300b034420f1900403907a0b59001784c03012161a5031010440f5101511109030300d176213030031002040e48903608104522810342048110b14484000141c10780c100300d07041c070180c6e17035061900000c100c4620b0000405036003212081d20908482501c41c03842480385040604200600e004810000008900c484c1582000141c1a500002200c3c03900d25a81c44101e811109420141c007866101a00c0315407000592000c1603408100208902d0440d2102144240340000c0070845000495046002d42d1001011a000c903a01e183e00000e0071005160540b203e1201003100600050994801c400b241e00030402840700c04200002c0241642e00100c80205540c54558040b84c6c0c06101540c800030306660300c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 160722760 1250 160721510 160721521
    0x6011401032a1d0f0a03060b01050708030901060306051501081f030c030506010614130605090a18060302040b030a1a0405070e13020f04020708120606160813080115060503 75
    0x2604890368000d040d19001c00701c125200c0058029075088070002081c0b20714600c401018501065030000e0030101038180703c401d9055a841800404048c81500d0503c0418415000020f0071680158440c8042a002058031455172138100c00340c0b6400303409085c05038a124040781042e41c1c0405040d07400520f90100781c6e8103240030000c1802c101d0898102420001158074040284100041c0960403903017507940f81d4882d2820843c8440c80d501501400c0500c4003c00c0c3d0f4100120352003600a030409910050001070190b5841b0301030010440c6c454082202c8da80c441b001042503290520407444600400e8010306200161030ba9501707001c0418400c40102c00080c007020070107100040101002074010004804040e0500d51045003000380910b030202d10400b1a1b41510940c0d003482e00980d2403450340b10310300c2ca003065054910706040240043c00d99070042024031030084050300c102c009d146690b00034031741650385415030440c4502c18412500181c5040e8140342944000c0d0b407200000300c0845115181c156241d0301c54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 160724010 1250 160722760 160722791
    0x5070c1b08010e03210108061f0504020a020114010608090307150b04151502030f04060503071421060301020a0203040e090c210d02010b060417030f040f0f080601140103 74
    0x201c0e08144080d40c0703050021028001d00000410301c82c8055000c1d0102e440c20341c814012102030034000c5008541280d404078040c0171146010140b1140c0140040229136110400325080ba00304115a0b80181c1d1100c00c00c2c001044520855800b403c2c05191480542c54036010b41d41d039901c22600000c2c5441c6000c0d12040c030100c0e41d07030302c810102440107106000c0465002407544590115004085201c01942c8000880c0c1d4000011100542d056030705c0d507403c040c40c003441584c11343c00c02480c0005001e0016601c20b0989503c030010300500ba50b00c000100c00316001040810325a500a00300c9002c1d82c13040281481c0e42d5000400d603412507480604800065584111040c01c0c0b01b11449003d070008006031134295100209409441540042c0c4100d94451180520807426260101300a0386c101c0b40808c41484080d080e00091034903081908101d80c64021000c18407025544180d020500240a1034010301440314000d44180c01080c043c4024001b550400c1c01041901c1003288080741416a541c8a49596800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 160725260 1250 160724010 160724063
    0x181f060902070507060206070c03020601050d151401080d090b0d020306010c0803190c0503060f010f030e1e070f0602101a12010b03070501020a0b0604050903090d080a0801060305070c 80
    0x1403100d01592100040d26007241d844003a03011701c1c00980280c100190102e8070031103200040c150158000c1140364078002c1804444600d112042d203081c20610b4141c1030b0b00c50940642c055500b210707690034502c2c0d0315000c8c04030f007040f01481d19202001810708082001c2a01c03501680c000f02c801400050f074035200e5000580c2c5690202500601e042408002c00c29140d04800c100c0e00800f04200052000e003c8080f001c0740e2510040b40d04a51160804100c0c02240d4801d40340d81000400b141000901d6080e40c0400602e00022400b844440e04525900315504442c01d002103030041c6080c08803250224100400a9280c080c840c88003d5000c0e9601c03414890045100341c402c00356031000e402c104a440000c8440783c00b030610304003054080c0c82905000103070355200240c1c8107406504803164503100d40300d10042201814005e4000202440140710f00d103d10f54034610640303450303445201929500c0e280340c44042c2c081c0005034040c03003d05140600704280190007006a204080d8440189683c80d407060304180d14488 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 160726510 1250 160725260 160725269
    0x20109050a06050105210a060903050f0d0905160812070203120c0a0b1b07020607020307090606120501091103010b1b0709020c0609010b030307031214100905181f06 72
    0x7240860030414001d442d03000031306039031094821a01c58480c2080507241c18008a10f02a400d81c8154043c50218001341e04c0b09540c60706c07070702d4800c1c0340c03160002c1000385517044036032504030702a507909d039a008002080158207402d6070145902004545851180d58031540e182002ca07448150014041003190307410311603220800350344034125441c0d40851072940e0760f6040318442103410340c40c68030100d401030380040408401310070300044003031800b809a07090108581042000b02d0b05481001d00110f00006240103520190180d9540c00042000078681d00c03080c1d61060384107009140c9007050100382001e039001240d0540d142000443d6489109040001000c04004080c0800740100c41d0086540002134004002d500e0202080341d81c0c0b0f44680606600320303081c92812961690040008000080c014003504c04540303080107001a40990b62191000980c008403a0009540c8003100d05101d90075071803003865003203941c001d18905001144900e5950b40c0711620903480095014100e10f462241c40c0350030110292 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 160727760 1250 160726510 160726513
    0x6071b08040e0c04080d0e10030903050c01020408030306092202061b100e0d170f06130c0206060a081902060f04050312070302070b030709090504061404032d0203030a0c02010905 78
    0x10703d002c074140c1641d5005030181c42c09a00070303040f40340d42c1c0602c0b40ca0300d00700c20000200403e10f050788400041d401002468011800d0000600491810705001e1000d0001041c49901031980c03407501804000c54a54002c00c1c103285581e8050b030007404051100701c60007043d58103803201a0b4810810101d0a600c0e110001c8000103485014440c3c48080c90760703008548005140400c07504121000351040c1c640405c107210024038500d08a00080c4200c1000c60a00e400c23610141401c24604144002d020641d854240400c001d13a00003001c2c4001805c0c02101c64008081c04000343c0b0300d00010228040794050070000c040c5c0729517804511180c001400380e0846000b080010210780c174000804481c1ca5043e08025010750141c01240e10010307943e003441040368464640c0d5a0340c00d06c1a814801c08400524000d80180c2d0f0155960055603403200301519010700030380c081d803504002d241c0c0242c803003501d9240c10300c00d803003042c0d60401144401580010549800c40c0e01c006c0007080c2c2001819040340181000c1c140038219 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 160729010 1250 160727760 160727789
    0x40b0d080c0d0e04140a0506210a1518060507050c011a04110c100e010f0609051f060f1d150304050f0c0a030618140c011106071b0804 59
    0x407100000b03407000803600141c4034951015200c0f03040108881d02c104511125050150006101c2503840e0300c655801b06004103282100310000e903c1031201c166910f0701e0341055214511440600900035041c169042d0380c20000e11a0011100508901c41071100300240007641714404580580c2c000e00548006500e07650081011024041c0c0c89a0405c8417901190b01441c901045650004858412903529000480050440c010210b55640c0248551042c01c1d0031550b85100001a0610034020440103002140000c902070038014040ba100c00c0b81c00034100646601050300300052074110b0070213500d11249081000c4c40f1030f641c40ba00091000030301d1000d540107d41c622210310611881000e14000e80c00381e03040b506050f01d8a0341e000d6942007600b0103590b010110318800c00024140340c129030888510040680151949070f52448800401500a00e20a0300303d024480d00030350380800828100b4400c131005003287e05084001a200590301c42d03061400c4c1211540a90600c1200d00858005040b8610302011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 160730260 1250 160729010 160729027
    0x3090509130201030e0c100c03050f130501030c020c0f0f0303090a0305061f030f200409060605190b070b0702070b07030207030b07020f06011e050310060e060a030f02040b0d08 77
    0x404401c03940d0803408685071001c20180740100003044012014050840a8a4038181d402640d04164803002207040210801410f403c10000c5000350408140d04044410340904010025050f030310340c2440300d021036100214078130f0a41d4034000d20510020059410780381c000c0f00c0e075001c03d0452003440c80054005222040000c01c01100050341441003440341088141c07100b27142000316130507030980b10191801860909600100c0d44200300701001c40340b2850800c011206d00d00104044d60032001050310b8a6030394210402941c1800500941c80819000c0c010604600f4040303030840602620502030f080383c5c4080005400340b13000b00501c002409a0008060320f03100c1c6850002d40e2001d16000c22a48402d140011941d110f000081c3d1444403050040944280d078200410952001c2c044103c40d000c003804000d0024182c4c8050149131460b0300781d02000701d0f40c1414010f4260504501a03d042d0249911020810215440e840e140d01d500303074121408244009030000294031020441ca000c1c1084000080000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 160731510 1250 160730260 160730281
    0x1104080303040f020406120b071d180f070905031b010c0510050411011b02040b01140406050304050d020a05150c1b0114010b090f0f13111309060f060c03090509 70
    0x2194402c640500c1b0117501c0c0c1d410064041d400400c000c004051520104019900842015280490440465110b40c1c040c400040ca4102941081200ca8410b0000d2081412003014284e074018000d04100700074514060102c0e5980d00700b14401c541506070307032100c0c40750b981c4a0020000b9a039000422140c5041500303403880000c0000341e0701200c1c0507030041c40c02c00f8954080c881041e601c01040710482c2c0c01c1c00c540c0d005c0c4406050303814115410014200c0011111400b504050000b4010507a280c64403840d0034a009480c00301c4010901c0103650001900c00001070300000c104010007044250481e0903280d4185c50001c0d401488c10754030f04800c14103c0e504440304158055906643c00c2d03025181243da0352007900c0c43c148150b580301e503041480300d0440706084c1000c8180e140c9122015041e081d2110403e0300d4a4215080d18800d001b26080001d0028661181c6c1a01480034000414040015916003202041000c0c042c1c03055409002c134100a110906000b03024000040c80040c10b255458508121002d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 160732760 1250 160731510 160731533
    0xd0501050c0301060f14030a091a090a030318050a170c0d0f0815010e0d050a020316150f020706030b030f010c11120705030306011128030e0d03080a110408030304 71
    0x340005a40717000388005540c4608900c039200080004450700e140c0310b851804001d848844015280000c40d0622010052902c10b151480b90400310041c0c0450f0300e140c50010140d8408a90160b500c1004815480202c0d82c04100300c400b84e64030124503254880614280d90860080798040030045c014501030201c0c80740c00500c200b501d00703210f55a820160741c0c3c0e521501c01050b56000c030300c5c2c0000c11f40b00740c207126414681c1d4100b2100307009000b110341c10026907000030301c0c2c1076442076110010031140da000c00c0310709000512013412a40e9070410440e80c003595400299070700c04a02c248010582c8402078150300741c4060000080c5d10510701c0003400244c030701d4400541002c1841844a2041c81071510307030014522100c1c103903005641d01001851a50700c0301001140d5805944170004d885000714180c0c1510720004010380756110381c40031440d540c0740456050103000d5075400f1f01943d01610910503044000780d03010320250b40c070280e81400042e42d040c10208201c3c55005a4000314480d00c00041844107002c25600710 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 160734010 1250 160732760 160732769
    0x9011418010f0329160203040f090905150f0c032503060f0f140909070b03010305010e190201020606010807180305061f03020907050702010e0607150f180206090d0501050c0301 77
    0x705100f4904141e51041d62070201c09204050382282c44c041030321a400d203c0010425a5503104490409031a44010f40c0a660079900030202d07255148114010850301384444044168071014004091071328082003840b4410082196518840000000380c0300304c001d085280031001501408030304800f4550014005180c18021048000e104038400075030303911101c15040c10b4070b00f007600d15203854502c4414060009809400d11416024255001c19908480009940294012400410700e00d8581303204a06240880c2a0943ca200080c5070410143c0d80004102d6007104080c40c105500795a001310840e04003001c802200c01444080d0800010700c400002e665001d01c840c40150125950907400f07a01c071240782d620000b908100c080d4005403403d400f44001e0003240c1e006050030740d0201440c0d800100780b5800040c1c11241000c0020000c812140e0610900540f4034407a5800c0140c070706a0303034422481c0d62041384001e100d000001600007651b11446009400b03154460002d0286050801104009810034010b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 160735260 1250 160734010 160734023
    0x20301150917030d09083606120c0304060905160311030a02010f2109060f05060a08071503090204150e1003030807030c030207020904030905040b030102030609011418010f03 76
    0x2800b0808680d580207104a8a20303030707402913180c207140290300130103006084400d49844005122602654142d00710b4400ca44242c1c0744c2c0c600e43c03038010600240701041d0321100a401170f035040c481120300d1345284c0300301500440718145141c0c5a0380d90703240c0340016141e10f00000704a40500e200e410a1401002c4031001604d21486a80900c1c80d1002d0500d03641d4809044040c0c0052820140b04000d00d01a000400000405d000303007a20890920300040b054548000003118125918100900c0c443c10901c101a00424112007a60002d4944544603a4070529805944241040941c15284190003544600c40c2d41e580940306121451910403450607054152141c040c202c420a00000c044a00c0403135000c050703980c10b4440c20490703150904101c0060040c01c100a041c0740d030070018000541e5500e881107102d0380c480d540e00032803142010140020341e080b801c4040d000b60300600505c09283e0340c0404950554501d03d002c480a0302d0010001050910104008004120006c00126620717060410910a0300d010f01d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 160736510 1250 160735260 160735277
    0x616030e13050c0313051e030a030e0a020109050411040e0a050406050c0705070317070503070c060207050315041b0509070503010509060d202d03010608032b0f02030115 74
    0x5201c0e094032002c83e02148004010400500c403080f96001c90f080705400344c1c0840d0f1032100e58840c20100540f100344184031503031011950403079156041c0110aa9512154041c080780b440036800a800e00e41c56009592240c1d88421034510500020002d5500518903016021142d00340002010001d007000da50541d462814440041c44104000c42120046da5120f0001c00390145176031501c0302481e040c0b881142d980d42007004420b0100e0420800b0308060740c06414514803891038510302a162501d03550115000c1d4009080001a000d01142d23030039441500000146007407401c4880c2a50002d10f141c100c5070b400318515042c4040164840d010b1410b85200785ca110600752100000c10181c5002c0d443c006050482c1541044441271310f45074034080117040500440c141c81e02d004094a401c4040d82c00748801c060352888059964a4240030f800b00405400e4041e5103411003103030300400803440c008100b0f641c508080d2010b91000c011584404008504000c04540341d58603000341941c40981c00c0700104c00030b80c0c0349 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 160737760 1250 160736510 160736539
    0x90f020a09090804031115030c1b0d0c03050306041b0c030f0c080f090f060d091a070915020c090703020a030e1c0f0c050a052505060301050f0616030e 66
    0x81c0b00b1816015042042103042c00c3c0f440d55024100104280e050350003c480c07200c040200058000554001c7d01c4900541c1e4035000d9401516282c00110290301c409a4040e000c4424801e0b000480114195054a0803603523940d180404100a0f000c3e030000c4e41c2c0d8254580403130000d015803004805408034801d03a1484d011300700c5c11070300301e03841d5010b24006040440104100c855000006000f0308072190043e0030440b90030500720000d111500500070003403030307980c0b105808420401c0440b05522000c4009a02800904083c00000d1008040d40540f50420901220400045008111801e54544014500c5030a40341142c0e004000e9048810510086420802490403180010074600c0d034036100804a6040840c6003c0b0803600a00c17102004030a1010850030600800c6c130911400c030840e802030700104661405c0b4014a02c0310b546030a8200a0742c1c01b49803080c42280c0d00c10301283d0454004540d01c079141428040020894480e0f04002c2c0c0003000d080300348030105a0841c8511466103005ca0380f403044c0d910320703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 160739010 1250 160737760 160737779
    0x709020307020f031305121504060b1311040302190e04050106140d020f090a09021512180616260403030c0908030f0d021b010e0d0e0102030904110d090f020a 69
    0xc201e020b444a0207480c9050206d81030007200300c200b1903c524111a100c401030321080f00b1520040d60306075041034030365096038142d040800842404503991441000758140d034046400d920301503400b0081c071400400314032011002c1c0c40300084015011503a00c0c00c1e094200b40c40d2040c003c203240d00c41d50001007030b02801c0110614081500c540d0712a0060141e082e1210b0001c2000001c460080c4a50400c5a8440b0b1040140c3c4170700c070940a9002131300b0401030ba0f0724000000315100c00c4000700303800300061613020780a440720808107240c0d03000241d000c0407040c0703a110b00c001a0790030150f1b4000c403106414071b95910000c6400c81524180120b0183c0c4003008201c20341d1a0440305613150780a00100341c0d20030400700d252607400200400e80d1035041303440107040c174061103900540c0100c80c0c1000d0b0000c0c0e4440700c002c12010000d2200311400b0025007840e54079000c83c40c001039202c6c000c14050500c035607614921000500c2804c421a01e021065400402c03464065281000c01071002640c242c1c042c100d07040000c1a2800b8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 160740260 1250 160739010 160739017
    0x712020108070e040e0d110105060402040b0711010e120604020906120309011107050907080103031e0804020103152607080f1906020405030a06020304060c0903030518030705030709020307020f03 85
    0x8060791140310958840100f654042c50032070200390800c1d035422003640c9840040c0007141d41034a40d07030b642041b01804035a81c0ba095460240895100c9c2e07104100030494001b00c4012140c802c1c0d4010755490003004940d00580700200882400c98119000d44820103050001141c514490303403007214121220340f03401c010b0110641c40800407041c02d40c070800c600754166000d0000100c100316000c007103406040e151b40100700c14140a888a5012900700300040c000c143d0080000e400c1400440310150000002c210300400101e009403003e41415a0350b05125513031059180060040c02c075100c040700701102407103080c02000c400c51003041c2a030f010724003011a014001190225001803104002c0c48202c0f40000041154489400c0888a490b42008002101c0d01c09000d403901d101e01501005890f89400d0500100b030320006192001040a6500d06000180d0004140c0d0300803520034048036840c00054004c01d140c41710b9504801e030700d03100340307800080c0140307054004503c02d403c16030a41e4644141007054607034900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 160741510 1250 160740260 160740263
    0x10b03090f0604110f0607120305191104090c0c0b0108030d1116081605070608010906090b15030a06030609060e070f030c060302031b0c0f06010f030b1305030715020c0712 75
    0x10134150120102d2610051114010390024590341c0b408102d99500800941c90400d443c002c03070b440e5800c00032902400b61030b10f0002c800400041c0041c14a6042c007403164072550207100d03050f07955a000060315501c6945505940c40d4460080000c80d43c44a034090b5a941042500c5040f07142030286900c2890710328000d0300c4d2141c00300a080c0706500c986980d66030729504101c1140c64064000101d642c0450000c009103001424503440b6000c2a50410800340151032598002d80246814550302c1c1907140c0b15102100444029413030718070345070345500c1c0d105409046954406440c580c1042401014820b6030360000c1c2c950714100d82200c40e80c964815050044544920001d440c2014510080100c18080c2d0010755121581100e0307032219550380440b401140e0400120b0100135413100806400840382000707164003528680540404540c82c555030084d00307010083c61100700c54008412401001400c0099a61140c2d100c140c210349081c1c01114030000b5004010040d20314130450500203120040c0940c0c0710b0700a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 160742760 1250 160741510 160741523
    0x2071a01050109052101150f08241303030b030708100501080a0201120507170f100f0503070603150b0a0c050c0d1101050703020c060408010911060c031603031103010b03090f0604 78
    0x401440b1060401c680c0400070505d82d9500c82c0d9001e41100100d40800e400f8040b88150314058074140209689890140074400f8840349003840280d800d19448400c140d40a606070140400f000024a070440281042d02e0701e41da05841000380c0400c090202180030350150f4019802042641e0b0798214441d9982c0200402038041900c1c101200b240841302d8000540c080e043c2c0c02c08030310825880480c8640301d41c007111840747c9035030aa03060040ca0007003a101d1b80001d107944e0490003031a50810300000c0e214110761151100341540d801008071550b0320918803078001c1aa108115403601d050a1000c0c00a886207030b01140d1138004ea4000e106245002134003541080d4001d003620b0101c0524a0040d100f96010b0142a01544030706034150005542d17600080019002c500c001080890141ca812440e007150040403910465040c090f074114004000160390b2074400102200d0503050003410b040d00184005002d41048001c0080081644032101009502500395601183d08210449034140d45400701620020a071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 160744010 1250 160742760 160742779
    0x7030b03010b0a05100518130903120902011d010210060602030406021207030207030b04020d0c0605190809032b0e0a030806010f0801051306090f1a0a0e07080a020405030102071a0105010905 83
    0x4086c41140070b13003a40000d00035a076490400c0000000e4000400100000210b07444401c140e00300340d0b02c2403142503040100703071041c44038042590010f070400e41c1c004070303107609010b4044d50040740ba0310030001d441000088450402210b612060004c8d04e03588607000e07401c0988680c0200c60510083c0d40101d446003901580604045411650703884103440c005081640c3c0142c0301d08143e008204000c02a20040c0300d9519000e69034200d8445030703295032012202d01c001f417040c454200f0215600100c00c0f10031104101c0038064203400880031807000c03100c000d480d41000a1600c0300c0c50101041c00507001075102c1c06174035507201c5595074400446180404005680000761000010403903400d2000030600e03402c08200c030102e0003030b455040103030450f0000d03403690f001d032030711040201c010b1200f01500b242110300681d440c0d5400c0d814000003203049240070f0150000c0226020000b00080392031f90540340034140003402550345842e181410303c2c00f24a58030040a1590746680005541d600500400c4101d41c000f07054040b8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 160745260 1250 160744010 160744039
    0x7050f03070e060d05070c030306050303070803060d0503040e07090602101b0c0212030a0306180e030a0e0d0807031101050106031808090d1b0603050a020702181504020307030b03010b0a05 82
    0x400350081d4208940010f0280f25562042d000390088510075910381c3d171a040a045542002003c1d0346440d409240170360410072029010601820850707521030710036a002148104940382080c07640c443d0381d00c280b402c05060310030b0010165110300300008480d6079078200c40e40018040d040504484041401d21101e100c10102c000340c003400740b1011103001e03000030b0105040e10420089182161f000401c0c250009907118000d100810985c0c454207680309414004010103040c24450076501c2c40741b00d40c1801031101480c40002c1940c6c40d01c4c4880300240c0d000c441d02d0745034089031501030109000b51101c4107182d424000080342e660700c04d2091038001c803420420003500000b240c81e40700c081c0d8410001260031030a0b80c00c1c03950110f4040310b045540d69402504455085150080040417104043c0c503d402d658010090200983d80d1030248140000e002410041e40c1d8441d041c1d4403072101101940c440c0c01c5030020081041c05da40591000007103030001e400a002c3c0322082c004010080340d040c02982e0744455120700440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 160746510 1250 160745260 160745267
    0x4120f030605330a020109020414011406160c03060c080f0402060901051806040b270f10030f090311010b031615090b12060f040207050c04020f07020604080109020907050f0307 77
    0x2d80203120348940c4084a1a51901c0b100c6510100760800540c7d115200002141840d00c50000d0100701d10014425550400501040c07654066210910406000c54040390044841d003001c00007503404981d01e404599246048005040c81700b82d4a07012074840400501e001040019040c07003150300400c150b01d4038594500540340380e080034040440100740d4040c0c0d1201a00c42c1c0001f48007502d41d620803d0344910481d5480c40810f01c21444034003202540304010181c0352102005e240b064a4111442e500800b640141100200305403648115140e003808000d8041c5034200c42d8101c00c9005a50080c011400043e05042c0c0e50000d4007c0480350400c810010810040041051580070010340752110303215a1703071900c1ca00627030000c09031030402c6081c0c2801d100581c6402c135015204054261425821304c8159220140c9800b242d4021a0044d50009014101c038605001101c0b40c0741d0b070080039103441e1038494151900a150f403460890040e0a0800460170241c011000d0390860101d02c205149142d40710341d000c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 160747760 1250 160746510 160746559
    0x90a091404021f0c0312060f030b0f1e06040c0e03032d0a08190e0f0318100e0103050903040f03080d1404020a0303030902150304110a05100f03110c030304120f030605 73
    0x1580801e59905022903500d48c001c00c0d110040d402000a0754050400061424851034040d01c00f0121850340401d04c56034803203114469600080440703001a00c0811040141c40c02035118040e00d500d4080000d41458176030b50b02d41200f640740d40c0c0c40040703004100083e080300c01b640306175a01a0701003040180000c030a112a0f035802190074580020108216102444243c544251140d00003200d40003c691102c07110a240462084604100c42c0003210313002004010f040c45e441881181d0425171101c0016500403010411580144580c010356001c056881c1080b40b02c3d500611041c1d200039007420f52aa40ca80c1ca0040141e018940080410035141d143d03070390641c000d10f02540100c1c0c228507800c50340801c0030762039006984a10300511055207417034000d000700101040356400661141c41882601c0500581c0262000500340e0a41070004101180b00321490441c005c4801801052000000300000c200c0c1e03c80b0110010446c0e6201c0700001c1e62007003001e4007a04d44034000c0c0ca030010b1015000d040d1a1420040780c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 160749010 1250 160747760 160747787
    0xf0c060d060e1312021507110c0303031602162402010e0a0b09160f090b1306030303140109050f0a0902190306051806040b0705090a091404021f0c03 65
    0x1c400c0d58815640c0e060620440e03c41860103a00d840e40c005108203801900794000c01c52024000040b03004000203000100500808100701d8452030546c01700800304020940303484001d003265203a10304219404000221450280018084c6000d80300039210541c484805648620a6035031082c4485045101c03025040d4036510210342d01c40118844c000c8091201b244040c1c011034030604589801d03025140740900c0b02400807402600841c0030000e1400c0c0300d10783e41c1500c86a03540458000075080c00a6043e0001040620a0601d0200000b04043c0c1545c002c0445100b42d03803801402d6a80ea0207880111041210303503d600c1d8690500103458100390381c2c441400b40d0701c001c1007075109807002028180520341607082124402d90710420300003050700354419100340080c200e00400c10780c5000d6803440303079440c4080c3c10282800808294001c00341c0c2e0701014103020b844046010001c080120403d00d903460003d80e0140c2c0038207a00080544003590204a0884030b064646400c50745400c1940c0444518070780c2440d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 160750260 1250 160749010 160749037
    0x3040215070f0b0412021b060c0f030408030711150a03090201031e0c1b1e020d080a0e04110906070b0c13030507081606021509070b0c1e0f0c06 63
    0x84403000070b260355000050940a0030429142e0314045c94080c099201001080040d50f0041903415508148200701c4041c2d2a800c0d0380840d100c01d54018050718085411b007400c20503010114000c0f034181000005422214050343d00510340203212410300c403c4072010194a60b0030300c0100143d815081c00b1360400c48034140f0600d000202070007510302d15a4000d541444441115803524480340c0c2c6141d110701ea180b059210169000502071041e0f89800090b0201200c007802a44032990314025584d9251881c584c003500075015070350342c611442c80140310f0241140c51500c503d01d4201e0b4005014041809d82d45109400341485180c14103544510742d0680f0000c2046014590802561610525030420b503402184140000d2a07001d0030268110b08082444100e4000c0d24083c0e04100111035001070000e120700c9504c01c00c0e04540c1c8400b4646814149503420150f82a003001502c0904400e00054492030000004a1083c840031042402030b00d8010036001b40000303500c2092400503a00d0b140008204000a080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 160751510 1250 160750260 160750267
    0x100e09040f031803060209030609011104170304050315010603060b040f0905090f0d02152401050a050706021602090703060803040923070e090a060635010b030a0c0302090603040215 79
    0x10961050f011903002160403580124085040d41810080c944e0410b0b0b801d0000c1c8603038007103449080c40b28060740c80b446041e020b01c8000b80d036101c3e45c00d004641c00f41070060143c6880440281d03000c0341c2200b0a1180e02c000900e0404002040308064046e5800d40e20780c20701c2488070a02c2c00e4014006010050300c186494082c52010602000c003c00030308080300950303000f034003a03d0718a8220b58650200104018480c010200307403840c165001e440c0072140c1c08801d00709652140b08200301107620b401010401007840380700081c40c0b110b07450b00018000e0454400c90b5402c2550f51125802c03800d462551050f4510b5038401c1c00305100000c880c2d00f15409055103131b09160f01010907000c05090100c070584400380072401510701c8464600300a00340c0c9602245100d8248551858003500070f1241401c00300091102044c1d11b180a03002030000d041c03031000e10200740681c0c0196100d030840354542e481a0b0b0303410782540c03415007110f088500a000323481c6101001001c041c110303500c076000c1c000220014540d25072000004c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 160752760 1250 160751510 160751537
    0x52a030f180d1b0f030f03030c0917060402122a03030706020d06060806010f02150c040504051015180b0f07050f0309010e0a151103040f090b100e09040f03 68
    0x409400d0b41640100411181980030204070300032000700360808601c0210155091021800140b91080e413240e051400051800402c0001c5179083e03007640040d0301150031141d00c8070402c00001509030045000702e40c0d0b8401c403501048841c5d559100000690b0858203031f20303c12512404042814070b40800060b040e0383c60b120899460b50304982c0b0101c200d42c241940c840013444559802212154440d0080c01e00004809200c88042e5a46841e000e0411a040e1110001206580c1d030303600361801042c01600521550800300c0c85c606c0c00e91752502071032849601180306099581d104010400c0050450014400b01500f0b22000c0c00c0d40754807890902c4c0d85218100301a00c0001c004205184072075901002844e240e0041c040010300108151010a11aa00a450030b00200814083c00e4070480c0d1182000704200103500c11450460245510120b4009442540001c0c148456009181d804208440044020002880984005141d04c03102c5030081c0b641d0b400900003070b40707205400f44981e009080c90484403454 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 160754010 1250 160752760 160752769
    0x6190b1201030605060a0b0d0e0115080102073c0503070206030702070e010603060b0d0b030a060e0d030e031207050c010b0301090807031805240702060307052a030f18 73
    0x40000d004184050010002e0018601c19990010800c03900c2c031410510304108070701c0c01c0c020f02c1c1140360010307179407504125560400d52005100d80c0d0704803e00c10181b580c40c13002c28004e4102c40010b032048000601e002c213070703800f403052041d9245110760701604400080e40d0000e4541e071912842100d651000304403180c0035070b842d8000f45205160070703401440118140384240d1030600041e130001e0241401c04600780b055000c140c00740d07040e55803a88400111200c6640005c0c1c42d1507c034550142500e440c00f42034614030500890416010b40c0d09880500400310f03600300250341d0b48030f5920320308e002e0502c80010541e40751041d001854904050750012610150000c002821240142c10490704043d0001d07003801050703000080702521a0307400391020305881c40e00c0c01099081100d01c200c410740080c0340300c4076555900520b0944540d150081c1080b6103c0ca4000000b41039988500e0064086095080c1c951602d881d0403061449403601010103903042502106082d000c03a040452006c0d113180040c0920407241c0c66 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 160755260 1250 160754010 160754017
    0x30506011d0120060105010f020307080d0c02030721020d1805040903170a0c0806030a021e040905031803190c0302092503141305060103021516030c171206190b 70
    0x20f0b410082c00055142000260200d0600c41c48441590010301c02c03500401d8401c4140c0740720041070b000100348074405501c102d0551144500040440c01421000c0350004a032510520200559400b07c81246001d42d20a1b600b4007803207480c114541400799414000c504154106140c100c0c401c0c10b20b070800e8008c078460702110b80e400b00c410b02c0825a0795000046130a0703000c9540b54000034240c01611004031240c0200d10300e41012440400d18070140e1480843c40e0b00c07207a000321042908401a01d49894a10201a8041c80c10980d810712a1088400890078211000d1208840d10b0780040f0a00300b2500d15400d20981040c0141410012941c598100d6085000d9030000310845005940000b03040710b20403202001b1110140200c04002041c40c01c030000940001445419a80c048031800311a04041040d50001d01c0f82c014034100e80e0312002c510408154111401c008a58440d0b45030001440982880c183c0798010b00f400f00c0070310707041200072449a0829600503030ba0100c80d0005106455164240e4401e240e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 160756510 1250 160755260 160755317
    0xe0a05030d0b0108041509050f07080606030f010204060f03090204060f0b0a17070203041202190e0a050a0b010806040c12150e060603041a0a06080a0f050d030506011d01 74
    0x100001041d0007000264070401580442c00d0800002c00c1c20a0b4031952038652441355034040e0030741e40300d48010a005d0100b00d1000030643c2c44044801440e10741d800760f5181c620a5034554040c0c420f0f500700300e2041e04180280c0b130540d41180d413880c8103c180c0040440c047d00d14407200ba60409e650b442d000c1460030148020310080d04050304d0b11a40c4a00e40d0344020b00b01d000c5400201c12168000c010301170103c0d130100458040790301e03009110f49a07204034000500401c449000c1442d00301000c2c00b00040c2210124406841090044000c12495444050a10540e40c040704200d000511200000c0c07107900d03107075001161050241c40c0141c503e0542d0045a0b08680c000012440ca44500c40820455540c0c0401000c0c1d1116081c4e44460075820507a40f42034284458400e612074201c003813000500400c0781e5a210000408980d0304850b404401420000014204240e003600c0901a5918440b1668040d0103100d00644040e5504840e2030360440c410f96501c5100e0364042e0401040c4240552001c007071808588095 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 160757760 1250 160756510 160756513
    0x504050604121715010818120d0f060e040210030207020307051011010501170d0207120f021801031b050915060d02130801020c0124050f0d05060a14070905060301180e0a05 75
    0x400120001400000c402084480b507941850b111a00d03d81010500003081d03c60300940a0716180c0315541c00c8041e0800ad5a90184180341c8440042c1851861450b04c0c0035600076140c0c155045500700c01201a813290800c041e4041c0d000440c100309074101050704420001d05850040305114040310032500752030382a8481c030320f805d480600e032420605042c807507060b1001103400100019031074903401c0400f404450901400c0c1d407203c2c09100c425512401488150304510044c0075a481da1240341003107445052016207a485590004082000d0408414450041d80242c9020800c0d0101d6010050182e024001303510300c42d41c091001d529803020b5112004013070001071001507194020070391000c0c04c42e41c0c401c22811031120000100c81800309c2c5503400c1425917105031800079145c11981e0209084d0348100c000103095100340000c00186002c00da0000d9030411010300003104540740c03000125001c07019400307030540c800c000700700400c50056a034010000d6002a80c1011a11101e001c00c0682032100080c0151000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 160759010 1250 160757760 160757791
    0x4030b1302042a021c140c0106030b1614030402131a0409350403030c050c06041409060a05010f05070f080304080301030302010b090411040507021e0c030705030105040506041217 78
    0x354041c0209035505050401704080c4880d50172006101c503149650020300d903000084c0060a00f4400e42011000c1d68201c00c8650050034481d021074400744150389000006407100210070403a2512001720f074066a001040c030428003072003010304402800103035480c440400300c1c526211400e807900d0007103440c40742c00745000c00c1050114081c000d0603100200440904002c801021054138007110058034260781d003500d00544070603800c0c035109240184901c0d84030341c0502f0101c0c00142d00910388803120b01c2c08006031003001650300e611052111241d114011103020444040860f842a44603402806100303020705800b820f600000c3d100c40c004da510503102940c24000000041c818107809001d03032606e1000641d010081864981c8600709801a1034046078420b1303840d400800c04c614404c2020300309003481c1422107a14400f40d507004c643d4803401001201d000c0d0040314000211480c0610690f8400c81e01721003e400a641c5540d640c0360304011030207904090206a02c4140b00d03421056090758407854034074801009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 160760260 1250 160759010 160759091
    0x70c12031d0c150a09180902100801030206040b0f0403060204030302061008060103170c210a0e061303060c0c060c020115080303040c14040b0d111504030b130204 71
    0x80c0403001c03070180e50040d8000c0d90b0b50220340c1c6508080300c10202d0300316035407a12849100b00841d607682280d40290302000314503880c0d06040c00c02c1d6111518042c82260f8080c0c401c10140002d1310054400d01c001b941c011000d000c10444085420010416001d0f50102c891600762203640d941d080f41c005810950059110b28100071040407481400c1c0040c00381000103000c42c2d807450381c860001c241c03104200000940b004c10101004c80e810041c00040001c8a00e188141000c202c0c1000e4a580155a200d00082e04002000841d810180115000a6102041200c1807800c54481300302500c1b5096102c0200801d081d4080c000c903140344551640140c42c1c1c1d00114074200550907800780400540c00011070b1b03405c00c10a010008860801e103801700e901c0480315122800c10b400000e801400420346068000c5920001101000701d01c00301c03031400d8001200c404061440c0380001d2152030080e03010041840010710042000201e02042000c0034900c014404600046408440c5c94a4585486180160281c40200c0d92 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 160761510 1250 160760260 160760291
    0x18151311031008030f04050609010903140607030f110306040905070e0c030f0705040503030702090702011b030501030c090506010f03020903010923070603020307020c090405031911060a06050105070b070c1203 91
    0x1802003c407007000310700f07141c40030442d06010f01c0742c0e20489106c1d10300080c03d2030482e401480c2400045800128078100c01002454003a1242c00403260507000910f440754880c085101031058103400d41c1c4003103e0509640e9400300303010081204076001d45141c41040400601480403c1c40c06100e48140e03000291241460030810350420000b4000d2130030f000c0284018400c94a00005841469804070760381c008035201d00600317a0044c20007441c0f0703661100008001c0c0d61225010340000d81264813800e0104003503540d503d0280f049600030707180c00c1d00151026800f0417149100360040c4c146180000c0000440d041706550f45001280806644100405c80100c000f58840d818403105004040c07504065180d841e1009000f511040d08040540c402c009007404a024400208207aa10051107112068070b4007010a10242c403480d2030552030f0310507100e01c0000500c80c441d107008203822104103841c0c40381004850341c2d45101c5400c000f8a02d004004001c014240400e0029036482c0c404255610000380920070340e8401c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 160762760 1250 160761510 160761541
    0xf061311010305040b0403052209090209060319030c0512130501110c090112060b060706090b01171c021f0204150905090a0c050d0c08060f1815131103 66
    0x1d05261400d410440403520a03138401e03600982c145000d036503511554800c1e014440c0c03c00c0400011a003000c0c0302140f0480700382d1100c4101d070300807114011035a44880800d5902e07031642c4a1207041b40c00b01510301c07001a01841284084610070016540030560403121305855400400700c1800182c0f914008001d42c0d600451204014121300015084901d28000800c40c0301d201846000402484030a020090007400e91124860304401001e03e0b544846034288030b00640501c20f4144d4111142e0380000032100c7c800e2140310b4005c106c80c0701a200c804d20b54690980101a080010300039401025642100111200c0002c07544010b02e000050302c6a0800c2e4144212100e180308034010310400c10024031547d0340b00408250700c10488040880c1c102e0850f041142c603030180100c440301581c100035114030b005800a800c148115000c0d01c0c0705e00c0c3e41084104200405030709200811800b442003001c03403c3d050034814000305a00780a8402104502003949002c1102d02d017008000322081c0100a00c6105000740703524 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 160764010 1250 160762760 160762793
    0x312170708061201020901141309060e04050106121509030e030a06060306180c0e04030e060f0403060f0c1e0917030d060b040503060c0702180a0c0327020d02030f0613 73
    0x3c60506e0203000002e410300d64142c01c0c0300907a0a002c542100802d004040c8040504035058083c4072440ea2203c0c445644003050320122450750030100082184600c0500c0c401c0707010342000b844d0900701603994040e1b0061560301c90503000c0200036442d601c150b803020004120300501ca41c01c0083c0c6245035050083c102c41c1e140c00b042405003014600000410403050310f0b601550300c0c103000980300e41c880c0d2a0a592124900305041d80052002c500505c00d8042d240182080303a0103070354288000c0c48018640003c07900707801003500109d0003180802280443c003443c08200d01c0075074240205ca5544602888020090b15000040c0d25400010b0f2046003000e81e00404005201e039110603401c05080c04000b0380c480e84010300d071120b0380300c1c041602c0c415076560020544c440300c0c0a4280315910b0401d4000740d0041d008210b0400003180c1040346c0c1e810b94141c0e560384140e2913405568600140401ca5003042500c1003152000d907854410828401803480007442901d005010921300040d1901c2c0d5031400e4405d0401460341d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 160765260 1250 160764010 160764013
    0x1404030c0203010b240f04080109030507030e030304030b040818030f0d1e05030106051813060501030c110309060c10050915070804170309030d2f09030703121707080612 74
    0x94880b441c0ca0400700705c08404000b500c0d054452011110b8a519401a64402445582480c6500091540013401005454060f030354080c1400180e00505607284100e04c0f008083e403040134000380208040001420400d60f900280001c0c043c00040080d01e08113a0020f4800c80b5000812400310b669001491800440d1b1203a4502281c014001d40127045030005103e508244040010260703040412005d9442c042000104281c00d8202e01002090017002c650040d180881d00d0498250140c0f40995a094100c0c40c181006510b860154820300041750001c540143c4203100d00c0c000800c011615001d042e1140c1c21103001494201d141c01c00400400030042d02c60000d0000072014000403807140511449910401d034255541c0c2d4031806140d070310703603c030b800055481d40c0d1170011500400300f8030000042e05102e10300c1c146c60700459001c41859181c0301d0604981c6d410341c00f83d078040000600c0005900d845220900b807944c507011492030307140c805040845855001030f04000800007107180203990b001034110302c8c20 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 160766510 1250 160765260 160765279
    0x50f13181a0607030e0d050a241b052208151b03130c171506040e0604020d030c021503010303140403051b130e070306060b09130f1404030c0203010b 65
    0x80410850b00c507854000d800c0009031410f9405c203451389040c034032040e584001159540c03181d03402c1440360781003101c600c0f15510400c03c4a040e40c04000340070704800010b140a0f00042000c881000769420303804091310010140d001061417440600700c1d010b8000400c1c1c1440540711015840c41043c0003244014034444081c1c842212010342c0c0d60514059a50003000c010504a0545140c10b20071500d80d585d40c088518020042102201d420020500040402051003408a03685860b002c0100381c0d00c1046041405a100900040141c42c0ca40c00d880340c1d0314024205440c500a60f500420720414201301c80303181002c0d00000410030141d10503054160031040e0000d003414a8110760b11103072141e08607082402510102455054940d41301e40d480071807064210810440c0d846c00c1c8040588800d82848191102032500b03200141c451414401c8824450005060b00d001881800c0140d000f000c605408090050740c40d100030308003d00340002540118002c0d2504a092200c0341304247c20350f01702450f0301d4059005c14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 160767760 1250 160766510 160766561
    0x50402030f012304020a03150e0c0f0d0e0a05060919020609040f0b03010e0109170406050a08040303150b0315030c130b0d0506010b090109060305010605070201050f1318 74
    0x4140741d41514000350b54100b5180c001110010f00f001010003540e845440000c104407a5605030780900801003401e20030b28180c0355202141489846c0407101d03042214020801005800d2000c801011650007203c0001800b0700030011003480e012880342d045071242c1c40b0205009080304204a078079180b02c07694107641c00440c03550780410524011b054a840c0a00c0d00d44501913030994240d0050740a015000c1e000f00000742e584441075020f818280c0065400c400600c1c0c14441c240180300803281961191380302d036807821085880450b80d01000034010b904155907450a0259641c1d030081c180d000b000c00c6817130315450781820300c1e4405484040d030314407074440d521402180800e515682c007028031401c0c90b8000001c241498201080f66801d00d0f22000380f143c0101c10001c10070021100103015504805e030307504800e07a500e8a20541c1156028080d080101d0000c3c80800700541c4074400400c900e200300c0640504027188080303003c42207070032034100960030010023040010101d5544101844001011704605891158 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 160769010 1250 160767760 160767781
    0xc1c181406090d14090102011d0115080114180727110a0c020603060d050708071703040f12080d0e0f1902010c1106040f06050a0206060108071205070905030106060c050705040203 78
    0x40c04158080e041002c0f070080c0e991ba0003035200d00312680ca40781d2540c403401c2241c94902e000345402e24050100450710500407800d07000c14071038500c902085410300011500d6054120341c501e0750220300000f15125441c00414200c00d559400188150024020f8000070940744071030050741c00205941880440500c15200001d031301600c401c405680640e48142d90361104400301c0c03400f0391208009000d0744100180044c1c42c440c000358402c2114000700003400d5087c0c1062070251248580d1241515060901c54181320b13041c580001c1d88403151240d040301340303840402280d0f1000d82e2429500165a5000b821146103c10340610100e418440d140c0b0300c01d014a4000d81c0040d010b550b65060107484aa6203540c200c02d80e07107401e41290041d081d881c114070b180c144d039000000c000d5072119030703800c006000c0c0402044055010303100c3c20f03000380f002e0303100c604140305000d00107001860000c050604000c407408001900d40c900b0f11a500c0501b20980e994603205a49062641c9085d80540c40382d80168410010800701844 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 160770260 1250 160769010 160769027
    0xc06080c070620120a050105010504120311010207020414090c0a081506060904050108030d0e1614032a04050c030c041e08070f14090c1c181406090d 65
    0x1c0c08100020800c0700314000f90140744603803c040c0c0d180700c0c0c0003c003a00d90003100303545580318181c5101c0074002a030300c1b4401110b060040d403007030100304ea408601d080006030289018844d01aa030300001800e1900603000501074812140e01d16034a01c04650502c8039904d8240180c1c10041000e4610989007440c2c40082a607540c2c1803500348004000c030320049480c583d2800221845444c00034000d02103035031100081916580803610074040c0303e240012104082c880810001e60190011760710094061800401246000b00c841d5141d5040c050080c801544140c07000c500da52510140c210402010b10000600c405c944010700744402d1607a0602c100000c0c82c0041c0c0407074055500f40030040440c03801c1c0c203070803509000043d045080c0e00e0082c12804030b031041420b00300d041110600702820342051260000e20041910a80d000450010100314408944101c0014002289020f81c40020025403200d41480301083c40c01c0c0071a04800702c800d44106160b010000c0d290461032100103050b100108c50340c081d01c20303403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160771510 1250 160770260 160770263
    0x20a030206070c021804050708061302010801060e01051204060501081b100e2413090506150315120c211f110c1005010609052202070f0503070c06080c07 67
    0xf000b843c0e03c0c1c0854882d00000c51074080e84400c680d81c2800c09203445ca840d00c00300c0c024032103548180710020b4114070300c40b9050040141c0603120500e09901f444402c64000900c01d00f80b60501404020226811400941c203d21503800b4000024565040112249c20100300501908030070b4000300b04074401d551081c800804021780c43c00c00d88582c0c031850000ca00140045401c1c45250050100c030310048050f07540040c168032201c0445110340e10b80741c1c56000203d982c10307140e25800580038107020142d04146001103412096a541400240310214002900800703682540ca0294001081c0c614582c2005000c42401d01c2d80481c000b1622118240d201da07482c9450110010040f440c009902e80d01c1045501c04411f08042c2d021180d030303812040c86019a81c01c0c3e003031540d0300b1040c81e00000188145c411442c05094880061a560000900c010a004000042c01700c44d4501d650030001c040000c0c441103072070303480e00c2c0c402c03c081c40d1035124a080000c440c1410b917200300144450141009a01d0303001d00100d0700440d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 160772760 1250 160771510 160771517
    0x30d052104060b10020106080606010809100506062209050105060913090606030f081e0310060e030c04050f0a05060d0b040303150e0c12010504090201020705060d022701020d020a03020607 82
    0x2681c550405001500f48400c00b103401203110340581c040d5540c190492400d4514500840c4d841d0380b960001116502011074908080c0d410010b05500c005001c1e41080703401c2203000f86498109041c3d0300c25620312030780812f1030350b000304c42485080105c0403040c01000d005020407900a82803141c0030f00800c60300140d0500900c6215650500071040242c207030700c035401031600200c1520f1124a1898012407035844100852681a030100c1c0301184007035883c00710713407041e56000c44000c040d500d840801c1d1110a5120107407075060050701d2140f60641c485104691143c400c8441c542d8050412000074000c07a03034042c100301e0041d1402d01d4680f01060f443c1200f60b400039410302d80083d000c8100e10480308141d100742c00c400148004002841880c28040020f0aa0b1b80009041c54040f66a500d01700400c8510045009002d60440320041001340f40c40c07405081503a80e03600015252aa5000c5428194004007041c0a03150044401c00f10841d6070400010751070715028001130010700d00d640c401035603e4100a0450080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 160774010 1250 160772760 160772827
    0xa050d110c0604120309051603110405040203210f0a05070311060106050306010e0d0203010c18080109260f0c2b08010311030a0206130e06031207150603150902030d05 73
    0x40320310a031b0001c0c0700242c005080d02ca40014080b05059451018032081d940703c01c03040044500307490940700e0f682c040d03a170080c0200000c000c03130004600100649400410000d50602c00994000325100041000d00b1842d42d0b0503641d44090700c3c016150095458414103213900140c014000207810204594110f803003400d021800703d64400c0003038422020304e18000c1d015420010340340002c40d000320142c8100f03601500d000485945810b00c10f42290803002d8060b0000903003004154003007a10480015058248410040c90b02d280442111019440f004134194554400b40c8415468275420074060044409070002c401240c840c03010041021106000203403000f80e0340d140b000415a820001c0b80304040d0f0282c241c42d01e4400c082c0100c0d101c00200c0c8604c82150f01004001650341c0780100f840310b0300b10082c100d191f041c44000e0312060350f991030311071010020760740c0c2d00b0000c000b140720030704808008943c0203800f040c50303003c61041c1341c28454041601811b201703051044000e4001e0310902c1490a0313160b4403c1c080d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 160775260 1250 160774010 160774043
    0x30b06011112120c07060f0603020913080409051012080702030105072c0402040503070f050a0f06021509010603140a03030b040501081902061303050a030e061920030a050d110c0604 79
    0x42e44621640244050700c1c01e1081da80e800443d400150482b4001ca640891541c0c0d0fa645050302600c039501d0043c400041080240308091855101d12303004201c4042c1c0406580c0c494025950718031030001300361845000482c243d02103241c06d010341e5034003600d2031900c404c5103210300e020780e400000c5107440700c4010009441c01103032a441c2c1c0d40c1918020140142141c04030782d41d4544e03101711621140a0640501da06601c00300b2000009403851044810a0307000b06902c0c122036510040030039000d040c6031800d549408001002c121401a91071070450b05401a01c0c80315030501d000380895141003080e50081d42414010810518040f0308040c046d610720003190b1950b2428400901180f15801900c80041e800b06008018424000740b628136151180e120011840040130400101d401219900122803003034840ba02e542c1032050581007002d1181815242c8058448010a410354002c104084001800410744011040a070f004000340d41d0165041c092425140e260b865441d910010805402040914041c41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 160776510 1250 160775260 160775281
    0x16020f030109060c0914030304030f14030c010c030507031401031509170409090209090a02300f060702070e010f03140304080709020307030b011704060b060d0204030b0601111212 78
    0x4042035000f8002c0141c40080d00c0e0140805219000c0d070600070b0078501401419083c0002245c040c0d9411201034502c034400780d41c2c0e0b001d40d080e03501c007013041c1800140541903501d04240240c03801003400b5140458149031140340141181d94110800702d0718408070004102090491403a08a00b408003240410b260400f41401c000807030700041c00410250000a0019544c4502e62010360b02078821586102141c540e01c0c42e19a1301c5031013290281d4450307404840400811701d0120014100304001000c20900c0729103a940382e0910841019054150b0010010001b4199050006001030540001050740c95410400792510040c0340e800001c0407019040c10011411004100b0385008026034000c4680c00e03078450510201a400a4441c54042030800400011640c040d2144009684007040d1150b1203a07615200e00c000b038a4003024140c0c103c0c0f400c10142015544600080015600802c0c01c4500e0341010000101011018410084c968004240d00c07918081c4600864038910720408a08040703448615080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 160777760 1250 160776510 160776521
    0x8060909010222060906080702330a0605120a030e0f0109050303041d10050607030309020a0b0d0515030f031e09040e1c050f0403030c1e0c090b040216020f0301 70
    0x5042e03143c09012520040f9030f0000810943d00c06541e0602499603d800031389425030140e6210002d43c0040d0780d42030f4400c400c01c4a1481d0900040c8103c00711640351940541e10100a61b10540d41d43e46030b10341413140c0d003400c030300d10745078071400f00c000303140403900c0351001000340e02e83e100303c58032a05560710091072a038403510a54002e4400101602c2d034035642e41400240515a402910a01c2c042c420b000500502c00b01000c0d0048450282032503140003425a8210001c01e43c510040303903c443c115002003000b03141c183c06422510605040003c0604040c02c515000c0144055480d11940c002c2c00c1d058842d60b0040269920010f01520b40e58070701b80c0045040440f4090700c40d4480d0060b11b441320856a141000030b40f040001e45692421206207403000b42280c0500ca42c0828516120040008100003481201b5003902d141c042c403a5842d01003184c1c84085d1202100c03510039903040c00c0b0b07210309000203425889118520704044404501c1d02d500082d03560041038105130701034070400f00100c0f203456588003074021 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 160779010 1250 160777760 160777777
    0x306040b04110a081003080703080a11030a060e01090902011403090f0a060204091503020603071b0203030c0c010f050c0c010507140a060e0706110c0402160b0705030105180403080609090102 83
    0x82c4018056000100c0407504010a02d01c00108500041217455000c0359410040c0d0390444052441c240c3c40341c030705550141c0082e01100c6403a541d080b4513504c60021201460042c1c800d0304001c2886032815240321b2a607001a00721111040c070301014100140e030091480c41108054840e00d03510780d5640d04030b240c00c00844010a44007405021803034410003c01350b00400a603000200c00b00000780456540880c10052400025000303501040030840b12800384a80410b001051064042103018543c0071900f10740007440608000c0d0703c5081071500c550f800c0f072244900c00c41c1e50310703141c1d0034032240e11030300341c0e4030130f0003800242c1800070000d0400188034102c10f845521102c0c03441151100d41e21403402800801c010300580701d507802141d8000c59018419000355851080b510000d00100c0301d000d003000029808071043c03202c1c005180c5503080004070001e01c1340d485650103071503181c0c80c2d40c0341c83c00b0b02c100c074030112400d030340d0900f400320030000044e03040308800e50000d40a03113880c8600d0740e444014600902c110641c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 160780260 1250 160779010 160779019
    0x307140f0307150606050c12160203120a0e010810030807080405120d080c090a26160807050f0612040c050a090506040f0501060c0b06060720010e0102070510050306040b 74
    0xd220381480300041840c500b815030003e0801ca880c0d92804115030f1070054411100c410380010791282c0e07444001c81c0140c00e13005000f206c0300c40505000c0d400280f0304000d4a0381642c3ca0080802c0c10311102e5046081070b0708000007070a01016038a00fa0070000d8007806203001c010650500888c000302808070100a603400303080c01900b00e060620b005003186545201090f8980000b805020015520a4218003540e200307a4020b0a01011103062407101200c1c20241920130417004e40780010f140290740d04016810004a41a201c210828180002c250401007560400c5006214015900c0004d4480c0b8044460b4525400c13040d06050b02d403450400490305140c0c0c012944010204804202e2074190303882240110400c43e81000248086007500c000d40d10240f141c2004034003051109008111a1000c0e6580702c040200214903200b00c560300e8581300700c280f809410207040403c200503059600200c00141c0007009000a102c100d10b00f40014044070380840c204410030034080003060142d02d031030f000108a60f90007030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 160781510 1250 160780260 160780267
    0x313081308100c02241302040c0c0b060102121b120c07060305060a030816060212010e1501020f07050409020a0504020a170f010305100e1005090d090e090307140f03 72
    0x70903466442d58007510740c200b000e150015101c035980c000240ca068014401d07140011010301d0805c00b040405008242c10034283c05005002c006a40718070941c00d00c103403e03441c0c2484010b90350421242d150b034010308040c10765018406000c244610f003810b651403c5800c6400204812080941c10300b44420740a40343d4124102290201d209400415000b041d1002941c080040369034140c2045030b0300e1030343d00c009004000104444a60a081c10810328141da029880140c43c22045450410800c0b200342c1c000890036000300c05015134411466405404900244004d100b01c41c038440503a510364030b03035200b06845655203503a404110b485003403840d001010700600c05c41d1501405200505000c0940c07102030281c4500c000001d88500041c8a030506a0790000001e00015a01c000030300300a00c6150f81080c0d86100b950040312619285014251090080c40c0203080c2028900340b01812402c0300750050136a940c8020200014401d0000545001c1c5400505500450030000d03100b42c2043c0d05140413003200e01001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 160782760 1250 160781510 160781519
    0x305190c021f020d030b0604030803040203161202010f0302130608070c080408072108040b0d0207120e040c0302070203120a030e030a030b0a0f0503060619050d140f06040803130813 79
    0x7a4205403202c0e56000c0d20071880402c0c1085007241c9800e0000c0383e0207a014003092020a540f40f014591040c8080c0440c3e00e1012184080c8070350560030f600510011050044007411541c0c040b001050003c100d050a45c01c0024441c01a900d0181900419041058040014a4045c8104032202840c0c0e0045505d035500c0b601c80e0f420684401140c019811102c2d86d440e240c01c0380c0b403003a14148a40c150005906030515051461001441e4000118820308a40902c00c0d40c0200700102111441441c4d5078030f078406400d02a034248401c1d07401380c0d001401410310621450005d038801040c0c0001150b240b41d46075540b070016540640040503011140c05481c44003140e601e801c0c0d41c141d4000520100200d40341c2500e80d540d800380d8000b80741180030f80c0d0b4158000c100820428200b60816210904640051040080e10b48020820b0040780400644100007040d00604407848240a50b86007009030001070003191401c0c4d00d031940c9912000d4140c20b01002c403000080148170614082e03400303a050810b040c4002a0380c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 160784010 1250 160782760 160782799
    0xa02040918050705010f02060a0b060912010f05012103120e06040309030b01090504080d150e0c0912030a0c0b07050d1103010503010e210708070204180515040305190c02 74
    0x904070841d1284501c400108803903001d00201075181c500c1c1d0b401002241d40e030b1500c0c000900141520f40783c111109003e5004c06642c1c10180c009003075030b078000000300700300100807010640b00180e20081d41a49008071a5a90300329541d42e4101d09501414400780300d560ba030780310400924002c400c400c1b07d03000d400207100415500c0465031040360b003d14030400a590300c40001c40212f030020b8500038031031241080500500c02c0690007400c41e04030007818203a20140ea50070303484c09800c400c490300d0602e5480000c02020f0b600d00510300b004150031a00c02941440138800014050a0344101e02030035912034480092444c40c0b040313084a0b103109001e0400d2000008a40ea0050590000c0c09240e01c01c0d420711900105170300300048d00780201605500981040702e86021040f07955800702c8401c0e40c2c02d0600300031000140c0c8480c0204002c070450801c6c515114902401d11900341111b0541711101e51080700c05100c0130951003802c0d6121041c9101d22010b40d8039003a03109032201d04c003080009420a52004240d4a0000b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 160785260 1250 160784010 160784051
    0x30a05040201080702010c050301090518100507181a072108061f0c030807090b130f050a0e06010513080f060f1501200705132003040b040b0a020409 65
    0x1c02c0e00c8116040e110540182c1c243c1f0038040b8403800040041c40100560601508040c0e0000903503c14000c03000142544c80342400c410050700003402c1d0710741e400d2003841680904082620040b0300101c2c0901e0781007203618090407a81c2040355074200d001140a206105802140c0743e204101c580020030100403086014254980446a8502c60001d00b0280044020020718240300504950f079599152405030f40c0039546010040e04100800680f2100429882c1900c8c000345024001d04081095040c1b40c403c0020b508050b507041035000d4400c1000c1001100381c01501d02d40c01400901b4140d40342d00300300740d114810440d01c1d80840ea5602c03820302c0440e41c000e400728401d8095400500c1c10f040c5680c2d10040d00503040811212240007580000c06003180900c1c0700e83c0b0b0074422160701c061314581c5940f80b000030400c60b007000403c014242d4540c450301c403501c0f440303803007900000050f4070700340c1586450b407507081d82050028030150915549400003070030050a98100c40240241840803c03140315203c1c071080399820b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 160786510 1250 160785260 160785263
    0xc0a1202030d0314040f1e0308060f030109030f030e150c031005040b0a090e03040312050c15060105030c0901170106030e06100b160f0b010306021c050106021e12030a0504 75
    0x244003440b42038076110b8001d0807040f01c00051042d986032107a0307490b58010000300106684060780016100d12088040140da00650300a90300c02c942d9040150800c00004c0501c02d5040c441d81c580501c0d100083d8000401c000ca021103420001488003441c484507082440441c41000c40501103400c01900300707051000345006160002c400e200158654040c401154443e07402ca6620142c078100030042405690000303280b8175186400c1e241441d85c2d0381e5625091040c1c2e4101c000100300c01080401440004111011002e008444404030310b0a0820010b0600e01c80600350545003040014501d5061340078034214001d0a42300020002c2940c4e4a00004006003900c10030551140910310114a0130010749017100d003031b2041c108040b0318140d1045d4a2a0100d2044a42121001c1c00e04412801080044420741d008601503080540d0300c180426808074524119a110307010a45840d0040c0000c40d40020b16590b030400e283c040040b8080d07110a0700e49880303a2140c08409440c80041046511401900040e0085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 160787760 1250 160786510 160786513
    0xd02030f0a0b030c0d020402041701060e160f051b0f1c1d0103050415020706090b090a030e10021509030909070906120518010f0b01020601080a02060d0506030c0a120203 74
    0x2900c8081c101c0c0c00752410704580c150b060380300404080704c900c0c01d00c40b01400d040c4010001860299613a50221304050907452504d81c90355500301c10401c1c51003a0080c2580880341c20368904000742c1c1414007a00125022041d0400c10401182448803003602210705c0b50100e0301602294031100110800603503501414001c814050085100c07044150700071303440c002c1544d207507581c190494490400110001d043c014000d94000303003184401400021103100030600f4070700508001c5143c070620708100002410141041c1c40d554403d881c031001180e4001c1d4803200a00301281d8200c0300d851105400c80c44e02900c60711160707035008610240040710500100902e04a2002e0307500c41d00950ba41c06041e16589090300c0b1305800b00d1100c86290b800706207a5404140d00c50807205480820185040c5050f08681d00d82c600740840541c1d40c0144291980c0400c5581d0040c0558402400c102c0a142c0c00300d9064050001d000f1a419103c2004c2609030703a003406820030300d0358081d04100d00035544d1039101e4001d0000000c203a009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 160789010 1250 160787760 160787791
    0x106090f06020304050f010c120e010306170a0b040c090c080412030e030d090f0b0403050c0609121204050c2d0319020f04060b0301090905011a031509120d0203 70
    0x10a00e08a5040215440c0c0d0700510309081c0b424081c0a140030207164050b041100302e03410000021113080600c0c0d40c14046036106c038400c01e16040050704551705600700c091001220441c00c0c403000c00c001004142180d102c24000d00d541c035a0302d00710cc5103018075000300c00320a017804591980c0941c02450103210700c2c050300c03e45850f00f216000031307000c43e100c4081402440d00108840144040a504410052481100b43c00c0350401543c643c91103140041e9021030004030001030902d0307090f5081103c00c2c0c000a490000e0036130428040c81d5102c244c03241056000e40060300c3c0002a085c0071043c005c4400d0203001074007100e07100c1c440c4a00200d48030b405c540d06124600e0000450798003802c001600b00e20441c0c0104402007000407540801c50920b04040c10203600c0f0340c5482000c82e003084240023841c020b01c0d90400201d0703400b00600c1c00307600750f13407508000403100b00f10745c0c4102c001a80d00040703038072400209c0c00b00340100b0348442d200c2c82d060840b40d40a105407400000f03a0307507400c0c401d203134029441149000d00c000c0c90b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 160790260 1250 160789010 160789019
    0x51311040c090e250903021206010e01120809040501060512160e0409110a0311011101110f031317030103020f12070902160615090c0801080a1101110a0b010609 70
    0x200c400711403026002940b03800c018005a462041c480303410194105800b241078004070600e00c0c840c3c00514800303000800032034041046040804401d407000700c1a0014004540c1130040000c41d4020521500e0b202841384021041800425001c17903118840181c010f100b550707110305000c1c00341e80c00041c5040c0c0f6500401c00140e980300510001c4216011160780f0030f911003800341304020281038103610680e9401552506042d0300d9407426403440c011032140c805d084080c05480009411021002892211369050054601d107000d411000c50b100880d543c0540c90322900e40d12120328020450f00001004000c243c1890680c0360100d2000d10304072842100c0342d10540a05809001d624080c1e8014040140e20844050041000b683c01510b064034648840c0c42201080351180380580d005800e5403061080801000d0204019500030511100e406040040c020351500c0889036581914000107481c00c0e0001c01a100a40e10509290040c403804c1c80885a900c1464105259121000e215400210303580c1e440016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 160791366 1106 160790260 160790269
    0x509040507051e0f130e070306020c0105012c0603161805010b070206040b0706090206040e10090b0a05010e0f03030406050c0105071e0e13051311 64
    0x40c81d07600d0700c0140006451160400f020488010028640c5615070080705659480d0a58403580c090241d42c0d030700e01c01005004d08042c400d0003800070000034022580c02400421000e54001c100b0303660307900c080040b500310f110351700c15000c0600030100c044030070285a240d41c0f100b4042e00351400d02003050f203020601c8145400c00c0703888460500000301010803501c542c40c050144412054074000c0245c002030094000c034440c05150010000703100c4100411a040070300f1207503018000589660702c03900c45110003e4221101040c125141000040750703000c41c0201c0d00301040c041c0c19511102c0c03d0100446090016440365074201d100340a001d00d01c1d4400300003c00040009985103034441c1034406281d401d41e0000342005040040e00b418540511361a14000c0c6401c0c01e403030401180001100020880c0c80750700c6818200c6e158540010000050003003144030001612507003005011200307400401 = true := by decide +kernel

theorem cover : BRFrame.Cov 160611510 160791366 := by
  have h0 := BRFrame.cov_init 160611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 160611510 ≤ n) (h2 : n < 160791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
